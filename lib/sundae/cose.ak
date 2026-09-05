use aiken/builtin
use aiken/cbor
use aiken/crypto
use aiken/option

pub type COSESignatures =
  List<COSESignature>

pub type HeaderMap =
  ByteArray

pub type Headers {
  protected: HeaderMap,
  unprotected: HeaderMap,
}

pub type COSESignature {
  headers: Headers,
  signature: ByteArray,
}

pub type COSESign1 {
  headers: Headers,
  payload: Option<ByteArray>,
  signature: ByteArray,
}

pub type COSESign {
  headers: Headers,
  payload: Option<ByteArray>,
  signatures: COSESignatures,
}

pub type SignedMessage {
  MultiSig(COSESign)
  SingleSig(COSESign1)
}

pub type SigStructure {
  context: ByteArray,
  body_protected: ByteArray,
  external_aad: ByteArray,
  payload: ByteArray,
}

pub fn data_to_sign(
  signed_message: SignedMessage,
  external_aad: Option<ByteArray>,
) -> SigStructure {
  let headers = headers(signed_message)

  SigStructure {
    context: context(signed_message),
    body_protected: headers.protected,
    external_aad: option.or_else(external_aad, #""),
    payload: payload(signed_message),
  }
}

pub fn headers(signed_message: SignedMessage) -> Headers {
  when signed_message is {
    SingleSig(cose_sign1) -> cose_sign1.headers
    MultiSig(cose_sign) -> cose_sign.headers
  }
}

pub fn context(signed_message: SignedMessage) -> ByteArray {
  when signed_message is {
    SingleSig(_) -> "Signature1"
    MultiSig(_) -> "Signature"
  }
}

pub fn payload(signed_message: SignedMessage) -> ByteArray {
  when signed_message is {
    SingleSig(cose_sign1) -> option.or_else(cose_sign1.payload, #"")
    MultiSig(cose_sign) -> option.or_else(cose_sign.payload, #"")
  }
}

/// Encode a byte array with definite-length CBOR encoding (major type 2).
/// This produces `40-57` for 0-23 bytes, `58xx` for 24-255 bytes, `59xxxx` for 256-65535 bytes.
fn encode_bytes_definite(data: ByteArray) -> ByteArray {
  let len = builtin.length_of_bytearray(data)
  if len <= 23 {
    // 40-57: length encoded in lower 5 bits
    builtin.cons_bytearray(0x40 + len, data)
  } else if len <= 255 {
    // 58 xx: 1-byte length prefix
    builtin.cons_bytearray(0x58, builtin.cons_bytearray(len, data))
  } else {
    // 59 xx xx: 2-byte length prefix (big-endian)
    let hi = len / 256
    let lo = len % 256
    builtin.cons_bytearray(
      0x59,
      builtin.cons_bytearray(hi, builtin.cons_bytearray(lo, data)),
    )
  }
}

/// Encode a text string with definite-length CBOR encoding (major type 3).
/// This produces `60-77` for 0-23 chars, `78xx` for 24-255 chars.
fn encode_text_definite(data: ByteArray) -> ByteArray {
  let len = builtin.length_of_bytearray(data)
  if len <= 23 {
    // 60-77: length encoded in lower 5 bits
    builtin.cons_bytearray(0x60 + len, data)
  } else if len <= 255 {
    // 78 xx: 1-byte length prefix
    builtin.cons_bytearray(0x78, builtin.cons_bytearray(len, data))
  } else {
    // 79 xx xx: 2-byte length prefix (big-endian)
    let hi = len / 256
    let lo = len % 256
    builtin.cons_bytearray(
      0x79,
      builtin.cons_bytearray(hi, builtin.cons_bytearray(lo, data)),
    )
  }
}

pub fn serialise_sig_structure(sig_structure: SigStructure) -> ByteArray {
  trace @"SigStructure.context": sig_structure.context
  trace @"SigStructure.body_protected": sig_structure.body_protected
  trace @"SigStructure.external_aad": sig_structure.external_aad
  trace @"SigStructure.payload": sig_structure.payload

  // Manually construct CBOR with definite-length encoding to match CIP-30 wallets
  // Format: 84 (4-element array) + context + body_protected + external_aad + payload
  let context_encoded = encode_text_definite(sig_structure.context)
  let body_protected_encoded = encode_bytes_definite(sig_structure.body_protected)
  let external_aad_encoded = encode_bytes_definite(sig_structure.external_aad)
  let payload_encoded = encode_bytes_definite(sig_structure.payload)

  let result =
    builtin.append_bytearray(
      #"84",
      builtin.append_bytearray(
        context_encoded,
        builtin.append_bytearray(
          body_protected_encoded,
          builtin.append_bytearray(external_aad_encoded, payload_encoded),
        ),
      ),
    )
  trace @"serialise_sig_structure result": result
  result
}

test single_signature() {
  let pub_key =
    #"384783f24116d6a337f62e20ec8da898bab5379bc49d1dc7317fa446ee3d40ab"

  let signature =
    #"95dad3041fd972ac86eeeb5f462a438b7dca10d7bfc287618e4c5401a3bca6217829e1ee5ca2bfac5f4106ec8f26d6851a7ff8975f1be1dc438ba8b277219800"

  let payload: ByteArray = "Hello, Cardano!"

  // Pre-serialized CBOR: {1: -8, 4: pub_key}
  let protected_header =
    #"a20127045820384783f24116d6a337f62e20ec8da898bab5379bc49d1dc7317fa446ee3d40ab"

  let signed_message =
    SingleSig(
      COSESign1 {
        headers: Headers { protected: protected_header, unprotected: #"" },
        payload: Some(payload),
        signature,
      },
    )

  let sig_structure = data_to_sign(signed_message, None)

  let serialised_sig_structure = serialise_sig_structure(sig_structure)

  expect
    serialised_sig_structure == #"846a5369676e6174757265315826a20127045820384783f24116d6a337f62e20ec8da898bab5379bc49d1dc7317fa446ee3d40ab404f48656c6c6f2c2043617264616e6f21"

  expect
    crypto.verify_ed25519_signature(
      pub_key,
      serialised_sig_structure,
      signature,
    )

  True
}

test multi_signature() {
  let pub_key_1 =
    #"f1b2e2a115dc2644c0aa3caca5bdcfbcfc7d3cdea2ee0281bf78f2793286e321"
  let signature_1 =
    #"43b4ffe0f219f184fbeb13f3d98dcad448d1771e7248b7c188301567fdaccd4726c8aee5d550cad3ddf8ddb7f680262eea2e34d102ae4e49290a34ecb810a002"

  let pub_key_2 =
    #"08a616a8b390df1211656bfe6690a9ec7cffaec3e5a6e2e5a12a7a93368c7ad6"
  let signature_2 =
    #"68cc5e4c6e3f99f1e2edce84f4bfcef2c8b4bc057420ee5c5f0ab0e4a76b1bdb48837f4cf63f9345ddcf8795d153fccd05331ea8c96bdaf4c4c1fabfc403d50a"

  let payload: ByteArray = "Hello, Cardano!"

  // Pre-serialized CBOR: {1: -8, 4: pub_key_1}
  let protected_header_1 =
    #"a20127045820f1b2e2a115dc2644c0aa3caca5bdcfbcfc7d3cdea2ee0281bf78f2793286e321"

  // Pre-serialized CBOR: {1: -8, 4: pub_key_2}
  let protected_header_2 =
    #"a2012704582008a616a8b390df1211656bfe6690a9ec7cffaec3e5a6e2e5a12a7a93368c7ad6"

  let signed_message =
    MultiSig(
      COSESign {
        headers: Headers { protected: #"", unprotected: #"" },
        payload: Some(payload),
        signatures: [
          COSESignature {
            headers: Headers {
              protected: protected_header_1,
              unprotected: #"",
            },
            signature: signature_1,
          },
          COSESignature {
            headers: Headers {
              protected: protected_header_2,
              unprotected: #"",
            },
            signature: signature_2,
          },
        ],
      },
    )

  let sig_structure = data_to_sign(signed_message, None)

  let serialised_sig_structure = serialise_sig_structure(sig_structure)

  expect
    serialised_sig_structure == #"84695369676e617475726540404f48656c6c6f2c2043617264616e6f21"

  expect
    crypto.verify_ed25519_signature(
      pub_key_1,
      serialised_sig_structure,
      signature_1,
    )

  expect
    crypto.verify_ed25519_signature(
      pub_key_2,
      serialised_sig_structure,
      signature_2,
    )

  True
}

/// Build a SigStructure for a COSESign1 message using an external payload.
/// This is used when the COSESign1.payload is None and the actual payload
/// is stored separately (e.g., in SignedRedeemer.payload).
pub fn build_sig_structure_for_sign1(
  headers: Headers,
  payload: ByteArray,
) -> SigStructure {
  SigStructure {
    context: "Signature1",
    body_protected: headers.protected,
    external_aad: #"",
    payload,
  }
}

test build_sig_structure_for_sign1_test() {
  let pub_key =
    #"384783f24116d6a337f62e20ec8da898bab5379bc49d1dc7317fa446ee3d40ab"

  let signature =
    #"95dad3041fd972ac86eeeb5f462a438b7dca10d7bfc287618e4c5401a3bca6217829e1ee5ca2bfac5f4106ec8f26d6851a7ff8975f1be1dc438ba8b277219800"

  // Pre-serialized CBOR: {1: -8, 4: pub_key}
  let protected_header =
    #"a20127045820384783f24116d6a337f62e20ec8da898bab5379bc49d1dc7317fa446ee3d40ab"

  let headers = Headers { protected: protected_header, unprotected: #"" }

  let payload: ByteArray = "Hello, Cardano!"

  let sig_structure = build_sig_structure_for_sign1(headers, payload)

  // Should produce same result as data_to_sign for a SingleSig message
  let signed_message =
    SingleSig(
      COSESign1 { headers, payload: Some(payload), signature },
    )
  let expected_sig_structure = data_to_sign(signed_message, None)

  expect sig_structure.context == expected_sig_structure.context
  expect sig_structure.body_protected == expected_sig_structure.body_protected
  expect sig_structure.external_aad == expected_sig_structure.external_aad
  expect sig_structure.payload == expected_sig_structure.payload

  // Also verify that it can be serialized and verified
  let serialised = serialise_sig_structure(sig_structure)
  expect crypto.verify_ed25519_signature(pub_key, serialised, signature)

  True
}
