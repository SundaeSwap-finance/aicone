use aiken/builtin
use aiken/cbor
use aiken/collection/list
use aiken/crypto
use aiken/option

const hdr_key_id: Data = 4

type COSESignatures =
  List<COSESignature>

type HeaderMap =
  Pairs<Data, Data>

type Headers {
  protected: HeaderMap,
  unprotected: HeaderMap,
}

type COSESignature {
  headers: Headers,
  signature: ByteArray,
}

type COSESign1 {
  headers: Headers,
  payload: Option<ByteArray>,
  signature: ByteArray,
}

type COSESign {
  headers: Headers,
  payload: Option<ByteArray>,
  signatures: COSESignatures,
}

type SignedMessage {
  MultiSig(COSESign)
  SingleSig(COSESign1)
}

type SigStructure {
  context: ByteArray,
  body_protected: ByteArray,
  external_aad: ByteArray,
  payload: ByteArray,
}

fn data_to_sign(
  signed_message: SignedMessage,
  external_aad: Option<ByteArray>,
) -> SigStructure {
  when signed_message is {
    SingleSig(cose_sign1) -> {
      let body_protected =
        if list.length(cose_sign1.headers.protected) > 0 {
          cbor.serialise(cose_sign1.headers.protected)
        } else {
          #""
        }
      SigStructure {
        context: "Signature1",
        body_protected,
        external_aad: option.or_else(external_aad, #""),
        payload: option.or_else(cose_sign1.payload, #""),
      }
    }
    MultiSig(cose_sign) -> {
      let body_protected =
        if list.length(cose_sign.headers.protected) > 0 {
          cbor.serialise(cose_sign.headers.protected)
        } else {
          #""
        }

      SigStructure {
        context: "Signature",
        body_protected,
        external_aad: option.or_else(external_aad, #""),
        payload: option.or_else(cose_sign.payload, #""),
      }
    }
  }
}

fn serialise_sig_structure(sig_structure: SigStructure) -> ByteArray {
  let raw_bytes =
    cbor.serialise(
      [
        sig_structure.context,
        sig_structure.body_protected,
        sig_structure.external_aad,
        sig_structure.payload,
      ],
    )

  let context_type_byte = builtin.slice_bytearray(1, 1, raw_bytes)
  let fixed_content_type_byte = builtin.write_bits(context_type_byte, [5], True)
  let content_bytes =
    builtin.slice_bytearray(
      2,
      builtin.length_of_bytearray(raw_bytes) - 3,
      raw_bytes,
    )

  builtin.append_bytearray(
    #"84",
    builtin.append_bytearray(fixed_content_type_byte, content_bytes),
  )
}

test single_signature() {
  let pub_key =
    #"384783f24116d6a337f62e20ec8da898bab5379bc49d1dc7317fa446ee3d40ab"

  let signature =
    #"95dad3041fd972ac86eeeb5f462a438b7dca10d7bfc287618e4c5401a3bca6217829e1ee5ca2bfac5f4106ec8f26d6851a7ff8975f1be1dc438ba8b277219800"

  let payload: ByteArray = "Hello, Cardano!"

  let signed_message =
    SingleSig(
      COSESign1 {
        headers: Headers {
          protected: [
            Pair(as_data(1), as_data(-8)),
            Pair(as_data(hdr_key_id), as_data(pub_key)),
          ],
          unprotected: [],
        },
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

  let signed_message =
    MultiSig(
      COSESign {
        headers: Headers { protected: [], unprotected: [] },
        payload: Some(payload),
        signatures: [
          COSESignature {
            headers: Headers {
              protected: [
                Pair(as_data(1), as_data(-8)),
                Pair(as_data(hdr_key_id), as_data(pub_key_1)),
              ],
              unprotected: [],
            },
            signature: signature_1,
          },
          COSESignature {
            headers: Headers {
              protected: [
                Pair(as_data(1), as_data(-8)),
                Pair(as_data(hdr_key_id), as_data(pub_key_2)),
              ],
              unprotected: [],
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
