use aiken/collection/list
use aiken/collection/pairs
use aiken/crypto.{
  Signature, VerificationKey, blake2b_224, verify_ed25519_signature,
}
use aiken/interval.{Finite, Interval, IntervalBound}
use cardano/address.{Credential}
use cardano/assets.{Lovelace}
use cardano/transaction.{ValidityRange}

pub type MultisigScript {
  Signature { key_hash: ByteArray }
  AllOf { scripts: List<MultisigScript> }
  AnyOf { scripts: List<MultisigScript> }
  AtLeast { required: Int, scripts: List<MultisigScript> }
  Before { time: Int }
  After { time: Int }
  Script { script_hash: ByteArray }
}

pub fn satisfied(
  script: MultisigScript,
  signatories: List<ByteArray>,
  valid_range: ValidityRange,
  withdrawals: Pairs<Credential, Lovelace>,
) -> Bool {
  when script is {
    Signature { key_hash } -> list.has(signatories, key_hash)
    AllOf { scripts } ->
      list.all(
        scripts,
        fn(s) { satisfied(s, signatories, valid_range, withdrawals) },
      )
    AnyOf { scripts } ->
      list.any(
        scripts,
        fn(s) { satisfied(s, signatories, valid_range, withdrawals) },
      )
    AtLeast { required, scripts } ->
      required <= list.count(
        scripts,
        fn(s) { satisfied(s, signatories, valid_range, withdrawals) },
      )
    Before { time } ->
      when valid_range.upper_bound is {
        IntervalBound { bound_type: Finite(hi), is_inclusive: True } ->
          hi <= time
        IntervalBound { bound_type: Finite(hi), is_inclusive: False } ->
          hi < time
        _ -> False
      }
    After { time } ->
      when valid_range.lower_bound is {
        IntervalBound { bound_type: Finite(lo), is_inclusive: True } ->
          time <= lo
        IntervalBound { bound_type: Finite(lo), is_inclusive: False } ->
          time < lo
        _ -> False
      }
    Script { script_hash } ->
      pairs.has_key(withdrawals, address.Script(script_hash))
  }
}

pub fn satisfied_payload(
  script: MultisigScript,
  payload: ByteArray,
  signatures: List<(VerificationKey, Signature)>,
  valid_range: ValidityRange,
  withdrawals: Pairs<Credential, Lovelace>,
) -> Bool {
  when script is {
    // A member without a matching signature is unsatisfied, not an abort:
    // AtLeast counts with list.count (no short-circuit), so a trapping leaf
    // would fail a met threshold on the first non-signing member. Mirrors the
    // total `satisfied` leaf (list.has).
    Signature { key_hash } ->
      when list.find(signatures, fn((k, _)) { blake2b_224(k) == key_hash }) is {
        Some((public_key, signature)) ->
          verify_ed25519_signature(public_key, payload, signature)
        None -> False
      }
    AllOf { scripts } ->
      list.all(
        scripts,
        fn(s) {
          satisfied_payload(s, payload, signatures, valid_range, withdrawals)
        },
      )
    AnyOf { scripts } ->
      list.any(
        scripts,
        fn(s) {
          satisfied_payload(s, payload, signatures, valid_range, withdrawals)
        },
      )
    AtLeast { required, scripts } ->
      required <= list.count(
        scripts,
        fn(s) {
          satisfied_payload(s, payload, signatures, valid_range, withdrawals)
        },
      )
    Before { time } ->
      when valid_range.upper_bound is {
        IntervalBound { bound_type: Finite(hi), is_inclusive: True } ->
          hi <= time
        IntervalBound { bound_type: Finite(hi), is_inclusive: False } ->
          hi < time
        _ -> False
      }
    After { time } ->
      when valid_range.lower_bound is {
        IntervalBound { bound_type: Finite(lo), is_inclusive: True } ->
          time <= lo
        IntervalBound { bound_type: Finite(lo), is_inclusive: False } ->
          time < lo
        _ -> False
      }
    Script { script_hash } ->
      pairs.has_key(withdrawals, address.Script(script_hash))
  }
}

fn valid_range(lo: Int, hi: Int) -> ValidityRange {
  Interval {
    lower_bound: IntervalBound { bound_type: Finite(lo), is_inclusive: True },
    upper_bound: IntervalBound { bound_type: Finite(hi), is_inclusive: False },
  }
}

test satisfying() {
  let key_hash1 = "key1"
  let key_hash2 = "key2"
  let key_hash3 = "key3"
  let sig1 = Signature { key_hash: key_hash1 }
  trace @"Signature": sig1
  let sig2 = Signature { key_hash: key_hash2 }
  let sig3 = Signature { key_hash: key_hash3 }
  let all_of = AllOf { scripts: [sig1, sig2] }
  trace @"AllOf": all_of
  let any_of = AnyOf { scripts: [sig1, sig2] }
  trace @"AnyOf": any_of
  let at_least = AtLeast { required: 2, scripts: [sig1, sig2, sig3] }
  trace @"AtLeast": at_least
  let before = Before { time: 10 }
  trace @"Before": before
  let after = After { time: 10 }
  trace @"After": after
  let between = AllOf { scripts: [After { time: 10 }, Before { time: 15 }] }
  trace @"Between": between
  let script = Script { script_hash: "some_script" }
  trace @"Script": script
  let vesting = AnyOf {
    scripts: [
      AllOf { scripts: [before, sig1] },
      // clawback
      AllOf { scripts: [after, sig2] },
      // dao clawback
      script,
    ],
  }
  trace @"Vesting": vesting
  let no_w: Pairs<Credential, Lovelace> = []
  let correct_w = [Pair(address.Script("some_script"), 0)]
  let incorrect_w = [Pair(address.Script("other_script"), 0)]
  let both_w = [
    Pair(address.Script("some_script"), 0),
    Pair(address.Script("other_script"), 0),
  ]
  // Helper method because ? binds more tightly than !
  let unsatisfied = fn(
    n: MultisigScript,
    s: List<ByteArray>,
    v: ValidityRange,
    w: Pairs<Credential, Lovelace>,
  ) {
    !satisfied(n, s, v, w)
  }
  list.all(
    [
      satisfied(sig1, [key_hash1], valid_range(0, 1), no_w)?,
      satisfied(sig2, [key_hash1, key_hash2], valid_range(0, 1), no_w)?,
      satisfied(all_of, [key_hash1, key_hash2], valid_range(0, 1), no_w)?,
      satisfied(any_of, [key_hash2], valid_range(0, 1), no_w)?,
      satisfied(at_least, [key_hash2, key_hash3], valid_range(0, 1), no_w)?,
      satisfied(before, [], valid_range(0, 5), no_w)?,
      satisfied(after, [], valid_range(15, 20), no_w)?,
      satisfied(after, [], valid_range(10, 15), no_w)?,
      satisfied(between, [], valid_range(12, 13), no_w)?,
      satisfied(script, [], valid_range(0, 1), correct_w)?,
      satisfied(script, [], valid_range(0, 1), both_w)?,
      satisfied(vesting, [key_hash1], valid_range(0, 5), no_w)?,
      satisfied(vesting, [key_hash2], valid_range(15, 20), no_w)?,
      satisfied(vesting, [key_hash3], valid_range(0, 1), correct_w)?,
      unsatisfied(sig1, [key_hash2], valid_range(0, 1), no_w)?,
      unsatisfied(sig3, [key_hash1, key_hash2], valid_range(0, 1), no_w)?,
      unsatisfied(all_of, [key_hash1, key_hash3], valid_range(0, 1), no_w)?,
      unsatisfied(any_of, [key_hash3], valid_range(0, 1), no_w)?,
      unsatisfied(at_least, [key_hash2], valid_range(0, 1), no_w)?,
      unsatisfied(before, [], valid_range(5, 15), no_w)?,
      unsatisfied(before, [], valid_range(5, 10), no_w)?,
      unsatisfied(before, [], valid_range(10, 10), no_w)?,
      unsatisfied(after, [], valid_range(5, 15), no_w)?,
      unsatisfied(between, [], valid_range(0, 5), no_w)?,
      unsatisfied(between, [], valid_range(0, 13), no_w)?,
      unsatisfied(between, [], valid_range(0, 20), no_w)?,
      unsatisfied(between, [], valid_range(13, 20), no_w)?,
      unsatisfied(between, [], valid_range(13, 15), no_w)?,
      unsatisfied(between, [], valid_range(15, 20), no_w)?,
      unsatisfied(script, [], valid_range(0, 1), incorrect_w)?,
      unsatisfied(vesting, [key_hash2], valid_range(0, 5), no_w)?,
      unsatisfied(vesting, [key_hash1], valid_range(15, 20), no_w)?,
      unsatisfied(vesting, [key_hash3], valid_range(10, 10), no_w)?,
      unsatisfied(vesting, [key_hash3], valid_range(0, 5), no_w)?,
      unsatisfied(vesting, [key_hash3], valid_range(15, 20), no_w)?,
      unsatisfied(vesting, [key_hash3], valid_range(15, 20), incorrect_w)?,
    ],
    fn(n) { n },
  )
}

test satisfying_payload() {
  let payload = "some_payload"
  // Generated from seed "E5C6E8D39E443DC0A2845BB13217070EE2D82E7C1BE580DA22E7C6BF2DB56EA9"
  // here: https://cyphr.me/ed25519_tool/ed.html
  let key1 = #"becff931d5043db380b78f5b1ba79d549999024c5fc0c9dd9390da0d12b054bc"
  let key_hash1 = blake2b_224(key1)
  let sig1 = Signature { key_hash: key_hash1 }
  let signature = #"bda2210a08762fc1032523653f32d57cc97bfbaf84c46566625f4240c3ad59d3d2efc7a1d1640cf79e4d337368595e7bdce92af6ea0c3278c2998482b8dd7d05"
  let wrong_signature = #"cda2210a08762fc1032523653f32d57cc97bfbaf84c46566625f4240c3ad59d3d2efc7a1d1640cf79e4d337368595e7bdce92af6ea0c3278c2998482b8dd7d05"
  let no_w: Pairs<Credential, Lovelace> = []
  and {
    satisfied_payload(
      sig1,
      payload,
      [(key1, signature)],
      valid_range(0, 1),
      no_w,
    ),
    !satisfied_payload(
      sig1,
      payload,
      [(key1, wrong_signature)],
      valid_range(0, 1),
      no_w,
    ),
  }
}

// A declared member with no matching signature must count as unsatisfied, not
// abort the whole check. AtLeast counts with list.count (no short-circuit), so
// a trapping leaf would fail a met threshold; AnyOf traps only when the absent
// member sorts before a satisfied one. Both regressions covered here.
test satisfying_payload_atleast_tolerates_absent_signer() {
  let payload = "some_payload"
  let key1 = #"becff931d5043db380b78f5b1ba79d549999024c5fc0c9dd9390da0d12b054bc"
  let sig1 = Signature { key_hash: blake2b_224(key1) }
  let signature = #"bda2210a08762fc1032523653f32d57cc97bfbaf84c46566625f4240c3ad59d3d2efc7a1d1640cf79e4d337368595e7bdce92af6ea0c3278c2998482b8dd7d05"
  let absent = Signature { key_hash: #"00" }
  let no_w: Pairs<Credential, Lovelace> = []
  let script = AtLeast { required: 1, scripts: [sig1, absent] }
  satisfied_payload(
    script,
    payload,
    [(key1, signature)],
    valid_range(0, 1),
    no_w,
  )
}

test satisfying_payload_anyof_tolerates_absent_signer_first() {
  let payload = "some_payload"
  let key1 = #"becff931d5043db380b78f5b1ba79d549999024c5fc0c9dd9390da0d12b054bc"
  let sig1 = Signature { key_hash: blake2b_224(key1) }
  let signature = #"bda2210a08762fc1032523653f32d57cc97bfbaf84c46566625f4240c3ad59d3d2efc7a1d1640cf79e4d337368595e7bdce92af6ea0c3278c2998482b8dd7d05"
  let absent = Signature { key_hash: #"00" }
  let no_w: Pairs<Credential, Lovelace> = []
  let script = AnyOf { scripts: [absent, sig1] }
  satisfied_payload(
    script,
    payload,
    [(key1, signature)],
    valid_range(0, 1),
    no_w,
  )
}

/// Verify a multisig script where each signer may have signed a different payload.
/// This is needed for COSESign1 compatibility where each signer's Sig_structure
/// includes their own protected headers.
///
/// Each entry in signatures is (VerificationKey, Signature, Payload) where
/// Payload is the serialized Sig_structure that was signed by that key.
pub fn satisfied_payloads(
  script: MultisigScript,
  signatures: List<(VerificationKey, Signature, ByteArray)>,
  valid_range: ValidityRange,
  withdrawals: Pairs<Credential, Lovelace>,
) -> Bool {
  when script is {
    Signature { key_hash } -> {
      trace @"Checking Signature for key_hash": key_hash
      let found =
        list.find(signatures, fn((k, _, _)) { blake2b_224(k) == key_hash })
      when found is {
        Some((public_key, signature, payload)) -> {
          trace @"Found signature, verifying..."
          trace @"verify_ed25519 public_key": public_key
          trace @"verify_ed25519 payload": payload
          trace @"verify_ed25519 signature": signature
          let result = verify_ed25519_signature(public_key, payload, signature)
          trace @"Signature verification result": result
          result
        }
        None -> {
          trace @"No signature found for key_hash": key_hash
          False
        }
      }
    }
    AllOf { scripts } -> {
      trace @"Checking AllOf with script count": list.length(scripts)
      let result =
        list.all(
          scripts,
          fn(s) { satisfied_payloads(s, signatures, valid_range, withdrawals) },
        )
      trace @"AllOf result": result
      result
    }
    AnyOf { scripts } -> {
      trace @"Checking AnyOf with script count": list.length(scripts)
      let result =
        list.any(
          scripts,
          fn(s) { satisfied_payloads(s, signatures, valid_range, withdrawals) },
        )
      trace @"AnyOf result": result
      result
    }
    AtLeast { required, scripts } -> {
      trace @"Checking AtLeast": required
      let count =
        list.count(
          scripts,
          fn(s) { satisfied_payloads(s, signatures, valid_range, withdrawals) },
        )
      trace @"AtLeast satisfied count": count
      let result = required <= count
      trace @"AtLeast result": result
      result
    }
    Before { time } -> {
      trace @"Checking Before": time
      let result =
        when valid_range.upper_bound is {
          IntervalBound { bound_type: Finite(hi), is_inclusive: True } ->
            hi <= time
          IntervalBound { bound_type: Finite(hi), is_inclusive: False } ->
            hi < time
          _ -> False
        }
      trace @"Before result": result
      result
    }
    After { time } -> {
      trace @"Checking After": time
      let result =
        when valid_range.lower_bound is {
          IntervalBound { bound_type: Finite(lo), is_inclusive: True } ->
            time <= lo
          IntervalBound { bound_type: Finite(lo), is_inclusive: False } ->
            time < lo
          _ -> False
        }
      trace @"After result": result
      result
    }
    Script { script_hash } -> {
      trace @"Checking Script": script_hash
      let result = pairs.has_key(withdrawals, address.Script(script_hash))
      trace @"Script result": result
      result
    }
  }
}

test satisfied_payloads_test() {
  // Each signer can have their own payload (simulating different Sig_structures
  // due to different protected headers in COSESign1)
  let payload = "some_payload"
  // Generated from seed "E5C6E8D39E443DC0A2845BB13217070EE2D82E7C1BE580DA22E7C6BF2DB56EA9"
  // here: https://cyphr.me/ed25519_tool/ed.html
  let key1 = #"becff931d5043db380b78f5b1ba79d549999024c5fc0c9dd9390da0d12b054bc"
  let key_hash1 = blake2b_224(key1)
  let sig1 = Signature { key_hash: key_hash1 }
  let signature =
    #"bda2210a08762fc1032523653f32d57cc97bfbaf84c46566625f4240c3ad59d3d2efc7a1d1640cf79e4d337368595e7bdce92af6ea0c3278c2998482b8dd7d05"
  let wrong_signature =
    #"cda2210a08762fc1032523653f32d57cc97bfbaf84c46566625f4240c3ad59d3d2efc7a1d1640cf79e4d337368595e7bdce92af6ea0c3278c2998482b8dd7d05"
  let no_w: Pairs<Credential, Lovelace> = []
  and {
    satisfied_payloads(
      sig1,
      [(key1, signature, payload)],
      valid_range(0, 1),
      no_w,
    ),
    !satisfied_payloads(
      sig1,
      [(key1, wrong_signature, payload)],
      valid_range(0, 1),
      no_w,
    ),
  }
}

// ============================================================================
// Shape predicates
// ============================================================================

/// True if `script` can be satisfied by NOBODY — some path is met with no
/// signature and no script-withdrawal, using structure or time bounds alone.
/// A `Signature` or `Script` leaf is a real authenticator; `Before` / `After`
/// and empty or zero-threshold combinators are not.
///
/// A caller that stores a multisig taken from untrusted data (for example an
/// oracle key set supplied by datum) can reject an "authenticates no one"
/// value with `!satisfiable_by_nobody(script)`. This leaves every real shape
/// available — including the `Script` withdrawal path and future script-based
/// restrictions — and rejects only the shapes anyone can satisfy.
pub fn satisfiable_by_nobody(script: MultisigScript) -> Bool {
  when script is {
    Signature { .. } -> False
    Script { .. } -> False
    Before { .. } -> True
    After { .. } -> True
    AllOf { scripts } -> list.all(scripts, satisfiable_by_nobody)
    AnyOf { scripts } -> list.any(scripts, satisfiable_by_nobody)
    AtLeast { required, scripts } ->
      required <= list.count(scripts, satisfiable_by_nobody)
  }
}

test satisfiable_by_nobody_rejects_vacuous_and_time_only() {
  let sig = Signature { key_hash: #"01" }
  let scr = Script { script_hash: #"02" }
  and {
    // Vacuous or time-only shapes authenticate no one.
    satisfiable_by_nobody(AtLeast { required: 0, scripts: [] }),
    satisfiable_by_nobody(AllOf { scripts: [] }),
    satisfiable_by_nobody(Before { time: 10 }),
    satisfiable_by_nobody(After { time: 10 }),
    satisfiable_by_nobody(AnyOf { scripts: [sig, Before { time: 10 }] }),
    satisfiable_by_nobody(AtLeast { required: 0, scripts: [sig] }),
    // A real authenticator is required on every satisfying path.
    !satisfiable_by_nobody(sig),
    !satisfiable_by_nobody(scr),
    !satisfiable_by_nobody(AtLeast { required: 1, scripts: [sig] }),
    !satisfiable_by_nobody(AllOf { scripts: [sig, Before { time: 10 }] }),
    !satisfiable_by_nobody(AnyOf { scripts: [sig, scr] }),
  }
}
