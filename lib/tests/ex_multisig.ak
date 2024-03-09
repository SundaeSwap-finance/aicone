use aiken/cbor
use aiken/list as native_list
use aiken/fuzz.{list as fuzz_list, bool, list_between, int_between, one_of, map, map2, constant, and_then, label}
use aiken/bytearray
use aiken/hash.{blake2b_256}
use aiken/time.{PosixTime}
use aiken/transaction.{ValidityRange}
use aiken/dict.{Dict}
use aiken/interval.{Interval, IntervalBound, Finite}
use aiken/list
use aiken/transaction/credential.{StakeCredential, Inline, ScriptCredential, VerificationKeyCredential}
use sundae/multisig.{MultisigScript, Signature, AllOf, AnyOf, AtLeast, Before, After, Script, satisfied}

pub fn byte() -> Fuzzer<ByteArray> {
    int_between(0, 255) |> map2(constant(#""), _, bytearray.push)
}

pub fn public_key() -> Fuzzer<ByteArray> {
    byte() |> map(blake2b_256) |> map(fn(x) { bytearray.take(x, 28) })
}
pub fn script_hash() -> Fuzzer<ByteArray> {
    byte() |> map(blake2b_256) |> map(fn(x) { bytearray.take(x, 28) })
}

pub fn posix_time() -> Fuzzer<PosixTime> {
    int_between(1600000000, 2000000000) |> map(fn(x) { x })
}

pub fn signature_multisig() -> Fuzzer<MultisigScript> {
    public_key() |> map(Signature)
}
pub fn all_of_multisig(depth: Int) -> Fuzzer<MultisigScript> {
    list_between(multisig(depth - 1), 1, depth) |> map(AllOf)
}
pub fn any_of_multisig(depth: Int) -> Fuzzer<MultisigScript> {
    list_between(multisig(depth - 1), 1, depth) |> map(AnyOf)
}
pub fn at_least_multisig(depth: Int) -> Fuzzer<MultisigScript> {
    list_between(multisig(depth - 1), 1, depth) |> and_then(fn(scripts) {
        int_between(1, native_list.length(scripts)) |> map(fn(count) {
            AtLeast(count, scripts)
        })
    })
}
pub fn before_multisig() -> Fuzzer<MultisigScript> {
    posix_time() |> map(Before)
}
pub fn after_multisig() -> Fuzzer<MultisigScript> {
    posix_time() |> map(After)
}
pub fn script_multisig() -> Fuzzer<MultisigScript> {
    script_hash() |> map(Script)
}

pub fn uniform(bits: Int) -> Fuzzer<Int> {
    if bits == 0 {
        constant(0)
    } else {
        bool() |> and_then(fn(b) {
            if b {
                uniform(bits - 1) |> map(fn(x) { x * 2 + 1 })
            } else {
                uniform(bits - 1) |> map(fn(x) { x * 2 })
            }
        })
    }
}

pub fn multisig(depth: Int) -> Fuzzer<MultisigScript> {
    uniform(6) |>
    and_then(fn(variant) {
        let variant = variant % 7
        when variant is {
            1 if depth >= 1 -> { all_of_multisig(depth - 1) }
            2 if depth >= 1 -> { any_of_multisig(depth - 1) }
            3 if depth >= 1 -> { at_least_multisig(depth - 1) }

            0 -> { signature_multisig() }
            4 -> { before_multisig() }
            5 -> { after_multisig() }
            6 -> { script_multisig() }
            
            1 | 2 | 3 -> { multisig(depth)}

            _ -> {
                fail
            }
        }
    })
}

pub type TestCase {
    sig: MultisigScript,
    signatories: List<ByteArray>,
    valid_range: ValidityRange,
    withdrawals: Dict<StakeCredential, Int>,
}

pub fn compare_stake(left: StakeCredential, right: StakeCredential) -> Ordering {
    let left = when left is {
        Inline(ScriptCredential(x)) -> x
        Inline(VerificationKeyCredential(x)) -> x
        _ -> fail
    }
    let right = when right is {
        Inline(ScriptCredential(x)) -> x
        Inline(VerificationKeyCredential(x)) -> x
        _ -> fail
    }
    bytearray.compare(left, right)
}

pub fn withdrawals() -> Fuzzer<Dict<StakeCredential, Int>> {
    int_between(0,10) |> and_then(fn(count) {
        map2(
            list_between(public_key(), count, count) |> map(fn(pks) { list.map(pks, fn(pk) { Inline(ScriptCredential(pk)) }) }),
            list_between(int_between(0, 100), count, count),
            fn(keys, amounts) {
                dict.from_list(list.zip(keys, amounts), compare_stake)
            }
        )
    })
}

pub fn test_case() -> Fuzzer<TestCase> {
    multisig(5) |> and_then(fn(sig) {
        fuzz_list(public_key()) |> and_then(fn(signatories) {
            withdrawals() |> and_then(fn(withdrawals) {
            map2(
                posix_time(),
                posix_time(),
                fn(start, end) {
                    TestCase {
                        sig: sig,
                        signatories: signatories,
                        valid_range: Interval {
                            upper_bound: IntervalBound {
                                bound_type: Finite(start),
                                is_inclusive: True,
                            },
                            lower_bound: IntervalBound {
                                bound_type: Finite(end),
                                is_inclusive: True,
                            }
                        },
                        withdrawals: withdrawals,
                    }
                })
            })
        })
    })
}

test shouldnt_crash(test_case via test_case()) {
    label(
        when test_case.sig is {
            Signature(_) -> @"Signature"
            AllOf(_) -> @"AllOf"
            AnyOf(_) -> @"AnyOf"
            AtLeast(_, _) -> @"AtLeast"
            Before(_) -> @"Before"
            After(_) -> @"After"
            Script(_) -> @"Script"
        }
    )
    let satisfied = satisfied(
        test_case.sig,
        test_case.signatories,
        test_case.valid_range,
        test_case.withdrawals
    )
    label(
        when satisfied is {
            True -> @"True"
            False -> @"False"
        }
    )
    True
}