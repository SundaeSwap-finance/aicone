use aiken/list as native_list
use aiken/fuzz.{list as fuzz_list, bool, list_between, int_between, map, constant, and_then, label}
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
    let byte <- and_then(int_between(0, 255))
    constant(bytearray.push(#"", byte))
}

pub fn public_key() -> Fuzzer<ByteArray> {
    let b <- and_then(byte())
    let hash = blake2b_256(b)
    constant(bytearray.take(hash, 28))
}
pub fn script_hash() -> Fuzzer<ByteArray> {
    let b <- and_then(byte())
    let hash = blake2b_256(b)
    constant(bytearray.take(hash, 28))
}

pub fn posix_time() -> Fuzzer<PosixTime> {
    int_between(1600000000, 2000000000) |> map(identity)
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
    let scripts <- and_then(list_between(multisig(depth - 1), 1, depth))
    let count <- and_then(int_between(1, native_list.length(scripts)))
    constant(AtLeast(count, scripts))
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
        let bit <- and_then(bool())
        let rest <- and_then(uniform(bits - 1))
        if bit {
            constant(rest * 2 + 1)
        } else {
            constant(rest * 2)
        }
    }
}

pub fn multisig(depth: Int) -> Fuzzer<MultisigScript> {
    let variant <- and_then(uniform(6))
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
    let count <- and_then(int_between(0, 10))
    let keys <- and_then(list_between(public_key(), count, count))
    let keys = list.map(keys, fn(pk) { Inline(ScriptCredential(pk)) })
    let amounts <- and_then(list_between(int_between(0, 100), count, count))
    constant(dict.from_list(list.zip(keys, amounts), compare_stake))
}

pub fn test_case() -> Fuzzer<TestCase> {
    let script <- and_then(multisig(5))
    let signatories <- and_then(fuzz_list(public_key()))
    let withdrawals <- and_then(withdrawals())
    let lower_bound <- and_then(posix_time())
    let upper_bound <- and_then(posix_time())
    let valid_range = Interval {
        lower_bound: IntervalBound {
            bound_type: Finite(lower_bound),
            is_inclusive: True,
        },
        upper_bound: IntervalBound {
            bound_type: Finite(upper_bound),
            is_inclusive: True,
        }
    }
    constant(
        TestCase {
            sig: script,
            signatories,
            valid_range,
            withdrawals,
        }
    )
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