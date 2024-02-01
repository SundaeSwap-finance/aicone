use aiken/dict.{Dict}
use aiken/list
use aiken/transaction.{ValidityRange, Output}
use aiken/interval.{Finite}
use aiken/transaction/credential.{Address, StakeCredential, Script, Inline, ScriptCredential}
use aiken/transaction/value
use aiken/hash.{Hash, Blake2b_224}
use aiken/time.{PosixTime}
use sundae/multisig

pub type ScheduleEntry {
    date: PosixTime,
    amount: Int,
}

pub type Schedule {
    Recurring { start: PosixTime, interval: Int, amount: Int, end: PosixTime }
    Structured { phases: List<ScheduleEntry> }
}

pub type PaymentPlan {
    owner: multisig.MultisigScript,
    recipient: Address,
    condition: Option<ByteArray>,
    fee: Int,
    schedule: Schedule,
}

fn condition_satisfied(condition: Option<ByteArray>, withdrawals: Dict<StakeCredential, Int>) -> Bool {
    when condition is {
        None -> True
        Some(cond) -> {
            dict.has_key(withdrawals, Inline(ScriptCredential(cond)))
        }
    }
}

fn get_bounds(valid_range: ValidityRange) -> (PosixTime, PosixTime) {
    expect Finite(lo) = valid_range.lower_bound.bound_type
    expect Finite(hi) = valid_range.upper_bound.bound_type
    (lo, hi)
}

//
//
//  DISCLAIMER:
//  This is currently a sketch of an idea, and is not safe to use in production until it's been refined more.
//  In particular, it's currently vulnerable to double-satisfaction and all manner of things
//

pub fn satisfied(
    own_script_hash: Hash<Blake2b_224, Script>,
    plan: PaymentPlan,
    signatories: List<ByteArray>,
    valid_range: ValidityRange,
    withdrawals: Dict<StakeCredential, Int>,
    utxo: Output,
    outputs: List<Output>,
) -> Bool {
    // If they've attached some extra condition, make sure it is satisfied
    expect condition_satisfied(plan.condition, withdrawals)

    // Calculate the amount that is still owned by the owner, and the amount that is now owned by the recipient
    let (lo, hi) = get_bounds(valid_range)
    expect hi - lo <= 60 * 60 * 1000 // tx validity range must be within one hour, so we can rely on the time
    let (owned, sent) = when plan.schedule is {
        Recurring { start, interval, amount, end } -> {
            let periods = (hi - start) / interval
            if hi <= start {
                (value.lovelace_of(utxo.value), 0)
            } else if lo >= end {
                (0, amount * periods)
            } else {
                let sent = amount * periods
                let owned = value.lovelace_of(utxo.value) - sent
                (owned, sent)
            }
        }
        Structured { phases } -> {
            let sent = list.foldl(phases, 0, fn(p, total) { if hi >= p.date { total + p.amount } else { total } })
            let owned = value.lovelace_of(utxo.value) - sent
            (owned, sent)
        }
    }
    // make sure the amount sent to recipient is at least the amount that has been unlocked so far
    let recipient_amount = list.foldl(outputs, 0, fn(o, total) { if o.address == plan.recipient { total + value.lovelace_of(o.value) } else { total } })
    expect recipient_amount >= sent
    // and at least the remainder (minus a fee) must be sent back to the script, or the owner has to sign the tx
    expect [output] = list.filter(outputs, fn(o) { o.address.payment_credential == ScriptCredential(own_script_hash) })
    expect output.datum == utxo.datum
    or {
        multisig.satisfied(plan.owner, signatories, valid_range, withdrawals),
        value.lovelace_of(output.value) >= owned - plan.fee
    }
}