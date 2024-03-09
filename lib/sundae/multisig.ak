use aiken/interval.{Finite, Interval, IntervalBound}
use aiken/list
use aiken/dict.{Dict}
use aiken/time.{PosixTime}
use aiken/transaction.{ValidityRange}
use aiken/transaction/credential.{StakeCredential, Inline, ScriptCredential}

pub type MultisigScript {
  Signature { key_hash: ByteArray }
  AllOf { scripts: List<MultisigScript> }
  AnyOf { scripts: List<MultisigScript> }
  AtLeast { required: Int, scripts: List<MultisigScript> }
  Before { time: PosixTime }
  After { time: PosixTime }
  Script { script_hash: ByteArray }
}

pub fn satisfied(
  script: MultisigScript,
  signatories: List<ByteArray>,
  valid_range: ValidityRange,
  withdrawals: Dict<StakeCredential, Int>,
) -> Bool {
  when script is {
    Signature { key_hash } -> list.has(signatories, key_hash)
    AllOf { scripts } ->
      list.all(scripts, fn(s) { satisfied(s, signatories, valid_range, withdrawals) })
    AnyOf { scripts } ->
      list.any(scripts, fn(s) { satisfied(s, signatories, valid_range, withdrawals) })
    AtLeast { required, scripts } ->
      required <= list.count(
        scripts,
        fn(s) { satisfied(s, signatories, valid_range, withdrawals) },
      )
    // TODO: could be simplified with https://github.com/aiken-lang/aiken/issues/566
    Before { time } ->
      when valid_range.upper_bound.bound_type is {
        Finite(hi) ->
          if valid_range.upper_bound.is_inclusive {
            hi <= time
          } else {
            hi < time
          }
        _ -> False
      }
    After { time } ->
      when valid_range.lower_bound.bound_type is {
        Finite(lo) ->
          if valid_range.lower_bound.is_inclusive {
            time <= lo
          } else {
            time < lo
          }
        _ -> False
      }
    Script { script_hash } -> dict.has_key(withdrawals, Inline(ScriptCredential(script_hash)))
  }
}