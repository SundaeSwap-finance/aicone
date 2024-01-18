use aiken/cbor
use aiken/bytearray
use aiken/string

pub const examples_enabled: Int = 1
pub fn trace_example(label: String, a) -> Bool {
    if examples_enabled > 0 {
        trace string.join([label, bytearray.to_hex(cbor.serialise(a))], @": ")
        True
    } else {
        True
    }
}