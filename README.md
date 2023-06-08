# aicone

Aiken libraries written and maintained by SundaeSwap Labs

> Note: everything is provided as one library right now, until Aiken supports monorepos.
> see: https://github.com/aiken-lang/aiken/discussions/590

## sundae/multisig

Provides a multisig interface very similar to [Cardano Native Scripts / Simple Scripts](https://github.com/input-output-hk/cardano-node/blob/master/doc/reference/simple-scripts.md#type-sig).

Note: it can't actually be identical to cardano simple scripts, as they use Slots, and plutus scripts don't have access to the slot, only the POSIX time.