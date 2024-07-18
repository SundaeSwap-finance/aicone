use aiken/list
use aiken/transaction.{ScriptContext, WithdrawFrom, Publish}
use aiken/transaction/certificate.{CredentialRegistration, CredentialDeregistration, CredentialDelegation}

validator(owner: ByteArray, delegator: ByteArray) {
    fn stake(_r: Data, ctx: ScriptContext) -> Bool {
        when ctx.purpose is {
            WithdrawFrom(_) -> {
                list.has(ctx.transaction.extra_signatories, owner)
            }
            Publish(cert) -> {
                when cert is {
                    CredentialRegistration(_) | CredentialDeregistration(_) -> {
                        list.has(ctx.transaction.extra_signatories, owner)
                    }
                    CredentialDelegation(_, _) -> {
                        list.has(ctx.transaction.extra_signatories, delegator)
                    }
                    _ -> False
                }
            }
            _ -> False
        }
    }
}
