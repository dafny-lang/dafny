// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Gas {
    type State = ()
    const STATICCALL : nat := 0xfa

    function f(op: nat, s: State): State
    {
        match op
            case STATICCALL => s
            case _ => s
    }
}