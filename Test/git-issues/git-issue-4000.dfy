// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Gas {
    const STATICCALL : nat := 0xfa

    function f(op: nat, s: int): int
    {
        match op
            case STATICCALL => 0
            case _ => s
    }

    lemma MatchIsCorrect() {
      assert f(0, 2) == 2;
    }
}