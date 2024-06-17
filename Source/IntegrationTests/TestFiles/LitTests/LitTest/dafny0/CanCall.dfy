// RUN: %testDafnyForEachResolver "%s"


module ModifiesCallee {
  ghost function Wrap(S: set<object>): set<object> {
    S
  }

  method DoWrapped(S: set<object>)
    modifies Wrap(S)
  {
    DoOne(S);
  }

  method DoOne(S: set<object>)
    modifies S
  {
  }
}

module ModifiesCaller {
  ghost function Wrap(S: set<object>): set<object> {
    S
  }

  method DoWrapped(S: set<object>)
    modifies Wrap(S)
  {
  }

  method DoOne(S: set<object>)
    modifies S
  {
    DoWrapped(S);
  }
}

module ArraySeqInit {
  function F(a: int): int {
    45
  }

  method TestArrayF() {
    var m := new int[3](F);
    assert m[0] == 45;
  }

  method TestArrayLambda() {
    var m := new int[3](_ => 45);
    assert m[0] == 45;
  }

  method TestSeqF() {
    var m := seq(3, F);
    assert m[0] == 45;
  }

  method TestSeqLambda() {
    var m := seq(3, _ => 45);
    assert m[0] == 45;
  }

}
