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
