// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s" -- --allow-deprecation


// Imported from bug 76. LitInt would be triggered on, causing matching failures.

ghost predicate P(x:int, y:int)

lemma L1(x:int, y:int)
    requires y == 2;
    requires forall i :: P(i, 3);
{
    assert P(x, y + 1);
}

lemma L2(x:int, y:int)
    requires y == 2;
    requires forall i {:trigger P(i, 3)} :: P(i, 3);
{
    assert P(x, y + 1);
}

lemma L3(x:int, y:int)
    requires y == 2;
    requires forall i :: P(i, 3);
{
    var dummy := 3;
    assert P(x, y + 1);
}

lemma L4(x:int, y:int)
    requires y == 2;
    requires forall i, j :: j == 3 ==> P(i, j);
{
    assert P(x, y + 1);
}

// Include "this" among parameters of lit axioms

datatype Tree = Empty | Node(left: Tree, right: Tree)
{
  ghost function Elements(): set<int>
    decreases this
  {
    match this
    case Empty => {}
    case Node(left, right) => left.Elements() + right.Elements()
  }
}

ghost function Sum(t: Tree): int
ghost predicate IsEven(x: int)

lemma TimesOut(t: Tree)
  requires forall u :: u in t.Elements() ==> IsEven(u)
{
  assert t.Node? ==> IsEven(Sum(t));  // error (but this once used to time out due to bad translation of member functions)
}
