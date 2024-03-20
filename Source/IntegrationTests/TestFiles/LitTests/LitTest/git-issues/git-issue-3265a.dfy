// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function F(x: int): set<int>

method MultiSetDifferenceTrigger(
    ghost MainSet: multiset<object>, Elements: multiset<object>,
    ghost MainSet2: multiset<object>, Elements2: multiset<object>)
  modifies MainSet - Elements
{
  assume forall o: object | o in MainSet2 - Elements2 ::
            o in MainSet - Elements;  // Verified
  forall o <- MainSet2
    ensures true
  {
    if Elements2[o] < MainSet2[o] {
      assert o in MainSet - Elements;
    }
  }
}


method MultiSetUnionTrigger(
    ghost MainSet: multiset<object>, Elements: multiset<object>,
    ghost MainSet2: multiset<object>, Elements2: multiset<object>)
  modifies MainSet - Elements
{
  var p := MainSet - Elements;
  var c := MainSet2 - Elements2;
  assume forall o: object | o in MainSet2 + Elements2 ::
            o in MainSet + Elements;  // Verified
  forall o | o in MainSet2 || o in Elements2
    ensures true
  {
    assert o in MainSet || o in Elements;
  }
}

method MultiSetIntersectionTrigger(
    ghost MainSet: multiset<object>, Elements: multiset<object>,
    ghost MainSet2: multiset<object>, Elements2: multiset<object>)
  modifies MainSet - Elements
{
  assume forall o: object | o in MainSet2 * Elements2 ::
            o in MainSet * Elements;  // Verified
  forall o | o in MainSet2 && o in Elements2
    ensures true
  {
    assert o in MainSet && o in Elements;
  }
}

method MultiSetDifferenceElement(
    ghost MainSet: multiset<object>, Element: object,
    ghost MainSet2: multiset<object>, Element2: object)
  modifies MainSet - multiset{Element}
{
  var p := MainSet - multiset{Element};
  var c := MainSet2 - multiset{Element2};
  assume c <= p;
  assert forall o: object | o in c ::
            o in p;  // Verified
  assert c == MainSet2 - multiset{Element2}; // Verified
  modify MainSet2 - multiset{Element2}; // Verified, always worked
}

method MultiSetDifference(
    ghost MainSet: multiset<object>, Elements: multiset<object>,
    ghost MainSet2: multiset<object>, Elements2: multiset<object>)
  modifies MainSet - Elements
{
  var p := MainSet - Elements;
  var c := MainSet2 - Elements2;
  assume c <= p;
  assume forall o: object | o in MainSet2 - Elements2 ::
            o in MainSet - Elements;  // Verified
  assert c == MainSet2 - Elements2; // Verified
  modify MainSet2 - Elements2; // Verified, always worked
}


method MultiSetUnion(
    ghost MainSet: multiset<object>, Elements: multiset<object>,
    ghost MainSet2: multiset<object>, Elements2: multiset<object>)
  modifies MainSet + Elements
{
  var p := MainSet + Elements;
  var c := MainSet2 + Elements2;
  assume c <= p;
  assume forall o: object | o in MainSet2 + Elements2 ::
            o in MainSet + Elements;  // Verified
  assert c == MainSet2 + Elements2; // Verified
  modify MainSet2 + Elements2; // This used to give a modify error
}


method MultiSetIntersection(
    ghost MainSet: multiset<object>, Elements: multiset<object>,
    ghost MainSet2: multiset<object>, Elements2: multiset<object>)
  modifies MainSet * Elements
{
  var p := MainSet * Elements;
  var c := MainSet2 * Elements2;
  assume c <= p;
  assume forall o: object | o in MainSet2 * Elements2 ::
            o in MainSet * Elements;  // Verified
  assert c == MainSet2 * Elements2; // Verified
  modify MainSet2 * Elements2; // This used to give a modify error
}