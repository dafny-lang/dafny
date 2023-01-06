// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


method SetDifferenceTrigger(
    ghost MainSet: set<object>, Elements: set<object>,
    ghost MainSet2: set<object>, Elements2: set<object>)
  modifies MainSet - Elements
{
  assume forall o: object | o in MainSet2 - Elements2 ::
            o in MainSet - Elements;  // Verified
  forall o <- MainSet2 ensures true {
    if o !in Elements2 {
      assert o in MainSet;
      assert o !in Elements;
    }
  }
}


method SetUnionTrigger(
    ghost MainSet: set<object>, Elements: set<object>,
    ghost MainSet2: set<object>, Elements2: set<object>)
  modifies MainSet - Elements
{
  var p := MainSet - Elements;
  var c := MainSet2 - Elements2;
  assume forall o: object | o in MainSet2 + Elements2 ::
            o in MainSet + Elements;  // Verified
  forall o | o in MainSet2 || o in Elements2 ensures true {
    assert o in MainSet || o in Elements;
  }
}

method SetIntersectionTrigger(
    ghost MainSet: set<object>, Elements: set<object>,
    ghost MainSet2: set<object>, Elements2: set<object>)
  modifies MainSet - Elements
{
  assume forall o: object | o in (MainSet2 * Elements2) ::
            o in MainSet * Elements;  // Verified
  forall o | o in MainSet2 && o in Elements2 ensures true {
    assert o in MainSet && o in Elements;
  }
}

method SetDifferenceElement(
    ghost MainSet: set<object>, Element: object,
    ghost MainSet2: set<object>, Element2: object)
  modifies MainSet - {Element}
{
  var p := MainSet - {Element};
  var c := MainSet2 - {Element2};
  assume c <= p;
  assert forall o: object | o in c ::
            o in p;  // Verified
  assert c == MainSet2 - {Element2}; // Verified
  modify MainSet2 - {Element2}; // Modify error
}

method SetDifference(
    ghost MainSet: set<object>, Elements: set<object>,
    ghost MainSet2: set<object>, Elements2: set<object>)
  modifies MainSet - Elements
{
  var p := MainSet - Elements;
  var c := MainSet2 - Elements2;
  assume c <= p;
  assume forall o: object | o in MainSet2 - Elements2 ::
            o in MainSet - Elements;  // Verified
  assert c == MainSet2 - Elements2; // Verified
  modify MainSet2 - Elements2; // Modify error
}


method SetUnion(
    ghost MainSet: set<object>, Elements: set<object>,
    ghost MainSet2: set<object>, Elements2: set<object>)
  modifies MainSet + Elements
{
  var p := MainSet + Elements;
  var c := MainSet2 + Elements2;
  assume c <= p;
  assume forall o: object | o in MainSet2 + Elements2 ::
            o in MainSet + Elements;  // Verified
  assert c == MainSet2 + Elements2; // Verified
  modify MainSet2 + Elements2; // Modify error
}


method SetIntersection(
    ghost MainSet: set<object>, Elements: set<object>,
    ghost MainSet2: set<object>, Elements2: set<object>)
  modifies MainSet * Elements
{
  var p := MainSet * Elements;
  var c := MainSet2 * Elements2;
  assume c <= p;
  assume forall o: object | o in MainSet2 * Elements2 ::
            o in MainSet * Elements;  // Verified
  assert c == MainSet2 * Elements2; // Verified
  modify MainSet2 * Elements2; // Modify error
}