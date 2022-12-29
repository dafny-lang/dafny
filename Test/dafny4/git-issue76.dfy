// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=py "%s" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  M0();
  M1();
  EqualityOfStrings0();
  EqualityOfStrings1();
}

// The verification of the following methods requires knowledge
// about the injectivity of sequence displays.

method M0()
{
  assert {"x","y","z"}-{"y"} == {"x","z"};
}

method M1()
{
  var n :| ("R",n) in {("R",2),("P",1)};
  assert n == 2;
  print n, "\n";
}

method EqualityOfStrings0() {
  assert "a" != "b";
}

method EqualityOfStrings1() {
  assert "a" + "b" == "ab";
}

method M2()
{
  assert !( [0,0] in {[0,2],[1,2]} );
}

method M3()
{
  assert [0,0] !in {[0,2],[1,2]};
}
