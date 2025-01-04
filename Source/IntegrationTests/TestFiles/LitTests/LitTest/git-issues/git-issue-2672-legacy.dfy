// RUN: %testDafnyForEachCompiler "%s" -- --type-system-refresh=false --general-newtypes=false

newtype sreal = r: real | r > -4 as real
newtype sint = r: int | r > -4 as int
newtype ssreal = r: sreal | r > -3 as sreal
newtype ssint = r: sint | r > -3 as sint

method Print(b: bool, end: string)
  // Print boolean `b` as `true` or `false`, then print `end`.  This is needed
  // by C++ due to BUG(https://github.com/dafny-lang/dafny/issues/2773).
{
  if b {
    print "true";
  } else {
    print "false";
  }
  print end;
}

method Main() {
  Print(24 as sreal <= 1507 as sreal, " ");
  Print(24 as ssreal <= 1507 as ssreal, "\n");

  Print(24 as sreal == 1507 as sreal, " ");
  Print(24 as ssreal == 1507 as ssreal, "\n");

  Print(24 as sreal >= 1507 as sreal, " ");
  Print(24 as ssreal >= 1507 as ssreal, "\n");

  Print(24 as sreal < 1507 as sreal, " ");
  Print(24 as ssreal < 1507 as ssreal, "\n");

  Print(24 as sreal != 1507 as sreal, " ");
  Print(24 as ssreal != 1507 as ssreal, "\n");

  Print(24 as sreal > 1507 as sreal, " ");
  Print(24 as ssreal > 1507 as ssreal, "\n");
}
