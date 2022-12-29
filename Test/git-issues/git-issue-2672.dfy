// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

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
  Print(24 as real <= 1507 as real, " ");
  Print(24 as sreal <= 1507 as sreal, " ");
  Print(24 as ssreal <= 1507 as ssreal, " ");
  Print(24 as int <= 1507 as int, " ");
  Print(24 as sint <= 1507 as sint, " ");
  Print(24 as ssint <= 1507 as ssint, " ");
  Print(24 as bv16 <= 1507 as bv16, " ");
  Print(24 as bv232 <= 1507 as bv232, " ");
  Print(24 as char <= 1507 as char, " ");
  Print(24 as ORDINAL <= 1507 as ORDINAL, "\n");

  Print(24 as real == 1507 as real, " ");
  Print(24 as sreal == 1507 as sreal, " ");
  Print(24 as ssreal == 1507 as ssreal, " ");
  Print(24 as int == 1507 as int, " ");
  Print(24 as sint == 1507 as sint, " ");
  Print(24 as ssint == 1507 as ssint, " ");
  Print(24 as bv16 == 1507 as bv16, " ");
  Print(24 as bv232 == 1507 as bv232, " ");
  Print(24 as char == 1507 as char, " ");
  Print(24 as ORDINAL == 1507 as ORDINAL, "\n");

  Print(24 as real >= 1507 as real, " ");
  Print(24 as sreal >= 1507 as sreal, " ");
  Print(24 as ssreal >= 1507 as ssreal, " ");
  Print(24 as int >= 1507 as int, " ");
  Print(24 as sint >= 1507 as sint, " ");
  Print(24 as ssint >= 1507 as ssint, " ");
  Print(24 as bv16 >= 1507 as bv16, " ");
  Print(24 as bv232 >= 1507 as bv232, " ");
  Print(24 as char >= 1507 as char, " ");
  Print(24 as ORDINAL >= 1507 as ORDINAL, "\n");

  Print(24 as real < 1507 as real, " ");
  Print(24 as sreal < 1507 as sreal, " ");
  Print(24 as ssreal < 1507 as ssreal, " ");
  Print(24 as int < 1507 as int, " ");
  Print(24 as sint < 1507 as sint, " ");
  Print(24 as ssint < 1507 as ssint, " ");
  Print(24 as bv16 < 1507 as bv16, " ");
  Print(24 as bv232 < 1507 as bv232, " ");
  Print(24 as char < 1507 as char, " ");
  Print(24 as ORDINAL < 1507 as ORDINAL, "\n");

  Print(24 as real != 1507 as real, " ");
  Print(24 as sreal != 1507 as sreal, " ");
  Print(24 as ssreal != 1507 as ssreal, " ");
  Print(24 as int != 1507 as int, " ");
  Print(24 as sint != 1507 as sint, " ");
  Print(24 as ssint != 1507 as ssint, " ");
  Print(24 as bv16 != 1507 as bv16, " ");
  Print(24 as bv232 != 1507 as bv232, " ");
  Print(24 as char != 1507 as char, " ");
  Print(24 as ORDINAL != 1507 as ORDINAL, "\n");

  Print(24 as real > 1507 as real, " ");
  Print(24 as sreal > 1507 as sreal, " ");
  Print(24 as ssreal > 1507 as ssreal, " ");
  Print(24 as int > 1507 as int, " ");
  Print(24 as sint > 1507 as sint, " ");
  Print(24 as ssint > 1507 as ssint, " ");
  Print(24 as bv16 > 1507 as bv16, " ");
  Print(24 as bv232 > 1507 as bv232, " ");
  Print(24 as char > 1507 as char, " ");
  Print(24 as ORDINAL > 1507 as ORDINAL, "\n");

  Print(0 as bv0 <= 0 as bv0, " ");
  Print(0 as bv0 == 0 as bv0, " ");
  Print(0 as bv0 >= 0 as bv0, "\n");

  Print(0 as bv0 < 0 as bv0, " ");
  Print(0 as bv0 != 0 as bv0, " ");
  Print(0 as bv0 > 0 as bv0, "\n");
}
