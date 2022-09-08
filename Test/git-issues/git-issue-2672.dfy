// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

newtype sreal = r: real | r > -4 as real
newtype sint = r: int | r > -4 as int
newtype ssreal = r: sreal | r > -3 as sreal
newtype ssint = r: sint | r > -3 as sint

method Main() {
  print 24 as real <= 1507 as real, " ";
  print 24 as sreal <= 1507 as sreal, " ";
  print 24 as ssreal <= 1507 as ssreal, " ";
  print 24 as int <= 1507 as int, " ";
  print 24 as sint <= 1507 as sint, " ";
  print 24 as ssint <= 1507 as ssint, " ";
  print 24 as bv16 <= 1507 as bv16, " ";
  print 24 as bv232 <= 1507 as bv232, " ";
  print 24 as char <= 1507 as char, " ";
  print 24 as ORDINAL <= 1507 as ORDINAL, "\n";

  print 24 as real == 1507 as real, " ";
  print 24 as sreal == 1507 as sreal, " ";
  print 24 as ssreal == 1507 as ssreal, " ";
  print 24 as int == 1507 as int, " ";
  print 24 as sint == 1507 as sint, " ";
  print 24 as ssint == 1507 as ssint, " ";
  print 24 as bv16 == 1507 as bv16, " ";
  print 24 as bv232 == 1507 as bv232, " ";
  print 24 as char == 1507 as char, " ";
  print 24 as ORDINAL == 1507 as ORDINAL, "\n";

  print 24 as real >= 1507 as real, " ";
  print 24 as sreal >= 1507 as sreal, " ";
  print 24 as ssreal >= 1507 as ssreal, " ";
  print 24 as int >= 1507 as int, " ";
  print 24 as sint >= 1507 as sint, " ";
  print 24 as ssint >= 1507 as ssint, " ";
  print 24 as bv16 >= 1507 as bv16, " ";
  print 24 as bv232 >= 1507 as bv232, " ";
  print 24 as char >= 1507 as char, " ";
  print 24 as ORDINAL >= 1507 as ORDINAL, "\n";

  print 24 as real < 1507 as real, " ";
  print 24 as sreal < 1507 as sreal, " ";
  print 24 as ssreal < 1507 as ssreal, " ";
  print 24 as int < 1507 as int, " ";
  print 24 as sint < 1507 as sint, " ";
  print 24 as ssint < 1507 as ssint, " ";
  print 24 as bv16 < 1507 as bv16, " ";
  print 24 as bv232 < 1507 as bv232, " ";
  print 24 as char < 1507 as char, " ";
  print 24 as ORDINAL < 1507 as ORDINAL, "\n";

  print 24 as real != 1507 as real, " ";
  print 24 as sreal != 1507 as sreal, " ";
  print 24 as ssreal != 1507 as ssreal, " ";
  print 24 as int != 1507 as int, " ";
  print 24 as sint != 1507 as sint, " ";
  print 24 as ssint != 1507 as ssint, " ";
  print 24 as bv16 != 1507 as bv16, " ";
  print 24 as bv232 != 1507 as bv232, " ";
  print 24 as char != 1507 as char, " ";
  print 24 as ORDINAL != 1507 as ORDINAL, "\n";

  print 24 as real > 1507 as real, " ";
  print 24 as sreal > 1507 as sreal, " ";
  print 24 as ssreal > 1507 as ssreal, " ";
  print 24 as int > 1507 as int, " ";
  print 24 as sint > 1507 as sint, " ";
  print 24 as ssint > 1507 as ssint, " ";
  print 24 as bv16 > 1507 as bv16, " ";
  print 24 as bv232 > 1507 as bv232, " ";
  print 24 as char > 1507 as char, " ";
  print 24 as ORDINAL > 1507 as ORDINAL, "\n";

  print 0 as bv0 <= 0 as bv0, " ";
  print 0 as bv0 == 0 as bv0, " ";
  print 0 as bv0 >= 0 as bv0, "\n";

  print 0 as bv0 < 0 as bv0, " ";
  print 0 as bv0 != 0 as bv0, " ";
  print 0 as bv0 > 0 as bv0, "\n";
}
