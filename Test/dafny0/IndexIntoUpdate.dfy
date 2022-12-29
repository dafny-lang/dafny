// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
method M()  {
  var s := [1, 2, 3, 4];
  assert 3 in s;
  s := s[0 := 1];
  if * { assert 3 in s; } // FIXME: This should verify
  else { assert s[2] == 3; assert 3 in s; }
}
