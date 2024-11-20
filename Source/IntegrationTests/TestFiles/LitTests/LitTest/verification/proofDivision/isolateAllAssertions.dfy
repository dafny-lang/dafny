// RUN: ! %verify --progress VerificationJobs --cores=1 %s &> %t.raw
// RUN: %sed 's#\(time.*\)#<redacted>#g' %t.raw > %t
// RUN: %diff "%s.expect" "%t"


method {:isolate_assertions} Foo(x: int) returns (r: int) 
  ensures r > 3
  ensures r < 10 
{
  assert true;
  assert true;
  if (x == 3) {
    return 7;
  } else {
    return 12;
  }
}

method Bar() {
  assert true;
  assert true;
}
