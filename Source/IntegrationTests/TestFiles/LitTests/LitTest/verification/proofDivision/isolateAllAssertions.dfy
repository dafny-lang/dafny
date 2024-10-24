// RUN: %verify --progress VerificationJobs --cores=1 %s &> %t.raw
// RUN: %sed 's#\(time.*\)#<redacted>#g' %t.raw > %t
// RUN: %diff "%s.expect" "%t"




method {:isolate_assertions} Foo() {
  assert true;
  assert true;
}

method Bar() {
  assert true;
  assert true;
}
