// RUN: ! %verify --isolate-assertions --cores=1 --progress VerificationJobs "%s" &> %t.raw
// RUN: %sed 's#\(time.*\)#<redacted>#g' %t.raw > %t
// RUN: %diff "%s.expect" "%t"
ghost function f(i:nat, j:nat):int {
  if i == 0 then 0 else f(i - 1, i * j + 1) + f(i - 1, 2 * i * j)
}
lemma{:resource_limit 10000000} L()
{
  assert true;
  assert f(10, 5) == 0; // runs out of resources
  assert true;
  assert f(10, 6) == 0; // runs out of resources
}
