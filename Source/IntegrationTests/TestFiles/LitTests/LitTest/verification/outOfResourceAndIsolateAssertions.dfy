// RUN: ! %verify --isolate-assertions --cores=1 --progress "%s" &> "%t"
// RUN: %OutputCheck --file-to-check "%t" "%S/Inputs/outOfResourceAndIsolateAssertions.check"


ghost function f(i:nat, j:nat):int {if i == 0 then 0 else f(i - 1, i * j + 1) + f(i - 1, 2 * i * j)}

lemma{:resource_limit 10000000} L()
{
  assert true;
  assert f(10, 5) == 0; // runs out of resources
  assert true;
  assert f(10, 6) == 0; // runs out of resources
}
