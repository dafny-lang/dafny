// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


ghost function f(i:nat, j:nat):int {if i == 0 then 0 else f(i - 1, i * j + 1) + f(i - 1, 2 * i * j)}

lemma{:resource_limit 10000000} L()
{
  assert f(10, 5) == 0;
}
