// RUN: %build -t:lib "%S/Inputs/generatesUnderscoreVariables.dfy" --output "%S/Build/function" > "%t"
// RUN: %resolve "%s" "%S/Build/function.doo" >> "%t"
// RUN: %diff "%s.expect" "%t"

lemma TestInjective() {
  assert Injective<int, int>((x) => x + 2);
  var square := (x: int) => x * x;
  assert square(-1) == square(1);
  assert !Injective<int, int>((x) => x * x);
}