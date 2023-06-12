include "./A.dfy"
module ModB {
  import ModA
  const y := ModA.x + 2;
}
