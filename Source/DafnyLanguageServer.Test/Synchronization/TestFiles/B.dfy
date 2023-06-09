include "./A.dfy"
module ModB {
  import ModA;
  var y = ModA.x + 2;
}
