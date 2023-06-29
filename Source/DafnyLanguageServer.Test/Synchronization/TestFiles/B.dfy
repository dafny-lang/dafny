include "./A.dfy"
module ModB {
  import ModA
  const y := ModA.x + 2
  
  const calledModAFunction := ModA.TakesIdentityAndAppliesIt((x, _) => x, 3)
}

module SpreadOverMultipleFiles.Child2 {
  const x := 3
}