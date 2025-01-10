
replaceable module DfyRandom {
  method GetRandomNat(ceiling: nat) returns (r: nat) 
    ensures r < ceiling
}