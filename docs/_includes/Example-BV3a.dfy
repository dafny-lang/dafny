const i: bv4 := 9
const j: bv4 := 3

method p() {
  assert i as bv5 == 9 as bv6; // error: mismatched types
}
