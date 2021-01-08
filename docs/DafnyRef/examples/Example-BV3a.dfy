
const k: bv4 := 9

method p() {
  assert k as bv5 == 9 as bv6; // error: mismatched types
}
