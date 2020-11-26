const j: bv4 := 9

method n() {
  assert j == 25; // error: 25 is out of range for bv4
}
