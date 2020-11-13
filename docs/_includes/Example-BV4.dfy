const i: bv4 := 9
const j: bv4 := 3

method m() {
  assert i as bv3 == 1; // error: i is out of range for bv3
}
