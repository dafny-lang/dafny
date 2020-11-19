const i: bv4 := 9
const j: bv4 := 3

method m() {
  assert i == 25; // error: 25 is out of range for bv4
}
