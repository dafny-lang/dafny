const i: bv4 := 9
const j: bv4 := 3

method m() {
  assert i & 4 | j == 0 ; // parentheses required
  assert i as bv5 == 9 as bv6; // error: mismatched types
}
