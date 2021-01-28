const i: bv4 := 9
const j: bv4 := 3

method m() {
  assert (i & j) == (1 as bv4);
  assert (i | j) == (11 as bv4);
  assert (i ^ j) == (10 as bv4);
  assert !i == (6 as bv4);
  assert -i == (7 as bv4);
  assert (i + i) == (2 as bv4);
  assert (j - i) == (10 as bv4);
  assert (i * j) == (11 as bv4);
  assert (i as int) / (j as int) == 3;
  assert (j << 1) == (6 as bv4);
  assert (i << 1) == (2 as bv4);
  assert (i >> 1) == (4 as bv4);
  assert i == 9; // auto conversion of literal to bv4
  assert i * 4 == j + 8 + 9; // arithmetic is modulo 16
  assert i + j >> 1 == (i + j) >> 1; // + - bind tigher than << >> 
  assert i + j ^ 2 == i + (j^2); 
  assert i * j & 1 == i * (j&1); // & | ^ bind tighter than + - *
}
