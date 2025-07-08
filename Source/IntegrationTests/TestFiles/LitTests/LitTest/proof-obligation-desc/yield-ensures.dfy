// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

iterator Repeat0(val: int, count: nat) yields (out: int, index: int)
  yield ensures this.out == val
  yield ensures 0 <= index <= count
{
  for i := 0 to count { yield count, -i; }
}

iterator Repeat1(val: int, count: nat) yields (out: int, index: int)
  yield ensures this.out == val
  yield ensures 0 <= index <= count
{
  for i := 0 to count {
    out := count;
    index := -i;
    yield;
  }
}
