// RUN: %verify "%s" --allow-warnings > "%t"
// RUN: %diff "%s.expect" "%t"

type t = i:int | 0 <= i < 10

ghost function f():t

ghost function g():int

lemma L1() returns(m:map<int, t>)
{
  m := map i | 0 <= i < 5 :: f(); // FAILS
}

lemma L2() returns(m:map<int, t>)
{
  m := map i | 0 <= i < 5 :: [f()][0]; // SUCCEEDS
}
