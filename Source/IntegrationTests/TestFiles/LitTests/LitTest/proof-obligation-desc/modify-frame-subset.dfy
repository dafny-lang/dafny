// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var x: int
  var y: int
}

method ModifyStmt(s: seq<C>)
  requires |s| > 5
  modifies s[3]
  modifies {s[4]}`x
  modifies {s[5]}`y
{
  modify s[0], {s[1]}`x, {s[2]}`y;
}

method LoopModifies(s: seq<C>)
  requires |s| > 5
  modifies s[3]
  modifies {s[4]}`x
  modifies {s[5]}`y
{
  for i := 0 to 3
    modifies s[0], {s[1]}`x, {s[2]}`y
  { }
}

method Callee(s': seq<C>)
  requires |s'| > 5
  modifies s'[0], {s'[1]}`x, {s'[2]}`y

method Caller(s: seq<C>)
  requires |s| > 5
  modifies s[3]
  modifies {s[4]}`x
  modifies {s[5]}`y
{
  Callee(s);
}
