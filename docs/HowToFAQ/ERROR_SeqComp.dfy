function f(i: int): int
  requires i < 10 
{
  i
}

method test() {
  var s := seq(5, i => f(i));
}
