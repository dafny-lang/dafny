// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option<V> = Some(value: V) | None

predicate IsGoodInt(x: int)
{
  && 0 <= x
  && x != 5  // related location
}

predicate IsGoodOpt_Impl(opt: Option<int>)
{
  && (opt.Some? ==> IsGoodInt(opt.value))  // related location
  && (opt.None? ==> true)
}

predicate IsGoodOpt_IfThenElse(opt: Option<int>)
{
  if opt.Some? then
    var x := opt.value;
    IsGoodInt(x)
  else
    true
}

predicate IsGoodOpt_Match(opt: Option<int>)
{
  match opt {
    case Some(x) => IsGoodInt(x)  // related location
    case None => true
  }
}

method Main() {
  var x := Some(5);
  if
  case true =>
    assert IsGoodOpt_Impl(x);  // error
  case true =>
    assert IsGoodOpt_IfThenElse(x);  // error
  case true =>
    assert IsGoodOpt_Match(x);  // error
}
