// NONUNIFORM: Test of Rust's ability to support newtypes
// RUN: %baredafny run -t:rs --type-system-refresh --general-newtypes --enforce-determinism "%s"

newtype BoolWrapper = bool {
  const n: int := if this then 1 else 0
  static function True(): BoolWrapper {
    true as BoolWrapper
  }
  function Or(other: BoolWrapper): BoolWrapper {
    if n == 1 then True() else other
  }
  static const OrFun: (BoolWrapper, BoolWrapper) -> BoolWrapper := 
    (a, b) => a || b

  static function ApplyFalseTrue(f: (BoolWrapper, BoolWrapper) -> BoolWrapper): BoolWrapper {
    f(false as BoolWrapper, true as BoolWrapper)
  }
  
  function xor(other: BoolWrapper): BoolWrapper {
    this != other
  }
}

method Main(){
  expect (true as BoolWrapper).Or(false as BoolWrapper) == (true as BoolWrapper);
  expect (false as BoolWrapper).Or(false as BoolWrapper) == (false as BoolWrapper);
  expect (false as BoolWrapper).Or(true as BoolWrapper) == (true as BoolWrapper);
  expect BoolWrapper.ApplyFalseTrue(BoolWrapper.OrFun) == (true as BoolWrapper);
  var x := true as BoolWrapper;
  if !x {
    expect if !x then false else false;
  } else if x {
    expect if x then true else true;
  }
}
