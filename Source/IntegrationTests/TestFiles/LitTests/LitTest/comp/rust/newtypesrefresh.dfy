// RUN: %baredafny run -t:rs --type-system-refresh --general-newtypes "%s"

newtype BoolWrapper = bool {
  const n: int := if this then 1 else 0
  static function True(): BoolWrapper {
    true as BoolWrapper
  }
  function Or(other: BoolWrapper): BoolWrapper {
    if n == 1 then True() else other
  }
}

method Main(){
  expect (true as BoolWrapper).Or(false as BoolWrapper) == (true as BoolWrapper);
  expect (false as BoolWrapper).Or(false as BoolWrapper) == (false as BoolWrapper);
  expect (false as BoolWrapper).Or(true as BoolWrapper) == (true as BoolWrapper);  
}
