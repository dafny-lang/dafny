// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

datatype Wrapper<T> = Wrapper(s: seq<T>)
{
  static function empty(): Wrapper<T> {
    Wrapper([])
  }
}

datatype Wrapper2<T> = Wrapper2(s: seq<T>, t: T)
{
  static function empty(t: T): Wrapper2<T> {
    Wrapper2([], t)
  }
}

method Main() {
  var xs: Wrapper<nat> := Wrapper<nat>.empty();
  var xs2: Wrapper2 := Wrapper2.empty(2792);
  print xs, " ", xs2, "\n"; // [] Wrapper2([], 2792)
}
