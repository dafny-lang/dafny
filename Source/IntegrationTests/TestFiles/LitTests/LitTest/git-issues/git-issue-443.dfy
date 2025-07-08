// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

method Main() {
  print F(), " ", G(802.11), "\n";  // 12 15
}

function F(): int {
  var rx := false;
  assert 20 < 30 by {
    var u := 5.0;  // this once caused a crash in Translator.cs
    assert u < 6.0;
  }
  12
}

function G<T>(t: T): int {
  var rx := false;
  assert 20 < 30 by {
    var u: T := t;  // this once caused a crash in Translator.cs
    {
      var v: T := u;
      assert t == v;
      v := t;
      assert t == u;
    }
    assert u == t;
  }
  15
}
