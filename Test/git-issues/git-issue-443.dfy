// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print F(), " ", G(802.11), "\n";  // 12 15
}

function method F(): int {
  var rx := false;
  assert 20 < 30 by {
    var u := 5.0;  // this once caused a crash in Translator.cs
    assert u < 6.0;
  }
  12
}

function method G<T>(t: T): int {
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
