

class {:benchmark} SequenceRace {

  const s: seq<int>

  constructor() {
    s := [];
    for x := 0 to 1000 {
      s := s + [x];
    }
  }

  method LazyRace() {
    // Using expect means compilers can't optimize calculations away
    // since they could lead to throwing exceptions
    expect 0 < |s|;
    expect s[0] == 0;
  }

}