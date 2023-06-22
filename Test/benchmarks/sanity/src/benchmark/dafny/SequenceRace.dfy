

class SequenceRace {

  const s: seq<int>

  constructor() {
    s := [];
    for x := 0 to 1000 {
      s := s + [x];
    }
  }

  method {:benchmark} LazyRace() {
    expect 0 < |s|;
    expect s[0] == 0;
  }

}