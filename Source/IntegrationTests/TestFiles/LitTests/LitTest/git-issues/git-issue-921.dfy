// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


module StringsOfLength {
  type ShortString = s: string | |s| < 10

  method M() {
    var x: ShortString := "Far too long I'm sure you'll agree"; // value does not satisfy the subset constraints of 'ShortString'
  }

  method N() {
    var x2: ShortString := "Far " + "too long " + "I'm sure " + "you'll agree"; // checking append
  }
}

module StringsOfLength2 {
  type ShortString = s: string | |s| <= 2

  method M() {
    var x2: ShortString := "12" + "34";
  }
}

