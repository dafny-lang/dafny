// RUN: %testDafnyForEachResolver "%s"


type lowercase = ch | 'a' <= ch <= 'z' witness 'd'

method InitTests() {
  var aa := new lowercase[3];
  var s := "hello";
  aa := new lowercase[|s|](i requires 0 <= i < |s| => s[i]);
}

