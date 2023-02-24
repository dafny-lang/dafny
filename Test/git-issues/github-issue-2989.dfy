// RUN: %translate go --unicode-char:false "%s" > "%t"
// RUN: %translate go --unicode-char:true "%s" >> "%t"
// RUN: %diff "%s.expect" "%t" 

method Main() {
  var s := Foo();
}

method {:extern "foo"} Foo() returns (s: string)

method Bar() returns (s: string) {
  return "hello";
}
