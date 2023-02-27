// RUN: %translate go --unicode-char:false "%s" > "%t"
// RUN: %translate go --unicode-char:true "%s" >> "%t"
// RUN: %diff "%s.expect" "%t" 

method Main() {
  var s := Foo();
}

// An extern method that returned a string used to cause
// an internal contract violation and nonsensical errors like
// "Error: Cannot convert from string to seq<char>"

method {:extern "foo"} Foo() returns (s: string)

method Bar() returns (s: string) {
  return "hello";
}
