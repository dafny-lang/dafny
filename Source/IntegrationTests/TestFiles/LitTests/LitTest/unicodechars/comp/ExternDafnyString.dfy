// RUN: %dafny /compile:3 /unicodeChar:1 /compileTarget:java "%s" %S/ExternDafnyString.java > "%t"
// RUN: %diff "%s.expect" "%t"
// In this example, the extern method obtains a Java string and returns it as a Dafny string.

class {:extern "java.lang.String"} JavaString {
  ghost const value: string
}

method {:extern "dafny.ExternDafnyString", "getStringFromFile"} GetStringFromFile() returns (s: string)

method Main() {
  var s := GetStringFromFile();

  var previousStart := 0;
  for i := 0 to |s|
    invariant previousStart <= i
  {
    if s[i] == '/' {
      print s[previousStart..i], "\n";
      previousStart := i + 1;
    }
  }
  if previousStart != |s| {
    print s[previousStart..], "\n";
  }
}
