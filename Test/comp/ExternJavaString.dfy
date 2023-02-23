// RUN: %dafny /compile:3 /compileTarget:java "%s" %S/Conversions.java %S/ExternJavaString.java > "%t"
// RUN: %diff "%s.expect" "%t"
// In this example, the extern method obtains a Java string and returns it as such.
// The Dafny code converts that Java string to a Dafny string.

class {:extern "java.lang.String"} JavaString {
  ghost const value: string
}

// Note, the following has to be a method, not a function, because the reference it
// returns is not determined functionally from the input argument.
method {:extern "Util.Conversions", "ToJavaString"} ToJavaString(s: string) returns (js: JavaString)
  ensures js.value == s

// The conversion this way can be a function.
function {:extern "dafny.DafnySequence", "asString"} ToDafnyString(js: JavaString): string
  ensures ToDafnyString(js) == js.value

method {:extern "dafny.ExternJavaString", "getStringFromFile"} GetStringFromFile() returns (js: JavaString)

method Main() {
  var js := GetStringFromFile();
  var s := ToDafnyString(js);

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
