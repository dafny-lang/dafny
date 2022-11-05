// RUN: %testDafnyForEachCompiler "%s" -- /unicodeChar:1

// TODO:
// * AllChars()
// * Character literal escape testing (\U doesn't always work in C#)
// * Main method arguments


newtype uint32 = x: int | 0 <= x < 0x1_0000_0000
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

// WARNING: Do not do this in real code!
// It's a great example of what NOT to do when working with Unicode,
// since the concept of upper/lower case is culture-specific.
// TODO: more thorough testing of comparators, especially
// edge cases where lexicographic comparision of UTF-8/16 would get the wrong answer.
function method ToLower(ch: char): char {
  if 'A' <= ch <= 'Z' then
    ch - 'A' + 'a'
  else
    ch
}

function method MapToLower(s: string): string {
  if 0 == |s| then
    []
  else
    [ToLower(s[0])] + MapToLower(s[1..])
}

function method MapToInt32(s: string): seq<int32> {
  if 0 == |s| then
    []
  else
    [s[0] as int32] + MapToInt32(s[1..])
}

datatype Option<T> = Some(value: T) | None

datatype StringOption = SomeString(value: string) | NoString

method Main(args: seq<string>) {
  var trickyString := "Dafny is just so \U{1F60E}";
  print trickyString, "\n";

  var trickyString2 := "Dafny is just so " + [0x1F60E as char];
  print trickyString2, "\n";

  // Testing that runtimes don't confuse a seq<uint32> for a string
  // (which would be a problem if we used Int32 in C# instead of Rune, for example)
  var s := "Ceci n'est pas une string";
  var notAString := MapToInt32(s);
  print notAString, "\n";

  // Ensuring character arithmetic can be compiled
  var sarcastic := "Oh UNicOdE, tHaT's a REaL usEFuL FEaTuRe!";
  var sincere := MapToLower(sarcastic);
  print sincere, "\n";

  print 'D', "\n";
  // TODO:
  // print '\'', "\n";
  // print '\n', "\n";

  var mightBeString := Some(trickyString);
  print mightBeString, "\n";
  print mightBeString.value, "\n";

  var definitelyString := SomeString(trickyString);
  print definitelyString, "\n";
  print definitelyString.value, "\n";

  var tupleOfString := (trickyString, 42);
  print tupleOfString, "\n";

  Print("D");
  Print('D');
  Print(0x1F60E as char);

  AllCharsTest();
}

method Print<T>(t: T) {
  print t, "\n";
}

method AllCharsTest() {
  var allChars := set c: char | true;
  var allCodePoints := (set cp: int | 0 <= cp < 0xD800 :: cp as char)
                     + (set cp: int | 0xE000 <= cp < 0x11_0000 :: cp as char);
  // TODO:
  // assert allChars == allCodePoints;
  expect |allChars| == |allCodePoints|;
  expect allChars == allCodePoints;

}
