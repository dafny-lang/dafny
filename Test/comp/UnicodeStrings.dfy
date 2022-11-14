// RUN: %testDafnyForEachCompiler "%s" -- /unicodeChar:1

newtype uint8 = x: int | 0 <= x < 0x100 
newtype uint16 = x: int | 0 <= x < 0x1_0000 
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000 
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000 
newtype int8 = x: int | -0x80 <= x < 0x80
newtype int16 = x: int | -0x8000 <= x < 0x8000
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 8000_0000_0000_0000


// WARNING: Do not do this in real code!
// It's a great example of what NOT to do when working with Unicode,
// since the concept of upper/lower case is culture-specific.
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

  var mightBeString := Some(trickyString);
  print mightBeString, "\n";
  print mightBeString.value, "\n";

  var definitelyString := SomeString(trickyString);
  print definitelyString, "\n";
  print definitelyString.value, "\n";

  var tupleOfString := (trickyString, 42);
  print tupleOfString, "\n";

  CharPrinting();
  CharCasting();
  CharComparisons();
  AllCharsTest();
}

method CharPrinting() {
  var chars := "D\0\r\n\\\"\'\U{1F60E}";
  for i := 0 to |chars| {
    print chars[i], "\n";
  }
  for i := 0 to |chars| {
    var r := Print(chars[i]);
    expect chars[i] == r;
  }
}

method Print<T>(t: T) returns (r: T) {
  print t, "\n";
  return t;
}

method AssertAndExpect(p: bool) 
  requires p
{
  expect p;
}

method CharCasting() {
  // TODO: more edge cases for UTF-8/16
  var chars := "\0azAZ\U{10FFFF}";
  for i := 0 to |chars| {
    CastChar(chars[i]);
  }
}

method CastChar(c: char) {
  if (c as int < 0x80) {
    var asInt8 := c as int8;
    AssertAndExpect(asInt8 as char == c);
  }
  if (c as int < 0x100) {
    var asUint8 := c as uint8;
    AssertAndExpect(asUint8 as char == c);
  }
  if (c as int < 0x8000) {
    var asInt16 := c as int16;
    AssertAndExpect(asInt16 as char == c);
  }
  if (c as int < 0x1_0000) {
    var asUint16 := c as uint16;
    AssertAndExpect(asUint16 as char == c);
  }
  var asInt32 := c as int32;
  AssertAndExpect(asInt32 as char == c);
  var asInt64 := c as int64;
  AssertAndExpect(asInt64 as char == c);
}

method CharComparisons() {
  AssertAndExpect('a' < 'b');
  AssertAndExpect('a' <= 'a');
  AssertAndExpect('b' > 'a');
  AssertAndExpect('b' >= 'b');

  // Some evil edge cases to catch comparing
  // encoded bytes lexicographically by accident 😈.
  // UTF-8 seems to have the property that this comparison
  // is the same, but UTF-16 doesn't.

  // '￮' == [0xFFEE] in UTF-16
  // '𝄞' == [0xD834, 0xDD1E] in UTF-16
  AssertAndExpect('￮' < '𝄞');
}

method AllCharsTest() {
  ghost var allChars := set c: char {:trigger Identity(c)} | true :: Identity(c);
  ghost var allCodePoints := (set cp: int {:trigger Identity(cp)} | 0 <= cp < 0xD800 :: Identity(cp as char))
                     + (set cp: int {:trigger Identity(cp)} | 0xE000 <= cp < 0x11_0000 :: Identity(cp as char));
  assert forall c: char {:trigger Identity(c)} :: 0 <= Identity(c as int) < 0xD800 || 0xE000 <= Identity(c as int) < 0x11_0000;
  assert forall c: char :: Identity(c) in allChars;
  assert allChars == allCodePoints;

  // I'd love to expect allChars == allCodePoints, but that's currently
  // an O(n^2) operation in some runtimes that don't have hashcode-based
  // set operations, and n here is over a million. :P
  // Even just computing allChars at runtime seems to be too slow in Javascript. :(
  // We calculate some small subsets here just as a basic sanity check
  // all AllUnicodeChars() is implemented in the runtimes.
  expect forall c: char {:trigger Identity(c)} :: 0 <= c as int < 0xD800 || 0xE000 <= c as int < 0x11_0000;
}

// Dummy identity function just to enable triggers that Dafny and Boogie are happy with
function method Identity<T>(x: T): T { x }
