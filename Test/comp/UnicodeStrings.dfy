// RUN: %testDafnyForEachCompiler "%s" -- /unicodeChar:1

method AssertAndExpect(p: bool) 
  requires p
{
  expect p;
}

// Included to test casting between char and all supported native types
newtype uint8 = x: int | 0 <= x < 0x100 
newtype uint16 = x: int | 0 <= x < 0x1_0000 
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000 
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000 
newtype int8 = x: int | -0x80 <= x < 0x80
newtype int16 = x: int | -0x8000 <= x < 0x8000
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 8000_0000_0000_0000

const AllCasesAsCodePoints := [
  0,        // \0, minimum value
  0x9,      // \t
  0xA,      // \n
  0xD,      // \r
  0x22,     // \"
  0x27,     // \'
  0x44,     // \\
  0x5c,     // D (because Dafny)
  0x80,     // First non-ASCII codepoint (and hence first with two bytes in UTF-8)
  0xFF,     // Last codepoint that could fit into a single byte
  0x100,    // First codepoint that can't fit into a single byte
  0xD7FF,   // Last codepoint before the surrogate range
  0xE000,   // First codepoint after the surrogate range
  0xFFEE,   // '￮', which is after the surrogate range but a single code unit in UTF-16
  0x1_0000, // First codepoint beyong the BMP, requiring two UTF-16 code units
  0x1_D11E, // '𝄞', [0xD834, 0xDD1E] in UTF-16
            // Included along with ￮ as an evil test case to catch comparing
            // encoded bytes lexicographically by accident 😈.
            // UTF-8 seems to have the property that this comparison
            // is the same, but UTF-16 doesn't.
  0x1_F680, // Typical non-BMP codepoint (🚀)
  0x10_FFFF // Maximum value
];


// The primary definition of the character values is casting to characters from integers.
// This is the simplest and most likely to be correct at runtime, and used as the baseline for comparisons.
const AllCases := 
  seq(|AllCasesAsCodePoints|, i requires 0 <= i < |AllCasesAsCodePoints| => AllCasesAsCodePoints[i] as char)

const AlternateForms: seq<seq<char>> := [
  // As character literals with escapes
  ['\0', '\t', '\n', '\r', '\"', '\'', '\U{44}', '\\', '\U{80}', '\U{FF}',
      '\U{100}', '\U{D7FF}', '\U{E000}', '\U{FFEE}', '\U{10000}', '\U{1D11E}', '\U{1F680}', '\U{10FFFF}'],
  // As verbatim character literals where reasonable, or using a \U escape where not
  ['\U{0}', '\U{9}', '\U{A}', '\U{D}', '\U{22}', '\U{27}', 'D', '\U{5c}', 
      '', 'ÿ', 'Ā', '\U{D7FF}', '\U{E000}', '￮', '𐀀', '𝄞', '🚀', '\U{10FFFF}'],
  // In a string literal with escapes
  "\0\t\n\r\"\'\U{44}\\\U{80}\U{FF}\U{100}\U{D7FF}\U{E000}\U{FFEE}\U{10000}\U{1D11E}\U{1F680}\U{10FFFF}",
  // In a string literal without escapes where reasonable
  "\U{0}\U{9}\U{A}\U{D}\U{22}\U{27}D\U{5c}ÿĀ\U{D7FF}\U{E000}￮𐀀𝄞🚀\U{10FFFF}"
]

method AllCharCasesTest() {
  // Boy a foreach loop would be really nice right about now... \U{1F604}
  for caseIndex := 0 to |AllCases| {
    var thisCase := AllCases[caseIndex];
    for formIndex := 0 to |AlternateForms| {
      expect thisCase == AlternateForms[formIndex][caseIndex];
      expect !(thisCase != AlternateForms[formIndex][caseIndex]);
      
      expect AlternateForms[formIndex][caseIndex] == thisCase;
      expect !(AlternateForms[formIndex][caseIndex] != thisCase);

      CastChar(thisCase);
    }
  }

  // Comparisons - taking advantage of the list of cases being in ascending order
  for i := 0 to |AllCases| {
    var left := AllCases[i];
    for j := 0 to |AllCases| {
      var right := AllCases[j];
      if i < j {
        expect left < right;
        expect left <= right;
        expect !(left == right);
        expect left != right;
        expect !(left > right);
        expect !(left >= right);
      } else if i == j {
        expect !(left < right);
        expect left <= right;
        expect left == right;
        expect !(left != right);
        expect !(left > right);
        expect left >= right;
      } else {
        expect !(left < right);
        expect !(left <= right);
        expect !(left == right);
        expect left != right;
        expect left > right;
        expect left >= right;
      }
    }
  }
}

// WARNING: Do not do this in real code!
// It's a great example of what NOT to do when working with Unicode,
// since the concept of upper/lower case is culture-specific.
function ToLower(ch: char): char {
  if 'A' <= ch <= 'Z' then
    ch - 'A' + 'a'
  else
    ch
}

function MapToLower(s: string): string {
  if 0 == |s| then
    []
  else
    [ToLower(s[0])] + MapToLower(s[1..])
}

function MapToInt32(s: string): seq<int32> {
  if 0 == |s| then
    []
  else
    [s[0] as int32] + MapToInt32(s[1..])
}

method Main(args: seq<string>) {
  AllCharCasesTest();
  CharQuantification();
  StringPrinting();
  CharPrinting();
}

// Not including any non-printable characters in this one
const stringThatNeedsEscaping := "D\0\r\n\\\"\'\U{1F60E}";

method CharPrinting() {
  var chars := stringThatNeedsEscaping;
  for i := 0 to |chars| {
    print chars[i], "\n";
  }
  for i := 0 to |chars| {
    var r := Print(chars[i]);
    expect chars[i] == r;
  }
}

// Used to ensure characters can be passing in and out of generic code
// (which is a real challenge in Java for example)
method Print<T>(t: T) returns (r: T) {
  print t, "\n";
  return t;
}

datatype Option<T> = Some(value: T) | None

datatype StringOption = SomeString(value: string) | NoString

method StringPrinting() {
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

  // Exercising the new rules for how strings are printed,
  // namely that a string is only printed verbatim if the value
  // is statically known to be a seq<char>

  var mightBeString := Some(trickyString);
  print mightBeString, "\n";
  print mightBeString.value, "\n";

  // Note that the string is printed as a string, but with double quotes and escaping
  var definitelyString := SomeString(stringThatNeedsEscaping);
  print definitelyString, "\n";

  var tupleOfString := (stringThatNeedsEscaping, 42);
  print tupleOfString, "\n";
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
  var asInt := c as int;
  AssertAndExpect(asInt as char == c);
  var asReal := c as real;
  AssertAndExpect(asReal as char == c);
}

// Testing that the runtime implementation of AllChars() is correct
method CharQuantification() {
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
  // It seems to be fast enough just to iterate over all characters though.
  expect forall c: char {:trigger Identity(c)} :: 0 <= c as int < 0xD800 || 0xE000 <= c as int < 0x11_0000;
}

// Dummy identity function just to enable triggers that Dafny and Boogie are happy with
function Identity<T>(x: T): T { x }
