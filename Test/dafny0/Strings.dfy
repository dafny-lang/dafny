// RUN: %testDafnyForEachCompiler "%s" -- --unicode-char=false

method Char(a: char, s: string, i: int) returns (b: char)
{
  var ch: char := *;
  if a == ch {
    b := ch;
  } else if 0 <= i < |s| {
    b := s[i];
  } else {
    b := *;
  }
}

// An attribute parameter that is a string literal is passed down
// to Boogie as a string literal.
method {:MyAttribute "hello", "hi" + "there", 57} AttrTest()
{
}

method M(a: char, b: char) returns (s: string, t: seq<char>)
  ensures |s| == 3 ==> t == [a, b, b];
{ 
  s := *;
  s := s + [a, b, b] + s;
  t := s;
  s := t[0..|s|];
}

// Note that actually printing strings with non-ASCII characters
// is currently inconsistent across both languages and platforms.
// See https://github.com/dafny-lang/dafny/pull/2938 for an
// attempt to fix this that had to be reverted.
// For now we're just making runtimes assertions about the contents of
// strings rather than printing them and relying on the diff with the expect file.
method Main()
{
  var ch: char := *;
  var s, t := M(ch, ch);
  print "ch = ", ch, "\n";
  print "The string is: " + s + "\n";
  var x, y, z, zz := Escapes();
  print "Escape X: ", x, "\n";
  print "Escape Y: ", y, "\n";
  print "Escape Z: ", z, "\n";
  // TODO: Won't work until https://github.com/dafny-lang/dafny/issues/2999 is addressed
  // print "Escape ZZ: ", zz, "\n";
  var c, d := CharEscapes();
  print "Here is the end" + [c, d] + [' ', ' ', ' '] + [[d]][0] + "   ", d, "\n";

  // Testing non-ASCII characters directly in string literals.
  // Code points outside the BMP are still not supported.
  // See https://github.com/dafny-lang/dafny/issues/818.
  
  var coffeeInvitation :=  "Let's go to the café";
  assert |coffeeInvitation| == 20;
  expect |coffeeInvitation| == 20;
  assert coffeeInvitation[19] == 'é';
  expect coffeeInvitation[19] == 'é';

  var firstNonAsciiChar := "Ā";
  assert |firstNonAsciiChar| == 1;
  expect |firstNonAsciiChar| == 1;
  assert firstNonAsciiChar[0] == 'Ā';
  expect firstNonAsciiChar[0] == 'Ā';

  // Something above the surrogate range,
  // and a verbatim string to make sure that's handled as well.
  var highBMPChar := @"￮";
  assert |highBMPChar| == 1;
  expect |highBMPChar| == 1;
  assert highBMPChar[0] == 0xFFEE as char;
  expect highBMPChar[0] == 0xFFEE as char;
  
  // Testing invalid UTF-16 content that Dafny allows (when --unicode-char=false)

  var x?, y?, z? := WeirdStrings();
  
  expect |x?| == 30;
  expect x?[29] as int == 55296;
  expect |y?| == 30;
  expect x?[29] as int == 55296;
  expect |z?| > 2;
  expect z?[0..2] == ['\ude0e', '\ud83d'];

  var c?, d? := WeirdChars();
  expect c? == 0xD800 as char;
  expect d? == '\uDFFF';

  // Ensuring we're precise enough about identifying \u escapes
  print "I'm afraid you'll find escape quite impossible, \\u007", "\n";
  print "Luckily I have this nifty gadget from my good friend, \\\u0051", "\n";

  AllCharsTest();
}

method GimmieAChar(s: string) returns (ch: char)
{
  if s == "" {
    ch := "tn"[1];
    assert ch == "nt"[0];
  } else {
    var i :| 0 <= i < |s|;  // if guard guarantees such an i exists
    ch := s[i];
  }
}

method Escapes() returns (x: string, y: string, z: string, zz: string)
  ensures |zz| > 2
{
  x := "I say \"hello\" \\ you say \'good bye'";
  y := @"I say ""hello"" \ you say 'good bye'";
  assert x == y;
  z := "There needs to be \u0052\u0026\u0044\n\tYes, sir";
  zz := "\ud83d\ude0e is the UTF-16 for a very cool emoji";
}

method CharEscapes() returns (c: char, d: char)
{
  // cool variable names, huh?
  var 'x := 'R';
  var x' := '\u0052';
  assert 'x==x' ;
  c := '\n';
  d := '*';
}

// Strings that aren't valid UTF-16 sequences
method WeirdStrings() returns (x: string, y: string, z: string)
{
  x := "What even is this character: \uD800";
  y := "What even is this character: " + [0xD800 as char];
  assert x == y;
  z := "\ude0e\ud83d is not using surrogates correctly";
}

// Surrogate code points
method WeirdChars() returns (c: char, d: char)
{
  c := '\uD800';
  d := 0xDFFF as char;
}

method AllCharsTest() {
  var allChars := set c: char {:trigger Identity(c)} | true :: Identity(c);
  var allUTF16CodeUnits := set cp: int {:trigger Identity(cp)} | 0 <= cp < 0x1_0000 :: Identity(cp as char);
  assert forall c: char {:trigger Identity(c)} :: 0 <= Identity(c as int) < 0x1_0000;
  assert forall c: char :: Identity(c) in allChars;
  assert allChars == allUTF16CodeUnits;

  // I'd love to expect allChars == allCodePoints, but that's currently
  // an O(n^2) operation in some runtimes that don't have hashcode-based
  // set operations, and n here is 2^16. :P
  expect |allChars| == |allUTF16CodeUnits|;
}

function Identity<T>(x: T): T { x }

method CharsAndArrows() {
  var lambda := (c: char) requires c <= 'Z' => c + 1 as char;
  var fromLambda := lambda('C');
  print fromLambda, "\n";

  var funcRef := IncrementChar;
  var fromFuncRef := funcRef('C');
  print fromFuncRef, "\n";
}

function IncrementChar(c: char): char 
  requires c <= 'Z'
{
  c + 1 as char
}
