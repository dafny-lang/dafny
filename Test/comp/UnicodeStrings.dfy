// RUN: %baredafny verify --unicode-char "%s" %args > "%t"
// RUN: %baredafny run --no-verify --unicode-char --target:cs "%s" %args >> "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint32 = x: int | 0 <= x < 0x1_0000_0000
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

// WARNING: Do not do this in real code!
// It's a great example of what NOT to do when working with Unicode,
// since the concept of upper/lower case is culture-specific.
function method toLower(ch: char): char {
  if 'A' <= ch <= 'Z' then
    ch - 'A' + 'a'
  else
    ch
}

method Main(args: seq<string>) {
  var trickyString := "Dafny is just so \U{1F60E}";
  print trickyString, "\n";

  var trickyString2 := "Dafny is just so " + [0x1F60E as char];
  print trickyString2, "\n";

  // Testing that runtimes don't confuse a seq<uint32> for a string
  // (which would be a problem if we used Int32 in C# instead of Rune, for example)
  var s := "Ceci n'est pas une string";
  var notAString := seq(|s|, i requires 0 <= i < |s| => s[i] as int32);
  print notAString, "\n";

  // Ensuring character arithmetic can be compiled
  var sarcastic := "Oh UNicOdE, tHaT's a REaL usEFuL FEaTuRe!";
  var sincere := seq(|sarcastic|, i requires 0 <= i < |sarcastic| => toLower(sarcastic[i]));
  print sincere, "\n";
}


