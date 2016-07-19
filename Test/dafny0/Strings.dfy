// RUN: %dafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Char(a: char, s: string, i: int) returns (b: char)
{
  var ch: char;
  if a == ch {
    b := ch;
  } else if 0 <= i < |s| {
    b := s[i];
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
  s := s + [a, b, b] + s;
  t := s;
  s := t[0..|s|];
}

method Main()
{
  var ch: char;
  var s, t := M(ch, ch);
  print "ch = ", ch, "\n";
  print "The string is: " + s + "\n";
  var x, y, z := Escapes();
  print "Escape X: ", x, "\n";
  print "Escape Y: ", y, "\n";
  print "Escape Z: ", z, "\n";
  var c, d := CharEscapes();
  print "Here is the end" + [c, d] + [' ', ' ', ' '] + [[d]][0] + "   ", d, "\n";
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

method Escapes() returns (x: string, y: string, z: string)
{
  x := "I say \"hello\" \\ you say \'good bye'";
  y := @"I say ""hello"" \ you say 'good bye'";
  assert x == y;
  z := "There needs to be \u0052\u0026\u0044\n\tYes, sir";
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
