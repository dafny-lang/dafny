// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main()
{
  mapTest();
  imapTest();
}

method mapTest() {
  print "map test \n";
  var m := map[4 := 5, 6 := 7];
  assert (set x | x in m) == m.Keys;
  assert (set x | x in m :: m[x]) == m.Values;
  print m.Keys, "\n";
  print m.Values, "\n";
  assert (4,5) in m.Items;
  print m.Items, "\n";
}

method imapTest() {
  print "imap test \n";
  var m := imap[4 := 5, 6 := 7];
  assert (iset x | x in m) == m.Keys;
  assert (iset x | x in m :: m[x]) == m.Values;
  print m.Keys, "\n";
  print m.Values, "\n";
  assert (4,5) in m.Items;
  print m.Items, "\n";
}

