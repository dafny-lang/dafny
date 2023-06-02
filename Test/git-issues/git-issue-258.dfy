// RUN: %dafny /compile:0 /unicodeChar:0 "%s" > "%t"
// RUN: %dafny /compile:3 /unicodeChar:0 /spillTargetCode:3 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /compile:3 /unicodeChar:0 /spillTargetCode:3 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /compile:3 /unicodeChar:0 /spillTargetCode:3 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /unicodeChar:0 /spillTargetCode:3 /compileTarget:go "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method pr<T>(s: seq<T>) {
  print s, "\n";
}

method Main() {
  var a := new char[2];
  a[0] := 'h';
  a[1] := 'i';
  print a[..], "\n";   // hi
  print (a[..]), "\n"; // hi
  var b := new char[0];
  print b[..], "\n";   //    -- empty line
  print "", "\n";      //    -- empty line
  print "HI!", "\n";   // HI!

  pr(a[..]);           // hi
  pr(b[..]);           //    -- empty line  // JS and GO unavoidably produce [] -- as a generic object cannot distinguish empty char sequence and empty other sequence
  pr("HI!");           // HI!
  pr("");              //    -- empty line

  var d:= new int[2];
  d[0] := 23;
  d[1] := 45;
  print d[..], "\n";   // [23,45]
  pr(d[..]);           // [23,45]
  d := new int[0];
  print d[..], "\n";   // []
  pr(d[..]);           // []

  var s: string := "abc";
  print (s+s), "\n";   // abcabc
  pr(s+s);             // abcabc
  print ("abc"+"def"), "\n"; // abcdef
  pr("abc"+"def");           // abcdef
  print ""+"", "\n";         //    -- empty line
  pr(""+"");                 //    -- empty line
  print [1,2]+[3,4], "\n";   // [1,2,3,4]
  pr([1,2]+[3,4]);           // [1,2,3,4]

  // print []+[], "\n"; // not legal Dafny
  // pr([]+[]);         // not legal Dafny
}


