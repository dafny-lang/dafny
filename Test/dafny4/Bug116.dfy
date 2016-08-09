// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype struct = S  // this is ok

method Main()
{
  var s := S;  // this line generates illegal C# code
  print s;
}





