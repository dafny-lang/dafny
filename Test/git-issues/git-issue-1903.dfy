// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method g<T>(x : seq<T> := []) 
{
   print "worked!\n";  
}


method Main() { 
   g<nat>();
}
