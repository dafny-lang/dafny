// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method g<T>(x : seq<T> := []) 
{
   print "worked!\n";  
}


method {:verify true} Main() { 
   g<nat>();
}
