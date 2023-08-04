// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

method g<T>(x : seq<T> := []) 
{
   print "worked!\n";  
}


method Main() { 
   g<nat>();
}
