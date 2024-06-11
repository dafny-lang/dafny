// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

method g<T>(x : seq<T> := []) 
{
   print "worked!\n";  
}


method Main() { 
   g<nat>();
}
