// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0 -- --relax-definite-assignment

method g<T>(x : seq<T> := []) 
{
   print "worked!\n";  
}


method Main() { 
   g<nat>();
}
