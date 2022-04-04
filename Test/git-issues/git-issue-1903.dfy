// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method g<T>(x : seq<T> := []) 
{
   print "worked!\n";  
}


method {:verify true} Main() { 
    //g<nat>([]);   // works 
   g<nat>();   //  compile error
}

//__default.g<BigInteger>(Dafny.Sequence<BigInteger>.FromElements());
//__default.g<BigInteger>(Dafny.Sequence<__S>.FromElements());
