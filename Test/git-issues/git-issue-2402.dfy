// RUN: %dafny_0 /compile:1 /compileTarget:cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module M 
{ 
    type T
    const t : T
    lemma Randomlemma()
    {
        forall i:int {}
    }
}

module N refines M 
{ 
}