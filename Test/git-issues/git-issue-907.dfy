// RUN: %dafny /compile:1 /compileTarget:java /spillTargetCode:1  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Checks that the Java runtime library is present

function method identity(n:nat):nat
{
    n
}

