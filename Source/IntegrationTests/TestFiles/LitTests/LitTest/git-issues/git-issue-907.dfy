// RUN: %translate java %trargs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Checks that the Java runtime library is present

function identity(n:nat):nat
{
    n
}

