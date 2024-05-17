// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C { var f: int }

function FrameDereferenceNonNull(c: C?): bool
    reads c`f
{ true }