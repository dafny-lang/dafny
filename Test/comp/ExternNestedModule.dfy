// RUN: %dafny /compile:4 /spillTargetCode:2 /compileTarget:py %S/ExternNestedModule.py "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main(){
    print Library.THREE, "\n";
}

module {:extern "Nested.Library"} Library {
    const THREE := TWO + 1; 
    const TWO: int
}