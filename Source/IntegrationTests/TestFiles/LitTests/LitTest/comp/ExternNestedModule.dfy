// RUN: %run --target py "%s" --input %S/ExternNestedModule.py > "%t"
// RUN: %diff "%s.expect" "%t"

method Main(){
    print Library.THREE, "\n";
}

module {:extern "Nested.Library"} Library {
    const THREE := TWO + 1
    const TWO: int
}
