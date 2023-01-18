// RUN: ! %baredafny verify --use-basename-for-filename --cores=0 "%s" 2> "%t"
// RUN: ! %baredafny verify --use-basename-for-filename --cores=earga "%s" 2>> "%t"
// RUN: ! %baredafny verify --use-basename-for-filename --cores=earga% "%s" 2>> "%t"
// RUN: ! %baredafny verify --use-basename-for-filename "%s" >> "%t"
// RUN: ! %baredafny verify --use-basename-for-filename --cores=1 "%s" >> "%t"
// RUN: ! %baredafny verify --use-basename-for-filename --cores=0% "%s" >> "%t"
// RUN: ! %baredafny verify --use-basename-for-filename --cores=50% "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() ensures false {
}
