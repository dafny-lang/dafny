// RUN: ! %baredafny verify --use-basename-for-filename --cores=0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() ensures false {
}
