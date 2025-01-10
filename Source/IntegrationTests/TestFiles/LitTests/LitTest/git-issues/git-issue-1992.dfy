// RUN: %exits-with 4 %baredafny verify --use-basename-for-filename --show-snippets:false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function foo(x: int): int {
  match x // Error here
    case 0 => 1
}

