// RUN: %resolve --function-syntax:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The issue here is whether the error message location is at the method keyword or, badly, at the end of the body

function method f(): bool {



  true
}

predicate method p() {





  true
}
