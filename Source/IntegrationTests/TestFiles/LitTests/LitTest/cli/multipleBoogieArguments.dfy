// RUN: %baredafny verify --boogie "/randomSeedIterations:0" --boogie "/vcsLoad:2" %s 2> %t
// RUN: %baredafny verify --boogie "/vcsLoad:2 /randomSeedIterations:0" %s 2>> %t
// RUN: %diff "%s.expect" "%t"

function id(x:int) : (r:int) { x }