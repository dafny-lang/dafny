// RUN: %baredafny translate go "%S/project.toml"
// RUN: cp -r "%S/go.*" "%S/helloworld-go/"
// RUN: cp -r "%S/../module-libraries/DafnyRuntimeGo" "%S"
// RUN: go run -C %S/helloworld-go/ helloworld.go > %t
// RUN: %diff "%s.expect" "%t"