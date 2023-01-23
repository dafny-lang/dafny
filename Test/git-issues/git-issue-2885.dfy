// RUN: %dafny /compile:1 /compileTarget:cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype KeyValues<T> = Store(underlying: map<string, T> := map[])

function method CreateStore<T>(): (r: KeyValues<T>) {
  Store()
}
