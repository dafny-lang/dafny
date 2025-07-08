// RUN: %build "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype KeyValues<T> = Store(underlying: map<string, T> := map[])

function CreateStore<T>(): (r: KeyValues<T>) {
  Store()
}
