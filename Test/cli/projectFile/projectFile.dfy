// A project file can specify input files and configure options
// RUN: %baredafny resolve "%S/dafny.toml" > "%t"

// Test option override behavior
// RUN: %baredafny resolve "%S/dafny.toml" --warn-shadowing=false >> "%t"

// Multiple project files are not allowed
// RUN: ! %baredafny resolve "%S/dafny.toml" "%S/broken/dafny.toml" 2>> "%t"

// Project files may not contain unknown properties
// RUN: ! %baredafny resolve "%S/broken/dafny.toml" 2>> "%t"

// Project files must be files on disk.
// RUN: ! %baredafny resolve "%S/doesNotExist/dafny.toml" 2>> "%t"
// RUN: %diff "%s.expect" "%t"