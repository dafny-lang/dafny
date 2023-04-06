// A project file can specify input files and configure options
// RUN: %baredafny resolve --use-basename-for-filename "%S/dafny.toml" > "%t"

// Test option override behavior
// RUN: %baredafny resolve --use-basename-for-filename "%S/dafny.toml" --warn-shadowing=false >> "%t"

// Multiple project files are not allowed
// RUN: ! %baredafny resolve --use-basename-for-filename "%S/dafny.toml" "%S/broken/dafny.toml"

// Project files may not contain unknown properties
// RUN: ! %baredafny resolve --use-basename-for-filename "%S/broken/dafny.toml" 2>> "%t"

// Project files must be files on disk.
// RUN: ! %baredafny resolve --use-basename-for-filename "%S/doesNotExist/dafny.toml" 2>> "%t"

// Project file options must have the right type
// RUN: ! %baredafny resolve --use-basename-for-filename "%S/badTypes/dafny.toml" 2>> "%t"

// RUN: %diff "%s.expect" "%t"