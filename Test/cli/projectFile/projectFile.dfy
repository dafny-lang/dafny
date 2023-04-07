// A project file can specify input files and configure options
// RUN: %baredafny resolve --use-basename-for-filename "%S/dafny.toml" > "%t"

// Test option override behavior
// RUN: %baredafny resolve --use-basename-for-filename "%S/dafny.toml" --warn-shadowing=false >> "%t"

// Multiple project files are not allowed
// RUN: ! %baredafny resolve --use-basename-for-filename "%S/dafny.toml" "%S/broken/dafny.toml"

// Project files may not contain unknown properties
// RUN: ! %baredafny resolve --use-basename-for-filename "%S/broken/dafny.toml"

// Project files must be files on disk.
// RUN: ! %baredafny resolve --use-basename-for-filename "%S/doesNotExist/dafny.toml"

// Project file options must have the right type
// RUN: ! %baredafny resolve --use-basename-for-filename "%S/badTypes/dafny.toml" 2>> "%t"

// A project file without includes will take all .dfy files as input
// RUN: %baredafny resolve --use-basename-for-filename "%S/noIncludes/dafny.toml" >> "%t"

// RUN: %diff "%s.expect" "%t"