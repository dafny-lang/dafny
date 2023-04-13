// A project file can specify input files and configure options
// RUN: %baredafny resolve --use-basename-for-filename "%S/dafny.toml" > "%t"

// Test using a URL instead of a local file as a project file
// RUN: ! %baredafny resolve --use-basename-for-filename "https://github.com/dafny-lang/dafny/blob/master/dafny.toml"

// Test option override behavior
// RUN: %baredafny resolve --use-basename-for-filename "%S/dafny.toml" --warn-shadowing=false >> "%t"

// Multiple project files are not allowed
// RUN: ! %baredafny resolve --use-basename-for-filename "%S/dafny.toml" "%S/broken/dafny.toml"

// Project files may not contain unknown properties
// RUN: ! %baredafny resolve --use-basename-for-filename "%S/broken/dafny.toml"

// Warn if file contains options that don't exist
// RUN: %baredafny resolve --use-basename-for-filename "%S/broken/invalidOption.toml" >> "%t"

// Project files must be files on disk.
// RUN: ! %baredafny resolve --use-basename-for-filename "%S/doesNotExist/dafny.toml"

// Project file options must have the right type
// RUN: ! %baredafny resolve --use-basename-for-filename "%S/badTypes/dafny.toml" 2>> "%t"

// A project file without includes will take all .dfy files as input
// RUN: %baredafny resolve --use-basename-for-filename "%S/noIncludes/dafny.toml" >> "%t"

// Files included by the project file and on the CLI, duplicate is ignored.
// RUN: %baredafny resolve --use-basename-for-filename "%S/dafny.toml" "%S/src/input.dfy" >> "%t"

// Files excluded by the project file and included on the CLI, are included
// RUN: ! %baredafny resolve --use-basename-for-filename "%S/dafny.toml" "%S/src/excluded.dfy" >> "%t"

// RUN: %diff "%s.expect" "%t"