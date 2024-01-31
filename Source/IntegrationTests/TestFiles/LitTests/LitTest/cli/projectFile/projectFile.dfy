// Invalid value gives error and stops compilation
// RUN: ! %resolve --warn-shadowing=true %S/broken/invalidValue.toml 2> "%t"

// A project file can specify input files and configure options
// RUN: %resolve "%S/dfyconfig.toml" >> "%t"

// Test using a URL instead of a local file as a project file
// RUN: ! %resolve "https://github.com/dafny-lang/dafny/blob/master/web.toml" 2>> %t

// Test option override behavior
// RUN: %resolve "%S/dfyconfig.toml" --warn-shadowing=false >> "%t"

// Test option with default override behavior
// RUN: ! %resolve "%S/dfyconfig.toml" --function-syntax=3 >> "%t"

// Multiple project files are not allowed
// RUN: ! %resolve "%S/dfyconfig.toml" "%S/broken/dfyconfig.toml" 2>> %t

// Project files may not contain unknown properties
// RUN: ! %resolve "%S/broken/dfyconfig.toml" 2>> %t

// Warn if file contains options that don't exist
// RUN: %resolve "%S/broken/invalidOption.toml" >> "%t"

// Project files must be files on disk.
// RUN: ! %resolve "%S/doesNotExist.toml" 2>> %t

// Project file options must have the right type
// RUN: ! %resolve "%S/badTypes/dfyconfig.toml" >> "%t"

// A project file without includes will take all .dfy files as input
// RUN: %resolve "%S/noIncludes/dfyconfig.toml" >> "%t"

// Files included by the project file and on the CLI, duplicate is ignored.
// RUN: %resolve "%S/dfyconfig.toml" "%S/src/input.dfy" >> "%t"

// Files excluded by the project file and included on the CLI, are included
// RUN: ! %resolve "%S/dfyconfig.toml" "%S/src/excluded.dfy" >> "%t"

// RUN: %diff "%s.expect" "%t"
