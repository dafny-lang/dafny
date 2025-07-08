// Invalid value gives error and stops compilation
// RUN: echo '1' >> %t
// RUN: ! %resolve --warn-shadowing=true %S/broken/invalidValue.toml &> "%t"
// RUN: echo '2' >> %t
// A project file can specify input files and configure options
// RUN: ! %resolve "%S/dfyconfig.toml" &>> "%t"
// RUN: echo '3' >> %t
// Test using a URL instead of a local file as a project file
// RUN: ! %resolve "https://github.com/dafny-lang/dafny/blob/master/web.toml" &>> %t
// RUN: echo '4' >> %t

// Test option override behavior
// RUN: %resolve "%S/dfyconfig.toml" --warn-shadowing=false &>> "%t"
// RUN: echo '5' >> %t

// Test option with default override behavior
// RUN: ! %resolve "%S/dfyconfig.toml" --function-syntax=3 &>> "%t"
// RUN: echo '6' >> %t

// Multiple project files are not allowed
// RUN: ! %resolve "%S/dfyconfig.toml" "%S/broken/dfyconfig.toml" &>> %t
// RUN: echo '7' >> %t

// Project files may not contain unknown properties
// RUN: ! %resolve "%S/broken/dfyconfig.toml" &>> %t
// RUN: echo '8' >> %t

// Warn if file contains options that don't exist
// RUN: ! %resolve "%S/broken/invalidOption.toml" &>> "%t"
// RUN: echo '9' >> %t

// Project files must be files on disk.
// RUN: ! %resolve "%S/doesNotExist.toml" &>> %t
// RUN: echo '10' >> %t

// Project file options must have the right type
// RUN: ! %resolve "%S/badTypes/dfyconfig.toml" &>> "%t"
// RUN: echo '11' >> %t

// A project file without includes will take all .dfy files as input
// RUN: ! %resolve "%S/noIncludes/dfyconfig.toml" &>> "%t"

// RUN: echo '12' >> %t
// Files included by the project file and on the CLI, duplicate is ignored.
// RUN: ! %resolve "%S/dfyconfig.toml" "%S/src/input.dfy" &>> "%t"

// RUN: echo '13' >> %t
// Files excluded by the project file and included on the CLI, are included
// RUN: ! %resolve "%S/dfyconfig.toml" "%S/src/excluded.dfy" &>> "%t"

// RUN: echo '14' >> %t
// A project file can be found from an input file
// RUN: ! %resolve --find-project %S/src/input.dfy &>> "%t"

// RUN: echo '15' >> %t
// RUN: ! %baredafny format --use-basename-for-filename --check "%S/dfyconfig.toml" &>> "%t"

// Project files may not contain unknown properties
// RUN: echo '16' >> %t
// RUN: ! %build "%S/broken/dfyconfig.toml" &>> %t

// RUN: %diff "%s.expect" "%t"
