// RUN: %dafny /version > %t
// RUN: %OutputCheck --file-to-check "%t" "%s"

// Just make sure the version string is present and not a default like 0.0.0 or 1.0.0.
// This will have to be changed with each major version but I can live with that :)
// CHECK: Dafny 3\..*
