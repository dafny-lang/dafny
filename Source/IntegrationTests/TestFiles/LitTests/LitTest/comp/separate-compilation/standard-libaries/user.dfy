// NONUNIFORM: Test is too complex for the uniform back-end testing mechanism
// RUN: %build --target=lib "%S/Inputs/library.dfy" --standard-libraries=true --output %S/Outputs > %t
// RUN: %run --standard-libraries=true %s --input "%S/Outputs.doo" >> %t
//
// Let's pretend we're vending a Dafny library outside of Dafny, and we want to include the std-lib with the library,
// since the external user won't include it
// RUN: %build "%S/Inputs/library.dfy" --standard-libraries=true --output %S/Outputs >> %t
// RUN: %run --standard-libraries=true %s --library "%S/Outputs.doo" --input "%S/Outputs.dll" --translate-standard-library=false >> %t
// RUN: %diff "%s.expect" "%t"

import opened UsesWrappers

method Main() {
  print SafeDiv(4, 2), "\n";
  print SafeDiv(7, 0), "\n";
}

