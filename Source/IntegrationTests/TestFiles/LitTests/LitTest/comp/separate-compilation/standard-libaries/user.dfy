// RUN: %build --target=lib "%S/Inputs/library.dfy" --standard-libraries=true --output %S/Outputs > %t
// RUN: %run --standard-libraries=true %s --input "%S/Outputs.doo" >> %t
// RUN: %diff "%s.expect" "%t"

import opened UsesWrappers

method Main() {
  print SafeDiv(4, 2), "\n";
  print SafeDiv(7, 0), "\n";
}

