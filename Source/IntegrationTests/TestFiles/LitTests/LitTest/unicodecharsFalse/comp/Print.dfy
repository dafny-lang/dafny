// NONUNIFORM: https://github.com/dafny-lang/dafny/issues/4108 and https://github.com/dafny-lang/dafny/issues/2582
// RUN: %verify --allow-deprecation --unicode-char false --relax-definite-assignment "%s" > "%t"
// RUN: %run --no-verify --allow-deprecation --unicode-char false --target cs "%s" >> "%t"
// RUN: %run --no-verify --allow-deprecation --unicode-char false --target js "%s" >> "%t"
// RUN: %run --no-verify --allow-deprecation --unicode-char false --target go "%s" >> "%t"
// RUN: %run --no-verify --allow-deprecation --unicode-char false --target java "%s" >> "%t"
include "../../comp/Print.dfy"
