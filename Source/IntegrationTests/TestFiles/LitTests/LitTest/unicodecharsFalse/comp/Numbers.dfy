// NONUNIFORM: https://github.com/dafny-lang/dafny/issues/4174
// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --type-system-refresh=false --general-newtypes=false --allow-deprecation --relax-definite-assignment --unicode-char false --verify-included-files
include "../../comp/Numbers.dfy"
