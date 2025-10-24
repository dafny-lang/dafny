// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --allow-deprecation --unicode-char false --enforce-determinism

include "../../git-issues/github-issue-2928.dfy"
