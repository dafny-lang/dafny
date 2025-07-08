// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --allow-deprecation --unicode-char false

include "../../git-issues/github-issue-2928.dfy"
