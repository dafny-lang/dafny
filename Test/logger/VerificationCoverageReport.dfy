// NONUNIFORM: Not a compiler test
// UNSUPPORTED: windows
// RUN: rm -rf "%t"/coverage
// RUN: %baredafny verify --use-basename-for-filename --show-snippets false --verify-included-files --coverage-report "%t/coverage" %s
// RUN: %sed 's/<h1 hidden.*//' "%t"/coverage/*/ProofDependencyLogging.dfy_verification.html > "%t"/coverage_actual.html
// RUN: %diff "%S/ProofDependencyLogging.dfy_verification.html.expect" "%t/coverage_actual.html"

include "ProofDependencyLogging.dfy"
