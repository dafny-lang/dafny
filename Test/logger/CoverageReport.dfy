// NONUNIFORM: Not a compiler test
// UNSUPPORTED: windows
// Verification coverage:
// RUN: rm -rf "%t"/coverage_verificaion
// RUN: %baredafny verify --use-basename-for-filename --show-snippets false --verify-included-files --coverage-report "%t/coverage_verificaion" %s
// RUN: mv "%t"/coverage_verificaion/* "%t"/coverage_verificaion/report/
// RUN: %sed 's/<h1 hidden.*//' "%t"/coverage_verificaion/report/ProofDependencyLogging.dfy_verification.html > "%t"/coverage_verification_actual.html
// RUN: %diff "%S/ProofDependencyLogging.dfy_verification.html.expect" "%t/coverage_verification_actual.html"
// Test coverage:
// RUN: rm -rf "%t"/coverage_testing
// RUN: %baredafny generate-tests Block --coverage-report "%t/coverage_testing" %s
// RUN: mv "%t"/coverage_testing/* "%t"/coverage_testing/report/
// RUN: %sed 's/<h1 hidden.*//' "%t"/coverage_testing/report/ProofDependencyLogging.dfy_tests_expected.html > "%t"/coverage_testing_actual.html
// RUN: %diff "%S/ProofDependencyLogging.dfy_tests_expected.html.expect" "%t/coverage_testing_actual.html"
// Combined coverage:
// RUN: rm -rf "%t"/coverage_combined
// RUN: %baredafny merge-coverage-reports "%t"/coverage_combined "%t"/coverage_testing/report "%t"/coverage_verification/report
// RUN: mv "%t"/coverage_combined/* "%t"/coverage_combined/report/
// RUN: %sed 's/<h1 hidden.*//' "%t"/coverage_combined/report/ProofDependencyLogging.dfy_combined.html > "%t"/coverage_combined.html
// RUN: %diff "%S/ProofDependencyLogging.dfy_combined.html.expect" "%t/coverage_combined.html"


include "ProofDependencyLogging.dfy"
