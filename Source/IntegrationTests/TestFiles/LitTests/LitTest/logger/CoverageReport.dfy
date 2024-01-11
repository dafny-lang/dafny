// NONUNIFORM: Not a compiler test
// Verification coverage:
// RUN: rm -rf "%t"/coverage_verification
// RUN: %baredafny verify --use-basename-for-filename --show-snippets false --verify-included-files --no-timestamp-for-coverage-report --verification-coverage-report "%t/coverage_verification" %s
// RUN: %sed 's/<h1 hidden.*//' "%t"/coverage_verification/ProofDependencies.dfy_verification.html > "%t"/coverage_verification_actual.html
// RUN: %diff "%S/ProofDependencies.dfy_verification.html.expect" "%t/coverage_verification_actual.html"
// Expected test coverage:
// RUN: rm -rf "%t"/coverage_testing
// RUN: %baredafny generate-tests Block --no-timestamp-for-coverage-report --coverage-report "%t/coverage_testing" %s
// RUN: %sed 's/<h1 hidden.*//' "%t"/coverage_testing/ProofDependencies.dfy_tests_expected.html > "%t"/coverage_testing_actual.html
// RUN: %diff "%S/ProofDependencies.dfy_tests_expected.html.expect" "%t/coverage_testing_actual.html"
// Combined coverage:
// RUN: rm -rf "%t"/coverage_combined
// RUN: %baredafny merge-coverage-reports --no-timestamp-for-coverage-report "%t"/coverage_combined "%t"/coverage_testing "%t"/coverage_verification
// RUN: %sed 's/<h1 hidden.*//' "%t"/coverage_combined/ProofDependencies.dfy_combined.html > "%t"/coverage_combined.html
// RUN: %diff "%S/ProofDependencies.dfy_combined.html.expect" "%t/coverage_combined.html"
// Combined, limited coverage:
// RUN: rm -rf "%t"/coverage_combined
// RUN: %baredafny merge-coverage-reports --only-label NotCovered --no-timestamp-for-coverage-report "%t"/coverage_combined_limited "%t"/coverage_testing "%t"/coverage_verification
// RUN: %sed 's/<h1 hidden.*//' "%t"/coverage_combined_limited/ProofDependencies.dfy_combined.html > "%t"/coverage_combined_limited.html
// RUN: %diff "%S/ProofDependencies.dfy_combined_limited.html.expect" "%t/coverage_combined_limited.html"


include "ProofDependencies.dfy"
