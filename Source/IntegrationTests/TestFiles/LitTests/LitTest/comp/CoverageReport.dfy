// Actual runtime test coverage
// (See also logger/CoverageReport.dfy for verification coverage and expected coverage of generated tests)

// RUN: rm -rf "%t"/execution_testing
// RUN: %baredafny run %args -t:cs --no-timestamp-for-coverage-report --coverage-report "%t/execution_testing" %s
// RUN: %sed 's/<h1 hidden.*//' "%t"/execution_testing/BranchCoverage.dfy_tests_actual.html > "%t"/coverage_tests_actual.html
// RUN: %diff "%S/CoverageReport.dfy_tests_actual.html.expect" "%t/coverage_tests_actual.html"

include "BranchCoverage.dfy"