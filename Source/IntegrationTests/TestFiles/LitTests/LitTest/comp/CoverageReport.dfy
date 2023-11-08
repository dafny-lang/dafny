// NONUNIFORM: Out-of-band output (coverage reports) not easily testable via %testDafnyForEachCompiler

// Actual runtime test coverage
// (See also logger/CoverageReport.dfy for verification coverage and expected coverage of generated tests)

// RUN: rm -rf "%t"/execution_testing
// RUN: %baredafny run %args -t:cs --no-timestamp-for-coverage-report --coverage-report "%t_coverage_reports/execution_testing" %s
// RUN: %sed 's/<h1 hidden.*//' "%t_coverage_reports"/execution_testing/BranchCoverage.dfy_tests_actual.html > "%t_coverage_reports"/coverage_tests_actual.html
// RUN: %diff "%S/CoverageReport.dfy_tests_actual.html.expect" "%t_coverage_reports/coverage_tests_actual.html"

// Manually assert the other backends cleanly report they don't support this feature yet
// RUN: %exits-with 3 %baredafny run %args -t:java --no-timestamp-for-coverage-report --coverage-report "%t_coverage_reports/execution_testing" %s > "%t"
// RUN: %exits-with 3 %baredafny run %args -t:js --no-timestamp-for-coverage-report --coverage-report "%t_coverage_reports/execution_testing" %s >> "%t"
// RUN: %exits-with 3 %baredafny run %args -t:go --no-timestamp-for-coverage-report --coverage-report "%t_coverage_reports/execution_testing" %s >> "%t"
// RUN: %exits-with 3 %baredafny run %args -t:py --no-timestamp-for-coverage-report --coverage-report "%t_coverage_reports/execution_testing" %s >> "%t"
// RUN: %exits-with 3 %baredafny run %args -t:cpp --no-timestamp-for-coverage-report --coverage-report "%t_coverage_reports/execution_testing" %s >> "%t"
// RUN: %exits-with 3 %baredafny run %args -t:rs --no-timestamp-for-coverage-report --coverage-report "%t_coverage_reports/execution_testing" %s >> "%t"
// RUN: %diff "%s.expect" "%t"

include "BranchCoverage.dfy"