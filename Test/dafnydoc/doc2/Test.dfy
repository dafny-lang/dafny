// RUN: rm -rf "%S/docs2"
// RUN: %baredafny doc --use-basename-for-filename --program-name=TestProgram --output:"%S/docs2" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %diff "%S/docs2/index.html" "%S/docs-expected/index.html"
// RUN: %diff "%S/docs2/__95.html" "%S/docs-expected/__95.html"
// RUN: %diff "%S/docs2/Test_13716.html" "%S/docs-expected/Test_13716.html"

module Test {}
