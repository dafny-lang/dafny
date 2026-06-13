// RUN: %exits-with 5 %stdin "function f(): int\n{\n0\n}" %baredafny format --check --stdin
// RUN: %exits-with 0 %stdin "function f(): int {\n  0\n}" %baredafny format --check --stdin

// Also verify --print produces the correctly formatted output.
// RUN: %exits-with 0 %stdin "function f(): int\n{\n0\n}\n" %baredafny format --print --stdin > "%t"
// RUN: %diff "%s.expect" "%t"

// Regression test: format --stdin always reported the input as already
// formatted. After reading stdin, the input is parsed from a temp file, but
// the formatter looked up the program by the original stdin URI: both
// GetFirstTokenForUri and IndentationFormatter.ForProgram were passed the
// stdin URI instead of the temp file URI, so no first token was found and
// formatting was skipped. The fix passes the temp file URI to both.
