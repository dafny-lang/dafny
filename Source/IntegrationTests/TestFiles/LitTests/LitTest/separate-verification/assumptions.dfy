// Passing --no-verify because TestAuditor.dfy intentionally has a failing assertion,
// but that would otherwise mean we don't get far enough to exercise the LibraryBackend.
// RUN: ! %baredafny build -t:lib --no-verify %args %s > %t
// RUN: %diff "%s.expect" %t

include "../auditor/TestAuditor.dfy"