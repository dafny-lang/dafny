// Passing --no-verify because TestAuditor.dfy intentionally has a failing assertion,
// but that would otherwise mean we don't get far enough to exercise the LibraryBackend.
// RUN: ! %build -t:lib --allow-axioms false --no-verify --reads-clauses-on-methods %args %s > %t
// RUN: %diff "%s.expect" %t

include "../auditor/TestAuditor.dfy"