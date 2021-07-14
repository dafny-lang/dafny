// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips we-should-always-print-tooltips.dfy > "%t"
// RUN: %diff "%s.expect" "%t"

// WISH it would be great to add /printTooltips to all tests
