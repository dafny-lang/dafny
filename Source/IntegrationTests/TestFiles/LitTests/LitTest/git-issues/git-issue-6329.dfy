// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Parser inconsistency: field type parsing depends on AcceptReferrers() setting
// Before fix: Parse error "this symbol not expected in VarDeclStatement"
// After fix: Proper resolution error "Type or type parameter is not declared"

method Test() {
  var x: seq<field>;
}
