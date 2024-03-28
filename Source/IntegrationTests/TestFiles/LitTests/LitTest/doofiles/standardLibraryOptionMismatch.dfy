// RUN: %translate cs %s --standard-libraries --unicode-char=false > "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() {
}