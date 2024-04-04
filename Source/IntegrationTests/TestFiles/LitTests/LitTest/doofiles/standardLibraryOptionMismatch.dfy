// RUN: %translate cs --unicode-char false --standard-libraries true %s &> "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() {
}