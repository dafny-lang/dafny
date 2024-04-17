// RUN: %build %s -t:lib --allow-warnings --output="%S/Output/allowWarnings.doo" &> "%t"
// RUN: ! %stdin "method Bar() { }" %resolve --stdin %S/Output/allowWarnings.doo &>> %t
// RUN: %diff "%s.expect" "%t"

method Foo() {
}