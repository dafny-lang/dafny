// RUN: %build %s -t:lib --allow-warnings --output="%S/Output/allowWarnings.doo" > "%t"
// RUN: %resolve %s %S/Output/allowWarnings.doo >> %t
// RUN: %diff "%s.expect" "%t"

method Foo() {
}