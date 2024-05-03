// RUN: %build -t:lib %s --function-syntax:3 --output=%t.doo &> %t
// RUN: %resolve %t.doo --function-syntax:3 &>> %t 
predicate Foo() {
  true
}