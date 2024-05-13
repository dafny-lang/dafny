// RUN: %build -t:lib %s --function-syntax:3 --output=%t3.doo &> %t
// RUN: %build -t:lib %s --function-syntax:4 --output=%t4.doo &>> %t
// RUN: %resolve %t3.doo --function-syntax:3 &>> %t
// RUN: %resolve %t4.doo --function-syntax:3 &>> %t
// RUN: %resolve %t3.doo --function-syntax:4 &>> %t 
// RUN: %resolve %t4.doo --function-syntax:4 &>> %t
// RUN: %diff "%s.expect" "%t"
 
predicate Foo() {
  true
}