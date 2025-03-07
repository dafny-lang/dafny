// NONUNIFORM: Testing CLI options handling, not actual compilation
// RUN: %resolve --function-syntax:4 --function-syntax:3 "%s" > "%t"
// RUN: %resolve --quantifier-syntax:3 --quantifier-syntax:4  "%s" >> "%t"
// RUN: %build --target:java --target:cs  "%s" >> "%t"
// RUN: %resolve --unicode-char false --unicode-char true  "%s" >> "%t"
// RUN: %resolve --prelude "%s" --prelude "%s"  "%s" >> "%t"
// RUN: %verify --cores:2 --cores:1  "%s" >> "%t"
// RUN: %verify --solver-log x.tct --solver-log y.txt  "%s" >> "%t"
// RUN: %verify --resource-limit 100e3 --resource-limit 200e3  "%s" >> "%t"
// RUN: ! %verify --solver-path x --solver-path y  "%s"
// RUN: %verify --verification-time-limit 300 --verification-time-limit 500  "%s" >> "%t"
// RUN: %verify --error-limit:10 --error-limit:5  "%s" >> "%t"
// RUN: %translate cs %trargs --output x --output y  "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
// Crashes size x is nothing real
// ## %verify --solver-plugin x --solver-plugin x  "%s" >> "%t"

module A {}
