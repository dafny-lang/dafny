// RUN: %resolve --function-syntax:4 --function-syntax:3 "%s" > "%t"
// RUN: %resolve --quantifier-syntax:3 --quantifier-syntax:4  "%s" >> "%t"
// RUN: %build --target:java --target:cs  "%s" >> "%t"
// RUN: %resolve --unicode-char:false --unicode-char:true  "%s" >> "%t"
// RUN: %resolve --prelude "%s" --prelude "%s"  "%s" >> "%t"
// RUN: %verify --cores:2 --cores:1  "%s" >> "%t"
// RUN: %verify --solver-log x.tct --solver-log y.txt  "%s" >> "%t"
// RUN: %verify --resource-limit 100 --resource-limit 200  "%s" >> "%t"
// RUN: %verify --solver-path x --solver-path y  "%s" >> "%t"
// RUN: %verify --verification-time-limit 300 --verification-time-limit 500  "%s" >> "%t"
// RUN: %resolve --error-limit:10 --error-limit:5  "%s" >> "%t"
// RUN: %translate cs --output x --output y  "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
// Crashes size x is nothing real
// ## %verify --solver-plugin x --solver-plugin x  "%s" >> "%t"
// Not testing --boogi, --boogie-filter

module A {}
