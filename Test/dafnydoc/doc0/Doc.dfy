// RUN: %baredafny doc "%S"/doc.toml
// RUN: %diff "%S"/documentation/index.html "%S"/docs-expected/index.html
// RUN: %diff "%S"/documentation/_.html "%S"/docs-expected/_.html
// RUN: %diff "%S"/documentation/styles.css "%S"/docs-expected/styles.css
