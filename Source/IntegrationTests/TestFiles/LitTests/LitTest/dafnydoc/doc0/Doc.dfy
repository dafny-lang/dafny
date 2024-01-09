// RUN: %baredafny doc "%S"/doc.toml
// RUN: %diff "%S"/documentation/index.html "%S"/docs-expected/index.html
// RUN: %diff "%S"/documentation/__95.html "%S"/docs-expected/__95.html
// RUN: %diff "%S"/documentation/styles.css "%S"/docs-expected/styles.css
