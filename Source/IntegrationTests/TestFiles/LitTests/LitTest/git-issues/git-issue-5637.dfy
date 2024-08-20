// RUN: %translate cs --include-test-runner --allow-warnings %s > "%t"
// RUN: %diff "%s.expect" "%t"