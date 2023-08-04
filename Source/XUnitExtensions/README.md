# XUnitExtensions

This package contains extensions for the [xUnit](https://xunit.net/) testing framework in two categories:

1. A [special case](FileTheoryAttribute.cs) of parameterized `Theory` tests where each test case is encoded as a file, 
   and allowing such test cases to be executed in parallel (xUnit does not support parallel
   execution within a single `Theory` out of the box) and/or in separate shards across multiple machines.
2. An [alternate interpreter](Lit/LitTestCase.cs) for [LLVM Integrated Tester (LIT)](https://llvm.org/docs/CommandGuide/lit.html) tests, allowing
   a test suite using the LIT syntax to be run as a `Theory`.