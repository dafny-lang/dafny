// RUN: %baredafny resource Syntax.cs-schema %S/Syntax.cs-schema
// RUN: %OutputCheck --file-to-check %S/Syntax.cs-schema "%s"
// CHECK: abstract class IOrigin
