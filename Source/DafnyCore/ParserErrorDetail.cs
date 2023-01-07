// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using System.Globalization;

namespace Microsoft.Dafny;

public class ParserErrorDetail {

  public static string p_bad_const_initialize_op = "P-bad-const-initialize-op";

  public static void init() {

    ErrorDetail.Add(p_bad_const_initialize_op, "replace with :=", ":=",
    @"
```dafny
const c: int = 5
```

Dafny's syntax for initialization and assignment uses `:=`, not `=` (like some other languages).
In fact `=` is not used at all in Dafny.
"
    );


  }
}
