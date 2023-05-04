// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using static Microsoft.Dafny.ErrorRegistry;

namespace Microsoft.Dafny;

public class ResolutionErrors {

  public enum ErrorId {
    // ReSharper disable once InconsistentNaming
    r_assert_only_assumes_others,
    r_assert_only_before_after
  }

  static ResolutionErrors() {
    Add(ErrorId.r_assert_only_assumes_others,
    @"
When annotating an assertion with the `{:only}` attribute, all other implicit and explicit assertions
are transformed into assumptions. This is a way to focus on an assertion and its proof, but this annotation has to be removed once finished.
This warning is a reminder about it.", Remove(true, "Finish focusing and remove {:only}"));
    Add(ErrorId.r_assert_only_before_after,
      @"
The `{:only}` attribute accepts an optional argument ""after"" or ""before"" to indicate that the assertions afterwards
(respectively before) should be transformed into assumptions.", Replace(@"""before""", "Replace with \"before\""));
  }
}
