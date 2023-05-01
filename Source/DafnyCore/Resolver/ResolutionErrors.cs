// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using static Microsoft.Dafny.ErrorRegistry;

namespace Microsoft.Dafny;

public class ResolutionErrors {

  public enum ErrorId {
    // ReSharper disable once InconsistentNaming
    r_assert_only_assumes_others
  }

  static ResolutionErrors() {
    Add(ErrorId.r_assert_only_assumes_others,
    @"
When annotating an assert with the `{:only}` attribute, all other implicit and explicit assertions
are assumed. This is a way to focus on an assertion and its proof, but this annotation has to be removed once finished.
This warning is a reminder about it.", Remove(true, "Finish focusing and remove {:only}"));
  }
}
