//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {
  public abstract class PreTypeConstraint {
    public readonly IOrigin tok;

    // exactly one of "errorFormatString" and "errorFormatStringProducer" is non-null
    private readonly string errorFormatString;
    private readonly Func<string> errorFormatStringProducer;

    public string ErrorFormatString => errorFormatString ?? errorFormatStringProducer();

    public abstract string ErrorMessage();

    public PreTypeConstraint(IOrigin tok, string errorFormatString, PreTypeConstraint baseError = null) {
      Contract.Requires(tok != null);
      Contract.Requires(errorFormatString != null);
      this.tok = tok;
      if (baseError == null) {
        this.errorFormatString = errorFormatString;
      } else {
        this.errorFormatStringProducer = () => baseError.ErrorMessage() + " (" + errorFormatString + ")";
      }
    }

    public PreTypeConstraint(IOrigin tok, Func<string> errorFormatStringProducer) {
      Contract.Requires(tok != null);
      Contract.Requires(errorFormatStringProducer != null);
      this.tok = tok;
      this.errorFormatStringProducer = errorFormatStringProducer;
    }
  }

  public abstract class OptionalErrorPreTypeConstraint : PreTypeConstraint {
    public readonly bool ReportErrors;
    public OptionalErrorPreTypeConstraint(IOrigin tok, string errorFormatString, PreTypeConstraint baseError, bool reportErrors)
      : base(tok, errorFormatString, baseError) {
      ReportErrors = reportErrors;
    }

    public OptionalErrorPreTypeConstraint(IOrigin tok, Func<string> errorFormatStringProducer, bool reportErrors)
      : base(tok, errorFormatStringProducer) {
      ReportErrors = reportErrors;
    }
  }
}
