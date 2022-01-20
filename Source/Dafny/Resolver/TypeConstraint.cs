#define TI_DEBUG_PRINT
//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using JetBrains.Annotations;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Microsoft.Dafny {
  public record TypeConstraint(Type Super, Type Sub, TypeConstraint.ErrorMsg ErrMsg, bool KeepConstraints) {
    private static readonly List<ErrorMsg> ErrorsToBeReported = new List<ErrorMsg>();
    public static void ReportErrors(ErrorReporter reporter) {
      Contract.Requires(reporter != null);
      foreach (var err in ErrorsToBeReported) {
        err.ReportAsError(reporter);
      }
      ErrorsToBeReported.Clear();
    }
    public abstract class ErrorMsg {
      public abstract IToken Tok { get; }
      bool reported;
      public void FlagAsError() {
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine($"DEBUG: flagging error: {ApproximateErrorMessage()}");
        }
        TypeConstraint.ErrorsToBeReported.Add(this);
      }
      internal void ReportAsError(ErrorReporter reporter) {
        Contract.Requires(reporter != null);
        if (!reported) {  // this "reported" bit is checked only for the top-level message, but this message and all nested ones get their "reported" bit set to "true" as a result
          Reporting(reporter, "");
        }
      }
      private void Reporting(ErrorReporter reporter, string suffix) {
        Contract.Requires(reporter != null);
        Contract.Requires(suffix != null);

        object[] RemoveAmbiguity(object[] msgArgs) {
          var renderedInterpolated = new HashSet<string>();
          var ambiguity = false;
          foreach (var x in msgArgs) {
            var str = x.ToString();
            if (renderedInterpolated.Contains(str)) {
              ambiguity = true;
            }

            renderedInterpolated.Add(str);
          }
          if (ambiguity) {
            return msgArgs.Select(x =>
              (object)(x is UserDefinedType udt ? udt.FullName : x.ToString())
            ).ToArray();
          } else {
            return msgArgs;
          }
        }
        if (this is ErrorMsgWithToken) {
          var err = (ErrorMsgWithToken)this;
          Contract.Assert(err.Tok != null);
          reporter.Error(MessageSource.Resolver, err.Tok, err.Msg + suffix, RemoveAmbiguity(err.MsgArgs));
        } else {
          var err = (ErrorMsgWithBase)this;
          err.BaseMsg.Reporting(reporter, " (" + string.Format(err.Msg, RemoveAmbiguity(err.MsgArgs)) + ")" + suffix);
        }
        reported = true;
      }

      protected abstract string ApproximateErrorMessage();
    }
    public class ErrorMsgWithToken : ErrorMsg {
      readonly IToken tok;
      public override IToken Tok {
        get { return tok; }
      }
      public readonly string Msg;
      public readonly object[] MsgArgs;
      public ErrorMsgWithToken(IToken tok, string msg, params object[] msgArgs) {
        Contract.Requires(tok != null);
        Contract.Requires(msg != null);
        Contract.Requires(msgArgs != null);
        this.tok = tok;
        this.Msg = msg;
        this.MsgArgs = msgArgs;
      }

      protected override string ApproximateErrorMessage() => string.Format(Msg, MsgArgs);
    }
    public class ErrorMsgWithBase : ErrorMsg {
      public override IToken Tok {
        get { return BaseMsg.Tok; }
      }
      public readonly ErrorMsg BaseMsg;
      public readonly string Msg;
      public readonly object[] MsgArgs;
      public ErrorMsgWithBase(ErrorMsg baseMsg, string msg, params object[] msgArgs) {
        Contract.Requires(baseMsg != null);
        Contract.Requires(msg != null);
        Contract.Requires(msgArgs != null);
        BaseMsg = baseMsg;
        Msg = msg;
        MsgArgs = msgArgs;
      }

      protected override string ApproximateErrorMessage() => string.Format(Msg, MsgArgs);
    }
    public void FlagAsError() {
      ErrMsg.FlagAsError();
    }
  }
}
