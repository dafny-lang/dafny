using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using VC;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public record BoogieUpdate(ICanVerify CanVerify, IImplementationTask Task, IVerificationStatus BoogieStatus)
  : ICompilationEvent {

}