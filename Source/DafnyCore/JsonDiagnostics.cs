#nullable enable

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Text.Json.Nodes;
using DafnyCore;
using VCGeneration;

namespace Microsoft.Dafny;

record DiagnosticMessageData(MessageSource source, ErrorLevel level, IOrigin tok, string? category, string message, List<ErrorInformation.AuxErrorInfo>? related) {
  private static JsonObject SerializePosition(Boogie.IToken tok) {
    return new JsonObject {
      ["pos"] = tok.pos,
      ["line"] = tok.line,
      ["character"] = tok.col - 1
    };
  }

  private static JsonObject SerializeRange(DafnyOptions options, IOrigin origin) {
    var showSnippets = options.Get(Snippets.ShowSnippets);
    var range = new JsonObject {
      ["start"] = SerializePosition(showSnippets ? origin.StartToken : origin.Center),
    };
    if (origin is RangeToken rangeToken1 && showSnippets) {
      range["end"] = SerializePosition(rangeToken1.EndToken);
    } else if (origin is BoogieRangeOrigin rangeToken2 && showSnippets) {
      range["end"] = SerializePosition(rangeToken2.EndToken);
    }
    return range;
  }

  private static JsonObject SerializeToken(DafnyOptions options, IOrigin tok) {
    return new JsonObject {
      ["filename"] = tok.filename,
      ["uri"] = tok.Uri.AbsoluteUri,
      ["range"] = SerializeRange(options, tok)
    };
  }

  private static int SerializeErrorLevel(ErrorLevel lvl) {
    return lvl switch {
      ErrorLevel.Error => 1,
      ErrorLevel.Warning => 2,
      ErrorLevel.Info => 4,
      _ => throw new ArgumentException()
    };
  }

  private static string SerializeMessage(string? category, string message) {
    return category == null ? message : $"{category}: {message}";
  }

  private static JsonObject SerializeRelated(DafnyOptions options, IOrigin tok, string? category, string message) {
    return new JsonObject {
      ["location"] = SerializeToken(options, tok),
      ["message"] = SerializeMessage(category, message),
    };
  }

  private static IEnumerable<JsonNode> SerializeInnerTokens(IOrigin tok, DafnyOptions options) {
    while (tok is NestedOrigin nestedToken) {
      tok = nestedToken.Inner;
      var message = nestedToken.Message != null ? "Related location: " + nestedToken.Message : "Related location";
      yield return SerializeRelated(options, tok, null, message);
    }
  }

  private static IEnumerable<JsonNode> SerializeAuxInfo(ErrorInformation.AuxErrorInfo aux, DafnyOptions options) {
    var reportRanges = options.Get(Snippets.ShowSnippets);
    yield return SerializeRelated(options, BoogieGenerator.ToDafnyToken(reportRanges, aux.Tok), aux.Category, aux.Msg);
    foreach (var n in SerializeInnerTokens(BoogieGenerator.ToDafnyToken(reportRanges, aux.Tok), options)) {
      yield return n;
    }
  }

  public JsonNode ToJson(DafnyOptions options) {
    var auxRelated = related?.SelectMany(aux => SerializeAuxInfo(aux, options)) ?? Enumerable.Empty<JsonNode>();
    var innerRelated = SerializeInnerTokens(tok, options);
    return new JsonObject {
      ["location"] = SerializeToken(options, tok),
      ["severity"] = SerializeErrorLevel(level),
      ["message"] = SerializeMessage(category, message),
      ["source"] = source.ToString(),
      ["relatedInformation"] = new JsonArray(auxRelated.Concat(innerRelated).ToArray())
    };
  }

  public void WriteJsonTo(DafnyOptions options, TextWriter wr) {
    wr.WriteLine(ToJson(options).ToJsonString(new JsonSerializerOptions { WriteIndented = false }));
  }
}

public class DafnyJsonConsolePrinter : DafnyConsolePrinter {
  public override void ReportBplError(Boogie.IToken tok, string message, bool error, TextWriter tw, string? category = null) {
    var level = error ? ErrorLevel.Error : ErrorLevel.Warning;
    var origin = BoogieGenerator.ToDafnyToken(Options.Get(Snippets.ShowSnippets), tok);
    new DiagnosticMessageData(MessageSource.Verifier, level, origin, category, message, null).WriteJsonTo(Options, tw);
  }

  public override void WriteErrorInformation(VCGeneration.ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true) {
    var related = errorInfo.Aux.Where(e =>
      !(skipExecutionTrace && (e.Category ?? "").Contains("Execution trace"))).ToList();
    var dafnyToken = BoogieGenerator.ToDafnyToken(Options.Get(Snippets.ShowSnippets), errorInfo.Tok);
    new DiagnosticMessageData(MessageSource.Verifier, ErrorLevel.Error,
      dafnyToken, errorInfo.Category, errorInfo.Msg, related).WriteJsonTo(Options, tw);
    tw.Flush();
  }

  public DafnyJsonConsolePrinter(DafnyOptions options) : base(options) {
  }
}

public class JsonConsoleErrorReporter : BatchErrorReporter {
  protected override bool MessageCore(MessageSource source, ErrorLevel level, string errorID, Dafny.IOrigin tok, string msg) {
    if (base.MessageCore(source, level, errorID, tok, msg) && (Options is { PrintTooltips: true } || level != ErrorLevel.Info)) {
      new DiagnosticMessageData(source, level, tok, level == ErrorLevel.Error ? "Error" : null, msg, null).WriteJsonTo(Options, Options.OutputWriter);
      return true;
    }

    return false;
  }

  public JsonConsoleErrorReporter(DafnyOptions options) : base(options) {
  }
}