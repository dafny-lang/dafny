using Newtonsoft.Json;
using Newtonsoft.Json.Converters;

namespace Microsoft.Dafny.LanguageServer.Workspace.Notifications {
  /// <summary>
  /// Enumeration that identifies that actual compilation status.
  /// </summary>
  [JsonConverter(typeof(StringEnumConverter))]
  public enum CompilationStatus {
    ResolutionStarted,
    ParsingFailed,
    ResolutionFailed,
    CompilationSucceeded
  }
}
