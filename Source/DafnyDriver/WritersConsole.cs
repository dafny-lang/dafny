#nullable enable
using System.CommandLine;
using System.CommandLine.IO;
using System.IO;

namespace Microsoft.Dafny;

class WritersConsole(TextReader inputWriter, TextWriter outWriter, TextWriter errWriter)
  : IConsole {
  public TextReader InputWriter { get; } = inputWriter;
  public TextWriter ErrWriter { get; } = errWriter;
  public TextWriter OutWriter { get; } = outWriter;

  public IStandardStreamWriter Out => StandardStreamWriter.Create(OutWriter ?? TextWriter.Null);

  public bool IsOutputRedirected => OutWriter != null;
  public IStandardStreamWriter Error => StandardStreamWriter.Create(ErrWriter ?? TextWriter.Null);
  public bool IsErrorRedirected => ErrWriter != null;
  public bool IsInputRedirected => false;
}