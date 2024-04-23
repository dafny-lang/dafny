#nullable enable
using System.CommandLine;
using System.CommandLine.IO;
using System.IO;

namespace Microsoft.Dafny;

class WritersConsole : IConsole {
  public TextReader InputWriter { get; }
  public TextWriter ErrWriter { get; }
  public TextWriter OutWriter { get; }

  public WritersConsole(TextReader inputWriter, TextWriter outWriter, TextWriter errWriter) {
    InputWriter = inputWriter;
    this.ErrWriter = errWriter;
    this.OutWriter = outWriter;
  }

  public IStandardStreamWriter Out => StandardStreamWriter.Create(OutWriter ?? TextWriter.Null);

  public bool IsOutputRedirected => OutWriter != null;
  public IStandardStreamWriter Error => StandardStreamWriter.Create(ErrWriter ?? TextWriter.Null);
  public bool IsErrorRedirected => ErrWriter != null;
  public bool IsInputRedirected => false;
}