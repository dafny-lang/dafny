using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace XUnitExtensions.Lit;

class CombinedWriter : TextWriter {
  private IEnumerable<TextWriter> writers;

  public CombinedWriter(Encoding encoding, IEnumerable<TextWriter> writers) {
    this.Encoding = encoding;
    this.writers = writers;
  }

  public override Encoding Encoding { get; }

  public override void Flush() {
    foreach (var writer in writers) {
      writer.Flush();
    }
    base.Flush();
  }

  public override Task FlushAsync() {
    return Task.WhenAll(writers.Select(w => w.FlushAsync()));
  }

  public override void Write(char value) {
    foreach (var writer in writers) {
      writer.Write(value);
    }
  }

  public override void Write(char[] buffer, int index, int count) {
    foreach (var writer in writers) {
      writer.Write(buffer, index, count);
    }
  }

  public override Task WriteAsync(char value) {
    return Task.WhenAll(writers.Select(w => w.WriteAsync(value)));
  }

  public override Task WriteAsync(char[] buffer, int index, int count) {
    return Task.WhenAll(writers.Select(w => w.WriteAsync(buffer, index, count)));
  }
}