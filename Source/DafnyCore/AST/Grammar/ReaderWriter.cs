using System;
using System.IO;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

class ReaderWriter : TextReader {

  public TextWriter Writer => writer;
  private readonly WriterFromQueue writer = new();
  
  class WriterFromQueue : TextWriter {
    public char[] Buffer { get; set; }
    public int Count { get; set; }
    public int Index { get; set; }

    public SemaphoreSlim WriteStop { get; } = new(0);
    public SemaphoreSlim DoneWriting = new(0);

    public override Encoding Encoding => Encoding.Unicode;
    public string Remainder { get; private set; }

    public override Task FlushAsync() {
      DoneWriting.Release(int.MaxValue);
      return Task.CompletedTask;
    }

    public override async Task WriteAsync(string value) {
      await WriteStop.WaitAsync();
        
      value.CopyTo(0, Buffer, Index, Count);
      var copied = Math.Min(Count, value.Length);
      Count -= copied;
      Index += copied;

      if (Count > 0) {
        WriteStop.Release();
      } else {
        Remainder = value.Substring(copied);
        DoneWriting.Release();
      }
    }

    public override Task WriteLineAsync(string value) {
      return WriteAsync(value + Environment.NewLine);
    }
  }

  public override async Task<int> ReadAsync(char[] buffer, int index, int count) {
    var remainingCount = count;
    if (writer.Remainder.Length > 0) {
      var copyLength = Math.Min(count, writer.Remainder.Length);
      writer.Remainder.CopyTo(0, buffer, index, copyLength);
      remainingCount -= copyLength;
      index += copyLength;
    }

    if (remainingCount <= 0) {
      return count;
    }
      
    writer.Buffer = buffer;
    writer.Count = remainingCount;
    writer.Index = index;
    writer.WriteStop.Release();
    await writer.DoneWriting.WaitAsync();
    return writer.Index - index;
  }

  public override int Read(char[] buffer, int index, int count) {
    throw new NotSupportedException();
  }
}