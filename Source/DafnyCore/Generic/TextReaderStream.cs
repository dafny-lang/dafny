using System;
using System.IO;
using System.Text;

namespace Microsoft.Dafny; 

public class TextReaderStream : Stream
{
  private readonly TextReader textReader;
  private readonly Encoding encoding;

  public TextReaderStream(TextReader textReader, Encoding encoding)
  {
    this.textReader = textReader;
    this.encoding = encoding;
  }

  public override bool CanRead => true;
  public override bool CanSeek => false;
  public override bool CanWrite => false;
  public override long Length => throw new NotSupportedException();

  public override long Position
  {
    get => throw new NotSupportedException();
    set => throw new NotSupportedException();
  }

  private byte[] remainder = Array.Empty<byte>();
  private int remainderOffset;
  
  public override int Read(byte[] buffer, int offset, int count) {
    if (remainder.Length > remainderOffset) {
      var amount = remainder.Length - remainderOffset;
      Array.Copy(remainder, remainderOffset, buffer, offset, amount);
      count -= amount;
    }
    
    var maxCharCount = encoding.GetMaxCharCount(count);
    var charBuffer = new char[maxCharCount];
    int charsRead = textReader.Read(charBuffer, 0, maxCharCount);
    if (charsRead == 0) {
      return 0;
    }

    var bytesToWrite = encoding.GetBytes(charBuffer);
    Array.Copy(bytesToWrite, 0, buffer, offset, count);
    remainder = bytesToWrite;
    remainderOffset = count;
    
    return Math.Max(count, bytesToWrite.Length);
  }

  public override long Seek(long offset, SeekOrigin origin)
  {
    throw new NotSupportedException();
  }

  public override void SetLength(long value)
  {
    throw new NotSupportedException();
  }

  public override void Write(byte[] buffer, int offset, int count)
  {
    throw new NotSupportedException();
  }

  public override void Flush()
  {
    throw new NotSupportedException();
  }
}