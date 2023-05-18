using System;
using System.Diagnostics.Contracts;
using System.IO;

namespace Microsoft.Dafny;

/// <summary>
/// The ints returned are UTF8
/// </summary>

public class Buffer {
  // This Buffer supports the following cases:
  // 1) seekable stream (file)
  //    a) whole stream in buffer
  //    b) part of stream in buffer
  // 2) non seekable stream (network, console)

  public const int EOF = 0x11_0000; // Maximum Unicode codepoint + 1;
  const int MIN_BUFFER_LENGTH = 1024; // 1KB
  const int MAX_BUFFER_LENGTH = MIN_BUFFER_LENGTH * 64; // 64KB
  byte[]/*!*/ buf;         // input buffer
  int bufStart;       // position of first byte in buffer relative to input stream
  int bufLen;         // length of buffer
  int fileLen;        // length of input stream (may change if the stream is no file)
  int bufPos;         // current position in buffer
  Stream/*!*/ stream;      // input stream (seekable)
  bool isUserStream;  // was the stream opened by the user?

  [ContractInvariantMethod]
  void ObjectInvariant(){
    Contract.Invariant(buf != null);
    Contract.Invariant(stream != null);
  }

//  [NotDelayed]
  public Buffer (Stream/*!*/ s, bool isUserStream) : base() {
    Contract.Requires(s != null);
    stream = s; this.isUserStream = isUserStream;

    int fl, bl;
    if (s.CanSeek) {
      fl = (int) s.Length;
      bl = fl < MAX_BUFFER_LENGTH ? fl : MAX_BUFFER_LENGTH; // Math.Min(fileLen, MAX_BUFFER_LENGTH);
      bufStart = Int32.MaxValue; // nothing in the buffer so far
    } else {
      fl = bl = bufStart = 0;
    }

    buf = new byte[(bl>0) ? bl : MIN_BUFFER_LENGTH];
    fileLen = fl;  bufLen = bl;

    if (fileLen > 0) Pos = 0; // setup buffer to position 0 (start)
    else bufPos = 0; // index 0 is already after the file, thus Pos = 0 is invalid
    if (bufLen == fileLen && s.CanSeek) Close();
  }

  protected Buffer(Buffer/*!*/ b) { // called in UTF8Buffer constructor
    Contract.Requires(b != null);
    buf = b.buf;
    bufStart = b.bufStart;
    bufLen = b.bufLen;
    fileLen = b.fileLen;
    bufPos = b.bufPos;
    stream = b.stream;
    // keep destructor from closing the stream
    //b.stream = null;
    isUserStream = b.isUserStream;
    // keep destructor from closing the stream
    b.isUserStream = true;
  }

  ~Buffer() { Close(); }

  protected void Close() {
    if (!isUserStream && stream != null) {
      stream.Close();
      //stream = null;
    }
  }

  public virtual int Read () {
    if (bufPos < bufLen) {
      return buf[bufPos++];
    } else if (Pos < fileLen) {
      Pos = Pos; // shift buffer start to Pos
      return buf[bufPos++];
    } else if (stream != null && !stream.CanSeek && ReadNextStreamChunk() > 0) {
      return buf[bufPos++];
    } else {
      return EOF;
    }
  }

  public int Peek () {
    int curPos = Pos;
    int ch = Read();
    Pos = curPos;
    return ch;
  }

  public string/*!*/ GetString (int beg, int end) {
    Contract.Ensures(Contract.Result<string>() != null);
    int len = 0;
    char[] buf = new char[end - beg];
    if(end != beg) {
      int oldPos = Pos;
      Pos = beg;
      while (Pos < end) {
        buf[len++] = (char) Read();
      }

      Pos = oldPos;
    }
    return new String(buf, 0, len);
  }

  public int Pos {
    get { return bufPos + bufStart; }
    set {
      if (value >= fileLen && stream != null && !stream.CanSeek) {
        // Wanted position is after buffer and the stream
        // is not seek-able e.g. network or console,
        // thus we have to read the stream manually till
        // the wanted position is in sight.
        while (value >= fileLen && ReadNextStreamChunk() > 0);
      }

      if (value < 0 || value > fileLen) {
        throw new FatalError("buffer out of bounds access, position: " + value);
      }

      if (value >= bufStart && value < bufStart + bufLen) { // already in buffer
        bufPos = value - bufStart;
      } else if (stream != null) { // must be swapped in
        stream.Seek(value, SeekOrigin.Begin);
        bufLen = stream.Read(buf, 0, buf.Length);
        bufStart = value; bufPos = 0;
      } else {
        // set the position to the end of the file, Pos will return fileLen.
        bufPos = fileLen - bufStart;
      }
    }
  }

  // Read the next chunk of bytes from the stream, increases the buffer
  // if needed and updates the fields fileLen and bufLen.
  // Returns the number of bytes read.
  private int ReadNextStreamChunk() {
    int free = buf.Length - bufLen;
    if (free == 0) {
      // in the case of a growing input stream
      // we can neither seek in the stream, nor can we
      // foresee the maximum length, thus we must adapt
      // the buffer size on demand.
      byte[] newBuf = new byte[bufLen * 2];
      Array.Copy(buf, newBuf, bufLen);
      buf = newBuf;
      free = bufLen;
    }
    int read = stream.Read(buf, bufLen, free);
    if (read > 0) {
      fileLen = bufLen = (bufLen + read);
      return read;
    }
    // end of stream reached
    return 0;
  }
}

//-----------------------------------------------------------------------------------
// UTF8Buffer
//-----------------------------------------------------------------------------------
public class UTF8Buffer: Buffer {
  private int pendingLowSurrogate = -1;
  public UTF8Buffer(Buffer/*!*/ b): base(b) {Contract.Requires(b != null);}

  public override int Read() {
    int ch;
    if (pendingLowSurrogate != -1) {
      ch = pendingLowSurrogate;
      pendingLowSurrogate = -1;
      return ch;
    }
    do {
      ch = base.Read();
      // until we find a utf8 start (0xxxxxxx or 11xxxxxx)
    } while ((ch >= 128) && ((ch & 0xC0) != 0xC0) && (ch != EOF));
    if (ch < 128 || ch == EOF) {
      // nothing to do, first 127 chars are the same in ascii and utf8
      // 0xxxxxxx or end of file character
    } else if ((ch & 0xF0) == 0xF0) {
      // 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
      int c1 = ch & 0x07; ch = base.Read();
      int c2 = ch & 0x3F; ch = base.Read();
      int c3 = ch & 0x3F; ch = base.Read();
      int c4 = ch & 0x3F;
      ch = (((((c1 << 6) | c2) << 6) | c3) << 6) | c4;
    } else if ((ch & 0xE0) == 0xE0) {
      // 1110xxxx 10xxxxxx 10xxxxxx
      int c1 = ch & 0x0F; ch = base.Read();
      int c2 = ch & 0x3F; ch = base.Read();
      int c3 = ch & 0x3F;
      ch = (((c1 << 6) | c2) << 6) | c3;
    } else if ((ch & 0xC0) == 0xC0) {
      // 110xxxxx 10xxxxxx
      int c1 = ch & 0x1F; ch = base.Read();
      int c2 = ch & 0x3F;
      ch = (c1 << 6) | c2;
    }
    if (0x10000 <= ch && ch < 0x11_0000) {
      ch = ch - 0x10000; 
      pendingLowSurrogate = 0xDC00 + (ch & 0x3FF);
      ch = 0xD800 + ((ch >> 10) & 0x3FF);
    }
    return ch;
  }
}