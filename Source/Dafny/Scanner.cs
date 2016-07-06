
using System;
using System.IO;
using System.Collections;
using System.Collections.Generic;
using System.Text;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;


namespace Microsoft.Dafny {

//-----------------------------------------------------------------------------------
// Buffer
//-----------------------------------------------------------------------------------
public class Buffer {
	// This Buffer supports the following cases:
	// 1) seekable stream (file)
	//    a) whole stream in buffer
	//    b) part of stream in buffer
	// 2) non seekable stream (network, console)

	public const int EOF = 65535 + 1; // char.MaxValue + 1;
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
		int oldPos = Pos;
		Pos = beg;
		while (Pos < end) buf[len++] = (char) Read();
		Pos = oldPos;
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
	public UTF8Buffer(Buffer/*!*/ b): base(b) {Contract.Requires(b != null);}

	public override int Read() {
		int ch;
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
		return ch;
	}
}

//-----------------------------------------------------------------------------------
// Scanner
//-----------------------------------------------------------------------------------
public class Scanner {
	const char EOL = '\n';
	const int eofSym = 0; /* pdt */
	const int maxT = 142;
	const int noSym = 142;


	[ContractInvariantMethod]
	void objectInvariant(){
		Contract.Invariant(this._buffer != null);
		Contract.Invariant(t != null);
		Contract.Invariant(start != null);
		Contract.Invariant(tokens != null);
		Contract.Invariant(pt != null);
		Contract.Invariant(tval != null);
		Contract.Invariant(Filename != null);
		Contract.Invariant(FullFilename != null);
		Contract.Invariant(errorHandler != null);
	}

	private Buffer/*!*/ _buffer; // scanner buffer

	public Buffer/*!*/ buffer {
		get {
			Contract.Ensures(Contract.Result<Buffer>() != null);
			return this._buffer;
		}
		set {
			Contract.Requires(value != null);
			this._buffer = value;
		}
	}

	Token/*!*/ t;          // current token
	int ch;           // current input character
	int pos;          // byte position of current character
	int charPos;
	int col;          // column number of current character
	int line;         // line number of current character
	int oldEols;      // EOLs that appeared in a comment;
	static readonly Hashtable/*!*/ start; // maps first token character to start state

	Token/*!*/ tokens;     // list of tokens already peeked (first token is a dummy)
	Token/*!*/ pt;         // current peek token

	char[]/*!*/ tval = new char[128]; // text of current token
	int tlen;         // length of current token

	private string/*!*/ Filename;
	private Errors/*!*/ errorHandler;

	internal string/*!*/ FullFilename { get; private set; }

	static Scanner() {
		start = new Hashtable(128);
		for (int i = 63; i <= 63; ++i) start[i] = 1;
		for (int i = 65; i <= 90; ++i) start[i] = 1;
		for (int i = 95; i <= 95; ++i) start[i] = 1;
		for (int i = 98; i <= 122; ++i) start[i] = 1;
		for (int i = 49; i <= 57; ++i) start[i] = 49;
		start[97] = 50; 
		start[39] = 51; 
		start[48] = 52; 
		start[34] = 21; 
		start[64] = 26; 
		start[58] = 89; 
		start[44] = 29; 
		start[124] = 90; 
		start[8226] = 32; 
		start[46] = 91; 
		start[59] = 33; 
		start[61] = 92; 
		start[45] = 93; 
		start[123] = 36; 
		start[125] = 37; 
		start[91] = 38; 
		start[93] = 39; 
		start[40] = 40; 
		start[41] = 41; 
		start[60] = 94; 
		start[62] = 95; 
		start[33] = 96; 
		start[8800] = 43; 
		start[42] = 44; 
		start[96] = 67; 
		start[35] = 69; 
		start[8804] = 71; 
		start[8805] = 72; 
		start[8660] = 74; 
		start[8658] = 76; 
		start[8656] = 77; 
		start[38] = 78; 
		start[8743] = 80; 
		start[8744] = 82; 
		start[172] = 83; 
		start[8704] = 84; 
		start[8707] = 85; 
		start[43] = 86; 
		start[47] = 87; 
		start[37] = 88; 
		start[Buffer.EOF] = -1;

	}

//	[NotDelayed]
	public Scanner (string/*!*/ fullFilename, string/*!*/ fileName, Errors/*!*/ errorHandler, bool useBaseName = false) : base() {
		Contract.Requires(fileName != null);
		Contract.Requires(errorHandler != null);
		this.errorHandler = errorHandler;
		pt = tokens = new Token();  // first token is a dummy
		t = new Token(); // dummy because t is a non-null field
		try {
			Stream stream = new FileStream(fileName, FileMode.Open, FileAccess.Read, FileShare.Read);
			this._buffer = new Buffer(stream, false);
			this.FullFilename = fullFilename;
			Filename = useBaseName? GetBaseName(fileName): fileName;
			Init(1);
		} catch (IOException) {
			throw new FatalError("Cannot open file " + fileName);
		}
	}

//	[NotDelayed]
	public Scanner (Stream/*!*/ s, Errors/*!*/ errorHandler, string/*!*/ fullFilename, string/*!*/ fileName, int lineNumber = 1, bool useBaseName = false) : base() {
		Contract.Requires(s != null);
		Contract.Requires(errorHandler != null);
		Contract.Requires(fileName != null);
		pt = tokens = new Token();  // first token is a dummy
		t = new Token(); // dummy because t is a non-null field
		this._buffer = new Buffer(s, true);
		this.errorHandler = errorHandler;
		this.FullFilename = fullFilename;
		this.Filename = useBaseName? GetBaseName(fileName) : fileName;
		Init(lineNumber);
	}

	string GetBaseName(string fileName) {
		return System.IO.Path.GetFileName(fileName); // Return basename
	}

	void Init(int lineNumber) {
		pos = -1; line = lineNumber; col = 0;
		oldEols = 0;
		NextCh();
		if (ch == 0xEF) { // check optional byte order mark for UTF-8
			NextCh(); int ch1 = ch;
			NextCh(); int ch2 = ch;
			if (ch1 != 0xBB || ch2 != 0xBF) {
				throw new FatalError(String.Format("illegal byte order mark: EF {0,2:X} {1,2:X}", ch1, ch2));
			}
			buffer = new UTF8Buffer(buffer); col = 0;
			NextCh();
		}
		pt = tokens = new Token();  // first token is a dummy
	}

	string/*!*/ ReadToEOL(){
	Contract.Ensures(Contract.Result<string>() != null);
	  int p = buffer.Pos;
	  int ch = buffer.Read();
	  // replace isolated '\r' by '\n' in order to make
	  // eol handling uniform across Windows, Unix and Mac
	  if (ch == '\r' && buffer.Peek() != '\n') ch = EOL;
	  while (ch != EOL && ch != Buffer.EOF){
		ch = buffer.Read();
		// replace isolated '\r' by '\n' in order to make
		// eol handling uniform across Windows, Unix and Mac
		if (ch == '\r' && buffer.Peek() != '\n') ch = EOL;
	  }
	  string/*!*/ s = buffer.GetString(p, buffer.Pos);
	  Contract.Assert(s!=null);
	  return s;
	}

	void NextCh() {
		if (oldEols > 0) { ch = EOL; oldEols--; }
		else {
//			pos = buffer.Pos;
//			ch = buffer.Read(); col++;
//			// replace isolated '\r' by '\n' in order to make
//			// eol handling uniform across Windows, Unix and Mac
//			if (ch == '\r' && buffer.Peek() != '\n') ch = EOL;
//			if (ch == EOL) { line++; col = 0; }

			while (true) {
				pos = buffer.Pos;
				ch = buffer.Read(); col++;
				// replace isolated '\r' by '\n' in order to make
				// eol handling uniform across Windows, Unix and Mac
				if (ch == '\r' && buffer.Peek() != '\n') ch = EOL;
				if (ch == EOL) {
					line++; col = 0;
				} else if (ch == '#' && col == 1) {
				  int prLine = line;
				  int prColumn = 0;

				  string/*!*/ hashLine = ReadToEOL();
				  Contract.Assert(hashLine!=null);
				  col = 0;
				  line++;

				  hashLine = hashLine.TrimEnd(null);
				  if (hashLine.StartsWith("line ") || hashLine == "line") {
					// parse #line pragma:  #line num [filename]
					string h = hashLine.Substring(4).TrimStart(null);
					int x = h.IndexOf(' ');
					if (x == -1) {
					  x = h.Length;  // this will be convenient below when we look for a filename
					}
					try {
					  int li = int.Parse(h.Substring(0, x));

					  h = h.Substring(x).Trim();

					  // act on #line
					  line = li;
					  if (h.Length != 0) {
						// a filename was specified
						Filename = h;
					  }
					  continue;  // successfully parsed and acted on the #line pragma

					} catch (FormatException) {
					  // just fall down through to produce an error message
					}
					this.errorHandler.SemErr(Filename, prLine, prColumn, "Malformed (#line num [filename]) pragma: #" + hashLine);
					continue;
				  }

				  this.errorHandler.SemErr(Filename, prLine, prColumn, "Unrecognized pragma: #" + hashLine);
				  continue;
				}
				return;
			  }


		}

	}

	void AddCh() {
		if (tlen >= tval.Length) {
			char[] newBuf = new char[2 * tval.Length];
			Array.Copy(tval, 0, newBuf, 0, tval.Length);
			tval = newBuf;
		}
		if (ch != Buffer.EOF) {
			tval[tlen++] = (char) ch;
			NextCh();
		}
	}



	bool Comment0() {
		int level = 1, pos0 = pos, line0 = line, col0 = col, charPos0 = charPos;
		NextCh();
		if (ch == '/') {
			NextCh();
			for(;;) {
				if (ch == 10) {
					level--;
					if (level == 0) { oldEols = line - line0; NextCh(); return true; }
					NextCh();
				} else if (ch == Buffer.EOF) return false;
				else NextCh();
			}
		} else {
			buffer.Pos = pos0; NextCh(); line = line0; col = col0; charPos = charPos0;
		}
		return false;
	}

	bool Comment1() {
		int level = 1, pos0 = pos, line0 = line, col0 = col, charPos0 = charPos;
		NextCh();
		if (ch == '*') {
			NextCh();
			for(;;) {
				if (ch == '*') {
					NextCh();
					if (ch == '/') {
						level--;
						if (level == 0) { oldEols = line - line0; NextCh(); return true; }
						NextCh();
					}
				} else if (ch == '/') {
					NextCh();
					if (ch == '*') {
						level++; NextCh();
					}
				} else if (ch == Buffer.EOF) return false;
				else NextCh();
			}
		} else {
			buffer.Pos = pos0; NextCh(); line = line0; col = col0; charPos = charPos0;
		}
		return false;
	}


	public void CheckLiteral() {
		switch (t.val) {
			case "bool": t.kind = 6; break;
			case "char": t.kind = 7; break;
			case "int": t.kind = 8; break;
			case "nat": t.kind = 9; break;
			case "real": t.kind = 10; break;
			case "object": t.kind = 11; break;
			case "string": t.kind = 12; break;
			case "set": t.kind = 13; break;
			case "iset": t.kind = 14; break;
			case "multiset": t.kind = 15; break;
			case "seq": t.kind = 16; break;
			case "map": t.kind = 17; break;
			case "imap": t.kind = 18; break;
			case "assume": t.kind = 31; break;
			case "calc": t.kind = 32; break;
			case "case": t.kind = 33; break;
			case "then": t.kind = 34; break;
			case "else": t.kind = 35; break;
			case "decreases": t.kind = 36; break;
			case "invariant": t.kind = 37; break;
			case "function": t.kind = 38; break;
			case "predicate": t.kind = 39; break;
			case "inductive": t.kind = 40; break;
			case "lemma": t.kind = 41; break;
			case "copredicate": t.kind = 42; break;
			case "modifies": t.kind = 43; break;
			case "reads": t.kind = 44; break;
			case "requires": t.kind = 45; break;
			case "include": t.kind = 60; break;
			case "abstract": t.kind = 61; break;
			case "ghost": t.kind = 62; break;
			case "static": t.kind = 63; break;
			case "protected": t.kind = 64; break;
			case "extern": t.kind = 65; break;
			case "module": t.kind = 66; break;
			case "exclusively": t.kind = 67; break;
			case "refines": t.kind = 68; break;
			case "import": t.kind = 69; break;
			case "opened": t.kind = 70; break;
			case "as": t.kind = 72; break;
			case "default": t.kind = 73; break;
			case "export": t.kind = 74; break;
			case "opaque": t.kind = 75; break;
			case "reveal": t.kind = 76; break;
			case "extends": t.kind = 77; break;
			case "class": t.kind = 78; break;
			case "trait": t.kind = 79; break;
			case "datatype": t.kind = 80; break;
			case "codatatype": t.kind = 81; break;
			case "var": t.kind = 82; break;
			case "newtype": t.kind = 83; break;
			case "type": t.kind = 84; break;
			case "iterator": t.kind = 85; break;
			case "yields": t.kind = 86; break;
			case "returns": t.kind = 87; break;
			case "method": t.kind = 88; break;
			case "colemma": t.kind = 89; break;
			case "comethod": t.kind = 90; break;
			case "constructor": t.kind = 91; break;
			case "free": t.kind = 92; break;
			case "ensures": t.kind = 93; break;
			case "yield": t.kind = 94; break;
			case "label": t.kind = 96; break;
			case "break": t.kind = 97; break;
			case "where": t.kind = 98; break;
			case "return": t.kind = 100; break;
			case "new": t.kind = 101; break;
			case "if": t.kind = 102; break;
			case "while": t.kind = 103; break;
			case "match": t.kind = 104; break;
			case "assert": t.kind = 105; break;
			case "print": t.kind = 106; break;
			case "forall": t.kind = 107; break;
			case "parallel": t.kind = 108; break;
			case "modify": t.kind = 109; break;
			case "exists": t.kind = 128; break;
			case "in": t.kind = 130; break;
			case "false": t.kind = 135; break;
			case "true": t.kind = 136; break;
			case "null": t.kind = 137; break;
			case "this": t.kind = 138; break;
			case "fresh": t.kind = 139; break;
			case "old": t.kind = 140; break;
			default: break;
		}
	}

	Token/*!*/ NextToken() {
	  Contract.Ensures(Contract.Result<Token>() != null);
		while (ch == ' ' ||
			ch >= 9 && ch <= 10 || ch == 13
		) NextCh();
		if (ch == '/' && Comment0() ||ch == '/' && Comment1()) return NextToken();
		int apx = 0;
		int recKind = noSym;
		int recEnd = pos;
		t = new Token();
		t.pos = pos; t.col = col; t.line = line;
		t.filename = this.Filename;
		int state;
		if (start.ContainsKey(ch)) {
			Contract.Assert(start[ch] != null);
			state = (int) start[ch];
		}
		else { state = 0; }
		tlen = 0; AddCh();

		switch (state) {
			case -1: { t.kind = eofSym; break; } // NextCh already done
			case 0: {
				if (recKind != noSym) {
					tlen = recEnd - t.pos;
					SetScannerBehindT();
				}
				t.kind = recKind; break;
			} // NextCh already done
			case 1:
				recEnd = pos; recKind = 1;
				if (ch == 39 || ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'z') {AddCh(); goto case 1;}
				else {t.kind = 1; t.val = new String(tval, 0, tlen); CheckLiteral(); return t;}
			case 2:
				recEnd = pos; recKind = 1;
				if (ch == 39 || ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'z') {AddCh(); goto case 2;}
				else {t.kind = 1; t.val = new String(tval, 0, tlen); CheckLiteral(); return t;}
			case 3:
				recEnd = pos; recKind = 1;
				if (ch == 39 || ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'z') {AddCh(); goto case 3;}
				else {t.kind = 1; t.val = new String(tval, 0, tlen); CheckLiteral(); return t;}
			case 4:
				recEnd = pos; recKind = 1;
				if (ch == 39 || ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'z') {AddCh(); goto case 4;}
				else {t.kind = 1; t.val = new String(tval, 0, tlen); CheckLiteral(); return t;}
			case 5:
				recEnd = pos; recKind = 1;
				if (ch == 39 || ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'z') {AddCh(); goto case 5;}
				else {t.kind = 1; t.val = new String(tval, 0, tlen); CheckLiteral(); return t;}
			case 6:
				recEnd = pos; recKind = 1;
				if (ch == 39 || ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'z') {AddCh(); goto case 6;}
				else {t.kind = 1; t.val = new String(tval, 0, tlen); CheckLiteral(); return t;}
			case 7:
				if (ch == 39 || ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'z') {AddCh(); goto case 8;}
				else {goto case 0;}
			case 8:
				recEnd = pos; recKind = 1;
				if (ch == 39 || ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'z') {AddCh(); goto case 8;}
				else {t.kind = 1; t.val = new String(tval, 0, tlen); CheckLiteral(); return t;}
			case 9:
				if (ch >= '0' && ch <= '9' || ch >= 'A' && ch <= 'F' || ch >= 'a' && ch <= 'f') {AddCh(); goto case 10;}
				else {goto case 0;}
			case 10:
				recEnd = pos; recKind = 3;
				if (ch >= '0' && ch <= '9' || ch >= 'A' && ch <= 'F' || ch >= 'a' && ch <= 'f') {AddCh(); goto case 10;}
				else if (ch == '_') {AddCh(); goto case 11;}
				else {t.kind = 3; break;}
			case 11:
				if (ch >= '0' && ch <= '9' || ch >= 'A' && ch <= 'F' || ch >= 'a' && ch <= 'f') {AddCh(); goto case 10;}
				else {goto case 0;}
			case 12:
				if (ch >= '0' && ch <= '9') {AddCh(); goto case 13;}
				else {goto case 0;}
			case 13:
				recEnd = pos; recKind = 4;
				if (ch >= '0' && ch <= '9') {AddCh(); goto case 13;}
				else if (ch == '_') {AddCh(); goto case 14;}
				else {t.kind = 4; break;}
			case 14:
				if (ch >= '0' && ch <= '9') {AddCh(); goto case 13;}
				else {goto case 0;}
			case 15:
				if (ch == 39) {AddCh(); goto case 20;}
				else {goto case 0;}
			case 16:
				if (ch >= '0' && ch <= '9' || ch >= 'A' && ch <= 'F' || ch >= 'a' && ch <= 'f') {AddCh(); goto case 17;}
				else {goto case 0;}
			case 17:
				if (ch >= '0' && ch <= '9' || ch >= 'A' && ch <= 'F' || ch >= 'a' && ch <= 'f') {AddCh(); goto case 18;}
				else {goto case 0;}
			case 18:
				if (ch >= '0' && ch <= '9' || ch >= 'A' && ch <= 'F' || ch >= 'a' && ch <= 'f') {AddCh(); goto case 19;}
				else {goto case 0;}
			case 19:
				if (ch >= '0' && ch <= '9' || ch >= 'A' && ch <= 'F' || ch >= 'a' && ch <= 'f') {AddCh(); goto case 15;}
				else {goto case 0;}
			case 20:
				{t.kind = 19; break;}
			case 21:
				if (ch <= 9 || ch >= 11 && ch <= 12 || ch >= 14 && ch <= '!' || ch >= '#' && ch <= '[' || ch >= ']' && ch <= 65535) {AddCh(); goto case 21;}
				else if (ch == '"') {AddCh(); goto case 28;}
				else if (ch == 92) {AddCh(); goto case 55;}
				else {goto case 0;}
			case 22:
				if (ch >= '0' && ch <= '9' || ch >= 'A' && ch <= 'F' || ch >= 'a' && ch <= 'f') {AddCh(); goto case 23;}
				else {goto case 0;}
			case 23:
				if (ch >= '0' && ch <= '9' || ch >= 'A' && ch <= 'F' || ch >= 'a' && ch <= 'f') {AddCh(); goto case 24;}
				else {goto case 0;}
			case 24:
				if (ch >= '0' && ch <= '9' || ch >= 'A' && ch <= 'F' || ch >= 'a' && ch <= 'f') {AddCh(); goto case 25;}
				else {goto case 0;}
			case 25:
				if (ch >= '0' && ch <= '9' || ch >= 'A' && ch <= 'F' || ch >= 'a' && ch <= 'f') {AddCh(); goto case 21;}
				else {goto case 0;}
			case 26:
				if (ch == '"') {AddCh(); goto case 27;}
				else {goto case 0;}
			case 27:
				if (ch <= '!' || ch >= '#' && ch <= 65535) {AddCh(); goto case 27;}
				else if (ch == '"') {AddCh(); goto case 56;}
				else {goto case 0;}
			case 28:
				{t.kind = 20; break;}
			case 29:
				{t.kind = 22; break;}
			case 30:
				{t.kind = 24; break;}
			case 31:
				{t.kind = 25; break;}
			case 32:
				{t.kind = 26; break;}
			case 33:
				{t.kind = 28; break;}
			case 34:
				{t.kind = 29; break;}
			case 35:
				{t.kind = 30; break;}
			case 36:
				{t.kind = 46; break;}
			case 37:
				{t.kind = 47; break;}
			case 38:
				{t.kind = 48; break;}
			case 39:
				{t.kind = 49; break;}
			case 40:
				{t.kind = 50; break;}
			case 41:
				{t.kind = 51; break;}
			case 42:
				{t.kind = 55; break;}
			case 43:
				{t.kind = 56; break;}
			case 44:
				{t.kind = 57; break;}
			case 45:
				if (ch == 'n') {AddCh(); goto case 46;}
				else {goto case 0;}
			case 46:
				if (ch <= '&' || ch >= '(' && ch <= '/' || ch >= ':' && ch <= '>' || ch == '@' || ch >= '[' && ch <= '^' || ch == '`' || ch >= '{' && ch <= 65535) {apx++; AddCh(); goto case 47;}
				else {goto case 0;}
			case 47:
				{
					tlen -= apx;
					SetScannerBehindT();
					t.kind = 58; break;}
			case 48:
				{t.kind = 59; break;}
			case 49:
				recEnd = pos; recKind = 2;
				if (ch >= '0' && ch <= '9') {AddCh(); goto case 49;}
				else if (ch == '_') {AddCh(); goto case 57;}
				else if (ch == '.') {AddCh(); goto case 12;}
				else {t.kind = 2; break;}
			case 50:
				recEnd = pos; recKind = 1;
				if (ch == 39 || ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'q' || ch >= 's' && ch <= 'z') {AddCh(); goto case 2;}
				else if (ch == 'r') {AddCh(); goto case 58;}
				else {t.kind = 1; t.val = new String(tval, 0, tlen); CheckLiteral(); return t;}
			case 51:
				recEnd = pos; recKind = 1;
				if (ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'z') {AddCh(); goto case 59;}
				else if (ch == 39) {AddCh(); goto case 60;}
				else if (ch <= 9 || ch >= 11 && ch <= 12 || ch >= 14 && ch <= '&' || ch >= '(' && ch <= '/' || ch >= ':' && ch <= '>' || ch == '@' || ch == '[' || ch >= ']' && ch <= '^' || ch == '`' || ch >= '{' && ch <= 65535) {AddCh(); goto case 15;}
				else if (ch == 92) {AddCh(); goto case 54;}
				else {t.kind = 1; t.val = new String(tval, 0, tlen); CheckLiteral(); return t;}
			case 52:
				recEnd = pos; recKind = 2;
				if (ch >= '0' && ch <= '9') {AddCh(); goto case 49;}
				else if (ch == '_') {AddCh(); goto case 57;}
				else if (ch == 'x') {AddCh(); goto case 9;}
				else if (ch == '.') {AddCh(); goto case 12;}
				else {t.kind = 2; break;}
			case 53:
				recEnd = pos; recKind = 1;
				if (ch == 39 || ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'z') {AddCh(); goto case 53;}
				else {t.kind = 1; t.val = new String(tval, 0, tlen); CheckLiteral(); return t;}
			case 54:
				if (ch == '"' || ch == 39 || ch == '0' || ch == 92 || ch == 'n' || ch == 'r' || ch == 't') {AddCh(); goto case 15;}
				else if (ch == 'u') {AddCh(); goto case 16;}
				else {goto case 0;}
			case 55:
				if (ch == '"' || ch == 39 || ch == '0' || ch == 92 || ch == 'n' || ch == 'r' || ch == 't') {AddCh(); goto case 21;}
				else if (ch == 'u') {AddCh(); goto case 22;}
				else {goto case 0;}
			case 56:
				recEnd = pos; recKind = 20;
				if (ch == '"') {AddCh(); goto case 27;}
				else {t.kind = 20; break;}
			case 57:
				if (ch >= '0' && ch <= '9') {AddCh(); goto case 49;}
				else {goto case 0;}
			case 58:
				recEnd = pos; recKind = 1;
				if (ch == 39 || ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'q' || ch >= 's' && ch <= 'z') {AddCh(); goto case 3;}
				else if (ch == 'r') {AddCh(); goto case 61;}
				else {t.kind = 1; t.val = new String(tval, 0, tlen); CheckLiteral(); return t;}
			case 59:
				recEnd = pos; recKind = 1;
				if (ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'z') {AddCh(); goto case 62;}
				else if (ch == 39) {AddCh(); goto case 63;}
				else {t.kind = 1; t.val = new String(tval, 0, tlen); CheckLiteral(); return t;}
			case 60:
				recEnd = pos; recKind = 1;
				if (ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'z') {AddCh(); goto case 62;}
				else if (ch == 39) {AddCh(); goto case 7;}
				else {t.kind = 1; t.val = new String(tval, 0, tlen); CheckLiteral(); return t;}
			case 61:
				recEnd = pos; recKind = 1;
				if (ch == 39 || ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'b' && ch <= 'z') {AddCh(); goto case 4;}
				else if (ch == 'a') {AddCh(); goto case 64;}
				else {t.kind = 1; t.val = new String(tval, 0, tlen); CheckLiteral(); return t;}
			case 62:
				recEnd = pos; recKind = 1;
				if (ch == 39 || ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'z') {AddCh(); goto case 8;}
				else {t.kind = 1; t.val = new String(tval, 0, tlen); CheckLiteral(); return t;}
			case 63:
				recEnd = pos; recKind = 19;
				if (ch == 39 || ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'z') {AddCh(); goto case 8;}
				else {t.kind = 19; break;}
			case 64:
				recEnd = pos; recKind = 1;
				if (ch == 39 || ch >= '0' && ch <= '9' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'x' || ch == 'z') {AddCh(); goto case 5;}
				else if (ch == 'y') {AddCh(); goto case 65;}
				else {t.kind = 1; t.val = new String(tval, 0, tlen); CheckLiteral(); return t;}
			case 65:
				recEnd = pos; recKind = 5;
				if (ch == 39 || ch == '0' || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'z') {AddCh(); goto case 6;}
				else if (ch >= '1' && ch <= '9') {AddCh(); goto case 66;}
				else {t.kind = 5; break;}
			case 66:
				recEnd = pos; recKind = 5;
				if (ch == 39 || ch == '?' || ch >= 'A' && ch <= 'Z' || ch == '_' || ch >= 'a' && ch <= 'z') {AddCh(); goto case 53;}
				else if (ch >= '0' && ch <= '9') {AddCh(); goto case 66;}
				else {t.kind = 5; break;}
			case 67:
				{t.kind = 95; break;}
			case 68:
				{t.kind = 99; break;}
			case 69:
				{t.kind = 110; break;}
			case 70:
				{t.kind = 112; break;}
			case 71:
				{t.kind = 113; break;}
			case 72:
				{t.kind = 114; break;}
			case 73:
				{t.kind = 115; break;}
			case 74:
				{t.kind = 116; break;}
			case 75:
				{t.kind = 117; break;}
			case 76:
				{t.kind = 118; break;}
			case 77:
				{t.kind = 120; break;}
			case 78:
				if (ch == '&') {AddCh(); goto case 79;}
				else {goto case 0;}
			case 79:
				{t.kind = 121; break;}
			case 80:
				{t.kind = 122; break;}
			case 81:
				{t.kind = 123; break;}
			case 82:
				{t.kind = 124; break;}
			case 83:
				{t.kind = 126; break;}
			case 84:
				{t.kind = 127; break;}
			case 85:
				{t.kind = 129; break;}
			case 86:
				{t.kind = 131; break;}
			case 87:
				{t.kind = 133; break;}
			case 88:
				{t.kind = 134; break;}
			case 89:
				recEnd = pos; recKind = 21;
				if (ch == ':') {AddCh(); goto case 30;}
				else if (ch == '|') {AddCh(); goto case 31;}
				else if (ch == '=') {AddCh(); goto case 68;}
				else {t.kind = 21; break;}
			case 90:
				recEnd = pos; recKind = 23;
				if (ch == '|') {AddCh(); goto case 81;}
				else {t.kind = 23; break;}
			case 91:
				recEnd = pos; recKind = 27;
				if (ch == '.') {AddCh(); goto case 97;}
				else {t.kind = 27; break;}
			case 92:
				recEnd = pos; recKind = 71;
				if (ch == '>') {AddCh(); goto case 34;}
				else if (ch == '=') {AddCh(); goto case 98;}
				else {t.kind = 71; break;}
			case 93:
				recEnd = pos; recKind = 132;
				if (ch == '>') {AddCh(); goto case 35;}
				else {t.kind = 132; break;}
			case 94:
				recEnd = pos; recKind = 52;
				if (ch == '=') {AddCh(); goto case 99;}
				else {t.kind = 52; break;}
			case 95:
				recEnd = pos; recKind = 53;
				if (ch == '=') {AddCh(); goto case 70;}
				else {t.kind = 53; break;}
			case 96:
				recEnd = pos; recKind = 125;
				if (ch == '=') {AddCh(); goto case 42;}
				else if (ch == 'i') {AddCh(); goto case 45;}
				else {t.kind = 125; break;}
			case 97:
				recEnd = pos; recKind = 141;
				if (ch == '.') {AddCh(); goto case 48;}
				else {t.kind = 141; break;}
			case 98:
				recEnd = pos; recKind = 54;
				if (ch == '>') {AddCh(); goto case 75;}
				else {t.kind = 54; break;}
			case 99:
				recEnd = pos; recKind = 111;
				if (ch == '=') {AddCh(); goto case 100;}
				else {t.kind = 111; break;}
			case 100:
				recEnd = pos; recKind = 119;
				if (ch == '>') {AddCh(); goto case 73;}
				else {t.kind = 119; break;}

		}
		t.val = new String(tval, 0, tlen);
		return t;
	}

	private void SetScannerBehindT() {
		buffer.Pos = t.pos;
		NextCh();
		line = t.line; col = t.col;
		for (int i = 0; i < tlen; i++) NextCh();
	}

	// get the next token (possibly a token already seen during peeking)
	public Token/*!*/ Scan () {
	 Contract.Ensures(Contract.Result<Token>() != null);
		if (tokens.next == null) {
			return NextToken();
		} else {
			pt = tokens = tokens.next;
			return tokens;
		}
	}

	// peek for the next token, ignore pragmas
	public Token/*!*/ Peek () {
	  Contract.Ensures(Contract.Result<Token>() != null);
		do {
			if (pt.next == null) {
				pt.next = NextToken();
			}
			pt = pt.next;
		} while (pt.kind > maxT); // skip pragmas

		return pt;
	}

	// make sure that peeking starts at the current scan position
	public void ResetPeek () { pt = tokens; }

} // end Scanner

public delegate void ErrorProc(int n, string filename, int line, int col);
}