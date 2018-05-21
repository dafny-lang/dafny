using System;
using System.Collections.Generic;
using System.Text;
using System.IO;

namespace DocumentationTransducer
{
  class Program
  {
    static bool IsKeyword(string ident) {
      switch (ident) {
        case "array":
        case "as":
        case "assert":
        case "bool":
        case "break":
        case "class":
        case "constructor":
        case "datatype":
        case "decreases":
        case "default":
        case "else":
        case "ensures":
        case "exists":
        case "false":
        case "forall":
        case "function":
        case "ghost":
        case "if":
        case "import":
        case "int":
        case "in":
        case "invariant":
        case "map":
        case "method":
        case "modifies":
        case "module":
        case "multiset":
        case "nat":
        case "new":
        case "null":
        case "object":
        case "opened":
        case "predicate":
        case "reads":
        case "refines":
        case "requires":
        case "return":
        case "returns":
        case "set":
        case "seq":
        case "static":
        case "then":
        case "this":
        case "true":
        case "type":
        case "var":
        case "while":
          return true;
        default:
          return false;
      }
    }

    // Takes a Dafny source snippet or listing and performs basic syntax highlighting.
    // The result is clean, HTML span element markup, suitable for CSSing.
    // Pre: source != null;
    // Post: \result != null;
    static string highlightDafnyToHTML(string source) {
      char[] s = source.ToCharArray();
      string r = "";
      const int Start = 0;
      const int Number = 1;
      const int Ident = 2;
      const int Comment = 3;
      const int CommentStart = 4;
      int state = Start;
      string buffer = "";
      int i = 0;
      while (i < source.Length) {
        char c = s[i];
        switch (state) {
          case Start:
            if (Char.IsDigit(c))
              state = Number;
            else if (c == '/') {
              state = CommentStart;
              buffer = "/";
              i++;
            } else if (char.IsLetter(c) || c == '_')
              state = Ident;
            else {
              switch (c) {
                case '<':
                  r += "&lt;";
                  break;
                case '>':
                  r += "&gt;";
                  break;
                case '"':
                  r += "&quot;";
                  break;
                case '&':
                  r += "&amp;";
                  break;
                case '\t':
                  r += "   ";
                  break;
                default:
                  r += c;
                  break;
              }
              i++;
            }
            break;
          case Number:
            if (char.IsDigit(c)) {
              buffer += c;
              i++;
            } else {
              r = r + "<span class='number'>" + buffer + "</span>";
              buffer = "";
              state = Start;
            }
            break;
          case Ident:
            if (char.IsLetterOrDigit(c) || c == '_') {
              buffer += c;
              i++;
            } else {
              if (IsKeyword(buffer))
                r += "<span class='keyword'>" + buffer + "</span>";
              else
                r += "<span class='ident'>" + buffer + "</span>";
              buffer = "";
              state = Start;
            }
            break;
          case Comment:
            if (c != '\n' && c != '\r') {
              buffer += c;
              i++;
            } else {
              r += "<span class='comment'>" + buffer + "</span>";
              buffer = "";
              state = Start;
            }
            break;
          case CommentStart:
            if (c == '/') {
              buffer += c;
              i++;
              state = Comment;
            } else {
              r += buffer;
              buffer = "";
              state = Start;
            }
            break;
        }

      }
      switch (state) // clean up any unfinished symbols.
      {
        case Start:

          break;
        case Number:
          r = r + "<span class='number'>" + buffer + "</span>";
          break;
        case Ident:
          if (IsKeyword(buffer))
            r += "<span class='keyword'>" + buffer + "</span>";
          else
            r += "<span class='ident'>" + buffer + "</span>";
          break;
        case Comment:
          r += "<span class='comment'>" + buffer + "</span>";
          break;
        case CommentStart:
          r += buffer;
          break;
      }
      return r;
    }

    static void DumpFile(string fname, string contents) {
      StreamWriter streamWriter = new StreamWriter(fname);
      streamWriter.Write(contents);
      streamWriter.Close();
    }
    static string ProcessC(StreamWriter output, string source) {
      //assert: string starts with <c>
      source = source.Substring("<c>".Length);
      int firstClosingTag = source.IndexOf("</c>");
      if (firstClosingTag == -1) {
        System.Console.WriteLine(" ! No matching inline code tag (</c>). Ignoring tag.");
        return source;
      } else {
        output.Write("<span class=\"highlightedCode\">" + highlightDafnyToHTML(source.Substring(0, firstClosingTag)) + "</span>");
        return source.Substring(firstClosingTag + "</c>".Length);
      }
    }
    static string ProcessSnippet(StreamWriter output, string source) {
      //assert: string starts with <c>
      source = source.Substring("<snippet>".Length);
      int firstClosingTag = source.IndexOf("</snippet>");
      if (firstClosingTag == -1) {
        System.Console.WriteLine(" ! No matching snippet code tag (</snippet>). Ignoring tag.");
        return source;
      } else {
        output.Write("<div class =\"highlightedCode\"><pre>" + highlightDafnyToHTML(source.Substring(0, firstClosingTag)) + "</pre></div>");
        return source.Substring(firstClosingTag + "</snippet>".Length);
      }
    }
    static string ProcessListing(StreamWriter output, string source, ref int listingCount, string tutorialName) {
      //assert: string starts with <listing>
      source = source.Substring("<listing>".Length);
      int firstEditorTag = source.IndexOf("<editor/>");
      int firstClosingTag = source.IndexOf("</listing>");

      if (firstClosingTag == -1) {
        System.Console.WriteLine(" ! No matching lising tag (</listing>). Ignoring tag.");
        return source;
      } else {
        string display, editor;
        if (firstEditorTag == -1 || firstEditorTag >= firstClosingTag) {
          // no seperate editor.
          display = source.Substring(0, firstClosingTag);
          editor = display;
        } else {
          // distinct editor/display sections.
          display = source.Substring(0, firstEditorTag);
          editor = source.Substring(firstEditorTag + "<editor/>".Length, firstClosingTag - (firstEditorTag + "<editor/>".Length));
        }
        string fname = tutorialName + "." + listingCount + ".dfy";
        string pref = tutorialName + "." + listingCount;
        listingCount++;
        output.Write("<div class=\"highlightedCode\"><pre pref=\"" + pref + "\">" + highlightDafnyToHTML(display) + "</pre></div>");
        DumpFile(fname, editor.Trim());
        System.Console.WriteLine(" - Wrote to " + fname);
        return source.Substring(firstClosingTag + "</listing>".Length);
      }
    }
    static void ProcessDocument(string tutorialName, string outputFilename, string source) {
      string header = "<html>\n<head>\n<title>" + tutorialName + "</title>\n<link rel=StyleSheet href=\"style.css\" type=\"text/css\">\n</head>\n<body>\n";
      string footer = "\n</body></html>";
      StreamWriter output = new StreamWriter(outputFilename);
      output.Write(header);
      int listingCount = 1;
      while (source != "") {
        int firstAngle = source.IndexOf("<");
        if (firstAngle == -1) {
          output.Write(source);
          source = "";
        } else {
          output.Write(source.Substring(0, firstAngle));
          source = source.Substring(firstAngle);
          if (source.StartsWith("<listing>")) {
            source = ProcessListing(output, source, ref listingCount, tutorialName);
          } else if (source.StartsWith("<c>")) {
            source = ProcessC(output, source);
          } else if (source.StartsWith("<snippet>")) {
            source = ProcessSnippet(output, source);
          } else // some other tag
                    {
            output.Write("<");
            source = source.Substring(1);
          }
        }
      }

      output.Write(footer);
      output.Close();
      System.Console.WriteLine(" - Wrote to " + outputFilename);
    }
    static void Main(string[] args) {
      if (args.Length < 1) {
        System.Console.WriteLine("Not enough args. Usage: DocumentationTransducer input.source");
        return;
      }
      string input = args[0];
      StreamReader streamReader = new StreamReader(input);
      string text = streamReader.ReadToEnd();
      streamReader.Close();
      if (input.EndsWith(".source")) {
        input = input.Substring(0, input.Length - ".source".Length);
      }
      ProcessDocument(input, input + ".htm", text);
    }
  }
}
