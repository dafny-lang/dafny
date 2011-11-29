using System;
using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.VisualStudio;
using Microsoft.VisualStudio.TextManager.Interop;
using Microsoft.VisualStudio.Package;

using Irony.Parsing;
using Irony.Ast;

using System.IO;

namespace Demo
{
    public class IronyLanguageService : Microsoft.VisualStudio.Package.LanguageService
    {
        private Grammar grammar;
        private Parser parser;
        private ParsingContext context;

        public IronyLanguageService()
        {
            grammar = new Grammar();
            parser = new Parser(Configuration.Grammar);
            context = new ParsingContext(parser);
        }


        #region Custom Colors
        public override int GetColorableItem(int index, out IVsColorableItem item)
        {
            if (index <= Configuration.ColorableItems.Count)
            {
                item = Configuration.ColorableItems[index - 1];
                return Microsoft.VisualStudio.VSConstants.S_OK;
            }
            else
            {
                throw new ArgumentNullException("index");
            }
        }

        public override int GetItemCount(out int count)
        {
            count = Configuration.ColorableItems.Count;
            return Microsoft.VisualStudio.VSConstants.S_OK;
        }
        #endregion

        #region MPF Accessor and Factory specialisation
        private LanguagePreferences preferences;
        public override LanguagePreferences GetLanguagePreferences()
        {
            if (this.preferences == null)
            {
                this.preferences = new LanguagePreferences(this.Site,
                                                        typeof(IronyLanguageService).GUID,
                                                        this.Name);
                this.preferences.Init();
            }

            return this.preferences;
        }

        public override Microsoft.VisualStudio.Package.Source CreateSource(IVsTextLines buffer)
        {
            return new Source(this, buffer, this.GetColorizer(buffer));
        }

        private IScanner scanner;
        public override IScanner GetScanner(IVsTextLines buffer)
        {
            if (scanner == null)
                this.scanner = new LineScanner(grammar);

            return this.scanner;
        }
        #endregion

        public override void OnIdle(bool periodic)
        {
            // from IronPythonLanguage sample
            // this appears to be necessary to get a parse request with ParseReason = Check?
            Source src = (Source)GetSource(this.LastActiveTextView);
            if (src != null && src.LastParseTime >= Int32.MaxValue >> 12)
            {
                src.LastParseTime = 0;
            }
            base.OnIdle(periodic);
        }

        public override Microsoft.VisualStudio.Package.AuthoringScope ParseSource(ParseRequest req)
        {
            Debug.Print("ParseSource at ({0}:{1}), reason {2}", req.Line, req.Col, req.Reason);
            Source source = (Source)this.GetSource(req.FileName);
            switch (req.Reason)
            {
                case ParseReason.Check:
                    // This is where you perform your syntax highlighting.
                    // Parse entire source as given in req.Text.
                    // Store results in the AuthoringScope object.
                var parsed = parser.Parse(req.Text, req.FileName);
                var root = parsed.Root;
                if (root != null) {

                  AstNode node = (AstNode)root.AstNode;
                  source.ParseResult = node;
                }

                    // Used for brace matching.
                    TokenStack braces = parser.Context.OpenBraces;
                    foreach (Token brace in braces) {
                      if (brace.OtherBrace == null) continue;
                      TextSpan openBrace = new TextSpan();
                      openBrace.iStartLine = brace.Location.Line;
                      openBrace.iStartIndex = brace.Location.Column;
                      openBrace.iEndLine = brace.Location.Line;
                      openBrace.iEndIndex = openBrace.iStartIndex + brace.Length;

                      TextSpan closeBrace = new TextSpan();
                      closeBrace.iStartLine = brace.OtherBrace.Location.Line;
                      closeBrace.iStartIndex = brace.OtherBrace.Location.Column;
                      closeBrace.iEndLine = brace.OtherBrace.Location.Line;
                      closeBrace.iEndIndex = closeBrace.iStartIndex + brace.OtherBrace.Length;

                      if (source.Braces == null) {
                        source.Braces = new List<TextSpan[]>();
                      }
                      source.Braces.Add(new TextSpan[2] { openBrace, closeBrace });
                    }

                    if (parser.Context.CurrentParseTree.ParserMessages.Count > 0) {
                      foreach (ParserMessage error in parser.Context.CurrentParseTree.ParserMessages) {
                        TextSpan span = new TextSpan();
                        span.iStartLine = span.iEndLine = error.Location.Line - 1;
                        span.iStartIndex = error.Location.Column;
                        span.iEndIndex = error.Location.Position;
                        req.Sink.AddError(req.FileName, error.Message, span, Severity.Error);
                      }
                    } else { // parse looks okay, send it to Dafny.
                      if (!File.Exists(@"C:\tmp\StartDafny.bat")) {
                        AddErrorBecauseOfToolProblems(req, @"Can't find C:\tmp\StartDafny.bat");
                      } else {

                        // From: http://dotnetperls.com/process-redirect-standard-output
                        // (Also, see: http://msdn.microsoft.com/en-us/library/system.diagnostics.processstartinfo.redirectstandardoutput.aspx)
                        //
                        // Setup the process with the ProcessStartInfo class.
                        //
                        ProcessStartInfo start = new ProcessStartInfo();
                        start.FileName = @"cmd.exe";
                        start.Arguments = @"/c C:\tmp\StartDafny.bat"; // Specify exe name.
                        start.UseShellExecute = false;
                        start.RedirectStandardInput = true;
                        start.RedirectStandardOutput = true;
                        start.CreateNoWindow = true;
                        //start.WindowStyle = ProcessWindowStyle.Minimized; // need this or else you see the window pop up
                        //
                        // Start the process.
                        //
                        using (Process process = Process.Start(start)) {
                          //
                          // Push the file contents to the new process
                          //
                          StreamWriter myStreamWriter = process.StandardInput;
                          myStreamWriter.WriteLine(req.Text);
                          myStreamWriter.Close();
                          //
                          // Read in all the text from the process with the StreamReader.
                          //
                          using (StreamReader reader = process.StandardOutput) {
                            //string result = reader.ReadToEnd();
                            //Console.Write(result);

                            for (string line = reader.ReadLine(); line != null; line = reader.ReadLine()) {
                              // the lines of interest have the form "filename(line,col): some_error_label: error_message"
                              // where "some_error_label" is "Error" or "syntax error" or "Error BP5003" or "Related location"
                                if (line.Equals("")) continue;
                                if (line.StartsWith("Dafny program verifier finished with"))
                                {
                                    if (line.Contains("time out"))
                                    {
                                        AddErrorBecauseOfToolProblems(req, "Verification timed out.");
                                    }
                                    else
                                    {
                                        if (!line.Contains("inconclusive") && !line.Contains("out of memory"))
                                        {
                                            if (line.Contains(" 0 errors"))
                                                AddMessage(req, "Verification successful.");
                                        }
                                        else
                                        {
                                            AddErrorBecauseOfToolProblems(req, "Internal verification fault.");
                                        }
                                    }
                                    break;
                                }
                              string message;
                              int n = line.IndexOf("): ", 2);  // we start at 2, to avoid problems with "C:\..."
                              if (n == -1) {
                                continue;
                              } else {
                                int m = line.IndexOf(": ", n + 3);
                                if (m == -1) {
                                  continue;
                                }
                                message = line.Substring(m + 2);
                              }
                              line = line.Substring(0, n);  // line now has the form "filename(line,col"

                              n = line.LastIndexOf(',');
                              if (n == -1) { continue; }
                              var colString = line.Substring(n + 1);
                              line = line.Substring(0, n);  // line now has the form "filename(line"
                              
                              n = line.LastIndexOf('(');
                              if (n == -1) { continue; }
                              var lineString = line.Substring(n + 1);

                              try {
                                TextSpan span = new TextSpan();
                                span.iStartLine = span.iEndLine = Int32.Parse(lineString) - 1;
                                span.iStartIndex = Int32.Parse(colString) - 1;
                                span.iEndIndex = span.iStartIndex + 5;  // hack
                                req.Sink.AddError(req.FileName, message, span, Severity.Error);
                              } catch (System.FormatException) {
                                continue;
                              } catch (System.OverflowException) {
                                continue;
                              }
                            }
                          }
                        }
                      }
                    }

                    break;

                case ParseReason.DisplayMemberList:
                    // Parse the line specified in req.Line for the two
                    // tokens just before req.Col to obtain the identifier
                    // and the member connector symbol.
                    // Examine existing parse tree for members of the identifer
                    // and return a list of members in your version of the
                    // Declarations class as stored in the AuthoringScope
                    // object.
                    break;

                case ParseReason.MethodTip:
                    // Parse the line specified in req.Line for the token
                    // just before req.Col to obtain the name of the method
                    // being entered.
                    // Examine the existing parse tree for all method signatures
                    // with the same name and return a list of those signatures
                    // in your version of the Methods class as stored in the
                    // AuthoringScope object.
                    break;

                case ParseReason.HighlightBraces:
                case ParseReason.MemberSelectAndHighlightBraces:
                    if (source.Braces != null)
                    {
                        foreach (TextSpan[] brace in source.Braces)
                        {
                            if (brace.Length == 2)
                                req.Sink.MatchPair(brace[0], brace[1], 1);
                            else if (brace.Length >= 3)
                                req.Sink.MatchTriple(brace[0], brace[1], brace[2], 1);
                        }
                    }
                    break;
            }

            return new AuthoringScope(source.ParseResult);
        }

        private static void AddErrorBecauseOfToolProblems(ParseRequest req, string msg)
        {
            TextSpan span = new TextSpan();
            span.iStartLine = span.iEndLine = 0;
            span.iStartIndex = 0;
            span.iEndIndex = 0;
            req.Sink.AddError(req.FileName, msg, span, Severity.Error);
        }
        private static void AddMessage(ParseRequest req, string msg)
        {
            TextSpan span = new TextSpan();
            span.iStartLine = span.iEndLine = 0;
            span.iStartIndex = 0;
            span.iEndIndex = 1;
            req.Sink.AddError(req.FileName, msg, span, Severity.Hint);
        }

        /// <summary>
        /// Called to determine if the given location can have a breakpoint applied to it. 
        /// </summary>
        /// <param name="buffer">The IVsTextBuffer object containing the source file.</param>
        /// <param name="line">The line number where the breakpoint is to be set.</param>
        /// <param name="col">The offset into the line where the breakpoint is to be set.</param>
        /// <param name="pCodeSpan">
        /// Returns the TextSpan giving the extent of the code affected by the breakpoint if the 
        /// breakpoint can be set.
        /// </param>
        /// <returns>
        /// If successful, returns S_OK; otherwise returns S_FALSE if there is no code at the given 
        /// position or returns an error code (the validation is deferred until the debug engine is loaded). 
        /// </returns>
        /// <remarks>
        /// <para>
        /// CAUTION: Even if you do not intend to support the ValidateBreakpointLocation but your language 
        /// does support breakpoints, you must override the ValidateBreakpointLocation method and return a 
        /// span that contains the specified line and column; otherwise, breakpoints cannot be set anywhere 
        /// except line 1. You can return E_NOTIMPL to indicate that you do not otherwise support this 
        /// method but the span must always be set. The example shows how this can be done.
        /// </para>
        /// <para>
        /// Since the language service parses the code, it generally knows what is considered code and what 
        /// is not. Normally, the debug engine is loaded and the pending breakpoints are bound to the source. It is at this time the breakpoint location is validated. This method is a fast way to determine if a breakpoint can be set at a particular location without loading the debug engine.
        /// </para>
        /// <para>
        /// You can implement this method to call the ParseSource method with the parse reason of CodeSpan. 
        /// The parser examines the specified location and returns a span identifying the code at that 
        /// location. If there is code at the location, the span identifying that code should be passed to 
        /// your implementation of the CodeSpan method in your version of the AuthoringSink class. Then your 
        /// implementation of the ValidateBreakpointLocation method retrieves that span from your version of 
        /// the AuthoringSink class and returns that span in the pCodeSpan argument.
        /// </para>
        /// <para>
        /// The base method returns E_NOTIMPL.
        /// </para>
        /// </remarks>
        public override int ValidateBreakpointLocation(IVsTextBuffer buffer, int line, int col, TextSpan[] pCodeSpan)
        {
            // TODO: Add code to not allow breakpoints to be placed on non-code lines.
            // TODO: Refactor to allow breakpoint locations to span multiple lines.
            if (pCodeSpan != null)
            {
                pCodeSpan[0].iStartLine = line;
                pCodeSpan[0].iStartIndex = col;
                pCodeSpan[0].iEndLine = line;
                pCodeSpan[0].iEndIndex = col;
                if (buffer != null)
                {
                    int length;
                    buffer.GetLengthOfLine(line, out length);
                    pCodeSpan[0].iStartIndex = 0;
                    pCodeSpan[0].iEndIndex = length;
                }
                return VSConstants.S_OK;
            }
            else
            {
                return VSConstants.S_FALSE;
            }
        }

        public override ViewFilter CreateViewFilter(CodeWindowManager mgr, IVsTextView newView)
        {
            return new IronyViewFilter(mgr, newView);
        }

        public override string Name
        {
            get { return Configuration.Name; }
        }

        public override string GetFormatFilterList()
        {
            return Configuration.FormatList;
        }
    }
}
