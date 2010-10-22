//***************************************************************************
// Copyright © 2010 Microsoft Corporation.  All Rights Reserved.
// This code released under the terms of the 
// Microsoft Public License (MS-PL, http://opensource.org/licenses/ms-pl.html.)
//***************************************************************************
using EnvDTE;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.ComponentModel.Composition;
using System.Windows.Threading;
using Microsoft.VisualStudio.Shell;
using Microsoft.VisualStudio.Shell.Interop;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Classification;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Text.Projection;
using Microsoft.VisualStudio.Utilities;
using System.Diagnostics;
using System.IO;

namespace DafnyLanguage
{
  [Export(typeof(ITaggerProvider))]
  [ContentType("dafny")]
  [TagType(typeof(ErrorTag))]
  internal sealed class ErrorTaggerProvider : ITaggerProvider
  {
    [Import(typeof(Microsoft.VisualStudio.Shell.SVsServiceProvider))]
    internal IServiceProvider _serviceProvider = null;

    [Import]
    ITextDocumentFactoryService _textDocumentFactory = null;

    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      // create a single tagger for each buffer.
      Func<ITagger<T>> sc = delegate() { return new ErrorTagger(buffer, _serviceProvider, _textDocumentFactory) as ITagger<T>; };
      return buffer.Properties.GetOrCreateSingletonProperty<ITagger<T>>(sc);
    }
  }

  /// <summary>
  /// Translate PkgDefTokenTags into ErrorTags and Error List items
  /// </summary>
  internal sealed class ErrorTagger : ITagger<ErrorTag>, IDisposable
  {
    ITextBuffer _buffer;
    ITextDocument _document;
    ITextSnapshot _snapshot;  // may be null
    List<DafnyError> _errors = new List<DafnyError>();
    ErrorListProvider _errorProvider;

    internal ErrorTagger(ITextBuffer buffer, IServiceProvider serviceProvider, ITextDocumentFactoryService textDocumentFactory) {
      _buffer = buffer;
      if (!textDocumentFactory.TryGetTextDocument(_buffer, out _document))
        _document = null;
      _snapshot = null;  // this makes sure the next snapshot will look different
      _errorProvider = new ErrorListProvider(serviceProvider);

      // ProcessFile(null, EventArgs.Empty);
      BufferIdleEventUtil.AddBufferIdleEventListener(_buffer, ProcessFile);
    }

    public void Dispose() {
      if (_errorProvider != null) {
        _errorProvider.Tasks.Clear();
        _errorProvider.Dispose();
      }
      BufferIdleEventUtil.RemoveBufferIdleEventListener(_buffer, ProcessFile);
    }

    /// <summary>
    /// Find the Error tokens in the set of all tokens and create an ErrorTag for each
    /// </summary>
    public IEnumerable<ITagSpan<ErrorTag>> GetTags(NormalizedSnapshotSpanCollection spans) {
      if (spans.Count == 0) yield break;
      var snapshot = spans[0].Snapshot;

      foreach (var err in _errors) {
        if (err.Category != ErrorCategory.ProcessError) {
          var line = snapshot.GetLineFromLineNumber(err.Line);
          var length = line.Length - err.Column;
          if (5 < length) length = 5;
          SnapshotSpan span = new SnapshotSpan(new SnapshotPoint(snapshot, line.Start.Position + err.Column), length);
          // http://msdn.microsoft.com/en-us/library/dd885244.aspx says one can use the error types below, but they
          // all show as purple squiggles for me.  And just "error" (which is not mentioned on that page) shows up
          // as red.
          string ty;
          switch (err.Category) {
            default:  // unexpected category
            case ErrorCategory.ParseError:
              // ty = "syntax error";
              ty = "error"; break;
            case ErrorCategory.ResolveError:
              ty = "compiler error"; break;
            case ErrorCategory.VerificationError:
              ty = "other error"; break;
          }
          yield return new TagSpan<ErrorTag>(span, new ErrorTag(ty, err.Message));
        }
      }
    }

    // the Classifier tagger is translating buffer change events into TagsChanged events, so we don't have to
    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    /// <summary>
    /// Calls the Dafny verifier on the program, updates the Error List accordingly.
    /// </summary>
    void ProcessFile(object sender, EventArgs args) {
      ITextSnapshot snapshot = _buffer.CurrentSnapshot;
      if (snapshot == _snapshot)
        return;  // we've already done this snapshot
      NormalizedSnapshotSpanCollection spans = new NormalizedSnapshotSpanCollection(new SnapshotSpan(snapshot, 0, snapshot.Length));

      var newErrors = Verify(_buffer.CurrentSnapshot.GetText());

      _errorProvider.Tasks.Clear();
      foreach (var err in newErrors) {
        ErrorTask task = new ErrorTask();
        task.CanDelete = true;
        task.Category = TaskCategory.BuildCompile;
        if (_document != null)
          task.Document = _document.FilePath;
        task.ErrorCategory = TaskErrorCategory.Error;
        task.Text = err.Message;
        if (err.Category != ErrorCategory.ProcessError) {
          task.Line = err.Line;
          task.Column = err.Column;
          task.Navigate += new EventHandler(task_Navigate);
        }
        _errorProvider.Tasks.Add(task);
      }

      _errors = newErrors;
      _snapshot = snapshot;
      var chng = TagsChanged;
      if (chng != null)
        chng(this, new SnapshotSpanEventArgs(new SnapshotSpan(snapshot, 0, snapshot.Length)));
    }

    private static List<DafnyError> Verify(string theProgram) {
      List<DafnyError> errors = new List<DafnyError>();

      if (!File.Exists(@"C:\tmp\StartDafny.bat")) {
        RecordError(errors, 0, 0, ErrorCategory.ProcessError, @"Can't find C:\tmp\StartDafny.bat");
        return errors;
      }

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
      //
      // Start the process.
      //
      using (System.Diagnostics.Process process = System.Diagnostics.Process.Start(start)) {
        //
        // Push the file contents to the new process
        //
        StreamWriter myStreamWriter = process.StandardInput;
        myStreamWriter.WriteLine(theProgram);
        myStreamWriter.Close();
        //
        // Read in all the text from the process with the StreamReader.
        //
        using (StreamReader reader = process.StandardOutput) {
          for (string line = reader.ReadLine(); !String.IsNullOrEmpty(line); line = reader.ReadLine()) {
            // the lines of interest have the form "filename(line,col): some_error_label: error_message"
            // where "some_error_label" is "Error" or "syntax error" or "Error BP5003" or "Related location"
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
              int errLine = Int32.Parse(lineString) - 1;
              int errCol = Int32.Parse(colString) - 1;
              RecordError(errors, errLine, errCol, message.StartsWith("syntax error") ? ErrorCategory.ParseError : ErrorCategory.VerificationError, message);
            } catch (System.FormatException) {
              continue;
            } catch (System.OverflowException) {
              continue;
            }
          }
        }
      }
      return errors;
    }

    private static void RecordError(List<DafnyError> errors, int line, int col, ErrorCategory cat, string msg) {
      errors.Add(new DafnyError(line, col, cat, msg));
    }

    /// <summary>
    /// Callback method attached to each of our tasks in the Error List
    /// </summary>
    void task_Navigate(object sender, EventArgs e) {
      ErrorTask error = sender as ErrorTask;
      if (error != null) {
        error.Line += 1;
        error.Column += 1;
        _errorProvider.Navigate(error, new Guid(EnvDTE.Constants.vsViewKindCode));
        error.Column -= 1;
        error.Line -= 1;
      }
    }
  }

  public enum ErrorCategory
  {
    ProcessError, ParseError, ResolveError, VerificationError
  }

  internal class DafnyError
  {
    public readonly int Line;  // 0 based
    public readonly int Column;  // 0 based
    public readonly ErrorCategory Category;
    public readonly string Message;
    public DafnyError(int line, int col, ErrorCategory cat, string msg) {
      Line = line;
      Column = col;
      Category = cat;
      Message = msg;
    }
  }
}
