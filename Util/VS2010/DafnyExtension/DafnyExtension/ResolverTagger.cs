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
using Dafny = Microsoft.Dafny;

namespace DafnyLanguage
{
  [Export(typeof(ITaggerProvider))]
  [ContentType("dafny")]
  [TagType(typeof(DafnyResolverTag))]
  internal sealed class ResolverTaggerProvider : ITaggerProvider
  {
    [Import(typeof(Microsoft.VisualStudio.Shell.SVsServiceProvider))]
    internal IServiceProvider _serviceProvider = null;

    [Import]
    ITextDocumentFactoryService _textDocumentFactory = null;

    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      // create a single tagger for each buffer.
      Func<ITagger<T>> sc = delegate() { return new ResolverTagger(buffer, _serviceProvider, _textDocumentFactory) as ITagger<T>; };
      return buffer.Properties.GetOrCreateSingletonProperty<ITagger<T>>(sc);
    }
  }

  public abstract class DafnyResolverTag : ITag
  {
  }
  public class DafnyErrorResolverTag : DafnyResolverTag
  {
    public readonly string Typ;
    public readonly string Msg;
    public DafnyErrorResolverTag(string typ, string msg) {
      Typ = typ;
      Msg = msg;
    }
  }
  public class DafnySuccessResolverTag : DafnyResolverTag
  {
    public readonly Dafny.Program Program;
    public DafnySuccessResolverTag(Dafny.Program program) {
      Program = program;
    }
  }

  /// <summary>
  /// Translate PkgDefTokenTags into ErrorTags and Error List items
  /// </summary>
  internal sealed class ResolverTagger : ITagger<DafnyResolverTag>, IDisposable
  {
    ITextBuffer _buffer;
    ITextDocument _document;
    ITextSnapshot _snapshot;  // may be null
    List<DafnyError> _errors = new List<DafnyError>();
    ErrorListProvider _errorProvider;
    public Dafny.Program _program;  // non-null only if the snapshot contains a Dafny program that type checks

    internal ResolverTagger(ITextBuffer buffer, IServiceProvider serviceProvider, ITextDocumentFactoryService textDocumentFactory) {
      _buffer = buffer;
      if (!textDocumentFactory.TryGetTextDocument(_buffer, out _document))
        _document = null;
      _snapshot = null;  // this makes sure the next snapshot will look different
      _errorProvider = new ErrorListProvider(serviceProvider);

      BufferIdleEventUtil.AddBufferIdleEventListener(_buffer, ProcessFile);
    }

    public void Dispose() {
      if (_errorProvider != null) {
        try {
          _errorProvider.Tasks.Clear();
        } catch (InvalidOperationException) {
          // this may occur if the SVsServiceProvider somehow has been uninstalled before our Dispose method is called
        }
        _errorProvider.Dispose();
      }
      BufferIdleEventUtil.RemoveBufferIdleEventListener(_buffer, ProcessFile);
    }

    /// <summary>
    /// Find the Error tokens in the set of all tokens and create an ErrorTag for each
    /// </summary>
    public IEnumerable<ITagSpan<DafnyResolverTag>> GetTags(NormalizedSnapshotSpanCollection spans) {
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
            case ErrorCategory.ParseWarning:
              ty = "warning"; break;
          }
          yield return new TagSpan<DafnyResolverTag>(span, new DafnyErrorResolverTag(ty, err.Message));
        }
      }
      if (_program != null) {
        yield return new TagSpan<DafnyResolverTag>(new SnapshotSpan(snapshot, 0, snapshot.Length), new DafnySuccessResolverTag(_program));
      }
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    /// <summary>
    /// Calls the Dafny verifier on the program, updates the Error List accordingly.
    /// </summary>
    void ProcessFile(object sender, EventArgs args) {
      ITextSnapshot snapshot = _buffer.CurrentSnapshot;
      if (snapshot == _snapshot)
        return;  // we've already done this snapshot
      NormalizedSnapshotSpanCollection spans = new NormalizedSnapshotSpanCollection(new SnapshotSpan(snapshot, 0, snapshot.Length));

      var driver = new DafnyDriver(_buffer.CurrentSnapshot.GetText(), _document != null ? _document.FilePath : "<program>");
      Dafny.Program program = driver.Process();
      var newErrors = driver.Errors;

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
      _program = program;
      var chng = TagsChanged;
      if (chng != null)
        chng(this, new SnapshotSpanEventArgs(new SnapshotSpan(snapshot, 0, snapshot.Length)));
    }

    /// <summary>
    /// Callback method attached to each of our tasks in the Error List
    /// </summary>
    void task_Navigate(object sender, EventArgs e) {
      ErrorTask error = sender as ErrorTask;
      if (error != null) {
        error.Line += 1;
        error.Column += 1;
        // TODO: how to move the cursor to the right column?
        _errorProvider.Navigate(error, new Guid(EnvDTE.Constants.vsViewKindCode));
        error.Column -= 1;
        error.Line -= 1;
      }
    }
  }

  public enum ErrorCategory
  {
    ProcessError, ParseWarning, ParseError, ResolveError, VerificationError
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
