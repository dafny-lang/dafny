using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Windows.Shapes;
using Microsoft.VisualStudio;
using Microsoft.VisualStudio.Shell;
using Microsoft.VisualStudio.Shell.Interop;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.TextManager.Interop;
using Microsoft.VisualStudio.Utilities;
using Dafny = Microsoft.Dafny;


namespace DafnyLanguage
{

  #region Provider

  [Export(typeof(ITaggerProvider))]
  [ContentType("dafny")]
  [TagType(typeof(IDafnyResolverTag))]
  internal sealed class ResolverTaggerProvider : ITaggerProvider
  {
    [Import(typeof(Microsoft.VisualStudio.Shell.SVsServiceProvider))]
    internal IServiceProvider _serviceProvider = null;

    [Import]
    ITextDocumentFactoryService _textDocumentFactory = null;

    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag
    {
      // create a single tagger for each buffer.
      Func<ITagger<T>> sc = delegate() { return new ResolverTagger(buffer, _serviceProvider, _textDocumentFactory) as ITagger<T>; };
      return buffer.Properties.GetOrCreateSingletonProperty<ITagger<T>>(sc);
    }
  }

  #endregion


  #region Tagger

  #region Tags

  public interface IDafnyResolverTag : ITag
  {
  }

  public class DafnyErrorResolverTag : ErrorTag, IDafnyResolverTag
  {
    public DafnyError Error { get; private set; }

    public DafnyErrorResolverTag(DafnyError error)
      : base(ConvertToErrorType(error), error.Message)
    {
      Error = error;
    }

    private static string ConvertToErrorType(DafnyError err) {
      // the COLORs below indicate what I see on my machine
      switch (err.Category) {
        case ErrorCategory.ProcessError:
        case ErrorCategory.ParseError:
          return "syntax error";  // COLOR: red
        case ErrorCategory.ResolveError:
          return "compiler error";  // COLOR: blue
        case ErrorCategory.ParseWarning:
        case ErrorCategory.ResolveWarning:
          return "compiler warning";  // COLOR: blue
        case ErrorCategory.InternalError:
        case ErrorCategory.VerificationError:
          return "error";  // COLOR: red
        case ErrorCategory.AuxInformation:
          return "other error";  // COLOR: purple red
        default:
          Contract.Assert(false);
          throw new InvalidOperationException();
      }
    }
  }

  public class DafnyErrorStateResolverTag : IDafnyResolverTag
  {
    public readonly DafnyError Error;
    public readonly ITrackingSpan Span;
    public readonly int Id;
    public readonly string Description;
    public DafnyErrorStateResolverTag(DafnyError error, ITrackingSpan span, int id, string description)
    {
      Error = error;
      Span = span;
      Id = id;
      Description = description;
    }
  }

  public class DafnySuccessResolverTag : IDafnyResolverTag
  {
    public readonly Dafny.Program Program;
    public DafnySuccessResolverTag(Dafny.Program program)
    {
      Program = program;
    }
  }

  #endregion


  /// <summary>
  /// Translate PkgDefTokenTags into ErrorTags and Error List items
  /// </summary>
  public sealed class ResolverTagger : ITagger<IDafnyResolverTag>, IDisposable
  {
    readonly ITextBuffer _buffer;
    readonly ITextDocument _document;
    ErrorListProvider _errorProvider;
    private bool m_disposed;

    // The 'Snapshot' and 'Program' fields should be updated and read together, so they are protected by "this"
    public ITextSnapshot Snapshot;  // may be null
    public Dafny.Program Program;  // non-null only if the snapshot contains a Dafny program that type checks
    public bool RunResolver { get; set; }  // whether the resolver should be run

    List<DafnyError> _resolutionErrors = new List<DafnyError>();  // if nonempty, then _snapshot is the snapshot from which the errors were produced

    internal void AddError(DafnyError error, string unitId, string requestId)
    {
      ErrorContainer entry;
      if (_verificationErrors.TryGetValue(unitId, out entry))
      {
        lock (entry)
        {
          if (entry.RequestId == null || new DateTime(long.Parse(entry.RequestId)) < new DateTime(long.Parse(requestId)))
          {
            entry.Errors.Clear();
            entry.RequestId = requestId;
          }
        }
        entry.Errors.Push(error);
        UpdateErrorList(Snapshot);
      }
    }

    string MostRecentRequestId;
    
    internal void ReInitializeVerificationErrors(string mostRecentRequestId, IEnumerable<Microsoft.Boogie.Implementation> implementations)
    {
      var implNames = implementations.Select(impl => impl.Name);
      lock (this)
      {
        MostRecentRequestId = mostRecentRequestId;
        var outOfDatekeys = _verificationErrors.Keys.Except(implNames);
        foreach (var key in outOfDatekeys)
        {
          ErrorContainer oldError;
          _verificationErrors.TryRemove(key, out oldError);
        }

        var newKeys = implNames.Except(_verificationErrors.Keys).ToList();
        newKeys.Add("$$program$$");
        foreach (var key in newKeys)
        {
          _verificationErrors.TryAdd(key, new ErrorContainer());
        }
      }
    }

    public class ErrorContainer
    {
      internal string RequestId;
      internal ConcurrentStack<DafnyError> Errors = new ConcurrentStack<DafnyError>();
    }

    public readonly ConcurrentDictionary<string, ErrorContainer> _verificationErrors = new ConcurrentDictionary<string, ErrorContainer>();

    public IEnumerable<DafnyError> VerificationErrors
    {
      get
      {
        return _verificationErrors.Values.Where(ec => ec.RequestId == MostRecentRequestId).SelectMany(ec => ec.Errors.Reverse()).ToList();
      }
    }

    public IEnumerable<DafnyError> AllErrors
    {
      get
      {
        lock (this)
        {
          bool anyResolutionErrors = false;
          if (_resolutionErrors != null) {
            foreach (var err in _resolutionErrors) {
              if (CategoryConversion(err.Category) == TaskErrorCategory.Error) {
                anyResolutionErrors = true;
              }
              yield return err;
            }
          }
          if (!anyResolutionErrors) {
            foreach (var err in VerificationErrors) {
              yield return err;
            }
          }
        }
      }
    }

    public static readonly IDictionary<ITextBuffer, ResolverTagger> ResolverTaggers = new ConcurrentDictionary<ITextBuffer, ResolverTagger>();

    internal ResolverTagger(ITextBuffer buffer, IServiceProvider serviceProvider, ITextDocumentFactoryService textDocumentFactory)
    {
      _buffer = buffer;
      if (!textDocumentFactory.TryGetTextDocument(_buffer, out _document))
        _document = null;
      Snapshot = null;  // this makes sure the next snapshot will look different
      _errorProvider = new ErrorListProvider(serviceProvider);

      BufferIdleEventUtil.AddBufferIdleEventListener(_buffer, ResolveBuffer);
      this.RunResolver = true;
    }

    public void Dispose()
    {
      Dispose(true);
      GC.SuppressFinalize(this);
    }

    private void Dispose(bool disposing)
    {
      lock (this)
      {
        if (!m_disposed)
        {
          if (disposing)
          {
            if (_errorProvider != null)
            {
              try
              {
                _errorProvider.Tasks.Clear();
              }
              catch (InvalidOperationException)
              {
                // this may occur if the SVsServiceProvider somehow has been uninstalled before our Dispose method is called
              }
              _errorProvider.Dispose();
              _errorProvider = null;
            }
            BufferIdleEventUtil.RemoveBufferIdleEventListener(_buffer, ResolveBuffer);
            if (_document != null && _document.TextBuffer != null)
            {
              ResolverTaggers.Remove(_document.TextBuffer);
            }
          }

          m_disposed = true;
        }
      }
    }

    /// <summary>
    /// Find the Error tokens in the set of all tokens and create an ErrorTag for each
    /// </summary>
    public IEnumerable<ITagSpan<IDafnyResolverTag>> GetTags(NormalizedSnapshotSpanCollection spans)
    {
      if (spans.Count == 0) yield break;
      var currentSnapshot = spans[0].Snapshot;
      foreach (var err in AllErrors)
      {
        if (err.Category != ErrorCategory.ProcessError && err.Filename == System.IO.Path.GetFullPath(_document.FilePath))
        {
          yield return new TagSpan<IDafnyResolverTag>(err.Span.GetSpan(currentSnapshot), new DafnyErrorResolverTag(err));

          if (err.StateSpans != null)
          {
            for (int i = 0; i < err.StateSpans.Length; i++)
            {
              var span = err.StateSpans[i];
              var name = err.Model.States.ToArray()[i].Name;
              var descStart = name.LastIndexOf(": ") + 2;
              var description = 1 < descStart ? name.Substring(descStart) : "";
              if (span != null)
              {
                yield return new TagSpan<IDafnyResolverTag>(span.GetSpan(currentSnapshot), new DafnyErrorStateResolverTag(err, span, i, description));
              }
            }
          }
        }
      }

      ITextSnapshot snap;
      Dafny.Program prog;
      lock (this)
      {
        snap = Snapshot;
        prog = Program;
      }
      if (prog != null)
      {
        yield return new TagSpan<IDafnyResolverTag>(new SnapshotSpan(snap, 0, snap.Length), new DafnySuccessResolverTag(prog));
      }
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    /// <summary>
    /// Calls the Dafny parser/resolver/type checker on the contents of the buffer, updates the Error List accordingly.
    /// </summary>
    public void ResolveBuffer(object sender, EventArgs args) {
      ITextSnapshot snapshot = _buffer.CurrentSnapshot;
      if (snapshot == Snapshot)
        return;  // we've already done this snapshot

      string filename = _document != null ? _document.FilePath : "<program>";
      var driver = new DafnyDriver(_buffer, filename);
      List<DafnyError> newErrors;
      Dafny.Program program;
      try
      {
        program = driver.ProcessResolution(RunResolver);
        newErrors = driver.Errors;
      }
      catch (Exception e)
      {
        newErrors = new List<DafnyError> { new DafnyError(filename, 0, 0, ErrorCategory.InternalError, "internal Dafny error: " + e.Message, snapshot, false) };
        program = null;
      }

      lock (this)
      {
        Snapshot = snapshot;
        Program = program;
      }

      if (program != null && _document != null)
      {
        ResolverTaggers[_document.TextBuffer] = this;
      }
      else if (_document != null)
      {
        ResolverTaggers.Remove(_document.TextBuffer);
      }

      _resolutionErrors = newErrors;

      UpdateErrorList(snapshot);
    }

    public void UpdateErrorList(ITextSnapshot snapshot)
    {
      if (_errorProvider != null && !m_disposed)
      {
        _errorProvider.SuspendRefresh();  // reduce flickering
        _errorProvider.Tasks.Clear();
        foreach (var err in AllErrors)
        { 
          var lineNum = 0;
          var columnNum = 0;
          if (err.Span != null) {
            var span = err.Span.GetSpan(snapshot);
            lineNum = snapshot.GetLineNumberFromPosition(span.Start.Position);
            var line = snapshot.GetLineFromPosition(span.Start.Position);
            columnNum = span.Start - line.Start;
          } else {
            lineNum = err.Line;
            columnNum = err.Column;
          }
          
          ErrorTask task = new ErrorTask()
          {
            Category = TaskCategory.BuildCompile,
            ErrorCategory = CategoryConversion(err.Category),
            Text = err.Message,
            Line = lineNum,
            Column = columnNum
          };
          if (err.Filename != null) {
            task.Document = err.Filename;
          } 
          else if (_document != null)
          {
            task.Document = _document.FilePath;
          }
          if (err.Category != ErrorCategory.ProcessError && err.Category != ErrorCategory.InternalError)
          {
            task.Navigate += new EventHandler(NavigateHandler);
          }
          _errorProvider.Tasks.Add(task);
        }
        _errorProvider.ResumeRefresh();
      }
      var chng = TagsChanged;
      if (chng != null)
        chng(this, new SnapshotSpanEventArgs(new SnapshotSpan(snapshot, 0, snapshot.Length)));
    }

    static TaskErrorCategory CategoryConversion(ErrorCategory cat)
    {
      switch (cat)
      {
        case ErrorCategory.ParseError:
        case ErrorCategory.ResolveError:
        case ErrorCategory.VerificationError:
        case ErrorCategory.InternalError:
          return TaskErrorCategory.Error;
        case ErrorCategory.ParseWarning:
        case ErrorCategory.ResolveWarning:
          return TaskErrorCategory.Warning;
        case ErrorCategory.AuxInformation:
          return TaskErrorCategory.Message;
        default:
          Contract.Assert(false);  // unexpected category
          return TaskErrorCategory.Error;  // please compiler
      }
    }

    void NavigateHandler(object sender, EventArgs arguments)
    {
      var task = sender as ErrorTask;
      if (task == null || task.Document == null)
        return;

      // This would have been the simple way of doing things:
      //     _errorProvider.Navigate(error, new Guid(EnvDTE.Constants.vsViewKindCode));
      // Unfortunately, it doesn't work--it seems to ignore the column position.  (Moreover, it wants 1-based
      // line/column numbers, whereas the Error Task pane wants 0-based line/column numbers.)
      // So, instead we do all the things that follow:

      var openDoc = Package.GetGlobalService(typeof(IVsUIShellOpenDocument)) as IVsUIShellOpenDocument;
      if (openDoc == null)
        return;

      IVsWindowFrame frame;
      Microsoft.VisualStudio.OLE.Interop.IServiceProvider sp;
      IVsUIHierarchy hier;
      uint itemid;
      Guid logicalView = VSConstants.LOGVIEWID_Code;
      if (Microsoft.VisualStudio.ErrorHandler.Failed(openDoc.OpenDocumentViaProject(task.Document, ref logicalView, out sp, out hier, out itemid, out frame)) || frame == null)
        return;

      object docData;
      Microsoft.VisualStudio.ErrorHandler.ThrowOnFailure(frame.GetProperty((int)__VSFPROPID.VSFPROPID_DocData, out docData));

      // Get the VsTextBuffer
      VsTextBuffer buffer = docData as VsTextBuffer;
      if (buffer == null)
      {
        IVsTextBufferProvider bufferProvider = docData as IVsTextBufferProvider;
        if (bufferProvider != null)
        {
          IVsTextLines lines;
          Microsoft.VisualStudio.ErrorHandler.ThrowOnFailure(bufferProvider.GetTextBuffer(out lines));
          buffer = lines as VsTextBuffer;
          if (buffer == null)
            return;
        }
      }

      VsTextManager textManager = Package.GetGlobalService(typeof(VsTextManagerClass)) as VsTextManager;
      if (textManager == null)
        return;

      // Finally, move the cursor
      Microsoft.VisualStudio.ErrorHandler.ThrowOnFailure(textManager.NavigateToLineAndColumn(buffer, ref logicalView, task.Line, task.Column, task.Line, task.Column));
    }
  }


  #region Errors

  public enum ErrorCategory
  {
    ProcessError, ParseWarning, ParseError, ResolveWarning, ResolveError, VerificationError, AuxInformation, InternalError
  }

  public class DafnyError
  {
    public readonly string Filename;
    public readonly int Line;  // 0 based
    public readonly int Column;  // 0 based
    public readonly ErrorCategory Category;
    public readonly string Message;
    protected readonly ITextSnapshot Snapshot;
    public readonly ITrackingSpan Span;
    public readonly string ModelText;
    public Microsoft.Boogie.Model _model;
    public Microsoft.Boogie.Model Model
    {
      get
      {
        if (_model == null && !string.IsNullOrEmpty(ModelText))
        {
          using (var rd = new StringReader(ModelText))
          {
            var models = Microsoft.Boogie.Model.ParseModels(rd).ToArray();
            Contract.Assert(models.Length == 1);
            _model = models[0];
          }
        }
        return _model;
      }
    }
    private ITrackingSpan[] _stateSpans;
    public ITrackingSpan[] StateSpans
    {
      get
      {
        if (_stateSpans == null && Model != null)
        {          
          var model = Model;
          var locRegex = new Regex(@"\((\d+),(\d+)\)");
          _stateSpans = model.States.Select(
           cs =>
           {
             var match = locRegex.Match(cs.Name);
             if (!match.Success)
             {
               return null;
             }
             else
             {
               var line = Math.Max(0, int.Parse(match.Groups[1].Value) - 1);
               var column = Math.Max(0, int.Parse(match.Groups[2].Value));
               var sLine = Snapshot.GetLineFromLineNumber(line);
               Contract.Assert(column <= sLine.Length);
               var sLength = Math.Max(0, Math.Min(sLine.Length - column, 0));
               return Snapshot.CreateTrackingSpan(sLine.Start + column, sLength, SpanTrackingMode.EdgeExclusive, TrackingFidelityMode.Forward);
             }
           }).ToArray();
        }
        return _stateSpans;
      }
    }
    public int SelectedStateId { get; set; }
    public Shape SelectedStateAdornment { get; set; }
    public bool IsSelected { get { return SelectedError == this; } }
    private readonly ErrorSelection _errorSelection;
    public DafnyError SelectedError { get { return _errorSelection.Error; } set { _errorSelection.Error = value; } }
    public Shape Adornment;
    public delegate void StateChangeEventHandler(object sender);
    public event StateChangeEventHandler StateChangeEvent;
    public void Notify()
    {
      if (StateChangeEvent != null)
      {
        StateChangeEvent(this);
      }
    }
    public void UnsubscribeAll()
    {
      if (StateChangeEvent != null)
      {
        foreach (var d in StateChangeEvent.GetInvocationList())
        {
          StateChangeEvent -= (StateChangeEventHandler)d;
        }
      }
    }

    internal class ErrorSelection
    {
      internal DafnyError Error = null;
    }

    internal static readonly ErrorSelection _errorSelectionSingleton = new ErrorSelection();


    /// <summary>
    /// "line" and "col" are expected to be 0-based
    /// </summary>
    public DafnyError(string filename, int line, int col, ErrorCategory cat, string msg, ITextSnapshot snapshot, bool isRecycled, string model = null, bool inCurrentDocument = true)
    {
      Filename = filename;
      Line = Math.Max(0, line);
      Column = Math.Max(0, col);
      Category = cat;
      Message = msg + ((isRecycled && cat == ErrorCategory.VerificationError) ? " (recycled)" : "");
      Snapshot = snapshot;
      if (inCurrentDocument) {
        var sLine = snapshot.GetLineFromLineNumber(line);
        Contract.Assert(Column <= sLine.Length);
        var sLength = Math.Max(0, Math.Min(sLine.Length - Column, 5));
        Span = snapshot.CreateTrackingSpan(sLine.Start + Column, sLength, SpanTrackingMode.EdgeExclusive, TrackingFidelityMode.Forward);
      } else {
        Span = null;
      }
      ModelText = model;
      _errorSelection = _errorSelectionSingleton;
      SelectedStateId = -1;
    }
  }

  #endregion

  #endregion

}
