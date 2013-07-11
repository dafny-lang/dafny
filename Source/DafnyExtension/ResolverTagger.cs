//***************************************************************************
// Copyright © 2010 Microsoft Corporation.  All Rights Reserved.
// This code released under the terms of the
// Microsoft Public License (MS-PL, http://opensource.org/licenses/ms-pl.html.)
//***************************************************************************


using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.Diagnostics.Contracts;
using System.Linq;
using EnvDTE;
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
  [TagType(typeof(DafnyResolverTag))]
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

  public abstract class DafnyResolverTag : ITag
  {
  }

  public class DafnyErrorResolverTag : DafnyResolverTag
  {
    public readonly string Typ;
    public readonly string Msg;
    public DafnyErrorResolverTag(string typ, string msg)
    {
      Typ = typ;
      Msg = msg;
    }
  }

  public class DafnySuccessResolverTag : DafnyResolverTag
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
  public sealed class ResolverTagger : ITagger<DafnyResolverTag>, IDisposable
  {
    readonly ITextBuffer _buffer;
    readonly ITextDocument _document;
    ErrorListProvider _errorProvider;

    // The 'Snapshot' and 'Program' fields should be updated and read together, so they are protected by "this"
    public ITextSnapshot Snapshot;  // may be null
    public Dafny.Program Program;  // non-null only if the snapshot contains a Dafny program that type checks

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
    
    internal void ReInitializeVerificationErrors(string mostRecentRequestId, List<Microsoft.Boogie.Declaration> units)
    {
      var implNames = units.OfType<Microsoft.Boogie.Implementation>().Select(impl => impl.Name);
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
        return _verificationErrors.Values.Where(ec => ec.RequestId == MostRecentRequestId).SelectMany(ec => ec.Errors.Reverse());
      }
    }

    public IEnumerable<DafnyError> AllErrors
    {
      get
      {
        lock (this)
        {
          if (_resolutionErrors != null && _resolutionErrors.Any())
          {
            return _resolutionErrors;
          }
          else
          {
            return VerificationErrors;
          }
        }
      }
    }

    public static readonly IDictionary<string, Dafny.Program> Programs = new ConcurrentDictionary<string, Dafny.Program>();

    internal ResolverTagger(ITextBuffer buffer, IServiceProvider serviceProvider, ITextDocumentFactoryService textDocumentFactory)
    {
      _buffer = buffer;
      if (!textDocumentFactory.TryGetTextDocument(_buffer, out _document))
        _document = null;
      Snapshot = null;  // this makes sure the next snapshot will look different
      _errorProvider = new ErrorListProvider(serviceProvider);

      BufferIdleEventUtil.AddBufferIdleEventListener(_buffer, ResolveBuffer);
    }

    public void Dispose()
    {
      Dispose(true);
      GC.SuppressFinalize(this);
    }

    private void Dispose(bool disposing)
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
        }

        m_disposed = true;
      }
    }

    /// <summary>
    /// Find the Error tokens in the set of all tokens and create an ErrorTag for each
    /// </summary>
    public IEnumerable<ITagSpan<DafnyResolverTag>> GetTags(NormalizedSnapshotSpanCollection spans)
    {
      if (spans.Count == 0) yield break;
      var currentSnapshot = spans[0].Snapshot;
      foreach (var err in AllErrors)
      {
        if (err.Category != ErrorCategory.ProcessError)
        {
          string ty;  // the COLORs below indicate what I see on my machine
          switch (err.Category)
          {
            default:  // unexpected category
            case ErrorCategory.ParseError:
            case ErrorCategory.ParseWarning:
              ty = "syntax error"; break;  // COLOR: red
            case ErrorCategory.ResolveError:
              ty = "compiler error"; break;  // COLOR: blue
            case ErrorCategory.VerificationError:
              ty = "error"; break;  // COLOR: red
            case ErrorCategory.AuxInformation:
              ty = "other error"; break;  // COLOR: purple red
            case ErrorCategory.InternalError:
              ty = "error"; break;  // COLOR: red
          }
          yield return new TagSpan<DafnyResolverTag>(err.Span.GetSpan(currentSnapshot), new DafnyErrorResolverTag(ty, err.Message));
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
        yield return new TagSpan<DafnyResolverTag>(new SnapshotSpan(snap, 0, snap.Length), new DafnySuccessResolverTag(prog));
      }
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;
    private bool m_disposed;

    /// <summary>
    /// Calls the Dafny parser/resolver/type checker on the contents of the buffer, updates the Error List accordingly.
    /// </summary>
    void ResolveBuffer(object sender, EventArgs args)
    {
      ITextSnapshot snapshot = _buffer.CurrentSnapshot;
      if (snapshot == Snapshot)
        return;  // we've already done this snapshot

      var driver = new DafnyDriver(snapshot, _document != null ? _document.FilePath : "<program>");
      List<DafnyError> newErrors;
      Dafny.Program program;
      try
      {
        program = driver.ProcessResolution();
        newErrors = driver.Errors;
      }
      catch (Exception e)
      {
        newErrors = new List<DafnyError> { new DafnyError(0, 0, ErrorCategory.InternalError, "internal Dafny error: " + e.Message, snapshot) };
        program = null;
      }

      lock (this)
      {
        Snapshot = snapshot;
        Program = program;
      }

      if (program != null && _document != null)
      {
        Programs[_document.FilePath] = program;
      }
      else if (_document != null)
      {
        Programs.Remove(_document.FilePath);
      }

      _resolutionErrors = newErrors;

      UpdateErrorList(snapshot);
    }

    public void UpdateErrorList(ITextSnapshot snapshot)
    {
      lock (this) 
      {
        if (_errorProvider != null)
        {
          _errorProvider.SuspendRefresh();  // reduce flickering
          _errorProvider.Tasks.Clear();
          foreach (var err in AllErrors)
          {
            var span = err.Span.GetSpan(snapshot);
            var lineNum = snapshot.GetLineNumberFromPosition(span.Start.Position);
            var line = snapshot.GetLineFromPosition(span.Start.Position);
            var columnNum = span.Start - line.Start;
            ErrorTask task = new ErrorTask()
            {
              Category = TaskCategory.BuildCompile,
              ErrorCategory = CategoryConversion(err.Category),
              Text = err.Message,
              Line = lineNum,
              Column = columnNum
            };
            if (_document != null)
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
    ProcessError, ParseWarning, ParseError, ResolveError, VerificationError, AuxInformation, InternalError
  }

  public class DafnyError
  {
    public readonly int Line;  // 0 based
    public readonly int Column;  // 0 based
    public readonly ErrorCategory Category;
    public readonly string Message;
    public readonly ITrackingSpan Span;
    /// <summary>
    /// "line" and "col" are expected to be 0-based
    /// </summary>
    public DafnyError(int line, int col, ErrorCategory cat, string msg, ITextSnapshot snapshot)
    {
      Line = Math.Max(0, line);
      Column = Math.Max(0, col);
      Category = cat;
      Message = msg;
      var sLine = snapshot.GetLineFromLineNumber(line);
      Contract.Assert(Column <= sLine.Length);
      var sLength = Math.Max(0, Math.Min(sLine.Length - Column, 5));
      Span = snapshot.CreateTrackingSpan(sLine.Start + Column, sLength, SpanTrackingMode.EdgeExclusive, TrackingFidelityMode.Forward);
    }
  }

  #endregion

  #endregion

}
