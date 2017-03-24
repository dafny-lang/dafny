using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using System.Windows;
using System.Windows.Media;
using System.Windows.Shapes;
using System.Windows.Threading;
using Microsoft.VisualStudio.Shell;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.Text.Formatting;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;
using Dafny = Microsoft.Dafny;


namespace DafnyLanguage
{

  #region UI stuff

  internal class ProgressMarginGlyphFactory : IGlyphFactory
  {
    public UIElement GenerateGlyph(IWpfTextViewLine line, IGlyphTag tag) {
      var pgt = tag as ProgressGlyphTag;
      if (pgt == null) {
        return null;
      }

      return new Rectangle()
      {
        Fill = pgt.Val == 0 ? Brushes.Violet : Brushes.DarkOrange,
        Height = 18.0,
        Width = 3.0
      };
    }
  }

  [Export(typeof(IGlyphFactoryProvider))]
  [Name("ProgressMarginGlyph")]
  [Order(After = "TokenTagger")]
  [ContentType("dafny")]
  [TagType(typeof(ProgressGlyphTag))]
  internal sealed class ProgressMarginGlyphFactoryProvider : IGlyphFactoryProvider
  {
    public IGlyphFactory GetGlyphFactory(IWpfTextView view, IWpfTextViewMargin margin) {
      return new ProgressMarginGlyphFactory();
    }
  }

  internal class ProgressGlyphTag : IGlyphTag
  {
    public readonly int Val;
    public ProgressGlyphTag(int val) {
      Val = val;
    }
  }

  internal class RunVerifierThreadParams
  {
    public RunVerifierThreadParams(Dafny.Program i_program, ITextSnapshot i_snapshot, string i_requestId, ResolverTagger i_errorListHolder, bool i_diagnoseTimeouts)
    {
      program = i_program;
      snapshot = i_snapshot;
      requestId = i_requestId;
      errorListHolder = i_errorListHolder;
      diagnoseTimeouts = i_diagnoseTimeouts;
    }

    public Dafny.Program program;
    public ITextSnapshot snapshot;
    public string requestId;
    public ResolverTagger errorListHolder;
    public bool diagnoseTimeouts;
  }

  #endregion


  #region Provider

  [Export(typeof(ITaggerProvider))]
  [ContentType("dafny")]
  [Name("ProgressTagger")]
  [TagType(typeof(ProgressGlyphTag))]
  class ProgressTaggerProvider : ITaggerProvider
  {
    [Import]
    internal IBufferTagAggregatorFactoryService AggregatorFactory = null;

    [Import(typeof(Microsoft.VisualStudio.Shell.SVsServiceProvider))]
    internal IServiceProvider _serviceProvider = null;

    [Import]
    ITextDocumentFactoryService _textDocumentFactory = null;

    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      ITagAggregator<IDafnyResolverTag> tagAggregator = AggregatorFactory.CreateTagAggregator<IDafnyResolverTag>(buffer);
      // create a single tagger for each buffer.
      Func<ITagger<T>> sc = delegate() { return new ProgressTagger(buffer, _serviceProvider, tagAggregator, _textDocumentFactory) as ITagger<T>; };
      return buffer.Properties.GetOrCreateSingletonProperty<ITagger<T>>(sc);
    }
  }

  #endregion


  #region Tagger

  public class ProgressTagger : ITagger<ProgressGlyphTag>, IDisposable
  {
    ErrorListProvider _errorProvider;
    ITextBuffer _buffer;
    ITextDocument _document;
    bool _disposed;
    bool _logSnapshots = false;
    DateTime _created;
    int _version;
    int _verificationTaskStackSize = 16 * 1024 * 1024;

    readonly DispatcherTimer timer;

    public ProgressTagger(ITextBuffer buffer, IServiceProvider serviceProvider, ITagAggregator<IDafnyResolverTag> tagAggregator, ITextDocumentFactoryService textDocumentFactory) {
      _buffer = buffer;

      if (!textDocumentFactory.TryGetTextDocument(_buffer, out _document))
      {
        _document = null;
      }

      _errorProvider = new ErrorListProvider(serviceProvider);

      timer = new DispatcherTimer(DispatcherPriority.ApplicationIdle);
      timer.Interval = TimeSpan.FromMilliseconds(50);
      timer.Tick += new EventHandler(UponIdle);

      tagAggregator.TagsChanged += new EventHandler<TagsChangedEventArgs>(_aggregator_TagsChanged);
      buffer.Changed += new EventHandler<TextContentChangedEventArgs>(buffer_Changed);
      bufferChangesPostVerificationStart.Add(new SnapshotSpan(buffer.CurrentSnapshot, 0, buffer.CurrentSnapshot.Length));
      _created = DateTime.UtcNow;
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
        if (!_disposed)
        {
          if (disposing)
          {
            if (lastRequestId != null)
            {
              Microsoft.Boogie.ExecutionEngine.CancelRequest(lastRequestId);
            }
            if (_document != null && _document.TextBuffer != null)
            {
              ProgressTaggers.Remove(_document.TextBuffer);
            }
            _buffer.Changed -= buffer_Changed;
            timer.Tick -= UponIdle;
            _errorProvider.Dispose();
            _errorProvider = null;
            ClearCachedVerificationResults();
            if (resolver != null)
            {
              resolver.Dispose();
              resolver = null;
            }
          }

          _disposed = true;
        }
      }
    }

    // The following fields and the contents of the following two lists are protected by the lock "this".
    List<SnapshotSpan> bufferChangesPreVerificationStart = new List<SnapshotSpan>();  // buffer changes after the last completed verification and before the currently running verification
    List<SnapshotSpan> bufferChangesPostVerificationStart = new List<SnapshotSpan>();  // buffer changes since the start of the currently running verification

    void buffer_Changed(object sender, TextContentChangedEventArgs e) {
      lock (this) {
        foreach (var change in e.Changes) {
          var startLine = e.After.GetLineFromPosition(change.NewPosition);
          var endLine = e.After.GetLineFromPosition(change.NewEnd);
          bufferChangesPostVerificationStart.Add(new SnapshotSpan(startLine.Start, endLine.End));
        }
      }
    }

    // The next field is protected by "this"
    ResolverTagger resolver;
    // Keep track of the most recent resolution results.
    void _aggregator_TagsChanged(object sender, TagsChangedEventArgs e) {
      var r = sender as ResolverTagger;
      if (r != null) {
        lock (this) {
          resolver = r;
        }
        timer.Stop();
        timer.Start();
      }
    }

    bool verificationInProgress;  // this field is protected by "this".  Invariant:  !verificationInProgress ==> bufferChangesPreVerificationStart.Count == 0
    public bool VerificationDisabled { get; private set; }
    bool isDiagnosingTimeouts;
    string lastRequestId;

    public static readonly IDictionary<ITextBuffer, ProgressTagger> ProgressTaggers = new ConcurrentDictionary<ITextBuffer, ProgressTagger>();

    public readonly ConcurrentDictionary<string, ITextSnapshot> RequestIdToSnapshot = new ConcurrentDictionary<string, ITextSnapshot>();

    /// <summary>
    /// This method is invoked when the user has been idle for a little while.
    /// Note, "sender" and "args" are allowed to be passed in as null--they are not used by this method.
    /// </summary>
    public void UponIdle(object sender, EventArgs args) {
      lock (this) {
        if (verificationInProgress) {
          // This UponIdle message came at an inopportune time--we've already kicked off a verification.
          // Just back off.
          resolver.UpdateErrorList(resolver.Snapshot);
          return;
        }

        if (resolver == null) return;
        
        Dafny.Program prog;
        ITextSnapshot snap;
        lock (resolver) {
          prog = resolver.Program;
          snap = resolver.Snapshot;
        }
        if (prog == null || VerificationDisabled) return;
        // We have a successfully resolved program to verify

        var dt = isDiagnosingTimeouts;
        if (!dt)
        {
          var resolvedVersion = snap.Version.VersionNumber;
          if (bufferChangesPostVerificationStart.Count == 0)
          {
            // Nothing new to verify.  No reason to start a new verification.
            return;
          }
          else if (!bufferChangesPostVerificationStart.TrueForAll(span => span.Snapshot.Version.VersionNumber <= resolvedVersion))
          {
            // There have been buffer changes since the program that was resolved.  Do nothing here,
            // and instead just await the next resolved program.
            return;
          }
        }

        // at this time, we're committed to running the verifier
        lastRequestId = null;
        lock (RequestIdToSnapshot)
        {
          do
          {
            lastRequestId = DateTime.UtcNow.Ticks.ToString();
          } while (RequestIdToSnapshot.ContainsKey(lastRequestId));
          RequestIdToSnapshot[lastRequestId] = snap;
        }

        if (_document != null)
        {
          ProgressTaggers[_document.TextBuffer] = this;
        }

        RunVerifierThreadParams verifierThreadParams = new RunVerifierThreadParams(prog, snap, lastRequestId, resolver, dt);
        Thread thread = new Thread(RunVerifierThreadRoutine, _verificationTaskStackSize);
        thread.Start(verifierThreadParams);

        verificationInProgress = true;
        if (dt)
        {
          isDiagnosingTimeouts = false;
        }

        // Change orange progress markers into yellow ones
        Contract.Assert(bufferChangesPreVerificationStart.Count == 0);  // follows from monitor invariant
        var empty = bufferChangesPreVerificationStart;
        bufferChangesPreVerificationStart = bufferChangesPostVerificationStart;
        bufferChangesPostVerificationStart = empty;

        // Notify to-whom-it-may-concern about the changes we just made
        NotifyAboutChangedTags(snap);
      }
    }

    private void NotifyAboutChangedTags(ITextSnapshot snap)
    {
      var chng = TagsChanged;
      if (chng != null)
      {
        chng(this, new SnapshotSpanEventArgs(new SnapshotSpan(snap, 0, snap.Length)));
      }
    }

    public void StopVerification()
    {
      Microsoft.Boogie.ExecutionEngine.CancelRequest(lastRequestId);
      lock (this)
      {
        bufferChangesPreVerificationStart.Clear();
        bufferChangesPostVerificationStart.Clear();
        bufferChangesPostVerificationStart.Add(new SnapshotSpan(_buffer.CurrentSnapshot, 0, _buffer.CurrentSnapshot.Length));
        VerificationDisabled = true;
        verificationInProgress = false;
        NotifyAboutChangedTags(_buffer.CurrentSnapshot);
      }
    }

    public void StartVerification(bool clearCache = true, bool diagnoseTimeouts = false)
    {
      lock (this)
      {
        bufferChangesPreVerificationStart.Clear();
        bufferChangesPostVerificationStart.Clear();
        bufferChangesPostVerificationStart.Add(new SnapshotSpan(_buffer.CurrentSnapshot, 0, _buffer.CurrentSnapshot.Length));
        VerificationDisabled = false;
        isDiagnosingTimeouts = diagnoseTimeouts;
        if (clearCache)
        {
          ClearCachedVerificationResults();
        }
        NotifyAboutChangedTags(_buffer.CurrentSnapshot);
      }
    }

    private void ClearCachedVerificationResults()
    {
      if (_document != null)
      {
        Microsoft.Boogie.ExecutionEngine.Cache.RemoveMatchingKeys(new Regex(string.Format(@"^{0}:", Regex.Escape(GetHashCode().ToString()))));
      }
    }

    void RunVerifier(Dafny.Program program, ITextSnapshot snapshot, string requestId, ResolverTagger errorListHolder, bool diagnoseTimeouts) {
      Contract.Requires(program != null);
      Contract.Requires(snapshot != null);
      Contract.Requires(requestId != null);
      Contract.Requires(errorListHolder != null);

      if (_logSnapshots)
      {
        var logDirName = System.IO.Path.Combine(System.IO.Path.GetDirectoryName(program.FullName), "logs");
        Directory.CreateDirectory(logDirName);
        var logFileName = System.IO.Path.Combine(logDirName, System.IO.Path.GetFileName(System.IO.Path.ChangeExtension(program.FullName, string.Format("{0}.v{1}{2}", _created.Ticks, _version, System.IO.Path.GetExtension(program.FullName)))));        
        using (var writer = new StreamWriter(logFileName))
        {
          snapshot.Write(writer);
        }
        _version++;
      }

      DafnyDriver.SetDiagnoseTimeouts(diagnoseTimeouts);

      try
      {
        string filename = _document != null ? _document.FilePath : "<program>";
        var driver = new DafnyDriver(_buffer, filename);
        bool success = driver.Verify(program, errorListHolder, GetHashCode().ToString(), requestId, errorInfo =>
        {
          if (!_disposed)
          {
            errorInfo.BoogieErrorCode = null;
            var isRecycled = false;
            ITextSnapshot s = null;
            if (errorInfo.OriginalRequestId != null)
            {
              isRecycled = errorInfo.OriginalRequestId != requestId;
              RequestIdToSnapshot.TryGetValue(errorInfo.OriginalRequestId, out s);
            }
            if (s == null && errorInfo.RequestId != null)
            {
              RequestIdToSnapshot.TryGetValue(errorInfo.RequestId, out s);
            }
            if (s != null)
            {
              errorListHolder.AddError(new DafnyError(errorInfo.Tok.filename, errorInfo.Tok.line - 1, errorInfo.Tok.col - 1, ErrorCategory.VerificationError, errorInfo.FullMsg, s, isRecycled, errorInfo.Model.ToString(), System.IO.Path.GetFullPath(_document.FilePath) == errorInfo.Tok.filename), errorInfo.ImplementationName, requestId);
              foreach (var aux in errorInfo.Aux)
              {
                errorListHolder.AddError(new DafnyError(aux.Tok.filename, aux.Tok.line - 1, aux.Tok.col - 1, ErrorCategory.AuxInformation, aux.FullMsg, s, isRecycled, null, System.IO.Path.GetFullPath(_document.FilePath) == aux.Tok.filename), errorInfo.ImplementationName, requestId);
              }
            }
          }
        });
        if (!success)
        {
          foreach (var error in driver.Errors) {
            errorListHolder.AddError(error, "$$program$$", requestId);
          }
        }
      }
      catch (Exception e)
      {
        errorListHolder.AddError(new DafnyError("$$program$$", 0, 0, ErrorCategory.InternalError, "Verification process error: " + e.Message, snapshot, false), "$$program$$", requestId);
      }
      finally
      {
        DafnyDriver.SetDiagnoseTimeouts(!diagnoseTimeouts);
      }

      lock (this) {
        bufferChangesPreVerificationStart.Clear();
        verificationInProgress = false;
      }

      errorListHolder.UpdateErrorList(snapshot);

      // Notify to-whom-it-may-concern about the cleared pre-verification changes
      NotifyAboutChangedTags(snapshot);

      // If new changes took place since we started the verification, we may need to kick off another verification
      // immediately.
      UponIdle(null, null);
    }

    private void RunVerifierThreadRoutine(object o)
    {
        RunVerifierThreadParams p = (RunVerifierThreadParams)o;
        RunVerifier(p.program, p.snapshot, p.requestId, p.errorListHolder, p.diagnoseTimeouts);
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    IEnumerable<ITagSpan<ProgressGlyphTag>> ITagger<ProgressGlyphTag>.GetTags(NormalizedSnapshotSpanCollection spans)
    {
      if (spans.Count == 0) yield break;
      var targetSnapshot = spans[0].Snapshot;

      List<SnapshotSpan> pre;
      List<SnapshotSpan> post;
      lock (this) {
        pre = bufferChangesPreVerificationStart.ToList();
        post = bufferChangesPostVerificationStart.ToList();
      }

      // If the requested snapshot isn't the same as the one our words are on, translate our spans to the expected snapshot
      var chs = new NormalizedSnapshotSpanCollection(pre.Select(span => span.TranslateTo(targetSnapshot, SpanTrackingMode.EdgeExclusive)));
      foreach (SnapshotSpan span in NormalizedSnapshotSpanCollection.Overlap(spans, chs)) {
        yield return new TagSpan<ProgressGlyphTag>(span, new ProgressGlyphTag(0));
      }
      chs = new NormalizedSnapshotSpanCollection(post.Select(span => span.TranslateTo(targetSnapshot, SpanTrackingMode.EdgeExclusive)));
      foreach (SnapshotSpan span in NormalizedSnapshotSpanCollection.Overlap(spans, chs)) {
        yield return new TagSpan<ProgressGlyphTag>(span, new ProgressGlyphTag(1));
      }
    }
  }

  #endregion

}
