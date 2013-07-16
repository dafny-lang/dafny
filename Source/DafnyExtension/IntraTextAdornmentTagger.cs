//***************************************************************************
//
//    Copyright (c) Microsoft Corporation. All rights reserved.
//    This code is licensed under the Visual Studio SDK license terms.
//    THIS CODE IS PROVIDED *AS IS* WITHOUT WARRANTY OF
//    ANY KIND, EITHER EXPRESS OR IMPLIED, INCLUDING ANY
//    IMPLIED WARRANTIES OF FITNESS FOR A PARTICULAR
//    PURPOSE, MERCHANTABILITY, OR NON-INFRINGEMENT.
//
//***************************************************************************

using System;
using System.Collections.Generic;
using System.Linq;
using System.Windows;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.Text.Tagging;

namespace DafnyLanguage
{
  /// <summary>
  /// Helper class for interspersing adornments into text.
  /// </summary>
  /// <remarks>
  /// To avoid an issue around intra-text adornment support and its interaction with text buffer changes,
  /// this tagger reacts to text and color tag changes with a delay. It waits to send out its own TagsChanged
  /// event until the WPF Dispatcher is running again and it takes care to report adornments
  /// that are consistent with the latest sent TagsChanged event by storing that particular snapshot
  /// and using it to query for the data tags.
  /// </remarks>
  internal abstract class IntraTextAdornmentTagger<TData, TAdornment>
      : ITagger<IntraTextAdornmentTag>
      where TAdornment : UIElement
  {
    protected readonly IWpfTextView view;
    private Dictionary<SnapshotSpan, TAdornment> adornmentCache = new Dictionary<SnapshotSpan, TAdornment>();
    protected ITextSnapshot snapshot { get; private set; }
    private readonly List<SnapshotSpan> invalidatedSpans = new List<SnapshotSpan>();

    protected IntraTextAdornmentTagger(IWpfTextView view)
    {
      this.view = view;
      this.snapshot = view.TextBuffer.CurrentSnapshot;

      this.view.LayoutChanged += HandleLayoutChanged;
      this.view.TextBuffer.Changed += HandleBufferChanged;
    }

    /// <param name="span">The span of text that this adornment will elide.</param>
    /// <returns>Adornment corresponding to given data. May be null.</returns>
    protected abstract TAdornment CreateAdornment(TData data, SnapshotSpan span);

    /// <returns>True if the adornment was updated and should be kept. False to have the adornment removed from the view.</returns>
    protected abstract bool UpdateAdornment(TAdornment adornment, TData data);

    /// <param name="spans">Spans to provide adornment data for. These spans do not necessarily correspond to text lines.</param>
    /// <remarks>
    /// If adornments need to be updated, call <see cref="RaiseTagsChanged"/> or <see cref="InavlidateSpans"/>.
    /// This will, indirectly, cause <see cref="GetAdornmentData"/> to be called.
    /// </remarks>
    /// <returns>
    /// A sequence of:
    ///  * adornment data for each adornment to be displayed
    ///  * the span of text that should be elided for that adornment (zero length spans are acceptable)
    ///  * and affinity of the adornment (this should be null if and only if the elided span has a length greater than zero)
    /// </returns>
    protected abstract IEnumerable<Tuple<SnapshotSpan, PositionAffinity?, TData>> GetAdornmentData(NormalizedSnapshotSpanCollection spans);

    private void HandleBufferChanged(object sender, TextContentChangedEventArgs args)
    {
      var editedSpans = args.Changes.Select(change => new SnapshotSpan(args.After, change.NewSpan)).ToList();
      InvalidateSpans(editedSpans);
    }

    /// <summary>
    /// Causes intra-text adornments to be updated asynchronously.
    /// </summary>
    protected void InvalidateSpans(IList<SnapshotSpan> spans)
    {
      lock (this.invalidatedSpans)
      {
        bool wasEmpty = this.invalidatedSpans.Count == 0;
        this.invalidatedSpans.AddRange(spans);

        if (wasEmpty && this.invalidatedSpans.Count > 0)
          this.view.VisualElement.Dispatcher.BeginInvoke(new Action(AsyncUpdate));
      }
    }

    private void AsyncUpdate()
    {
      // Store the snapshot that we're now current with and send an event
      // for the text that has changed.
      if (this.snapshot != this.view.TextBuffer.CurrentSnapshot)
      {
        this.snapshot = this.view.TextBuffer.CurrentSnapshot;

        Dictionary<SnapshotSpan, TAdornment> translatedAdornmentCache = new Dictionary<SnapshotSpan, TAdornment>();

        foreach (var keyValuePair in this.adornmentCache)
          translatedAdornmentCache.Add(keyValuePair.Key.TranslateTo(this.snapshot, SpanTrackingMode.EdgeExclusive), keyValuePair.Value);

        this.adornmentCache = translatedAdornmentCache;
      }

      List<SnapshotSpan> translatedSpans;
      lock (this.invalidatedSpans)
      {
        translatedSpans = this.invalidatedSpans.Select(s => s.TranslateTo(this.snapshot, SpanTrackingMode.EdgeInclusive)).ToList();
        this.invalidatedSpans.Clear();
      }

      if (translatedSpans.Count == 0)
        return;

      var start = translatedSpans.Select(span => span.Start).Min();
      var end = translatedSpans.Select(span => span.End).Max();

      RaiseTagsChanged(new SnapshotSpan(start, end));
    }

    /// <summary>
    /// Causes intra-text adornments to be updated synchronously.
    /// </summary>
    protected void RaiseTagsChanged(SnapshotSpan span)
    {
      var handler = this.TagsChanged;
      if (handler != null)
        handler(this, new SnapshotSpanEventArgs(span));
    }

    private void HandleLayoutChanged(object sender, TextViewLayoutChangedEventArgs e)
    {
      SnapshotSpan visibleSpan = this.view.TextViewLines.FormattedSpan;

      // Filter out the adornments that are no longer visible.
      List<SnapshotSpan> toRemove = new List<SnapshotSpan>(
          from keyValuePair
          in this.adornmentCache
          where !keyValuePair.Key.TranslateTo(visibleSpan.Snapshot, SpanTrackingMode.EdgeExclusive).IntersectsWith(visibleSpan)
          select keyValuePair.Key);

      foreach (var span in toRemove)
        this.adornmentCache.Remove(span);
    }


    // Produces tags on the snapshot that the tag consumer asked for.
    public virtual IEnumerable<ITagSpan<IntraTextAdornmentTag>> GetTags(NormalizedSnapshotSpanCollection spans)
    {
      if (spans == null || spans.Count == 0)
        yield break;

      // Translate the request to the snapshot that this tagger is current with.

      ITextSnapshot requestedSnapshot = spans[0].Snapshot;

      var translatedSpans = new NormalizedSnapshotSpanCollection(spans.Select(span => span.TranslateTo(this.snapshot, SpanTrackingMode.EdgeExclusive)));

      // Grab the adornments.
      foreach (var tagSpan in GetAdornmentTagsOnSnapshot(translatedSpans))
      {
        // Translate each adornment to the snapshot that the tagger was asked about.
        SnapshotSpan span = tagSpan.Span.TranslateTo(requestedSnapshot, SpanTrackingMode.EdgeExclusive);

        IntraTextAdornmentTag tag = new IntraTextAdornmentTag(tagSpan.Tag.Adornment, tagSpan.Tag.RemovalCallback, tagSpan.Tag.Affinity);
        yield return new TagSpan<IntraTextAdornmentTag>(span, tag);
      }
    }

    // Produces tags on the snapshot that this tagger is current with.
    private IEnumerable<TagSpan<IntraTextAdornmentTag>> GetAdornmentTagsOnSnapshot(NormalizedSnapshotSpanCollection spans)
    {
      if (spans.Count == 0)
        yield break;

      ITextSnapshot snapshot = spans[0].Snapshot;

      System.Diagnostics.Debug.Assert(snapshot == this.snapshot);

      // Since WPF UI objects have state (like mouse hover or animation) and are relatively expensive to create and lay out,
      // this code tries to reuse controls as much as possible.
      // The controls are stored in this.adornmentCache between the calls.

      // Mark which adornments fall inside the requested spans with Keep=false
      // so that they can be removed from the cache if they no longer correspond to data tags.
      HashSet<SnapshotSpan> toRemove = new HashSet<SnapshotSpan>();
      foreach (var ar in this.adornmentCache)
        if (spans.IntersectsWith(new NormalizedSnapshotSpanCollection(ar.Key)))
          toRemove.Add(ar.Key);

      foreach (var spanDataPair in GetAdornmentData(spans).Distinct(new Comparer()))
      {
        // Look up the corresponding adornment or create one if it's new.
        TAdornment adornment;
        SnapshotSpan snapshotSpan = spanDataPair.Item1;
        PositionAffinity? affinity = spanDataPair.Item2;
        TData adornmentData = spanDataPair.Item3;
        if (this.adornmentCache.TryGetValue(snapshotSpan, out adornment))
        {
          if (UpdateAdornment(adornment, adornmentData))
            toRemove.Remove(snapshotSpan);
        }
        else
        {
          adornment = CreateAdornment(adornmentData, snapshotSpan);

          if (adornment == null)
            continue;

          // Get the adornment to measure itself. Its DesiredSize property is used to determine
          // how much space to leave between text for this adornment.
          // Note: If the size of the adornment changes, the line will be reformatted to accommodate it.
          // Note: Some adornments may change size when added to the view's visual tree due to inherited
          // dependency properties that affect layout. Such options can include SnapsToDevicePixels,
          // UseLayoutRounding, TextRenderingMode, TextHintingMode, and TextFormattingMode. Making sure
          // that these properties on the adornment match the view's values before calling Measure here
          // can help avoid the size change and the resulting unnecessary re-format.
          adornment.Measure(new Size(double.PositiveInfinity, double.PositiveInfinity));

          this.adornmentCache.Add(snapshotSpan, adornment);
        }

        yield return new TagSpan<IntraTextAdornmentTag>(snapshotSpan, new IntraTextAdornmentTag(adornment, null, affinity));
      }

      foreach (var snapshotSpan in toRemove)
        this.adornmentCache.Remove(snapshotSpan);
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    private class Comparer : IEqualityComparer<Tuple<SnapshotSpan, PositionAffinity?, TData>>
    {
      public bool Equals(Tuple<SnapshotSpan, PositionAffinity?, TData> x, Tuple<SnapshotSpan, PositionAffinity?, TData> y)
      {
        if (x == null && y == null)
          return true;
        if (x == null || y == null)
          return false;
        return x.Item1.Equals(y.Item1);
      }

      public int GetHashCode(Tuple<SnapshotSpan, PositionAffinity?, TData> obj)
      {
        return obj.Item1.GetHashCode();
      }
    }

  }
}
