/*******************************************************************************
 *  SeqExt - Extensions to Std.Collections.Seq
 *  
 *  This module adds MaxBy and MinBy functions to the Seq functionality
 *  without redefining the entire Seq module (which would cause duplicate errors).
 *
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Std.Collections.SeqExt {
  import opened Wrappers

  /**********************************************************
   *
   *  Finding Maximum and Minimum Elements
   *
   ***********************************************************/

/// Find the maximum element in a sequence using a comparator function
///
/// The comparator function should return:
///   -1 if a < b (first argument is less than second)
///    0 if a == b (equal)
///    1 if a > b (first argument is greater than second)
///
/// Example usage with Duration:
///   var maxDuration := MaxBy(durations, Duration.Compare)
  function MaxBy<T>(s: seq<T>, comparator: (T, T) -> int): T
    requires |s| > 0
    decreases |s|
  {
    MaxByHelper(s, 1, s[0], comparator)
  }

/// Helper function for MaxBy - iterates through sequence tracking the maximum
  function MaxByHelper<T>(s: seq<T>, idx: nat, current: T, comparator: (T, T) -> int): T
    requires idx <= |s|
    decreases |s| - idx
  {
    if idx == |s| then
      current
    else
      var cmp := comparator(current, s[idx]);
      var next := if cmp < 0 then s[idx] else current;
      MaxByHelper(s, idx + 1, next, comparator)
  }

/// Find the minimum element in a sequence using a comparator function
///
/// The comparator function should return:
///   -1 if a < b (first argument is less than second)
///    0 if a == b (equal)
///    1 if a > b (first argument is greater than second)
///
/// Example usage with Duration:
///   var minDuration := MinBy(durations, Duration.Compare)
  function MinBy<T>(s: seq<T>, comparator: (T, T) -> int): T
    requires |s| > 0
    decreases |s|
  {
    MinByHelper(s, 1, s[0], comparator)
  }

/// Helper function for MinBy - iterates through sequence tracking the minimum
  function MinByHelper<T>(s: seq<T>, idx: nat, current: T, comparator: (T, T) -> int): T
    requires idx <= |s|
    decreases |s| - idx
  {
    if idx == |s| then
      current
    else
      var cmp := comparator(current, s[idx]);
      var next := if cmp > 0 then s[idx] else current;
      MinByHelper(s, idx + 1, next, comparator)
  }
}
