// A module clashing with a standard-library module anchors a diagnostic inside the
// bundled standard-library .doo. Check that the snippet shows the library's program
// text rather than raw archive bytes (https://github.com/dafny-lang/dafny/issues/6486).
// RUN: %exits-with 2 %resolve --standard-libraries:true --show-snippets:true "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// The snippet lines must be anchored to the .doo-anchored error: an unanchored search is also
// satisfied by the identical module text in this file's own "Related location" snippet, which
// master already prints correctly -- the header was never broken, the snippet body was.
// The line number must be four digits or more so that only the library's own snippet can match;
// this file is a dozen lines long, while the module sits deep inside the bundled .doo.
// CHECK: DafnyStandardLibraries.dfy\(\d+,\d+\): Error: Duplicate module name: Wrappers
// CHECK-NEXT: ^ +\|$
// CHECK-NEXT: ^\d{4,} \| module Std.Wrappers \{$
module Std.Wrappers {
  const x := 1
}
