// The embedding note has to cover what a .doo can actually contribute, not just top-level modules
// (https://github.com/dafny-lang/dafny/issues/6486). A .doo may hold only a top-level type
// declaration, and a dotted module name puts the real declaration under a synthesized parent that
// has no origin of its own; a flat scan for top-level modules passed over both.
// RUN: %build -t=lib --use-basename-for-filename "%S/Inputs/embedTypeOnly.dfy" --output "%S/Output/embedTypeOnly" > "%t"
// RUN: %build -t=lib --use-basename-for-filename --show-hints "%S/Output/embedTypeOnly.doo" "%s" --output "%S/Output/embedTypeTop" >> "%t"
// RUN: %build -t=lib --use-basename-for-filename "%S/Inputs/embedDotted.dfy" --output "%S/Output/embedDotted" >> "%t"
// RUN: %build -t=lib --use-basename-for-filename --show-hints "%S/Output/embedDotted.doo" "%S/Inputs/embedDottedUser.dfy" --output "%S/Output/embedDottedTop" >> "%t"
// Passing the same .doo with --library embeds nothing, so it must not be announced:
// RUN: %build -t=lib --use-basename-for-filename --show-hints --library "%S/Output/embedTypeOnly.doo" "%s" --output "%S/Output/embedTypeLib" >> "%t"
// RUN: %diff "%s.expect" "%t"

method UseColor() {
  var c: Color := Red;
}
