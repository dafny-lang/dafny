// Diamond dependencies through .doo files (https://github.com/dafny-lang/dafny/issues/6486):
// passing a .doo positionally embeds its modules into the produced library, and combining
// two libraries that embed the same module fails. Check that the embedding is announced
// and that the failure renders the embedded program text rather than raw archive bytes.
// RUN: %build -t=lib --use-basename-for-filename "%S/Inputs/diamondBase.dfy" --output "%S/Output/diamondBase" > "%t"
// RUN: %build -t=lib --use-basename-for-filename "%S/Output/diamondBase.doo" "%S/Inputs/diamondMid.dfy" --output "%S/Output/diamondMid" >> "%t"
// RUN: %exits-with 2 %build -t=lib --use-basename-for-filename --show-snippets:true "%S/Output/diamondBase.doo" "%S/Output/diamondMid.doo" "%s" --output "%S/Output/diamondTop" >> "%t"
// Passing every transitive dependency via --library is the intended workflow and keeps working:
// RUN: %build -t=lib --use-basename-for-filename --library "%S/Output/diamondBase.doo" "%S/Inputs/diamondMid.dfy" --output "%S/Output/diamondMidLib" >> "%t"
// RUN: %build -t=lib --use-basename-for-filename --library "%S/Output/diamondBase.doo" --library "%S/Output/diamondMidLib.doo" "%s" --output "%S/Output/diamondTopLib" >> "%t"
// RUN: %diff "%s.expect" "%t"
module C {
  import A
  import B
}
