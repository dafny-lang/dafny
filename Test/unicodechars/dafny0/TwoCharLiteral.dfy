// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename --unicode-char:false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
    var c := '🚀';
}
