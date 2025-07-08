// RUN: %exits-with -any %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Attributes on top-level declarations

@Option("--function-syntax:3") // Should be Options
module SimpleLinearModule {
}

function OtherUnresolvedfunction(): string {
  3
}