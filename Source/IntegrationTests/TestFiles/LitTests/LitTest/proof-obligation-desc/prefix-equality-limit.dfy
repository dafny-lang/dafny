// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

codatatype Stream = More(Stream)

method PrefixEqualityLimit(s: Stream, i: int) {
  ghost var g := s ==#[i] s;
}