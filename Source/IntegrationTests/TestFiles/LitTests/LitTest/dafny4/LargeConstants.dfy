// RUN: %testDafnyForEachResolver "%s"


lemma largeIsLarge()
  ensures 0x8000000000000000 > 0 {
}

lemma SmallIsSmall()
  ensures -0x8000000000000000 < 0 {
}

lemma ShouldCancelOut()
  ensures -0x8000000000000000 + 0x8000000000000000 == 0 {
}
