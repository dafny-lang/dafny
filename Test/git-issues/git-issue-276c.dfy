// RUN: %dafny /compile:0 /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Main {
    const A := "asd"
    const B := "def"
    newtype b1 = x | 0 <= x < |A|
    newtype b2 = x | 0 <= x < |A+B|
    newtype b3 = x | 0 <= x < (if 1.2 == 2.2 then 10 else 20)
    newtype b4 = x | 0 <= x < (if 1.2 <= 2.2 then 10 else 20)
    newtype b5 = x | 0 <= x < (5.5).Floor
    newtype b6 = x | 0 <= x < (6.0 as int)
    newtype b7 = x | 0 <= x < (16 as real).Floor
    newtype b8 = x | 0 <= x < (6.0 as real).Floor
    newtype b9 = x | 0 <= x < (9 as nat)
}

