// NONUNIFORM: Only testing the translation to Boogie aspect of the pipeline depending on checks
// RUN: %baredafny run  %args --log-level verbose "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%S/TranslationCasesTranslate.check"

// RUN: %baredafny run  %args --log-level verbose --no-verify "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%S/TranslationCasesNoTranslation.check"

// RUN: %baredafny run  %args --log-level verbose --no-verify --bprint:file.bpl "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%S/TranslationCasesTranslate.check"

// RUN: %baredafny run  %args --log-level verbose --no-verify --sprint:file.bpl "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%S/TranslationCasesTranslate.check"

// RUN: %baredafny run  %args --log-level verbose --no-verify --sprint:file.bpl "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%S/TranslationCasesTranslate.check"

module VerifiableModule {
  @Test
  method CanTest() {
    assert 1 == 1;
    expect 1 == 1;
  }
  method Main() {
    CanTest();
  }
}
