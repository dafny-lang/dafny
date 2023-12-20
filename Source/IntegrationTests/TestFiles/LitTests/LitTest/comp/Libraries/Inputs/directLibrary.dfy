include "indirectLibrary.dfy"

module GloballyUniqueProducer {

  module ExportingModule {
    import A = AnotherGloballyUniqueProducer.ExportingModule
    const exportedVariable := A.exportedVariable + 1
  }
}