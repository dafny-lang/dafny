package DafnyStdLibs_FileIOInternalExterns

import (
  _dafny "dafny"
  os "os"
)

type CompanionStruct_NonDefaultClass_ struct{}

var Companion_NonDefaultClass_ = CompanionStruct_NonDefaultClass_{}

func (CompanionStruct_NonDefaultClass_) INTERNAL__ReadBytesFromFile(path dafny.Sequence) (isError bool, bytesRead dafny.Sequence, errorMsg dafny.Sequence) {
  p = dafny.SequenceVerbatimString(path, false)
	dat, err := os.ReadFile(p)
  if err != nil {
		return (true, dat, nil)
	}
  return (false, nil, err.Error())
}

func (CompanionStruct_NonDefaultClass_) INTERNAL__WriteBytesToFile(path dafny.Sequence, bytes dafny.Sequence) (isError bool, errorMsg dafny.Sequence) {
  p = dafny.SequenceVerbatimString(path, false)
	dat = 
	err := os.WriteFile(p, dat)
  if err != nil {
		return (true, err.Error())
	}
  return (false, nil)
}