package DafnyStdLibs_FileIOInternalExterns

import (
	_dafny "dafny"
	os "os"
	filepath "path/filepath"
)

func INTERNAL__ReadBytesFromFile(path _dafny.Sequence) (isError bool, bytesRead _dafny.Sequence, errorMsg _dafny.Sequence) {
	p := _dafny.SequenceVerbatimString(path, false)
	dat, err := os.ReadFile(p)
	if err != nil {
		errAsSequence := _dafny.UnicodeSeqOfUtf8Bytes(err.Error())
		return true, _dafny.EmptySeq, errAsSequence
	}
	datAsSequence := _dafny.SeqOfBytes(dat)
	return false, datAsSequence, _dafny.EmptySeq
}

func INTERNAL__WriteBytesToFile(path _dafny.Sequence, bytes _dafny.Sequence) (isError bool, errorMsg _dafny.Sequence) {
	p := _dafny.SequenceVerbatimString(path, false)

	// Create directories
	os.MkdirAll(filepath.Dir(p), os.ModePerm)

	bytesArray := _dafny.ToByteArray(bytes)
	err := os.WriteFile(p, bytesArray, 0644)
	if err != nil {
		errAsSequence := _dafny.UnicodeSeqOfUtf8Bytes(err.Error())
		return true, errAsSequence
	}
	return false, _dafny.EmptySeq
}
