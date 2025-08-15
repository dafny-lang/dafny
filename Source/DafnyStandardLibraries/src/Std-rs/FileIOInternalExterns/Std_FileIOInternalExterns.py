# Module: Std_FileIOInternalExterns

import traceback
import os
import os.path
import pathlib
import _dafny

class default__:
  @staticmethod
  def INTERNAL__ReadBytesFromFile(path):
    path_str = path.VerbatimString(False)
    try:
      with open(path_str, mode="rb") as file:
          contents = file.read()
          contents_seq = _dafny.Seq(contents)
          return (False, contents_seq, _dafny.Seq())
    except:
      exc_str = traceback.format_exc()
      exc_seq = _dafny.Seq(exc_str)
      return (True, _dafny.Seq(), exc_seq)
  
  @staticmethod
  def INTERNAL__WriteBytesToFile(path, contents):
    path_str = path.VerbatimString(False)
    contents_bytes = bytes(contents)

    try:
      pathlib.Path(path_str).parent.mkdir(parents=True, exist_ok=True)

      with open(path_str, mode="wb") as file:
          contents = file.write(contents_bytes)
          return (False, _dafny.Seq())
    except:
      exc_str = traceback.format_exc()
      exc_seq = _dafny.Seq(exc_str)
      return (True, exc_seq)

