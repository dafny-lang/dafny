module UsesFileIO {
  import Std.FileIO

  method WriteGreeting(path: string)
    decreases *
  {
    var res := FileIO.WriteBytesToFile(path, [104, 105]);
    expect res.Success?;
  }
}
