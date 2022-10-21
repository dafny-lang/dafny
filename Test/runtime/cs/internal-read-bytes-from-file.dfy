// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target:cs "%s" -- "%s.data" >> "%t"
// RUN: %diff "%s.expect" "%t"

method
  {:extern "Dafny.Helpers", "INTERNAL_ReadBytesFromFile"}
  {:compile false}
  INTERNAL_ReadBytesFromFile(path: string)
  returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)

method Main(args: seq<string>) {
  {
    var expectedStr := "Hello world\nGoodbye\n";
    var expectedBytes := seq(|expectedStr|, i requires 0 <= i < |expectedStr| => expectedStr[i] as bv8);

    expect |args| == 2;
    var dataFilePath := args[1];

    var isError, bytesRead, errorMsg := INTERNAL_ReadBytesFromFile(dataFilePath);
    expect !isError;
    expect bytesRead == expectedBytes;
    expect errorMsg == [];
  }

  {
    var isError, bytesRead, errorMsg := INTERNAL_ReadBytesFromFile("");
    expect isError;
    expect bytesRead == [];
    expect "System.ArgumentException: " <= errorMsg;
  }
}
