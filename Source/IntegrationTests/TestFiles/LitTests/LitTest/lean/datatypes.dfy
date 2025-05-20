
// dafny 4.10.1.0
// Command Line Options:
// generatedOutput

datatype tData = New(value: nat, bit: bool)

datatype tAck = New(bit: bool)

datatype tSenderInit = New(receiver: nat, messages: seq<nat>, bit: bool)

datatype tReceiverInit = New(sender: nat, bit: bool)

datatype tSenderState = New(messages: seq<nat>, current: nat, bit: bool)

datatype tReceiverState = New(messages: seq<nat>, bit: bool) {
  function This(): int { 3 }
}

datatype Event = Null(Null: ()) | halt(Null: ()) | eData(TData: tData) | eAck(TAck: tAck) | eTick(Null: ()) | eSenderInit(TSenderInit: tSenderInit) | eReceiverInit(TReceiverInit: tReceiverInit) | eSenderState(TSenderState: tSenderState) | eReceiverState(TReceiverState: tReceiverState)
