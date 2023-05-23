// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Io {
  ghost predicate AdvanceTime(oldTime:int) { oldTime > 2 }
  class Time
  {
    static method GetTime()
        ensures AdvanceTime(1);
  }

  ghost function MaxPacketSize() : int { 65507 }

  class UdpClient
  {
    method Receive()
        ensures AdvanceTime(3);

    method Send() returns(ok:bool)
        requires 0 <= MaxPacketSize();
  }
}

abstract module Host {
    import opened Io // Doesn't work.
    //import Io          // Works
}

abstract module Main {
    import H : Host
}
