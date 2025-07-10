// RUN: ! %verify %s > %t
// RUN: %diff "%s.expect" "%t"

// Diamond property

trait Common { method M() { } }
trait Left extends Common { method M() { } }
trait Right extends Common { method M() { } }
trait Both extends Left, Right { } // error: Both inherits M with a body in two different ways

trait BothRedeclare extends Left, Right { method M() { } } // error: Both inherits M with a body in two different ways