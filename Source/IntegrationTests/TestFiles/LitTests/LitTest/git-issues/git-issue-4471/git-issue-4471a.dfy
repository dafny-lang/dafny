// RUN: %exits-with 0 %verify "%s"

trait YT<W> extends object {
  const f: W
}

class Y extends YT<Y -> nat> {
}
