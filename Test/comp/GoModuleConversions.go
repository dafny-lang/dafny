package GoModuleConversions

import (
  "dafny"
	url "net/url"
)

func ParseURL(dafnyAddress dafny.Sequence) (*url.URL, error) {
	var address = dafny.SequenceVerbatimString(dafnyAddress, false);
  return url.Parse(address)
}
