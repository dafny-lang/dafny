---
title: "Error: z3 cannot be opened because the developer cannot be verified"
---

This error occurs on a Mac after a new installation of Dafny, with Z3.
It is a result of security policies on the Mac.

You can fix the result by running the shell script `allow_on_mac.sh`
that is part of the release.

The problem can arise with other components of Dafny as well.

