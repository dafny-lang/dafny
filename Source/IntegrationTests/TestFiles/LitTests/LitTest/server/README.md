The tests in the folder feed base64 encoded data to the Dafny server.

Here are instructions for how to decode and encode `.transcript` files.

# Editing a test

To modify a test file:

* decode the base64-encoded data into plaintext programs,
* modify the programs, and
* re-encode the programs as base64 strings.

For an encoded test file `a.transcript`, decode it into a file `plain.transcript` as follows:

```
$(DAFNY_SERVER) -decode a.transcript > plain.transcript
```

The resulting file is like `a.transcript`, but with all programs decoded.

Next, edit the programs in `plain.transcript` to your liking. If you want to check that you're
getting the output you expect, run

```
$(DAFNY_SERVER) -plaintext plain.transcript
```

When you're satisfied, encode the programs again like this:

```
$(DAFNY_SERVER) -encode plain.transcript > a.transcript
```

Note, the base64 encoding actually contains more information than just a program. It also
contains the path to the original program that created the transcript, and another couple
of fields. This information is not output using `-decode` above, so even if you don't make
any change to `plain.transcript`, you may not get back exactly what you stared with. (In
the unlikely event that you will actually need that information for a test, you're on your
own. It may help to see the "unmarshal" and "marshal" commands in Server.cs.)
