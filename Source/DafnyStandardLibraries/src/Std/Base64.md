## The `Base64` module

The `Std.Base64` module contains an encoder and decoder for Base64, which allows arbitrary byte sequences to be represented in sequences of characters drawn entirely from 7-bit ASCII. This encoder and decoder have two interfaces, one which uses `uint8` to represent arbitrary bytes, and one which uses `bv8`. The encoder and decoder are proved to be inverses of each other, for both interfaces.

The `uint8`-based interface consists of the `Encode` and `Decode` functions along with the `EncodeDecode` and `DecodeEncode` lemmas. The `bv8`-based interface consists of the `EncodeBV` and `DecodeBV` functions along with the `EncodeDecodeBV` and `DecodeEncodeBV` lemmas. The `uint8`-based interface is a wrapper on top of the `bv8`-based interface, because Base64 encoding is more straightforward to specify and verify using bit vectors.

The implementation currently uses a recursive approach with sequence concatenation, which limits its performance on large sequences. A more efficient implementation will be possible without changing the public interface, however.
