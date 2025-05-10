/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

var Std_Concurrent = Std_Concurrent || {};
var Std_FileIOInternalExterns = Std_FileIOInternalExterns || {};
Std_FileIOInternalExterns.__default = (function() {
  const buffer = require("buffer");
  const fs = require("fs");
  const nodePath = require("path");

  let $module = {};

  /**
   * Attempts to read all bytes from the file at the given `path`, and returns an array of the following values:
   *
   *   - `isError`: true iff an error was thrown during path string conversion or when reading the file
   *   - `bytesRead`: the sequence of bytes from the file, or an empty sequence if `isError` is true
   *   - `errorMsg`: the error message of the thrown error if `isError` is true, or an empty sequence otherwise
   *
   * We return these values individually because `Result` is not defined in the runtime but instead in library code.
   * It is the responsibility of library code to construct an equivalent `Result` value.
   */
  $module.INTERNAL__ReadBytesFromFile = function(path) {
    const emptySeq = _dafny.Seq.of();
    try {
      const readOpts = { encoding: null };  // read as buffer, not string
      const pathStr = path.toVerbatimString(false)
      const buf = fs.readFileSync(pathStr, readOpts);
      const readBytes = _dafny.Seq.from(buf.valueOf(), byte => new BigNumber(byte));
      return [false, readBytes, emptySeq];
    } catch (e) {
      const errorMsg = _dafny.Seq.UnicodeFromString(e.stack);
      return [true, emptySeq, errorMsg];
    }
  }

  /**
   * Attempts to write all given `bytes` to the file at the given `path`, creating nonexistent parent directories as necessary,
   * and returns an array of the following values:
   *
   *   - `isError`: true iff an error was thrown during path string conversion or when writing to the file
   *   - `errorMsg`: the error message of the thrown error if `isError` is true, or an empty sequence otherwise
   *
   * We return these values individually because `Result` is not defined in the runtime but instead in library code.
   * It is the responsibility of library code to construct an equivalent `Result` value.
   */
  $module.INTERNAL__WriteBytesToFile = function(path, bytes) {
    try {
      const buf = buffer.Buffer.from(bytes);
      const pathStr = path.toVerbatimString(false)
      createParentDirs(pathStr);
      fs.writeFileSync(pathStr, buf);  // no need to specify encoding because data is a Buffer
      return [false, _dafny.Seq.of()];
    } catch (e) {
      const errorMsg = _dafny.Seq.from(e.stack);
      return [true, errorMsg];
    }
  }

  /**
   * Creates the nonexistent parent directory(-ies) of the given path.
   */
  const createParentDirs = function(path) {
    const parentDir = nodePath.dirname(nodePath.normalize(path));
    fs.mkdirSync(parentDir, { recursive: true });
  };

  return $module;
})();
