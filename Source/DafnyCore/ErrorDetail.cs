// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;
public static class ErrorDetail {

  public enum ErrorID {
    None,

    sc_malformed_pragma,
    sc_unknown_pragma,
    p_bad_const_initialize_op,
    p_deprecated_semicolon,
    p_no_leading_underscore,
    p_abstract_not_allowed,
    p_no_ghost_for_by_method,
    p_no_static,
  }

  // This dictionary maps an errorID (error code) to a code action and explanatory text
  // (which could be moderately lengthy)


  static private Dictionary<ErrorID, string> errorDetailMap = new Dictionary<ErrorID, string>();

  static ErrorDetail() { init(); }

  static bool initialized = false;
  public static void init() {
    if (!initialized) {
      ParserErrorDetail.init();
      initialized = true;
    }
  }
  // Adds information into the dictionary
  public static void Add(ErrorID errorID, string detail) {
    errorDetailMap.Add(errorID, detail);
  }

  // Returns the error detail for the given error ID;
  // result could be null if there is no such detail
#nullable enable
  public static string? GetDetail(ErrorID errorID) {
    if (errorDetailMap.TryGetValue(errorID, out var result)) {
      return result;
    }
    return null;
  }
#nullable disable
}


