// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;
public static class ErrorDetail {
  // This dictionary maps an errorID (error code) to a code action and explanatory text
  // (which could be moderately lengthy)


  static private Dictionary<string, string> errorDetailMap = new Dictionary<string, string>();

  static ErrorDetail() { init(); }

  static bool initialized = false;
  public static void init() {
    if (!initialized) {
      ParserErrorDetail.init();
      initialized = true;
    }
  }
  // Adds information into the dictionary
  public static void Add(string errorID, string detail) {
    errorDetailMap.Add(errorID, detail);
  }

  // Returns the error detail for the given error ID;
  // result could be null if there is no such detail
#nullable enable
  public static string? GetDetail(string errorID) {
    if(errorDetailMap.TryGetValue(errorID, out var result)) {
      return result;
    }
    return null;
  }
#nullable disable
}


