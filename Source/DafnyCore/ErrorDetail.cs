// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;
public static class ErrorDetail {
  // This dictionary maps an errorID (error code) to a code action and explanatory text
  // (which could be moderately lengthy)

  public class Info {
    public Info(string description, object actions, string explanation) {
      this.description = description;
      this.actions = actions;
      this.explanation = explanation;
    }
    public object actions;
    public string explanation;
    public string description;
  }

  static Dictionary<string, Info> errorDetailMap = new Dictionary<string, Info>();

  static ErrorDetail() { init(); }

  static bool initialized = false;
  public static void init() {
    if (initialized) return;
    ParserErrorDetail.init();
    initialized = true;
  }
  // Adds information into the distionary
  public static void Add(string errorID, string description, object actions, string detail) {
    errorDetailMap.Add(errorID, new Info(description, actions, detail));
  }

  // Returns the error detail for the given error ID;
  // result could be null if there is no such detail
  public static string GetDetail(string errorID) {
    //init();
    return errorDetailMap.ContainsKey(errorID) ? errorDetailMap[errorID].explanation : null;
  }
  public static object GetActions(string errorID) {
    //init();
    return errorDetailMap.ContainsKey(errorID) ? errorDetailMap[errorID].actions : null;
  }
  public static string GetDecription(string errorID) {
    //init();
    return errorDetailMap.ContainsKey(errorID) ? errorDetailMap[errorID].description : null;
  }
  public static Info GetInfo(string errorID) {
    //init();
    return errorDetailMap.ContainsKey(errorID) ? errorDetailMap[errorID] : null;
  }
}


