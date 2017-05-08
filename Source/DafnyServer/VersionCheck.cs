using System;
using System.Globalization;
using System.Runtime.Serialization;
using System.Security.Permissions;
using System.Text.RegularExpressions;

namespace DafnyServer {
  public class VersionCheck {
    private readonly string _currentVersion = "1.9.13";
    
    public void CurrentVersion() {
      Console.WriteLine("VERSION:" + _currentVersion);
    }
  }
  
}
