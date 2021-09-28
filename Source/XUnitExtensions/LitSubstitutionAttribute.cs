using System;
using System.Net.Mail;

namespace XUnitExtensions {
  [AttributeUsage(AttributeTargets.Method, AllowMultiple = true)]
  public class LitSubstitutionAttribute : Attribute {
    public LitSubstitutionAttribute(string key) {
      
    }
    
    public virtual Type MainClass { get; set; }
    public virtual string CLIPath { get; set; }
    
    public virtual string[] Arguments { get; set; }
  }
}