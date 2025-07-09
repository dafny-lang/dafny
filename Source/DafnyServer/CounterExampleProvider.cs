// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.Serialization;
using System.Text.RegularExpressions;
using Microsoft.Boogie;
using Microsoft.Dafny;

namespace DafnyServer {
  public sealed class CounterExampleProvider {
    public readonly string ModelBvd;

    public CounterExampleProvider() {
      ModelBvd = $"./model{GetHashCode()}.bvd";
    }

    public CounterExample LoadCounterModel(DafnyOptions options) {
      try {
        var models = LoadModelFromFile(options);
        return ConvertModels(models);
      } catch (Exception) {
        return new CounterExample();
      }
    }

    private List<DafnyModel> LoadModelFromFile(DafnyOptions options) {
      using var wr = new StreamReader(ModelBvd);
      var output = wr.ReadToEnd();
      var models = ExtractModels(output);
      var dafnyModels = BuildModels(options, models).ToList();
      return dafnyModels;
    }

    private static IEnumerable<DafnyModel> BuildModels(DafnyOptions options, IEnumerable<Model> modelList) {
      return modelList.Select(model => new DafnyModel(model, options));
    }

    private static List<Model> ExtractModels(string output) {
      const string begin = "*** MODEL";
      const string end = "*** END_MODEL";
      var beginIndex = output.IndexOf(begin, StringComparison.Ordinal);
      var endIndex = output.IndexOf(end, StringComparison.Ordinal);
      if (beginIndex == -1 || endIndex == -1) {
        return [];
      }

      var modelString = output.Substring(beginIndex, endIndex + end.Length - beginIndex);
      var models = Model.ParseModels(new StringReader(modelString));

      return models;
    }

    private CounterExample ConvertModels(List<DafnyModel> specificModels) {
      foreach (var dafnyModel in specificModels) {
        var counterExample = new CounterExample();
        foreach (var state in dafnyModel.States) {
          if (state == null) {
            continue;
          }

          var counterExampleState = new CounterExampleState {
            Name = state.FullStateName
          };
          AddLineInformation(counterExampleState, state.FullStateName);

          var vars = state.ExpandedVariableSet();

          foreach (var variableNode in vars) {
            counterExampleState.Variables.Add(new CounterExampleVariable {
              Name = "",
              Value = variableNode.ToString(),
              // DatatypeConstructorName is same as Value now but keeping this for legacy
              CanonicalName = variableNode.ToString()
            });
          }
          var index = counterExample.States.FindIndex(c => c.Column == counterExampleState.Column && c.Line == counterExampleState.Line);
          if (index != -1) {
            counterExample.States[index] = counterExampleState;
          } else {
            counterExample.States.Add(counterExampleState);
          }
        }
        return counterExample;
      }

      return new CounterExample();
    }

    private static void AddLineInformation(CounterExampleState state, string stateCapturedStateName) {
      if ("<initial>".Equals(stateCapturedStateName)) {
        state.Line = 0;
        state.Column = 0;
        return;
      }

      var regex = ".*?(dfy)(\\()(\\d+)(,)(\\d+)(\\))";
      var r = new Regex(regex, RegexOptions.IgnoreCase | RegexOptions.Singleline);
      var m = r.Match(stateCapturedStateName);
      if (m.Success) {
        var lineStr = m.Groups[3].ToString();
        state.Line = int.Parse(lineStr);
        var columnStr = m.Groups[5].ToString();
        state.Column = int.Parse(columnStr);
      }
    }

    [Serializable]
    [DataContract]
    public class CounterExample {
      [DataMember]
      public List<CounterExampleState> States { get; set; }

      public CounterExample() {
        States = [];
      }
    }

    [Serializable]
    [DataContract]
    public class CounterExampleState {
      [DataMember]
      public List<CounterExampleVariable> Variables { get; set; }
      [DataMember]
      public string Name { get; set; }
      [DataMember]
      public int Line { get; set; }
      [DataMember]
      public int Column { get; set; }
      public CounterExampleState() {
        Variables = [];
      }
    }

    [Serializable]
    [DataContract]
    public class CounterExampleVariable {
      [DataMember]
      public string Name { get; set; }
      [DataMember]
      public string RealName { get; set; }
      [DataMember]
      public string Value { get; set; }
      [DataMember]
      public string CanonicalName { get; set; }
    }
  }


}