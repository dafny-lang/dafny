// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.IO;
using System.Runtime.Serialization;
using System.Text.RegularExpressions;
using DafnyServer.CounterExampleGeneration;
using Microsoft.Boogie;

namespace DafnyServer {
  public class CounterExampleProvider {
    private List<DafnyModel> _dafnyModels;
    public static readonly string ModelBvd = "./model.bvd";

    public CounterExample LoadCounterModel() {
      try {
        var models = LoadModelFromFile();
        return ConvertModels(models);
      } catch (Exception) {
        return new CounterExample();
      }
    }

    private List<DafnyModel> LoadModelFromFile() {
      using (var wr = new StreamReader(ModelBvd)) {
        var output = wr.ReadToEnd();
        var models = ExtractModels(output);
        _dafnyModels = BuildModels(models);
      }
      return _dafnyModels;
    }

    private List<DafnyModel> BuildModels(List<Model> modellist) {
      var list = new List<DafnyModel>();
      foreach (var model in modellist) {
        var specifiedModel = new DafnyModel(model);
        list.Add(specifiedModel);
      }
      return list;
    }

    private List<Model> ExtractModels(string output) {
      const string begin = "*** MODEL";
      const string end = "*** END_MODEL";
      var beginIndex = output.IndexOf(begin, StringComparison.Ordinal);
      var endIndex = output.IndexOf(end, StringComparison.Ordinal);
      if (beginIndex == -1 || endIndex == -1) {
        return new List<Model>();
      }

      var modelString = output.Substring(beginIndex, endIndex + end.Length - beginIndex);
      var models = Model.ParseModels(new StringReader(modelString));

      return models;
    }

    private CounterExample ConvertModels(List<DafnyModel> specificModels) {
      foreach (var dafnyModel in specificModels) {
        var counterExample = new CounterExample();
        foreach (var state in dafnyModel.States) {
          if (state == null) continue;

          var counterExampleState = new CounterExampleState {
            Name = state.FullStateName
          };
          AddLineInformation(counterExampleState, state.FullStateName);

          var vars = state.ExpandedVariableSet(2);

          foreach (var variableNode in vars) {
            counterExampleState.Variables.Add(new CounterExampleVariable {
              Name = variableNode.ShortName,
              Value = variableNode.Value,
              // CanonicalName is same as Value now but keeping this for legacy
              CanonicalName = variableNode.Value
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

    private void AddLineInformation(CounterExampleState state, string stateCapturedStateName) {
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
        States = new List<CounterExampleState>();
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
        Variables = new List<CounterExampleVariable>();
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