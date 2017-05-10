using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Runtime.Serialization;
using System.Runtime.Serialization.Json;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.ModelViewer;
using Microsoft.Boogie.ModelViewer.Dafny;
using Microsoft.Dafny;
using Program = Microsoft.Boogie.Program;

namespace DafnyServer
{
    public class CounterExampleProvider
    {
        private List<ILanguageSpecificModel> _languageSpecificModels;

        public void LoadModel(Program boogieProgram)
        {
            if (boogieProgram.Resolve() == 0 && boogieProgram.Typecheck() == 0)
            {
                //FIXME ResolveAndTypecheck?
                ExecutionEngine.EliminateDeadVariables(boogieProgram);
                ExecutionEngine.CollectModSets(boogieProgram);
                ExecutionEngine.CoalesceBlocks(boogieProgram);
                ExecutionEngine.Inline(boogieProgram);

                var realConsoleOut = Console.Out;
                using (var writer = new StringWriter())
                {
                    Console.SetOut(writer);

                    //NOTE: We could capture errors instead of printing them (pass a delegate instead of null)
                    ExecutionEngine.InferAndVerify(boogieProgram, new PipelineStatistics(), "ServerProgram", null,
                    DateTime.UtcNow.Ticks.ToString());
                    writer.Flush();

                    var output = writer.GetStringBuilder().ToString();
                    Console.SetOut(realConsoleOut);
                    Console.WriteLine(output);

                    var models = ExtractModels(output);
                    _languageSpecificModels = BuildModels(models);
                    
                }
            }
        }


        public string ToJson()
        {
            return ConvertModels(_languageSpecificModels);
        } 

        private List<ILanguageSpecificModel> BuildModels(List<Model> modellist)
        {
            var list = new List<ILanguageSpecificModel>();
            foreach (var model in modellist)
            {
                var specifiedModel = Provider.Instance.GetLanguageSpecificModel(model, new ViewOptions() { DebugMode = true });
                list.Add(specifiedModel);
            }
            return list;
        }

        private List<Model> ExtractModels(string output)
        {
            const string begin = "*** MODEL";
            const string end = "*** END_MODEL";
            var beginIndex = output.IndexOf(begin, StringComparison.Ordinal);
            var endIndex = output.IndexOf(end, StringComparison.Ordinal);
            if (beginIndex == -1 || endIndex == -1)
            {
                return new List<Model>();
            }

            var modelString = output.Substring(beginIndex, endIndex + end.Length - beginIndex);
            var models = Model.ParseModels(new StringReader(modelString));

            return models;
        }
        
        private string ConvertModels(List<ILanguageSpecificModel> specificModels)
        {
            //TODO list of models
            foreach (var languageSpecificModel in specificModels)
            {
                var counterExample = new CounterExample();
                foreach (var s in languageSpecificModel.States)
                {
                    var state = s as Microsoft.Boogie.ModelViewer.Dafny.StateNode;

                    var counterExampleState = new CounterExampleState
                    {
                        Name = state.CapturedStateName
                    };
                    AddLineInformation(counterExampleState, state.CapturedStateName);
                    
                    foreach (var variableNode in state.Vars)
                    {
                        counterExampleState.Variables.Add(new CounterExampleVariable
                        {
                            RealName = variableNode.realName,
                            Name = variableNode.ShortName,
                            Value = variableNode.Value,
                            CanonicalName = languageSpecificModel.CanonicalName(variableNode.Element)
                        });
                    }
                    counterExample.States.Add(counterExampleState);
                }
                return ConvertToJson(counterExample);
            }

            return ConvertToJson(new CounterExample());
        }

        private void AddLineInformation(CounterExampleState state, string stateCapturedStateName)
        {
            if ("<initial>".Equals(stateCapturedStateName))
            {
                state.Line = 0;
                state.Column = 0;
                return;
            }

            var regex = ".*?(dfy)(\\()(\\d+)(,)(\\d+)(\\))"; 
            var r = new Regex(regex, RegexOptions.IgnoreCase | RegexOptions.Singleline);
            var m = r.Match(stateCapturedStateName);
            if (m.Success)
            {
                var lineStr = m.Groups[3].ToString();
                state.Line = Int32.Parse(lineStr);
                var columnStr = m.Groups[5].ToString();
                state.Column = Int32.Parse(columnStr);
            }
        }
        
        private static string ConvertToJson<T>(T data)
        {
            var serializer = new DataContractJsonSerializer(typeof(T));
            using (var ms = new MemoryStream())
            {
                serializer.WriteObject(ms, data);
                return Encoding.Default.GetString(ms.ToArray());
            }
        }

        [Serializable]
        [DataContract]
        class CounterExample
        {
          [DataMember]
            public List<CounterExampleState> States { get; }

          public CounterExample()
            {
                States = new List<CounterExampleState>();
            }
        }

        [Serializable]
        [DataContract]
        class CounterExampleState
        {
          [DataMember]
            public List<CounterExampleVariable> Variables { get; }

          [DataMember]
            public string Name { get; set; }
            [DataMember]
            public int Line { get; set; }
            [DataMember]
            public int Column { get; set; }
            public CounterExampleState()
            {
                Variables = new List<CounterExampleVariable>();
            }
        }

        [Serializable]
        [DataContract]
        class CounterExampleVariable
        {
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
