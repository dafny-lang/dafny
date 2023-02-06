using System;
using System.Collections.Concurrent;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Plugins;
using Newtonsoft.Json.Linq;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;
using static Microsoft.Dafny.ErrorDetail;

namespace Microsoft.Dafny.LanguageServer.Handlers;

public class DafnyCodeActions {

  private static Dictionary<ErrorID, Func<Diagnostic, Range, List<DafnyCodeAction>>> codeActionMap =
    new Dictionary<ErrorID, Func<Diagnostic, Range, List<DafnyCodeAction>>>();

  public static Func<Diagnostic, Range, List<DafnyCodeAction>>? GetAction(ErrorID errorId) {
    init();
    return codeActionMap.ContainsKey(errorId) ? codeActionMap[errorId] : null;
  }

  public static List<DafnyCodeAction> ReplacementAction(string title, Diagnostic diagnostic, Range range, string newText) {
    var edit = new DafnyCodeActionEdit[] { new DafnyCodeActionEdit(range, newText) };
    var action = new InstantDafnyCodeAction(title, new List<Diagnostic> { diagnostic }, edit);
    return new List<DafnyCodeAction> { action };
  }

  public static List<DafnyCodeAction> ReplacementActions(Diagnostic diagnostic, Range range, Tuple<String, String>[] data) {
    List<DafnyCodeAction> actions = new List<DafnyCodeAction>();
    foreach (var pair in data) {
      var edit = new DafnyCodeActionEdit[] { new DafnyCodeActionEdit(range, pair.Item2) };
      var action = new InstantDafnyCodeAction(pair.Item1, new List<Diagnostic> { diagnostic }, edit);
      actions.Add(action);
    }
    return actions;
  }

  public static List<DafnyCodeAction> RemoveAction(string title, Diagnostic diagnostic, Range range) {
    var edit = new DafnyCodeActionEdit[] { new DafnyCodeActionEdit(range, "") };
    var action = new InstantDafnyCodeAction(title, new List<Diagnostic> { diagnostic }, edit);
    return new List<DafnyCodeAction> { action };
  }


  public static void AddRemoveAction(ErrorID errorID, String title) {
    codeActionMap.Add(errorID, (Diagnostic diagnostic, Range range) => RemoveAction(title, diagnostic, range));
  }

  public static void AddReplaceAction(ErrorID errorID, String title, String newContent) {
    codeActionMap.Add(errorID, (Diagnostic diagnostic, Range range) => ReplacementAction(title, diagnostic, range, newContent));
  }

  public static void AddReplacementActions(ErrorID errorID, Tuple<String, String>[] actions) {
    codeActionMap.Add(errorID, (Diagnostic diagnostic, Range range) => ReplacementActions(diagnostic, range, actions));
  }

  private static bool initialized = false;
  public static void init() {
    if (initialized) {
      return;
    }
    initialized = true;
    AddRemoveAction(ErrorID.p_duplicate_modifier, "remove duplicate modifier'");
    AddRemoveAction(ErrorID.p_abstract_not_allowed, "remove 'abstract'");
    AddRemoveAction(ErrorID.p_no_ghost_for_by_method, "remove 'ghost'");
    AddRemoveAction(ErrorID.p_ghost_forbidden_default, "remove 'ghost'");
    AddRemoveAction(ErrorID.p_ghost_forbidden, "remove 'ghost'");
    AddRemoveAction(ErrorID.p_no_static, "remove 'static'");
    AddRemoveAction(ErrorID.p_deprecated_attribute, "remove attribute");
    AddReplaceAction(ErrorID.p_literal_string_required, "replace with empty string", "\"\"");
    AddRemoveAction(ErrorID.p_no_leading_underscore, "remove underscore");
    // p_bitvector_too_large -- no code action
    // p_array_dimension_too_large -- no code action
    // p_superfluous_exoirt -- TODO - need a code action
    // p_bad_module_decl -- no code action
    AddRemoveAction(ErrorID.p_extraneous_comma_in_export, "remove comma");
    AddReplaceAction(ErrorID.p_top_level_field, "replace 'var' by 'const'", "const"); // also remove entire declaration?
    // p_bad_datatype_refinement -- what code action
    AddReplaceAction(ErrorID.p_no_mutable_fields_in_value_types, "replace 'var' by 'const'", "const");
    AddReplaceAction(ErrorID.p_bad_const_initialize_op, "replace = with :=", ":=");
    // p_const_is_missing_type_or_init -- no code action
    AddRemoveAction(ErrorID.p_output_of_function_not_ghost, "remove 'ghost'");
    AddRemoveAction(ErrorID.p_ghost_function_output_not_ghost, "remove 'ghost'");
    AddRemoveAction(ErrorID.p_no_new_on_output_formals, "remove 'new'");
    AddRemoveAction(ErrorID.p_no_nameonly_on_output_formals, "remove 'nameonly'");
    AddRemoveAction(ErrorID.p_no_older_on_output_formals, "remove 'older'");
    // p_var_decl_must_have_type -- no code action
    // p_no_init_for_var_field -- remove entire initiallizer
    // p_datatype_formal_is_not_id -- no code action - perhaps remove the name and the colon
    AddRemoveAction(ErrorID.p_nameonly_must_have_parameter_name, "remove 'nameonly'");
    AddReplaceAction(ErrorID.p_should_be_yields_instead_of_returns, "replace 'returns' by 'yields'", "yields");
    AddRemoveAction(ErrorID.p_type_parameter_variance_forbidden, "remove type parameter variance");

    AddReplacementActions(ErrorID.p_unexpected_type_characteristic, new Tuple<String, String>[]{
      Tuple.Create("replace with '=='", "=="),
      Tuple.Create("replace with '0'", "0"),
      Tuple.Create("replace with '00'", "00"),
      Tuple.Create("replace with '!new'", "!new")});

    // p_missing_type_characteristic -- need to insert something? or remove comma?

    AddReplacementActions(ErrorID.p_illegal_type_characteristic, new Tuple<String, String>[]{
      Tuple.Create("replace with '=='", "=="),
      Tuple.Create("replace with '0'", "0"),
      Tuple.Create("replace with '00'", "00"),
      Tuple.Create("replace with '!new'", "!new")});

    AddReplaceAction(ErrorID.p_deprecated_colemma, "Replace 'colemma' with 'greatest lemma'", "greatest lemma");
    AddReplaceAction(ErrorID.p_deprecated_inductive_lemma, "Replace 'inductive' with 'least'", "least");
    AddReplaceAction(ErrorID.p_constructor_not_in_class, "replace 'constructor' with 'method'", "method");

    // p_method_missing_name -- insert a name?
    AddRemoveAction(ErrorID.p_extraneous_k, "remove '[type]'");
    // p_constructors_have_no_out_parameters - remove everything from returns through )
    // p_reads_star_must_be_alone -- remove *, remove everything else
    AddRemoveAction(ErrorID.p_no_defaults_for_out_parameters, "remove initializer");
    // p_set_only_one_type_parameter
    // p_iset_only_one_type_parameter
    // p_multiset_only_one_type_parameter
    // p_seq_only_one_type_parameter
    // p_map_needs_two_type_parameters
    // p_imap_needs_two_type_parameters




    AddRemoveAction(ErrorID.p_deprecating_function_method, "remove 'method'");
  }
}


