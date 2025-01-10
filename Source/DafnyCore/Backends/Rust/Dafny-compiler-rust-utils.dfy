module DafnyCompilerRustUtils {
  import Std
  import opened Std.Wrappers
  import opened DAST
  import R = RAST

  // Split a Dafny name along dots
  function DafnyNameToContainingPathAndName(n: Name, acc: seq<Ident> := []): (seq<Ident>, Name)
    decreases |n.dafny_name|
  {
    var s := n.dafny_name;
    if |s| == 0 then
      if |acc| == 0 then ([], Name("")) else (acc[0..|acc|-1], acc[|acc|-1].id)
    else
    if s[0] != '.' then
      if |acc| == 0 then DafnyNameToContainingPathAndName(Name(s[1..]), [Ident.Ident(Name(s[0..1]))]) else
      DafnyNameToContainingPathAndName(Name(s[1..]), acc[0..|acc|-1] + [Ident.Ident(Name(acc[|acc|-1].id.dafny_name + [s[0]]))])
    else
    if |acc| == 0 then DafnyNameToContainingPathAndName(Name(s[1..]), []) else
    DafnyNameToContainingPathAndName(Name(s[1..]), acc + [Ident.Ident(Name(""))])
  }

  type ModWithBody = x: R.Mod | x.Mod? witness *
  type ExternMod = x: R.Mod | x.ExternMod? witness *

  datatype SeqMap<K, V> = SeqMap(keys: seq<K>, values: map<K, V>)
  {
    static function Empty(): SeqMap<K, V> {
      SeqMap([], map[])
    }
    static function Single(key: K, value: V): SeqMap<K, V> {
      SeqMap([key], map[key := value])
    }
  }

  datatype GatheringModule =
    GatheringModule(
      existingMod: ModWithBody,
      submodules: SeqMap<string, GatheringModule>
    ) |
    ExternMod(m: ExternMod)
  {

    static function MergeSeqMap(m1: SeqMap<string, GatheringModule>, m2: SeqMap<string, GatheringModule>): SeqMap<string, GatheringModule>
      decreases m1
    {
      SeqMap(
        m1.keys + Std.Collections.Seq.Filter((k: string) => k !in m1.keys, m2.keys),
        map k <- m1.values.Keys + m2.values.Keys ::
          if k in m1.values then
            if k in m2.values then m1.values[k].Merge(m2.values[k]) else
            m1.values[k]
          else
            m2.values[k])
    }


    static function MergeSeqMapAll(m1: SeqMap<string, GatheringModule>, m2s: seq<SeqMap<string, GatheringModule>>): SeqMap<string, GatheringModule>
      decreases |m2s|
    {
      if |m2s| == 0 then m1 else
      MergeSeqMapAll(MergeSeqMap(m1, m2s[0]), m2s[1..])
    }

    function Merge(m2: GatheringModule): GatheringModule
      decreases this
    {
      if !GatheringModule? then m2 else if !m2.GatheringModule? then this else
      GatheringModule(
        R.Mod(existingMod.docString + m2.existingMod.docString, existingMod.attributes, existingMod.name, existingMod.body + m2.existingMod.body),
        MergeSeqMap(submodules, m2.submodules)
      )
    }

    static function Wrap(containingPath: seq<string>, rawDecl: R.Mod): SeqMap<string, GatheringModule> {
      if |containingPath| == 0 then
        var name := rawDecl.name;
        if rawDecl.Mod? then
          SeqMap.Single(name, GatheringModule(rawDecl, SeqMap.Empty()))
        else
          SeqMap.Single(name, ExternMod(rawDecl))
      else
        var enclosingModule := containingPath[0];
        SeqMap.Single(enclosingModule,
                      GatheringModule(R.Mod("", [], enclosingModule, []), Wrap(containingPath[1..], rawDecl)))
    }
    function ToRust(): R.Mod {
      if ExternMod? then m else
      var keysWithContent := Std.Collections.Seq.Filter(key => key in submodules.values, submodules.keys);
      existingMod.(body :=
      existingMod.body +
      seq(|keysWithContent|, i requires 0 <= i < |keysWithContent| =>
        var moduleName := keysWithContent[i];
        var submodule := submodules.values[moduleName].ToRust();
        R.ModDecl(submodule)
        )
      )
    }
  }

}