import Polyfold
/-!
Trusted-base extraction. For each main declaration, collect the project constants in its type,
then close transitively: definitions/instances/opaques → type + value; structures/classes/
inductives → type + constructor types. Ordinary theorems met inside a value are proofs: their
statement is already fixed by the surrounding term (kernel terms carry all implicit arguments),
so they are not followed; auxiliary `proof_n` / `eq_n` theorems are followed (type only).
Stop at non-`Polyfold` modules.
Auxiliary constants (`match_n`, `proof_n`, `eq_n`, `_private`, `casesOn`, projections, ctors, …)
are followed but reported under their parent declaration.
Output: graph.tsv  (node, kind, module, direct deps)  and  mains.tsv  (label, name, kind, deps), in
Exposition/checklist/.  Run from the project folder: `lake env lean Exposition/checklist/TrustedBase.lean`,
then `python3 Exposition/checklist/build_checklist.py`.
-/
open Lean Meta Elab Command

def mains : List (String × String) := [
  ("core|Prop 1.1.11", "proposition_1_1_11"),
  ("core|Thm 1.3.1", "theorem_1_3_1"),
  ("core|Thm 1.3.5", "theorem_1_3_5"),
  ("core|Thm 2.1.15", "theorem_2_1_15"),
  ("core|Thm 2.3.10", "theorem_2_3_10"),
  ("core|Thm 2.3.16", "theorem_2_3_16"),
  ("core|Thm 2.4.12", "theorem_2_4_12"),
  ("core|Thm 2.5.17", "MPolyfold.theorem_2_5_17_interior"),
  ("core|Thm 2.5.17", "MPolyfold.theorem_2_5_17_isSubMPolyfold_face"),
  ("core|Thm 2.5.17", "MPolyfold.theorem_2_5_17_isTame_face"),
  ("core|Thm 3.1.13", "theorem_3_1_13"),
  ("core|Thm 3.1.18", "theorem_3_1_18"),
  ("core|Thm 3.1.21", "theorem_3_1_21"),
  ("core|Thm 3.1.22", "theorem_3_1_22_2021def"),
  ("core|Thm 3.1.26", "theorem_3_1_26_2021def"),
  ("core|Cor 3.1.27", "corollary_3_1_27_2021def"),
  ("core|Thm 3.2.3", "theorem_3_2_3_2021def"),
  ("core|Thm 3.6.8", "theorem_3_6_8_book"),
  ("core|Thm 3.6.10", "theorem_3_6_10_2021def"),
  ("core|Thm 3.6.11", "theorem_3_6_11_2021def"),
  ("core|Thm 4.1.2", "MPolyfold.theorem_4_1_2"),
  ("core|Thm 4.2.7", "MPolyfold.theorem_4_2_7"),
  ("core|Thm 4.2.11", "MPolyfold.theorem_4_2_11"),
  ("core|Thm 4.3.1", "theorem_4_3_1"),
  ("core|Cor 5.2.5", "corollary_5_2_5_2021def"),
  ("core|Thm 5.3.5", "theorem_5_3_5_2021def"),
  ("core|Thm 5.3.10", "theorem_5_3_10_book_2021def"),
  ("core|Thm 5.3.12", "theorem_5_3_12_book_2021def"),
  ("core|Prop 6.2.2", "proposition_6_2_2_interval_2021def"),
  ("core|Thm 5.4.2", "theorem_5_4_2"),
  ("orientation|Thm 6.6.11", "theorem_6_6_11"),
  ("orientation|Thm 6.6.13", "theorem_6_6_13"),
  ("orientation|Thm 6.6.17", "theorem_6_6_17"),
  ("orientation|Thm 6.6.18", "theorem_6_6_18"),
  ("orientation|Thm 6.7.1", "theorem_6_7_1"),
  ("partII|Thm 7.1.13", "EpGroupoid.theorem_7_1_13"),
  ("partII|Thm 7.2.14", "EpGroupoid.theorem_7_2_14"),
  ("partII|Thm 7.3.1", "EpGroupoid.theorem_7_3_1"),
  ("partII|Cor 7.3.6", "EpGroupoid.corollary_7_3_6"),
  ("partII|Thm 7.5.4", "EpGroupoid.theorem_7_5_4"),
  ("partII|Thm 7.5.7", "EpGroupoid.theorem_7_5_7"),
  ("partII|Thm 7.6.1", "EpGroupoid.theorem_7_6_1"),
  ("partII|Thm 8.1.1", "EpGroupoid.theorem_8_1_1"),
  ("partII|Thm 8.1.11", "EpFunctor.theorem_8_1_11"),
  ("partII|Thm 8.1.12", "theorem_8_1_12"),
  ("partII|Thm 8.1.15", "EpGroupoid.theorem_8_1_15"),
  ("partII|Thm 8.5.3", "EpFunctor.theorem_8_5_3"),
  ("partII|Thm 8.5.8", "EpFunctor.theorem_8_5_8"),
  ("partII|Prop 9.1.11", "EpGroupoid.proposition_9_1_11_unique"),
  ("partII|Thm 9.2.1", "EpGroupoid.theorem_9_2_1"),
  ("partII|Thm 9.5.15", "EP.theorem_9_5_15"),
  ("partII|Thm 9.5.15", "EP.theorem_9_5_15_dim1_all"),
  ("partII|Thm 9.5.16", "EP.theorem_9_5_16"),
  ("partII|Thm 9.5.16", "EP.theorem_9_5_16_dim1_all"),
  ("partII|Thm 9.5.17", "EP.theorem_9_5_17"),
  ("partII|Thm 9.5.17", "EP.theorem_9_5_17_dim1"),
  ("partII|Thm 9.5.18", "EP.theorem_9_5_18"),
  ("partII|Thm 9.5.18", "EP.theorem_9_5_18_dim1_isLUC"),
  ("partII|Thm 10.1.7", "EpFunctor.theorem_10_1_7"),
  ("partII|Thm 10.2.2", "WeakFibredProduct.theorem_10_2_2"),
  ("partII|Thm 10.2.2", "WeakFibredProduct.theorem_10_2_2_both"),
  ("partII|Thm 10.3.8", "EPLocalization.Diagram.theorem_10_3_8"),
  ("partII|Thm 10.3.10", "EPLocalization.EPLoc.theorem_10_3_10"),
  ("partII|Thm 10.3.14", "EPLocalization.EPLoc.theorem_10_3_14"),
  ("partII|Thm 10.3.15", "EPLocalization.EPLoc.theorem_10_3_15"),
  ("partII|Thm 10.3.21", "EPLocalization.EPLoc.theorem_10_3_21"),
  ("partII|Thm 10.5.7", "SBLocalization.theorem_10_5_7_of_isEffective"),
  ("partII|Thm 11.1.1", "EPLocalization.EPLoc.theorem_11_1_1"),
  ("partII|Thm 11.3.3", "EPLocalization.EPLoc.theorem_11_3_3_one"),
  ("partII|Thm 11.3.3", "EPLocalization.EPLoc.theorem_11_3_3_two"),
  ("partII|Thm 11.3.3", "EPLocalization.EPLoc.theorem_11_3_3_three"),
  ("partII|Thm 11.3.3", "EPLocalization.EPLoc.theorem_11_3_3_four"),
  ("partII|Thm 11.3.3", "EPLocalization.EPLoc.theorem_11_3_3_five"),
  ("partII|Thm 11.3.3", "EPLocalization.EPLoc.theorem_11_3_3_six"),
  ("partII|Thm 11.3.5", "EPLocalization.EPLoc.theorem_11_3_5_push"),
  ("partII|Thm 11.3.5", "EPLocalization.EPLoc.theorem_11_3_5_pull"),
  ("partII|Thm 11.3.7", "EPLocalization.EPLoc.theorem_11_3_7_push"),
  ("partII|Thm 11.3.7", "EPLocalization.EPLoc.theorem_11_3_7_pull"),
  ("partII|Thm 11.3.8", "EPLocalization.EPLoc.theorem_11_3_8_push"),
  ("partII|Thm 11.3.8", "EPLocalization.EPLoc.theorem_11_3_8_pull"),
  ("partII|Thm 11.3.9", "EPLocalization.EPLoc.theorem_11_3_9_push_boundaryOrientation"),
  ("partII|Thm 11.3.9", "EPLocalization.EPLoc.theorem_11_3_9_pull_boundaryOrientation"),
  ("partII|Thm 11.6.6", "ProperCoveringHom.theorem_11_6_6"),
  ("partIII|Thm 12.2.2", "EpStrongBundle.theorem_12_2_2"),
  ("partIII|Thm 12.4.2", "EpStrongBundle.theorem_12_4_2"),
  ("partIII|Thm 13.1.8", "EpGroupoid.theorem_13_1_8"),
  ("partIII|Prop 16.1.4", "PolyfoldStructure.proposition_16_1_4"),
  ("partIII|Lemma 16.1.13", "PolyfoldStructure.lemma_16_1_13"),
  ("partIII|Lemma 16.1.19", "PolyfoldStructure.lemma_16_1_19"),
  ("partIII|Thm 12.2.7", "EpStrongBundle.theorem_12_2_7"),
  ("partIII|Thm 12.2.11", "EpStrongBundle.theorem_12_2_11"),
  ("partIII|Thm 12.3.9", "EpStrongBundle.theorem_12_3_9"),
  ("partIII|Thm 12.5.7", "theorem_12_5_7_one_hyp"),
  ("partIII|Thm 13.5.6", "SBLocalization.theorem_13_5_6"),
  ("partIII|Thm 15.2.2", "SBLocalization.theorem_15_2_2_hyp"),
  ("partIII|Thm 15.2.5", "SBLocalization.theorem_15_2_5_hyp"),
  ("partIII|Lemma 16.2.2", "PolyfoldClass.lemma_16_2_2"),
  ("partIII|Def 16.2.3", "PolyfoldClass.definition_16_2_3"),
  ("partIII|Thm 16.2.6", "PolyfoldClass.theorem_16_2_6_complex"),
  ("partIII|Thm 16.4.6", "PolyfoldClass.OrientedRep.theorem_16_4_6_hyp"),
  ("partIII|Thm 12.2.13", "EpStrongBundle.theorem_12_2_13"),
  ("partIII|Prop 13.3.19", "SBLocalization.proposition_13_3_19"),
  ("partIII|Thm 13.4.1", "SBLocalization.theorem_13_4_1"),
  ("partIII|Thm 13.4.3", "SBLocalization.theorem_13_4_3"),
  ("partIII|Thm 13.4.4", "SBLocalization.theorem_13_4_4"),
  ("partIII|Thm 13.5.3", "SBLocalization.theorem_13_5_3"),
  ("partIII|Thm 13.5.7", "SBLocalization.theorem_13_5_7"),
  ("partIII|Thm 14.1.6", "EpGroupoid.theorem_14_1_6_hyp"),
  ("partIII|Thm 14.1.9", "SBLocalization.theorem_14_1_9_hyp"),
  ("partIII|Prop 14.4.14", "SBLocalization.proposition_14_4_14"),
  ("partIII|Thm 14.5.5", "SBLocalization.theorem_14_5_5"),
  ("partIII|Thm 15.1.1", "SBLocalization.theorem_15_1_1_functor"),
  ("partIII|Thm 15.3.7", "SBLocalization.theorem_15_3_7_of_hyp"),
  ("partIII|Thm 15.3.9", "SBLocalization.theorem_15_3_9_hyp"),
  ("partIII|Thm 15.4.3", "SBLocalization.theorem_15_4_3_hyp"),
  ("partIII|Cor 15.4.4", "SBLocalization.corollary_15_4_4_hyp"),
  ("partIII|Thm 16.2.4", "PolyfoldClass.theorem_16_2_4"),
  ("partIII|Thm 16.3.15", "StrongPolyfoldBundle.theorem_16_3_15_one"),
  ("partIII|Thm 16.3.17", "StrongPolyfoldBundle.theorem_16_3_17_one"),
  ("partIII|Thm 16.5.7", "StrongPolyfoldBundle.theorem_16_5_7_hyp"),
  ("partIII|Thm 16.6.4", "StrongPolyfoldBundle.theorem_16_6_4"),
  ("tame|Thm 2.7.13", "MPolyfold.theorem_2_7_13_book"),
  ("tame|Thm 7.6.9", "EpGroupoid.theorem_7_6_9_book")]

def isDigits (s : String) : Bool := !s.isEmpty && s.all Char.isDigit

def auxComp : Name → Bool
  | .str _ s => s.startsWith "_" ||
      (s.startsWith "match_" && isDigits (s.drop 6).toString) ||
      (s.startsWith "proof_" && isDigits (s.drop 6).toString) ||
      (s.startsWith "eq_" && isDigits (s.drop 3).toString) ||
      ["eq_def", "brecOn", "below", "binductionOn", "ibelow", "casesOn", "recOn", "rec",
       "noConfusion", "noConfusionType", "ctorIdx", "inj", "injEq", "sizeOf_spec"].contains s
  | .num .. => true
  | .anonymous => false

def isProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!.getRoot == `Polyfold
  | none => false

/-- The declaration a constant is reported under. -/
def parentOf (env : Environment) (n : Name) : Name := Id.run do
  let n := privateToUserName n
  let cs := n.components
  let n' := match cs.findIdx? auxComp with
    | some i => Name.fromComponents (cs.take i)
    | none => n
  match env.find? n' with
  | some (.ctorInfo c) => return c.induct
  | some (.recInfo _) => return n'.getPrefix
  | _ =>
    match env.getProjectionFnInfo? n' with
    | some p => match env.find? p.ctorName with
      | some (.ctorInfo c) => return c.induct
      | _ => return n'
    | none => return n'

def directDeps (env : Environment) (n : Name) : NameSet :=
  match env.find? n with
  | some (.defnInfo d) => d.type.getUsedConstantsAsSet ∪ d.value.getUsedConstantsAsSet
  | some (.opaqueInfo d) => d.type.getUsedConstantsAsSet ∪ d.value.getUsedConstantsAsSet
  | some (.thmInfo d) => d.type.getUsedConstantsAsSet
  | some (.axiomInfo d) => d.type.getUsedConstantsAsSet
  | some (.inductInfo i) => i.ctors.foldl (fun s c => match env.find? c with
      | some ci => s ∪ ci.type.getUsedConstantsAsSet | none => s) i.type.getUsedConstantsAsSet
  | some (.ctorInfo c) => c.type.getUsedConstantsAsSet.insert c.induct
  | some (.recInfo r) => ({} : NameSet).insert r.getMajorInduct
  | _ => {}

/-- Project constants we follow: everything except ordinary (non-auxiliary) theorems. -/
def follow (env : Environment) (d : Name) : Bool :=
  isProject env d && (!(env.find? d matches some (.thmInfo _)) || parentOf env d != d)

def kindOf (env : Environment) (n : Name) : String :=
  match env.find? n with
  | some (.defnInfo d) =>
    if isInstanceCore env n then "instance"
    else if d.hints matches .abbrev then "abbrev" else "def"
  | some (.inductInfo _) =>
    if isClass env n then "class" else if isStructure env n then "structure" else "inductive"
  | some (.thmInfo _) => "theorem"
  | some (.opaqueInfo _) => "opaque"
  | some (.axiomInfo _) => "axiom"
  | some _ => "other"
  | none => "missing"

#eval show CommandElabM Unit from do
  let env ← getEnv
  let out := "Exposition/checklist/"
  let mut work : Array Name := #[]
  let mut mainLines : Array String := #[]
  for (lab, s) in mains do
    let n := `Polyfold ++ s.toName
    match env.find? n with
    | none => logWarning m!"missing main {n}"
    | some ci =>
      let ds := ci.type.getUsedConstantsAsSet.toList.filter (follow env)
      work := work ++ ds.toArray
      let ps := (ds.map (parentOf env)).eraseDups.filter (· != n)
      mainLines := mainLines.push
        s!"{lab}\t{n}\t{kindOf env n}\t{env.header.moduleNames[(env.getModuleIdxFor? n).get!.toNat]!}\t{" ".intercalate (ps.map toString)}"
  -- BFS over raw constants; edges between parents
  let mut seen : NameSet := {}
  let mut edges : Std.HashMap Name NameSet := {}
  while !work.isEmpty do
    let r := work.back!
    work := work.pop
    if seen.contains r then continue
    seen := seen.insert r
    let p := parentOf env r
    if !seen.contains p then work := work.push p
    let mut es := edges.getD p {}
    for d in (directDeps env r).toList do
      if follow env d then
        let q := parentOf env d
        if q != p then es := es.insert q
        if !seen.contains d then work := work.push d
    edges := edges.insert p es
  let mut lines : Array String := #[]
  for (p, es) in edges.toList do
    let m := match env.getModuleIdxFor? p with
      | some i => env.header.moduleNames[i.toNat]!.toString | none => "?"
    lines := lines.push s!"{p}\t{kindOf env p}\t{m}\t{" ".intercalate (es.toList.map toString)}"
  IO.FS.writeFile (out ++ "graph.tsv") ("\n".intercalate lines.toList ++ "\n")
  IO.FS.writeFile (out ++ "mains.tsv") ("\n".intercalate mainLines.toList ++ "\n")
  logInfo m!"mains {mainLines.size}, raw constants {seen.size}, nodes {edges.size}"
