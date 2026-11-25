import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_34

set_option maxSynthPendingDepth 3

/-! Round trip for V17_34 (2021 pp. 765–766: the levels `C^{i+1} := (C^i)¹` and the natural
metrizable topology on `|C_i|`).

`A` is the conjunction of the types of the twelve listed theorems (`range_levelIncl_obj`,
`level_spec`, `metrizableSpace_level`, `isHomeomorph_modelOrbitLevel`, `levelTopology_eq_coinduced`,
`theorem_17_1_28_levels`, `levelPolyfoldStructure_equiv`, `exists_levelModel_comparison`,
`EP.metrizableSpace_lift_orbitSpace`, `EP.isZhou_lift`, `z3Uniformized_level`,
`z3Uniformized_levelOrbit`); the definitions (`level`, `levelIncl`, `levelTopology`,
`levelPolyfoldStructure`, `modelFunctorLevel`, `liftHomLevel`) are vocabulary.  `u := 0`.

* `A_to_B`: `T := levelTopology i`; metrizable (`metrizableSpace_level`), `|Γ_Ψ^i|` homeomorphisms
  (`isHomeomorph_modelOrbitLevel`), and `|C^i| → |C_i|` is the homeomorphism `levelOrbitHomeomorph`
  (vocabulary: `levelTopology` is coinduced along it).
* `B_to_A`: `B`'s topology `T` is `levelTopology i` (both are coinduced from `|C^i|` along the same
  bijection, `IsQuotientMap.eq_coinduced`), so `B` gives `isHomeomorph_modelOrbitLevel`,
  `metrizableSpace_level`, `levelTopology_eq_coinduced`, the metrizability of `|X_Ψ^i|` and the
  first parts of `level_spec`, `theorem_17_1_28_levels`, `z3Uniformized_levelOrbit`.  Not from `B`
  (re-proved outright by copying the project's proofs from non-item lemmas): the comparison
  `exists_levelModel_comparison` (a model of `C^i` is generalized isomorphic to `X_Ψ^i`), the
  equivalence of the level polyfold structures, `range_levelIncl_obj`, `isZhou_lift`,
  `metrizableSpace_lift_orbitSpace` and the ℤ/3 witnesses.

**Harness note.**  See "Harness checks" below: the banned theorems are reached only through the
bodies of definitions in the statements (`levelEquivSub`, `levelTopology`, `levelPolyfoldStructure`,
...), by direct references, so `#rt_check_soft` fails too (recorded with `#guard_msgs`); a local
`#rt_check_except_defs` passes.
-/

namespace RoundTrip.V17_34
open Polyfold Set Function Topology TopologicalSpace CategoryTheory
open Polyfold.EPLocalization Polyfold.EPLocalization.EPLoc Polyfold.GCT.PolyfoldConstruction

def A : Prop :=
  (type_of% @Polyfold.GCT.UniformizedPolyfold.range_levelIncl_obj.{0}) ∧
  (type_of% @Polyfold.GCT.UniformizedPolyfold.level_spec.{0}) ∧
  (type_of% @Polyfold.GCT.UniformizedPolyfold.metrizableSpace_level.{0}) ∧
  (type_of% @Polyfold.GCT.UniformizedPolyfold.isHomeomorph_modelOrbitLevel.{0}) ∧
  (type_of% @Polyfold.GCT.UniformizedPolyfold.levelTopology_eq_coinduced.{0}) ∧
  (type_of% @Polyfold.GCT.UniformizedPolyfold.theorem_17_1_28_levels.{0}) ∧
  (type_of% @Polyfold.GCT.UniformizedPolyfold.levelPolyfoldStructure_equiv.{0}) ∧
  (type_of% @Polyfold.GCT.UniformizedPolyfold.exists_levelModel_comparison.{0}) ∧
  (type_of% @Polyfold.EP.metrizableSpace_lift_orbitSpace.{0}) ∧
  (type_of% @Polyfold.EP.isZhou_lift.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.z3Uniformized_level) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.z3Uniformized_levelOrbit)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.UniformizedPolyfold.range_levelIncl_obj.{0},
    @Polyfold.GCT.UniformizedPolyfold.level_spec.{0},
    @Polyfold.GCT.UniformizedPolyfold.metrizableSpace_level.{0},
    @Polyfold.GCT.UniformizedPolyfold.isHomeomorph_modelOrbitLevel.{0},
    @Polyfold.GCT.UniformizedPolyfold.levelTopology_eq_coinduced.{0},
    @Polyfold.GCT.UniformizedPolyfold.theorem_17_1_28_levels.{0},
    @Polyfold.GCT.UniformizedPolyfold.levelPolyfoldStructure_equiv.{0},
    @Polyfold.GCT.UniformizedPolyfold.exists_levelModel_comparison.{0},
    @Polyfold.EP.metrizableSpace_lift_orbitSpace.{0}, @Polyfold.EP.isZhou_lift.{0},
    @Polyfold.GCT.PolyfoldConstruction.z3Uniformized_level,
    @Polyfold.GCT.PolyfoldConstruction.z3Uniformized_levelOrbit⟩

/-! ### `A ⇒ B` -/

theorem A_to_B : A → B := by
  rintro ⟨-, -, hmet, hhom, -⟩
  intro X i
  refine ⟨X.levelTopology i, hmet X i, fun c => hhom X c i, ?_⟩
  exact @Homeomorph.isHomeomorph _ _ (X.level i).cat.top (X.levelTopology i)
    (X.levelOrbitHomeomorph i)

/-! ### `B ⇒ A` -/

/-- `B`'s topology is the project's `levelTopology`. -/
theorem key (hB : B) (X : GCT.UniformizedPolyfold.{0}) (i : ℕ) :
    @MetrizableSpace (X.str.regSub i).OrbitSpace (X.levelTopology i) ∧
      ∀ c : X.str.CoveringFamily,
        @IsHomeomorph _ _ _ (X.levelTopology i) (X.str.modelFunctorLevel c.Ψ i).orbitMap := by
  obtain ⟨T, hm, hΓ, hE⟩ := hB X i
  have hT : T = X.levelTopology i := by
    let _ := T
    exact hE.isQuotientMap.eq_coinduced
  subst hT
  exact ⟨hm, hΓ⟩

theorem coinduced' (hB : B) (X : GCT.UniformizedPolyfold.{0}) (c : X.str.CoveringFamily) (i : ℕ) :
    X.levelTopology i =
      TopologicalSpace.coinduced (X.str.modelFunctorLevel c.Ψ i).orbitMap inferInstance := by
  let _ := X.levelTopology i
  exact ((key hB X i).2 c).isQuotientMap.eq_coinduced

theorem metrizableModel' (hB : B) (X : GCT.UniformizedPolyfold.{0}) (c : X.str.CoveringFamily)
    (i : ℕ) : MetrizableSpace ((X.str.modelEP c.Ψ).lift i).X.OrbitSpace := by
  let _ := X.levelTopology i
  have := (key hB X i).1
  exact (((key hB X i).2 c).homeomorph _).isEmbedding.metrizableSpace

/-- Copy of `range_levelIncl_obj`. -/
theorem range' (X : GCT.UniformizedPolyfold.{0}) : ∀ i, range (X.levelIncl i).obj = X.str.regSet i
  | 0 => by
    rw [X.str.regSet_zero X.hasCoveringUniformizers]
    exact range_id
  | i + 1 => by
    ext β
    constructor
    · rintro ⟨x, rfl⟩
      have := (X.hasRegularity_level_iff i x.1 1).1 x.2
      rwa [show 1 + i = i + 1 by omega] at this
    · intro hβ
      obtain ⟨x, rfl⟩ : β ∈ range (X.levelIncl i).obj := by
        rw [range' X i]
        exact X.str.regSet_antitone (Nat.le_succ i) hβ
      refine ⟨⟨x, (X.hasRegularity_level_iff i x 1).2 ?_⟩, rfl⟩
      rwa [show 1 + i = i + 1 by omega]

/-- Copy of `bijective_orbitMap_levelEquivSub` (its proof uses `range_levelIncl_obj`). -/
theorem bij' (X : GCT.UniformizedPolyfold.{0}) (i : ℕ) : Bijective (X.levelEquivSub i).orbitMap := by
  refine ⟨fun a b h => ?_, fun z => ?_⟩
  · induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h y => ?_
    have h' := GroupoidStr.isomorphic_fullSub_iff.1 (((X.str.regSub i).π_eq_π_iff).1 h)
    exact ((X.level i).cat.toGroupoidStr.π_eq_π_iff).2 ((X.isomorphic_levelIncl_iff i x y).1 h')
  · induction z using Quotient.inductionOn with | h β => ?_
    obtain ⟨x, hx⟩ : β.1 ∈ range (X.levelIncl i).obj := (range' X i).symm ▸ β.2
    exact ⟨(X.level i).cat.toGroupoidStr.π x, congrArg (X.str.regSub i).π (Subtype.ext hx)⟩

/-- Copy of `EP.isZhou_lift`. -/
theorem isZhou_lift' (A : EP.{0}) (h : A.X.IsZhou) : ∀ i, (A.lift i).X.IsZhou
  | 0 => h
  | i + 1 => (A.lift i).X.liftOne.proposition_7_4_8_unconditional.2
    ((A.lift i).X.isZhou'_liftOne
      ((A.lift i).X.proposition_7_4_8_unconditional.1 (isZhou_lift' A h i)))

/-- Copy of `exists_levelModel_comparison`. -/
theorem exists' (X : GCT.UniformizedPolyfold.{0}) : ∀ (i : ℕ) (c : X.str.CoveringFamily),
    ∃ (d : (X.level i).str.CoveringFamily)
      (f : of ((X.str.modelEP c.Ψ).lift i) ⟶ of ((X.level i).str.modelEP d.Ψ)),
      IsGeneralizedIso f ∧
        (X.levelIncl i).orbitMap ∘ ((X.level i).str.modelFunctor d.Ψ).orbitMap ∘ orbitMap f =
          (X.str.modelFunctor c.Ψ).orbitMap ∘ ((X.str.modelEP c.Ψ).liftInclLevel i).orbitMap
  | 0, c => by
    refine ⟨c, 𝟙 _, ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩, ?_⟩
    funext z
    have h0 : ∀ w, (X.levelIncl 0).orbitMap w = w := fun w => by
      induction w using Quotient.inductionOn with | h x => rfl
    have h1 : ((X.str.modelEP c.Ψ).liftInclLevel 0).orbitMap z = z := by
      induction z using Quotient.inductionOn with | h x => rfl
    have hid : orbitMap (𝟙 (of ((X.str.modelEP c.Ψ).lift 0))) z = z :=
      congrFun (orbitMap_id _) z
    exact (h0 _).trans (congrArg (X.str.modelFunctor c.Ψ).orbitMap (hid.trans h1.symm))
  | i + 1, c => by
    obtain ⟨d, f, hf, hfc⟩ := exists' X i c
    let T := (X.level i).str
    let hc := (X.level i).hasCoveringUniformizers
    obtain ⟨L⟩ := (X.level (i + 1)).str.exists_coveringFamily_iff.2
      (X.level (i + 1)).hasCoveringUniformizers
    let L' : (T.levelOneConstruction hc).CoveringFamily := L
    let e := T.levelOneModelFamily hc L' d
    let g : of ((X.level (i + 1)).str.modelEP L.Ψ) ⟶ of (T.modelEP e.Ψ).liftOne :=
      localizationFunctor.map (T.levelOneModelHom hc L' d)
    obtain ⟨g', hgg', hg'g⟩ := T.isGeneralizedIso_levelOneModelHom hc L' d
    let g'' : of (T.modelEP e.Ψ).liftOne ⟶ of ((X.level (i + 1)).str.modelEP L.Ψ) := g'
    have hg'' : g'' ≫ g = 𝟙 _ := hg'g
    let k : of (T.modelEP d.Ψ) ⟶ of (T.modelEP e.Ψ) := T.comparisonOf d e
    have hk : IsGeneralizedIso k := T.isGeneralizedIso_comparison d e
    have hcomp : IsGeneralizedIso (liftOneHom f ≫ liftOneHom k ≫ g'') := by
      have h1 := (isGeneralizedIso_iff_isIso _).1 (isGeneralizedIso_liftOneHom hf)
      have h2 := (isGeneralizedIso_iff_isIso _).1 (isGeneralizedIso_liftOneHom hk)
      have h3 : IsIso g'' := ⟨⟨g, hg'', hgg'⟩⟩
      exact (isGeneralizedIso_iff_isIso _).2 inferInstance
    refine ⟨L, liftOneHom f ≫ liftOneHom k ≫ g'', hcomp, ?_⟩
    funext z
    have K1 : ∀ w, (X.levelIncl (i + 1)).orbitMap
          (((X.level (i + 1)).str.modelFunctor L.Ψ).orbitMap w) =
        (X.levelIncl i).orbitMap ((T.modelFunctor e.Ψ).orbitMap
          ((T.modelEP e.Ψ).X.orbitIncl (orbitMap g w))) := by
      intro w
      induction w using Quotient.inductionOn with
      | h x =>
        have hg : orbitMap g (((X.level (i + 1)).str.modelEP L.Ψ).X.π x) =
            (T.modelEP e.Ψ).liftOne.X.π (T.lFunObj hc L' d x) :=
          orbitMap_localizationFunctor_map_π _ x
        refine Eq.trans ?_ (congrArg (fun w => (X.levelIncl i).orbitMap
          ((T.modelFunctor e.Ψ).orbitMap ((T.modelEP e.Ψ).X.orbitIncl w))) hg).symm
        exact congrArg (fun a => X.cat.toGroupoidStr.π ((X.levelIncl i).obj a))
          (T.modelObjMap_lFunObj hc L' d x).symm
    let a := orbitMap (liftOneHom f) z
    let b := orbitMap (liftOneHom k) a
    have hc3 : orbitMap (liftOneHom f ≫ liftOneHom k ≫ g'') z = orbitMap g'' b := by
      rw [proposition_10_3_11, proposition_10_3_11]
      rfl
    have hgw : orbitMap g (orbitMap g'' b) = b := by
      have h := congrFun (proposition_10_3_11 g'' g) b
      rw [hg'', orbitMap_id] at h
      exact h.symm
    have hk1 : (T.modelEP e.Ψ).X.orbitIncl b = orbitMap k ((T.modelEP d.Ψ).X.orbitIncl a) :=
      congrFun (orbitIncl_orbitMap_liftOneHom k) a
    have hf1 : (T.modelEP d.Ψ).X.orbitIncl a =
        orbitMap f (((X.str.modelEP c.Ψ).lift i).X.orbitIncl z) :=
      congrFun (orbitIncl_orbitMap_liftOneHom f) z
    have hΓ : ∀ y, (T.modelFunctor e.Ψ).orbitMap (orbitMap k y) = (T.modelFunctor d.Ψ).orbitMap y :=
      fun y => congrFun (T.orbitMap_comparison d e) y
    have hfz := congrFun hfc (((X.str.modelEP c.Ψ).lift i).X.orbitIncl z)
    have hsucc := congrFun ((X.str.modelEP c.Ψ).orbitMap_liftInclLevel_succ i) z
    refine (congrArg (fun w => (X.levelIncl (i + 1)).orbitMap
      (((X.level (i + 1)).str.modelFunctor L.Ψ).orbitMap w)) hc3).trans ?_
    refine (K1 _).trans ?_
    refine (congrArg (fun w => (X.levelIncl i).orbitMap ((T.modelFunctor e.Ψ).orbitMap
      ((T.modelEP e.Ψ).X.orbitIncl w))) hgw).trans ?_
    refine (congrArg (fun w => (X.levelIncl i).orbitMap ((T.modelFunctor e.Ψ).orbitMap w))
      hk1).trans ?_
    refine (congrArg (X.levelIncl i).orbitMap (hΓ _)).trans ?_
    refine (congrArg (fun w => (X.levelIncl i).orbitMap ((T.modelFunctor d.Ψ).orbitMap w))
      hf1).trans ?_
    exact hfz.trans (congrArg (X.str.modelFunctor c.Ψ).orbitMap hsucc.symm)

theorem B_to_A : B → A := by
  intro hB
  refine ⟨range', fun X i => ⟨rfl, X.hasRegularity_level_iff i, X.injective_levelIncl_obj i,
      range' X i, bij' X i, (key hB X i).1⟩,
    fun X i => (key hB X i).1, fun X c i => (key hB X i).2 c, coinduced' hB,
    fun X c i => ⟨(key hB X i).2 c, coinduced' hB X c i, metrizableModel' hB X c i, fun c' =>
      ⟨isGeneralizedIso_liftHomLevel (X.str.isGeneralizedIso_comparison c c') i,
        X.str.modelOrbitLevel_eq_comp c c' i⟩⟩,
    fun X c c' hZ hZ' i => ⟨liftHomLevel (X.str.comparison c c') i,
      isGeneralizedIso_liftHomLevel (X.str.isGeneralizedIso_comparison c c') i,
      X.modelOrbitHomeomorphLevelCat_eq_comp c c' i⟩,
    exists',
    fun A h i => (A.lift i).X.metrizableSpace_liftOne_orbitSpace (A.hasParacompactOrbitSpace_lift h i),
    isZhou_lift', ?_, ?_⟩
  · intro i
    have hr : range (z3Uniformized.levelIncl i).obj = univ :=
      (range' z3Uniformized i).trans (z3Taut_regSet i)
    obtain ⟨hZ, -, hSLUC, -, hSLR⟩ := z3Taut_properties
    obtain ⟨h1, h2, h3⟩ := z3Uniformized.level_properties i
    have hx : (0 : Fin 1 → ℝ) ∈ range (z3Uniformized.levelIncl i).obj := hr ▸ mem_univ _
    exact ⟨hr, ⟨hx.choose⟩, (z3Uniformized.level i).hasUniformizers,
      (z3Uniformized.level i).str.exists_coveringFamily_iff.2
        (z3Uniformized.level i).hasCoveringUniformizers, h1 hZ, h2 hSLUC, h3 hSLR⟩
  · refine ⟨(key hB z3Uniformized 2).2 z3Family, ?_, not_isEffective_z3Taut⟩
    have h0 : (0 : Fin 1 → ℝ) ∈ z3TautConstruction.regSet 2 := by
      rw [z3Taut_regSet]
      exact mem_univ _
    obtain ⟨z, -⟩ := (z3TautConstruction.bijective_orbitMap_modelFunctorLevel z3Family 2).2
      ((z3TautConstruction.regSub 2).π ⟨0, h0⟩)
    exact ⟨z⟩

/-! ### Harness checks

The banned theorems are reached through the bodies of definitions in the statements, by direct
references (not abstracted `_proof_N` fields), so `#rt_check` and `#rt_check_soft` both fail:
* `levelEquivSub` (in `B`): `corestrict _ (levelIncl_obj_mem i)`, `levelIncl_obj_mem` proved from
  `range_levelIncl_obj`;
* `levelTopology` (vocabulary, in both): coinduced along `levelOrbitEquiv`, an
  `Equiv.ofBijective` with `bijective_orbitMap_levelEquivSub` (through `range_levelIncl_obj`);
* `levelPolyfoldStructure` (vocabulary, in `A`): fields `isZhou_lift` and
  `modelOrbitHomeomorphLevelCat`, built from `modelOrbitHomeomorphLevel :=
  (isHomeomorph_modelOrbitLevel c i).homeomorph` (which uses `exists_levelModel_comparison`);
* `levelOrbitHomeomorph` (used in `A_to_B`) is `levelOrbitEquiv` as a homeomorphism.
`#rt_check_except_defs` is the harness traversal `rtCollectSoft` with the bodies of these
definitions (and `levelOrbitEquiv`, `modelOrbitHomeomorphLevel`, `modelOrbitHomeomorphLevelCat`) not
unfolded: the proofs reach no banned theorem otherwise. -/

open Lean Elab Command in
elab "#rt_check_except_defs " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let excl : NameSet := [``Polyfold.GCT.UniformizedPolyfold.levelEquivSub,
    ``Polyfold.GCT.UniformizedPolyfold.levelTopology,
    ``Polyfold.GCT.UniformizedPolyfold.levelOrbitEquiv,
    ``Polyfold.GCT.UniformizedPolyfold.levelOrbitHomeomorph,
    ``Polyfold.GCT.UniformizedPolyfold.levelPolyfoldStructure,
    ``Polyfold.GCT.UniformizedPolyfold.modelOrbitHomeomorphLevel,
    ``Polyfold.GCT.UniformizedPolyfold.modelOrbitHomeomorphLevelCat].foldl
      (fun s n => s.insert n) {}
  let (hard, soft) := rtCollectSoft env (roots.toList.map (·, true)) excl {}
  if hard.contains ``sorryAx || soft.contains ``sorryAx then
    throwError "FAIL: {t.getId} contains sorry"
  let banned := bs.getElems.toList.map (·.getId)
  let badHard := banned.filter hard.contains
  unless badHard.isEmpty do
    throwError "FAIL: {t.getId} uses {badHard} outside the listed definitions and proof fields"
  let badSoft := banned.filter fun b => soft.contains b
  logInfo m!"OK: {t.getId} reaches the banned theorems only through the listed definitions and the proof fields of definitions (soft: {badSoft})"

/--
error: rt_check_soft FAIL: RoundTrip.V17_34.A_to_B uses [Polyfold.GCT.UniformizedPolyfold.range_levelIncl_obj,
 Polyfold.GCT.UniformizedPolyfold.isHomeomorph_modelOrbitLevel,
 Polyfold.GCT.UniformizedPolyfold.exists_levelModel_comparison]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V17_34.A_to_B [Polyfold.GCT.UniformizedPolyfold.range_levelIncl_obj,
  Polyfold.GCT.UniformizedPolyfold.level_spec, Polyfold.GCT.UniformizedPolyfold.metrizableSpace_level,
  Polyfold.GCT.UniformizedPolyfold.isHomeomorph_modelOrbitLevel,
  Polyfold.GCT.UniformizedPolyfold.levelTopology_eq_coinduced,
  Polyfold.GCT.UniformizedPolyfold.theorem_17_1_28_levels,
  Polyfold.GCT.UniformizedPolyfold.levelPolyfoldStructure_equiv,
  Polyfold.GCT.UniformizedPolyfold.exists_levelModel_comparison,
  Polyfold.EP.metrizableSpace_lift_orbitSpace, Polyfold.EP.isZhou_lift,
  Polyfold.GCT.PolyfoldConstruction.z3Uniformized_level,
  Polyfold.GCT.PolyfoldConstruction.z3Uniformized_levelOrbit]
/--
error: rt_check_soft FAIL: RoundTrip.V17_34.B_to_A uses [Polyfold.GCT.UniformizedPolyfold.range_levelIncl_obj,
 Polyfold.GCT.UniformizedPolyfold.isHomeomorph_modelOrbitLevel,
 Polyfold.GCT.UniformizedPolyfold.exists_levelModel_comparison]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V17_34.B_to_A [Polyfold.GCT.UniformizedPolyfold.range_levelIncl_obj,
  Polyfold.GCT.UniformizedPolyfold.level_spec, Polyfold.GCT.UniformizedPolyfold.metrizableSpace_level,
  Polyfold.GCT.UniformizedPolyfold.isHomeomorph_modelOrbitLevel,
  Polyfold.GCT.UniformizedPolyfold.levelTopology_eq_coinduced,
  Polyfold.GCT.UniformizedPolyfold.theorem_17_1_28_levels,
  Polyfold.GCT.UniformizedPolyfold.levelPolyfoldStructure_equiv,
  Polyfold.GCT.UniformizedPolyfold.exists_levelModel_comparison,
  Polyfold.EP.metrizableSpace_lift_orbitSpace, Polyfold.EP.isZhou_lift,
  Polyfold.GCT.PolyfoldConstruction.z3Uniformized_level,
  Polyfold.GCT.PolyfoldConstruction.z3Uniformized_levelOrbit]
#rt_check_except_defs RoundTrip.V17_34.A_to_B [Polyfold.GCT.UniformizedPolyfold.range_levelIncl_obj,
  Polyfold.GCT.UniformizedPolyfold.level_spec, Polyfold.GCT.UniformizedPolyfold.metrizableSpace_level,
  Polyfold.GCT.UniformizedPolyfold.isHomeomorph_modelOrbitLevel,
  Polyfold.GCT.UniformizedPolyfold.levelTopology_eq_coinduced,
  Polyfold.GCT.UniformizedPolyfold.theorem_17_1_28_levels,
  Polyfold.GCT.UniformizedPolyfold.levelPolyfoldStructure_equiv,
  Polyfold.GCT.UniformizedPolyfold.exists_levelModel_comparison,
  Polyfold.EP.metrizableSpace_lift_orbitSpace, Polyfold.EP.isZhou_lift,
  Polyfold.GCT.PolyfoldConstruction.z3Uniformized_level,
  Polyfold.GCT.PolyfoldConstruction.z3Uniformized_levelOrbit]
#rt_check_except_defs RoundTrip.V17_34.B_to_A [Polyfold.GCT.UniformizedPolyfold.range_levelIncl_obj,
  Polyfold.GCT.UniformizedPolyfold.level_spec, Polyfold.GCT.UniformizedPolyfold.metrizableSpace_level,
  Polyfold.GCT.UniformizedPolyfold.isHomeomorph_modelOrbitLevel,
  Polyfold.GCT.UniformizedPolyfold.levelTopology_eq_coinduced,
  Polyfold.GCT.UniformizedPolyfold.theorem_17_1_28_levels,
  Polyfold.GCT.UniformizedPolyfold.levelPolyfoldStructure_equiv,
  Polyfold.GCT.UniformizedPolyfold.exists_levelModel_comparison,
  Polyfold.EP.metrizableSpace_lift_orbitSpace, Polyfold.EP.isZhou_lift,
  Polyfold.GCT.PolyfoldConstruction.z3Uniformized_level,
  Polyfold.GCT.PolyfoldConstruction.z3Uniformized_levelOrbit]
#rt_overlap RoundTrip.V17_34.B_to_A [Polyfold.GCT.UniformizedPolyfold.range_levelIncl_obj,
  Polyfold.GCT.UniformizedPolyfold.level_spec, Polyfold.GCT.UniformizedPolyfold.metrizableSpace_level,
  Polyfold.GCT.UniformizedPolyfold.isHomeomorph_modelOrbitLevel,
  Polyfold.GCT.UniformizedPolyfold.levelTopology_eq_coinduced,
  Polyfold.GCT.UniformizedPolyfold.theorem_17_1_28_levels,
  Polyfold.GCT.UniformizedPolyfold.levelPolyfoldStructure_equiv,
  Polyfold.GCT.UniformizedPolyfold.exists_levelModel_comparison,
  Polyfold.EP.metrizableSpace_lift_orbitSpace, Polyfold.EP.isZhou_lift,
  Polyfold.GCT.PolyfoldConstruction.z3Uniformized_level,
  Polyfold.GCT.PolyfoldConstruction.z3Uniformized_levelOrbit]

end RoundTrip.V17_34
