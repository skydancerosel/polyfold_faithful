import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_33

set_option maxSynthPendingDepth 3

/-! Round trip for V17_33 (2021 Theorem 17.1.28, p. 766: `C_1` is a GCT with the polyfold structure
`(F¹, M_{F¹})`).

`A` is the conjunction of the types of `isHomeomorph_modelOrbitEquivOne`, `metrizableSpace_levelOne`,
`theorem_17_1_28_gct`, `isOpenEmbedding_levelOneFunctor`, `theorem_17_1_28`,
`levelOne_hasRegularity_iff`, `levelOne_hasUniformizers` (the definitions `levelOneTopology`,
`levelOneGCT`, `levelOneUnif`, `levelOneTransEquiv`, `ltrPolyfold`, `levelOneConstruction`,
`levelOnePolyfoldClass`, `levelOneHomeomorphRaised` are vocabulary), with `u := 0`.

* `B_to_A`: `B`'s first conjunct is the topology statement (`|Γ_Ψ¹|` homeomorphisms for every
  covering family, for the topology of `levelOneGCT`, which is `levelOneTopology` by definition);
  from it: `isHomeomorph_modelOrbitEquivOne`, `metrizableSpace_levelOne` (`|X_Ψ¹|` is metrizable),
  `theorem_17_1_28_gct`, `isOpenEmbedding_levelOneFunctor` (the project's proof, with `B`'s
  homeomorphism in place of the banned lemma).  `theorem_17_1_28`, `levelOne_hasRegularity_iff`,
  `levelOne_hasUniformizers` are statements about the project's `levelOneConstruction`, which `B`
  does not mention (it asserts that *some* structure `S₁` exists); they are re-proved outright
  (copies of the project's proofs from non-item lemmas).
* `A_to_B` is not proved.  The topology and the description of `F¹` follow from `A`
  (`theorem_17_1_28_gct`, `theorem_17_1_28` with `S₁ := levelOneConstruction hc`).  The gap is the
  transition structures: `B` asks, for EVERY pair `Ψ, Ψ'` of uniformizers of `F`, that
  `M_{F¹}(Ψ¹, Ψ'¹) → M(Ψ, Ψ')¹`, `(q, φ, q') ↦ (q, φ, q')` be a homeomorphism and an
  sc-diffeomorphism.  `A` (like the project's `levelOneConstruction`) gives this only for the
  uniformizer `Ψ₀ = levelOneData Ψ¹` chosen to define `M_{F¹}(Ψ¹, Ψ'¹)`.  If two uniformizers
  `Ψ ≠ Ψ₀` have the same lift `Ψ¹ = Ψ₀¹` (they differ only on points of level `0`), `B` needs the
  M-polyfold structures `M(Ψ, Ψ')¹` and `M(Ψ₀, Ψ₀')¹` to coincide on their common underlying set;
  nothing in `A` (or in Definition 17.1.8 as formalized: the structures on different `M(Ψ, Ψ')` are
  independent data tied only by smoothness of `s, t, u, ι, m`) yields this.  Since `S₁.M` is a single
  structure per pair of lifts, no choice of `S₁` avoids the issue.

**Harness note.**  `B` and `A` mention `levelOneGCT`, whose field `metrizable` is the banned
`metrizableSpace_levelOne` (a direct reference in the body), and `levelOneUnif` (also under
`levelOneConstruction`), whose field `isOpenEmbedding_orbitMap` is the banned
`isOpenEmbedding_levelOneFunctor`; `modelOrbitHomeomorphOne` (under `levelOnePolyfoldStructure`,
`levelOneHomeomorphRaised`, `isOpenEmbedding_levelOneFunctor`) is built from the banned
`isHomeomorph_modelOrbitEquivOne`.  So `#rt_check` and `#rt_check_soft` fail (recorded with
`#guard_msgs`); the local `#rt_check_except_defs` (bodies of `levelOneGCT`, `levelOneUnif`,
`modelOrbitHomeomorphOne` not unfolded) passes on `B_to_A` and on `A_to_B_partial`.
-/

namespace RoundTrip.V17_33
open Polyfold Set Function Topology TopologicalSpace CategoryTheory
open Polyfold.GCT.PolyfoldConstruction

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne.{0},
    @Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne.{0},
    @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct.{0},
    @Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor.{0},
    @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28.{0},
    @Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff.{0},
    @Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers.{0}⟩

/-! ### `B ⇒ A` -/

section FromB

variable (hB : B) {C : GCT.{0}} (S : C.PolyfoldConstruction) (hc : S.HasCoveringUniformizers)

include hB in
theorem homeo (c : S.CoveringFamily) :
    @IsHomeomorph _ _ _ (S.levelOneTopology hc) (S.modelOrbitEquivOne c) :=
  (hB C S hc).1 c

include hB in
theorem metrizable : @MetrizableSpace (S.regSub 1).OrbitSpace (S.levelOneTopology hc) := by
  let _ := S.levelOneTopology hc
  have := (S.modelEP (S.levelOneCover hc).Ψ).X.metrizableSpace_liftOne_orbitSpace
    (S.hasParacompactOrbitSpace_model _)
  exact ((homeo hB S hc (S.levelOneCover hc)).homeomorph _).symm.isEmbedding.metrizableSpace

include hB in
theorem openEmb (Ψ : S.Unif) :
    letI := S.levelOneMulAction Ψ
    @IsOpenEmbedding _ _ _ (S.levelOneTopology hc) (S.levelOneFunctor Ψ).orbitMap := by
  let _ := S.levelOneMulAction Ψ
  let _ := S.levelOneTopology hc
  set c := (S.levelOneCover hc).adjoin S Ψ
  have hΓ := homeo hB S hc c
  have hX := (S.modelEP c.Ψ).X.liftOne.proposition_7_1_8_isOpenQuotientMap
  have hι := S.isLocalScDiffeo_adjoinIncl hc Ψ
  set T := GroupoidStr.translation Ψ.1.G (Ψ.1.P.Level 1)
  have hfac : (S.levelOneFunctor Ψ).orbitMap ∘ T.π =
      (S.modelFunctorOne c.Ψ).orbitMap ∘ (S.modelEP c.Ψ).X.liftOne.π ∘ S.adjoinIncl hc Ψ :=
    funext fun x => S.levelOneFunctor_orbitMap_π hc Ψ x
  have hcomp : Continuous ((S.modelFunctorOne c.Ψ).orbitMap ∘ (S.modelEP c.Ψ).X.liftOne.π ∘
      S.adjoinIncl hc Ψ) :=
    hΓ.continuous.comp (hX.continuous.comp hι.continuous)
  have hq : IsQuotientMap T.π := isQuotientMap_quotient_mk'
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact hq.continuous_iff.2 (hfac ▸ hcomp)
  · intro a b h
    induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h y => ?_
    have h' : (S.regSub 1).π ((S.levelOneFunctor Ψ).obj x) =
        (S.regSub 1).π ((S.levelOneFunctor Ψ).obj y) := h
    obtain ⟨φ, hs, ht⟩ := GroupoidStr.isomorphic_fullSub_iff.1 (((S.regSub 1).π_eq_π_iff).1 h')
    obtain ⟨g, hg, -⟩ := Ψ.1.toUniformizer.exists_smul_eq_mor (φ := φ) hs ht
    exact (T.π_eq_π_iff).2 ⟨(g, x), rfl, MPolyfold.level_ext hg⟩
  · intro W hW
    have hW' : (S.levelOneFunctor Ψ).orbitMap '' W =
        ((S.modelFunctorOne c.Ψ).orbitMap ∘ (S.modelEP c.Ψ).X.liftOne.π ∘ S.adjoinIncl hc Ψ) ''
          (T.π ⁻¹' W) := by
      rw [← hfac, image_comp, image_preimage_eq _ hq.surjective]
    rw [hW', image_comp, image_comp]
    exact hΓ.isOpenMap _ (hX.isOpenMap _ (hι.isOpenMap _ (hW.preimage hq.continuous)))

end FromB

/-! ### Copies (statements about `levelOneConstruction`, not consequences of `B`) -/

theorem t28' {C : GCT.{0}} (S : C.PolyfoldConstruction) (hc : S.HasCoveringUniformizers) :
    type_of% (@Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28.{0} C S hc) := by
  refine ⟨rfl, fun _ => rfl, fun _ => ⟨rfl, HEq.rfl, fun _ => rfl⟩, fun L L' => ?_⟩
  obtain ⟨h1, h2, h3⟩ := S.levelOneInclOf_spec hc L.1 L'.1 (S.levelOneData hc L)
    (S.levelOneData hc L') (S.levelOneData_eq hc L) (S.levelOneData_eq hc L')
  exact ⟨_, _, _, S.levelOneData_eq hc L, S.levelOneData_eq hc L', h1, h2, h3⟩

theorem reg' {C : GCT.{0}} {S : C.PolyfoldConstruction} {hc : S.HasCoveringUniformizers}
    (L : GCT.Unif (S.levelOneF hc)) {x : L.1.O}
    {α : (S.levelOneGCT hc).Obj}
    (hx : (S.levelOneGCT hc).toGroupoidStr.Isomorphic (L.1.obj x) α) (m : ℕ) :
    (S.levelOneConstruction hc).HasRegularity m α ↔ S.HasRegularity (m + 1) α.1 := by
  set Ψ := S.levelOneData hc L
  have hL := S.levelOneData_eq hc L
  rw [hasRegularity_iff (S := S.levelOneConstruction hc) L hx m,
    levelOneObjCast_mem_levelSet_iff hL x m]
  have hiso : C.toGroupoidStr.Isomorphic
      (Ψ.1.obj (Ψ.1.P.levelVal 1 (S.levelOneObjCast hc L.1 Ψ hL x))) α.1 := by
    rw [(S.levelOneObjCast_spec hc L.1 Ψ hL).2.2 x]
    exact GroupoidStr.isomorphic_fullSub_iff.1 hx
  exact (hasRegularity_iff Ψ hiso (m + 1)).symm

theorem unif' {C : GCT.{0}} {S : C.PolyfoldConstruction} (hu : S.HasUniformizers) :
    (S.levelOneConstruction (S.hasCoveringUniformizers_of_hasUniformizers hu)).HasUniformizers := by
  intro α
  obtain ⟨Ψ, hΨ⟩ := hu (show S.regSet 1 from α).1
  exact ⟨_, ⟨⟨Ψ, _, hΨ⟩, hΨ, rfl⟩⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun S hc c => homeo hB S hc c, fun S hc => metrizable hB S hc, fun {C} S hc => ?_,
    fun S hc Ψ => openEmb hB S hc Ψ, fun S hc => t28' S hc, fun L _ _ hx m => reg' L hx m,
    fun hu => unif' hu⟩
  exact ⟨rfl, (hB _ S hc).1, metrizable hB S hc, S.continuous_orbitInclLevelOne hc,
    S.injective_orbitInclLevelOne, C.toGroupoidStr.range_orbitMap_fullSubInclusion _⟩

/-! ### `A ⇒ B`: what is proved -/

/-- The topology and the description of `F¹` (all of `B` but the transition structures). -/
theorem A_to_B_partial : A →
    ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (hc : S.HasCoveringUniformizers),
      (∀ c : S.CoveringFamily,
        @IsHomeomorph _ _ _ (S.levelOneGCT hc).top (S.modelFunctorOne c.Ψ).orbitMap) ∧
      ∃ S₁ : (S.levelOneGCT hc).PolyfoldConstruction,
        ∀ α : (S.levelOneGCT hc).Obj,
          S₁.F α = {L | ∃ Ψ : S.Unif, Ψ.1 ∈ S.F α.1 ∧ L = S.levelOneUnif hc Ψ} := by
  rintro ⟨-, -, hgct, -, h28, -⟩ C S hc
  exact ⟨(hgct S hc).2.1, S.levelOneConstruction hc, (h28 S hc).2.1⟩

/-! ### Harness checks -/

open Lean Elab Command in
/-- `#rt_check_except_defs T [nᵢ]`: the harness traversal `rtCollectSoft` with the bodies of the
listed definitions not unfolded (they reference the banned theorems directly in their fields). -/
elab "#rt_check_except_defs " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let excl : NameSet := [``Polyfold.GCT.PolyfoldConstruction.levelOneGCT,
    ``Polyfold.GCT.PolyfoldConstruction.levelOneUnif,
    ``Polyfold.GCT.PolyfoldConstruction.modelOrbitHomeomorphOne].foldl
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
error: rt_check FAIL: RoundTrip.V17_33.B_to_A uses [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
 Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
 Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V17_33.B_to_A [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct,
  Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers]
/--
error: rt_check_soft FAIL: RoundTrip.V17_33.B_to_A uses [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
 Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
 Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V17_33.B_to_A [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct,
  Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers]
/--
error: rt_check FAIL: RoundTrip.V17_33.A_to_B_partial uses [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
 Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
 Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V17_33.A_to_B_partial [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct,
  Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers]
/--
error: rt_check_soft FAIL: RoundTrip.V17_33.A_to_B_partial uses [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
 Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
 Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V17_33.A_to_B_partial [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct,
  Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers]

#rt_check_except_defs RoundTrip.V17_33.B_to_A [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct,
  Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers]
#rt_check_except_defs RoundTrip.V17_33.A_to_B_partial [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct,
  Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers]
#rt_overlap RoundTrip.V17_33.B_to_A [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct,
  Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers]

end RoundTrip.V17_33
