import Polyfold.Chapter17.ProperCoveringMorita
import Polyfold.Chapter17.Subpolyfold
import Polyfold.Chapter17.ModelPropertiesExamples

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.8:
an **effective witness** of **Definition 17.8.13** (p. 836, proper polyfold covering structure and
functor), of the sc-smooth model `τ̂ : E → X` and the square **(17.104)** (p. 838), and of the
Morita equivalence of the models of different covering families (p. 838).  Numbers and pages are
the 2021 text's.

# Two sheets of the reflection `ℤ/2 ⋉ ℝ`

## What is formalized

* For a finite group `G` acting on `O` and a discrete set of sheets `S` with any action of `G`
  (namespace `Polyfold`): `sheetBaseConstruction` (the polyfold structure of `B = G ⋉ O` whose
  sets `F(β)` are `{Ψ₀}` at the `G`-fixed points `β` and empty elsewhere: the tautological
  structure with smaller sets, `restrictF`) and **`sheetFixedPolyfoldCoveringStructure`**, a
  proper polyfold covering structure (Definition 17.8.13) for the sheet functor
  `G ⋉ (S × O) → G ⋉ O`, with the sheet uniformizers at the `G`-fixed points.  Unlike
  `sheetPolyfoldCoveringStructure` it needs no trivial action.
* For the reflection: **`reflectionPolyfoldCoveringFunctor`** (two sheets of `ℤ/2 ⋉ ℝ` over
  `ℤ/2 ⋉ ℝ`, `−1` acting by `x ↦ −x`), the one-element family `reflHatFam` at `0`
  (`reflHatFam_isCoveringFamily`: it covers `|B|`), the two-element family `reflHatPairFam`, and
  **`reflectionHatModel_nondegenerate`**: the action of `G = ℤ/2` on `O = ℝ` is effective and
  non-trivial, `X` is an effective ep-groupoid, `E` and `τ̂` of (17.104) are built (`τ̂` a proper
  covering functor, Definition 8.5.1), `Γ̂`, `Γ` are equivalences with `|Γ̂|`, `|Γ|`
  homeomorphisms, the object `(true, 0)` of `E` has the non-unit automorphism `reflHatMor` over
  the non-unit automorphism `τ̂(reflHatMor)` of `0`, the morphism `reflHatMove` of `E` moves
  `(true, 1)` to `(true, −1)`, and the fibre of `τ̂` over `0` has two points.
* **`reflectionHatModel_morita`**: `hatModel_morita` for the families with one and with two copies
  of the sheet uniformizer, and `|f̂|` sends the class of `(true, 0)` to the class of the copy
  `(true, (true, 0))`.

## Readings

* Definition 17.8.12 allows `F(β) = ∅` (as for Definition 17.1.6): here `F(β) ≠ ∅` only at the
  `G`-fixed point `0`; the single uniformizer at `0` has footprint `|B|`, so the families above
  are covering families and `B` is a polyfold for the induced structure.
-/

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### Sheet structures for any action -/

section SheetFixed

open GCT GCT.PolyfoldConstruction ProperCoveringUniformizer ProperCoveringUniformizerConstruction

variable {G : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  {O : Type u} [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O]
  {PO : MPolyfold O} (hP : ∀ g : G, PO.IsScSmoothMap PO fun y => g • y)
  (S : Type u) [TopologicalSpace S] [DiscreteTopology S] [MulAction G S]
  [ParacompactSpace (S × O)] [Nonempty S]

/-- The uniformizers `Ψ` of the sheet construction are tautological. -/
theorem sheetBase_subset (β : O) :
    (sheetConstruction hP S).toUniformizerConstruction.F β ⊆
      (twistConstruction hP (TranslationTwist.refl G O)).F β := by
  rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
  exact Set.mem_singleton _

/-- **The polyfold structure of `B = G ⋉ O` on the uniformizers of the sheet construction**:
`F(β) = {Ψ₀}` for `G`-fixed `β`, `F(β) = ∅` otherwise, with the tautological transition
M-polyfolds. -/
def sheetBaseConstruction : (GCT.translation G O hP).PolyfoldConstruction :=
  (twistConstruction hP (TranslationTwist.refl G O)).restrictF _ (sheetBase_subset hP S)

/-- **A proper polyfold covering structure** (Definition 17.8.13) for the sheet functor
`G ⋉ (S × O) → G ⋉ O` of any action: the sheet uniformizers at the `G`-fixed points, the
structure `sheetBaseConstruction` of `B`, and the tautological transition M-polyfolds of
`A = G ⋉ (S × O)`. -/
def sheetFixedPolyfoldCoveringStructure :
    ProperPolyfoldCoveringStructure (sheetGCTFunctor hP S) where
  toC := sheetConstruction hP S
  SB := sheetBaseConstruction hP S
  SB_F _ := rfl
  topH U U' := sheetTopOf hP S U.2.1 U'.2.1 U.unif U'.unif (sheet_eq hP S U) (sheet_eq hP S U')
  t2H U U' := sheetT2Of hP S U.2.1 U'.2.1 U.unif U'.unif (sheet_eq hP S U) (sheet_eq hP S U')
  paraH U U' := sheetParaOf hP S U.2.1 U'.2.1 U.unif U'.unif (sheet_eq hP S U) (sheet_eq hP S U')
  MH U U' := sheetMOf hP S U.2.1 U'.2.1 U.unif U'.unif (sheet_eq hP S U) (sheet_eq hP S U')
  isLocalScDiffeo_src U U' :=
    sheetSrcOf hP S U.2.1 U'.2.1 U.unif U'.unif (sheet_eq hP S U) (sheet_eq hP S U')
  isLocalScDiffeo_tgt U U' :=
    sheetTgtOf hP S U.2.1 U'.2.1 U.unif U'.unif (sheet_eq hP S U) (sheet_eq hP S U')
  isScSmoothMap_unit U := sheetUnitOf hP S U.2.1 U.unif (sheet_eq hP S U)
  isScSmoothMap_inv U U' :=
    sheetInvOf hP S U.2.1 U'.2.1 U.unif U'.unif (sheet_eq hP S U) (sheet_eq hP S U')
  isScSmoothMap_mul U U' U'' :=
    sheetMulOf hP S U.2.1 U'.2.1 U''.2.1 U.unif U'.unif U''.unif (sheet_eq hP S U)
      (sheet_eq hP S U') (sheet_eq hP S U'')
  isLocalScDiffeo_p U U' :=
    sheetPOf hP S U.2.1 U'.2.1 U.unif U'.unif (sheet_eq hP S U) (sheet_eq hP S U') _ _

end SheetFixed

/-! ### The reflection -/

section Reflection

open GCT GCT.PolyfoldConstruction ProperPolyfoldCoveringStructure EpGroupoid.Examples
  ProperCoveringUniformizerConstruction EPLocalization.EPLoc

attribute [local instance] instMulActionUnitsBool'

/-- **A proper polyfold covering functor with an effective action** (Definition 17.8.13): two
sheets of `ℤ/2 ⋉ ℝ` over `ℤ/2 ⋉ ℝ`, `−1` acting by `x ↦ −x`. -/
def reflectionPolyfoldCoveringFunctor :
    ProperPolyfoldCoveringFunctor (sheetGCT isScSmoothMap_units_smul Bool)
      (GCT.translation ℤˣ (Fin 1 → ℝ) isScSmoothMap_units_smul) where
  P := sheetGCTFunctor isScSmoothMap_units_smul Bool
  isProperCovering := isProperCoveringGCT_sheet isScSmoothMap_units_smul fun _ _ => rfl
  S := sheetFixedPolyfoldCoveringStructure isScSmoothMap_units_smul Bool

/-- The sheet uniformizer at `0` as a uniformizer of the construction. -/
def reflHatUnif : reflectionPolyfoldCoveringFunctor.S.toC.Unif :=
  ⟨⟨0, reflectionSheetUniformizer⟩, sheetUniformizer_mem isScSmoothMap_units_smul Bool 0
    units_smul_zero_rn⟩

/-- The one-element family `{(Ψ̂, Ψ)}` at `0`. -/
abbrev reflHatFam : PUnit.{1} → reflectionPolyfoldCoveringFunctor.S.toC.Unif := fun _ => reflHatUnif

/-- The two-element family `{(Ψ̂, Ψ), (Ψ̂, Ψ)}` at `0`. -/
abbrev reflHatPairFam : Bool → reflectionPolyfoldCoveringFunctor.S.toC.Unif := fun _ => reflHatUnif

/-- The base uniformizer `Ψ₀` has footprint `|B|`. -/
theorem reflHatUnif_footprint (z : (GCT.translation ℤˣ (Fin 1 → ℝ)
    isScSmoothMap_units_smul).toGroupoidStr.OrbitSpace) :
    z ∈ (reflectionPolyfoldCoveringFunctor.S.toC.baseUnif reflectionPolyfoldCoveringFunctor.S.SB
      reflectionPolyfoldCoveringFunctor.S.SB_F reflHatUnif).1.footprint := by
  change z ∈ (GCT.LocalUniformizer.tautological _ _).footprint
  rw [GCT.LocalUniformizer.tautological_footprint]
  exact mem_univ z

/-- `{(Ψ̂, Ψ)}` is a covering family: its base uniformizer covers `|B|`. -/
theorem reflHatFam_isCoveringFamily :
    reflectionPolyfoldCoveringFunctor.S.SB.IsCoveringFamily
      (reflectionPolyfoldCoveringFunctor.S.baseFam reflHatFam) :=
  eq_univ_of_forall fun z => mem_iUnion.2 ⟨PUnit.unit, reflHatUnif_footprint z⟩

/-- `{(Ψ̂, Ψ), (Ψ̂, Ψ)}` is a covering family. -/
theorem reflHatPairFam_isCoveringFamily :
    reflectionPolyfoldCoveringFunctor.S.SB.IsCoveringFamily
      (reflectionPolyfoldCoveringFunctor.S.baseFam reflHatPairFam) :=
  eq_univ_of_forall fun z => mem_iUnion.2 ⟨true, reflHatUnif_footprint z⟩

/-- The covering family `{(Ψ̂, Ψ)}`. -/
def reflHatCover : reflectionPolyfoldCoveringFunctor.S.CoveringFamily :=
  ⟨PUnit, reflHatFam, reflHatFam_isCoveringFamily⟩

/-- The covering family `{(Ψ̂, Ψ), (Ψ̂, Ψ)}`. -/
def reflHatPairCover : reflectionPolyfoldCoveringFunctor.S.CoveringFamily :=
  ⟨Bool, reflHatPairFam, reflHatPairFam_isCoveringFamily⟩

/-- The object `(true, 0)` of `E`. -/
abbrev reflHatPt : reflectionPolyfoldCoveringFunctor.S.HatObj reflHatFam :=
  ⟨PUnit.unit, (true, 0)⟩

/-- The automorphism `(−1, (true, 0))` of `(true, 0)` in `E`. -/
def reflHatMor : reflectionPolyfoldCoveringFunctor.S.HatMor reflHatFam :=
  ⟨(PUnit.unit, PUnit.unit), ⟨(true, 0), ((-1 : ℤˣ), (true, 0)), (true, 0), rfl,
    Prod.ext (by exact rfl) (by exact units_smul_zero_rn _)⟩⟩

/-- The morphism `(−1, (true, 1)) : (true, 1) → (true, −1)` of `E`. -/
def reflHatMove : reflectionPolyfoldCoveringFunctor.S.HatMor reflHatFam :=
  ⟨(PUnit.unit, PUnit.unit), ⟨(true, fun _ => 1), ((-1 : ℤˣ), (true, fun _ => 1)),
    (true, fun _ => -1), rfl, Prod.ext (by exact rfl) (by
      funext i
      change ((-1 : ℤˣ) • (fun _ => 1 : Fin 1 → ℝ)) i = -1
      norm_num [Units.smul_def])⟩⟩

/-- `−1 ≠ 1` in `ℤˣ`. -/
theorem units_neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := fun h => by
  have := congrArg Units.val h
  norm_num at this

/-- **The non-degenerate effective witness of Definition 17.8.13 and (17.104)**: for the two
sheets of `ℤ/2 ⋉ ℝ` over `ℤ/2 ⋉ ℝ` and the family `{(Ψ̂, Ψ)}` at `0`: the group `G = ℤ/2` of the
uniformizer acts effectively and non-trivially on `O = ℝ`; `X` is an effective ep-groupoid;
`τ̂ : E → X` is a proper covering functor; `Γ̂` and `Γ` are equivalences with `|Γ̂|`, `|Γ|`
homeomorphisms; `(true, 0)` has the non-unit automorphism `reflHatMor` in `E`, with
`τ̂(reflHatMor)` a non-unit automorphism in `X`; `reflHatMove` moves `(true, 1)` to
`(true, −1)`; the fibre of `τ̂` over `0` has two points. -/
theorem reflectionHatModel_nondegenerate :
    let F := reflectionPolyfoldCoveringFunctor
    let hPc := F.isProperCovering
    (∀ g : reflHatUnif.unif.Ψ.G, (∀ x : reflHatUnif.unif.Ψ.O, g • x = x) → g = 1) ∧
      (∃ (g : reflHatUnif.unif.Ψ.G) (x : reflHatUnif.unif.Ψ.O), g • x ≠ x) ∧
      (F.S.baseEP reflHatFam).X.IsEffective ∧
      (F.S.hatModelFunctor reflHatFam hPc).IsProperCovering ∧
      (F.S.hatFunctor reflHatFam hPc).toFunctor.IsEquivalence ∧
      IsHomeomorph (F.S.hatFunctor reflHatFam hPc).orbitMap ∧
      (F.S.baseFunctor reflHatFam).toFunctor.IsEquivalence ∧
      IsHomeomorph (F.S.baseFunctor reflHatFam).orbitMap ∧
      (F.S.hatEpGroupoid reflHatFam hPc).src reflHatMor = reflHatPt ∧
      (F.S.hatEpGroupoid reflHatFam hPc).tgt reflHatMor = reflHatPt ∧
      reflHatMor ≠ (F.S.hatEpGroupoid reflHatFam hPc).unit reflHatPt ∧
      (F.S.hatModelFunctor reflHatFam hPc).mor reflHatMor ≠
        (F.S.baseEP reflHatFam).X.unit ((F.S.hatModelFunctor reflHatFam hPc).obj reflHatPt) ∧
      (F.S.hatEpGroupoid reflHatFam hPc).src reflHatMove = ⟨PUnit.unit, (true, fun _ => 1)⟩ ∧
      (F.S.hatEpGroupoid reflHatFam hPc).tgt reflHatMove = ⟨PUnit.unit, (true, fun _ => -1)⟩ ∧
      (F.S.hatEpGroupoid reflHatFam hPc).src reflHatMove ≠
        (F.S.hatEpGroupoid reflHatFam hPc).tgt reflHatMove ∧
      ((F.S.hatModelFunctor reflHatFam hPc).obj ⁻¹' {⟨PUnit.unit, (0 : Fin 1 → ℝ)⟩}).ncard = 2 := by
  intro F hPc
  refine ⟨?_, ⟨(-1 : ℤˣ), (fun _ => 1 : Fin 1 → ℝ), fun h => ?_⟩, ?_,
    F.S.hatModelFunctor_isProperCovering reflHatFam hPc,
    hatFunctor_isEquivalence hPc reflHatFam_isCoveringFamily,
    isHomeomorph_hatOrbitMap hPc reflHatFam_isCoveringFamily,
    (lemma_17_1_15_of_isCovering reflHatFam_isCoveringFamily).1,
    (lemma_17_1_15_of_isCovering reflHatFam_isCoveringFamily).2, rfl, rfl, fun h => ?_,
    fun h => ?_, rfl, rfl, fun h => ?_, ?_⟩
  · intro g hg
    rcases Int.units_eq_one_or g with rfl | rfl
    · rfl
    · have h1 := congrFun (hg (fun _ => 1 : Fin 1 → ℝ)) 0
      change ((-1 : ℤˣ) • (fun _ => 1 : Fin 1 → ℝ)) 0 = 1 at h1
      norm_num [Units.smul_def] at h1
  · have h1 := congrFun h 0
    change ((-1 : ℤˣ) • (fun _ => 1 : Fin 1 → ℝ)) 0 = 1 at h1
    norm_num [Units.smul_def] at h1
  · exact HasModelProperty.forall isGenIsoInvariant_isEffective reflection_isEffective
      reflectionSingleFamily
  · have h1 := congrArg (fun φ : F.S.HatMor reflHatFam => φ.2.mor.1) h
    change (-1 : ℤˣ) = 1 at h1
    exact units_neg_one_ne_one h1
  · have h1 := congrArg (fun φ : F.S.SB.ModelMor (F.S.baseFam reflHatFam) => φ.2.mor.1) h
    change (-1 : ℤˣ) = 1 at h1
    exact units_neg_one_ne_one h1
  · have h1 := congrArg (fun z : F.S.HatObj reflHatFam => (z.2 : Bool × (Fin 1 → ℝ)).2 0) h
    change (1 : ℝ) = -1 at h1
    norm_num at h1
  · have h : (F.S.hatModelFunctor reflHatFam hPc).obj ⁻¹' {⟨PUnit.unit, (0 : Fin 1 → ℝ)⟩} =
        {(⟨PUnit.unit, (true, 0)⟩ : F.S.HatObj reflHatFam), ⟨PUnit.unit, (false, 0)⟩} := by
      ext ⟨u, b, x⟩
      change (⟨u, x⟩ : F.S.SB.ModelObj (F.S.baseFam reflHatFam)) =
        ⟨PUnit.unit, (0 : Fin 1 → ℝ)⟩ ↔ _
      cases u
      constructor
      · intro h1
        have hx : x = 0 := eq_of_heq (Sigma.mk.inj_iff.1 h1).2
        subst hx
        cases b
        · exact Or.inr rfl
        · exact Or.inl rfl
      · rintro (h1 | h1) <;>
        · have hx : x = 0 :=
            congrArg (fun z : F.S.HatObj reflHatFam => (z.2 : Bool × (Fin 1 → ℝ)).2) h1
          rw [hx]
    rw [h]
    exact Set.ncard_pair fun h => Bool.noConfusion
      (congrArg (fun z : F.S.HatObj reflHatFam => (z.2 : Bool × (Fin 1 → ℝ)).1) h)

/-- **The Morita equivalence of p. 838 for the effective witness**: for the covering families
`{(Ψ̂, Ψ)}` and `{(Ψ̂, Ψ), (Ψ̂, Ψ)}` the conclusions of `hatModel_morita` hold, and `|f̂|` sends
the class of `(true, 0)` in `|E|` to the class of its copy `(true, (true, 0))`. -/
theorem reflectionHatModel_morita :
    let F := reflectionPolyfoldCoveringFunctor
    let hPc := F.isProperCovering
    (IsGeneralizedIso (F.S.hatComparison hPc reflHatCover reflHatPairCover) ∧
      F.S.hatComparison hPc reflHatCover reflHatCover = 𝟙 _ ∧
      F.S.hatComparison hPc reflHatCover reflHatPairCover ≫
          F.S.hatComparison hPc reflHatPairCover reflHatCover =
        F.S.hatComparison hPc reflHatCover reflHatCover ∧
      (F.S.hatFunctor reflHatPairCover.Uf hPc).orbitMap ∘
          orbitMap (F.S.hatComparison hPc reflHatCover reflHatPairCover) =
        (F.S.hatFunctor reflHatCover.Uf hPc).orbitMap ∧
      IsHomeomorph (orbitMap (F.S.hatComparison hPc reflHatCover reflHatPairCover)) ∧
      F.S.hatComparison hPc reflHatCover reflHatPairCover ≫
          localizationFunctor.map (F.S.hatModelHom hPc reflHatPairCover.Uf) =
        localizationFunctor.map (F.S.hatModelHom hPc reflHatCover.Uf) ≫
          F.S.SB.comparison reflHatCover.toBase reflHatPairCover.toBase ∧
      IsGeneralizedIso (F.S.SB.comparison reflHatCover.toBase reflHatPairCover.toBase) ∧
      IsHomeomorph (orbitMap (F.S.SB.comparison reflHatCover.toBase reflHatPairCover.toBase))) ∧
      orbitMap (F.S.hatComparison hPc reflHatCover reflHatPairCover)
          ((F.S.hatEP reflHatFam hPc).X.π ⟨PUnit.unit, (true, 0)⟩) =
        (F.S.hatEP reflHatPairFam hPc).X.π ⟨true, (true, 0)⟩ := by
  intro F hPc
  refine ⟨F.S.hatModel_morita hPc reflHatCover reflHatPairCover reflHatCover, ?_⟩
  refine (isHomeomorph_hatOrbitMap hPc reflHatPairFam_isCoveringFamily).injective ?_
  exact congrFun (F.S.orbitMap_hatComparison hPc reflHatCover reflHatPairCover)
    ((F.S.hatEP reflHatFam hPc).X.π ⟨PUnit.unit, (true, 0)⟩)

end Reflection

end Polyfold
