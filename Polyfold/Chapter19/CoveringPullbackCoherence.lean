import Polyfold.Chapter19.CoveringPullbackExamples
import Polyfold.Chapter17.StrongBundleStructuresExamples

/-!
# Coherence for the reflection bundle pulled back along `absBasic` (HWZ 2021 §19.8, pp. 934–939)

The coherence condition (2) of 2021 Definition 19.8.4 (Definition 19.6.15 for the pairs
`(Ψ, Γ)` of `F̃`) for the uniformizer construction `absFt` of `CoveringPullbackExamples`, so that
`absFt` has a transition construction in the sense of Definition 19.8.4, a basic construction in
the sense of Definition 19.8.5, and Theorem 19.8.6 has a non-degenerate instance, pp. 934–939.

For slice uniformizers `W_V = V ×_ℝ (ℝ × ℝ)`, `Γ(v, a) = a`, the map `H` of (19.16) is
`H(k, (v, a)) = (v, (φ, a), (t(k), g a))` for `k = (o, g, g o)`, so
`C = H'⁻¹ ∘ H : (k, (v, a)) ↦ (k, (t(k), g a))`.  The group element `g = k(k)` is locally constant
on `M(Ψ, Ψ')` (`continuous_absM_key`), and over the open set where it is `g`, `C` is
`a ↦ g a` (Chapter 19's `reflHmap`) followed by the pull-back projections; with the inverse
`(k, (t(k), a')) ↦ (k, (s(k), g⁻¹ a'))` of the same form it is a strong bundle isomorphism.

## What is formalized

* `sliceFibreMap`, `isStrongBundleMap_sliceFibreMap`: for sc-smooth `f₁ : X → V`, `f₂ : X → V'`
  and a continuous `c : X → ℤˣ` with `c(x) f₁(x) = f₂(x)`, the map
  `(x, (v, a)) ↦ (x, (f₂(x), c(x) a))` of pull-backs `f₁*W_V → f₂*W_{V'}` is a strong bundle map
  covering the identity.
* `absPU_eq`, `absFt_slice`, `absFt𝓕` (the keyed transition construction for `absFt`),
  `absFt_toCBC` (`(F̂, 𝓕) = absBasic`), `continuous_absFt_key`.
* `altC_absFt_eq`, **`absFt_isCoherent`** (Definition 19.8.4 (2) for `absFt`).
* **`absFtTransition`** (Definition 19.8.4), **`absFtBasic`** (Definition 19.8.5),
  `absFt_isCompatible`, **`absFt_theorem_19_8_6_full`** (Theorem 19.8.6 for `absFt`, all parts
  formalized in `theorem_19_8_6_hyp`), and `absFt_coherent_nondegenerate` (the fibre action of the
  morphism `(-1, 0)` on `W` is `-1`, and `C` is not the identity on the second factor there).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples GCT.PolyfoldConstruction TrivialBundle Chapter19

/-! ### Fibre maps between pull-backs of slice bundles -/

section SliceFibreMap

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {D D' : TranslationSlice ℤˣ (Fin 1 → ℝ)} {f₁ : X → (absSliceUnif D).O}
  {f₂ : X → (absSliceUnif D').O}

/-- The base point `x` of `(x, (v, a)) ∈ f₁*W_V`. -/
abbrev slicePt (z : pullbackSpace (sliceBun D).Q f₁) : X := z.1.1

/-- The fibre coordinate `a` of `(x, (v, a)) ∈ f₁*W_V`. -/
abbrev sliceA (z : pullbackSpace (sliceBun D).Q f₁) : (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
  (show SliceW D from z.1.2).1.2

/-- `a₁ = f₁(x)` for `(x, (v, a)) ∈ f₁*W_V`. -/
theorem slice_fst_eq (z : pullbackSpace (sliceBun D).Q f₁) :
    (sliceA z).1 = (f₁ (slicePt z)).1 := by
  obtain ⟨⟨x, ⟨⟨v, a⟩, hw⟩⟩, hz⟩ := z
  have hz' : v = f₁ x := hz
  have hw' : a.1 = v.1 := hw
  subst hz'
  exact hw'

/-- **The fibre map `(x, (v, a)) ↦ (x, (f₂(x), c(x) a))`** of pull-backs `f₁*W_V → f₂*W_{V'}`. -/
def sliceFibreMap (c : X → ℤˣ) (hcf : ∀ x, c x • (f₁ x).1 = (f₂ x).1)
    (z : pullbackSpace (sliceBun D).Q f₁) : pullbackSpace (sliceBun D').Q f₂ :=
  ⟨(slicePt z, (⟨(f₂ (slicePt z), c (slicePt z) • sliceA z), by
      change (c (slicePt z) • sliceA z).1 = (f₂ (slicePt z)).1
      rw [Prod.smul_fst, slice_fst_eq, hcf]⟩ : SliceW D')), rfl⟩

@[simp] theorem sliceFibreMap_val (c : X → ℤˣ) (hcf : ∀ x, c x • (f₁ x).1 = (f₂ x).1)
    (z : pullbackSpace (sliceBun D).Q f₁) :
    (show SliceW D' from (sliceFibreMap c hcf z).1.2).1 =
      (f₂ (slicePt z), c (slicePt z) • sliceA z) := rfl

/-- The fibre part `(x, (v, a)) ↦ c(x) a`, into the trivial bundle `ℝ × ℝ → ℝ`. -/
def sliceFibrePart (c : X → ℤˣ) (z : pullbackSpace (sliceBun D).Q f₁) :
    (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
  c (slicePt z) • sliceA z

variable [ParacompactSpace (pullbackSpace (sliceBun D).Q f₁)]

theorem isStrongBundleMap_sliceFibrePart (hf₁ : PX.IsScSmoothMap (absSliceUnif D).P f₁)
    (c : X → ℤˣ) (hc : Continuous c) (hcf : ∀ x, c x • (f₁ x).1 = (f₂ x).1) :
    ((sliceBun D).bundle.pullback hf₁).IsStrongBundleMap (bundle 1 1) (fun x => (f₂ x).1)
      (sliceFibrePart c) := by
  refine StrongBundle.isStrongBundleMap_of_locally_eqOn (fun z => ?_) fun x₀ => ?_
  · change (c (slicePt z) • sliceA z).1 = (f₂ (slicePt z)).1
    rw [Prod.smul_fst, slice_fst_eq, hcf]
  · have h1 : (sliceBun D).bundle.IsStrongBundleMap (bundle 1 1) (absSliceUnif D).obj
        (fun w : (sliceBun D).W => (show SliceW D from w).1.2) :=
      (bundle 1 1).isStrongBundleMap_pullbackProj' (isScSmoothMap_sliceObj D)
    refine ⟨c ⁻¹' {c x₀}, (isOpen_discrete _).preimage hc, rfl, _, _,
      (reflHmap (c x₀)).comp (h1.comp
          ((sliceBun D).bundle.isStrongBundleMap_pullbackProj' hf₁)), fun z hz => ?_⟩
    have hz' : c (slicePt z) = c x₀ := hz
    change c (slicePt z) • sliceA z = c x₀ • sliceA z
    rw [hz']

variable [ParacompactSpace (pullbackSpace (sliceBun D').Q f₂)]

/-- **`(x, (v, a)) ↦ (x, (f₂(x), c(x) a))` is a strong bundle map covering the identity**, for
sc-smooth `f₁`, `f₂` and a continuous (so locally constant) `c` with `c(x) f₁(x) = f₂(x)`. -/
theorem isStrongBundleMap_sliceFibreMap (hf₁ : PX.IsScSmoothMap (absSliceUnif D).P f₁)
    (hf₂ : PX.IsScSmoothMap (absSliceUnif D').P f₂) (c : X → ℤˣ) (hc : Continuous c)
    (hcf : ∀ x, c x • (f₁ x).1 = (f₂ x).1) :
    ((sliceBun D).bundle.pullback hf₁).IsStrongBundleMap ((sliceBun D').bundle.pullback hf₂) id
      (sliceFibreMap c hcf) := by
  have h1 := isStrongBundleMap_sliceFibrePart hf₁ c hc hcf
  have h2 : ((sliceBun D).bundle.pullback hf₁).IsStrongBundleMap (sliceBun D').bundle (f₂ ∘ id)
      (fun z => (⟨(f₂ (slicePt z), sliceFibrePart c z), by
        change (c (slicePt z) • sliceA z).1 = (f₂ (slicePt z)).1
        rw [Prod.smul_fst, slice_fst_eq, hcf]⟩ : SliceW D')) :=
    (bundle 1 1).isStrongBundleMap_pullbackPair (isScSmoothMap_sliceObj D') hf₂ h1
  exact (sliceBun D').bundle.isStrongBundleMap_pullbackPair hf₂ (l := id)
    MPolyfold.isScSmoothMap_id h2

end SliceFibreMap

/-! ### The transition construction of `absFt` -/

theorem absPU_zero : absPU 0 = slicePU overlapSlice₀ 0 (mem_univ _) zero_fix := by
  rw [absPU, dif_pos rfl]

/-- Every member of `F̃(β)` is the uniformizer of a slice. -/
theorem absPU_eq (β : Fin 1 → ℝ) :
    ∃ (D : TranslationSlice ℤˣ (Fin 1 → ℝ)) (hβ : β ∈ D.V) (hfix : ∀ h ∈ D.H, h • β = β),
      absPU β = slicePU D β hβ hfix := by
  by_cases h0 : β = 0
  · subst h0
    exact ⟨_, _, _, absPU_zero⟩
  · unfold absPU
    rw [dif_neg h0]
    by_cases hp : 0 < β 0
    · rw [dif_pos hp]
      exact ⟨_, _, _, rfl⟩
    · rw [dif_neg hp]
      exact ⟨_, _, _, rfl⟩

theorem absFt_slice (Ψ : absFt.toUniformizerConstruction.Unif) :
    ∃ D : TranslationSlice ℤˣ (Fin 1 → ℝ), Ψ.1 = sliceUniformizer isScSmoothMap_units_smul D := by
  obtain ⟨Ψ₁, β, Ψh, hmem, hΨ⟩ := Ψ
  obtain ⟨x, hx, rfl⟩ := hmem
  obtain ⟨D, hβ, hfix, h⟩ := absPU_eq β
  refine ⟨D, ?_⟩
  change Ψ₁ = _
  rw [← hΨ, mem_singleton_iff.1 hx, h]
  rfl

/-- **The keyed transition construction for `absFt`**: `F_h(q) = (q, g, g q)`. -/
def absFt𝓕 : absFt.toUniformizerConstruction.TransitionConstruction :=
  ⟦sliceData isScSmoothMap_units_smul absFt_slice⟧

theorem toCBC_sliceData_eq (U₁ U₂ : CoveringUniformizerConstruction absCovP) (h : U₁ = U₂)
    (h₁ : ∀ Ψ : U₁.toUniformizerConstruction.Unif,
      ∃ D : TranslationSlice ℤˣ (Fin 1 → ℝ), Ψ.1 = sliceUniformizer isScSmoothMap_units_smul D)
    (h₂ : ∀ Ψ : U₂.toUniformizerConstruction.Unif,
      ∃ D : TranslationSlice ℤˣ (Fin 1 → ℝ), Ψ.1 = sliceUniformizer isScSmoothMap_units_smul D) :
    (⟨U₁, ⟦sliceData isScSmoothMap_units_smul h₁⟧⟩ : CoveringBasicConstruction absCovP) =
      ⟨U₂, ⟦sliceData isScSmoothMap_units_smul h₂⟧⟩ := by
  subst h
  rfl

/-- **`(F̂, 𝓕)` is `absBasic`** (Definition 19.8.4 (3)). -/
theorem absFt_toCBC : absFt.toCBC absFt𝓕 = absBasic :=
  toCBC_sliceData_eq _ _ absFt_hatU _ _

/-- `k ↦ k(k)` is continuous on `M(Ψ, Ψ')`. -/
theorem continuous_absFt_key (x y : absFt.Unif) :
    Continuous fun k : absFt.MBase absFt𝓕 x y => (k : x.x.Ψh.Ψ.Trans y.x.Ψh.Ψ).mor.1 :=
  continuous_discrete_rng.2 fun k =>
    ((absFt.toCBC absFt𝓕).toBasic.isOpen_M_iff
      (F := sliceData isScSmoothMap_units_smul absFt_slice) rfl).2
      (sliceData_isOpenTr_key isScSmoothMap_units_smul absFt_slice _ _ k)

/-! ### Coherence -/

section Coherence

variable {β β' : Fin 1 → ℝ} {D D' : TranslationSlice ℤˣ (Fin 1 → ℝ)} {hβ : β ∈ D.V}
  {hβ' : β' ∈ D'.V} {hfix : ∀ h ∈ D.H, h • β = β} {hfix' : ∀ h ∈ D'.H, h • β' = β'}

theorem key_smul_src (x y : absFt.Unif) (k : absFt.MBase absFt𝓕 x y) :
    (k : x.x.Ψh.Ψ.Trans y.x.Ψh.Ψ).mor.1 • x.x.Ψh.Ψ.obj (absFt.srcB absFt𝓕 x y k) =
      y.x.Ψh.Ψ.obj (absFt.tgtB absFt𝓕 x y k) := by
  have a : (k : x.x.Ψh.Ψ.Trans y.x.Ψh.Ψ).mor.2 = x.x.Ψh.Ψ.obj (k : x.x.Ψh.Ψ.Trans y.x.Ψh.Ψ).src :=
    (k : x.x.Ψh.Ψ.Trans y.x.Ψh.Ψ).src_mor
  have b : (k : x.x.Ψh.Ψ.Trans y.x.Ψh.Ψ).mor.1 • (k : x.x.Ψh.Ψ.Trans y.x.Ψh.Ψ).mor.2 =
      y.x.Ψh.Ψ.obj (k : x.x.Ψh.Ψ.Trans y.x.Ψh.Ψ).tgt :=
    (k : x.x.Ψh.Ψ.Trans y.x.Ψh.Ψ).tgt_mor
  rw [← a]
  exact b

/-- The member `(Ψ_D, Ψ̂_D, Γ_D)` of `F̃`. -/
def sliceMember (mem : slicePU D β hβ hfix ∈ absFt.F β) : absFt.Unif :=
  ⟨β, slicePU D β hβ hfix, mem⟩

/-- **`C` for slice members**: `C(k, (v, a)) = (k, (t(k), k(k) a))`. -/
theorem altC_absFt_eq (mem : slicePU D β hβ hfix ∈ absFt.F β)
    (mem' : slicePU D' β' hβ' hfix' ∈ absFt.F β') :
    absFt.altC absFt𝓕 (sliceMember mem) (sliceMember mem') =
      sliceFibreMap (fun k : absFt.MBase absFt𝓕 (sliceMember mem) (sliceMember mem') =>
        (k : (absSliceUnif D).Trans (absSliceUnif D')).mor.1)
        (key_smul_src (sliceMember mem) (sliceMember mem')) := by
  funext z
  apply Subtype.ext
  refine Prod.ext ((sliceBun D).toStr.proj_lift (sliceBun D').toStr _ _ _) ?_
  apply Subtype.ext
  refine Prod.ext rfl ?_
  exact reflBan_act _

/-- `C⁻¹(k, (t(k), a')) = (k, (s(k), k(k)⁻¹ a'))`. -/
def altCinvAbs (mem : slicePU D β hβ hfix ∈ absFt.F β)
    (mem' : slicePU D' β' hβ' hfix' ∈ absFt.F β') :
    absFt.TgtPB absFt𝓕 (sliceMember mem) (sliceMember mem') →
      absFt.SrcPB absFt𝓕 (sliceMember mem) (sliceMember mem') :=
  sliceFibreMap (fun k : absFt.MBase absFt𝓕 (sliceMember mem) (sliceMember mem') =>
      (k : (absSliceUnif D).Trans (absSliceUnif D')).mor.1⁻¹) fun k => by
    rw [inv_smul_eq_iff]
    exact (key_smul_src (sliceMember mem) (sliceMember mem') k).symm

theorem isStrongBundleIso_altC_absFt (mem : slicePU D β hβ hfix ∈ absFt.F β)
    (mem' : slicePU D' β' hβ' hfix' ∈ absFt.F β') :
    (absFt.srcBundle absFt𝓕 (sliceMember mem) (sliceMember mem')).IsStrongBundleIso
      (absFt.tgtBundle absFt𝓕 (sliceMember mem) (sliceMember mem')) id
      (absFt.altC absFt𝓕 (sliceMember mem) (sliceMember mem')) id (altCinvAbs mem mem') := by
  have hc := continuous_absFt_key (sliceMember mem) (sliceMember mem')
  let _ : ParacompactSpace (pullbackSpace (sliceBun D).Q
      (absFt.srcB absFt𝓕 (sliceMember mem) (sliceMember mem'))) :=
    absFt.instParacompactSpaceSrcPB absFt𝓕 _ _
  let _ : ParacompactSpace (pullbackSpace (sliceBun D').Q
      (absFt.tgtB absFt𝓕 (sliceMember mem) (sliceMember mem'))) :=
    absFt.instParacompactSpaceTgtPB absFt𝓕 _ _
  rw [altC_absFt_eq]
  refine ⟨isStrongBundleMap_sliceFibreMap (absFt.isScSmoothMap_srcB absFt𝓕 _ _)
      (absFt.isScSmoothMap_tgtB absFt𝓕 _ _) _ hc _,
    ?_, fun z => ?_, fun z => ?_⟩
  · unfold altCinvAbs
    exact isStrongBundleMap_sliceFibreMap
      (absFt.isScSmoothMap_tgtB absFt𝓕 _ _) (absFt.isScSmoothMap_srcB absFt𝓕 _ _)
      (fun k : absFt.MBase absFt𝓕 (sliceMember mem) (sliceMember mem') =>
        (k : (absSliceUnif D).Trans (absSliceUnif D')).mor.1⁻¹)
      ((continuous_of_discreteTopology (f := fun g : ℤˣ => g⁻¹)).comp hc) _
  · apply Subtype.ext
    refine Prod.ext rfl (Subtype.ext (Prod.ext ?_ ?_))
    · exact (z.2 : _ = _).symm
    · exact inv_smul_smul _ _
  · apply Subtype.ext
    refine Prod.ext rfl (Subtype.ext (Prod.ext ?_ ?_))
    · exact (z.2 : _ = _).symm
    · exact smul_inv_smul _ _

end Coherence

/-- **2021 Definition 19.8.4 (2) for `absFt`**: every `C = H'⁻¹ ∘ H` is a strong bundle
isomorphism covering the identity of `M(Ψ, Ψ')`. -/
theorem absFt_isCoherent : absFt.IsCoherent absFt𝓕 := by
  rintro ⟨β, xx, mem⟩ ⟨β', yy, mem'⟩
  have hx : xx = absPU β := mem
  have hy : yy = absPU β' := mem'
  subst hx hy
  obtain ⟨D, hβ, hfix, h⟩ := absPU_eq β
  obtain ⟨D', hβ', hfix', h'⟩ := absPU_eq β'
  revert mem mem'
  rw [h, h']
  intro mem mem'
  exact ⟨(isStrongBundleIso_altC_absFt mem mem').toMap,
    (isStrongBundleIso_altC_absFt mem mem').isStrongBundleIsoOn_univ⟩

/-- **2021 Definition 19.8.4 for `absFt`**: the keyed transition construction, with class
uniformizers, a metrizable `T_{|B|}` and coherence. -/
def absFtTransition : absFt.PullbackTransitionConstruction where
  𝓕 := absFt𝓕
  hasClassUniformizers := absFt_toCBC ▸ absBasic_hasClassUniformizers
  metrizable := by
    obtain ⟨hB, hm, -⟩ := absBasic_conditions (absFt.toCBC absFt𝓕) absFt_toCBC
    exact hm
  isCoherent := absFt_isCoherent

/-- **2021 Definition 19.8.5 for `(absCovP, reflBan)`**: the basic construction `(F̃, 𝓕)`. -/
def absFtBasic : PullbackUniformizerConstruction.PullbackBasicConstruction absCovP reflBan :=
  ⟨absFt, absFtTransition⟩

theorem absFt_isCompatible : absFtTransition.toCoveringBasicConstruction.IsCompatible := by
  have h := absBasic_isCompatible
  rw [← absFt_toCBC] at h
  exact h

/-- **2021 Theorem 19.8.6 for `absFt`**: all conclusions of `theorem_19_8_6_hyp` (the functor `Γ̂`,
(1)–(4), and (5) for `|A|`, `|B|`) hold for every pair of members of `F̃`. -/
theorem absFt_theorem_19_8_6_full (x y : absFt.Unif) :
    (Injective x.x.gammaHat.obj ∧ x.x.gammaHat.toFunctor.Full ∧
      x.x.gammaHat.toFunctor.Faithful) ∧
    (absFt.srcBundle absFt𝓕 x y).IsStrongBundleIso (absFt.bundleG absFt𝓕 x y) id
      (absFt.altHHomeo absFt𝓕 x y) id (absFt.altHHomeo absFt𝓕 x y).symm ∧
    ((absFt.hatPoly absFt𝓕 x y).IsLocalScDiffeo (absFt.basePoly absFt𝓕 x y)
        (absFt.pBmap absFt𝓕 x y) ∧ Surjective (absFt.pBmap absFt𝓕 x y)) ∧
    Bijective (absFt.Umap absFt𝓕 x y) ∧
    Surjective (absFt.pbarMap absFt𝓕 x y) ∧
    (@MetrizableSpace _ (absFtTransition.toCoveringBasicConstruction.toBasic.natTop
        absFtTransition.hasClassUniformizers.toBasic) ∧
      @MetrizableSpace _ (absFtTransition.toCoveringBasicConstruction.natTopA Fact.out
        absFt_isCompatible absFtTransition.hasClassUniformizers)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
    absFt.theorem_19_8_6_hyp absFtTransition absFt_isCompatible x y
  exact ⟨h0, h1, h2, h3.1, h4.2.1, h5⟩

/-- **The coherence witness is non-degenerate**: on the member at `β = 0` (the slice `ℝ` with
group `ℤ/2`), `C` maps `(k, (0, (0, v)))` for `k = (0, -1, 0)` to `(k, (0, (0, -v)))`. -/
theorem absFt_coherent_nondegenerate :
    ∃ (x : absFt.Unif) (z : absFt.SrcPB absFt𝓕 x x),
      ((absFt.altC absFt𝓕 x x z : absFt.MBase absFt𝓕 x x × x.x.bun.W).2 : x.x.bun.W) ≠
        ((z : absFt.MBase absFt𝓕 x x × x.x.bun.W).2 : x.x.bun.W) := by
  have mem : slicePU overlapSlice₀ 0 (mem_univ _) zero_fix ∈ absFt.F 0 := absPU_zero ▸ rfl
  let k : (absSliceUnif overlapSlice₀).Trans (absSliceUnif overlapSlice₀) :=
    ⟨⟨0, mem_univ _⟩, ((-1 : ℤˣ), 0), ⟨0, mem_univ _⟩, rfl, by
      change (-1 : ℤˣ) • (0 : Fin 1 → ℝ) = 0
      exact units_smul_zero_rn _⟩
  let z : absFt.SrcPB absFt𝓕 (sliceMember mem) (sliceMember mem) :=
    ⟨(k, ⟨(⟨0, mem_univ _⟩, ((0 : Fin 1 → ℝ), (fun _ => 1 : Fin 1 → ℝ))), rfl⟩), rfl⟩
  refine ⟨sliceMember mem, z, fun h => ?_⟩
  rw [congrFun (altC_absFt_eq mem mem) z] at h
  have h2 := congrArg (fun w : SliceW overlapSlice₀ => (w.1.2.2 : Fin 1 → ℝ) 0) h
  change ((-1 : ℤˣ) • (fun _ => 1 : Fin 1 → ℝ)) 0 = 1 at h2
  rw [units_smul_rn_neg_one] at h2
  norm_num at h2

end GroupoidalCategory

end Polyfold
