import Polyfold.Chapter13.Commensurable
import Polyfold.Chapter10.EquivalenceReduced

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.4, pp. 621–628: the common transport tool behind **Theorem 13.4.1** (pull-back along a strong
bundle equivalence) and **Theorem 13.4.4** (pull-back along a proper strong bundle covering)
(2017: Theorems 13.3 and 13.5).

# Pull-back maps of strong bundles over ep-groupoids

## The text, paraphrased

Both proofs pull local sc⁺-section structures back along a map `Φ : W → W'` covering a functor
`F : X → X'` by `Φ(sᵢ(z)) = s'ᵢ(F(z))` (Theorem 13.4.1, the last display; (13.7) in Theorem
13.4.4).  What the two proofs use of `Φ` is the same: `Φ` commutes with the actions
(`Φ(μ(φ, w)) = μ'(F(φ), Φ(w))`), it is a local strong bundle isomorphism over a local
sc-diffeomorphism of the bases, and `F` is faithful (two morphisms with the same source and
target and the same image agree).

## What is formalized (namespace `Polyfold.SBLocalization`)

* `PullMap C A`: the data `(F, Φ)` with these three properties; `PullMap.ofEquivalence` (a strong
  bundle equivalence, Definition 10.4.1) and `PullMap.ofCovering` (a proper strong bundle
  covering, 2021 Definition 8.5.9, `IsProperStrongBundleCovering2021`).
* `PullMap.fiberEquiv` (the fibre maps are linear homeomorphisms), `eq_of_obj_eq`.
* `PullMap.pullSec`: the pulled-back section `z ↦ Φ_z⁻¹(s'(F(z)))`, its laws, and
  `PullMap.isScPlusSectionOn_pullSec` (an sc⁺-section of `P'` on `U'` pulls back to an sc⁺-section
  of `P` on every open `U` with `F(U) ⊆ U'`).
* `PullMap.obj_fibAct`: `Φ(μ(φ, w)) = μ'(F(φ), Φ(w))` in the form of `fibAct`.
* `PullMap.pull Λ' = Λ' ∘ Φ`, `PullMap.isWFunctor_pull`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **Two continuous lifts through `s` agree on an open set**: for continuous `a`, `b` on an open
`O` with `s ∘ a = s ∘ b`, the set where `a = b` is open (`s` is locally injective). -/
theorem isOpen_setOf_eq_of_src {α : Type*} [TopologicalSpace α] {O : Set α} (hO : IsOpen O)
    {a b : α → Mor} (ha : ContinuousOn a O) (hb : ContinuousOn b O)
    (hab : ∀ p ∈ O, X.src (a p) = X.src (b p)) : IsOpen {p | p ∈ O ∧ a p = b p} := by
  refine isOpen_iff_mem_nhds.2 fun p ⟨hp, he⟩ => ?_
  obtain ⟨V, hV, hpV, hinj⟩ := X.isLocalScDiffeo_src.isLocallyInjective (a p)
  have h1 : a ⁻¹' V ∈ 𝓝 p := (ha.continuousAt (hO.mem_nhds hp)).preimage_mem_nhds
    (hV.mem_nhds hpV)
  have h2 : b ⁻¹' V ∈ 𝓝 p := (hb.continuousAt (hO.mem_nhds hp)).preimage_mem_nhds
    (hV.mem_nhds (he ▸ hpV))
  filter_upwards [hO.mem_nhds hp, h1, h2] with q hq hq1 hq2
  exact ⟨hq, hinj hq1 hq2 (hab q hq)⟩

end EpGroupoid

namespace SBLocalization

open StrongBundle EpGroupoid

/-! ### The pull-back data -/

/-- **The data of a pull-back** (the common part of Theorems 13.4.1 and 13.4.4): a map
`Φ : W → W'` of strong bundles over ep-groupoids covering the functor `F : X → X'`
(`Φ(μ(φ, w)) = μ'(F(φ), Φ(w))`, Definition 8.3.2), a local strong bundle isomorphism over
every point of `X`, with `F` faithful. -/
structure PullMap (C A : SEP.{u}) where
  /-- The functor `F : X → X'` of the bases. -/
  ϕ : EpFunctor C.X A.X
  /-- The map `Φ : W → W'`. -/
  Φ : C.W → A.W
  isMap : C.E.IsMap A.E ϕ Φ
  isLocalIso : ∀ y : C.Obj, ∃ (U : Set C.Obj) (U' : Set A.Obj), y ∈ U ∧
    C.B.IsStrongBundleIsoOn A.B isMap.isStrongBundleMap U U'
  mor_injective : ∀ φ φ' : C.Mor, C.X.src φ = C.X.src φ' → C.X.tgt φ = C.X.tgt φ' →
    ϕ.mor φ = ϕ.mor φ' → φ = φ'

variable {A C : SEP.{u}}

namespace PullMap

variable (M : PullMap C A)

/-- **A strong bundle equivalence** (Definition 10.4.1) gives pull-back data. -/
def ofEquivalence {F : C ⟶ A} (hF : SEP.equivalences F) : PullMap C A where
  ϕ := SEP.Hom.ϕ F
  Φ := (SEP.Hom.Φ F).obj
  isMap := (sbe hF).isStrongBundleFunctor.isMap
  isLocalIso := (sbe hF).isLocalStrongBundleIso_obj
  mor_injective _ _ hs ht he := (sbe hF).isEquivalence_base.mor_injective hs ht he

@[simp] theorem ofEquivalence_ϕ {F : C ⟶ A} (hF : SEP.equivalences F) :
    (ofEquivalence hF).ϕ = SEP.Hom.ϕ F := rfl

@[simp] theorem ofEquivalence_Φ {F : C ⟶ A} (hF : SEP.equivalences F) :
    (ofEquivalence hF).Φ = (SEP.Hom.Φ F).obj := rfl

/-- **A proper strong bundle covering** (2021 Definition 8.5.9) gives pull-back data; the
faithfulness comes from Definition 8.5.1 (3) (`φ ↦ (F(φ), s(φ))` is injective). -/
def ofCovering {F : EpFunctor C.X A.X} {Φ : C.W → A.W}
    (h : C.E.IsProperStrongBundleCovering2021 A.E F Φ) : PullMap C A where
  ϕ := F
  Φ := Φ
  isMap := h.isMap
  isLocalIso := h.isLocalStrongBundleIso
  mor_injective φ φ' hs _ he := by
    let _ := MPolyfold.paracompactSpace_prod A.X.PMor C.X.PObj
    let _ := (A.X.PMor.prod C.X.PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct A.X.src F.obj)
    obtain ⟨g, hg⟩ := h.isProperCovering.isScDiffeo_fibredMap
    have e : F.fibredMap φ = F.fibredMap φ' := Subtype.ext (Prod.ext he hs)
    rw [← hg.left_inv φ (mem_univ _), ← hg.left_inv φ' (mem_univ _), e]

@[simp] theorem ofCovering_ϕ {F : EpFunctor C.X A.X} {Φ : C.W → A.W}
    (h : C.E.IsProperStrongBundleCovering2021 A.E F Φ) : (ofCovering h).ϕ = F := rfl

@[simp] theorem ofCovering_Φ {F : EpFunctor C.X A.X} {Φ : C.W → A.W}
    (h : C.E.IsProperStrongBundleCovering2021 A.E F Φ) : (ofCovering h).Φ = Φ := rfl

/-- `Φ` covers `F`: `P'(Φ(w)) = F(P(w))`. -/
theorem covers (w : C.W) : A.P (M.Φ w) = M.ϕ.obj (C.P w) :=
  M.isMap.isStrongBundleMap.covers w

/-- **The fibre maps `Φ_y : W_y → W'_{F(y)}` are linear homeomorphisms.** -/
def fiberEquiv (y : C.Obj) : C.P ⁻¹' {y} ≃L[ℝ] A.P ⁻¹' {M.ϕ.obj y} :=
  (Classical.choose_spec (Classical.choose_spec (M.isLocalIso y))).2.fiberEquiv
    (Classical.choose_spec (Classical.choose_spec (M.isLocalIso y))).1

@[simp] theorem fiberEquiv_apply (y : C.Obj) (v : C.P ⁻¹' {y}) :
    (M.fiberEquiv y v : A.W) = M.Φ v := rfl

/-- `Φ` is injective on the fibres. -/
theorem eq_of_obj_eq {w w₁ : C.W} (hP : C.P w = C.P w₁) (he : M.Φ w = M.Φ w₁) : w = w₁ := by
  have := (M.fiberEquiv (C.P w₁)).injective (a₁ := ⟨w, hP⟩) (a₂ := ⟨w₁, rfl⟩) (Subtype.ext he)
  exact congrArg Subtype.val this

/-- `F` is a local sc-diffeomorphism on objects. -/
theorem isLocalScDiffeo_obj : C.X.PObj.IsLocalScDiffeo A.X.PObj M.ϕ.obj := fun y => by
  obtain ⟨U, U', hy, hi⟩ := M.isLocalIso y
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  exact ⟨U, U', g, hy, hg⟩

/-! ### `μ` and `Φ` -/

/-- **`Φ(μ(φ, w)) = μ'(F(φ), Φ(w))`** in the form of `fibAct` (Definition 8.3.2). -/
theorem obj_fibAct {ψ : C.Mor} {v : C.W} (h : C.P v = C.X.src ψ) :
    M.Φ (fibAct ψ v) = fibAct (M.ϕ.mor ψ) (M.Φ v) := by
  have h' : A.P (M.Φ v) = A.X.src (M.ϕ.mor ψ) := by
    rw [M.covers, h, M.ϕ.src_mor]
  rw [fibAct_of h, fibAct_of h', M.isMap.map_μ ψ v h]

/-! ### The pulled-back sections -/

/-- **The pull-back of a section**: `pullSec s'(z) = Φ_z⁻¹(s'(F(z)))` where `s'(F(z))` lies over
`F(z)`, and `0_z` otherwise (the text: `Φ(sᵢ(z)) = s'ᵢ(F(z))`). -/
def pullSec (s' : A.Obj → A.W) (z : C.Obj) : C.W :=
  if h : A.P (s' (M.ϕ.obj z)) = M.ϕ.obj z then
    ((M.fiberEquiv z).symm ⟨s' (M.ϕ.obj z), h⟩ : C.P ⁻¹' {z})
  else fiberZero C.P z

theorem P_pullSec (s' : A.Obj → A.W) (z : C.Obj) : C.P (M.pullSec s' z) = z := by
  unfold pullSec
  split_ifs
  · exact ((M.fiberEquiv z).symm _).2
  · exact isSection_fiberZero z

theorem obj_pullSec {s' : A.Obj → A.W} {z : C.Obj} (h : A.P (s' (M.ϕ.obj z)) = M.ϕ.obj z) :
    M.Φ (M.pullSec s' z) = s' (M.ϕ.obj z) := by
  unfold pullSec
  rw [dif_pos h, ← fiberEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- `pullSec s'(z) = w` iff `s'(F(z)) = Φ(w)`, for `w` over `z`. -/
theorem pullSec_eq_iff {s' : A.Obj → A.W} {z : C.Obj} (h : A.P (s' (M.ϕ.obj z)) = M.ϕ.obj z)
    {w : C.W} (hw : C.P w = z) : M.pullSec s' z = w ↔ s' (M.ϕ.obj z) = M.Φ w := by
  constructor
  · rintro rfl; exact (M.obj_pullSec h).symm
  · intro e
    exact M.eq_of_obj_eq ((M.P_pullSec s' z).trans hw.symm) ((M.obj_pullSec h).trans e)

/-- **The pull-back of an sc⁺-section is an sc⁺-section**: if `s'` is an sc⁺-section of `P'` on
`U'` and `F(U) ⊆ U'` for an open `U`, then `pullSec s'` is one of `P` on `U` (on the level
`[1]`, locally `Ψ₁ ∘ s'[1] ∘ F` with `Ψ₁` the inverse of the local strong bundle isomorphism). -/
theorem isScPlusSectionOn_pullSec {s' : A.Obj → A.W} {U' : Set A.Obj}
    (hs' : IsScPlusSectionOn A s' U') {U : Set C.Obj} (hU : IsOpen U)
    (hUU' : MapsTo M.ϕ.obj U U') : IsScPlusSectionOn C (M.pullSec s') U := by
  refine IsScPlusSectionOn.of_locally hU fun y hy => ?_
  obtain ⟨U₀, U₀', hyU₀, hi⟩ := M.isLocalIso y
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
  obtain ⟨G', hG'val, hG'sm⟩ := hs'.2
  have hFs := M.isMap.isStrongBundleMap
  set O : Set C.Obj := U₀ ∩ U with hOdef
  have hO : IsOpen O := hg.isOpen_source.inter hU
  have hmem : ∀ z ∈ O, A.P (A.B.oneVal (G' (M.ϕ.obj z))) ∈ U₀' := fun z hz => by
    rw [hG'val _ (hUU' hz.2), hs'.1 _ (hUU' hz.2)]; exact hg.mapsTo hz.1
  have hval : ∀ z ∈ O, C.B.oneVal (Ψ₁ (G' (M.ϕ.obj z))) = M.pullSec s' z := fun z hz => by
    have hP : C.P (C.B.oneVal (Ψ₁ (G' (M.ϕ.obj z)))) = z := by
      rw [StrongBundle.IsStrongBundleIsoOn.P_inv_one (h := hFs) hg hΨ₁ (hmem z hz),
        hG'val _ (hUU' hz.2), hs'.1 _ (hUU' hz.2), hg.left_inv z hz.1]
    have hΦ : M.Φ (C.B.oneVal (Ψ₁ (G' (M.ϕ.obj z)))) = s' (M.ϕ.obj z) := by
      have e := congrArg A.B.oneVal (hΨ₁.right_inv _ (hmem z hz))
      rw [oneVal_oneRestrict] at e
      exact e.trans (hG'val _ (hUU' hz.2))
    exact ((M.pullSec_eq_iff (hs'.1 _ (hUU' hz.2)) hP).2 hΦ.symm).symm
  refine ⟨O, hO, ⟨hyU₀, hy⟩, inter_subset_right, fun z _ => M.P_pullSec s' z,
    Ψ₁ ∘ G' ∘ M.ϕ.obj, fun z hz => hval z hz, ?_⟩
  exact MPolyfold.IsScSmoothOn.comp hΨ₁.isScSmoothOn_inv
    (MPolyfold.IsScSmoothOn.comp hG'sm (hg.isScSmoothOn.mono hO inter_subset_left)
      fun z hz => hUU' hz.2) fun z hz => hmem z hz

/-! ### The pulled-back functor -/

/-- **The pull-back `Φ^*Λ' = Λ' ∘ Φ`.** -/
def pull (Λ' : A.W → ℚ≥0) : C.W → ℚ≥0 := Λ' ∘ M.Φ

theorem pull_apply (Λ' : A.W → ℚ≥0) (w : C.W) : M.pull Λ' w = Λ' (M.Φ w) := rfl

/-- `Φ^*Λ'` is a functor (`Φ` commutes with the actions). -/
theorem isWFunctor_pull {Λ' : A.W → ℚ≥0} (h : IsWFunctor A Λ') : IsWFunctor C (M.pull Λ') := by
  rintro ⟨⟨γ, w⟩, hq⟩
  change Λ' (M.Φ (C.E.μ ⟨(γ, w), hq⟩)) = Λ' (M.Φ w)
  rw [M.isMap.map_μ γ w hq]
  exact h _

/-- For an equivalence, `PullMap.pull` is the pull-back `pullMult F` of Chapter 11. -/
theorem pull_ofEquivalence {F : C ⟶ A} (hF : SEP.equivalences F) (Λ' : A.W → ℚ≥0) :
    (ofEquivalence hF).pull Λ' = pullMult F Λ' := rfl

end PullMap

end SBLocalization

end Polyfold
