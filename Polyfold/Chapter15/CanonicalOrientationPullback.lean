import Polyfold.Chapter15.CanonicalOrientationEquivalence
import Polyfold.Chapter7.ProperSubsets

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702, **Theorem 15.4.1** and **Definition 15.4.2** (2017: Theorem 15.6, Definition 15.7),
read along a strong bundle equivalence (Definition 10.4.1), with Chapter 11's pull-back of
orientations (Theorem 11.3.5, Definition 11.3.6) and the identification of orientations of
Theorem 12.5.7.

# The pull-back of a canonical orientation is canonical

## The text, paraphrased

(p. 702) For an oriented sc-Fredholm section functor `(f, o)` and an sc⁺-multisection `Λ` in
good position, `Θ = Λ ∘ f` carries the canonical orientation `T̂_((f, o), Λ)`, computed in local
branching structures whose sheets are the solution sets `Mᵢ = {f = sᵢ}` of a local
sc⁺-section structure `(sᵢ, σᵢ)` of `Λ`, oriented by `o`.  (§16.6, p. 739) Two models of the
orientation differ by strong bundle equivalences `Φ : W → W'` covering `ϕ : X → X'`, along
which `f = Φ^* f'`, `Λ = Λ' ∘ Φ`, `o = h^* o'`; the text uses that `T̂` is carried along.

## What is formalized (namespace `Polyfold.SBLocalization`)

For a strong bundle equivalence `h : A.E.IsStrongBundleEquivalence A'.E ϕ Φ`, `f = h^* f'`,
`Λ = Λ' ∘ Φ` and `o = h^* o'` (`pullOr`):

* `subDeriv_congr_sec`: the chart operator `D((f̂ − ŝ) ∘ r)` depends only on `s` over the domain
  of the chart.
* `KernelBranching.pullEquiv`: a local branching structure `K'` of `Λ' ∘ f'` at `ϕ(x)` described
  by kernels is carried to one of `Λ ∘ f` at `x`: the sections `Ψ ∘ sᵢ ∘ ϕ` of the local
  strong bundle isomorphism of `h` at `x`, the sheets `ϕ⁻¹(Mᵢ')` on the domain of a natural
  representation; `T_yMᵢ = ker (f − sᵢ)'(y)` and the onto condition are read in every chart
  through the inverse local isomorphism (`LocalIso.symm`).
* `KernelBranching.orTangent_pullOr`: `(T_yMᵢ, o_{i,y}) = (Tϕ)⁻¹ (T_{ϕ y}Mᵢ', o'_{i,ϕ y})`
  sheet by sheet, and `frames_pullEquiv`, `framesContinuous_pullEquiv`: the continuity of
  `y ↦ o'_{i,y}` along the sheets is carried along.
* **`IsCanonicalFor.pullSection`**: if `T̂'` is canonical for `(Λ', o')`, then `ϕ^* T̂'` is
  canonical for `(Λ' ∘ Φ, h^* o')` (Definition 15.4.2), with the same dimension.
* **`IsCanonicalFor.pullSection_eq_pullSection_of_canonical`**: over a diagram
  `W₁ ←Φ₁ W'' →Φ₂ W₂` with `Λ₁ ∘ Φ₁ = Λ₂ ∘ Φ₂` and `Φ₁^* o₁ = Φ₂^* o₂`, the canonical
  orientations satisfy `ϕ₁^* T̂₁ = ϕ₂^* T̂₂`, without a hypothesis on `W''`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

/-! ### The chart operator depends only on the section over the chart -/

section Congr

variable {A : SEP.{u}} {f : A.Obj → A.W}

/-- **`D((f̂ − ŝ) ∘ r)(z)` depends only on `s` over the domain of the chart.** -/
theorem subDeriv_congr_sec {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    {s₁ s₂ : A.Obj → A.W} (hf : A.B.IsScSmoothSection f) {O : Set A.Obj}
    (hs₁ : IsScPlusSectionOn A s₁ O) (hsub : c.φ.source ⊆ O) (h12 : EqOn s₁ s₂ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z ∈ c.U) :
    subDeriv c f s₂ z = subDeriv c f s₁ z := by
  have h1 := isSc1_sub_comp_r hf hs₁ hc hsub
  have hEq : EqOn ((fun y => c.principal f y - c.principal s₁ y) ∘ r c.R)
      ((fun y => c.principal f y - c.principal s₂ y) ∘ r c.R) c.U := by
    intro u hu
    have huO : r c.R u ∈ c.φ.model.O := c.r_mem_O hu
    have hw : c.φ.symm (r c.R u) ∈ c.φ.source := c.φ.symm_mapsTo huO
    change c.principal f (r c.R u) - c.principal s₁ (r c.R u) =
      c.principal f (r c.R u) - c.principal s₂ (r c.R u)
    unfold StrongBundleChart.principal
    rw [h12 hw]
  exact IsSc1.scDeriv_eqOn (h1.isSc1With_scDeriv.congr hEq)
    (c.relOpen.isScDomain.uniqueDiffWithinAt 1) hz

/-- The operator `subOp` of two sections that agree over the chart. -/
theorem coe_subOp_congr_sec (hf : A.B.IsScSmoothSection f) {s₁ s₂ : A.Obj → A.W}
    {O₁ O₂ : Set A.Obj} (hs₁ : IsScPlusSectionOn A s₁ O₁) (hs₂ : IsScPlusSectionOn A s₂ O₂)
    {y : A.Obj} (p : ChartPoint A.B y) (hsub₁ : p.c.φ.source ⊆ O₁) (hsub₂ : p.c.φ.source ⊆ O₂)
    (hfs₁ : f y = s₁ y) (hfs₂ : f y = s₂ y) (h12 : EqOn s₁ s₂ p.c.φ.source) (v : ↥p.T) :
    ((subOp hf hs₂ p hsub₂ hfs₂ v).1 : p.c.F 0) = (subOp hf hs₁ p hsub₁ hfs₁ v).1 := by
  rw [coe_subOp, coe_subOp, subDeriv_congr_sec p.isChart hf hs₁ hsub₁ h12 p.mem_U]

end Congr

/-! ### A structure described by kernels carried along the equivalence -/

section Equiv

variable {A A' : SEP.{u}} {ϕ : EpFunctor A.X A'.X}
  {Φ : EpFunctor A.E.toEpGroupoid A'.E.toEpGroupoid}
  (h : A.E.IsStrongBundleEquivalence A'.E ϕ Φ)
  {f : A.Obj → A.W} {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hpb : f = h.pullback f')
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)

include hF' hpb in
/-- Near `a`, `f(z) = Ψ(s'(ϕ z))` iff `f'(ϕ z) = s'(ϕ z)`. -/
theorem eq_isoSec_iff_loc (a : A.Obj) {z : A.Obj} (hz : z ∈ h.locSet a) {s' : A'.Obj → A'.W}
    (hs' : A'.P (s' (ϕ.obj z)) = ϕ.obj z) :
    f z = isoSec (h.locIso a) s' z ↔ f' (ϕ.obj z) = s' (ϕ.obj z) := by
  set L := h.locIso a with hL
  have e2 : f z = L.Ψ (f' (ϕ.obj z)) := h.eqOn_loc hpb hF'.2.isScSmooth.1 a hz
  have hU' : ϕ.obj z ∈ h.locSet' a := L.base.mapsTo hz
  change f z = L.Ψ (s' (ϕ.obj z)) ↔ _
  rw [e2]
  constructor
  · intro h0
    have h1 := congrArg L.Φ h0
    rwa [L.zero.right_inv _ (show A'.P (f' (ϕ.obj z)) ∈ h.locSet' a by
        rw [hF'.1.1.1 (ϕ.obj z)]; exact hU'),
      L.zero.right_inv _ (show A'.P (s' (ϕ.obj z)) ∈ h.locSet' a by rw [hs']; exact hU')] at h1
  · intro h0
    rw [h0]

variable {Λ' : A'.W → ℚ≥0} {x : A.Obj} (K' : KernelBranching A' f' Λ' (ϕ.obj x))
  {R : A.X.NaturalRep x} (hRU : R.U ⊆ isoSet (h.locIso x) K'.U)

include hF' hpb hRU in
theorem mem_M_iff_pull (i : K'.ι) {z : A.Obj} (hzR : z ∈ R.U) :
    f z = isoSec (h.locIso x) (K'.s i) z ↔ ϕ.obj z ∈ K'.M i := by
  have hϕU : ϕ.obj z ∈ K'.U := (hRU hzR).2
  rw [eq_isoSec_iff_loc h hF' hpb x (hRU hzR).1 ((K'.isScPlus i).1 _ (K'.U_subset hϕU)), K'.M_eq i]
  exact ⟨fun h0 => ⟨hϕU, h0⟩, fun h0 => h0.2⟩

include hF' hpb hRU in
/-- The carried sheet `{z ∈ R.U | f z = Ψ(sᵢ(ϕ z))}` is `g(Mᵢ' ∩ U'(x)) ∩ R.U`. -/
theorem sep_eq_image_pull (i : K'.ι) :
    {z ∈ R.U | f z = isoSec (h.locIso x) (K'.s i) z} =
      (h.locIso x).g '' (K'.M i ∩ h.locSet' x) ∩ R.U := by
  set L := h.locIso x with hL
  ext z
  constructor
  · rintro ⟨hzR, hz⟩
    have hzU := (hRU hzR).1
    exact ⟨⟨ϕ.obj z, ⟨(mem_M_iff_pull h hF' hpb K' hRU i hzR).1 hz, L.base.mapsTo hzU⟩,
      L.base.left_inv z hzU⟩, hzR⟩
  · rintro ⟨⟨w, ⟨hwM, hwU'⟩, rfl⟩, hzR⟩
    refine ⟨hzR, (mem_M_iff_pull h hF' hpb K' hRU i hzR).2 ?_⟩
    have e : ϕ.obj (L.g w) = w := L.base.right_inv w hwU'
    rw [e]
    exact hwM

open Classical in
include hRU in
/-- The carried local sc⁺-section structure of `Λ = Λ' ∘ Φ` on `U(x) ∩ ϕ⁻¹(O(K') ∩ U'(x))`. -/
theorem isLocalRepOn_pull :
    IsLocalRepOn A (fun w => Λ' (Φ.obj w)) (isoSet (h.locIso x) (K'.O ∩ h.locSet' x))
      (fun j => isoSec (h.locIso x) (K'.sAll j)) K'.σAll :=
  isLocalRepOn_isoSec (h.locIso x) (fun _ _ => rfl) (K'.isOpen_O.inter (h.isOpen_locSet' x))
    inter_subset_right (K'.isLocalRep.mono (K'.isOpen_O.inter (h.isOpen_locSet' x))
      inter_subset_left)

include hF hF' hpb hRU in
/-- **`T_yMᵢ = ker (f − sᵢ)'(y)` and `(f − sᵢ)'(y)` onto, for the carried sheets, in every
chart**: the chart `c` is carried to `W'` through the inverse local isomorphism, where the
structure `K'` gives both properties. -/
theorem chartVec_image_pull (i : K'.ι) {y : A.Obj} (hyR : y ∈ R.U)
    (hy : f y = isoSec (h.locIso x) (K'.s i) y) (c : StrongBundleChart A.X.PObj A.P)
    (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ isoSet (h.locIso x) (K'.O ∩ h.locSet' x))
    (hyc : y ∈ c.φ.source) (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ y) :
    chartVec c.isChart '' A.X.PObj.submanifoldTangent
        {z ∈ R.U | f z = isoSec (h.locIso x) (K'.s i) z} y =
      kerSet c f (isoSec (h.locIso x) (K'.s i)) z ∧
    ChartOnto c (subDeriv c f (isoSec (h.locIso x) (K'.s i)) z) z := by
  set L := h.locIso x with hL
  have hyU : y ∈ h.locSet x := (hRU hyR).1
  have hϕM : ϕ.obj y ∈ K'.M i := (mem_M_iff_pull h hF' hpb K' hRU i hyR).1 hy
  have hcU : c.φ.source ⊆ h.locSet x := fun w hw => (hsub hw).1
  set c'' := L.symm.transportChart c hcU with hc''def
  have hc'' : A'.B.IsChart c'' := L.symm.isChart_transportChart c hcU hc
  have hgy : L.g (ϕ.obj y) = y := L.base.left_inv y hyU
  have hϕU' : ϕ.obj y ∈ h.locSet' x := L.base.mapsTo hyU
  have hyc'' : ϕ.obj y ∈ c''.φ.source := ⟨hϕU', by
    change L.g (ϕ.obj y) ∈ c.φ.source
    rw [hgy]; exact hyc⟩
  have hsub'' : c''.φ.source ⊆ K'.O := fun w hw => by
    have h1 := hsub hw.2
    have h2 : L.ϕ (L.g w) = w := L.base.right_inv w hw.1
    have h3 : L.ϕ (L.g w) ∈ K'.O := h1.2.1
    rwa [h2] at h3
  have hz'' : c''.φ.model.E.toBase 1 z = c''.φ (ϕ.obj y) := by
    change c.φ.model.E.toBase 1 z = c.φ (L.g (ϕ.obj y))
    rw [hgy]; exact hz
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U :=
    mem_U_of_mem_O c.isRetraction (by rw [c.r_image, hz]; exact c.φ.mapsTo_model y hyc)
  have hfL'' : EqOn f' (L.symm.Ψ ∘ f ∘ L.symm.ϕ) (h.locSet' x) := fun w hw => by
    change f' w = L.Φ (f (L.g w))
    have e : f (L.g w) = L.Ψ (f' (L.ϕ (L.g w))) :=
      h.eqOn_loc hpb hF'.2.isScSmooth.1 x (L.base.mapsTo_inv hw)
    rw [e, L.base.right_inv w hw, L.zero.right_inv _ (show A'.P (f' w) ∈ h.locSet' x by
      rw [hF'.1.1.1 w]; exact hw)]
  have hsI := (isLocalRepOn_pull h K' (R := R) hRU).2.1 (K'.idx i)
  have e1 : subDeriv c'' f' (isoSec L.symm (isoSec L (K'.s i))) z =
      subDeriv c f (isoSec L (K'.s i)) z :=
    subDeriv_transportChart L.symm hcU hF.2.isScSmooth hfL'' hsI hc hsub hzU
  have h12 : EqOn (K'.s i) (isoSec L.symm (isoSec L (K'.s i))) c''.φ.source := fun w hw => by
    change K'.s i w = L.Φ (L.Ψ (K'.s i (L.ϕ (L.g w))))
    rw [L.base.right_inv w hw.1, L.zero.right_inv _ (show A'.P (K'.s i w) ∈ h.locSet' x by
      rw [(K'.isScPlus i).1 w (hsub'' hw)]; exact hw.1)]
  have e2 : subDeriv c'' f' (isoSec L.symm (isoSec L (K'.s i))) z = subDeriv c'' f' (K'.s i) z :=
    subDeriv_congr_sec hc'' hF'.2.isScSmooth (K'.isScPlus i) hsub'' h12 hzU
  have hD : subDeriv c'' f' (K'.s i) z = subDeriv c f (isoSec L (K'.s i)) z := e2.symm.trans e1
  have hK1 := K'.tangent_eq i (ϕ.obj y) hϕM c'' hc'' hsub'' hyc'' z hz''
  have hK2 := K'.onto i (ϕ.obj y) hϕM c'' hc'' hsub'' hyc'' z hz''
  refine ⟨?_, ?_⟩
  · have hker : kerSet c'' f' (K'.s i) z = kerSet c f (isoSec L (K'.s i)) z := by
      unfold kerSet; rw [hD]; rfl
    rw [← hker, ← hK1, sep_eq_image_pull h hF' hpb K' hRU i,
      submanifoldTangent_inter_isOpen R.isOpen_U hyR]
    have hA : A'.X.PObj.IsSmoothSubmanifold (K'.M i ∩ h.locSet' x) :=
      (K'.isSmoothSubmanifold i).inter_isOpen L.isOpen_U'
    have ht := submanifoldTangent_image_of_isScDiffeoOn L.base.symm hA inter_subset_right
      ⟨hϕM, hϕU'⟩
    rw [hgy] at ht
    rw [ht, submanifoldTangent_inter_isOpen L.isOpen_U' hϕU', image_image]
    refine image_congr fun α hα => ?_
    have hα1 : A'.X.PObj.levelVal 1 (A'.X.PObj.tangentProj α) = ϕ.obj y := hα.1
    exact chartVec_tangentMapOn_of_isScDiffeoOn L.base.symm c.isChart (by
      rw [hα1]
      exact ⟨hϕU', by change L.g (ϕ.obj y) ∈ c.φ.source; rw [hgy]; exact hyc⟩)
  · rw [← hD]; exact hK2

variable (hRP : A.X.HasPropernessProperty R.U)

open Classical in
include hF hF' hpb hRU hRP in
/-- **A structure described by kernels carried along the equivalence** (the step "the text uses
that `T̂` is carried along"): from `K'` at `ϕ(x)` and a natural representation `R` of `G_x` with
the properness property on `R.U ⊆ U(x) ∩ ϕ⁻¹(U(K'))`, the sheets
`Mᵢ = {z ∈ R.U | f(z) = Ψ(sᵢ'(ϕ z))} = R.U ∩ ϕ⁻¹(Mᵢ')` of the carried local sc⁺-section
structure, with the weights and dimensions of `K'`. -/
def KernelBranching.pullEquiv : KernelBranching A f (fun w => Λ' (Φ.obj w)) x where
  U := R.U
  isOpen_U := R.isOpen_U
  mem_U := R.mem_U
  ι := K'.ι
  M i := {z ∈ R.U | f z = isoSec (h.locIso x) (K'.s i) z}
  subset_U _ := sep_subset _ _
  isSmoothSubmanifold i := by
    rw [sep_eq_image_pull h hF' hpb K' hRU i]
    exact (((K'.isSmoothSubmanifold i).inter_isOpen (h.isOpen_locSet' x)).image_of_isScDiffeoOn
      (h.locIso x).base.symm inter_subset_right).inter_isOpen R.isOpen_U
  mem_M i := ⟨R.mem_U, (mem_M_iff_pull h hF' hpb K' hRU i R.mem_U).2 (K'.mem_M i)⟩
  isProperMap i := by
    rw [isProperMap_inclusion_iff]
    have hfc : Continuous f := continuousOn_univ.1 hF.2.isScSmooth.2.continuousOn
    have hRO : R.U ⊆ isoSet (h.locIso x) (K'.O ∩ h.locSet' x) := fun z hz =>
      ⟨(hRU hz).1, K'.U_subset (hRU hz).2, (h.locIso x).base.mapsTo (hRU hz).1⟩
    have hcs : ContinuousOn (isoSec (h.locIso x) (K'.s i)) R.U :=
      ((isLocalRepOn_pull h K' (R := R) hRU).2.1 (K'.idx i)).continuousOn.mono hRO
    have h1 : Continuous fun p : R.U => f p := hfc.comp continuous_subtype_val
    have h2 : Continuous fun p : R.U => isoSec (h.locIso x) (K'.s i) p :=
      hcs.comp_continuous continuous_subtype_val fun p => p.2
    convert isClosed_eq h1 h2 using 1
    ext p
    simp
  σ := K'.σ
  σ_pos := K'.σ_pos
  eq_sum y hy := by
    have hϕU : ϕ.obj y ∈ K'.U := (hRU hy).2
    change ((Λ' (Φ.obj (f y)) : ℚ≥0) : ℚ) = _
    rw [multisection_pullback_apply h hF' hpb (Λ' := Λ') y, K'.eq_sum (ϕ.obj y) hϕU]
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ⟨hy, (mem_M_iff_pull h hF' hpb K' hRU i hy).2 h1⟩ h2
    · exact absurd ((mem_M_iff_pull h hF' hpb K' hRU i hy).1 h2.2) h1
    · rfl
  rep := R
  U_eq := rfl
  hasPropernessProperty := hRP
  hasTameInducedStructure i := by
    rw [sep_eq_image_pull h hF' hpb K' hRU i]
    have hA : A'.X.PObj.IsSmoothSubmanifold (K'.M i ∩ h.locSet' x) :=
      (K'.isSmoothSubmanifold i).inter_isOpen (h.isOpen_locSet' x)
    exact MPolyfold.HasTameInducedStructure.inter_isOpen
      (hA.image_of_isScDiffeoOn (h.locIso x).base.symm inter_subset_right)
      (MPolyfold.HasTameInducedStructure.image_of_isScDiffeoOn hA
        (MPolyfold.HasTameInducedStructure.inter_isOpen (K'.isSmoothSubmanifold i)
          (K'.hasTameInducedStructure i) (h.isOpen_locSet' x))
        (h.locIso x).base.symm inter_subset_right) R.isOpen_U
  dim := K'.dim
  isSubmanifoldOfDim i := by
    rw [sep_eq_image_pull h hF' hpb K' hRU i]
    exact (((K'.isSubmanifoldOfDim i).inter_isOpen (h.isOpen_locSet' x)).image_isScDiffeoOn
      (h.locIso x).base.symm inter_subset_right).inter_isOpen R.isOpen_U
  O := isoSet (h.locIso x) (K'.O ∩ h.locSet' x)
  isOpen_O := isOpen_isoSet _ (K'.isOpen_O.inter (h.isOpen_locSet' x))
  U_subset := fun z hz =>
    ⟨(hRU hz).1, K'.U_subset (hRU hz).2, (h.locIso x).base.mapsTo (hRU hz).1⟩
  k := K'.k
  sAll j := isoSec (h.locIso x) (K'.sAll j)
  σAll := K'.σAll
  isLocalRep := isLocalRepOn_pull h K' hRU
  idx := K'.idx
  idx_injective := K'.idx_injective
  σ_eq := K'.σ_eq
  mem_range j z hz hfz := K'.mem_range j (ϕ.obj z) (hRU hz).2
    ((eq_isoSec_iff_loc h hF' hpb x (hRU hz).1
      ((K'.isLocalRep.2.1 j).1 _ (K'.U_subset (hRU hz).2))).1 hfz)
  M_eq _ := rfl
  smooth i y hy := h.smooth_of_obj (K'.smooth i _ ((mem_M_iff_pull h hF' hpb K' hRU i hy.1).1 hy.2))
  tangent_eq i y hy c hc hsub hyc z hz :=
    (chartVec_image_pull h hF hF' hpb K' hRU i hy.1 hy.2 c hc hsub hyc z hz).1
  onto i y hy c hc hsub hyc z hz :=
    (chartVec_image_pull h hF hF' hpb K' hRU i hy.1 hy.2 c hc hsub hyc z hz).2

/-! ### The oriented tangent spaces of the sheets, sheet by sheet -/

include h in
/-- The carried sections of two local isomorphisms of the equivalence agree where both are
defined. -/
theorem isoSec_locIso_eq {a b w : A.Obj} (hwa : w ∈ h.locSet a) (hwb : w ∈ h.locSet b)
    {s' : A'.Obj → A'.W} (hs' : A'.P (s' (ϕ.obj w)) = ϕ.obj w) :
    isoSec (h.locIso a) s' w = isoSec (h.locIso b) s' w := by
  set La := h.locIso a
  set Lb := h.locIso b
  have hb' : A'.P (s' (ϕ.obj w)) ∈ h.locSet' b := by rw [hs']; exact Lb.base.mapsTo hwb
  have hP : A.P (Lb.Ψ (s' (ϕ.obj w))) ∈ h.locSet a := by
    rw [Lb.covers_inv _ hb', hs']
    have e : Lb.g (Lb.ϕ w) = w := Lb.base.left_inv w hwb
    exact e.symm ▸ hwa
  have hΦ : La.Φ (Lb.Ψ (s' (ϕ.obj w))) = s' (ϕ.obj w) := Lb.zero.right_inv _ hb'
  change La.Ψ (s' (ϕ.obj w)) = Lb.Ψ (s' (ϕ.obj w))
  exact (congrArg La.Ψ hΦ).symm.trans (La.zero.left_inv _ hP)

include hpb in
/-- **One oriented kernel along the equivalence**: in a chart point `q` equal to the carried
chart point of `p`, for a local section `s` agreeing over the chart with `Ψ ∘ s' ∘ ϕ`, the
oriented kernel `(ker (f − s)'(y), o_y)` for the carried orientation is the image under `(Tϕ)⁻¹`
of `(ker (f' − s')'(ϕ y), o'_{ϕ y})`. -/
theorem linOrTangent_pullOr_of_eq_mpullPt {y : A.Obj} (hys : y ∈ A.X.PObj.smoothSet)
    (hys' : ϕ.obj y ∈ A'.X.PObj.smoothSet)
    (o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx f' hF'.2 x hs)
    (p : ChartPoint A'.B (ϕ.obj y)) (hp : p.c.φ.source ⊆ h.locSet' y)
    {s' : A'.Obj → A'.W} {O' : Set A'.Obj} (hO' : IsOpen O') (hO's : O' ⊆ h.locSet' y)
    (hs' : IsScPlusSectionOn A' s' O') (hsub' : p.c.φ.source ⊆ O')
    {s : A.Obj → A.W} {O : Set A.Obj} (hs : IsScPlusSectionOn A s O) (q : ChartPoint A.B y)
    (hq : q = (h.locIso y).mpullPt p hp (h.mem_locSet y) rfl) (hsubq : q.c.φ.source ⊆ O)
    (hss : EqOn (isoSec (h.locIso y) s') s q.c.φ.source) (hfs : f y = s y)
    (hfs' : f' (ϕ.obj y) = s' (ϕ.obj y))
    (hmem : subOp hF.2.isScSmooth hs q hsubq hfs ∈ q.linSet f)
    (hmem' : subOp hF'.2.isScSmooth hs' p hsub' hfs' ∈ p.linSet f') :
    linOrTangent hF.2 q ((orPt A.B y hys).orTransfer q hF.2 hys
        (h.pullOr hF hF' hpb hsec hsec' o' y hys)) ⟨_, hmem⟩ =
      (linOrTangent hF'.2 p ((orPt A'.B _ hys').orTransfer p hF'.2 hys' (o' _ hys'))
        ⟨_, hmem'⟩).map (fibreInv ϕ.tangent.obj y) := by
  subst hq
  set L := h.locIso y with hL
  have hlin : (L.mpullPt p hp (h.mem_locSet y) rfl).linSet f = p.linSet f' :=
    StrongBundle.LocalIso.linSet_mpullPt hF.2 hF'.2 (h.eqOn_loc hpb hF'.2.isScSmooth.1 y) hsec
      hsec' hys hys'
  change linOrTangent hF.2 _ ((orPt A.B y hys).orTransfer _ hF.2 hys
      (h.orEqv hF hF' hpb hsec hsec' y hys (o' (ϕ.obj y) (h.smooth_obj hys)))) _ = _
  rw [orTransfer_mpullPt_orEqv h hF hF' hpb hsec hsec' hys p hp hlin]
  have hsubI : (L.mpullPt p hp (h.mem_locSet y) rfl).c.φ.source ⊆ isoSet L O' :=
    fun z hz => ⟨hz.1, hsub' hz.2⟩
  have hymem : y ∈ (L.mpullPt p hp (h.mem_locSet y) rfl).c.φ.source :=
    (L.mpullPt p hp (h.mem_locSet y) rfl).mem_source
  have hfsI : f y = isoSec L s' y := hfs.trans (hss hymem).symm
  have hτ := fun (α' : A'.X.PObj.TangentSpace)
      (hα' : A'.X.PObj.levelVal 1 (A'.X.PObj.tangentProj α') = ϕ.obj y) =>
    fibreInv_tangent_obj_chartVec h y hp p.mem_source hα'
  exact linOrTangent_mconj hF'.2 hF.2 p (L.mpullPt p hp (h.mem_locSet y) rfl)
    (fibreInv ϕ.tangent.obj y) (L.mcastT p hp (h.mem_locSet y) rfl)
    (L.mcastK p hp (h.mem_locSet y) rfl)
    (ContinuousLinearEquiv.refl ℝ (p.c.φ.model.E 0)) (fun _ => rfl)
    (fun α' hα' => ⟨(hτ α' hα').1, (hτ α' hα').2⟩)
    (fun α hα => exists_fibreInv_tangent_obj_eq h y hα)
    (StrongBundle.LocalIso.mcastT_mem hlin) _ _ _
    (fun v => Subtype.ext ((coe_subOp_congr_sec hF.2.isScSmooth
      (isScPlusSectionOn_isoSec L hO' hO's hs') hs _ hsubI hsubq hfsI hfs hss v).trans
      (subOp_mpullPt h hF hF' hpb hO' hO's hs' p hp hsub' hsubI hfsI hfs' v)))

variable (hRP : A.X.HasPropernessProperty R.U)

include hpb in
/-- **`(T_yMᵢ, o_{i,y}) = (Tϕ)⁻¹ (T_{ϕ y}Mᵢ', o'_{i,ϕ y})`** for the carried structure, sheet by
sheet. -/
theorem KernelBranching.orTangent_pullEquiv
    (o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx f' hF'.2 x hs) (i : K'.ι) {y : A.Obj}
    (hy : y ∈ (KernelBranching.pullEquiv h hF hF' hpb K' hRU hRP).M i) :
    (KernelBranching.pullEquiv h hF hF' hpb K' hRU hRP).orTangent hF.2 hsec
        (h.pullOr hF hF' hpb hsec hsec' o') i y =
      (K'.orTangent hF'.2 hsec' o' i (ϕ.obj y)).map (fibreInv ϕ.tangent.obj y) := by
  set K := KernelBranching.pullEquiv h hF hF' hpb K' hRU hRP with hK
  set L := h.locIso y with hLdef
  have hys : y ∈ A.X.PObj.smoothSet := K.smooth i y hy
  have hys' : ϕ.obj y ∈ A'.X.PObj.smoothSet := h.smooth_obj hys
  have hϕM : ϕ.obj y ∈ K'.M i := (mem_M_iff_pull h hF' hpb K' hRU i hy.1).1 hy.2
  have hgy : L.g (ϕ.obj y) = y := L.base.left_inv y (h.mem_locSet y)
  have hG : IsOpen (h.locSet' y ∩ L.g ⁻¹' K.O) :=
    L.base.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage L.isOpen_U' K.isOpen_O
  have hV : IsOpen (K'.O ∩ (h.locSet' y ∩ L.g ⁻¹' K.O)) := K'.isOpen_O.inter hG
  have hyV : ϕ.obj y ∈ K'.O ∩ (h.locSet' y ∩ L.g ⁻¹' K.O) :=
    ⟨K'.mem_O hϕM, h.obj_mem_locSet' y, by rw [mem_preimage, hgy]; exact K.mem_O hy⟩
  set c' := (orChart A'.B (ϕ.obj y)).restrictInter hV with hc'def
  have hc' : A'.B.IsChart c' :=
    StrongBundle.IsChart.restrictInter hV (isChart_orChart (B := A'.B) _)
  have hyc' : ϕ.obj y ∈ c'.φ.source :=
    StrongBundleChart.mem_restrictInter_source _ hV (mem_orChart _) hyV
  have hcV : c'.φ.source ⊆ K'.O ∩ (h.locSet' y ∩ L.g ⁻¹' K.O) :=
    StrongBundleChart.restrictInter_source_subset (orChart A'.B (ϕ.obj y)) hV
  have hsubK' : c'.φ.source ⊆ K'.O := fun z hz => (hcV hz).1
  have hsubU' : c'.φ.source ⊆ h.locSet' y := fun z hz => (hcV hz).2.1
  have hc : A.B.IsChart (L.transportChart c' hsubU') := L.isChart_transportChart c' hsubU' hc'
  have hyc : y ∈ (L.transportChart c' hsubU').φ.source := ⟨h.mem_locSet y, hyc'⟩
  have hsubK : (L.transportChart c' hsubU').φ.source ⊆ K.O := fun z hz => by
    have h1 : L.g (L.ϕ z) ∈ K.O := (hcV hz.2).2.2
    rwa [L.base.left_inv z hz.1] at h1
  have hfs : f y = K.s i y := K.eq_of_mem hy
  have hfs' : f' (ϕ.obj y) = K'.s i (ϕ.obj y) := K'.eq_of_mem hϕM
  have hss : EqOn (isoSec L (K'.s i)) (K.s i) (L.transportChart c' hsubU').φ.source :=
    fun w hw => (isoSec_locIso_eq h (hsubK hw).1 hw.1
      ((K'.isScPlus i).1 _ (hsubK hw).2.1)).symm
  rw [K.orTangent_eq_linOrTangent hF.2 hsec _ hy hc hyc hsubK hys hfs,
    K'.orTangent_eq_linOrTangent hF'.2 hsec' o' hϕM hc' hyc' hsubK' hys' hfs']
  exact linOrTangent_pullOr_of_eq_mpullPt h hF hF' hpb hsec hsec' hys hys' o'
    (chartPtOf c' hc' hyc' hys') hsubU' (K'.isOpen_O.inter L.isOpen_U') inter_subset_right
    ((K'.isLocalRep.mono (K'.isOpen_O.inter L.isOpen_U') inter_subset_left).2.1 (K'.idx i))
    (fun z hz => ⟨hsubK' hz, hsubU' hz⟩) (K.isScPlus i)
    _ (chartPtOf_transportChart_eq_mpullPt h hc' hsubU' hyc' hys hys' hc hyc) hsubK hss hfs hfs' _ _

include hpb in
/-- The positive frames of the carried sheets are the images under `(Tϕ)⁻¹` of those of `K'`. -/
theorem KernelBranching.frames_pullEquiv
    (o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx f' hF'.2 x hs) (i : K'.ι) {y : A.Obj}
    (hy : y ∈ (KernelBranching.pullEquiv h hF hF' hpb K' hRU hRP).M i) :
    (KernelBranching.pullEquiv h hF hF' hpb K' hRU hRP).frames hF.2 hsec
        (h.pullOr hF hF' hpb hsec hsec' o') i y =
      (fun u => fibreInv ϕ.tangent.obj y ∘ u) '' K'.frames hF'.2 hsec' o' i (ϕ.obj y) := by
  have e := KernelBranching.orTangent_pullEquiv h hF hF' hpb hsec hsec' K' hRU hRP o' i hy
  unfold KernelBranching.orTangent at e
  rw [OrTangent.map_mk] at e
  exact eq_of_heq (OrTangent.mk.inj e).2.2

include hpb in
/-- **The continuity of `y ↦ o'_{i,y}` along the sheets is carried along** (Definition 9.3.2):
a frame field of `Mᵢ'` with continuous chart vectors in `φ'` gives the frame field `(Tϕ)⁻¹ e'(ϕ z)`
of the carried sheet, with the same chart vectors in the carried chart `φ' ∘ ϕ`. -/
theorem KernelBranching.framesContinuous_pullEquiv
    {o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx f' hF'.2 x hs}
    (hc' : K'.FramesContinuous hF'.2 hsec' o') :
    (KernelBranching.pullEquiv h hF hF' hpb K' hRU hRP).FramesContinuous hF.2 hsec
      (h.pullOr hF hF' hpb hsec hsec' o') := by
  set K := KernelBranching.pullEquiv h hF hF' hpb K' hRU hRP with hK
  set L := h.locIso x with hLdef
  intro i hn y hy
  have hϕM : ϕ.obj y ∈ K'.M i := (mem_M_iff_pull h hF' hpb K' hRU i hy.1).1 hy.2
  obtain ⟨φ', hφ', V', hV'o, hyV', hV'φ', e', he', hcont⟩ := hc' i hn (ϕ.obj y) hϕM
  have hVo : IsOpen (h.locSet x ∩ ϕ.obj ⁻¹' V') :=
    L.base.isScSmoothOn.continuousOn.isOpen_inter_preimage (h.isOpen_locSet x) hV'o
  have hMV : ∀ z ∈ K.M i ∩ (h.locSet x ∩ ϕ.obj ⁻¹' V'), ϕ.obj z ∈ K'.M i ∩ V' :=
    fun z hz => ⟨(mem_M_iff_pull h hF' hpb K' hRU i hz.1.1).1 hz.1.2, hz.2.2⟩
  refine ⟨MPolyfold.transportChart L.base φ', MPolyfold.transportChart_isChart L.base hφ',
    h.locSet x ∩ ϕ.obj ⁻¹' V', hVo, ⟨(hRU hy.1).1, hyV'⟩,
    fun z hz => ⟨hz.1, hV'φ' hz.2⟩,
    fun z j => fibreInv ϕ.tangent.obj z (e' (ϕ.obj z) j), fun z hz => ?_, ?_⟩
  · rw [KernelBranching.frames_pullEquiv h hF hF' hpb hsec hsec' K' hRU hRP o' i hz.1]
    exact ⟨e' (ϕ.obj z), he' _ (hMV z hz), rfl⟩
  · have hcomp : ContinuousOn (fun z j => chartVec hφ' (e' (ϕ.obj z) j))
        (K.M i ∩ (h.locSet x ∩ ϕ.obj ⁻¹' V')) :=
      hcont.comp (L.base.isScSmoothOn.continuousOn.mono fun z hz => hz.2.1) hMV
    refine hcomp.congr fun z hz => funext fun j => ?_
    have hzM' := hMV z hz
    have hα' : A'.X.PObj.levelVal 1 (A'.X.PObj.tangentProj (e' (ϕ.obj z) j)) = ϕ.obj z :=
      ((K'.isOrientedAt hF'.2 hsec' o' hzM'.1).1 _
        (((K'.isOrientedAt hF'.2 hsec' o' hzM'.1).mem_carrier (he' _ hzM') j)))
    obtain ⟨h1, h2⟩ :=
      EpFunctor.fibreInv_spec_tangent h.isEquivalence_base.isLocalScDiffeo_obj hα'
    have hαU : fibreInv ϕ.tangent.obj z (e' (ϕ.obj z) j) ∈ A.X.PObj.tangentPreimage
        (h.locSet x) := by
      change _ ∈ h.locSet x; rw [h1]; exact hz.1.1 |> (hRU ·) |>.1
    have e3 := EpFunctor.tangent_obj_eq_tangentMapOn (F := ϕ) L.base hαU
    beta_reduce
    rw [← chartVec_tangentMapOn_of_isScDiffeoOn L.base hφ' (by
      rw [h1]; exact ⟨(hRU hz.1.1).1, hV'φ' hz.2.2⟩)]
    exact (congrArg (chartVec hφ') e3).symm.trans (congrArg (chartVec hφ') h2)

end Equiv

/-! ### The pull-back of a canonical orientation -/

section Main

variable {A A' : SEP.{u}} {ϕ : EpFunctor A.X A'.X}
  {Φ : EpFunctor A.E.toEpGroupoid A'.E.toEpGroupoid}
  (h : A.E.IsStrongBundleEquivalence A'.E ϕ Φ)
  {f : A.Obj → A.W} {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hpb : f = h.pullback f')
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)

include hpb in
/-- **2021 Theorem 15.4.1 / Definition 15.4.2 along a strong bundle equivalence: the pull-back of
a canonical orientation is canonical.**  If `T̂'` is the canonical orientation of `Θ' = Λ' ∘ f'`
for `(f', o')`, then `ϕ^* T̂'` (Definition 11.3.6) is the canonical orientation of
`Θ = (Λ' ∘ Φ) ∘ f` for `(f, h^* o')`, with the same dimension: it is an orientation of `Θ`
(Theorem 11.3.5), and at every point `x` of the support the structure of `T̂'` at `ϕ(x)`,
carried along the local isomorphism of `h` at `x` (`KernelBranching.pullEquiv`), represents it. -/
theorem IsCanonicalFor.pullSection {Λ' : A'.W → ℚ≥0}
    {o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx f' hF'.2 x hs} {n : ℕ}
    {T' : A'.Obj → A'.X.PObj.OrTangent →₀ ℚ} (hT' : IsCanonicalFor Λ' hF'.2 hsec' o' n T') :
    IsCanonicalFor (fun w => Λ' (Φ.obj w)) hF.2 hsec (h.pullOr hF hF' hpb hsec hsec' o') n
      (ϕ.pullSection T') := by
  refine ⟨?_, fun x hx => ?_⟩
  · have hO := EpFunctor.isOrientation_pullSection h.isEquivalence_base
      (A'.X.hasIndependentTangentSums _) hT'.1
    rw [← pullbackTheta_eq h hF' hpb (Λ := fun w => Λ' (Φ.obj w)) (Λ' := Λ') rfl] at hO
    exact hO
  · have hx' : ϕ.obj x ∈ EpGroupoid.supp (fun z => ((Λ' (f' z) : ℚ≥0) : ℚ)) := by
      change (0 : ℚ) < (Λ' (f' (ϕ.obj x)) : ℚ)
      rw [← multisection_pullback_apply h hF' hpb (Λ' := Λ') x]
      exact hx
    obtain ⟨K', hc', hn', hR'⟩ := hT'.2 (ϕ.obj x) hx'
    obtain ⟨V, hxV, hVP⟩ := A.X.exists_hasPropernessProperty x
    have hWo : IsOpen (V ∩ isoSet (h.locIso x) K'.U) :=
      hVP.1.inter (isOpen_isoSet _ K'.isOpen_U)
    obtain ⟨R, hRW⟩ := A.X.theorem_7_1_13 x hWo ⟨hxV, h.mem_locSet x, K'.mem_U⟩
    have hRU : R.U ⊆ isoSet (h.locIso x) K'.U := fun z hz => (hRW hz).2
    have hRP : A.X.HasPropernessProperty R.U :=
      hVP.mono R.isOpen_U fun z hz => (hRW hz).1
    set K := KernelBranching.pullEquiv h hF hF' hpb K' hRU hRP with hK
    have hc : K.FramesContinuous hF.2 hsec (h.pullOr hF hF' hpb hsec hsec' o') :=
      KernelBranching.framesContinuous_pullEquiv h hF hF' hpb hsec hsec' K' hRU hRP hc'
    refine ⟨K, hc, hn', K.represents_toOrientedTame hc hn' fun y hy hys => ?_⟩
    have hϕU : ϕ.obj y ∈ K'.U := (hRU hy).2
    have hys' := h.smooth_obj hys
    rw [EpFunctor.pullSection_of_mem hys, hR' _ hϕU hys', K'.orientedSum_toOrientedTame]
    exact (KernelBranching.canonSum_pullOr h hF hF' hpb hsec hsec' o' K K' hy hϕU hys).symm

include hpb in
/-- **The pull-back of a canonical perturbation's orientation is canonical**: for an oriented
regular perturbation `P'` of `f'` with the canonical orientation of `(f', o')`,
`ϕ^* T̂_{P'}` is canonical for `(Λ_{P'} ∘ Φ, h^* o')`. -/
theorem IsCanonicalPerturbation.isCanonicalFor_pullSection
    {o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx f' hF'.2 x hs} {m : ℕ}
    {P' : OrientedRegularPerturbation A' f' m} (hP' : IsCanonicalPerturbation hF'.2 hsec' o' P') :
    IsCanonicalFor (fun w => P'.Λ (Φ.obj w)) hF.2 hsec (h.pullOr hF hF' hpb hsec hsec' o') (m + 1)
      (ϕ.pullSection P'.T) :=
  IsCanonicalFor.pullSection h hF hF' hpb hsec hsec' hP'

end Main

/-! ### Two strong bundle equivalences out of one bundle -/

section Diagram

variable {A₁ A₂ A'' : SEP.{u}} {ϕ₁ : EpFunctor A''.X A₁.X}
  {Φ₁ : EpFunctor A''.E.toEpGroupoid A₁.E.toEpGroupoid} {ϕ₂ : EpFunctor A''.X A₂.X}
  {Φ₂ : EpFunctor A''.E.toEpGroupoid A₂.E.toEpGroupoid}
  (h₁ : A''.E.IsStrongBundleEquivalence A₁.E ϕ₁ Φ₁)
  (h₂ : A''.E.IsStrongBundleEquivalence A₂.E ϕ₂ Φ₂)
  {f₁ : A₁.Obj → A₁.W} {f₂ : A₂.Obj → A₂.W} {f'' : A''.Obj → A''.W}
  (hF₁ : A₁.E.IsScFredholmSectionFunctor f₁) (hF₂ : A₂.E.IsScFredholmSectionFunctor f₂)
  (hF'' : A''.E.IsScFredholmSectionFunctor f'') (hpb₁ : f'' = h₁.pullback f₁)
  (hpb₂ : f'' = h₂.pullback f₂) (hsec₁ : A₁.B.HasScPlusSectionsThrough)
  (hsec₂ : A₂.B.HasScPlusSectionsThrough) (hsec'' : A''.B.HasScPlusSectionsThrough)

include hpb₁ hpb₂ in
/-- **The canonical orientations of two models agree over a diagram of strong bundle
equivalences** `W₁ ←Φ₁ W'' →Φ₂ W₂` (proof of Theorem 12.5.7 and §16.6, p. 739): for
`Λ₁ ∘ Φ₁ = Λ₂ ∘ Φ₂`, orientations with `h₁^* o₁ = h₂^* o₂`, and the canonical orientations
`T̂₁`, `T̂₂` of `Λ₁ ∘ f₁`, `Λ₂ ∘ f₂`: `ϕ₁^* T̂₁ = ϕ₂^* T̂₂` at every smooth point of `X''`.  The
canonical orientation on `W''` is `ϕ₁^* T̂₁` (`IsCanonicalFor.pullSection`). -/
theorem IsCanonicalFor.pullSection_eq_pullSection_of_canonical {Λ₁ : A₁.W → ℚ≥0}
    {Λ₂ : A₂.W → ℚ≥0} (hΛ : ∀ w, Λ₁ (Φ₁.obj w) = Λ₂ (Φ₂.obj w))
    {o₁ : ∀ x (hs : x ∈ A₁.X.PObj.smoothSet), Orx f₁ hF₁.2 x hs}
    {o₂ : ∀ x (hs : x ∈ A₂.X.PObj.smoothSet), Orx f₂ hF₂.2 x hs}
    (ho : h₁.pullOr hF'' hF₁ hpb₁ hsec'' hsec₁ o₁ = h₂.pullOr hF'' hF₂ hpb₂ hsec'' hsec₂ o₂)
    {n₁ n₂ : ℕ} {T₁ : A₁.Obj → A₁.X.PObj.OrTangent →₀ ℚ}
    {T₂ : A₂.Obj → A₂.X.PObj.OrTangent →₀ ℚ}
    (hT₁ : IsCanonicalFor Λ₁ hF₁.2 hsec₁ o₁ n₁ T₁) (hT₂ : IsCanonicalFor Λ₂ hF₂.2 hsec₂ o₂ n₂ T₂)
    {y : A''.Obj} (hys : y ∈ A''.X.PObj.smoothSet) :
    ϕ₁.pullSection T₁ y = ϕ₂.pullSection T₂ y :=
  IsCanonicalFor.pullSection_eq_pullSection h₁ h₂ hF₁ hF₂ hF'' hpb₁ hpb₂ hsec₁ hsec₂ hsec'' hΛ ho
    hT₁ hT₂ (IsCanonicalFor.pullSection h₁ hF'' hF₁ hpb₁ hsec'' hsec₁ hT₁) hys

end Diagram

end SBLocalization

end Polyfold
