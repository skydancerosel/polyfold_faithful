import Polyfold.Examples.Classical.ProductSetup

/-!
# The classical reduction crossed with the weighted `ℓ²` factor: the sc-Fredholm section

For Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Theorem 16.6.6,
2021 p. 739, with Definitions 3.6.4, 6.2.1, 15.3.1, 16.3.9, 16.3.18, 16.6.1 and 16.6.3.

## What is formalized (namespace `Polyfold.Examples.Classical.Product`)

* `fP φ`: the section `(x, e) ↦ ((x, φ x), (e, e))` of `AP σ`;
  `isScFredholmSectionFunctor_fP`, `isScFredholmSectionTame_fP` (Definition 3.6.4),
  `isIndexAt_fP` (Fredholm index `0` at every smooth point), `solutionSet_fP`.
* `prRep`, `prFredholmSection`: the sc-Fredholm section `|(x, e)| ↦ |((x, φ x), (e, e))|` of
  `prBundle σ` (Definitions 16.3.18, 16.6.1).
* `NP σ = max(gNorm σ w, |h|_1)`, `nP σ`: the auxiliary norms (Definitions 8.3.5, 16.3.9);
  `controlsCompactness_nP` (Definition 16.6.3, for a proper `φ`),
  `hasCompactSolutionSet_prFredholmSection`; `normW_NP_zero`: `N((x, w), (e, 0)) = gNorm σ w`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical.Product

open TrivialBundle EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure WeightedEllTwo SBLocalization StrongRetr
  Polyfold.Examples.OrbifoldSquareInf Polyfold.Examples.Classical

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]
  [FaithfulSMul G (Fin n → ℝ)]
  (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) {φ : (Fin n → ℝ) → (Fin n → ℝ)}

/-! ### The section -/

/-- **The section `f(x, e) = ((x, φ x), (e, e))`.** -/
abbrev fP (φ : (Fin n → ℝ) → (Fin n → ℝ)) : (AP σ).Obj → (AP σ).W := Prod.map (fSec φ) OrbifoldSquareInf.idSec

theorem fP_apply (x : (AP σ).Obj) : fP σ φ x = (fSec φ x.1, OrbifoldSquareInf.idSec x.2) := rfl

variable {σ}

theorem isScFredholmSectionFunctor_fP_and (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) :
    (AP σ).E.IsScFredholmSectionFunctor (fP σ φ) ∧
      (AP σ).B.IsScFredholmSectionTame (fP σ φ) :=
  isScFredholmSectionFunctor_prodMap (isScFredholmSectionFunctor_fSec hφ heq)
    (isScFredholmSectionTame_fSec σ hφ) isScFredholmSectionFunctor_idSec
    isScFredholmSectionTame_idSec

/-- **`f` is an sc-Fredholm section functor** of `(ℝⁿ × ℝⁿ) × (H ◁ H)` over `(G ⋉ ℝⁿ) × H`. -/
theorem isScFredholmSectionFunctor_fP (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) :
    (AP σ).E.IsScFredholmSectionFunctor (fP σ φ) :=
  (isScFredholmSectionFunctor_fP_and hφ heq).1

variable (σ) in
/-- **`f` has tame germ data** (Definition 3.6.4). -/
theorem isScFredholmSectionTame_fP (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) :
    (AP σ).B.IsScFredholmSectionTame (fP σ φ) :=
  (isScFredholmSectionFunctor_prodMap (isScFredholmSectionFunctor_fSec (σ := σ) hφ heq)
    (isScFredholmSectionTame_fSec σ hφ) isScFredholmSectionFunctor_idSec
    isScFredholmSectionTame_idSec).2

/-- **`f(x, e) = 0` iff `φ x = 0` and `e = 0`.** -/
theorem isZeroAt_fP_iff {x : (AP σ).Obj} :
    IsZeroAt (AP σ).P (fP σ φ) x ↔ φ x.1 = 0 ∧ x.2 = h0 := by
  have h : x ∈ solutionSet (AP σ).P (fP σ φ) ↔ φ x.1 = 0 ∧ x.2 = h0 := by
    refine (Set.ext_iff.1 (solutionSet_prodMap (A := AG σ) (A' := AH) (fSec φ) OrbifoldSquareInf.idSec) x).trans ?_
    exact and_congr isZeroAt_graphSection_iff isZeroAt_idSec_iff
  exact h

variable (σ) in
/-- **The solution set is `φ⁻¹(0) × {0}`.** -/
theorem solutionSet_fP :
    solutionSet (AP σ).P (fP σ φ) = (φ ⁻¹' {0}) ×ˢ ({h0} : Set HObj) := by
  ext x
  exact isZeroAt_fP_iff

/-- The points `(y, 0)` are smooth. -/
theorem mem_smoothSet_mk_h0P (y : Fin n → ℝ) :
    ((y, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet := by
  have h : ((y, h0) : (Fin n → ℝ) × HObj) ∈ ((rnPolyfold n).prod PH).smoothSet ↔
      y ∈ (rnPolyfold n).smoothSet ∧ h0 ∈ PH.smoothSet := MPolyfold.mem_smoothSet_prod
  refine h.2 ⟨by rw [rnPolyfold_smoothSet]; exact mem_univ _, ?_⟩
  exact mem_smoothSet_PH_iff.2 H.smooth.zero_mem

/-- **`(x, e)` is a smooth point of `ℝⁿ × H` iff `e ∈ H_∞`.** -/
theorem mem_smoothSet_AP_iff {x : (Fin n → ℝ) × HObj} :
    x ∈ (AP σ).X.PObj.smoothSet ↔ ((x.2 : HObj) : H 0) ∈ H.smooth := by
  have h : x ∈ ((rnPolyfold n).prod PH).smoothSet ↔
      x.1 ∈ (rnPolyfold n).smoothSet ∧ x.2 ∈ PH.smoothSet := MPolyfold.mem_smoothSet_prod
  have h1 : x.1 ∈ (rnPolyfold n).smoothSet := by rw [rnPolyfold_smoothSet]; exact mem_univ _
  exact h.trans ((and_iff_right h1).trans (LocalBundle.mem_smoothSet_iff relOpen_H h0))

/-! ### The index -/

variable (σ) in
set_option maxHeartbeats 800000 in
-- the product chart is unfolded
/-- **The Fredholm index of `f` is `0`** at every smooth point (Definition 6.2.1): for the
sc⁺-section `s(x, e) = ((x, (x − x₀) − φ x), (e, −e₀))`, `(f + s)(x, e) = ((x, x − x₀), (e, e − e₀))`
vanishes at `(x₀, e₀)` and its linearization there, in the product of the chart of `ℝⁿ` centred
at `x₀` and the chart of `H`, is the identity. -/
theorem isIndexAt_fP_mk (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (z₀ : Fin n → ℝ) (y : HObj) (hx : ((z₀, y) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet) :
    (AP σ).B.IsIndexAt (fP σ φ) ((z₀, y) : (AP σ).Obj) 0 := by
  classical
  have hf := (isScFredholmSectionFunctor_fP hφ heq).2
  have hy : (y : HObj) ∈ PH.smoothSet := (MPolyfold.mem_smoothSet_prod.1 hx).2
  set e : H 0 := (show HObj from y).1 with hedef
  have he : e ∈ H.smooth := mem_smoothSet_PH_iff.1 hy
  obtain ⟨e₁, he₁⟩ := (H.mem_smooth_iff.1 he) 1
  let ψ : (Fin n → ℝ) → (Fin n → ℝ) := fun z => (z - z₀) - φ z
  have hψ : ContDiff ℝ ∞ ψ := (contDiff_id.sub contDiff_const).sub hφ
  let S : (AP σ).Obj → (AP σ).W := Prod.map (graphSection ψ) (constSec (-e))
  have hS : (AP σ).B.IsScPlusSection S :=
    StrongBundle.IsScPlusSection.prod (isScPlusSection_graphSection hψ)
      (isScPlusSection_constSec (H.smooth.neg_mem he))
  have hFs := hf.isScSmooth.sectionAdd hS
  let c : StrongBundleChart (AP σ).X.PObj (AP σ).P :=
    (chart (k := n) z₀).prod (LocalBundle.chart (F := H) relOpen_H h0)
  have hc : (AP σ).B.IsChart c :=
    StrongBundle.IsChart.prod (isChart_chart (k := n) z₀)
      (LocalBundle.isChart_chart (F := H) relOpen_H h0)
  have hsrc : ((z₀, y) : (AP σ).Obj) ∈ c.φ.source := ⟨mem_univ _, mem_univ _⟩
  have hφ' : c.φ ((z₀, y) : (AP σ).Obj) = ((0 : Fin n → ℝ), e) :=
    Prod.ext (sub_self (show Fin n → ℝ from z₀)) rfl
  have hprin : ∀ u : (Fin n → ℝ) × H 0,
      c.principal (sectionAdd (AP σ).P (fP σ φ) S) u = (u.1, u.2 - e) := by
    intro u
    rw [c.principal_sectionAdd hf.isScSmooth.1 hS.1 (show u ∈ c.φ.model.O from
      ⟨mem_univ _, mem_univ _⟩)]
    have h1 : ((LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm u.2 : H 0) = u.2 :=
      (LocalBundle.baseChart relOpen_H h0).toPartialEquiv.right_inv (mem_univ _)
    refine Prod.ext ?_ ?_
    · change φ (u.1 + z₀) + ((u.1 + z₀ - z₀) - φ (u.1 + z₀)) = u.1
      abel
    · change ((LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm u.2 : H 0) + -e = u.2 - e
      rw [h1, sub_eq_add_neg]
  have h0z : IsZeroAt (AP σ).P (sectionAdd (AP σ).P (fP σ φ) S) ((z₀, y) : (AP σ).Obj) := by
    refine (c.isZeroAt_iff hFs.1 hsrc).2 ?_
    refine (congrArg (c.principal (sectionAdd (AP σ).P (fP σ φ) S)) hφ').trans ?_
    exact (hprin _).trans (Prod.ext rfl (sub_self e))
  let p₀ : ChartPoint (AP σ).B ((z₀, y) : (AP σ).Obj) :=
    { c := c
      isChart := hc
      mem_source := hsrc
      z := ((0 : Fin n → ℝ), e₁)
      toBase_z := by
        rw [hφ']
        exact Prod.ext rfl he₁ }
  have hzU : p₀.z ∈ c.φ.model.E.lvlSet c.U 1 := by
    change c.φ.model.E.toBase 1 p₀.z ∈ c.U
    exact ⟨mem_univ _, mem_univ _⟩
  have hr : r c.R = id := funext fun u => rfl
  have hDr : scDeriv c.U (r c.R) p₀.z = ContinuousLinearMap.id ℝ _ := by
    rw [hr]
    exact scDeriv_eq_of_hasFDerivAt c.relOpen (isScSmooth_id c.relOpen.isScDomain 1).isSc1 hzU
      (hasFDerivAt_id _)
  have hcomp : (c.principal (sectionAdd (AP σ).P (fP σ φ) S) ∘ r c.R) =
      fun u : (Fin n → ℝ) × H 0 => u - ((0 : Fin n → ℝ), e) := by
    rw [hr]
    funext u
    exact (hprin u).trans (Prod.ext (sub_zero _).symm rfl)
  have hDg : scDeriv c.U (c.principal (sectionAdd (AP σ).P (fP σ φ) S) ∘ r c.R) p₀.z =
      ContinuousLinearMap.id ℝ _ := by
    refine scDeriv_eq_of_hasFDerivAt c.relOpen
      ((isScSmooth_principal_comp_r (A := AP σ) hFs hc) 1).isSc1 hzU ?_
    rw [hcomp]
    exact (hasFDerivAt_id _).sub_const _
  have hL : ∀ v : ↥p₀.T, ((p₀.stabT hf hS h0z v : ↥p₀.K) : c.F 0) = (v : c.φ.model.E 0) := by
    intro v
    rw [ChartPoint.coe_stabT, linAt_apply]
    exact congrArg (fun D : c.φ.model.E 0 →L[ℝ] c.F 0 => D (v : c.φ.model.E 0)) hDg
  have hbij : Bijective (p₀.stabT hf hS h0z) := by
    constructor
    · intro v w hvw
      have h := congrArg (fun t : ↥p₀.K => (t : c.F 0)) hvw
      simp only [hL] at h
      exact Subtype.ext h
    · intro w
      have hwT : (w : c.F 0) ∈ p₀.T :=
        ⟨(w : c.F 0), congrArg (fun D : c.φ.model.E 0 →L[ℝ] c.φ.model.E 0 => D (w : c.F 0)) hDr⟩
      exact ⟨⟨(w : c.F 0), hwT⟩, Subtype.ext (hL _)⟩
  have h := (p₀.isFredholm_isIndexAt_of_mem_linSet hf (p₀.stabT_mem_linSet hf hS h0z hx)).2
  rwa [fredholmIndex_eq_zero_of_bijective _ hbij] at h

variable (σ) in
/-- **The Fredholm index of `f` is `0`** at every smooth point (Definition 6.2.1). -/
theorem isIndexAt_fP (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (x : (AP σ).Obj) (hx : x ∈ (AP σ).X.PObj.smoothSet) :
    (AP σ).B.IsIndexAt (fP σ φ) x 0 :=
  isIndexAt_fP_mk σ hφ heq x.1 x.2 hx

/-! ### The sc-Fredholm section of the strong polyfold bundle -/


/-- `|f|` is well defined on the orbit space. -/
theorem π_fP_eq (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    {x y : (AP σ).Obj} (h : (AP σ).X.π x = (AP σ).X.π y) :
    (AP σ).E.toEpGroupoid.π (fP σ φ x) = (AP σ).E.toEpGroupoid.π (fP σ φ y) := by
  obtain ⟨m, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 h
  have hf := (isScFredholmSectionFunctor_fP hφ heq).1.2 m
  refine (GroupoidStr.π_eq_π_iff _).2 ⟨⟨(m, fP σ φ ((AP σ).X.src m)), rfl⟩, ?_, ?_⟩
  · change fP σ φ ((AP σ).X.src m) = fP σ φ x
    rw [hs]
  · change (AP σ).E.μ ⟨(m, fP σ φ ((AP σ).X.src m)), rfl⟩ = fP σ φ y
    rw [← ht]
    exact hf.symm

variable (σ) in
/-- **The representative `(prStructure σ, f)`** of the section
`|(x, e)| ↦ |((x, φ x), (e, e))|` (Definition 16.3.18). -/
def prRep (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) :
    SectionRep (prBundle σ) where
  S := prStructure σ
  hS := rfl
  F := fP σ φ
  hF := (isScFredholmSectionFunctor_fP hφ heq).1
  f := Quotient.lift (fun x : (AP σ).Obj => (AP σ).E.toEpGroupoid.π (fP σ φ x))
    fun _ _ h => π_fP_eq hφ heq (Quotient.sound h)
  continuous_f := Continuous.quotient_lift ((AP σ).E.toEpGroupoid.continuous_π.comp
    (continuousOn_univ.1 (isScFredholmSectionFunctor_fP hφ heq).1.1.2.continuousOn)) _
  isSection z := Quotient.inductionOn z fun _ => rfl
  comm _ := rfl

variable (σ) in
/-- **The sc-Fredholm section `|(x, e)| ↦ |((x, φ x), (e, e))|`** of `prBundle σ`
(Definition 16.6.1). -/
def prFredholmSection (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) :
    FredholmSection (prBundle σ) :=
  ⟨⟦prRep σ hφ heq⟧, prRep σ hφ heq, rfl, isScFredholmSectionFunctor_fP hφ heq⟩

/-! ### The auxiliary norm and the control of compactness -/

variable (σ) in
/-- **The auxiliary norm of `(ℝⁿ × ℝⁿ) × (H ◁ H)`**: `N((x, w), (e, h)) = max(gNorm σ w, |h|_1)`. -/
def NP : (AP σ).B.One → ℝ := (AG σ).B.prodAuxNorm AH.B (NG σ) NH

variable (σ) in
/-- **`NP σ` is an auxiliary norm** (Definition 8.3.5). -/
theorem isAuxNorm_NP : (AP σ).E.IsAuxNorm (NP σ) :=
  EpStrongBundle.isAuxNorm_prodAuxNorm (isAuxNorm_NG σ) isAuxNorm_NH

variable (σ) in
/-- **The auxiliary norm `n` of the strong polyfold bundle** (Definition 16.3.9). -/
def nP : (AP σ).E.toEpGroupoid.OrbitSpace → ℝ := (prStructure σ).descend (NP σ)

variable (σ) in
theorem isAuxNorm_nP : (prBundle σ).IsAuxNorm (nP σ) := isAuxNorm_descend rfl (isAuxNorm_NP σ)

variable (σ) in
theorem normOf_nP : (prStructure σ).normOf (nP σ) = NP σ :=
  (prStructure σ).normOf_descend (isAuxNorm_NP σ).isOneInvariant

/-- **`(N, ℝⁿ × H)` controls the compactness of `f`** (Definition 15.3.1) for a proper `φ`. -/
theorem controlsCompactness_fP_univ (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) :
    ControlsCompactness (AP σ) (fP σ φ) (NP σ) univ := by
  have h := ControlsCompactness.prod (controlsCompactness_fSec_univ (σ := σ) hprop)
    controlsCompactness_idSec
  rw [univ_prod_univ] at h
  exact h

/-- **`(n, Z)` controls the compactness of the section** (Definition 16.6.3, with `U = Z`). -/
theorem controlsCompactness_nP (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) :
    (prFredholmSection σ hφ heq).1.ControlsCompactness (nP σ)
      (univ : Set (AP σ).X.OrbitSpace) := by
  refine ((prRep σ hφ heq).controlsCompactness_iff (isAuxNorm_nP σ) isOpen_univ).2 ?_
  rw [preimage_univ]
  change ControlsCompactness (AP σ) (fP σ φ) ((prStructure σ).normOf (nP σ)) univ
  rw [normOf_nP]
  exact controlsCompactness_fP_univ hprop

/-- **The solution set is compact**: it is the image of `φ⁻¹(0) × {0}`. -/
theorem hasCompactSolutionSet_prFredholmSection (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) :
    (prFredholmSection σ hφ heq).1.HasCompactSolutionSet := by
  refine (prRep σ hφ heq).hasCompactSolutionSet_iff.2 ?_
  change IsCompact ((AP σ).X.π '' solutionSet (AP σ).P (fP σ φ))
  rw [solutionSet_fP]
  exact ((hprop _ isCompact_singleton).prod isCompact_singleton).image (AP σ).X.continuous_π

variable (σ) in
/-- **`N((x, w), (e, 0)) = gNorm σ w`.** -/
theorem normW_NP_zero (p : (AG σ).W) (x : HObj) :
    normW (A := AP σ) (NP σ) ((p, ((x, (0 : H 0)) : AH.W)) : (AP σ).W) = gNorm σ p.2 := by
  have hp : p ∈ (AG σ).B.oneSet := by
    have h : (bundle n n).oneSet = univ := oneSet_eq
    exact h ▸ mem_univ p
  have h := normW_prodAuxNorm (A := AG σ) (A' := AH) (NG σ) NH
    (w := ((p, ((x, (0 : H 0)) : AH.W)) : (AP σ).W)) hp (zero_mem_oneSet_BH x)
  have h1 : normW (A := AG σ) (NG σ) p = gNorm σ p.2 :=
    (normW_of_mem (A := AG σ) (NG σ) hp).trans (NG_oneMk σ p hp)
  have h2 := normW_NH_zero x
  change normW (A := AP σ) ((AG σ).B.prodAuxNorm AH.B (NG σ) NH) _ = _
  rw [h, h1]
  change max (gNorm σ p.2) (normW (A := AH) NH ((x, (0 : H 0)) : AH.W)) = _
  rw [h2]
  exact max_eq_left (gNorm_nonneg σ _)

end Polyfold.Examples.Classical.Product
