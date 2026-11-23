import Polyfold.Examples.OrbifoldSquareInfSection
import Polyfold.Examples.OrbifoldSquare

/-!
# The orbifold `(ℂ × H)/ℤ₅` and the section `(z, e) ↦ (z², e)`: the five-branch multisection

The infinite-dimensional version of the worked example `ℂ/ℤ₅`, `z ↦ z²`, for Hofer–Wysocki–Zehnder,
*Polyfold and Fredholm Theory* (Springer 2021), Theorem 16.6.6, 2021 p. 739.

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquareInf`)

* `branchInf c j`: the sc⁺-section `(z, e) ↦ ((z, ζ^{2j} c), (e, 0))`; `Λinf c`: the multisection
  with these five branches, weight `1/5` each; `Λinf_eq` (it is `Λ5 c` on the `ℂ`-part where the
  `H`-part of the fibre vanishes), `isWFunctor_Λinf`, `isLocalRepOn_Λinf`,
  `isScPlusMultisection_Λinf` (Definition 13.2.1).
* `Λinf_sqInf_pos_iff`, `Λinf_sqInf_eq`, `Λinf_sqInf_pos_iff_orbit`, `π_ne_π_neg_inf`,
  `isRegular_of_Λinf_pos`: for `c = r²` the perturbed solution set consists of the two orbits of
  `(r, 0)` and `(−r, 0)`, with weight `1/5` and trivial isotropy.
* **`isInGeneralPosition_Λinf`** (Definition 15.3.5), for `c ≠ 0`: at a solution `(z, 0)`, `z ≠ 0`,
  the linearization `(f − s_j)'(z, 0) = (2z ·, id)` is onto `ℂ × H`.
* `tinf c`, `isControlledBy_tinf` (for `|c| ≤ 1`), `isInGeneralPositionWith_tinf`: the
  sc⁺-multisection of the strong polyfold bundle is controlled by `(n, Z)` and `(f, λ)` is in
  general position (Definitions 16.5.4, 16.6.4).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.OrbifoldSquareInf

open TrivialBundle EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure WeightedEllTwo OrbifoldSquare SBLocalization StrongRetr
  Linearization15

/-! ### The branches -/

/-- The branch `(z, e) ↦ ((z, ζ^{2j} c), (e, 0))`. -/
def branchInf (c : ℂ) (j : ZMod 5) : Ainf.Obj → Ainf.W := Prod.map (branch c j) (constSec 0)

theorem branchInf_apply (c : ℂ) (j : ZMod 5) (x : (Fin 2 → ℝ) × HObj) :
    branchInf c j x = ((x.1, branchVal c j), (x.2, (0 : H 0))) := rfl

theorem isScPlusSection_branchInf (c : ℂ) (j : ZMod 5) :
    Ainf.B.IsScPlusSection (branchInf c j) :=
  StrongBundle.IsScPlusSection.prod (isScPlusSection_branch c j)
    (isScPlusSection_constSec H.smooth.zero_mem)

theorem eq_branchInf_iff (c : ℂ) (j : ZMod 5) (w : A5.W × (HObj × H 0)) :
    (w : Ainf.W) = branchInf c j (Ainf.P w) ↔ w.1 = branch c j (A5.P w.1) ∧ w.2.2 = 0 := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg (fun p : A5.W × (HObj × H 0) => p.2.2) h⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext h1 (Prod.ext rfl h2)

open scoped Classical in
/-- **The multisection `Λ`** with the five branches `branchInf c j`, of weight `1/5` each. -/
def Λinf (c : ℂ) : Ainf.W → ℚ≥0 := fun w =>
  ∑ j : ZMod 5, if w = branchInf c j (Ainf.P w) then (1 / 5 : ℚ≥0) else 0

open scoped Classical in
/-- `Λ` is `Λ5 c` on the `ℂ`-part where the `H`-part of the fibre vanishes, and `0` elsewhere. -/
theorem Λinf_eq (c : ℂ) (w : A5.W × (HObj × H 0)) :
    Λinf c w = if w.2.2 = 0 then Λ5 c w.1 else 0 := by
  unfold Λinf Λ5
  split_ifs with h
  · refine Finset.sum_congr rfl fun j _ => ?_
    have e := eq_branchInf_iff c j w
    by_cases hj : w.1 = branch c j (A5.P w.1)
    · exact (if_pos (e.2 ⟨hj, h⟩)).trans (if_pos hj).symm
    · exact (if_neg fun h' => hj (e.1 h').1).trans (if_neg hj).symm
  · refine Finset.sum_eq_zero fun j _ => if_neg fun hj => h ?_
    exact ((eq_branchInf_iff c j w).1 hj).2

theorem Λinf_pos_iff (c : ℂ) (w : Ainf.W) :
    0 < Λinf c w ↔ ∃ j : ZMod 5, w = branchInf c j (Ainf.P w) := by
  classical
  unfold Λinf
  rw [Finset.sum_pos_iff]
  constructor
  · rintro ⟨j, -, hj⟩
    by_cases h : w = branchInf c j (Ainf.P w)
    · exact ⟨j, h⟩
    · rw [if_neg h] at hj
      exact absurd hj (lt_irrefl _)
  · rintro ⟨j, hj⟩
    refine ⟨j, Finset.mem_univ _, ?_⟩
    rw [if_pos hj]
    norm_num

open scoped Classical in
/-- **`Λ` is a functor** `W → ℚ⁺` (Definition 13.2.1). -/
theorem isWFunctor_Λinf (c : ℂ) : IsWFunctor Ainf (Λinf c) := by
  rintro ⟨⟨φ, w⟩, hq⟩
  have hq1 : (φ.1, w.1) ∈ pullbackSpace A5.P A5.X.src := congrArg Prod.fst hq
  have h1 : Λ5 c (A5.E.μ ⟨(φ.1, w.1), hq1⟩) = Λ5 c w.1 := isWFunctor_Λ5 c ⟨(φ.1, w.1), hq1⟩
  refine (Λinf_eq c ((A5.E.μ ⟨(φ.1, w.1), hq1⟩, w.2) : A5.W × (HObj × H 0))).trans
    (Eq.trans ?_ (Λinf_eq c w).symm)
  exact if_congr Iff.rfl h1 rfl

/-- The five branches with weight `1/5` are a local representation of `Λ`. -/
theorem isLocalRepOn_Λinf (c : ℂ) :
    IsLocalRepOn Ainf (Λinf c) univ (k := 5) (fun j : Fin 5 => branchInf c j)
      (fun _ => (1 / 5 : ℚ≥0)) := by
  classical
  refine ⟨fun _ => by norm_num,
    fun j => IsScPlusSectionOn.of_isScPlusSection (isScPlusSection_branchInf c j) isOpen_univ,
    ?_, fun w _ => by unfold Λinf; exact Finset.sum_congr rfl fun j _ => by split_ifs <;> rfl⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- **`Λ` is an sc⁺-multisection** (Definition 13.2.1). -/
theorem isScPlusMultisection_Λinf (c : ℂ) : IsScPlusMultisection Ainf (Λinf c) :=
  ⟨isWFunctor_Λinf c, fun x₀ => hasLocalSectionStructure_of_isLocalRepOn isOpen_univ
    (mem_univ x₀) (isLocalRepOn_Λinf c)⟩

/-! ### The perturbed solution set -/

theorem hobj_eq_h0_iff {y : HObj} : y = h0 ↔ (y : H 0) = 0 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

open scoped Classical in
theorem Λinf_sqInf (c : ℂ) (x : (Fin 2 → ℝ) × HObj) :
    Λinf c (sqInf x) = if x.2 = h0 then Λ5 c (sqSection x.1) else 0 := by
  classical
  refine (Λinf_eq c (sqSection x.1, idSec x.2)).trans ?_
  exact if_congr hobj_eq_h0_iff.symm rfl rfl

/-- `Λ(f(z, e)) > 0` iff `e = 0` and `z² = ζ^{2j} c` for some `j`. -/
theorem Λinf_sqInf_pos_iff (c : ℂ) (x : (Fin 2 → ℝ) × HObj) :
    0 < Λinf c (sqInf x) ↔ (∃ j : ZMod 5, OrbifoldSquare.sq x.1 = branchVal c j) ∧ x.2 = h0 := by
  rw [Λinf_sqInf]
  split_ifs with h
  · rw [Λ5_sqSection_pos_iff]
    exact (and_iff_left h).symm
  · exact ⟨fun h0' => absurd h0' (lt_irrefl _), fun h' => absurd h'.2 h⟩

open scoped Classical in
/-- Every perturbed solution lies on exactly one branch: `Λ(f(x))` is `1/5` or `0`. -/
theorem Λinf_sqInf_eq {c : ℂ} (hc : c ≠ 0) (x : (Fin 2 → ℝ) × HObj) :
    Λinf c (sqInf x) =
      if (∃ j : ZMod 5, OrbifoldSquare.sq x.1 = branchVal c j) ∧ x.2 = h0 then 1 / 5 else 0 := by
  classical
  rw [Λinf_sqInf, Λ5_sqSection_eq hc]
  by_cases h : x.2 = h0
  · rw [if_pos h]
    exact if_congr (and_iff_left h).symm rfl rfl
  · rw [if_neg h, if_neg fun h' => h h'.2]

/-- **The perturbed solutions for `c = r²` are the two orbits of `(r, 0)` and `(−r, 0)`.** -/
theorem Λinf_sqInf_pos_iff_orbit (r : ℂ) (x : (Fin 2 → ℝ) × HObj) :
    0 < Λinf (r ^ 2) (sqInf x) ↔
      (∃ g : G5, x = (g • cE.symm r, h0)) ∨ ∃ g : G5, x = (g • cE.symm (-r), h0) := by
  rw [Λinf_sqInf]
  split_ifs with h
  · rw [Λ5_sqSection_pos_iff_orbit]
    constructor
    · rintro (⟨g, hg⟩ | ⟨g, hg⟩)
      · exact Or.inl ⟨g, Prod.ext hg h⟩
      · exact Or.inr ⟨g, Prod.ext hg h⟩
    · rintro (⟨g, hg⟩ | ⟨g, hg⟩)
      · exact Or.inl ⟨g, congrArg Prod.fst hg⟩
      · exact Or.inr ⟨g, congrArg Prod.fst hg⟩
  · refine ⟨fun h0' => absurd h0' (lt_irrefl _), ?_⟩
    rintro (⟨g, hg⟩ | ⟨g, hg⟩) <;> exact absurd (congrArg Prod.snd hg) h

/-- **The two orbits are different points of the orbit space**, for `r ≠ 0`. -/
theorem π_ne_π_neg_inf {r : ℂ} (hr : r ≠ 0) :
    Xinf.π ((cE.symm r, h0) : (Fin 2 → ℝ) × HObj) ≠ Xinf.π (cE.symm (-r), h0) := by
  intro h
  obtain ⟨g, hg, -⟩ := π_eq_π_iff.1 h
  exact π_ne_π_neg hr ((action_π_eq_π_iff isScSmoothMap_smul).2 ⟨g, hg⟩)

/-- **The perturbed solutions have trivial isotropy**, for `c ≠ 0`. -/
theorem isRegular_of_Λinf_pos {c : ℂ} (hc : c ≠ 0) {x : (Fin 2 → ℝ) × HObj}
    (hx : 0 < Λinf c (sqInf x)) : Xinf.IsRegular x := by
  obtain ⟨⟨j, hj⟩, -⟩ := (Λinf_sqInf_pos_iff c x).1 hx
  refine isRegular_Xinf_iff.2 fun h => branchVal_ne_zero hc j ?_
  rw [← hj, h]
  exact (sq_eq_zero_iff 0).2 rfl

/-! ### General position -/

/-- In a chart whose partial quadrant is the whole space the reduced tangent space is the tangent
space. -/
theorem mem_reducedTangentFiber_of_univ_inf {φ : MChart Ainf.Obj} (hφ : Ainf.X.PObj.IsChart φ)
    {x : Ainf.X.PObj.Level 1} (hx : Ainf.X.PObj.levelVal 1 x ∈ φ.source) {k : ℕ} {V : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin k → ℝ)).prod V))
    (hT : φ.model.C = T 0 ⁻¹' quadrant k V 0) (hC : φ.model.C = univ)
    (α : Ainf.X.PObj.tangentFiber x) : α ∈ reducedTangentFiber hφ hx T := by
  have h0 : ∀ (v : φ.model.E 0) (i : Fin k), (T 0 v).1 i = 0 := by
    intro v i
    have h1 : ∀ u : φ.model.E 0, 0 ≤ (T 0 u).1 i := fun u => by
      have hu : u ∈ T 0 ⁻¹' quadrant k V 0 := by rw [← hT, hC]; exact mem_univ u
      exact hu i
    have h2 := h1 v
    have h3 := h1 (-v)
    rw [map_neg] at h3
    have h4 : (-(T 0 v)).1 i = -((T 0 v).1 i) := rfl
    rw [h4] at h3
    linarith
  exact Submodule.mem_comap.2 ((mem_minimalSubspaceWith T).2 fun i _ => h0 _ i)

/-- **`(f, Λ)` is in general position** (Definition 15.3.5), for `c ≠ 0`: at a solution `(z, 0)`
with `z² = ζ^{2j} c`, in the product of the chart of `ℂ` centred at `z` and the chart of `H`,
`(f − s_j)'(z, 0) = (2z ·, id)` is onto `ℂ × H`, and `ℂ × H` has no boundary. -/
theorem isInGeneralPosition_Λinf {c : ℂ} (hc : c ≠ 0) :
    IsInGeneralPosition Ainf sqInf (Λinf c) := by
  classical
  have : ParacompactSpace ((Fin 2 → ℝ) × HObj) := SEP.instParacompactObjProd A5 AH
  have : ParacompactSpace ((Fin 2 → ℝ) × AH.Obj) := SEP.instParacompactObjProd A5 AH
  have : ParacompactSpace (((Fin 2 → ℝ) × (Fin 2 → ℝ)) × (HObj × H 0)) :=
    SEP.instParacompactWProd A5 AH
  have : ParacompactSpace (((Fin 2 → ℝ) × (Fin 2 → ℝ)) × AH.W) :=
    SEP.instParacompactWProd A5 AH
  have hf := isScFredholmSectionFunctor_sqInf
  refine isInGeneralPosition_iff_exists.2 fun x hpos => ?_
  set x₀ : (Fin 2 → ℝ) × HObj := Ainf.X.PObj.levelVal 1 x with hx₀
  obtain ⟨⟨j₀, hj₀⟩, hx2⟩ := (Λinf_sqInf_pos_iff c x₀).1 hpos
  have hne : x₀.1 ≠ 0 := fun h =>
    branchVal_ne_zero hc j₀ (by rw [← hj₀, h]; exact (sq_eq_zero_iff 0).2 rfl)
  let ch : StrongBundleChart Ainf.X.PObj Ainf.P :=
    (chart (k := 2) x₀.1).prod (LocalBundle.chart (F := H) relOpen_H h0)
  have hch : Ainf.B.IsChart ch :=
    StrongBundle.IsChart.prod (isChart_chart (k := 2) x₀.1)
      (LocalBundle.isChart_chart (F := H) relOpen_H h0)
  have hx : Ainf.X.PObj.levelVal 1 x ∈ ch.φ.source := ⟨mem_univ _, mem_univ _⟩
  obtain ⟨k, V, T, hT⟩ := ch.φ.model.isPartialQuadrant
  refine ⟨ch.φ, ch.isChart, hx, k, V, T, hT, fun L hL => ?_⟩
  have hsurj : Surjective L := by
    let d : LocalLinData Ainf (Λinf c) x :=
      ⟨univ, isOpen_univ, 5, fun j : Fin 5 => branchInf c j, fun _ => (1 / 5 : ℚ≥0),
        isLocalRepOn_Λinf c, ch, hch, subset_univ _, hx⟩
    rw [linearization_eq hf d] at hL
    obtain ⟨i, hi, hLi⟩ := (mem_support_linSumIntr_iff (k := 5)
      (s := fun j : Fin 5 => branchInf c j) (σ := fun _ => (1 / 5 : ℚ≥0)) hf.1.1.1
      (fun _ => by norm_num) (fun _ z _ => rfl) (subset_univ _) hx L).1 hL
    rw [← hLi]
    have hsi := IsScPlusSectionOn.of_isScPlusSection (A := Ainf)
      (isScPlusSection_branchInf c i) isOpen_univ
    refine (surjective_toIntr_subDeriv_iff hf.1.1 hsi hch (subset_univ _) hx hi.symm).2 ?_
    set z := levelLift ch.φ 1 (Ainf.X.PObj.levelVal 1 x) with hzdef
    have hφ0 : ch.φ x₀ = (0 : (Fin 2 → ℝ) × H 0) :=
      Prod.ext (sub_self (show Fin 2 → ℝ from x₀.1)) (congrArg Subtype.val hx2)
    have hzb : ch.φ.model.E.toBase 1 z = (0 : (Fin 2 → ℝ) × H 0) :=
      (Ainf.X.PObj.toBase_levelLift ch.isChart hx (Ainf.X.PObj.levelVal_mem x)).trans hφ0
    have hzU : z ∈ ch.φ.model.E.lvlSet ch.U 1 := by
      change ch.φ.model.E.toBase 1 z ∈ ch.U
      exact ⟨mem_univ _, mem_univ _⟩
    have hr : r ch.R = id := funext fun u => rfl
    have hDr : scDeriv ch.U (r ch.R) z = ContinuousLinearMap.id ℝ _ := by
      rw [hr]
      exact scDeriv_eq_of_hasFDerivAt ch.relOpen
        (isScSmooth_id ch.relOpen.isScDomain 1).isSc1 hzU (hasFDerivAt_id _)
    set b : Fin 2 → ℝ := branchVal c i with hb
    let D1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := fderiv ℝ (OrbifoldSquare.sq - fun _ => b) x₀.1
    have hD1 : HasFDerivAt (OrbifoldSquare.sq - fun _ => b) D1 x₀.1 :=
      ((contDiff_sq.sub contDiff_const).differentiable (by simp)).differentiableAt.hasFDerivAt
    let D : (Fin 2 → ℝ) × H 0 →L[ℝ] (Fin 2 → ℝ) × H 0 :=
      (D1.comp (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (H 0))).prod
        (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (H 0))
    have hcomp : ((fun y => ch.principal sqInf y - ch.principal (branchInf c i) y) ∘ r ch.R) =
        fun u : (Fin 2 → ℝ) × H 0 => (OrbifoldSquare.sq (u.1 + x₀.1) - b, u.2) := by
      rw [hr]
      funext u
      have h1 : ((LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm u.2 : H 0) = u.2 :=
        (LocalBundle.baseChart relOpen_H h0).toPartialEquiv.right_inv (mem_univ _)
      refine Prod.ext rfl ?_
      change ((LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm u.2 : H 0) - 0 = u.2
      exact (congrArg (fun t : H 0 => t - 0) h1).trans (sub_zero (show H 0 from u.2))
    have hDg : subDeriv ch sqInf (branchInf c i) z = D := by
      refine scDeriv_eq_of_hasFDerivAt ch.relOpen
        (isSc1_sub_comp_r hf.1.1 hsi hch (subset_univ _)) hzU ?_
      rw [hcomp, hzb]
      have h1 : HasFDerivAt (fun u : (Fin 2 → ℝ) × H 0 => u.1 + x₀.1)
          (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (H 0)) 0 := hasFDerivAt_fst.add_const _
      have hD1' : HasFDerivAt (OrbifoldSquare.sq - fun _ => b) D1
          ((0 : (Fin 2 → ℝ) × H 0).1 + x₀.1) := by
        rw [Prod.fst_zero, zero_add]
        exact hD1
      exact (hD1'.comp (0 : (Fin 2 → ℝ) × H 0) h1).prodMk hasFDerivAt_snd
    intro w _
    obtain ⟨v1, hv1⟩ := surjective_fderiv_sq_sub_const hne b
      (show (Fin 2 → ℝ) × H 0 from w).1
    refine ⟨((v1, (show (Fin 2 → ℝ) × H 0 from w).2) : (Fin 2 → ℝ) × H 0),
      ⟨((v1, (show (Fin 2 → ℝ) × H 0 from w).2) : (Fin 2 → ℝ) × H 0), ?_⟩, ?_⟩
    · exact congrArg (fun S : ch.φ.model.E 0 →L[ℝ] ch.φ.model.E 0 =>
        S ((v1, (show (Fin 2 → ℝ) × H 0 from w).2) : (Fin 2 → ℝ) × H 0)) hDr
    · rw [hDg]
      exact Prod.ext hv1 rfl
  intro w
  obtain ⟨α, hα⟩ := hsurj w
  exact ⟨⟨α, mem_reducedTangentFiber_of_univ_inf ch.isChart hx T hT univ_prod_univ α⟩, hα⟩

/-! ### The sc⁺-multisection of the strong polyfold bundle -/

/-- **The sc⁺-multisection `λ`** of the strong polyfold bundle, the class of `Λ`
(Definition 16.5.1). -/
def tinf (c : ℂ) : ScPlusMultisection infBundle :=
  ⟦ofFunctor infStructure rfl (Λinf c) (isScPlusMultisection_Λinf c)⟧

/-- `N(Λ)(x) ≤ 1` for `|c| ≤ 1`. -/
theorem pointwiseNorm_Λinf_le {c : ℂ} (hc : ‖c‖ ≤ 1) (x : (Fin 2 → ℝ) × HObj) :
    pointwiseNorm (A := Ainf) Ninf (Λinf c) x ≤ 1 := by
  refine csSup_le ⟨_, mem_image_of_mem _ (⟨rfl, (Λinf_pos_iff c _).2 ⟨0, rfl⟩⟩ :
    branchInf c 0 x ∈ suppAt (A := Ainf) (Λinf c) x)⟩ ?_
  rintro _ ⟨w, ⟨-, hw⟩, rfl⟩
  obtain ⟨j, hj⟩ := (Λinf_pos_iff c w).1 hw
  rw [hj]
  refine (normW_Ninf_zero _ _).trans_le ?_
  change ‖cE (branchVal c j)‖ ≤ 1
  rw [norm_cE_branchVal]
  exact hc

/-- **`λ` is controlled by `(n, Z)`** (Definition 16.5.4), for `|c| ≤ 1`. -/
theorem isControlledBy_tinf {c : ℂ} (hc : ‖c‖ ≤ 1) :
    (tinf c).IsControlledBy ninf (univ : Set Ainf.X.OrbitSpace) := by
  refine ⟨fun z => ?_, subset_univ _⟩
  obtain ⟨x, rfl⟩ := infStructure.surjective_γπ z
  set b := ofFunctor infStructure rfl (Λinf c) (isScPlusMultisection_Λinf c)
  have h := normLam_eq (c := infBundle) (S := infStructure) rfl ninf (Λinf c) b.lam x
    fun w _ => b.comm w
  rw [normOf_ninf] at h
  exact h.le.trans (pointwiseNorm_Λinf_le hc x)

/-- **`(f, λ)` is in general position** (Definition 16.6.4), for `c ≠ 0`. -/
theorem isInGeneralPositionWith_tinf {c : ℂ} (hc : c ≠ 0) :
    infFredholmSection.1.IsInGeneralPositionWith (tinf c) :=
  ⟨infRep, Λinf c, isScPlusMultisection_Λinf c, rfl, rfl, isInGeneralPosition_Λinf hc⟩

end Polyfold.Examples.OrbifoldSquareInf
