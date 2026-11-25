import Polyfold.Examples.Classical.ProductSection

/-!
# The classical reduction crossed with the weighted `ℓ²` factor: the multisection

For Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Theorem 16.6.6,
2021 p. 739, with Definitions 13.2.1, 15.3.5, 16.5.1, 16.5.4 and 16.6.4.  The multisection of
constant branches of `Perturbation.lean` is crossed with the zero section of `H ◁ H`, as in
`OrbifoldSquareInfPerturbation.lean`.

## What is formalized (namespace `Polyfold.Examples.Classical.Product`)

* `branchP σ c g`: the sc⁺-section `(x, e) ↦ ((x, σ g c), (e, 0))`; `ΛP σ c`: the multisection
  with these branches, `g ∈ G`, weight `1/♯G` each; `ΛP_eq` (it is `ΛG σ c` on the `ℝⁿ`-part
  where the `H`-part of the fibre vanishes), `isWFunctor_ΛP`, `isLocalRepOn_ΛP`,
  `isScPlusMultisection_ΛP` (Definition 13.2.1).
* `ΛP_fP`, `ΛP_fP_eq`, `ΛP_fP_pos_iff`: `Λ(f(x, e)) = ♯{g | φ x = σ g c} / ♯G` for `e = 0`, and
  `0` otherwise.
* `negP b`, `subSec_branchP`: `f − s_g = f + (−s_g)` with `−s_g(x, e) = ((x, −σ g c), (e, 0))`.
* **`isInGeneralPosition_ΛP`** (Definition 15.3.5), for a regular value `c` of `φ`: at a
  solution `(x, 0)`, `φ x = σ g c`, in the product of the chart of `ℝⁿ` centred at `x` and the
  chart of `H`, the linearization `(f − s_g)'(x, 0) = (Dφ(x), id)` is onto `ℝⁿ × H`.
* `tP σ c`, `isControlledBy_tP` (for `gNorm σ c ≤ 1`), `isInGeneralPositionWith_tP`: the
  sc⁺-multisection of the strong polyfold bundle (Definition 16.5.1) is controlled by `(n, Z)`
  (Definition 16.5.4) and `(f, λ)` is in general position (Definition 16.6.4).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical.Product

open TrivialBundle EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure WeightedEllTwo SBLocalization StrongRetr Linearization15
  Polyfold.Examples.OrbifoldSquareInf Polyfold.Examples.Classical

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]
  [FaithfulSMul G (Fin n → ℝ)]
  (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) {φ : (Fin n → ℝ) → (Fin n → ℝ)}

/-! ### The branches -/

/-- The branch `(x, e) ↦ ((x, σ g c), (e, 0))`. -/
def branchP (c : Fin n → ℝ) (g : G) : (AP σ).Obj → (AP σ).W :=
  Prod.map (branchG σ c g) (constSec 0)

theorem branchP_apply (c : Fin n → ℝ) (g : G) (x : (Fin n → ℝ) × HObj) :
    branchP σ c g x = ((x.1, σ g c), (x.2, (0 : H 0))) := rfl

theorem isScPlusSection_branchP (c : Fin n → ℝ) (g : G) :
    (AP σ).B.IsScPlusSection (branchP σ c g) :=
  StrongBundle.IsScPlusSection.prod (isScPlusSection_branchG σ c g)
    (isScPlusSection_constSec H.smooth.zero_mem)

theorem eq_branchP_iff (c : Fin n → ℝ) (g : G) (w : (AG σ).W × (HObj × H 0)) :
    (w : (AP σ).W) = branchP σ c g ((AP σ).P w) ↔
      w.1 = branchG σ c g ((AG σ).P w.1) ∧ w.2.2 = 0 := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg (fun p : (AG σ).W × (HObj × H 0) => p.2.2) h⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext h1 (Prod.ext rfl h2)

open scoped _root_.Classical in
/-- **The multisection `Λ`** with the branches `branchP σ c g`, `g ∈ G`, of weight `1/♯G`
each. -/
def ΛP (c : Fin n → ℝ) : (AP σ).W → ℚ≥0 := fun w =>
  ∑ g : G, if w = branchP σ c g ((AP σ).P w) then (1 / Fintype.card G : ℚ≥0) else 0

open scoped _root_.Classical in
/-- `Λ` is `ΛG σ c` on the `ℝⁿ`-part where the `H`-part of the fibre vanishes, and `0`
elsewhere. -/
theorem ΛP_eq (c : Fin n → ℝ) (w : (AG σ).W × (HObj × H 0)) :
    ΛP σ c w = if w.2.2 = 0 then ΛG σ c w.1 else 0 := by
  unfold ΛP ΛG
  split_ifs with h
  · refine Finset.sum_congr rfl fun g _ => ?_
    have e := eq_branchP_iff σ c g w
    by_cases hg : w.1 = branchG σ c g ((AG σ).P w.1)
    · exact (if_pos (e.2 ⟨hg, h⟩)).trans (if_pos hg).symm
    · exact (if_neg fun h' => hg (e.1 h').1).trans (if_neg hg).symm
  · refine Finset.sum_eq_zero fun g _ => if_neg fun hg => h ?_
    exact ((eq_branchP_iff σ c g w).1 hg).2

theorem ΛP_pos_iff (c : Fin n → ℝ) (w : (AP σ).W) :
    0 < ΛP σ c w ↔ ∃ g : G, w = branchP σ c g ((AP σ).P w) := by
  classical
  unfold ΛP
  rw [Finset.sum_pos_iff]
  constructor
  · rintro ⟨g, -, hg⟩
    by_cases h : w = branchP σ c g ((AP σ).P w)
    · exact ⟨g, h⟩
    · rw [if_neg h] at hg
      exact absurd hg (lt_irrefl _)
  · rintro ⟨g, hg⟩
    refine ⟨g, Finset.mem_univ _, ?_⟩
    rw [if_pos hg]
    exact one_div_card_pos (G := G)

open scoped _root_.Classical in
/-- **`Λ` is a functor** `W → ℚ⁺` (Definition 13.2.1). -/
theorem isWFunctor_ΛP (c : Fin n → ℝ) : IsWFunctor (AP σ) (ΛP σ c) := by
  rintro ⟨⟨m, w⟩, hq⟩
  have hq1 : (m.1, w.1) ∈ pullbackSpace (AG σ).P (AG σ).X.src := congrArg Prod.fst hq
  have h1 : ΛG σ c ((AG σ).E.μ ⟨(m.1, w.1), hq1⟩) = ΛG σ c w.1 :=
    isWFunctor_ΛG σ c ⟨(m.1, w.1), hq1⟩
  refine (ΛP_eq σ c (((AG σ).E.μ ⟨(m.1, w.1), hq1⟩, w.2) : (AG σ).W × (HObj × H 0))).trans
    (Eq.trans ?_ (ΛP_eq σ c w).symm)
  exact if_congr Iff.rfl h1 rfl

/-- The branches `branchP σ c g`, indexed by `Fin ♯G`, with weight `1/♯G`, are a local
representation of `Λ` on `ℝⁿ × H`. -/
theorem isLocalRepOn_ΛP (c : Fin n → ℝ) :
    IsLocalRepOn (AP σ) (ΛP σ c) univ (k := Fintype.card G)
      (fun i => branchP σ c ((Fintype.equivFin G).symm i))
      (fun _ => (1 / Fintype.card G : ℚ≥0)) := by
  classical
  refine ⟨fun _ => one_div_card_pos (G := G),
    fun i => IsScPlusSectionOn.of_isScPlusSection (isScPlusSection_branchP σ c _) isOpen_univ,
    ?_, fun w _ => ?_⟩
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div,
      div_self (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]
  · unfold ΛP
    refine Fintype.sum_equiv (Fintype.equivFin G) _ _ fun g => ?_
    simp only [Equiv.symm_apply_apply]

/-- **`Λ` is an sc⁺-multisection** (Definition 13.2.1). -/
theorem isScPlusMultisection_ΛP (c : Fin n → ℝ) : IsScPlusMultisection (AP σ) (ΛP σ c) :=
  ⟨isWFunctor_ΛP σ c, fun x₀ => hasLocalSectionStructure_of_isLocalRepOn isOpen_univ
    (mem_univ x₀) (isLocalRepOn_ΛP σ c)⟩

/-! ### The perturbed solution set -/

open scoped _root_.Classical in
/-- `Λ(f(x, e)) = Λ_G(x, φ x)` for `e = 0`, and `0` otherwise. -/
theorem ΛP_fP (c : Fin n → ℝ) (x : (Fin n → ℝ) × HObj) :
    ΛP σ c (fP σ φ x) = if x.2 = h0 then ΛG σ c (fSec φ x.1) else 0 := by
  refine (ΛP_eq σ c (fSec φ x.1, OrbifoldSquareInf.idSec x.2)).trans ?_
  exact if_congr hobj_eq_h0_iff.symm rfl rfl

open scoped _root_.Classical in
/-- **`Λ(f(x, e)) = ♯{g | φ x = σ g c} / ♯G`** for `e = 0`, and `0` otherwise. -/
theorem ΛP_fP_eq (c : Fin n → ℝ) (x : (Fin n → ℝ) × HObj) :
    ΛP σ c (fP σ φ x) = if x.2 = h0 then
      ((Finset.univ.filter fun g : G => φ x.1 = σ g c).card : ℚ≥0) / Fintype.card G
      else 0 := by
  rw [ΛP_fP, ΛG_fSec]

/-- `Λ(f(x, e)) > 0` iff `e = 0` and `φ x = σ g c` for some `g`. -/
theorem ΛP_fP_pos_iff (c : Fin n → ℝ) (x : (Fin n → ℝ) × HObj) :
    0 < ΛP σ c (fP σ φ x) ↔ (∃ g : G, φ x.1 = σ g c) ∧ x.2 = h0 := by
  classical
  rw [ΛP_fP]
  split_ifs with h
  · rw [ΛG_fSec_pos_iff]
    exact (and_iff_left h).symm
  · exact ⟨fun h0' => absurd h0' (lt_irrefl _), fun h' => absurd h'.2 h⟩

/-- A perturbed solution `(x, e)` has `e = 0` and `φ x = σ g c` for some `g`. -/
theorem mem_hitSet_of_ΛP_pos {c : Fin n → ℝ} {x : (Fin n → ℝ) × HObj}
    (hx : 0 < ΛP σ c (fP σ φ x)) : (∃ g : G, φ x.1 = σ g c) ∧ x.2 = h0 :=
  (ΛP_fP_pos_iff σ c x).1 hx

/-! ### The sections `(x, e) ↦ ((x, −b), (e, 0))` -/

/-- The section `(x, e) ↦ ((x, −b), (e, 0))`. -/
def negP (b : Fin n → ℝ) : (AP σ).Obj → (AP σ).W :=
  Prod.map (graphSection fun _ => -b) (constSec 0)

theorem isScPlusSection_negP (b : Fin n → ℝ) : (AP σ).B.IsScPlusSection (negP σ b) :=
  StrongBundle.IsScPlusSection.prod (isScPlusSection_graphSection contDiff_const)
    (isScPlusSection_constSec H.smooth.zero_mem)

/-- `f − s_g = f + (−s_g)` for the branch `s_g(x, e) = ((x, σ g c), (e, 0))`. -/
theorem subSec_branchP (c : Fin n → ℝ) (g : G) :
    subSec (A := AP σ) (fP σ φ) (branchP σ c g) univ =
      sectionAdd (AP σ).P (fP σ φ) (negP σ (σ g c)) := by
  have hsec : IsSection (AP σ).P (branchP σ c g) := (isScPlusSection_branchP σ c g).1
  have he : extendZero (A := AP σ) univ (branchP σ c g) = branchP σ c g :=
    funext fun y => (extendZero_eqOn (A := AP σ) (fun y _ => hsec y) (mem_univ y)).symm
  unfold subSec
  rw [he]
  congr 1
  funext x
  obtain ⟨z, e⟩ : (Fin n → ℝ) × HObj := x
  refine (sectionSmul_apply hsec ((z, e) : (AP σ).Obj)).trans ?_
  let PH' : HObj × H 0 → HObj := LocalBundle.proj (E := H) (U := (univ : Set (H 0))) (F := H)
  let Φ := prodFiberCLE (proj n n) PH' ((z, e) : (Fin n → ℝ) × HObj)
  let v : Prod.map (proj n n) PH' ⁻¹' {((z, e) : (Fin n → ℝ) × HObj)} :=
    ⟨branchP σ c g ((z, e) : (AP σ).Obj), rfl⟩
  change ((((-1 : ℝ) • v : Prod.map (proj n n) PH' ⁻¹' {((z, e) : (Fin n → ℝ) × HObj)}) :
    ((Fin n → ℝ) × (Fin n → ℝ)) × (HObj × H 0))) = ((z, -σ g c), (e, (0 : H 0)))
  have hΦ : Φ ((-1 : ℝ) • v) = (-1 : ℝ) • Φ v := map_smul Φ _ _
  have h1 : (((Φ ((-1 : ℝ) • v)).1 : proj n n ⁻¹' {z}) : (Fin n → ℝ) × (Fin n → ℝ)) =
      (z, -σ g c) := by
    refine (congrArg Subtype.val (congrArg Prod.fst hΦ)).trans ?_
    refine Prod.ext (fst_fiber _) ?_
    refine (snd_smul _ _).trans ?_
    change (-1 : ℝ) • σ g c = -σ g c
    rw [neg_one_smul]
  have h2 : (((Φ ((-1 : ℝ) • v)).2 : PH' ⁻¹' {e}) : HObj × H 0) = (e, (0 : H 0)) := by
    refine (congrArg Subtype.val (congrArg Prod.snd hΦ)).trans ?_
    have h0' : (Φ v).2 = 0 := by
      apply (LocalBundle.fibEquiv (F := H) e).injective
      exact ((LocalBundle.fibEquiv (F := H) e).linearEquiv ℝ).map_zero.symm
    have hs : ((-1 : ℝ) • Φ v).2 = 0 := by
      change (-1 : ℝ) • (Φ v).2 = 0
      rw [h0', smul_zero]
    refine (congrArg Subtype.val hs).trans ?_
    refine Prod.ext rfl ?_
    exact ((LocalBundle.fibEquiv (F := H) e).linearEquiv ℝ).map_zero
  exact Prod.ext h1 h2

/-! ### General position -/

/-- In a chart whose partial quadrant is the whole space the reduced tangent space is the tangent
space. -/
theorem mem_reducedTangentFiber_of_univ_P {ψ : MChart (AP σ).Obj}
    (hψ : (AP σ).X.PObj.IsChart ψ) {x : (AP σ).X.PObj.Level 1}
    (hx : (AP σ).X.PObj.levelVal 1 x ∈ ψ.source) {k : ℕ} {V : ScBanach}
    (T : ScIso ψ.model.E ((ScBanach.const (Fin k → ℝ)).prod V))
    (hT : ψ.model.C = T 0 ⁻¹' quadrant k V 0) (hC : ψ.model.C = univ)
    (α : (AP σ).X.PObj.tangentFiber x) : α ∈ reducedTangentFiber hψ hx T := by
  have h0 : ∀ (v : ψ.model.E 0) (i : Fin k), (T 0 v).1 i = 0 := by
    intro v i
    have h1 : ∀ u : ψ.model.E 0, 0 ≤ (T 0 u).1 i := fun u => by
      have hu : u ∈ T 0 ⁻¹' quadrant k V 0 := by rw [← hT, hC]; exact mem_univ u
      exact hu i
    have h2 := h1 v
    have h3 := h1 (-v)
    rw [map_neg] at h3
    have h4 : (-(T 0 v)).1 i = -((T 0 v).1 i) := rfl
    rw [h4] at h3
    linarith
  exact Submodule.mem_comap.2 ((mem_minimalSubspaceWith T).2 fun i _ => h0 _ i)

variable {σ}

/-- **`(f, Λ)` is in general position** (Definition 15.3.5) for a regular value `c` of `φ`: at a
solution `(x, 0)` with `φ x = σ g c`, in the product of the chart of `ℝⁿ` centred at `x` and the
chart of `H`, `(f − s_g)'(x, 0) = (Dφ(x), id)` is onto `ℝⁿ × H`, since `Dφ(x)` is onto
(`surjective_fderiv_of_eq`), and `ℝⁿ × H` has no boundary. -/
theorem isInGeneralPosition_ΛP (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) {c : Fin n → ℝ}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x)) :
    IsInGeneralPosition (AP σ) (fP σ φ) (ΛP σ c) := by
  classical
  have hf := isScFredholmSectionFunctor_fP hφ heq
  refine isInGeneralPosition_iff_exists.2 fun x hpos => ?_
  set x₀ : (Fin n → ℝ) × HObj := (AP σ).X.PObj.levelVal 1 x with hx₀
  obtain ⟨-, hx2⟩ := (ΛP_fP_pos_iff σ c x₀).1 hpos
  let ch : StrongBundleChart (AP σ).X.PObj (AP σ).P :=
    (chart (k := n) x₀.1).prod (LocalBundle.chart (F := H) relOpen_H h0)
  have hch : (AP σ).B.IsChart ch :=
    StrongBundle.IsChart.prod (isChart_chart (k := n) x₀.1)
      (LocalBundle.isChart_chart (F := H) relOpen_H h0)
  have hx : (AP σ).X.PObj.levelVal 1 x ∈ ch.φ.source := ⟨mem_univ _, mem_univ _⟩
  obtain ⟨k, V, T, hT⟩ := ch.φ.model.isPartialQuadrant
  refine ⟨ch.φ, ch.isChart, hx, k, V, T, hT, fun L hL => ?_⟩
  have hsurj : Surjective L := by
    let d : LocalLinData (AP σ) (ΛP σ c) x :=
      ⟨univ, isOpen_univ, Fintype.card G, fun i => branchP σ c ((Fintype.equivFin G).symm i),
        fun _ => (1 / Fintype.card G : ℚ≥0), isLocalRepOn_ΛP σ c, ch, hch, subset_univ _, hx⟩
    rw [linearization_eq hf d] at hL
    obtain ⟨i, hi, hLi⟩ := (mem_support_linSumIntr_iff (k := Fintype.card G)
      (s := fun i => branchP σ c ((Fintype.equivFin G).symm i))
      (σ := fun _ => (1 / Fintype.card G : ℚ≥0)) hf.1.1.1
      (fun _ => one_div_card_pos (G := G)) (fun _ z _ => rfl) (subset_univ _) hx L).1 hL
    rw [← hLi]
    have hsi := IsScPlusSectionOn.of_isScPlusSection (A := AP σ)
      (isScPlusSection_branchP σ c ((Fintype.equivFin G).symm i)) isOpen_univ
    refine (surjective_toIntr_subDeriv_iff hf.1.1 hsi hch (subset_univ _) hx hi.symm).2 ?_
    set b : Fin n → ℝ := σ ((Fintype.equivFin G).symm i) c with hb
    have hsol : φ x₀.1 = b := (congrArg (fun p : (AP σ).W => p.1.2) hi).symm
    set z := levelLift ch.φ 1 ((AP σ).X.PObj.levelVal 1 x) with hzdef
    have hφ0 : ch.φ x₀ = (0 : (Fin n → ℝ) × H 0) :=
      Prod.ext (sub_self (show Fin n → ℝ from x₀.1)) (congrArg Subtype.val hx2)
    have hzb : ch.φ.model.E.toBase 1 z = (0 : (Fin n → ℝ) × H 0) :=
      ((AP σ).X.PObj.toBase_levelLift ch.isChart hx ((AP σ).X.PObj.levelVal_mem x)).trans hφ0
    have hzU : z ∈ ch.φ.model.E.lvlSet ch.U 1 := by
      change ch.φ.model.E.toBase 1 z ∈ ch.U
      exact ⟨mem_univ _, mem_univ _⟩
    have hr : r ch.R = id := funext fun u => rfl
    have hDr : scDeriv ch.U (r ch.R) z = ContinuousLinearMap.id ℝ _ := by
      rw [hr]
      exact scDeriv_eq_of_hasFDerivAt ch.relOpen
        (isScSmooth_id ch.relOpen.isScDomain 1).isSc1 hzU (hasFDerivAt_id _)
    let D1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := fderiv ℝ (φ - fun _ => b) x₀.1
    have hD1 : HasFDerivAt (φ - fun _ => b) D1 x₀.1 :=
      ((hφ.sub contDiff_const).differentiable (by simp)).differentiableAt.hasFDerivAt
    let D : (Fin n → ℝ) × H 0 →L[ℝ] (Fin n → ℝ) × H 0 :=
      (D1.comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (H 0))).prod
        (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (H 0))
    have hcomp : ((fun y => ch.principal (fP σ φ) y -
        ch.principal (branchP σ c ((Fintype.equivFin G).symm i)) y) ∘ r ch.R) =
        fun u : (Fin n → ℝ) × H 0 => (φ (u.1 + x₀.1) - b, u.2) := by
      rw [hr]
      funext u
      have h1 : ((LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm u.2 : H 0) = u.2 :=
        (LocalBundle.baseChart relOpen_H h0).toPartialEquiv.right_inv (mem_univ _)
      refine Prod.ext rfl ?_
      change ((LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm u.2 : H 0) - 0 = u.2
      exact (congrArg (fun t : H 0 => t - 0) h1).trans (sub_zero (show H 0 from u.2))
    have hDg : subDeriv ch (fP σ φ) (branchP σ c ((Fintype.equivFin G).symm i)) z = D := by
      refine scDeriv_eq_of_hasFDerivAt ch.relOpen
        (isSc1_sub_comp_r hf.1.1 hsi hch (subset_univ _)) hzU ?_
      rw [hcomp, hzb]
      have h1 : HasFDerivAt (fun u : (Fin n → ℝ) × H 0 => u.1 + x₀.1)
          (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (H 0)) 0 := hasFDerivAt_fst.add_const _
      have hD1' : HasFDerivAt (φ - fun _ => b) D1 ((0 : (Fin n → ℝ) × H 0).1 + x₀.1) := by
        rw [Prod.fst_zero, zero_add]
        exact hD1
      exact (hD1'.comp (0 : (Fin n → ℝ) × H 0) h1).prodMk hasFDerivAt_snd
    intro w _
    obtain ⟨v1, hv1⟩ := surjective_fderiv_sub_const hφ
      (surjective_fderiv_of_eq hφ heq hc hsol) b (show (Fin n → ℝ) × H 0 from w).1
    refine ⟨((v1, (show (Fin n → ℝ) × H 0 from w).2) : (Fin n → ℝ) × H 0),
      ⟨((v1, (show (Fin n → ℝ) × H 0 from w).2) : (Fin n → ℝ) × H 0), ?_⟩, ?_⟩
    · exact congrArg (fun S : ch.φ.model.E 0 →L[ℝ] ch.φ.model.E 0 =>
        S ((v1, (show (Fin n → ℝ) × H 0 from w).2) : (Fin n → ℝ) × H 0)) hDr
    · rw [hDg]
      exact Prod.ext hv1 rfl
  intro w
  obtain ⟨α, hα⟩ := hsurj w
  exact ⟨⟨α, mem_reducedTangentFiber_of_univ_P σ ch.isChart hx T hT univ_prod_univ α⟩, hα⟩

/-! ### The sc⁺-multisection of the strong polyfold bundle -/

variable (σ) in
/-- **The sc⁺-multisection `λ`** of the strong polyfold bundle over `(ℝⁿ × H)/G`, the class of
`Λ` (Definition 16.5.1). -/
def tP (c : Fin n → ℝ) : ScPlusMultisection (prBundle σ) :=
  ⟦ofFunctor (prStructure σ) rfl (ΛP σ c) (isScPlusMultisection_ΛP σ c)⟧

/-- `N(Λ)(x) ≤ 1` for `gNorm σ c ≤ 1`. -/
theorem pointwiseNorm_ΛP_le {c : Fin n → ℝ} (hc1 : gNorm σ c ≤ 1) (x : (Fin n → ℝ) × HObj) :
    pointwiseNorm (A := AP σ) (NP σ) (ΛP σ c) x ≤ 1 := by
  refine csSup_le ⟨_, mem_image_of_mem _ (⟨rfl, (ΛP_pos_iff σ c _).2 ⟨1, rfl⟩⟩ :
    branchP σ c 1 x ∈ suppAt (A := AP σ) (ΛP σ c) x)⟩ ?_
  rintro _ ⟨w, ⟨-, hw⟩, rfl⟩
  obtain ⟨g, hg⟩ := (ΛP_pos_iff σ c w).1 hw
  rw [hg]
  refine (normW_NP_zero σ (((AP σ).P w).1, σ g c) ((AP σ).P w).2).trans_le ?_
  change gNorm σ (σ g c) ≤ 1
  rw [gNorm_smul_invariant]
  exact hc1

/-- **`λ` is controlled by `(n, Z)`** (Definition 16.5.4), for `gNorm σ c ≤ 1`. -/
theorem isControlledBy_tP {c : Fin n → ℝ} (hc1 : gNorm σ c ≤ 1) :
    (tP σ c).IsControlledBy (nP σ) (univ : Set (AP σ).X.OrbitSpace) := by
  refine ⟨fun z => ?_, subset_univ _⟩
  obtain ⟨x, rfl⟩ := (prStructure σ).surjective_γπ z
  set b := ofFunctor (prStructure σ) rfl (ΛP σ c) (isScPlusMultisection_ΛP σ c)
  have h := normLam_eq (c := prBundle σ) (S := prStructure σ) rfl (nP σ) (ΛP σ c) b.lam x
    fun w _ => b.comm w
  rw [normOf_nP] at h
  exact h.le.trans (pointwiseNorm_ΛP_le hc1 x)

/-- **`(f, λ)` is in general position** (Definition 16.6.4), for a regular value `c` of `φ`. -/
theorem isInGeneralPositionWith_tP (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) {c : Fin n → ℝ}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x)) :
    (prFredholmSection σ hφ heq).1.IsInGeneralPositionWith (tP σ c) :=
  ⟨prRep σ hφ heq, ΛP σ c, isScPlusMultisection_ΛP σ c, rfl, rfl,
    isInGeneralPosition_ΛP hφ heq hc⟩

end Polyfold.Examples.Classical.Product
