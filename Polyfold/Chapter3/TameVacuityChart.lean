import Polyfold.Chapter3.NonVacuity
import Polyfold.Chapter3.TameVacuity

/-!
# The old hypothesis `htame` fails for the witness bundle of `NonVacuity.lean`

The chart-level form of Findings, Chapter 3 item 190, for a concrete strong bundle: for the trivial
strong bundle `ℝⁿ × ℝᵏ → ℝⁿ` of `NonVacuity.lean` (`TrivialBundle.bundle n k`), **not every
compatible strong bundle chart has a tame base retraction**
(`TrivialBundle.not_forall_isTame_of_isChart`).  So the hypothesis
`htame : ∀ c, B.IsChart c → (base retraction of c).IsTame` with which the §3.6 theorems were first
stated fails for this bundle, while the repaired hypotheses hold for it
(`TrivialBundle.hypotheses_theorem_3_6_11_graphSection_wholeChart`): the repair was needed, and the bundle
separates the two forms (`TrivialBundle.htame_fails_repaired_holds_wholeChart`).

The chart is the construction of item 190: the model `(ℝ ⊕ ℝ⁰) ⊕ ℝⁿ` with the partial quadrant
`[0, ∞) × ℝⁿ`, the retraction `r(a, u) = (1, u)` (the product of the constant retraction
`ScRetraction.halfLineConst` with the identity of `ℝⁿ`), whose retract is `{1} × ℝⁿ`, the chart
`x ↦ (1, x)` of `ℝⁿ`, and the strong bundle retraction `R((a, u), h) = ((1, u), h)`.  Its
transition maps with the translation charts are affine, so it is compatible with the atlas; its
base retraction is not tame (`ScRetraction.halfLineConst_prod_not_isTame`, `TameVacuity.lean`:
at `(0, u)` the degeneracy index is `1`, at `r(0, u) = (1, u)` it is `0`).

Not in the text (Findings, Chapter 3 item 202).
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace TrivialBundle

variable {n k : ℕ}

/-- The sc-Banach space `(ℝ ⊕ ℝ⁰) ⊕ ℝⁿ` of the non-tame chart. -/
abbrev Eodd (n : ℕ) : ScBanach := (halfLineSc zeroSc).prod (rnSc n)

lemma bijective_toBase_Eodd (j : ℕ) : Bijective ((Eodd n).toBase j) :=
  bijective_toBase_prod (bijective_toBase_param _) (bijective_toBase_const _) j

/-- **The non-tame retraction** `r(a, u) = (1, u)` of `[0, ∞) × ℝⁿ`. -/
abbrev Rodd (n : ℕ) : ScRetraction (Eodd n) (quadrant 1 zeroSc 0 ×ˢ univ) :=
  (ScRetraction.halfLineConst zeroSc).prod (ScRetraction.id (rn_relOpen_univ n))

lemma Rodd_retract : (Rodd n).retract = {halfLineOne zeroSc} ×ˢ univ := by
  rw [ScRetraction.prod_retract, ScRetraction.halfLineConst_retract]
  congr 1
  exact image_id _

lemma mem_Rodd_retract {p : (Eodd n) 0} : p ∈ (Rodd n).retract ↔ p.1 = halfLineOne zeroSc := by
  rw [Rodd_retract]; exact ⟨fun h => h.1, fun h => ⟨h, mem_univ _⟩⟩

/-- **The chart** `x ↦ (1, x)` of `ℝⁿ` onto the retract `{1} × ℝⁿ` of `Rodd`. -/
def oddChart : MChart (Fin n → ℝ) where
  model := ⟨Eodd n, quadrant 1 zeroSc 0 ×ˢ univ, (Rodd n).retract, ⟨Rodd n, rfl⟩⟩
  toPartialEquiv :=
    { toFun := fun x => ((halfLineOne zeroSc, x) : (Eodd n) 0)
      invFun := fun p => p.2
      source := univ
      target := (Rodd n).retract
      map_source' := fun _ _ => mem_Rodd_retract.2 rfl
      map_target' := fun _ _ => mem_univ _
      left_inv' := fun _ _ => rfl
      right_inv' := fun _ hp => Prod.ext (mem_Rodd_retract.1 hp).symm rfl }
  isOpen_source := isOpen_univ
  target_eq := rfl
  continuousOn_toFun := (continuous_const.prodMk continuous_id).continuousOn
  continuousOn_invFun := continuous_snd.continuousOn

lemma oddChart_overlap : (oddChart (n := n)).overlap (rnChart n 0) = (Rodd n).retract := by
  ext p
  refine ⟨?_, fun hp => ⟨p.2, ⟨mem_univ _, mem_univ _⟩, Prod.ext (mem_Rodd_retract.1 hp).symm rfl⟩⟩
  rintro ⟨x, -, rfl⟩
  exact mem_Rodd_retract.2 rfl

lemma rnChart_overlap_odd : (rnChart n 0).overlap (oddChart (n := n)) = univ :=
  eq_univ_of_forall fun x => ⟨x, ⟨mem_univ _, mem_univ _⟩, sub_zero x⟩

/-- `oddChart` is compatible with the chart `id` of `ℝⁿ` (transitions `(1, x) ↦ x`, `x ↦ (1, x)`). -/
theorem isChart_oddChart : (rnPolyfold n).IsChart (oddChart (n := n)) := by
  intro ψ hψ
  rw [mem_singleton_iff.1 hψ]
  refine ⟨?_, ?_⟩
  · rw [oddChart_overlap, rnChart_overlap_odd]
    refine (isScSmoothRetractMap_iff_exists ⟨Rodd n, rfl⟩).2 ⟨mapsTo_univ _ _, Rodd n, rfl, ?_⟩
    exact isScSmooth_of_bijective_toBase bijective_toBase_Eodd (bijective_toBase_const _)
      (Rodd n).isScDomain (f := fun p : (Eodd n) 0 => (p.2 : Fin n → ℝ) - 0)
      (contDiff_snd.sub contDiff_const).contDiffOn
  · rw [oddChart_overlap, rnChart_overlap_odd]
    exact isScSmoothRetractMap_of_bijective_toBase (bijective_toBase_const _)
      bijective_toBase_Eodd (rn_relOpen_univ n) (fun _ _ => mem_Rodd_retract.2 rfl)
      (g := fun x : Fin n → ℝ => ((halfLineOne zeroSc, x + 0) : (Eodd n) 0))
      (contDiff_const.prodMk (contDiff_id.add contDiff_const))

/-- The strong bundle retraction `R((a, u), h) = ((1, u), h)` on `([0, ∞) × ℝⁿ) ◁ ℝᵏ`. -/
def Rbodd : (Eodd n) 0 × (rnSc k) 0 → (Eodd n) 0 × (rnSc k) 0 :=
  fun q => ((halfLineOne zeroSc, q.1.2), q.2)

lemma bijective_toBase_EoddF (j : ℕ) : Bijective (((Eodd n).prod (rnSc k)).toBase j) :=
  bijective_toBase_prod bijective_toBase_Eodd (bijective_toBase_const _) j

lemma bijective_toBase_EoddF1 (j : ℕ) : Bijective (((Eodd n).prod (rnSc k).shift).toBase j) :=
  bijective_toBase_prod bijective_toBase_Eodd (bijective_toBase_shift (bijective_toBase_const _)) j

lemma contDiff_Rbodd : ContDiff ℝ ∞ (Rbodd (n := n) (k := k)) :=
  (contDiff_const.prodMk contDiff_fst.snd).prodMk contDiff_snd

lemma isStrongBundleRetraction_Rbodd :
    IsStrongBundleRetraction (Rodd n).U (Rbodd (n := n) (k := k)) where
  mapsTo q hq := ⟨(Rodd n).mapsTo hq.1, mem_univ _⟩
  fst_independent _ _ _ _ := rfl
  fiber_linear _ _ := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  preserves_filtration j l _ _ _ _ _ _ :=
    ⟨(bijective_toBase_Eodd j).2 _, (bijective_toBase_const _ l).2 _⟩
  isScSmooth_zero := isScSmooth_of_bijective_toBase bijective_toBase_EoddF bijective_toBase_EoddF
    ((Rodd n).relOpen.prod_univ (rnSc k)).isScDomain contDiff_Rbodd.contDiffOn
  isScSmooth_one := by
    have hU := ((Rodd n).relOpen.prod_univ (rnSc k).shift).isScDomain
    refine (isScSmooth_of_bijective_toBase bijective_toBase_EoddF1 bijective_toBase_EoddF1 hU
      (f := Rbodd (n := n) (k := k)) contDiff_Rbodd.contDiffOn).congr hU fun p _ => ?_
    refine Prod.ext rfl ?_
    change p.2 = invFun ((rnSc k).toBase 1) ((rnSc k).toBase 1 p.2)
    rw [leftInverse_invFun ((rnSc k).toBase_injective 1)]
  idem _ _ := rfl

/-- **The non-tame strong bundle chart** of `ℝⁿ × ℝᵏ → ℝⁿ`: over `oddChart`, with the strong
bundle retraction `Rbodd`, `(x, v) ↦ ((1, x), v)`. -/
def oddBundleChart : StrongBundleChart (rnPolyfold n) (proj n k) where
  φ := oddChart
  isChart := isChart_oddChart
  F := rnSc k
  U := (Rodd n).U
  R := Rbodd
  relOpen := (Rodd n).relOpen
  isRetraction := isStrongBundleRetraction_Rbodd
  base_retract := rfl
  toPartialEquiv := oddChart.toPartialEquiv.prod (PartialEquiv.refl (Fin k → ℝ))
  source_eq := by
    change (univ : Set (Fin n → ℝ)) ×ˢ (univ : Set (Fin k → ℝ)) = proj n k ⁻¹' univ
    rw [univ_prod_univ, preimage_univ]
  target_eq := by
    change (Rodd n).retract ×ˢ (univ : Set (Fin k → ℝ)) = Rbodd '' ((Rodd n).U ×ˢ univ)
    ext ⟨p, v⟩
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, -⟩
      exact ⟨(u, v), ⟨hu, mem_univ _⟩, rfl⟩
    · rintro ⟨q, hq, hqe⟩
      rw [← hqe]
      exact ⟨⟨q.1, hq.1, rfl⟩, mem_univ _⟩
  continuousOn_toFun := oddChart.continuousOn_toFun.prodMap continuousOn_id
  continuousOn_invFun := oddChart.continuousOn_invFun.prodMap continuousOn_id
  covers _ _ := rfl
  fiber_linear x _ := isLinearMap_fibEquiv x

lemma oddBundleChart_overlap (a : Fin n → ℝ) :
    (oddBundleChart (k := k)).overlap (chart a) = (Rodd n).retract ×ˢ univ := by
  ext ⟨p, v⟩
  constructor
  · rintro ⟨⟨x, w⟩, -, hxw⟩
    rw [← hxw]
    exact ⟨mem_Rodd_retract.2 rfl, mem_univ _⟩
  · rintro ⟨hp, -⟩
    exact ⟨(p.2, v), ⟨⟨mem_univ _, mem_univ _⟩, mem_univ _⟩,
      Prod.ext (Prod.ext (mem_Rodd_retract.1 hp).symm rfl) rfl⟩

lemma chart_overlap_odd (a : Fin n → ℝ) :
    (chart (k := k) a).overlap oddBundleChart = univ := by
  refine eq_univ_of_forall fun (p : (Fin n → ℝ) × (Fin k → ℝ)) =>
    ⟨(p.1 + a, p.2), ⟨mem_univ _, ⟨mem_univ _, mem_univ _⟩⟩, ?_⟩
  change (p.1 + a - a, p.2) = p
  rw [add_sub_cancel_right]

lemma relOpen_univ_shift (k : ℕ) : IsRelOpenInQuadrant (rnSc k).shift univ univ :=
  ⟨isPartialQuadrant_univ _, univ, isOpen_univ, (inter_univ _).symm⟩

/-- **`oddBundleChart` is compatible with every translation chart**: its transitions are
`((1, x), v) ↦ (x − a, v)` and `(x, v) ↦ ((1, x + a), v)`. -/
theorem oddBundleChart_compatible (a : Fin n → ℝ) :
    (oddBundleChart (k := k)).Compatible (chart a) := by
  -- the retraction `Rodd × 1` of `([0, ∞) × ℝⁿ) ⊕ ℝᵏ` (and on `ℝᵏ¹`) onto the overlap
  let S := (Rodd n).prod (ScRetraction.id (rn_relOpen_univ k))
  let S1 := (Rodd n).prod (ScRetraction.id (relOpen_univ_shift k))
  have hS : S.retract = (Rodd n).retract ×ˢ univ := by
    rw [ScRetraction.prod_retract]; congr 1; exact image_id _
  have hS1 : S1.retract = (Rodd n).retract ×ˢ univ := by
    rw [ScRetraction.prod_retract]; congr 1; exact image_id _
  have hss : strongShiftOne ((oddBundleChart (k := k)).overlap (chart a)) =
      (Rodd n).retract ×ˢ univ := by
    rw [oddBundleChart_overlap]; rfl
  have hss' : strongShiftOne ((chart (k := k) a).overlap oddBundleChart) = univ := by
    rw [chart_overlap_odd]; rfl
  have hsf1 : shiftFiber ((oddBundleChart (k := k)).transition (chart a)) =
      fun p : (Eodd n) 0 × (Fin k → ℝ) => ((p.1.2 : Fin n → ℝ) - a, p.2) :=
    funext fun p => Prod.ext rfl (by
      change invFun ((rnSc k).toBase 1) ((rnSc k).toBase 1 p.2) = p.2
      exact leftInverse_invFun ((rnSc k).toBase_injective 1) p.2)
  have hsf2 : shiftFiber ((chart (k := k) a).transition oddBundleChart) =
      fun p : (Fin n → ℝ) × (Fin k → ℝ) =>
        (((halfLineOne zeroSc, p.1 + a) : (Eodd n) 0), p.2) :=
    funext fun p => Prod.ext rfl (by
      change invFun ((rnSc k).toBase 1) ((rnSc k).toBase 1 p.2) = p.2
      exact leftInverse_invFun ((rnSc k).toBase_injective 1) p.2)
  have hr : ∀ v : Fin k → ℝ, v ∈ range ((rnSc k).toBase 1) := fun v =>
    (bijective_toBase_const _ 1).2 v
  have hrel1 : IsRelOpenInQuadrant ((rnSc n).prod (rnSc k).shift) (univ ×ˢ univ) univ := by
    rw [← univ_prod_univ]; exact (rn_relOpen_univ n).prod_univ (rnSc k).shift
  refine ⟨?_, ?_, ?_, ?_, fun _ _ _ => hr _, fun _ _ _ => hr _⟩
  · rw [oddBundleChart_overlap, chart_overlap_odd]
    refine (isScSmoothRetractMap_iff_exists ⟨S, hS⟩).2 ⟨mapsTo_univ _ _, S, hS, ?_⟩
    exact isScSmooth_of_bijective_toBase bijective_toBase_EoddF bijective_toBase_model
      S.isScDomain (f := fun p : (Eodd n) 0 × (Fin k → ℝ) => ((p.1.2 : Fin n → ℝ) - a, p.2))
      ((contDiff_fst.snd.sub contDiff_const).prodMk contDiff_snd).contDiffOn
  · rw [oddBundleChart_overlap, chart_overlap_odd]
    exact isScSmoothRetractMap_of_bijective_toBase bijective_toBase_model bijective_toBase_EoddF
      relOpen_model (fun _ _ => ⟨mem_Rodd_retract.2 rfl, mem_univ _⟩)
      (g := fun p : (Fin n → ℝ) × (Fin k → ℝ) =>
        (((halfLineOne zeroSc, p.1 + a) : (Eodd n) 0), p.2))
      ((contDiff_const.prodMk (contDiff_fst.add contDiff_const)).prodMk contDiff_snd)
  · rw [hss, hss', hsf1]
    refine (isScSmoothRetractMap_iff_exists ⟨S1, hS1⟩).2 ⟨mapsTo_univ _ _, S1, hS1, ?_⟩
    exact isScSmooth_of_bijective_toBase bijective_toBase_EoddF1
      (bijective_toBase_prod (bijective_toBase_const _)
        (bijective_toBase_shift (bijective_toBase_const _)))
      S1.isScDomain (f := fun p : (Eodd n) 0 × (Fin k → ℝ) => ((p.1.2 : Fin n → ℝ) - a, p.2))
      ((contDiff_fst.snd.sub contDiff_const).prodMk contDiff_snd).contDiffOn
  · rw [hss, hss', hsf2]
    exact isScSmoothRetractMap_of_bijective_toBase
      (bijective_toBase_prod (bijective_toBase_const _)
        (bijective_toBase_shift (bijective_toBase_const _)))
      bijective_toBase_EoddF1 hrel1 (fun _ _ => ⟨mem_Rodd_retract.2 rfl, mem_univ _⟩)
      ((contDiff_const.prodMk (contDiff_fst.add contDiff_const)).prodMk contDiff_snd)

/-- `oddBundleChart` is a strong bundle chart of `TrivialBundle.bundle n k`. -/
theorem isChart_oddBundleChart : (bundle n k).IsChart (oddBundleChart (k := k)) := by
  rintro _ ⟨a, rfl⟩
  exact oddBundleChart_compatible a

/-- **The hypothesis `htame` of the first formalization of §3.6 fails for the trivial bundle**
(Findings, Chapter 3 item 190, for a concrete bundle): the base retraction of the compatible
strong bundle chart `oddBundleChart`, `r(a, u) = (1, u)`, is not tame. -/
theorem not_forall_isTame_of_isChart :
    ¬ ∀ c : StrongBundleChart (rnPolyfold n) (proj n k), (bundle n k).IsChart c →
      (c.isRetraction.baseRetraction c.relOpen).IsTame := by
  intro h
  exact ScRetraction.halfLineConst_prod_not_isTame zeroSc (ScRetraction.id (rn_relOpen_univ n))
    ⟨0, mem_univ _⟩ ((h _ isChart_oddBundleChart).congr rfl fun _ _ => rfl)

/-- **The trivial bundle separates the old and the repaired hypotheses**: for a surjective linear
`L : ℝⁿ → ℝᵏ`, the graph section of `L` meets the repaired hypotheses of Theorem 3.6.11 (preprint 3.57), while the
old hypothesis `htame` (every compatible chart has a tame base retraction) fails for the bundle. -/
theorem htame_fails_repaired_holds_wholeChart (L : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ)) (hL : Surjective L) :
    ((bundle n k).IsScFredholmSectionWholeChart (graphSection L) ∧
      ∀ x, IsZeroAt (proj n k) (graphSection L) x →
        (bundle n k).IsGoodPositionGermTameWholeChart (graphSection L) x) ∧
    ¬ ∀ c : StrongBundleChart (rnPolyfold n) (proj n k), (bundle n k).IsChart c →
      (c.isRetraction.baseRetraction c.relOpen).IsTame :=
  ⟨hypotheses_theorem_3_6_11_linear_wholeChart L hL, not_forall_isTame_of_isChart⟩

end TrivialBundle

end Polyfold
