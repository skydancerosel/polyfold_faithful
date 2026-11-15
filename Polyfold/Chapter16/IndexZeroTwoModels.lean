import Polyfold.Chapter16.PointCountEquivalence
import Polyfold.Chapter15.CylinderFaceOntoWitness
import Polyfold.Chapter9.DimensionZeroIntegral
import Polyfold.Chapter8.TangentZhou

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
**Theorem 16.6.6** (p. 739) for Fredholm index `0`, the independence of the count from the model.
Numbers and pages are the 2021 text's.

# Two different models with the same perturbed solution set

## The statement checked

`StrongPolyfoldBundle.count_eq_of_mk_eq` says: if regular perturbations of dimension `0` in the
models of two representatives `a`, `b` give the same oriented branched suborbifold of `Z`, the
weighted counts of every `0`-form agree.  Here its hypothesis is met with `a ≠ b`, non-zero
fibres and a non-empty perturbed solution set (the base is `ℝ`, so `∂X = ∅`; the statement does
not involve the boundary).

## The example

`W = ℝ × ℝ → ℝ` over the trivial ep-groupoid of `ℝ` (`epSEP 1 1`), with `Γ = id`, `γ = id`
(`epStructure`), and the strong polyfold bundle `epPolyfoldBundle` it defines.  The sections
`f(x) = (x, x)` and `g(x) = (x, −x)` give two representatives (`graphRep`) that differ.  For both,
`(N, U, Λ₀)` with the zero multisection `Λ₀` is a structurable regular perturbation
(`isTransversal_antidiagSection` for `g`), `Λ₀ ∘ f = Λ₀ ∘ g = 1_{0}`, and with the orientation `+`
of the point `0` both give the same oriented branched suborbifold `((1_{0}, +), (X, id))`.

* **`StrongPolyfoldBundle.count_eq_of_mk_eq_two_models`**: two representatives `a ≠ b`, regular
  perturbations of dimension `0` in their models with the same oriented branched suborbifold and
  non-empty support, so `count_eq_of_mk_eq` applies to them.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace TrivialBundle

open SBLocalization StrongBundle StrongRetr MPolyfold EpGroupoid SEP StrongBundleEquivalenceExamples

/-- The section `g(x) = (x, −x)` of `ℝ × ℝ → ℝ` (the graph of `−id`). -/
abbrev antidiagSection : (epSEP 1 1).Obj → (epSEP 1 1).W :=
  graphSection (fun u : Fin 1 → ℝ => -u)

theorem contDiff_neg_rn : ContDiff ℝ ∞ (fun u : Fin 1 → ℝ => -u) := contDiff_neg

/-- `g(x) = (x, −x)` is an sc-Fredholm section functor of `ℝ × ℝ → ℝ`. -/
theorem isScFredholmSectionFunctor_antidiagSection :
    (epSEP 1 1).E.IsScFredholmSectionFunctor antidiagSection :=
  graphSection_mem_fredholmSectionFunctors_epBundle contDiff_neg_rn

/-- `S_g = {0}`. -/
theorem solutionSet_antidiagSection :
    solutionSet (epSEP 1 1).P antidiagSection =
      {show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ)} := by
  ext x
  exact (isZeroAt_graphSection_iff (n := 1) (k := 1) (φ := fun u => -u) (x := x)).trans
    neg_eq_zero

/-- `Λ₀(g(x)) > 0` only at `x = 0`. -/
theorem eq_zero_of_zeroMultisection_antidiagSection_pos {x₀ : (epSEP 1 1).Obj}
    (h : 0 < zeroMultisection (epSEP 1 1) (antidiagSection x₀)) :
    x₀ = (show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ)) := by
  classical
  have aux : ∀ w : (epSEP 1 1).W, w = antidiagSection x₀ →
      0 < zeroMultisection (epSEP 1 1) w → x₀ = (show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ)) := by
    intro w hw hpos
    by_contra hne
    unfold zeroMultisection at hpos
    rw [if_neg] at hpos
    · exact lt_irrefl _ hpos
    · intro e
      apply hne
      subst hw
      exact neg_eq_zero.1
        ((isZeroAt_graphSection_iff (n := 1) (k := 1) (φ := fun u => -u) (x := x₀)).1 e)
  exact aux _ rfl h

/-- `Λ₀(g(0)) = 1`. -/
theorem zeroMultisection_antidiagSection_zero :
    zeroMultisection (epSEP 1 1)
      (antidiagSection (show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ))) = 1 := by
  classical
  have aux : ∀ w : (epSEP 1 1).W,
      w = antidiagSection (show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ)) →
      zeroMultisection (epSEP 1 1) w = 1 := by
    intro w hw
    have key : w = fiberZero (epSEP 1 1).P ((epSEP 1 1).P w) := by
      subst hw
      exact (isZeroAt_graphSection_iff (n := 1) (k := 1) (φ := fun u => -u)
        (x := (0 : Fin 1 → ℝ))).2 neg_zero
    unfold zeroMultisection
    rw [if_pos key]
  exact aux _ rfl

/-- **`(g, Λ₀)` is transversal** (Definition 15.2.1): at the only point `0` of `supp(Λ₀ ∘ g)`,
in the translation chart, `(g − 0)'(0) = −id` is onto `ℝ`. -/
theorem isTransversal_antidiagSection :
    IsTransversal antidiagSection (zeroMultisection (epSEP 1 1)) := by
  classical
  have hf := isScFredholmSectionFunctor_antidiagSection
  intro x₀ hpos
  have h0 := eq_zero_of_zeroMultisection_antidiagSection_pos hpos
  have hx1 : x₀ ∈ (epSEP 1 1).X.PObj.levelSet 1 := by
    have h : (x₀ : Fin 1 → ℝ) ∈ (rnPolyfold 1).levelSet 1 := by
      rw [rnPolyfold_levelSet]; exact mem_univ _
    exact h
  refine ⟨hpos, hx1, ?_⟩
  set x := (epSEP 1 1).X.PObj.levelMk 1 x₀ hx1 with hxdef
  intro L hL
  have hxv : (epSEP 1 1).X.PObj.levelVal 1 x = x₀ := (epSEP 1 1).X.PObj.levelVal_levelMk _ _ _
  let c : StrongBundleChart (epSEP 1 1).X.PObj (epSEP 1 1).P := chart (k := 1) (0 : Fin 1 → ℝ)
  have hc : (epSEP 1 1).B.IsChart c := isChart_chart 0
  have hx : (epSEP 1 1).X.PObj.levelVal 1 x ∈ c.φ.source := mem_univ _
  have hx0 : antidiagSection ((epSEP 1 1).X.PObj.levelVal 1 x) =
      fiberZero (epSEP 1 1).P ((epSEP 1 1).X.PObj.levelVal 1 x) := by
    rw [hxv, h0]
    exact (isZeroAt_graphSection_iff (n := 1) (k := 1) (φ := fun u => -u)
      (x := (0 : Fin 1 → ℝ))).2 neg_zero
  rw [← (mem_support_linearization_zero_iff hf hc hx hx0 L).1 hL]
  refine (surjective_toIntr_subDeriv_iff hf.1.1 (isScPlusSectionOn_fiberZero isOpen_univ) hc
    (subset_univ _) hx hx0).2 ?_
  set z := levelLift c.φ 1 ((epSEP 1 1).X.PObj.levelVal 1 x)
  have hid : ∀ w : Fin 1 → ℝ, scDeriv (E := rnSc 1) (F := rnSc 1) univ (fun u : Fin 1 → ℝ => u) w =
      ContinuousLinearMap.id ℝ _ := fun w => by
    have := scDeriv_univ_const (V := Fin 1 → ℝ) (V' := Fin 1 → ℝ) contDiff_id w
    rw [fderiv_id] at this
    exact this
  have hneg : scDeriv (E := rnSc 1) (F := rnSc 1) univ (fun u : Fin 1 → ℝ => -u) z =
      -ContinuousLinearMap.id ℝ _ := by
    have := scDeriv_univ_const (V := Fin 1 → ℝ) (V' := Fin 1 → ℝ) contDiff_neg_rn z
    rw [this]
    exact ((hasFDerivAt_id (𝕜 := ℝ) (z : Fin 1 → ℝ)).neg).fderiv
  have he : ((fun y => c.principal antidiagSection y -
      c.principal (fiberZero (epSEP 1 1).P) y) ∘ r c.R) = fun u : Fin 1 → ℝ => -u := by
    funext u
    have h2 : c.principal (fiberZero (epSEP 1 1).P) u = 0 :=
      c.snd_fiberZero (x := c.φ.symm u) (mem_univ _)
    change c.principal antidiagSection u - c.principal (fiberZero (epSEP 1 1).P) u = -u
    rw [h2, sub_zero]
    change -(u + 0) = -u
    rw [add_zero]
  intro k _
  refine ⟨-k, ⟨-k, ?_⟩, ?_⟩
  · exact congrArg (fun T : (rnSc 1) 0 →L[ℝ] (rnSc 1) 0 => T (-k)) (hid z)
  · change scDeriv c.U ((fun y => c.principal antidiagSection y -
      c.principal (fiberZero (epSEP 1 1).P) y) ∘ r c.R) z (-k) = k
    rw [he]
    refine (congrArg (fun T : (rnSc 1) 0 →L[ℝ] (rnSc 1) 0 => T (-k)) hneg).trans ?_
    change -(-k) = k
    exact neg_neg k

/-- `(N, U)` controls the compactness of `g(x) = (x, −x)` for some auxiliary norm `N`. -/
theorem exists_controlsCompactness_antidiagSection :
    ∃ (N : (epSEP 1 1).B.One → ℝ) (U : Set (epSEP 1 1).Obj),
      ControlsCompactness (epSEP 1 1) antidiagSection N U := by
  have hpara := (EpGroupoid.admitsBumpFunctionsPointwise_trivial_rn 1).2
  have hS : (epSEP 1 1).E.HasCompactSolutionSetEp antidiagSection := by
    change IsCompact ((epSEP 1 1).X.π '' solutionSet (epSEP 1 1).P antidiagSection)
    rw [solutionSet_antidiagSection]
    exact isCompact_singleton.image (epSEP 1 1).X.continuous_π
  obtain ⟨N, hN⟩ := EpStrongBundle.theorem_12_2_2 (epSEP 1 1).E hpara
  exact ⟨N, exists_controlsCompactness isScFredholmSectionFunctor_antidiagSection hS hN⟩

/-- `(N, U)` controls the compactness of `f(x) = (x, x)` for some auxiliary norm `N`. -/
theorem exists_controlsCompactness_diagSection :
    ∃ (N : (epSEP 1 1).B.One → ℝ) (U : Set (epSEP 1 1).Obj),
      ControlsCompactness (epSEP 1 1) diagSection N U :=
  corollary_15_3_10_1_hypotheses_epSEP.2.2.2.2.2.2.2.2

/-! ### The perturbation `Λ₀` in both models -/

/-- The one sheet `{0}` of `ℝ`. -/
def pointSheet : Unit → Set (Fin 1 → ℝ) := fun _ => {0}

theorem zero_mem_smoothSet_rn : (0 : Fin 1 → ℝ) ∈ (rnPolyfold 1).smoothSet := by
  rw [rnPolyfold_smoothSet]; exact mem_univ _

/-- The orientation `+` of the point `0`. -/
def pointSheetOrientation : ∀ i, (rnPolyfold 1).SubmanifoldOrientation (pointSheet i) 0 :=
  fun _ => pointOrientation zero_mem_smoothSet_rn true

open scoped Classical in
/-- **`Λ₀ ∘ F = 1_{0}`** for a section `F` vanishing exactly at `0`. -/
theorem zeroMultisection_comp_eq {F : (epSEP 1 1).Obj → (epSEP 1 1).W}
    (h1 : ∀ x₀, 0 < zeroMultisection (epSEP 1 1) (F x₀) →
      x₀ = (show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ)))
    (h2 : zeroMultisection (epSEP 1 1) (F (show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ))) = 1) :
    (fun z : Fin 1 → ℝ => ((zeroMultisection (epSEP 1 1) (F z) : ℚ≥0) : ℚ)) =
      fun y : Fin 1 → ℝ => ∑ i with y ∈ pointSheet i, (1 : ℚ) := by
  funext y
  by_cases hy : y = 0
  · subst hy
    simp only [h2]
    simp [pointSheet]
  · have h0 : zeroMultisection (epSEP 1 1) (F y) = 0 :=
      le_antisymm (not_lt.1 fun h => hy (h1 y h)) zero_le
    rw [h0]
    have he : (Finset.univ.filter fun i : Unit => y ∈ pointSheet i) = ∅ :=
      Finset.filter_false_of_mem fun _ _ => hy
    rw [he, Finset.sum_empty]
    rfl

open scoped Classical in
/-- **The regular perturbation `(N, U, Λ₀)` of dimension `0`** of a section `F` with
`Λ₀ ∘ F = 1_{0}`, `(F, Λ₀)` transversal and `(N, U)` controlling compactness, with the
orientation `+` at `0`. -/
def pointPerturbationOfGraph {F : (epSEP 1 1).Obj → (epSEP 1 1).W}
    (hcc : ∃ (N : (epSEP 1 1).B.One → ℝ) (U : Set (epSEP 1 1).Obj),
      ControlsCompactness (epSEP 1 1) F N U)
    (htr : IsTransversal F (zeroMultisection (epSEP 1 1)))
    (hΘ : (fun z : Fin 1 → ℝ => ((zeroMultisection (epSEP 1 1) (F z) : ℚ≥0) : ℚ)) =
      fun y : Fin 1 → ℝ => ∑ i with y ∈ pointSheet i, (1 : ℚ)) :
    PointPerturbation (epSEP 1 1) F where
  N := hcc.choose
  U := hcc.choose_spec.choose
  Λ := zeroMultisection (epSEP 1 1)
  isRegular := ⟨hcc.choose_spec.choose_spec,
    isStructurable_zeroMultisection (hasParacompactOrbitSpace_trivial _),
    by rw [domSupp_zeroMultisection]; exact empty_subset _,
    fun x => by
      rw [pointwiseNorm_zeroMultisection hcc.choose_spec.choose_spec.1.isAuxNorm]
      exact one_pos,
    htr⟩
  T := orientedSumRn pointSheet (fun _ => (1 : ℚ)) pointSheetOrientation
  isBranched := by
    have h := (isPointTame_point_rn 0 pointSheet (fun _ => rfl) pointSheetOrientation).1
    rw [← hΘ] at h; exact h
  isCompact := by
    have h := (isPointTame_point_rn 0 pointSheet (fun _ => rfl) pointSheetOrientation).2.1
    rw [← hΘ] at h; exact h
  isOrientation := by
    have h := (isPointTame_point_rn 0 pointSheet (fun _ => rfl) pointSheetOrientation).2.2.1
    rw [← hΘ] at h; exact h
  loc := by
    have h := (isPointTame_point_rn 0 pointSheet (fun _ => rfl) pointSheetOrientation).2.2.2.2
    rw [← hΘ] at h; exact h

/-- `(N, U, Λ₀)` in the model of `f(x) = (x, x)`. -/
def diagPointPerturbation : PointPerturbation (epSEP 1 1) diagSection :=
  pointPerturbationOfGraph exists_controlsCompactness_diagSection isTransversal_diagSection
    (zeroMultisection_comp_eq (fun _ h => eq_zero_of_zeroMultisection_diagSection_pos h)
      zeroMultisection_diagSection_zero)

/-- `(N, U, Λ₀)` in the model of `g(x) = (x, −x)`. -/
def antidiagPointPerturbation : PointPerturbation (epSEP 1 1) antidiagSection :=
  pointPerturbationOfGraph exists_controlsCompactness_antidiagSection
    isTransversal_antidiagSection
    (zeroMultisection_comp_eq (fun _ h => eq_zero_of_zeroMultisection_antidiagSection_pos h)
      zeroMultisection_antidiagSection_zero)

/-! ### The strong polyfold bundle and the two representatives -/

/-- **The strong polyfold bundle structure `((P : W → X, μ), id, id)`** for
`|P| : |ℝ × ℝ| → |ℝ|` over the trivial ep-groupoid of `ℝ` (Definition 16.3.1). -/
def epStructure : StrongPolyfoldBundleStructure (epSEP 1 1).E.projFunctor.orbitMap where
  A := epSEP 1 1
  isZhou := isZhou_trivial _
  paracompact := hasParacompactOrbitSpace_trivial _
  isLRLocal := EpStrongBundle.isLRLocal_trivial _
  Γ := Homeomorph.refl _
  γ := Homeomorph.refl _
  comm := rfl

/-- The strong polyfold bundle of `epStructure` (Definition 16.3.4). -/
def epPolyfoldBundle : StrongPolyfoldBundle (epSEP 1 1).E.projFunctor.orbitMap :=
  ⟦epStructure⟧

open StrongPolyfoldBundle in
/-- **The representative `(epStructure, graph φ)`** of the section `|x| ↦ |(x, φ(x))|`
(Definition 16.3.18). -/
def graphRep (φ : (Fin 1 → ℝ) → (Fin 1 → ℝ)) (hφ : ContDiff ℝ ∞ φ) :
    SectionRep epPolyfoldBundle where
  S := epStructure
  hS := rfl
  F := graphSection φ
  hF := (graphSection_mem_fredholmSectionFunctors_epBundle hφ).1
  f := Quotient.lift
    (fun x : (epSEP 1 1).Obj => (epSEP 1 1).E.toEpGroupoid.π (graphSection φ x))
    fun x y h => by
      have e : x = y := injective_π_trivial_rn (Quotient.sound h)
      rw [e]
  continuous_f := Continuous.quotient_lift ((epSEP 1 1).E.toEpGroupoid.continuous_π.comp
    (continuous_id.prodMk hφ.continuous)) _
  isSection z := Quotient.inductionOn z fun _ => rfl
  comm _ := rfl

end TrivialBundle

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass SBLocalization TrivialBundle
open StrongBundleEquivalenceExamples EpGroupoid

/-- **`count_eq_of_mk_eq` for two different models** (Theorem 16.6.6 for Fredholm index `0`):
on `ℝ × ℝ → ℝ` (non-zero fibres) the representatives `a` of `f(x) = (x, x)` and `b` of
`g(x) = (x, −x)` differ, the regular perturbations `(N, U, Λ₀)` of dimension `0` in their models
give the same oriented branched suborbifold `((1_{0}, +), (X, id))`, whose support contains `0`;
so the two counts of every `0`-form agree. -/
theorem count_eq_of_mk_eq_two_models :
    ∃ (a b : SectionRep epPolyfoldBundle) (Pa : PointPerturbation a.S.A a.F)
      (Pb : PointPerturbation b.S.A b.F), a ≠ b ∧
      (⟦pointOrientedRep a Pa⟧ : OrientedSuborbifold epPolyfoldBundle.polyfold) =
        ⟦pointOrientedRep b Pb⟧ ∧
      (∀ y : (epSEP 1 1).Obj, Nontrivial ((epSEP 1 1).P ⁻¹' {y})) ∧
      (supp (pointOrientedRep a Pa).A.Θ).Nonempty ∧
      ∀ τ : ScForm epPolyfoldBundle.polyfold 0,
        Pa.count (ScForm.toStructure a.S.toPolyfoldStructure (toPolyfoldStructure_mem a.hS) τ) =
          Pb.count
            (ScForm.toStructure b.S.toPolyfoldStructure (toPolyfoldStructure_mem b.hS) τ) ∧
        Pa.countEff (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou)
            (ScForm.toStructure a.S.toPolyfoldStructure (toPolyfoldStructure_mem a.hS) τ) =
          Pb.countEff (b.S.A.X.proposition_7_4_10_of_isZhou b.S.isZhou)
            (ScForm.toStructure b.S.toPolyfoldStructure (toPolyfoldStructure_mem b.hS) τ) := by
  set a := graphRep id contDiff_id
  set b := graphRep (fun u : Fin 1 → ℝ => -u) contDiff_neg_rn
  have hab : a ≠ b := by
    intro h
    have h1 := congrFun (congrArg SectionRep.f h) ((epSEP 1 1).X.π (fun _ => (1 : ℝ)))
    obtain ⟨q, hq1, hq2⟩ := (GroupoidStr.π_eq_π_iff _).1 h1
    have e := congrArg (fun w : (epSEP 1 1).W => (w : (Fin 1 → ℝ) × (Fin 1 → ℝ)).2 0)
      (hq1.symm.trans hq2)
    norm_num [graphSection] at e
  have hrep : pointOrientedRep a diagPointPerturbation =
      pointOrientedRep b antidiagPointPerturbation := by
    have hΘ := (zeroMultisection_comp_eq (fun _ h => eq_zero_of_zeroMultisection_diagSection_pos h)
      zeroMultisection_diagSection_zero).trans
      (zeroMultisection_comp_eq (fun _ h => eq_zero_of_zeroMultisection_antidiagSection_pos h)
        zeroMultisection_antidiagSection_zero).symm
    unfold pointOrientedRep
    congr 1
    congr 1
  refine ⟨a, b, diagPointPerturbation, antidiagPointPerturbation, hab, congrArg _ hrep,
    corollary_15_3_10_1_hypotheses_epSEP.1, ?_, fun τ =>
      count_eq_of_mk_eq a b _ _ (congrArg _ hrep) τ⟩
  refine ⟨(0 : Fin 1 → ℝ), ?_⟩
  change (0 : ℚ) < ((zeroMultisection (epSEP 1 1)
    (diagSection (show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ))) : ℚ≥0) : ℚ)
  rw [zeroMultisection_diagSection_zero]
  exact one_pos

end StrongPolyfoldBundle

end Polyfold
