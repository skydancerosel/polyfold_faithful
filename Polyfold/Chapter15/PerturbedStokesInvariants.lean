import Polyfold.Chapter15.RegularPerturbations
import Polyfold.Chapter9.StokesTextHypotheses
import Polyfold.Chapter8.EpFormsFunctor
import Polyfold.Chapter9.StokesDimOne

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, pp. 702–703:
**Theorem 15.4.3** (Stokes for `S(f, Λ)`) and **Corollary 15.4.4** (the invariant
`Φ_{(f,o)}` does not depend on the perturbation) (2017: Theorem 15.7, Corollary 15.2).

# Stokes for perturbed solution sets, and the invariant

## The text, paraphrased

(T15.4.3) Over a tame ep-groupoid, let `(f, o)` be an oriented sc-Fredholm section of index `k`
with compact `|S_f|`, `(N, U)` controlling compactness, `Λ` an sc⁺-multisection with dom-supp in
`U`, (1) `N(Λ) ≤ 1`, (2) `T(f, Λ)` onto on `supp(Λ ∘ f)`, (3) in good position to `∂X` at the
boundary points of the support.  Then `Θ = Λ ∘ f` is a compact tame branched ep⁺-subgroupoid,
oriented by `o` (Theorem 15.4.1), `∂Θ` has the induced orientation (Definition 9.3.10), and
`∫_Θ dω = ∫_{∂Θ} ω` for every sc-form `ω` of degree `k − 1`; with the local unique continuation
property also for the effective integral.

(C15.4.4) For `d_X ≡ 0`, paracompact `|X|`, compact `|S_f|` and an orientation `o`, there is a
well-defined `Φ_{(f,o)} : H*_dR(X) → ℝ` with `Φ_{(f,o)}([ω]) = ∫_{(Λ ∘ f, o)} ω` for a regular
perturbation `(N, U, Λ)` (with the canonical orientation).  The proof is "left to the reader": by
Corollary 15.3.10 (3), two regular perturbations are joined by a compact cobordism `Θ̃` over
`[0, 1] × X`, and Stokes (Theorem 15.4.3) on `Θ̃` applied to the pull-back of a closed `ω` gives
the equality.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `localBranching_of_isGoodPositionAt`, **`theorem_15_4_3_isBranched_hyp`**: under (1)–(3)
  `Θ = Λ ∘ f` is a compact branched ep⁺-subgroupoid (Definitions 9.1.2, 9.1.6 (2)): local branching
  from L's Theorem 15.2.2 (interior points) and Theorem 15.2.5 (boundary points), compactness from
  G's `isCompact_orbitSupp_comp`.
* **`theorem_15_4_3_hyp`**, `theorem_15_4_3_eff_hyp`, `theorem_15_4_3_dim1_hyp`: Stokes for `Θ`,
  from K's Theorems 9.5.17, 9.5.18 (and the dimension-1 form), for an orientation `T̂` of `Θ`
  with oriented tame structures of dimension `m + 1` (`hloc`) given as data.  Theorem 15.4.1
  (the canonical orientation from `o`) is not formalized (F's gap), so the orientation is a
  hypothesis.
* `OrientedRegularPerturbation A f m`: a regular perturbation (Corollary 15.3.10 (1)) with an
  orientation of `Θ` described in dimension `m + 1`; `.integral`.
* **`corollary_15_4_4_statement A f m Can`**: Corollary 15.4.4 for a predicate `Can` that singles
  out the oriented regular perturbations with the canonical orientation from `(f, o)`: exact forms
  integrate to `0` (so `Φ` is defined on `H^{m+1}_dR`), and closed forms have the same integral
  over any two of them.
* **`integral_d_eq_zero_of_degIndex_eq_zero`**: for `d_X ≡ 0`, `∫_Θ dη = 0` (Stokes, `∂Θ = ∅`).
* **`integral_eq_of_cobordism`**: the cobordism argument of the proof, for an arbitrary
  sc-smooth functor `F : Y → X` (the projection `[0, 1] × X → X` in the text): if a compact
  oriented branched `Θ̃` on `Y` has `∫_{∂Θ̃} F^*ω = ∫_{Θ₁} ω − ∫_{Θ₀} ω`, then closed forms have
  equal integrals over `Θ₀` and `Θ₁` (Stokes on `Y` and `d F^* = F^* d`, Theorem 11.2.1 (2)).
* **`corollary_15_4_4_hyp`**: the statement holds when any two `Can`-perturbations are joined by
  such a cobordism (`HasOrientedCobordism`).  Nonvacuity: `hasOrientedCobordism_refl` (every
  oriented regular perturbation is cobordant to itself, by `Θ̃ = 0`).

## Reading

* `hPU` (sc-smooth partitions of unity on `X`) is the hypothesis of K's Theorem 9.5.17, inherited;
  the text's Theorem 15.4.3 does not state it.
* "Tame" and the dimension of `Θ` are carried by `hloc` (as in K's Theorem 9.5.17).
* `Φ_{(f,o)}` on `H*_dR(X)` is read degree-wise on `Ω^{m+1}_{ep,∞}`: vanishing on exact forms and
  equality on closed forms are what "well defined" means for `[ω] ↦ ∫ ω`.  The exact-form part
  uses Theorem 9.5.17 (`dim Θ ≥ 2`) and its dimension-1 form `theorem_9_5_17_dim1`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

/-! ### Theorem 15.4.3: `Θ = Λ ∘ f` is a compact branched ep⁺-subgroupoid -/

/-- At a point of good position (Definition 15.2.4), `z ↦ Λ(f(z))` has a local branching
structure (Definition 9.1.2 (2)–(4)), from L's Theorem 15.2.5 (as in G's
`remark_15_3_6_localBranching_hyp`). -/
theorem localBranching_of_isGoodPositionAt {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) {y : A.Obj} (hgp : IsGoodPositionAt f Λ y) :
    Nonempty (A.X.LocalBranchingStructure (fun z => (Λ (f z) : ℚ)) y) := by
  classical
  obtain ⟨R, O, k, s, σ, c, -, hrep, -, -, -, hS, hP, -, -, hcount, -, hI⟩ :=
    theorem_15_2_5_hyp hf hft hΛ hgp
  refine ⟨EpGroupoid.LocalBranchingStructure.mk R.U R.isOpen_U R.mem_U
    (ULift.{u} {i : Fin k // s i y = f y}) (fun j => {z ∈ R.U | f z = s j.down.1 z})
    (fun j => sep_subset _ _) (fun j => hS j.down.1) (fun j => ⟨R.mem_U, j.down.2.symm⟩)
    (fun j => hP j.down.1) (fun j => (σ j.down.1 : ℚ))
    (fun j => by exact_mod_cast hrep.1 j.down.1) ?_⟩
  intro z hz
  have e0 : ((Λ (f z) : ℚ≥0) : ℚ) = ∑ i, if f z = s i z then (σ i : ℚ) else 0 := by
    rw [hcount z hz, Finset.sum_filter]
    refine (map_sum NNRat.coeHom _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    split_ifs <;> rfl
  have e1 : (∑ i, if f z = s i z then (σ i : ℚ) else 0) =
      ∑ i with s i y = f y, (if f z = s i z then (σ i : ℚ) else 0) :=
    (Finset.sum_filter_of_ne fun i _ hne => hI i z hz (by
      by_contra h
      exact hne (if_neg h))).symm
  have e2 : (∑ i with s i y = f y, (if f z = s i z then (σ i : ℚ) else 0)) =
      ∑ a : {i // s i y = f y}, (if f z = s a.1 z then (σ a.1 : ℚ) else 0) :=
    Finset.sum_subtype _ (fun i => by simp) _
  have e3 : (∑ a : {i // s i y = f y}, (if f z = s a.1 z then (σ a.1 : ℚ) else 0)) =
      ∑ j : ULift.{u} {i // s i y = f y},
        (if f z = s j.down.1 z then (σ j.down.1 : ℚ) else 0) :=
    (Fintype.sum_equiv Equiv.ulift _ _ fun _ => rfl).symm
  refine e0.trans (e1.trans (e2.trans (e3.trans ?_)))
  simp only [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd ⟨hz, h1⟩ h2 | exact absurd h2.2 h1

/-- **Theorem 15.4.3, first conclusion (p. 702)**, with the inherited tame germ data: under
(1) `N(Λ) ≤ 1`, dom-supp in `U`, `(N, U)` controlling compactness, (2) `T(f, Λ)` onto on
`supp(Λ ∘ f)` and (3) good position (Definition 15.2.4) at the points of `∂X ∩ supp(Λ ∘ f)`,
`Θ = Λ ∘ f` is a compact branched ep⁺-subgroupoid. -/
theorem theorem_15_4_3_isBranched_hyp {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (hdom : domSupp Λ ⊆ U) (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x) :
    A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) := by
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  have hK := isCompact_orbitSupp_comp hf hfc hΛ hcc hN1 hdom
  have : CompactSpace (A.X.orbitSupp fun z => (Λ (f z) : ℚ)) := isCompact_iff_compactSpace.1 hK
  refine ⟨{ nonneg := fun z => NNRat.coe_nonneg _
            isFunctorial := isFunctorial_comp hf hΛ
            support_subset := fun z hz => mem_smoothSet_of_pos hft hΛ (by exact_mod_cast hz)
            paracompactSpace_orbitSupp := inferInstance
            localBranching := fun z hz => ?_ }, hK⟩
  have hpos : 0 < Λ (f z) := by exact_mod_cast hz
  by_cases hb : z ∈ A.X.PObj.boundary
  · exact localBranching_of_isGoodPositionAt hf hft hΛ (hgood z hb hpos)
  · have hd : A.X.PObj.degIndex z = 0 := Nat.lt_one_iff.1 (not_le.1 hb)
    exact remark_15_2_3_hyp hf hft hΛ hd (htr z hpos)

/-- **Theorem 15.4.3 (2017: Theorem 15.7), p. 702**, with the inherited hypotheses: tame germ
data of `f`, sc-smooth partitions of unity on `X` (Theorem 9.5.17's hypothesis), and the
orientation `T̂` of `Θ = Λ ∘ f` with oriented tame structures of dimension `m + 1` given as data
(the text: the canonical orientation of Theorem 15.4.1, not formalized).  Under (1)–(3), `Θ` is a
compact branched ep⁺-subgroupoid, and `∫_Θ̂ dω = μ^{∂Θ̂}_ω(∂S) = ∫_{∂Θ̂} ω` for every
`ω ∈ Ωᵐ_{ep,∞}(X)` (`m ≥ 1`; K's `theorem_9_5_17`). -/
theorem theorem_15_4_3_hyp {m : ℕ} (hm : 0 < m) (hPU : A.X.HasScPartitionsOfUnity)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (hdom : domSupp Λ ⊆ U) (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} (hT : A.X.IsOrientation (fun z => (Λ (f z) : ℚ)) T)
    (hloc : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
      ∃ C : A.X.OrientedTameStructure (m + 1) (fun z => (Λ (f z) : ℚ)) x, C.Represents T) :
    A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) ∧
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt hT hloc
            (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasure hm hΘ hcpt hT hloc ω univ := by
  obtain ⟨hΘ, hcpt⟩ := theorem_15_4_3_isBranched_hyp hf hft hcc hΛ hdom hN1 htr hgood
  exact ⟨hΘ, hcpt, fun hΘ hcpt ω => A.baseEP.theorem_9_5_17 hm hPU hΘ hcpt hT hloc ω⟩

/-- **Theorem 15.4.3, effective version, p. 703**: with the local unique continuation property
(Definition 7.2.18), `∮_Θ̂ dω = ∮_{∂Θ̂} ω` (K's `theorem_9_5_18`); hypotheses as in
`theorem_15_4_3_hyp`. -/
theorem theorem_15_4_3_eff_hyp {m : ℕ} (hm : 0 < m) (hPU : A.X.HasScPartitionsOfUnity)
    (hLUC : A.X.IsLUC) {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (hdom : domSupp Λ ⊆ U) (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} (hT : A.X.IsOrientation (fun z => (Λ (f z) : ℚ)) T)
    (hloc : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
      ∃ C : A.X.OrientedTameStructure (m + 1) (fun z => (Λ (f z) : ℚ)) x, C.Represents T) :
    A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) ∧
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) hΘ hcpt hT
            (A.baseEP.hloc_hasLUC hLUC hloc) (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasureEff hm hLUC hΘ hcpt hT hloc ω univ := by
  obtain ⟨hΘ, hcpt⟩ := theorem_15_4_3_isBranched_hyp hf hft hcc hΛ hdom hN1 htr hgood
  exact ⟨hΘ, hcpt, fun hΘ hcpt ω => A.baseEP.theorem_9_5_18 hm hPU hLUC hΘ hcpt hT hloc ω⟩

/-- **Theorem 15.4.3 for index `1`** (`Θ` of dimension `1`, `ω` a function): Stokes from K's
`theorem_9_5_17_dim1`, `∫_Θ̂ dω = μ^{∂Θ̂}_ω(∂S)` (a signed count over the finitely many oriented
boundary points); hypotheses as in `theorem_15_4_3_hyp`. -/
theorem theorem_15_4_3_dim1_hyp (hPU : A.X.HasScPartitionsOfUnity)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (hdom : domSupp Λ ⊆ U) (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} (hT : A.X.IsOrientation (fun z => (Λ (f z) : ℚ)) T)
    (hloc : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
      ∃ C : A.X.OrientedTameStructure (0 + 1) (fun z => (Λ (f z) : ℚ)) x, C.Represents T) :
    A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) ∧
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty 0),
        (A.baseEP.epFormsInftyEval (0 + 1)).tameBranchedIntegral (Nat.succ_pos 0) hΘ hcpt hT hloc
            (A.baseEP.epFormsInftyD 0 ω) =
          A.baseEP.boundaryBranchedMeasureDim1 hΘ hcpt hT hloc ω univ := by
  obtain ⟨hΘ, hcpt⟩ := theorem_15_4_3_isBranched_hyp hf hft hcc hΛ hdom hN1 htr hgood
  exact ⟨hΘ, hcpt, fun hΘ hcpt ω => A.baseEP.theorem_9_5_17_dim1 hPU hΘ hcpt hT hloc ω⟩

/-! ### Corollary 15.4.4 -/

/-- The branched integral of the zero form is `0`. -/
theorem tameBranchedIntegral_zero {B : EP.{u}} {n : ℕ} (hn : 0 < n) {Θ : B.Obj → ℚ}
    {T : B.Obj → B.X.PObj.OrTangent →₀ ℚ} (hΘ : B.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : B.X.IsCompactBranched Θ) (hT : B.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ EpGroupoid.supp Θ, ∃ C : B.X.OrientedTameStructure n Θ x, C.Represents T) :
    (B.epFormsInftyEval n).tameBranchedIntegral hn hΘ hcpt hT hloc 0 = 0 := by
  simp only [FormEval.tameBranchedIntegral, FormEval.concreteBranchedIntegral, branchedIntegral,
    map_zero]
  rfl

/-- If the orbit space of `supp(∂Θ)` is empty, every boundary measure gives `0` on it. -/
theorem signedMeasure_univ_eq_zero_of_boundary {B : EP.{u}} {Θ : B.Obj → ℚ}
    (hemp : ∀ x, x ∉ B.X.PObj.boundary ∩ EpGroupoid.supp Θ)
    {mσ : MeasurableSpace (B.X.orbitSupp (B.X.boundaryTheta Θ))}
    (μ : @SignedMeasure (B.X.orbitSupp (B.X.boundaryTheta Θ)) mσ) : μ univ = 0 := by
  have : IsEmpty (B.X.orbitSupp (B.X.boundaryTheta Θ)) := by
    refine ⟨fun ⟨_, x, hx, _⟩ => hemp x (B.X.supp_boundaryTheta_subset Θ hx)⟩
  rw [univ_eq_empty_iff.2 this]
  exact VectorMeasure.empty _

/-- The boundary measure of `Θ` vanishes when `∂X ∩ supp Θ = ∅`. -/
theorem boundaryMeasure_univ_eq_zero {B : EP.{u}} {m : ℕ} (hm : 0 < m) {Θ : B.Obj → ℚ}
    {T : B.Obj → B.X.PObj.OrTangent →₀ ℚ} (hΘ : B.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : B.X.IsCompactBranched Θ) (hT : B.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ EpGroupoid.supp Θ, ∃ C : B.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (hemp : ∀ x, x ∉ B.X.PObj.boundary ∩ EpGroupoid.supp Θ) (ω : B.epFormsInfty m) :
    B.boundaryMeasure hm hΘ hcpt hT hloc ω univ = 0 :=
  signedMeasure_univ_eq_zero_of_boundary hemp (B.boundaryMeasure hm hΘ hcpt hT hloc ω)

/-- **The integral of an exact form vanishes when `d_X ≡ 0`** (Corollary 15.4.4, `Φ` is defined on
cohomology): for `Θ` compact, branched, oriented and tame of dimension `m + 1` (`m ≥ 1`) and
`X` with partitions of unity, `∫_Θ̂ dη = μ^{∂Θ̂}_η(∂S) = 0`, since `∂Θ = 0` (`∂X = ∅`). -/
theorem integral_d_eq_zero_of_degIndex_eq_zero {B : EP.{u}} {m : ℕ} (hm : 0 < m)
    (hPU : B.X.HasScPartitionsOfUnity) (hd : ∀ x, B.X.PObj.degIndex x = 0) {Θ : B.Obj → ℚ}
    {T : B.Obj → B.X.PObj.OrTangent →₀ ℚ} (hΘ : B.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : B.X.IsCompactBranched Θ) (hT : B.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ EpGroupoid.supp Θ, ∃ C : B.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (η : B.epFormsInfty m) :
    (B.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt hT hloc
      (B.epFormsInftyD m η) = 0 := by
  rw [B.theorem_9_5_17 hm hPU hΘ hcpt hT hloc η]
  refine boundaryMeasure_univ_eq_zero hm hΘ hcpt hT hloc (fun x hx => ?_) η
  have h1 : 1 ≤ B.X.PObj.degIndex x := hx.1
  rw [hd x] at h1
  exact absurd h1 (by norm_num)

/-- **The integral of an exact form vanishes when `d_X ≡ 0`, dimension `1`** (K's
`theorem_9_5_17_dim1`). -/
theorem integral_d_eq_zero_of_degIndex_eq_zero_dim1 {B : EP.{u}}
    (hPU : B.X.HasScPartitionsOfUnity) (hd : ∀ x, B.X.PObj.degIndex x = 0) {Θ : B.Obj → ℚ}
    {T : B.Obj → B.X.PObj.OrTangent →₀ ℚ} (hΘ : B.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : B.X.IsCompactBranched Θ) (hT : B.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ EpGroupoid.supp Θ, ∃ C : B.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    (η : B.epFormsInfty 0) :
    (B.epFormsInftyEval (0 + 1)).tameBranchedIntegral (Nat.succ_pos 0) hΘ hcpt hT hloc
      (B.epFormsInftyD 0 η) = 0 := by
  rw [B.theorem_9_5_17_dim1 hPU hΘ hcpt hT hloc η]
  refine signedMeasure_univ_eq_zero_of_boundary (fun x hx => ?_)
    (B.boundaryBranchedMeasureDim1 hΘ hcpt hT hloc η)
  have h1 : 1 ≤ B.X.PObj.degIndex x := hx.1
  rw [hd x] at h1
  exact absurd h1 (by norm_num)

/-- **The cobordism argument of Corollary 15.4.4** (p. 703, "left to the reader"; the proof of
Corollary 15.3.10 builds `Θ̃` over `[0, 1] × X`).  Let `F : Y → X` be an sc-smooth functor (the
projection `[0, 1] × X → X`), `Y` with sc-smooth partitions of unity, `Θ̃` compact, branched,
oriented and tame of dimension `m + 2` on `Y`, and `Θ₀`, `Θ₁` compact, branched, oriented and
tame of dimension `m + 1` on `X`, with the boundary identity
`∫_{∂Θ̃} F^*ω = ∫_{Θ₁} ω − ∫_{Θ₀} ω` for all `ω`.  Then `∫_{Θ₀} ω = ∫_{Θ₁} ω` for every closed
`ω ∈ Ω^{m+1}_{ep,∞}(X)`: by Stokes (Theorem 9.5.17) on `Y`,
`∫_{∂Θ̃} F^*ω = ∫_{Θ̃} d F^*ω = ∫_{Θ̃} F^* dω = 0`. -/
theorem integral_eq_of_cobordism {X Y : EP.{u}} (F : EpFunctor Y.X X.X) {m : ℕ}
    (hPU : Y.X.HasScPartitionsOfUnity) {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    (I₀ I₁ : X.epFormsInfty (m + 1) → ℝ)
    (hbd : ∀ ω, Y.boundaryMeasure (Nat.succ_pos m) hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F (m + 1) ω) univ = I₁ ω - I₀ ω)
    (ω : X.epFormsInfty (m + 1)) (hω : X.epFormsInftyD (m + 1) ω = 0) : I₀ ω = I₁ ω := by
  have hS := Y.theorem_9_5_17 (Nat.succ_pos m) hPU hΘ' hcpt' hT' hloc'
    (EP.epFormsInftyPullback F (m + 1) ω)
  have hd : Y.epFormsInftyD (m + 1) (EP.epFormsInftyPullback F (m + 1) ω) = 0 := by
    have := LinearMap.congr_fun (EP.epFormsInftyD_comp_epFormsInftyPullback F (m + 1)) ω
    simp only [LinearMap.comp_apply] at this
    rw [this, hω, map_zero]
  rw [hd, tameBranchedIntegral_zero, hbd] at hS
  linarith

variable (A) in
/-- An **oriented regular perturbation of dimension `m + 1`**: a structurable regular
perturbation `(N, U, Λ)` of `f` (Corollary 15.3.10 (1)), with `Θ = Λ ∘ f` compact and branched,
and an orientation `T̂` of `Θ` described by oriented tame structures of dimension `m + 1` (the
data Theorem 15.4.1 provides for the canonical orientation from `(f, o)`). -/
structure OrientedRegularPerturbation (f : A.Obj → A.W) (m : ℕ) where
  /-- The auxiliary norm. -/
  N : A.B.One → ℝ
  /-- The controlling neighbourhood. -/
  U : Set A.Obj
  /-- The perturbation. -/
  Λ : A.W → ℚ≥0
  isRegular : IsRegularPerturbation A f N U Λ
  /-- The orientation `T̂` of `Θ = Λ ∘ f`. -/
  T : A.Obj → A.X.PObj.OrTangent →₀ ℚ
  isBranched : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ))
  isCompact : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))
  isOrientation : A.X.IsOrientation (fun z => (Λ (f z) : ℚ)) T
  loc : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
    ∃ C : A.X.OrientedTameStructure (m + 1) (fun z => (Λ (f z) : ℚ)) x, C.Represents T

namespace OrientedRegularPerturbation

variable {f : A.Obj → A.W} {m : ℕ}

/-- `∫_{(Λ ∘ f, o)} ω` for `ω ∈ Ω^{m+1}_{ep,∞}(X)` (Definition 9.5.6 (1)). -/
def integral (P : OrientedRegularPerturbation A f m) (ω : A.baseEP.epFormsInfty (m + 1)) : ℝ :=
  (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) P.isBranched
    P.isCompact P.isOrientation P.loc ω

/-- `P₀` and `P₁` are joined by an **oriented compact cobordism** in the sense of the proof of
Corollary 15.4.4: an ep-groupoid `Y` with partitions of unity, an sc-smooth functor `F : Y → X`,
and a compact branched `Θ̃` on `Y`, oriented and tame of dimension `m + 2`, with
`∫_{∂Θ̃} F^*ω = ∫_{P₁} ω − ∫_{P₀} ω` (in the text: `Y = [0, 1] × X`, `Θ̃ = Λ̃ ∘ f̃` from
Corollary 15.3.10 (3), and the boundary identity from `∂Θ̃ = Θ₁ ⊔ −Θ₀`). -/
def HasOrientedCobordism (P₀ P₁ : OrientedRegularPerturbation A f m) : Prop :=
  ∃ (Y : EP.{u}) (F : EpFunctor Y.X A.baseEP.X) (_ : Y.X.HasScPartitionsOfUnity)
    (Θ' : Y.Obj → ℚ) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ)
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T'),
    ∀ ω, Y.boundaryMeasure (Nat.succ_pos m) hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F (m + 1) ω) univ = P₁.integral ω - P₀.integral ω

/-- **The cobordism hypothesis is satisfiable**: every oriented regular perturbation is cobordant
to itself (`Y = X`, `F = id`, `Θ̃ = 0`, whose boundary measure vanishes), when `X` has
partitions of unity. -/
theorem hasOrientedCobordism_refl (hPU : A.X.HasScPartitionsOfUnity)
    (P : OrientedRegularPerturbation A f m) : HasOrientedCobordism P P := by
  have hemp : ∀ x, x ∉ A.X.PObj.boundary ∩ EpGroupoid.supp (0 : A.Obj → ℚ) := fun x hx =>
    lt_irrefl (0 : ℚ) hx.2
  have hcpt0 : A.X.IsCompactBranched (0 : A.Obj → ℚ) := by
    have : A.X.orbitSupp (0 : A.Obj → ℚ) = ∅ := by
      rw [orbitSupp, image_eq_empty, eq_empty_iff_forall_notMem]
      exact fun x hx => lt_irrefl (0 : ℚ) hx
    rw [IsCompactBranched, this]; exact isCompact_empty
  have hloc0 : ∀ x ∈ EpGroupoid.supp (0 : A.Obj → ℚ),
      ∃ C : A.X.OrientedTameStructure (m + 1 + 1) 0 x, C.Represents fun _ => 0 :=
    fun x hx => absurd hx (lt_irrefl (0 : ℚ))
  refine ⟨A.baseEP, EpFunctor.id _, hPU, 0, fun _ => 0, A.X.isBranchedEpSubgroupoid_zero,
    hcpt0, A.X.isOrientation_zero, hloc0, fun ω => ?_⟩
  rw [sub_self]
  exact boundaryMeasure_univ_eq_zero (B := A.baseEP) (Nat.succ_pos m)
    A.X.isBranchedEpSubgroupoid_zero hcpt0 A.X.isOrientation_zero hloc0 hemp _

end OrientedRegularPerturbation

variable (A) in
/-- **Corollary 15.4.4 (2017: Corollary 15.2), p. 703**, as a proposition, degree-wise in
degree `m + 1` (the dimension of `Θ`).  `Can P` is the condition that the orientation of `P` is
the canonical one from `(f, o)` (Theorem 15.4.1, not formalized, so `Can` is a parameter).
`Φ_{(f,o)}([ω]) = ∫_{(Λ ∘ f, o)} ω` is well defined: (i) exact forms integrate to `0` over every
`Can`-perturbation, (ii) a closed form has the same integral over any two `Can`-perturbations. -/
def corollary_15_4_4_statement (f : A.Obj → A.W) (m : ℕ)
    (Can : OrientedRegularPerturbation A f m → Prop) : Prop :=
  (∀ P, Can P → ∀ η : A.baseEP.epFormsInfty m, P.integral (A.baseEP.epFormsInftyD m η) = 0) ∧
  ∀ P₀ P₁, Can P₀ → Can P₁ → ∀ ω : A.baseEP.epFormsInfty (m + 1),
    A.baseEP.epFormsInftyD (m + 1) ω = 0 → P₀.integral ω = P₁.integral ω

/-- **Corollary 15.4.4 from the cobordism**: for `d_X ≡ 0` and `X` with sc-smooth partitions of
unity (Theorem 9.5.17's hypothesis), in every dimension `m + 1 ≥ 1`, the statement holds for every
predicate `Can` whose perturbations are pairwise joined by oriented compact cobordisms
(`HasOrientedCobordism`; in the text from Corollary 15.3.10 (3) with the canonical orientation of
`Θ̃` and `∂Θ̃ = Θ₁ ⊔ −Θ₀`). -/
theorem corollary_15_4_4_hyp {f : A.Obj → A.W} {m : ℕ}
    (hPU : A.X.HasScPartitionsOfUnity) (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (Can : OrientedRegularPerturbation A f m → Prop)
    (hcob : ∀ P₀ P₁, Can P₀ → Can P₁ → P₀.HasOrientedCobordism P₁) :
    corollary_15_4_4_statement A f m Can := by
  refine ⟨fun P _ η => ?_, fun P₀ P₁ h₀ h₁ ω hω => ?_⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact integral_d_eq_zero_of_degIndex_eq_zero_dim1 (B := A.baseEP) hPU hd
        P.isBranched P.isCompact P.isOrientation P.loc η
    · exact integral_d_eq_zero_of_degIndex_eq_zero (B := A.baseEP) hm hPU hd
        P.isBranched P.isCompact P.isOrientation P.loc η
  obtain ⟨Y, F, hPUY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := hcob P₀ P₁ h₀ h₁
  exact integral_eq_of_cobordism F hPUY hΘ' hcpt' hT' hloc' P₀.integral P₁.integral hbd ω hω

end SBLocalization

end Polyfold
