import Polyfold.Chapter15.P3W6R6_RelativeFamilies
import Polyfold.Chapter15.P3W5TY_Cutoff

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.9** (Transversal Extension Theorem; 2017: Theorem 15.5), steps (c)–(d),
pp. 698–699: the relative general position theorem (TX's `theorem_15_3_7_relative_statement`)
reduced to the two analytic steps of "arguing as in Theorem 15.3.7", relative to `Λ₀`.

# Relative general position

## The text, paraphrased

Given the structurable extension `Λ₀` of the boundary data with `N(Λ₀) < h`, dom-supp in `U`,
and `(f, Λ₀)` in general position at the points of `supp(Λ₀ ∘ f) ∩ ∂X`, the proof takes
parameter-dependent perturbations `Λ_t` with domain support away from `∂X`, as in Theorem 15.3.7,
and `Λ̃ = Λ_t ⊕ Λ₀` for a small regular `t`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `HasLocalGPFamiliesRel A f Λ₀ N U g`: every `x ∈ supp(Λ₀ ∘ f)` lies in a saturated open `Q`
  carrying a `RelGPFamily` (the relative local constructions).
* `HasParametricGeneralPositionRel A f Λ₀ N U`: for every linear family with
  `N(Λ_t) ≤ |t|₁ (1 − N(Λ₀))`, `dom-supp(Λ_t) ⊆ U` and (15.1) relative to `Λ₀` at every point of
  `supp(Λ₀ ∘ f)`, almost every small `t` has `(f, Λ₀ ⊕ Λ_t)` in general position (the relative
  form of "Achieving global transversality").
* Proved here: the finite cover of the compact `|supp(Λ₀ ∘ f)|` (`exists_relGPFamily_of_compact`),
  the choice of `t`, structurability (Proposition 13.3.12), `Λ̃ = Λ₀` over `∂X`
  (`multisectionAdd_eq_left_of_notMem_domSupp`, the families being taken with domain support in
  `U ∖ ∂X`), the bounds `dom-supp(Λ̃) ⊆ U` and `N(Λ̃) ≤ N(Λ₀) + |t|₁ (h − N(Λ₀)) < h`, and
  transversality:
  * **`theorem_15_3_7_relative_hyp`**: the conclusion of TX's relative statement from the two
    properties;
  * **`theorem_15_3_7_relative_of_hyp`**: `theorem_15_3_7_relative_statement A` from the two
    properties under the statement's hypotheses;
  * **`theorem_15_3_9_of_rel_hyp`**: Theorem 15.3.9 (`theorem_15_3_9_statement`) from TY's tame
    bundle charts `hB`, the extension statement of Theorem 14.1.9, and the two properties.
* `hasLocalGPFamiliesRel_of_boundary`: at the points of `supp(Λ₀ ∘ f) ∩ ∂X` the empty family
  suffices once `(f, Λ₀)` is in general position on a saturated open neighbourhood; so
  `HasLocalGPFamiliesRel` splits into the openness of general position near the boundary part of
  the support and the relative seeds at interior points.
* Satisfiability on `ℝⁿ × ℝ⁰ → ℝⁿ`: `hasLocalGPFamiliesRel_epSEP_zero`,
  `hasParametricGeneralPositionRel_epSEP_zero`,
  `theorem_15_3_7_relative_statement_epSEP_zero_of_hyp`.

## Reading

* "Away from `∂X`": `dom-supp(Λ_t) ⊆ U ∖ ∂X` (`∂X` is closed and saturated). This is what makes
  `Λ̃ = Λ₀` over `∂X`.
* The text's `N(Λ_t)` bound is read as `N(Λ_t) ≤ |t|₁ (h − N(Λ₀))`, so that `N(Λ̃) < h` holds
  pointwise without a uniform margin; the parametric step only needs `≤ |t|₁ (1 − N(Λ₀))`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold

variable {A : SEP.{u}}

/-! ### The two analytic steps, relative to `Λ₀` -/

variable (A) in
/-- **The relative local constructions** (steps (c)–(d) of the proof of Theorem 15.3.9, "argue as
in Theorem 15.3.7", with the local constructions of pp. 694–696): every `x ∈ supp(Λ₀ ∘ f)` lies
in a saturated open `Q` carrying a family with (15.1) relative to `Λ₀` at the points of
`supp(Λ₀ ∘ f) ∩ Q`, the bound `N(Λ_t) ≤ |t|₁ g` and domain support in `U`. -/
def HasLocalGPFamiliesRel (f : A.Obj → A.W) (Λ₀ : A.W → ℚ≥0) (N : A.B.One → ℝ) (U : Set A.Obj)
    (g : A.Obj → ℝ) : Prop :=
  ∀ x, 0 < Λ₀ (f x) → ∃ Q : Set A.Obj, IsOpen Q ∧ A.X.IsSaturated Q ∧ x ∈ Q ∧
    Nonempty (RelGPFamily A f Λ₀ N U g Q)

variable (A) in
/-- **"Achieving global transversality" relative to `Λ₀`** (pp. 696–699): for every linear family
`t ↦ Λ_t` of sc⁺-multisections with `N(Λ_t) ≤ |t|₁ (1 − N(Λ₀))`, `dom-supp(Λ_t) ⊆ U` and (15.1)
relative to `Λ₀` at every point of `supp(Λ₀ ∘ f)`, there is `ε > 0` such that for almost every
`t` with `‖t‖ < ε` the pair `(f, Λ₀ ⊕ Λ_t)` is in general position. -/
def HasParametricGeneralPositionRel (f : A.Obj → A.W) (Λ₀ : A.W → ℚ≥0) (N : A.B.One → ℝ)
    (U : Set A.Obj) : Prop :=
  ∀ (ℓ : ℕ) (Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0), (∀ t, IsScPlusMultisection A (Λ t)) →
    IsLinearFamily Λ →
    (∀ t x, pointwiseNorm N (Λ t) x ≤ (∑ j, |t j|) * (1 - pointwiseNorm N Λ₀ x)) →
    (∀ t, domSupp (Λ t) ⊆ U) →
    (∀ x : A.X.PObj.Level 1, 0 < Λ₀ (f (A.X.PObj.levelVal 1 x)) → IsParamOntoAtRel f Λ₀ Λ x) →
    ∃ ε > 0, ∀ᵐ t ∂(volume : Measure (Fin ℓ → ℝ)), ‖t‖ < ε →
      IsInGeneralPosition A f (multisectionAdd Λ₀ (Λ t))

variable {f : A.Obj → A.W} {Λ₀ : A.W → ℚ≥0} {N : A.B.One → ℝ} {U : Set A.Obj} {g : A.Obj → ℝ}

/-! ### From local to global -/

/-- Finite sums of relative families: families on `Q_i`, `i ∈ s`, give one on `⋃_{i ∈ s} Q_i`. -/
theorem nonempty_relGPFamily_biUnion (h𝒰 : Nonempty A.X.GoodSystem) (hN : A.B.IsAuxNorm N)
    {ι : Type*} (Q : ι → Set A.Obj) (F : ∀ i, Nonempty (RelGPFamily A f Λ₀ N U g (Q i)))
    (s : Finset ι) : Nonempty (RelGPFamily A f Λ₀ N U g (⋃ i ∈ s, Q i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨(RelGPFamily.zero h𝒰 hN).mono (by simp)⟩
  | insert a s _ ih =>
    obtain ⟨G⟩ := ih
    obtain ⟨Fa⟩ := F a
    exact ⟨(Fa.add hN G).mono (Finset.set_biUnion_insert a s Q).le⟩

/-- **"From local to global" relative to `Λ₀`**: if `|supp(Λ₀ ∘ f)|` is compact and every point of
`supp(Λ₀ ∘ f)` lies in a saturated open set carrying a relative family, one family covers all of
`supp(Λ₀ ∘ f)`. -/
theorem exists_relGPFamily_of_compact (h𝒰 : Nonempty A.X.GoodSystem) (hN : A.B.IsAuxNorm N)
    (hK : IsCompact (A.X.π '' {x | 0 < Λ₀ (f x)}))
    (hloc : HasLocalGPFamiliesRel A f Λ₀ N U g) :
    ∃ Q : Set A.Obj, {x | 0 < Λ₀ (f x)} ⊆ Q ∧ Nonempty (RelGPFamily A f Λ₀ N U g Q) := by
  classical
  choose Qx hQo hQs hxQ hF using hloc
  set S := {x | 0 < Λ₀ (f x)}
  have hcov : A.X.π '' S ⊆ ⋃ i : S, A.X.π '' Qx i.1 i.2 := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_iUnion.2 ⟨⟨x, hx⟩, x, hxQ x hx, rfl⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun i : S => A.X.π '' Qx i.1 i.2)
    (fun i => A.X.proposition_7_1_8 _ (hQo i.1 i.2)) hcov
  refine ⟨⋃ i ∈ s, Qx i.1 i.2, fun y hy => ?_,
    nonempty_relGPFamily_biUnion h𝒰 hN (fun i : S => Qx i.1 i.2) (fun i => hF i.1 i.2) s⟩
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (hs ⟨y, hy, rfl⟩)
  have hy' : y ∈ A.X.π ⁻¹' (A.X.π '' Qx i.1 i.2) := hyi
  rw [hQs i.1 i.2] at hy'
  exact mem_iUnion₂.2 ⟨i, hi, hy'⟩

/-- `|supp(Λ ∘ f)|` is compact for an admissible `Λ` (G's `isCompact_orbitSupp_comp`), as a
statement about `π '' {x | Λ(f(x)) > 0}`. -/
theorem isCompact_image_supp_comp (hf : A.E.IsScFredholmSectionFunctor f) (hfc : Continuous f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (hcc : ControlsCompactness A f N U)
    (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (hdom : domSupp Λ ⊆ U) :
    IsCompact (A.X.π '' {x | 0 < Λ (f x)}) := by
  have h := isCompact_orbitSupp_comp hf hfc hΛ hcc hN1 hdom
  have e : {x | 0 < Λ (f x)} = EpGroupoid.supp fun z => (Λ (f z) : ℚ) := by
    ext x
    change _ ↔ (0 : ℚ) < (Λ (f x) : ℚ)
    exact_mod_cast Iff.rfl
  rw [e]
  exact h

/-! ### The relative general position theorem -/

/-- **Steps (c)–(d) of the proof of Theorem 15.3.9 (pp. 698–699), from the two relative analytic
steps**: given the hypotheses on `Λ₀` (structurable, dom-supp in `U`, `N(Λ₀) < h`), the relative
local families with domain support in `U ∖ ∂X` and the relative parametric step, there is a
structurable `Λ̃ = Λ₀ ⊕ Λ_t` agreeing with `Λ₀` over `∂X`, with dom-supp in `U`, `N(Λ̃) < h`,
`(f, Λ̃)` transversal and in general position. -/
theorem theorem_15_3_7_relative_hyp (hf : A.E.IsScFredholmSectionFunctor f) (hfc : Continuous f)
    (hcc : ControlsCompactness A f N U) {h : A.Obj → ℝ} (hh : ∀ x, 0 < h x ∧ h x ≤ 1)
    (hΛ₀ : IsStructurable A Λ₀) (hdom₀ : domSupp Λ₀ ⊆ U)
    (hN₀ : ∀ x, pointwiseNorm N Λ₀ x < h x)
    (hloc : HasLocalGPFamiliesRel A f Λ₀ N (U ∩ A.X.PObj.boundaryᶜ)
      fun x => h x - pointwiseNorm N Λ₀ x)
    (hsard : HasParametricGeneralPositionRel A f Λ₀ N U) :
    ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧ (∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ₀ w) ∧
      domSupp Λ' ⊆ U ∧ (∀ x, pointwiseNorm N Λ' x < h x) ∧ IsTransversal f Λ' ∧
      IsInGeneralPosition A f Λ' := by
  have hN : A.B.IsAuxNorm N := hcc.1.isAuxNorm
  obtain ⟨D, -⟩ := hΛ₀.2
  have h𝒰 : Nonempty A.X.GoodSystem := ⟨D.𝒰⟩
  have hK := isCompact_image_supp_comp hf hfc hΛ₀.1 hcc (fun x => (hN₀ x).le.trans (hh x).2)
    hdom₀
  obtain ⟨Q, hSQ, ⟨F⟩⟩ := exists_relGPFamily_of_compact h𝒰 hN hK hloc
  have hN0 : ∀ x, 0 ≤ pointwiseNorm N Λ₀ x := pointwiseNorm_nonneg hN Λ₀
  have hFU : ∀ t, domSupp (F.Λ t) ⊆ U := fun t => (F.domSupp_subset t).trans inter_subset_left
  obtain ⟨ε, hε, hae⟩ := hsard F.ℓ F.Λ (fun t => (F.isStructurable t).1) F.isLinear
    (fun t x => (F.norm_le t x).trans (mul_le_mul_of_nonneg_left (by linarith [(hh x).2])
      (Finset.sum_nonneg fun j _ => abs_nonneg _)))
    hFU (fun x hx => F.paramOnto x (hSQ hx) hx)
  have hr : (0 : ℝ) < min ε (1 / (F.ℓ + 1)) := lt_min hε (by positivity)
  obtain ⟨t, ht, hgp⟩ := exists_norm_lt_of_ae hr (min_le_left _ _) hae
  have hsum : ∑ j, |t j| < 1 := sum_abs_lt_one (ht.trans_le (min_le_right _ _))
  have hΛt := F.isStructurable t
  have hsc : IsScPlusMultisection A (multisectionAdd Λ₀ (F.Λ t)) :=
    definition_13_2_9 hΛ₀.1 hΛt.1
  refine ⟨multisectionAdd Λ₀ (F.Λ t), proposition_13_3_12 hΛ₀ hΛt, fun w hw => ?_,
    (domSupp_multisectionAdd_subset _ _).trans (union_subset hdom₀ (hFU t)), fun x => ?_,
    isTransversal_of_isInGeneralPosition hf hsc hgp, hgp⟩
  · refine multisectionAdd_eq_left_of_notMem_domSupp hΛ₀.1 hΛt.1 fun hd => ?_
    exact (F.domSupp_subset t hd).2 hw
  · refine (pointwiseNorm_multisectionAdd_le hN hΛ₀.1 hΛt.1 x).trans_lt ?_
    have hm : 0 < h x - pointwiseNorm N Λ₀ x := sub_pos.2 (hN₀ x)
    have h1 : pointwiseNorm N (F.Λ t) x < h x - pointwiseNorm N Λ₀ x :=
      (F.norm_le t x).trans_lt (mul_lt_of_lt_one_left hm hsum)
    linarith

/-- **TX's relative statement (`theorem_15_3_7_relative_statement`, steps (c)–(d) of the proof of
Theorem 15.3.9)** from the two relative analytic steps, assumed under the statement's
hypotheses. -/
theorem theorem_15_3_7_relative_of_hyp
    (H : A.X.IsTame → A.X.HasParacompactOrbitSpace → A.X.PObj.AdmitsScPartitionsOfUnity →
      ∀ f : A.Obj → A.W, A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
        A.E.HasCompactSolutionSetEp f →
      ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
      ∀ h : A.Obj → ℝ, Continuous h → (∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) →
        (∀ x, 0 < h x ∧ h x ≤ 1) →
      ∀ Λ₀ : A.W → ℚ≥0, IsStructurable A Λ₀ → domSupp Λ₀ ⊆ U →
        (∀ x, pointwiseNorm N Λ₀ x < h x) →
        (∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary →
          0 < Λ₀ (f (A.X.PObj.levelVal 1 x)) → IsReducedOntoAtPt f Λ₀ x) →
        HasLocalGPFamiliesRel A f Λ₀ N (U ∩ A.X.PObj.boundaryᶜ)
            (fun x => h x - pointwiseNorm N Λ₀ x) ∧
          HasParametricGeneralPositionRel A f Λ₀ N U) :
    theorem_15_3_7_relative_statement A := by
  intro hX hpara hPU f hf hft hS N U hcc h hc hfun hh Λ₀ hΛ₀ hdom hN hbd
  obtain ⟨hloc, hsard⟩ := H hX hpara hPU f hf hft hS N U hcc h hc hfun hh Λ₀ hΛ₀ hdom hN hbd
  exact theorem_15_3_7_relative_hyp hf (continuousOn_univ.1 hft.isScSmooth.2.continuousOn) hcc hh
    hΛ₀ hdom hN hloc hsard

/-- **Theorem 15.3.9 (Transversal Extension Theorem), p. 694**, from TY's tame bundle charts
`hB`, the extension statement of Theorem 14.1.9 (GL's `theorem_14_1_9_extension_statement`) and
the two relative analytic steps (assumed under the hypotheses of TX's relative statement).  GL's
extension statement does not hold when `∂X ≠ ∅` (A6); the charged form is in
`P3W6R6_ChargedExtension`. -/
theorem theorem_15_3_9_of_rel_hyp
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source)
    (hext : theorem_14_1_9_extension_statement A)
    (H : A.X.IsTame → A.X.HasParacompactOrbitSpace → A.X.PObj.AdmitsScPartitionsOfUnity →
      ∀ f : A.Obj → A.W, A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
        A.E.HasCompactSolutionSetEp f →
      ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
      ∀ h : A.Obj → ℝ, Continuous h → (∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) →
        (∀ x, 0 < h x ∧ h x ≤ 1) →
      ∀ Λ₀ : A.W → ℚ≥0, IsStructurable A Λ₀ → domSupp Λ₀ ⊆ U →
        (∀ x, pointwiseNorm N Λ₀ x < h x) →
        (∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary →
          0 < Λ₀ (f (A.X.PObj.levelVal 1 x)) → IsReducedOntoAtPt f Λ₀ x) →
        HasLocalGPFamiliesRel A f Λ₀ N (U ∩ A.X.PObj.boundaryᶜ)
            (fun x => h x - pointwiseNorm N Λ₀ x) ∧
          HasParametricGeneralPositionRel A f Λ₀ N U) :
    theorem_15_3_9_statement A :=
  theorem_15_3_9_of_extension_ty hB hext (theorem_15_3_7_relative_of_hyp H)

/-! ### The boundary part of the local families -/

/-- **At the boundary part of the support the empty family suffices**: if every point of
`supp(Λ₀ ∘ f) ∩ ∂X` has a saturated open neighbourhood on which `(f, Λ₀)` is in general position
at the points of `supp(Λ₀ ∘ f)` (the openness of general position near the boundary data), and
every point of `supp(Λ₀ ∘ f) ∖ ∂X` has a relative family, then `HasLocalGPFamiliesRel` holds. -/
theorem hasLocalGPFamiliesRel_of_boundary (h𝒰 : Nonempty A.X.GoodSystem) (hN : A.B.IsAuxNorm N)
    (hopen : ∀ x ∈ A.X.PObj.boundary, 0 < Λ₀ (f x) → ∃ Q : Set A.Obj, IsOpen Q ∧
      A.X.IsSaturated Q ∧ x ∈ Q ∧ ∀ y : A.X.PObj.Level 1, A.X.PObj.levelVal 1 y ∈ Q →
        0 < Λ₀ (f (A.X.PObj.levelVal 1 y)) → IsReducedOntoAtPt f Λ₀ y)
    (hint : ∀ x ∉ A.X.PObj.boundary, 0 < Λ₀ (f x) → ∃ Q : Set A.Obj, IsOpen Q ∧
      A.X.IsSaturated Q ∧ x ∈ Q ∧ Nonempty (RelGPFamily A f Λ₀ N U g Q)) :
    HasLocalGPFamiliesRel A f Λ₀ N U g := by
  intro x hx
  by_cases hb : x ∈ A.X.PObj.boundary
  · obtain ⟨Q, hQo, hQs, hxQ, hgp⟩ := hopen x hb hx
    exact ⟨Q, hQo, hQs, hxQ, ⟨RelGPFamily.zeroOn h𝒰 hN hgp⟩⟩
  · exact hint x hb hx

/-! ### Satisfiability on `ℝⁿ × ℝ⁰ → ℝⁿ` -/

/-- **`HasLocalGPFamiliesRel` is satisfiable**: on `ℝⁿ × ℝ⁰ → ℝⁿ` every pair is in general
position, so the empty family on `Q = ℝⁿ` works, for every `f`, `Λ₀`, auxiliary norm `N`, `U`
and `g`. -/
theorem hasLocalGPFamiliesRel_epSEP_zero (n : ℕ)
    (f : (StrongBundleEquivalenceExamples.epSEP n 0).Obj →
      (StrongBundleEquivalenceExamples.epSEP n 0).W)
    (Λ₀ : (StrongBundleEquivalenceExamples.epSEP n 0).W → ℚ≥0)
    {N : (StrongBundleEquivalenceExamples.epSEP n 0).B.One → ℝ}
    (hN : (StrongBundleEquivalenceExamples.epSEP n 0).B.IsAuxNorm N)
    (U : Set (StrongBundleEquivalenceExamples.epSEP n 0).Obj)
    (g : (StrongBundleEquivalenceExamples.epSEP n 0).Obj → ℝ) :
    HasLocalGPFamiliesRel (StrongBundleEquivalenceExamples.epSEP n 0) f Λ₀ N U g := by
  intro x _
  refine ⟨univ, isOpen_univ, (StrongBundleEquivalenceExamples.epSEP n 0).X.isSaturated_univ,
    mem_univ x, ⟨RelGPFamily.zeroOn (nonempty_goodSystem_epSEP_zero n) hN fun y _ hy => ?_⟩⟩
  exact isInGeneralPosition_epSEP_zero n f Λ₀ y hy

/-- **`HasParametricGeneralPositionRel` is satisfiable**: on `ℝⁿ × ℝ⁰ → ℝⁿ` every pair is in
general position. -/
theorem hasParametricGeneralPositionRel_epSEP_zero (n : ℕ)
    (f : (StrongBundleEquivalenceExamples.epSEP n 0).Obj →
      (StrongBundleEquivalenceExamples.epSEP n 0).W)
    (Λ₀ : (StrongBundleEquivalenceExamples.epSEP n 0).W → ℚ≥0)
    (N : (StrongBundleEquivalenceExamples.epSEP n 0).B.One → ℝ)
    (U : Set (StrongBundleEquivalenceExamples.epSEP n 0).Obj) :
    HasParametricGeneralPositionRel (StrongBundleEquivalenceExamples.epSEP n 0) f Λ₀ N U :=
  fun _ _ _ _ _ _ _ => ⟨1, one_pos, ae_of_all _ fun _ _ => isInGeneralPosition_epSEP_zero n f _⟩

/-- **The hypotheses of `theorem_15_3_7_relative_of_hyp` hold together** on `ℝⁿ × ℝ⁰ → ℝⁿ`, which
gives TX's relative statement there through the reduction. -/
theorem theorem_15_3_7_relative_statement_epSEP_zero_of_hyp (n : ℕ) :
    theorem_15_3_7_relative_statement (StrongBundleEquivalenceExamples.epSEP n 0) :=
  theorem_15_3_7_relative_of_hyp fun _ _ _ f _ _ _ N U hcc _ _ _ _ Λ₀ _ _ _ _ =>
    ⟨hasLocalGPFamiliesRel_epSEP_zero n f Λ₀ hcc.1.isAuxNorm _ _,
      hasParametricGeneralPositionRel_epSEP_zero n f Λ₀ N U⟩

end SBLocalization

end Polyfold
