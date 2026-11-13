import Polyfold.Chapter15.P3W4GP_ParamFamily

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, **Theorem 15.3.7**
(General Position; 2017: Theorem 15.4), pp. 693–698: the existence of the perturbation, reduced
to the two analytic steps of the proof.

# Theorem 15.3.7 from the local families and the parametric transversality step

## The proof, paraphrased (pp. 694–698)

(Local constructions) At every `x ∈ S_f` a parameter family `t ↦ Λ^x_t`, `t ∈ ℝ^ℓ`, of atomic
(hence structurable) sc⁺-multisections with branches `Σ_j t_j s^g_j`, `N(s¹_j) ≤ min{1, h}`,
supported near the orbit of `x`, such that `T^R_{(f̃,Λ̃)}(0, y)` is onto for `y ∈ S_f` in a
saturated open `Q(x) ∋ x` (the "Interior" and "Boundary" assertions).  (From local to global)
Finitely many `|Q(x_i)|` cover `|S_f|`; `Λ_t = ⊕_i Λ^{x_i}_{t_i}`; (15.1) holds on `S_f`;
`N(Λ_t) < 1` for small `|t|`.  (Achieving global transversality) The compactness (15.2), the
implicit function theorem and Sard's theorem for the projections `F ∩ M_i → ℝ^ℓ` give a null set
off which every small `t` has `(f, Λ_t)` in general position.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`HasLocalGPFamilies A f N U h`**: the output of the local constructions (steps (a), (f) of
  G's gap G-1): every `x ∈ S_f` lies in a saturated open `Q` carrying a `GPFamily` on `Q`.
* **`HasParametricGeneralPosition A f N U`**: the output of "Achieving global transversality"
  (steps (e), (g), (h)): for every linear family of sc⁺-multisections with `N(Λ_t) ≤ |t|₁`,
  `dom-supp(Λ_t) ⊆ U` and (15.1) at every `x ∈ S_f`, there is `ε > 0` such that for almost every
  `t` with `‖t‖ < ε` the pair `(f, Λ_t)` is in general position (Definition 15.3.5).
* Proved here (steps (b), (c), (d) and the choice of `t` in (h)):
  * `nonempty_gpFamily_biUnion`: finite sums of families (`GPFamily.add`, Proposition 13.3.12);
  * `exists_gpFamily_of_compact`: the finite cover of the compact `|S_f|` ("From local to global");
  * `exists_norm_lt_of_ae`: a point of a positive-measure ball off a null set;
  * `sum_abs_lt_one`: `|t|₁ < 1` for `‖t‖ < 1/(ℓ+1)`;
  * **`theorem_15_3_7_hyp`**: the conclusions (1)–(4) and "structurable" of Theorem 15.3.7, from
    a good system and the two properties above;
  * **`theorem_15_3_7_of_hyp`**: `theorem_15_3_7_statement A` (G's Lean statement) from a good
    system and the two properties under the hypotheses of the theorem.
* Satisfiability: `hasLocalGPFamilies_epSEP_zero`, `hasParametricGeneralPosition_epSEP_zero`,
  `nonempty_goodSystem_epSEP_zero`, and `theorem_15_3_7_statement_epSEP_zero_of_hyp` (the
  statement on `ℝⁿ × ℝ⁰ → ℝⁿ` through `theorem_15_3_7_of_hyp`).

## Reading

* "Structurable" (Definition 13.3.6, D's `IsStructurable`) includes a good system; so the
  conclusion of Theorem 15.3.7 implies that a good system exists, and `Nonempty A.X.GoodSystem` is
  a hypothesis here (it holds for paracompact `|X|`, Theorem 13.1.8; Remark 15.3.8 drops
  paracompactness).
* (15.1) is read with the reduced tangent space `T^R_xX` and the operator `f'(x)` of
  `T(f, Λ₀)(x)`; the `t`-derivative of the branch `f − Σ_j t_j s_{ij}` at `t = 0` is
  `τ ↦ −Σ_j τ_j s_{ij}(x)` (the sign is immaterial for surjectivity).
* `N(Λ_t) ≤ |t|₁ · h` is the bound the proof's choice `N(s¹_j) ≤ min{1, h}` gives on the branches
  `Σ_j t_j s^g_j` (with Definition 8.3.5 (3), `normW_μ`); the proof's `ε₀` is `1/(ℓ+1)` in the
  sup norm of `ℝ^ℓ`.
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

/-! ### The two analytic steps, as properties -/

variable (A) in
/-- **The local constructions of the proof of Theorem 15.3.7** (pp. 694–696, "Local constructions
at `x ∈ S_f`", interior and boundary; steps (a) and (f) of gap G-1): every `x ∈ S_f` lies in a
saturated open `Q` (the saturation of `Q(x)`) on which there is a parameter family with the
properties of `GPFamily` (structurable, linear in `t`, `N(Λ_t) ≤ |t|₁ h`, domain support in `U`,
(15.1) at the points of `S_f ∩ Q`). -/
def HasLocalGPFamilies (f : A.Obj → A.W) (N : A.B.One → ℝ) (U : Set A.Obj) (h : A.Obj → ℝ) :
    Prop :=
  ∀ x ∈ solutionSet A.P f, ∃ Q : Set A.Obj, IsOpen Q ∧ A.X.IsSaturated Q ∧ x ∈ Q ∧
    Nonempty (GPFamily A f N U h Q)

variable (A) in
/-- **"Achieving global transversality" in the proof of Theorem 15.3.7** (pp. 696–698; steps
(e), (g), (h) of gap G-1: the compactness (15.2), the implicit function theorem near the
parametrized solution set, Sard's theorem for the projections to `ℝ^ℓ` on the intersections of
faces): for every linear family `t ↦ Λ_t` of sc⁺-multisections with `N(Λ_t) ≤ |t|₁`,
`dom-supp(Λ_t) ⊆ U` and (15.1) at every point of `S_f`, there is `ε > 0` such that for almost
every `t ∈ ℝ^ℓ` with `‖t‖ < ε` the pair `(f, Λ_t)` is in general position. -/
def HasParametricGeneralPosition (f : A.Obj → A.W) (N : A.B.One → ℝ) (U : Set A.Obj) : Prop :=
  ∀ (ℓ : ℕ) (Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0), (∀ t, IsScPlusMultisection A (Λ t)) →
    IsLinearFamily Λ → (∀ t x, pointwiseNorm N (Λ t) x ≤ ∑ j, |t j|) →
    (∀ t, domSupp (Λ t) ⊆ U) →
    (∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ solutionSet A.P f →
      IsParamOntoAt f Λ x) →
    ∃ ε > 0, ∀ᵐ t ∂(volume : Measure (Fin ℓ → ℝ)), ‖t‖ < ε → IsInGeneralPosition A f (Λ t)

/-! ### From local to global -/

variable {f : A.Obj → A.W} {N : A.B.One → ℝ} {U : Set A.Obj} {h : A.Obj → ℝ}

/-- **Finite sums of families** (`Λ_t = ⊕_i Λ^{x_i}_{t_i}`): families on `Q_i`, `i ∈ s`, give a
family on `⋃_{i ∈ s} Q_i` (the empty sum is `Λ₀`, which needs a good system). -/
theorem nonempty_gpFamily_biUnion (h𝒰 : Nonempty A.X.GoodSystem) (hN : A.B.IsAuxNorm N)
    {ι : Type*} (Q : ι → Set A.Obj) (F : ∀ i, Nonempty (GPFamily A f N U h (Q i)))
    (s : Finset ι) : Nonempty (GPFamily A f N U h (⋃ i ∈ s, Q i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨(GPFamily.zero h𝒰 hN (empty_subset U)).mono (by simp)⟩
  | insert a s _ ih =>
    obtain ⟨G⟩ := ih
    obtain ⟨Fa⟩ := F a
    exact ⟨(Fa.add hN G).mono (Finset.set_biUnion_insert a s Q).le⟩

/-- **"From local to global" (p. 696)**: if `|S_f|` is compact and every point of `S_f` lies in a
saturated open set carrying a family, then one family covers all of `S_f`. -/
theorem exists_gpFamily_of_compact (h𝒰 : Nonempty A.X.GoodSystem) (hN : A.B.IsAuxNorm N)
    (hS : A.E.HasCompactSolutionSetEp f) (hloc : HasLocalGPFamilies A f N U h) :
    ∃ Q : Set A.Obj, solutionSet A.P f ⊆ Q ∧ Nonempty (GPFamily A f N U h Q) := by
  classical
  choose Qx hQo hQs hxQ hF using hloc
  have hcov : A.X.π '' solutionSet A.P f ⊆ ⋃ i : solutionSet A.P f, A.X.π '' Qx i.1 i.2 := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_iUnion.2 ⟨⟨x, hx⟩, x, hxQ x hx, rfl⟩
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover (fun i : solutionSet A.P f => A.X.π '' Qx i.1 i.2)
    (fun i => A.X.proposition_7_1_8 _ (hQo i.1 i.2)) hcov
  refine ⟨⋃ i ∈ s, Qx i.1 i.2, fun y hy => ?_,
    nonempty_gpFamily_biUnion h𝒰 hN (fun i : solutionSet A.P f => Qx i.1 i.2)
      (fun i => hF i.1 i.2) s⟩
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (hs ⟨y, hy, rfl⟩)
  have hy' : y ∈ A.X.π ⁻¹' (A.X.π '' Qx i.1 i.2) := hyi
  rw [hQs i.1 i.2] at hy'
  exact mem_iUnion₂.2 ⟨i, hi, hy'⟩

/-! ### The choice of `t` -/

/-- **A small parameter off a null set**: if a property holds for almost every `t ∈ ℝ^ℓ` with
`‖t‖ < ε`, then it holds for some `t` with `‖t‖ < r`, for every `0 < r ≤ ε` (balls have positive
Lebesgue measure). -/
theorem exists_norm_lt_of_ae {ℓ : ℕ} {P : (Fin ℓ → ℝ) → Prop} {ε r : ℝ} (hr : 0 < r)
    (hrε : r ≤ ε) (hP : ∀ᵐ t ∂(volume : Measure (Fin ℓ → ℝ)), ‖t‖ < ε → P t) :
    ∃ t : Fin ℓ → ℝ, ‖t‖ < r ∧ P t := by
  by_contra H
  push Not at H
  have h0 : volume {t : Fin ℓ → ℝ | ¬(‖t‖ < ε → P t)} = 0 := ae_iff.1 hP
  have hsub : Metric.ball (0 : Fin ℓ → ℝ) r ⊆ {t | ¬(‖t‖ < ε → P t)} := fun t ht => by
    rw [mem_ball_zero_iff] at ht
    exact fun hP' => H t ht (hP' (ht.trans_le hrε))
  exact (Metric.measure_ball_pos volume (0 : Fin ℓ → ℝ) hr).ne' (measure_mono_null hsub h0)

/-- `|t|₁ < 1` for `‖t‖ < 1/(ℓ+1)` (sup norm on `ℝ^ℓ`). -/
theorem sum_abs_lt_one {ℓ : ℕ} {t : Fin ℓ → ℝ} (ht : ‖t‖ < 1 / (ℓ + 1)) : ∑ j, |t j| < 1 := by
  have h1 : ∑ j, |t j| ≤ ℓ * ‖t‖ := by
    calc ∑ j, |t j| ≤ ∑ _j : Fin ℓ, ‖t‖ :=
          Finset.sum_le_sum fun j _ => by
            rw [← Real.norm_eq_abs]; exact norm_le_pi_norm t j
      _ = ℓ * ‖t‖ := by simp
  have hℓ : (0 : ℝ) < ℓ + 1 := by positivity
  have h2 : ℓ * ‖t‖ ≤ ℓ * (1 / (ℓ + 1)) :=
    mul_le_mul_of_nonneg_left ht.le (Nat.cast_nonneg ℓ)
  have h3 : (ℓ : ℝ) * (1 / (ℓ + 1)) < 1 := by
    rw [mul_one_div, div_lt_one hℓ]; linarith
  linarith

/-- **Transversality from general position** (Remark 15.3.6, first sentence, with
`supp(Λ ∘ f) ⊆ X₁`). -/
theorem isTransversal_of_isInGeneralPosition (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (hgp : IsInGeneralPosition A f Λ) :
    IsTransversal f Λ := by
  intro x hx
  have hx1 := mem_levelSet_one_of_pos hf hΛ hx
  refine ⟨hx, hx1, fun L hL => hgp.surjective ?_ hL⟩
  rw [A.X.PObj.levelVal_levelMk]
  exact hx

/-! ### Theorem 15.3.7 -/

/-- **Theorem 15.3.7 (General Position; 2017: Theorem 15.4), pp. 693–698, existence part**, from
the two analytic steps of the proof: given a good system (part of "structurable", Definition
13.3.6), the local families (`HasLocalGPFamilies`) and the parametric transversality step
(`HasParametricGeneralPosition`), there is a structurable sc⁺-multisection functor `Λ` with
(1) `N(Λ) < h`, (2) `dom-supp(Λ) ⊆ U`, (3) `(f, Λ)` transversal, (4) `(f, Λ)` in general
position.  Proved here: the finite cover of `|S_f|`, the sum `⊕_i Λ^{x_i}`, its structurability
(Proposition 13.3.12), the bounds (1)–(2), and the choice of a small regular parameter. -/
theorem theorem_15_3_7_hyp (h𝒰 : Nonempty A.X.GoodSystem)
    (hf : A.E.IsScFredholmSectionFunctor f) (hS : A.E.HasCompactSolutionSetEp f)
    (hcc : ControlsCompactness A f N U) (hh : ∀ x, 0 < h x ∧ h x ≤ 1)
    (hloc : HasLocalGPFamilies A f N U h) (hsard : HasParametricGeneralPosition A f N U) :
    ∃ Λ : A.W → ℚ≥0, IsStructurable A Λ ∧ (∀ x, pointwiseNorm N Λ x < h x) ∧
      domSupp Λ ⊆ U ∧ IsTransversal f Λ ∧ IsInGeneralPosition A f Λ := by
  have hN : A.B.IsAuxNorm N := hcc.1.isAuxNorm
  obtain ⟨Q, hSQ, ⟨F⟩⟩ := exists_gpFamily_of_compact h𝒰 hN hS hloc
  obtain ⟨ε, hε, hae⟩ := hsard F.ℓ F.Λ (fun t => (F.isStructurable t).1) F.isLinear
    (fun t x => (F.norm_le t x).trans (mul_le_of_le_one_right
      (Finset.sum_nonneg fun j _ => abs_nonneg _) (hh x).2))
    F.domSupp_subset (fun x hx => F.paramOnto x (hSQ hx) hx)
  have hr : (0 : ℝ) < min ε (1 / (F.ℓ + 1)) := lt_min hε (by positivity)
  obtain ⟨t, ht, hgp⟩ := exists_norm_lt_of_ae hr (min_le_left _ _) hae
  have hsum : ∑ j, |t j| < 1 := sum_abs_lt_one (ht.trans_le (min_le_right _ _))
  refine ⟨F.Λ t, F.isStructurable t, fun x => ?_, F.domSupp_subset t,
    isTransversal_of_isInGeneralPosition hf (F.isStructurable t).1 hgp, hgp⟩
  exact (F.norm_le t x).trans_lt (mul_lt_of_lt_one_left (hh x).1 hsum)

/-- **Theorem 15.3.7 as stated (`theorem_15_3_7_statement`, G's proposition)** from a good system
and, under the hypotheses of the theorem, the two analytic steps of the proof
(`HasLocalGPFamilies`, `HasParametricGeneralPosition`). -/
theorem theorem_15_3_7_of_hyp (h𝒰 : Nonempty A.X.GoodSystem)
    (H : A.X.IsTame → A.X.AdmitsBumpFunctionsPointwise →
      ∀ f : A.Obj → A.W, A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
        A.E.HasCompactSolutionSetEp f →
        ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
        ∀ h : A.Obj → ℝ, Continuous h → (∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) →
          (∀ x, 0 < h x ∧ h x ≤ 1) →
          HasLocalGPFamilies A f N U h ∧ HasParametricGeneralPosition A f N U) :
    theorem_15_3_7_statement A := by
  intro htame hbump f hf hft hS N U hcc h hhc hhφ hh
  obtain ⟨hloc, hsard⟩ := H htame hbump f hf hft hS N U hcc h hhc hhφ hh
  exact theorem_15_3_7_hyp h𝒰 hf hS hcc hh hloc hsard

/-! ### Satisfiability on `ℝⁿ × ℝ⁰ → ℝⁿ` -/

/-- A good system exists on the trivial ep-groupoid of `ℝⁿ` (paracompact orbit space, Theorem
13.1.8). -/
theorem nonempty_goodSystem_epSEP_zero (n : ℕ) :
    Nonempty (StrongBundleEquivalenceExamples.epSEP n 0).X.GoodSystem :=
  ⟨((StrongBundleEquivalenceExamples.epSEP n 0).X.theorem_13_1_8
    (EpGroupoid.admitsBumpFunctionsPointwise_trivial_rn n).2 (fun _ => univ)
    (fun _ => isOpen_univ) fun _ => mem_univ _).choose⟩

/-- The fibres of `ℝⁿ × ℝ⁰ → ℝⁿ` are points. -/
theorem fiber_eq_epSEP_zero (n : ℕ) {y : (StrongBundleEquivalenceExamples.epSEP n 0).Obj}
    (a b : (StrongBundleEquivalenceExamples.epSEP n 0).P ⁻¹' {y}) : a = b :=
  Subtype.ext (Prod.ext (a.2.trans b.2.symm) (funext fun i => i.elim0))

/-- **`HasParametricGeneralPosition` is satisfiable**: on `ℝⁿ × ℝ⁰ → ℝⁿ` every pair is in general
position, for every `f`, `N`, `U`. -/
theorem hasParametricGeneralPosition_epSEP_zero (n : ℕ)
    (f : (StrongBundleEquivalenceExamples.epSEP n 0).Obj →
      (StrongBundleEquivalenceExamples.epSEP n 0).W)
    (N : (StrongBundleEquivalenceExamples.epSEP n 0).B.One → ℝ)
    (U : Set (StrongBundleEquivalenceExamples.epSEP n 0).Obj) :
    HasParametricGeneralPosition (StrongBundleEquivalenceExamples.epSEP n 0) f N U :=
  fun _ _ _ _ _ _ _ => ⟨1, one_pos, ae_of_all _ fun _ _ => isInGeneralPosition_epSEP_zero n f _⟩

/-- **`HasLocalGPFamilies` is satisfiable**: on `ℝⁿ × ℝ⁰ → ℝⁿ`, for every `f`, every auxiliary
norm `N`, every `U` and every `h ≥ 0`, the family `t ↦ Λ₀` (`ℓ = 0`) is a family on
`Q = ℝⁿ` (the fibres are `0`, so (15.1) holds). -/
theorem hasLocalGPFamilies_epSEP_zero (n : ℕ)
    (f : (StrongBundleEquivalenceExamples.epSEP n 0).Obj →
      (StrongBundleEquivalenceExamples.epSEP n 0).W)
    {N : (StrongBundleEquivalenceExamples.epSEP n 0).B.One → ℝ}
    (hN : (StrongBundleEquivalenceExamples.epSEP n 0).B.IsAuxNorm N)
    (U : Set (StrongBundleEquivalenceExamples.epSEP n 0).Obj)
    (h : (StrongBundleEquivalenceExamples.epSEP n 0).Obj → ℝ) :
    HasLocalGPFamilies (StrongBundleEquivalenceExamples.epSEP n 0) f N U h := by
  intro x _
  refine ⟨univ, isOpen_univ, ?_, mem_univ x, ⟨?_⟩⟩
  · exact (StrongBundleEquivalenceExamples.epSEP n 0).X.isSaturated_univ
  · let F₀ : GPFamily (StrongBundleEquivalenceExamples.epSEP n 0) f N U h ∅ :=
      GPFamily.zero (nonempty_goodSystem_epSEP_zero n) hN (empty_subset U)
    refine
      { ℓ := 0
        Λ := F₀.Λ
        isStructurable := F₀.isStructurable
        isLinear := F₀.isLinear
        norm_le := F₀.norm_le
        domSupp_subset := F₀.domSupp_subset
        paramOnto := fun y _ _ => ?_ }
    refine ⟨univ, 1, fun _ j => j.elim0, fun _ => 1, fun _ j => j.elim0, isOpen_univ,
      mem_univ _, fun t => ?_, fun L _ φ hφ hy m V T _ i w => ⟨0, zero_mem _, fun j => j.elim0,
        fiber_eq_epSEP_zero n _ _⟩⟩
    simp only [paramSec_fin_zero]
    exact isLocalRepOn_zeroMultisection isOpen_univ

/-- **The hypotheses of `theorem_15_3_7_of_hyp` hold together** on `ℝⁿ × ℝ⁰ → ℝⁿ`, which gives
the statement there through the reduction (G's `theorem_15_3_7_statement_epSEP_zero` proves it
directly). -/
theorem theorem_15_3_7_statement_epSEP_zero_of_hyp (n : ℕ) :
    theorem_15_3_7_statement (StrongBundleEquivalenceExamples.epSEP n 0) :=
  theorem_15_3_7_of_hyp (nonempty_goodSystem_epSEP_zero n)
    fun _ _ f _ _ _ N U hcc h _ _ _ =>
      ⟨hasLocalGPFamilies_epSEP_zero n f hcc.1.isAuxNorm U h,
        hasParametricGeneralPosition_epSEP_zero n f N U⟩

end SBLocalization

end Polyfold
