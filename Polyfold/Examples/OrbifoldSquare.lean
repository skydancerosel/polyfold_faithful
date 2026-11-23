import Polyfold.Examples.OrbifoldSquarePerturbation
import Polyfold.Chapter6.SmoothFiniteDimRanges

/-!
# The orbifold `ℂ/ℤ₅` and the section `z ↦ z²`: Theorem 16.6.6 for index `0`

A worked example for Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021),
**Theorem 16.6.6**, 2021 p. 739, for Fredholm index `0`.

## The example

`G = ℤ/5` acts on `ℂ` by `g · z = ζ^g z`, `ζ = exp(2πi/5)`; the ep-groupoid `X = G ⋉ ℂ` is
effective, with isotropy `ℤ/5` at `0` and trivial isotropy elsewhere.  The strong bundle is
`W = ℂ × ℂ → ℂ` with `g · (z, w) = (ζ^g z, ζ^{2g} w)`, and `f(z) = (z, z²)`: an sc-Fredholm
section functor of index `0` with solution set `{0}`, where `f'(0) = 0`.

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquare`)

* **`not_isTransversalAt_sectionMulti`**: for every sc⁺-section functor `s` of `W`
  (Definition 8.3.4 (2)): `s(0) = f(0)`, so `0` is a solution of `f = s`, and `(f, Λ_s)` is not
  transversal at `0` (Definition 15.2.1), `Λ_s` the multisection of the single section `s`.
  `fderiv_sub_eq_zero_of_equivariant` is the statement about the derivative: `(f − s)'(0) = 0`.
* **`theorem_16_6_6_hypotheses`**: the hypotheses of
  `theorem_16_6_6_index_zero_count_eq_unconditional` hold: `∂Z = ∅`, the solution set is compact,
  `n` is an auxiliary norm, `(n, Z)` controls compactness, and `CanonicalGermInput o 0` for the
  orientation `o = sqOrientationRep`.
* **`exists_canonical_t5`**: for `0 < |c| ≤ 1` the multisection `λ_c` with the five branches
  `z ↦ ζ^{2j} c` of weight `1/5` is admissible and has a perturbed solution set with the canonical
  orientation of `(f, o)`.
* **`count_eq_of_isAdmissible`**, **`exists_unique_count`**: the count of a closed `0`-form does
  not depend on the admissible perturbation; it is the count of `λ_c`, for every `0 < |c| ≤ 1`.
* `Λ5_sqSection_eq`, `Λ5_sqSection_pos_iff_orbit`, `π_ne_π_neg`: for `c = r²` the perturbed
  solution set consists of the two orbits of `r` and `−r`, with weight `1/5` and trivial
  isotropy.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.OrbifoldSquare

open TrivialBundle EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure StrongBundleEquivalenceExamples
  StrongBundleLocalizationExamples SBLocalization StrongRetr Linearization15 PolyfoldClass

/-! ### Multisections are needed -/

/-- **The derivative at `0` of an equivariant perturbation of `f` is zero**: if
`ψ(ζ z) = ζ² ψ(z)` for a `C^∞` map `ψ : ℂ → ℂ`, then `D(z² − ψ)(0) = 0`. -/
theorem fderiv_sub_eq_zero_of_equivariant {ψ : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (hψ : ContDiff ℝ ∞ ψ) (heq : ∀ x, ψ (rot ζ x) = rot (ζ ^ 2) (ψ x)) :
    fderiv ℝ (sq - ψ) 0 = 0 := by
  set h : (Fin 2 → ℝ) → (Fin 2 → ℝ) := sq - ψ with hh
  have hc : ContDiff ℝ ∞ h := contDiff_sq.sub hψ
  set D := fderiv ℝ h 0 with hD
  have hDat : HasFDerivAt h D 0 :=
    (hc.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hfun : h ∘ rot ζ = rot (ζ ^ 2) ∘ h := by
    funext x
    change sq (rot ζ x) - ψ (rot ζ x) = rot (ζ ^ 2) (sq x - ψ x)
    rw [sq_rot, heq, map_sub]
  have h1 : HasFDerivAt (h ∘ rot ζ) (D.comp (rot ζ)) 0 := by
    have h0 : HasFDerivAt h D (rot ζ 0) := by rw [map_zero]; exact hDat
    exact h0.comp 0 (rot ζ).hasFDerivAt
  have h2 : HasFDerivAt (rot (ζ ^ 2) ∘ h) ((rot (ζ ^ 2)).comp D) 0 :=
    (rot (ζ ^ 2)).hasFDerivAt.comp 0 hDat
  rw [hfun] at h1
  have e : D.comp (rot ζ) = (rot (ζ ^ 2)).comp D := h1.unique h2
  have hz := linear_eq_zero_of_equivariant D.toLinearMap fun x =>
    congrArg (fun S : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) => S x) e
  ext x : 1
  exact congrArg (fun S : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) => S x) hz

/-- An sc⁺-section of `ℂ × ℂ → ℂ` is the graph of a `C^∞` map. -/
theorem exists_contDiff_of_isScPlusSection {s : (Fin 2 → ℝ) → (Fin 2 → ℝ) × (Fin 2 → ℝ)}
    (hs : (bundle 2 2).IsScPlusSection s) :
    ∃ ψ : (Fin 2 → ℝ) → (Fin 2 → ℝ), ContDiff ℝ ∞ ψ ∧ s = graphSection ψ := by
  let ch : StrongBundleChart A5.X.PObj A5.P := chart (k := 2) (0 : Fin 2 → ℝ)
  have hch : A5.B.IsChart ch := isChart_chart 0
  have h := (IsScPlusSectionOn.of_isScPlusSection (A := A5) hs
    isOpen_univ).isScSmooth_principal_comp_r hch (subset_univ _)
  have h' : ContDiffOn ℝ ∞ (fun u : Fin 2 → ℝ => (ch.principal s ∘ r ch.R) u) univ :=
    IsScSmooth.contDiffOn_const (V := Fin 2 → ℝ) (isScDomain_univ _) h
  have e : (fun x : Fin 2 → ℝ => (s x).2) =
      fun u : Fin 2 → ℝ => (ch.principal s ∘ r ch.R) u := by
    funext u
    have h0 : u + 0 = u := add_zero u
    change (s u).2 = (s (u + 0)).2
    rw [h0]
  refine ⟨fun x => (s x).2, ?_, funext fun x => Prod.ext (hs.1 x) rfl⟩
  rw [e]
  exact contDiffOn_univ.1 h'

/-- **A single-valued equivariant perturbation is not transversal at `0`**, for the graph of a
`C^∞` map `ψ` with `ψ(ζ z) = ζ² ψ(z)`: `ψ(0) = 0`, and `(f, Λ_s)` is not transversal at `0`
(Definition 15.2.1), since `(f − s)'(0) = 0` is not onto `ℂ`. -/
theorem not_isTransversalAt_graph {ψ : (Fin 2 → ℝ) → (Fin 2 → ℝ)} (hψ : ContDiff ℝ ∞ ψ)
    (heq : ∀ x, ψ (rot ζ x) = rot (ζ ^ 2) (ψ x)) :
    ψ 0 = 0 ∧ ¬ IsTransversalAt (A := A5) sqSection (sectionMulti (A := A5) (graphSection ψ))
      (0 : Fin 2 → ℝ) := by
  classical
  have hψ0 : ψ 0 = 0 := by
    have h := heq 0
    rw [map_zero] at h
    exact eq_zero_of_rot_sq_fixed h.symm
  refine ⟨hψ0, ?_⟩
  rintro ⟨-, hx1, honto⟩
  have hf := isScFredholmSectionFunctor_sqSection
  have hs : A5.B.IsScPlusSection (graphSection ψ) := isScPlusSection_graphSection hψ
  set x := A5.X.PObj.levelMk 1 (0 : Fin 2 → ℝ) hx1 with hxdef
  have hxv : A5.X.PObj.levelVal 1 x = (0 : Fin 2 → ℝ) := A5.X.PObj.levelVal_levelMk _ _ _
  let ch : StrongBundleChart A5.X.PObj A5.P := chart (k := 2) (0 : Fin 2 → ℝ)
  have hch : A5.B.IsChart ch := isChart_chart 0
  have hx : A5.X.PObj.levelVal 1 x ∈ ch.φ.source := mem_univ _
  have hxs : sqSection (A5.X.PObj.levelVal 1 x) = graphSection ψ (A5.X.PObj.levelVal 1 x) := by
    rw [hxv]
    exact Prod.ext rfl (((sq_eq_zero_iff 0).2 rfl).trans hψ0.symm)
  have hL := honto _ ((mem_support_linearization_sectionMulti_iff hs hf hch hx hxs _).2 rfl)
  have hon := (surjective_toIntr_subDeriv_iff hf.1.1
    (IsScPlusSectionOn.of_isScPlusSection hs isOpen_univ) hch (subset_univ _) hx hxs).1 hL
  set z := levelLift ch.φ 1 (A5.X.PObj.levelVal 1 x) with hzdef
  have hz : z = 0 := by
    have h1 : ch.φ.model.E.toBase 1 z = ch.φ (A5.X.PObj.levelVal 1 x) :=
      A5.X.PObj.toBase_levelLift ch.isChart hx (A5.X.PObj.levelVal_mem x)
    rw [hxv] at h1
    have h2 : ch.φ (0 : Fin 2 → ℝ) = (0 : Fin 2 → ℝ) := sub_self (0 : Fin 2 → ℝ)
    exact h1.trans h2
  let w : Fin 2 → ℝ := cE.symm 1
  have hw : w ≠ 0 := fun h => by
    have : (1 : ℂ) = 0 := by
      rw [← cE.apply_symm_apply (1 : ℂ)]
      exact cE.map_eq_zero_iff.2 h
    exact one_ne_zero this
  obtain ⟨v, -, hv⟩ := hon w ⟨(_, w), ⟨mem_univ _, mem_univ _⟩, rfl⟩
  have he : ((fun y => ch.principal sqSection y - ch.principal (graphSection ψ) y) ∘ r ch.R) =
      loc (sq - ψ) 0 := by
    funext u
    rfl
  have hv1 : scDeriv ch.U ((fun y => ch.principal sqSection y -
      ch.principal (graphSection ψ) y) ∘ r ch.R) z v = w := hv
  rw [he, hz] at hv1
  have hv2 : fderiv ℝ (sq - ψ) 0 v = w :=
    (congrArg (fun S : (rnSc 2) 0 →L[ℝ] (rnSc 2) 0 => S v)
      (scDeriv_loc (contDiff_sq.sub hψ) 0)).symm.trans hv1
  rw [fderiv_sub_eq_zero_of_equivariant hψ heq] at hv2
  exact hw hv2.symm

/-- **Multisections are needed** (Definitions 8.3.4 (2), 15.2.1): for every sc⁺-section functor
`s` of `ℂ × ℂ → ℂ` over `ℤ/5 ⋉ ℂ` (an equivariant single-valued sc⁺-section), `s(0) = f(0)`, so
`0` lies in the perturbed solution set of the multisection `Λ_s` of `s`, and `(f, Λ_s)` is not
transversal at `0`: weight `2` has no invariant vector, and `(f − s)'(0) = −Ds(0)` is an
equivariant real-linear map of weight `1 → 2`, hence `0`. -/
theorem not_isTransversalAt_sectionMulti {s : (Fin 2 → ℝ) → (Fin 2 → ℝ) × (Fin 2 → ℝ)}
    (hs : A5.E.IsScPlusSectionFunctor s) :
    s 0 = sqSection 0 ∧ 0 < sectionMulti (A := A5) s (sqSection 0) ∧
      ¬ IsTransversalAt (A := A5) sqSection (sectionMulti (A := A5) s) (0 : Fin 2 → ℝ) := by
  obtain ⟨ψ, hψ, rfl⟩ := exists_contDiff_of_isScPlusSection hs.2
  have heq : ∀ x, ψ (rot ζ x) = rot (ζ ^ 2) (ψ x) := fun x => by
    obtain ⟨hsm, hfun⟩ := hs.1
    have h : graphSection ψ (Multiplicative.ofAdd (1 : ZMod 5) • x) =
        actW (Multiplicative.ofAdd 1) (graphSection ψ x) :=
      hfun ((Multiplicative.ofAdd 1, x) : A5.Mor)
    have h2 : ψ (rot (χ (Multiplicative.ofAdd 1)) x) =
        rot (χ (Multiplicative.ofAdd 1) ^ 2) (ψ x) := congrArg Prod.snd h
    rwa [χ_ofAdd_one] at h2
  obtain ⟨h0, hnt⟩ := not_isTransversalAt_graph hψ heq
  have e : graphSection ψ 0 = sqSection 0 :=
    Prod.ext rfl (h0.trans ((sq_eq_zero_iff 0).2 rfl).symm)
  exact ⟨e, (sectionMulti_pos_iff (A := A5) _ _).2 e.symm, hnt⟩

/-! ### Theorem 16.6.6 for index `0` -/

/-- **The hypotheses of Theorem 16.6.6 (2021 p. 739) for index `0` hold for
`|z| ↦ |(z, z²)|` over `ℂ/ℤ₅`**: `∂Z = ∅`, the solution set is compact, `n` is an auxiliary norm,
`Z` is open, `(n, Z)` controls compactness, and the model of the orientation `sqOrientationRep`
has tame germ data and Fredholm index `0`. -/
theorem theorem_16_6_6_hypotheses :
    sqBundle.polyfold.boundary = ∅ ∧ sqFredholmSection.1.HasCompactSolutionSet ∧
      sqBundle.IsAuxNorm n5 ∧ IsOpen (univ : Set A5.X.OrbitSpace) ∧
      sqFredholmSection.1.ControlsCompactness n5 (univ : Set A5.X.OrbitSpace) ∧
      CanonicalGermInput sqOrientationRep 0 :=
  ⟨sqBundle_boundary_eq_empty, hasCompactSolutionSet_sqFredholmSection, isAuxNorm_n5,
    isOpen_univ, controlsCompactness_n5, canonicalGermInput_sqOrientationRep⟩

/-- **Theorem 16.6.6 (2021 p. 739) for index `0`, for `|z| ↦ |(z, z²)|` over `ℂ/ℤ₅`**, in the
form of `theorem_16_6_6_index_zero_polyfold_statement`. -/
theorem theorem_16_6_6_sq :
    theorem_16_6_6_index_zero_polyfold_statement sqFredholmSection n5
      (univ : Set A5.X.OrbitSpace)
      (fun o Q => CanonicalGermInput o 0 ∧ IsCanonicalPointSolutionSet o Q) :=
  theorem_16_6_6_index_zero_all_admissible_unconditional _ _ _

/-- **The multisection `λ_c` with five branches is admissible and has a canonically oriented
perturbed solution set**, for `0 < |c| ≤ 1`: `λ_c` is controlled by `(n, Z)`, `(f, λ_c)` is in
general position, and `θ̂ = λ_c ∘ f` of dimension `0` carries the canonical orientation of
`(f, o)`. -/
theorem exists_canonical_t5 {c : ℂ} (hc0 : c ≠ 0) (hc1 : ‖c‖ ≤ 1) :
    ∃ Q : PointOrientedPerturbation sqFredholmSection.1, Q.t = t5 c ∧
      Q.IsAdmissible n5 (univ : Set A5.X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet sqOrientationRep Q :=
  theorem_16_6_6_index_zero_solutionSet_noBumps sqBundle_boundary_eq_empty isAuxNorm_n5
    isOpen_univ controlsCompactness_n5 canonicalGermInput_sqOrientationRep (t5 c)
    (isControlledBy_t5 hc1) (isInGeneralPositionWith_t5 hc0)

/-- **The count does not depend on the admissible perturbation** (Theorem 16.6.6, 2021 p. 739,
index `0`): any two admissible perturbations with the canonical orientation of `(f, o)` give the
same weighted signed count and the same effective count of a closed `0`-form. -/
theorem count_eq_of_isAdmissible {Q₀ Q₁ : PointOrientedPerturbation sqFredholmSection.1}
    (a₀ : Q₀.IsAdmissible n5 (univ : Set A5.X.OrbitSpace))
    (c₀ : IsCanonicalPointSolutionSet sqOrientationRep Q₀)
    (a₁ : Q₁.IsAdmissible n5 (univ : Set A5.X.OrbitSpace))
    (c₁ : IsCanonicalPointSolutionSet sqOrientationRep Q₁)
    (τ : ScForm sqBundle.polyfold 0) (hτ : ScForm.d τ = 0) :
    Q₀.count τ = Q₁.count τ ∧ Q₀.countEff τ = Q₁.countEff τ :=
  theorem_16_6_6_index_zero_count_eq_unconditional sqBundle_boundary_eq_empty isAuxNorm_n5
    isOpen_univ controlsCompactness_n5 canonicalGermInput_sqOrientationRep a₀ c₀ a₁ c₁ τ hτ

/-- **The invariant**: for a closed `0`-form `τ` there is exactly one number which is the count
of `τ` over every admissible perturbation with the canonical orientation of `(f, o)`; it is the
count over the five-branch multisection `λ_c`, for every `0 < |c| ≤ 1`. -/
theorem exists_unique_count (τ : ScForm sqBundle.polyfold 0) (hτ : ScForm.d τ = 0) :
    ∃! κ : ℝ, (∀ Q : PointOrientedPerturbation sqFredholmSection.1,
        Q.IsAdmissible n5 (univ : Set A5.X.OrbitSpace) →
        IsCanonicalPointSolutionSet sqOrientationRep Q → Q.count τ = κ) ∧
      ∀ c : ℂ, c ≠ 0 → ‖c‖ ≤ 1 → ∃ Q : PointOrientedPerturbation sqFredholmSection.1,
        Q.t = t5 c ∧ Q.IsAdmissible n5 (univ : Set A5.X.OrbitSpace) ∧
        IsCanonicalPointSolutionSet sqOrientationRep Q ∧ Q.count τ = κ := by
  obtain ⟨Q₁, -, a₁, c₁⟩ := exists_canonical_t5 (c := 1) one_ne_zero (by rw [norm_one])
  refine ⟨Q₁.count τ, ⟨fun Q a c => (count_eq_of_isAdmissible a c a₁ c₁ τ hτ).1,
    fun c hc0 hc1 => ?_⟩, fun κ hκ => (hκ.1 Q₁ a₁ c₁).symm⟩
  obtain ⟨Q, ht, a, hcan⟩ := exists_canonical_t5 hc0 hc1
  exact ⟨Q, ht, a, hcan, (count_eq_of_isAdmissible a hcan a₁ c₁ τ hτ).1⟩

/-! ### The perturbed solution set: two orbits of weight `1/5` -/

/-- Every perturbed solution lies on exactly one branch: `Λ(f(z))` is `1/5` or `0`. -/
theorem Λ5_sqSection_eq {c : ℂ} (hc : c ≠ 0) (x : Fin 2 → ℝ) :
    Λ5 c (sqSection x) = if ∃ j : ZMod 5, sq x = branchVal c j then 1 / 5 else 0 := by
  classical
  unfold Λ5
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    rw [Finset.sum_eq_single j]
    · exact if_pos ((sqSection_eq_branch_iff c j x).2 hj)
    · intro i _ hij
      refine if_neg fun hi => hij ?_
      exact branchVal_injective hc (((sqSection_eq_branch_iff c i x).1 hi).symm.trans hj)
    · intro hj'
      exact absurd (Finset.mem_univ j) hj'
  · refine Finset.sum_eq_zero fun i _ => if_neg fun hi => h ⟨i, ?_⟩
    exact (sqSection_eq_branch_iff c i x).1 hi

/-- **The perturbed solutions for `c = r²` are the two orbits of `r` and `−r`.** -/
theorem Λ5_sqSection_pos_iff_orbit (r : ℂ) (x : Fin 2 → ℝ) :
    0 < Λ5 (r ^ 2) (sqSection x) ↔
      (∃ g : G5, x = g • cE.symm r) ∨ ∃ g : G5, x = g • cE.symm (-r) := by
  rw [Λ5_sqSection_pos_iff]
  have key : ∀ j : ZMod 5, sq x = branchVal (r ^ 2) j ↔
      (x = Multiplicative.ofAdd j • cE.symm r ∨ x = Multiplicative.ofAdd j • cE.symm (-r)) := by
    intro j
    have e1 : sq x = branchVal (r ^ 2) j ↔ cE x ^ 2 = (χ (Multiplicative.ofAdd j) * r) ^ 2 := by
      rw [← cE.injective.eq_iff, cE_sq, cE_branchVal, mul_pow]
    have e2 : ∀ u : ℂ, x = Multiplicative.ofAdd j • cE.symm u ↔
        cE x = χ (Multiplicative.ofAdd j) * u := by
      intro u
      rw [← cE.injective.eq_iff, smul_def, cE_rot, ContinuousLinearEquiv.apply_symm_apply]
    rw [e1, e2, e2, mul_neg]
    exact sq_eq_sq_iff_eq_or_eq_neg
  constructor
  · rintro ⟨j, hj⟩
    rcases (key j).1 hj with h | h
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr ⟨_, h⟩
  · rintro (⟨g, hg⟩ | ⟨g, hg⟩)
    · exact ⟨Multiplicative.toAdd g, (key _).2 (Or.inl hg)⟩
    · exact ⟨Multiplicative.toAdd g, (key _).2 (Or.inr hg)⟩

/-- **The two orbits are different points of `ℂ/ℤ₅`**, for `r ≠ 0`: `−1` is not a fifth root of
unity. -/
theorem π_ne_π_neg {r : ℂ} (hr : r ≠ 0) : X5.π (cE.symm r) ≠ X5.π (cE.symm (-r)) := by
  intro h
  obtain ⟨k, hk⟩ := (action_π_eq_π_iff isScSmoothMap_smul).1 h
  have h1 : χ k * r = -r := by
    have := congrArg cE hk
    rwa [smul_def, cE_rot, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply] at this
  have h2 : χ k = -1 := by
    have h3 : χ k * r = -1 * r := by rw [h1, neg_one_mul]
    exact mul_right_cancel₀ hr h3
  have h4 : χ k ^ 2 = 1 := by rw [h2]; norm_num
  have h5 := (χ_sq_eq_one_iff k).1 h4
  rw [h5, χ_one] at h2
  norm_num at h2

/-- **The perturbed solutions have trivial isotropy**, for `c ≠ 0`. -/
theorem isRegular_of_Λ5_pos {c : ℂ} (hc : c ≠ 0) {x : Fin 2 → ℝ}
    (hx : 0 < Λ5 c (sqSection x)) : X5.IsRegular x := by
  obtain ⟨j, hj⟩ := (Λ5_sqSection_pos_iff c x).1 hx
  refine isRegular_X5_iff.2 fun h => branchVal_ne_zero hc j ?_
  rw [← hj, h]
  exact (sq_eq_zero_iff 0).2 rfl

end Polyfold.Examples.OrbifoldSquare
