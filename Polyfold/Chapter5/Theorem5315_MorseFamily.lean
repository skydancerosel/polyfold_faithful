import Polyfold.Chapter5.Theorem5315_MorseLagrange

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.3, the proof of
**Theorem 5.3.15** (pp. 224–228; 2017: Theorem 5.8; preprint: Theorem 5.22): the transversality
(5.12)–(5.14) and the parametrized Sard step, for a family of level sets.  Gap G.48.

# Generic non-degeneracy of the critical points on a family of level sets

## The text, paraphrased

(Proof of Theorem 5.3.15) With sections `s₁, …, s_m` such that `(λ, y) ↦ d(t|S_λ)(y)` has a
surjective linearization at the points `(0, y)`, `y` a critical point of `t|S`, the parametrized
Sard theorem gives parameters `λ` near `0` for which `t|S_λ` is a Morse function.

## What is formalized

In a chart of a finite-dimensional manifold the sets `S_λ` are the level sets `{h_λ = 0}` of
`h_λ(v) = μ(v) − Σ λᵢ Bᵢ(v)` (`famConstraint`), `μ, Bᵢ : V → F`, and `t` is a function `T` on `V`.

* `isOpen_setOf_surjective_clm`: onto operators into a finite-dimensional space form an open set.
* `surjective_fderiv_lagrangian_gradient` (**(5.13)–(5.14) in Lagrange form**): at a critical
  point `(v₀, c)` of the Lagrangian for `λ = 0`, the map
  `(λ, v, c) ↦ D_{(v, c)}(T − c(h_λ))` has a surjective derivative if `dμ(v₀)` is onto and the
  forms `Σ δᵢ c(dBᵢ(v₀) ·)`, `δ` with `Σ δᵢ Bᵢ(v₀) = 0`, restrict onto the dual of `ker dμ(v₀)`
  (in the text: the sections `sᵢ` of Lemma 5.3.17 realize a basis `τᵢ` of `T*_xS`).
* `ae_isLagrangeNondegenerate_family` (**the Sard step for the family**): under these hypotheses
  at every multiplier at `v₀` (none, if `v₀` is not a critical point), there are `ε > 0` and an
  open `Ω' ∋ v₀` such that for almost every `λ` with `|λ| < ε`, at every `v ∈ Ω'` with
  `h_λ(v) = 0`: `dh_λ(v)` is onto and every Lagrange multiplier `c` at `v` is non-degenerate.

## What the text leaves implicit, and the choices made

* The multiplier depends continuously on the critical point, so the critical points of
  `T|{h_λ = 0}` near `v₀`, `λ` small, lie in the open set where the transversality holds; this is
  the text's "since the section is smooth, there exists an open neighborhood `U(x)`".
-/

open Set Function MeasureTheory Module Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### Onto operators form an open set -/

section OpenSurjective

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
lemma surjective_of_isUnit_comp {A : E →L[ℝ] F} {R : F →L[ℝ] E} (h : IsUnit (A.comp R)) :
    Surjective A := by
  intro y
  have h1 : A.comp R * Ring.inverse (A.comp R) = 1 := Ring.mul_inverse_cancel _ h
  refine ⟨R (Ring.inverse (A.comp R) y), ?_⟩
  exact congrArg (fun L : F →L[ℝ] F => L y) h1

lemma exists_clm_rightInverse {A : E →L[ℝ] F} (hA : Surjective A) :
    ∃ R : F →L[ℝ] E, A.comp R = 1 := by
  obtain ⟨R, hR⟩ := (A : E →ₗ[ℝ] F).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hA)
  refine ⟨LinearMap.toContinuousLinearMap R, ContinuousLinearMap.ext fun y => ?_⟩
  exact congrArg (fun L : F →ₗ[ℝ] F => L y) hR

/-- **Onto operators into a finite-dimensional space form an open set.** -/
theorem isOpen_setOf_surjective_clm : IsOpen {A : E →L[ℝ] F | Surjective A} := by
  rw [isOpen_iff_mem_nhds]
  intro A₀ hA₀
  obtain ⟨R, hR⟩ := exists_clm_rightInverse hA₀
  have hcont : Continuous fun A : E →L[ℝ] F => A.comp R :=
    (ContinuousLinearMap.compL ℝ F E F).flip R |>.continuous
  have h1 : IsUnit (A₀.comp R) := by rw [hR]; exact isUnit_one
  have hmem : {A : E →L[ℝ] F | IsUnit (A.comp R)} ∈ 𝓝 A₀ :=
    hcont.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds h1)
  exact Filter.mem_of_superset hmem fun A hA => surjective_of_isUnit_comp hA

end OpenSurjective

/-! ### The family of constraints -/

section Family

variable {V Fc : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Fc]
  [NormedSpace ℝ Fc] {d : ℕ}

/-- **The constraint `h_λ = μ − Σ λᵢ Bᵢ`** of the level sets `S_λ` in a chart. -/
def famConstraint (μh : V → Fc) (B : Fin d → V → Fc) (lam : Fin d → ℝ) (v : V) : Fc :=
  μh v - ∑ i, lam i • B i v

/-- The derivative `dμ(v) − Σ λᵢ dBᵢ(v)` of the constraint. -/
def famConstraintDeriv (μh : V → Fc) (B : Fin d → V → Fc) (lam : Fin d → ℝ) (v : V) : V →L[ℝ] Fc :=
  fderiv ℝ μh v - ∑ i, lam i • fderiv ℝ (B i) v

variable {μh : V → Fc} {B : Fin d → V → Fc} {v : V}

lemma hasFDerivAt_famConstraint (hμ : DifferentiableAt ℝ μh v)
    (hB : ∀ i, DifferentiableAt ℝ (B i) v) (lam : Fin d → ℝ) :
    HasFDerivAt (famConstraint μh B lam) (famConstraintDeriv μh B lam v) v :=
  hμ.hasFDerivAt.sub (HasFDerivAt.fun_sum fun i _ => (hB i).hasFDerivAt.const_smul (lam i))

lemma famConstraintDeriv_zero : famConstraintDeriv μh B (0 : Fin d → ℝ) v = fderiv ℝ μh v := by
  simp [famConstraintDeriv]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma famConstraint_zero : famConstraint μh B (0 : Fin d → ℝ) v = μh v := by
  simp [famConstraint]

lemma famConstraintDeriv_apply (lam : Fin d → ℝ) (w : V) :
    famConstraintDeriv μh B lam v w = fderiv ℝ μh v w - ∑ i, lam i • fderiv ℝ (B i) v w := by
  simp [famConstraintDeriv]

end Family

/-! ### The Lagrangian of the family and its gradient -/

section Gradient

variable {V Fc : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Fc]
  [NormedSpace ℝ Fc] {d : ℕ}

/-- The Lagrangian of the family, `(λ, (v, c)) ↦ T(v) − c(h_λ(v))`. -/
def famLagrangian (T : V → ℝ) (μh : V → Fc) (B : Fin d → V → Fc)
    (q : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ))) : ℝ :=
  lagrangian T (famConstraint μh B q.1) q.2

/-- The gradient of the Lagrangian in `(v, c)`, as a function of `(λ, (v, c))`. -/
def famGradient (T : V → ℝ) (μh : V → Fc) (B : Fin d → V → Fc)
    (q : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ))) : (V × (Fc →L[ℝ] ℝ)) →L[ℝ] ℝ :=
  (fderiv ℝ (famLagrangian T μh B) q).comp
    (ContinuousLinearMap.inr ℝ (Fin d → ℝ) (V × (Fc →L[ℝ] ℝ)))

variable {Ω : Set V} {T : V → ℝ} {μh : V → Fc} {B : Fin d → V → Fc}

omit [NormedSpace ℝ V] in
lemma isOpen_famDomain (hΩ : IsOpen Ω) :
    IsOpen {q : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ)) | q.2.1 ∈ Ω} :=
  hΩ.preimage (continuous_fst.comp continuous_snd)

lemma contDiffOn_famLagrangian (hT : ContDiffOn ℝ ∞ T Ω) (hμ : ContDiffOn ℝ ∞ μh Ω)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) Ω) :
    ContDiffOn ℝ ∞ (famLagrangian T μh B)
      {q : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ)) | q.2.1 ∈ Ω} := by
  have hv : ContDiffOn ℝ ∞ (fun q : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ)) => q.2.1)
      {q | q.2.1 ∈ Ω} := (contDiff_fst.comp contDiff_snd).contDiffOn
  have hc : ContDiffOn ℝ ∞ (fun q : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ)) => q.2.2)
      {q | q.2.1 ∈ Ω} := (contDiff_snd.comp contDiff_snd).contDiffOn
  have hl : ∀ i, ContDiffOn ℝ ∞ (fun q : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ)) => q.1 i)
      {q | q.2.1 ∈ Ω} := fun i => ((contDiff_apply ℝ ℝ i).comp contDiff_fst).contDiffOn
  have h1 : ContDiffOn ℝ ∞ (fun q : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ)) => T q.2.1)
      {q | q.2.1 ∈ Ω} := hT.comp hv fun q hq => hq
  have h2 : ContDiffOn ℝ ∞ (fun q : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ)) => μh q.2.1)
      {q | q.2.1 ∈ Ω} := hμ.comp hv fun q hq => hq
  have h3 : ∀ i, ContDiffOn ℝ ∞ (fun q : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ)) => B i q.2.1)
      {q | q.2.1 ∈ Ω} := fun i => (hB i).comp hv fun q hq => hq
  have h4 : ContDiffOn ℝ ∞ (fun q : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ)) =>
      μh q.2.1 - ∑ i, q.1 i • B i q.2.1) {q | q.2.1 ∈ Ω} :=
    h2.sub (ContDiffOn.sum fun i _ => (hl i).smul (h3 i))
  exact h1.sub (hc.clm_apply h4)

variable (hΩ : IsOpen Ω) (hT : ContDiffOn ℝ ∞ T Ω) (hμ : ContDiffOn ℝ ∞ μh Ω)
  (hB : ∀ i, ContDiffOn ℝ ∞ (B i) Ω)

include hΩ hT hμ hB

lemma famGradient_eq {v : V} (hv : v ∈ Ω) (lam : Fin d → ℝ) (c : Fc →L[ℝ] ℝ) :
    famGradient T μh B (lam, (v, c)) =
      fderiv ℝ (lagrangian T (famConstraint μh B lam)) (v, c) := by
  have hd : DifferentiableAt ℝ (famLagrangian T μh B) (lam, (v, c)) :=
    ((contDiffOn_famLagrangian hT hμ hB).contDiffAt
      ((isOpen_famDomain hΩ).mem_nhds (show v ∈ Ω from hv))).differentiableAt (by simp)
  exact (fderiv_slice_eq (g := famLagrangian T μh B) (lam := lam) (z := (v, c)) hd).symm

lemma famGradient_apply {v : V} (hv : v ∈ Ω) (lam : Fin d → ℝ) (c : Fc →L[ℝ] ℝ)
    (z : V × (Fc →L[ℝ] ℝ)) :
    famGradient T μh B (lam, (v, c)) z =
      fderiv ℝ T v z.1 - c (famConstraintDeriv μh B lam v z.1) -
        z.2 (famConstraint μh B lam v) := by
  have hT1 : DifferentiableAt ℝ T v :=
    (hT.contDiffAt (hΩ.mem_nhds hv)).differentiableAt (by simp)
  have hμ1 : DifferentiableAt ℝ μh v :=
    (hμ.contDiffAt (hΩ.mem_nhds hv)).differentiableAt (by simp)
  have hB1 : ∀ i, DifferentiableAt ℝ (B i) v := fun i =>
    ((hB i).contDiffAt (hΩ.mem_nhds hv)).differentiableAt (by simp)
  have hh := hasFDerivAt_famConstraint hμ1 hB1 lam
  rw [famGradient_eq hΩ hT hμ hB hv, fderiv_lagrangian_apply hT1 hh.differentiableAt, hh.fderiv]

lemma contDiffOn_famGradient :
    ContDiffOn ℝ 1 (famGradient T μh B)
      {q : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ)) | q.2.1 ∈ Ω} := by
  set C : (((Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ))) →L[ℝ] ℝ) →L[ℝ] ((V × (Fc →L[ℝ] ℝ)) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (V × (Fc →L[ℝ] ℝ)) ((Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ))) ℝ).flip
      (ContinuousLinearMap.inr ℝ (Fin d → ℝ) (V × (Fc →L[ℝ] ℝ))) with hC
  have h2 : ContDiffOn ℝ 2 (famLagrangian T μh B)
      {q : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ)) | q.2.1 ∈ Ω} :=
    (contDiffOn_famLagrangian hT hμ hB).of_le (by decide)
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ (famLagrangian T μh B))
      {q : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ)) | q.2.1 ∈ Ω} :=
    h2.fderiv_of_isOpen (isOpen_famDomain hΩ) (by norm_num)
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := ((Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ))) →L[ℝ] ℝ) (F := (V × (Fc →L[ℝ] ℝ)) →L[ℝ] ℝ)
    C).comp_contDiffOn h1

/-- A directional derivative of the gradient, computed along a path. -/
lemma fderiv_famGradient_apply_of_path {q₀ : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ))}
    (hq₀ : q₀.2.1 ∈ Ω) {path : ℝ → (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ))}
    {w : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ))} (hpath : HasDerivAt path w 0) (h0 : path 0 = q₀)
    (z : V × (Fc →L[ℝ] ℝ)) {D : ℝ}
    (hD : HasDerivAt (fun s => famGradient T μh B (path s) z) D 0) :
    fderiv ℝ (famGradient T μh B) q₀ w z = D := by
  have hG : HasFDerivAt (famGradient T μh B) (fderiv ℝ (famGradient T μh B) q₀) (path 0) := by
    rw [h0]
    exact (((contDiffOn_famGradient hΩ hT hμ hB).contDiffAt
      ((isOpen_famDomain hΩ).mem_nhds (show q₀.2.1 ∈ Ω from hq₀))).differentiableAt
        (by simp)).hasFDerivAt
  have h1 : HasDerivAt (fun s : ℝ => famGradient T μh B (path s))
      (fderiv ℝ (famGradient T μh B) q₀ w) 0 :=
    HasFDerivAt.comp_hasDerivAt (E := (V × (Fc →L[ℝ] ℝ)) →L[ℝ] ℝ)
      (F := (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ))) (l := famGradient T μh B) (0 : ℝ) hG hpath
  have h2 : HasDerivAt (fun s : ℝ => famGradient T μh B (path s) z)
      (fderiv ℝ (famGradient T μh B) q₀ w z) 0 :=
    HasFDerivAt.comp_hasDerivAt (E := ℝ) (F := (V × (Fc →L[ℝ] ℝ)) →L[ℝ] ℝ)
      (l := fun A : (V × (Fc →L[ℝ] ℝ)) →L[ℝ] ℝ => A z) (0 : ℝ)
      (ContinuousLinearMap.apply ℝ ℝ z).hasFDerivAt h1
  exact h2.unique hD

end Gradient

/-! ### The transversality (5.13)–(5.14), in Lagrange form -/

section Transversality

variable {V Fc : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Fc]
  [NormedSpace ℝ Fc] [FiniteDimensional ℝ Fc] {d : ℕ}
  {Ω : Set V} {T : V → ℝ} {μh : V → Fc} {B : Fin d → V → Fc}
  (hΩ : IsOpen Ω) (hT : ContDiffOn ℝ ∞ T Ω) (hμ : ContDiffOn ℝ ∞ μh Ω)
  (hB : ∀ i, ContDiffOn ℝ ∞ (B i) Ω)

include hΩ hT hμ hB

omit [FiniteDimensional ℝ Fc] in
/-- The derivative of the gradient in the direction of the multiplier. -/
lemma fderiv_famGradient_mult {v₀ : V} (hv₀ : v₀ ∈ Ω) (c δc : Fc →L[ℝ] ℝ)
    (z : V × (Fc →L[ℝ] ℝ)) :
    fderiv ℝ (famGradient T μh B) ((0 : Fin d → ℝ), (v₀, c)) (0, (0, δc)) z =
      -δc (fderiv ℝ μh v₀ z.1) := by
  have hpath : HasDerivAt (fun s : ℝ => (((0 : Fin d → ℝ), (v₀, c + s • δc)) :
      (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ)))) (0, (0, δc)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => c + s • δc) δc 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δc).const_add c
    exact (hasDerivAt_const 0 (0 : Fin d → ℝ)).prodMk ((hasDerivAt_const 0 v₀).prodMk h1)
  refine fderiv_famGradient_apply_of_path hΩ hT hμ hB (show v₀ ∈ Ω from hv₀) hpath (by simp) z ?_
  have hline : (fun s : ℝ => famGradient T μh B ((0 : Fin d → ℝ), (v₀, c + s • δc)) z) =
      fun s => (fderiv ℝ T v₀ z.1 - c (fderiv ℝ μh v₀ z.1) - z.2 (μh v₀)) +
        s * (-δc (fderiv ℝ μh v₀ z.1)) := by
    funext s
    rw [famGradient_apply hΩ hT hμ hB hv₀, famConstraintDeriv_zero, famConstraint_zero]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hline]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (-δc (fderiv ℝ μh v₀ z.1))).const_add
    (fderiv ℝ T v₀ z.1 - c (fderiv ℝ μh v₀ z.1) - z.2 (μh v₀))

omit [FiniteDimensional ℝ Fc] in
/-- The derivative of the gradient in the direction of the parameter. -/
lemma fderiv_famGradient_param {v₀ : V} (hv₀ : v₀ ∈ Ω) (c : Fc →L[ℝ] ℝ) (δ : Fin d → ℝ)
    (z : V × (Fc →L[ℝ] ℝ)) :
    fderiv ℝ (famGradient T μh B) ((0 : Fin d → ℝ), (v₀, c)) (δ, (0, 0)) z =
      ∑ i, δ i * c (fderiv ℝ (B i) v₀ z.1) + z.2 (∑ i, δ i • B i v₀) := by
  have hpath : HasDerivAt (fun s : ℝ => ((s • δ, (v₀, c)) :
      (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ)))) (δ, (0, 0)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s • δ) δ 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const δ
    exact h1.prodMk (hasDerivAt_const 0 (v₀, c))
  refine fderiv_famGradient_apply_of_path hΩ hT hμ hB (show v₀ ∈ Ω from hv₀) hpath (by simp) z ?_
  have hline : (fun s : ℝ => famGradient T μh B (s • δ, (v₀, c)) z) =
      fun s => (fderiv ℝ T v₀ z.1 - c (fderiv ℝ μh v₀ z.1) - z.2 (μh v₀)) +
        s * (∑ i, δ i * c (fderiv ℝ (B i) v₀ z.1) + z.2 (∑ i, δ i • B i v₀)) := by
    funext s
    rw [famGradient_apply hΩ hT hμ hB hv₀, famConstraintDeriv_apply]
    simp only [famConstraint, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_sub,
      map_smul, map_sum]
    ring
  rw [hline]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
    (∑ i, δ i * c (fderiv ℝ (B i) v₀ z.1) + z.2 (∑ i, δ i • B i v₀))).const_add
    (fderiv ℝ T v₀ z.1 - c (fderiv ℝ μh v₀ z.1) - z.2 (μh v₀))

omit [FiniteDimensional ℝ Fc] in
/-- The derivative of the gradient in the direction of the point, on the multiplier part. -/
lemma fderiv_famGradient_point {v₀ : V} (hv₀ : v₀ ∈ Ω) (c : Fc →L[ℝ] ℝ) (δv : V)
    (ℓ : Fc →L[ℝ] ℝ) :
    fderiv ℝ (famGradient T μh B) ((0 : Fin d → ℝ), (v₀, c)) (0, (δv, 0)) (0, ℓ) =
      -ℓ (fderiv ℝ μh v₀ δv) := by
  have hline0 : HasDerivAt (fun s : ℝ => v₀ + s • δv) δv 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δv).const_add v₀
  have hpath : HasDerivAt (fun s : ℝ => (((0 : Fin d → ℝ), (v₀ + s • δv, c)) :
      (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ)))) (0, (δv, 0)) 0 :=
    (hasDerivAt_const 0 (0 : Fin d → ℝ)).prodMk (hline0.prodMk (hasDerivAt_const 0 c))
  refine fderiv_famGradient_apply_of_path hΩ hT hμ hB (show v₀ ∈ Ω from hv₀) hpath (by simp)
    (0, ℓ) ?_
  have hev : ∀ᶠ s : ℝ in 𝓝 0, v₀ + s • δv ∈ Ω := by
    have hc : ContinuousAt (fun s : ℝ => v₀ + s • δv) 0 := hline0.continuousAt
    exact hc.eventually (by simpa using hΩ.mem_nhds hv₀)
  have heq : (fun s : ℝ => famGradient T μh B ((0 : Fin d → ℝ), (v₀ + s • δv, c)) (0, ℓ)) =ᶠ[𝓝 0]
      fun s => -ℓ (μh (v₀ + s • δv)) := by
    filter_upwards [hev] with s hs
    rw [famGradient_apply hΩ hT hμ hB hs, famConstraint_zero]
    simp
  have hμ1 : HasFDerivAt μh (fderiv ℝ μh v₀) (v₀ + (0 : ℝ) • δv) := by
    simpa using ((hμ.contDiffAt (hΩ.mem_nhds hv₀)).differentiableAt (by simp)).hasFDerivAt
  have h1 : HasDerivAt (fun s : ℝ => μh (v₀ + s • δv)) (fderiv ℝ μh v₀ δv) 0 :=
    HasFDerivAt.comp_hasDerivAt (E := Fc) (F := V) (l := μh) (0 : ℝ) hμ1 hline0
  have h2 : HasDerivAt (fun s : ℝ => ℓ (μh (v₀ + s • δv))) (ℓ (fderiv ℝ μh v₀ δv)) 0 :=
    HasFDerivAt.comp_hasDerivAt (E := ℝ) (F := Fc) (l := ℓ) (0 : ℝ) ℓ.hasFDerivAt h1
  exact h2.neg.congr_of_eventuallyEq heq

/-- **The transversality (5.13)–(5.14) in Lagrange form**: let `dμ(v₀)` be onto and let the forms
`Σ δᵢ c(dBᵢ(v₀) ·)`, over the `δ` with `Σ δᵢ Bᵢ(v₀) = 0`, restrict onto the dual of
`ker dμ(v₀)`.  Then the gradient `(λ, v, c') ↦ D_{(v, c')}(T − c'(h_λ))` of the Lagrangian of the
family has a surjective derivative at `(0, v₀, c)`. -/
theorem surjective_fderiv_famGradient {v₀ : V} (hv₀ : v₀ ∈ Ω)
    (hsurj : Surjective (fderiv ℝ μh v₀)) (c : Fc →L[ℝ] ℝ)
    (hSC : ∀ β : V →L[ℝ] ℝ, ∃ δ : Fin d → ℝ, ∑ i, δ i • B i v₀ = 0 ∧
      ∀ κ, fderiv ℝ μh v₀ κ = 0 → β κ = ∑ i, δ i * c (fderiv ℝ (B i) v₀ κ)) :
    Surjective (fderiv ℝ (famGradient T μh B) ((0 : Fin d → ℝ), (v₀, c))) := by
  intro β
  set D := fderiv ℝ (famGradient T μh B) ((0 : Fin d → ℝ), (v₀, c)) with hD
  obtain ⟨r, hr⟩ := exists_eq_apply_of_dual_dual
    (β.comp (ContinuousLinearMap.inr ℝ V (Fc →L[ℝ] ℝ)))
  obtain ⟨δv, hδv⟩ := hsurj (-r)
  set β' := β - D (0, (δv, 0)) with hβ'
  have hβ'0 : ∀ ℓ : Fc →L[ℝ] ℝ, β' (0, ℓ) = 0 := fun ℓ => by
    have h1 : β (0, ℓ) = ℓ r := hr ℓ
    rw [hβ', sub_apply, h1, hD, fderiv_famGradient_point hΩ hT hμ hB hv₀, hδv]
    simp
  obtain ⟨δ, hδ0, hδ⟩ := hSC (β'.comp (ContinuousLinearMap.inl ℝ V (Fc →L[ℝ] ℝ)))
  obtain ⟨δc, hδc⟩ := exists_clm_comp_eq_of_ker_le (fderiv ℝ μh v₀)
    (β'.comp (ContinuousLinearMap.inl ℝ V (Fc →L[ℝ] ℝ)) -
      c.comp (∑ i, δ i • fderiv ℝ (B i) v₀)) fun κ hκ => by
    rw [sub_apply, hδ κ hκ]
    simp
  refine ⟨(0, (δv, 0)) + (δ, (0, 0)) - (0, (0, δc)), ContinuousLinearMap.ext fun z => ?_⟩
  have h1 : β z = β' z + D (0, (δv, 0)) z := by rw [hβ']; simp
  have h2 : β' z = β' (z.1, 0) + β' (0, z.2) := by rw [← map_add]; simp
  have h3 : β' (z.1, 0) = δc (fderiv ℝ μh v₀ z.1) + ∑ i, δ i * c (fderiv ℝ (B i) v₀ z.1) := by
    have := congrArg (fun L : V →L[ℝ] ℝ => L z.1) hδc
    simp only [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      sum_apply, smul_apply, map_sum, map_smul, smul_eq_mul] at this
    linarith
  have h4 : D (δ, (0, 0)) z = ∑ i, δ i * c (fderiv ℝ (B i) v₀ z.1) := by
    rw [hD, fderiv_famGradient_param hΩ hT hμ hB hv₀ c δ z, hδ0]; simp
  have h5 : D (0, (0, δc)) z = -δc (fderiv ℝ μh v₀ z.1) :=
    fderiv_famGradient_mult hΩ hT hμ hB hv₀ c δc z
  rw [map_sub, map_add, sub_apply, add_apply, h1, h2, h3, hβ'0, h4, h5]
  ring

end Transversality

/-! ### The Sard step for the family -/

section Sard

variable {V Fc : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Fc] [NormedSpace ℝ Fc] [FiniteDimensional ℝ Fc] {d : ℕ}
  {Ω : Set V} {T : V → ℝ} {μh : V → Fc} {B : Fin d → V → Fc}

/-- **The parametrized Sard step for a family of level sets** (proof of 2021 Theorem 5.3.15,
pp. 224–228): let `T, μ, Bᵢ` be `C^∞` on the open `Ω ⊆ V`, `h_λ = μ − Σ λᵢ Bᵢ`, `v₀ ∈ Ω` with
`dμ(v₀)` onto, and suppose that for every Lagrange multiplier `c` at `v₀` for `λ = 0`
(`μ(v₀) = 0`, `dT(v₀) = c ∘ dμ(v₀)`) the forms `Σ δᵢ c(dBᵢ(v₀) ·)`, `Σ δᵢ Bᵢ(v₀) = 0`, restrict
onto the dual of `ker dμ(v₀)`.  Then there are `ε > 0` and an open `Ω' ∋ v₀` such that for almost
every `λ` with `|λ| < ε`, at every `v ∈ Ω'` with `h_λ(v) = 0`: `dh_λ(v)` is onto, and every
Lagrange multiplier `c` at `v` (`dT(v) = c ∘ dh_λ(v)`) is non-degenerate. -/
theorem ae_isLagrangeNondegenerate_family (hΩ : IsOpen Ω) (hT : ContDiffOn ℝ ∞ T Ω)
    (hμ : ContDiffOn ℝ ∞ μh Ω) (hB : ∀ i, ContDiffOn ℝ ∞ (B i) Ω) {v₀ : V} (hv₀ : v₀ ∈ Ω)
    (hsurj : Surjective (fderiv ℝ μh v₀))
    (hSC : ∀ c : Fc →L[ℝ] ℝ, μh v₀ = 0 → fderiv ℝ T v₀ = c.comp (fderiv ℝ μh v₀) →
      ∀ β : V →L[ℝ] ℝ, ∃ δ : Fin d → ℝ, ∑ i, δ i • B i v₀ = 0 ∧
        ∀ κ, fderiv ℝ μh v₀ κ = 0 → β κ = ∑ i, δ i * c (fderiv ℝ (B i) v₀ κ)) :
    ∃ ε > 0, ∃ Ω' : Set V, IsOpen Ω' ∧ v₀ ∈ Ω' ∧ Ω' ⊆ Ω ∧
      ∀ᵐ lam : Fin d → ℝ, ‖lam‖ < ε → ∀ v ∈ Ω', famConstraint μh B lam v = 0 →
        Surjective (fderiv ℝ (famConstraint μh B lam) v) ∧
        ∀ c : Fc →L[ℝ] ℝ, fderiv ℝ T v = c.comp (fderiv ℝ (famConstraint μh B lam) v) →
          IsLagrangeNondegenerate T (famConstraint μh B lam) v c := by
  classical
  set W₀ : Set ((Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ))) := {q | q.2.1 ∈ Ω} with hW₀def
  have hW₀ : IsOpen W₀ := isOpen_famDomain hΩ
  have hG1 := contDiffOn_famGradient hΩ hT hμ hB
  set W₁ : Set ((Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ))) :=
    W₀ ∩ fderiv ℝ (famGradient T μh B) ⁻¹' {A | Surjective A} with hW₁def
  have hW₁ : IsOpen W₁ :=
    (hG1.continuousOn_fderiv_of_isOpen hW₀ le_rfl).isOpen_inter_preimage hW₀
      isOpen_setOf_surjective_clm
  have hg2 : ContDiffOn ℝ 2 (famLagrangian T μh B) W₁ :=
    ((contDiffOn_famLagrangian hT hμ hB).of_le (by decide)).mono inter_subset_left
  have hae := ae_hasOnlyMorseCriticalPointsOn (volume : Measure (Fin d → ℝ)) hW₁ hg2
    (fun p hp _ => hp.2)
  -- differentiability on `Ω`
  have hT1 : ∀ v ∈ Ω, DifferentiableAt ℝ T v := fun v hv =>
    (hT.contDiffAt (hΩ.mem_nhds hv)).differentiableAt (by simp)
  have hμ1 : ∀ v ∈ Ω, DifferentiableAt ℝ μh v := fun v hv =>
    (hμ.contDiffAt (hΩ.mem_nhds hv)).differentiableAt (by simp)
  have hB1 : ∀ v ∈ Ω, ∀ i, DifferentiableAt ℝ (B i) v := fun v hv i =>
    ((hB i).contDiffAt (hΩ.mem_nhds hv)).differentiableAt (by simp)
  -- a right inverse of `dμ(v₀)` and the multiplier as a continuous function
  obtain ⟨R₀, hR₀⟩ := exists_clm_rightInverse hsurj
  set p₀ : (Fin d → ℝ) × V := (0, v₀) with hp₀
  have hsnd : Tendsto (Prod.snd : (Fin d → ℝ) × V → V) (𝓝 p₀) (𝓝 v₀) := continuousAt_snd
  have hfst : ∀ i, ContinuousAt (fun p : (Fin d → ℝ) × V => p.1 i) p₀ := fun i =>
    ((continuous_apply i).comp continuous_fst).continuousAt
  have hΩev : ∀ᶠ p : (Fin d → ℝ) × V in 𝓝 p₀, p.2 ∈ Ω := hsnd.eventually (hΩ.mem_nhds hv₀)
  have hdμ : ContinuousAt (fun p : (Fin d → ℝ) × V => fderiv ℝ μh p.2) p₀ :=
    ContinuousAt.comp (g := fderiv ℝ μh) (f := Prod.snd) (x := p₀)
      ((hμ.contDiffAt (hΩ.mem_nhds hv₀)).continuousAt_fderiv (by simp)) continuousAt_snd
  have hdB : ∀ i, ContinuousAt (fun p : (Fin d → ℝ) × V => fderiv ℝ (B i) p.2) p₀ := fun i =>
    ContinuousAt.comp (g := fderiv ℝ (B i)) (f := Prod.snd) (x := p₀)
      (((hB i).contDiffAt (hΩ.mem_nhds hv₀)).continuousAt_fderiv (by simp)) continuousAt_snd
  have hdT : ContinuousAt (fun p : (Fin d → ℝ) × V => fderiv ℝ T p.2) p₀ :=
    ContinuousAt.comp (g := fderiv ℝ T) (f := Prod.snd) (x := p₀)
      ((hT.contDiffAt (hΩ.mem_nhds hv₀)).continuousAt_fderiv (by simp)) continuousAt_snd
  have hDh : ContinuousAt (fun p : (Fin d → ℝ) × V => famConstraintDeriv μh B p.1 p.2) p₀ :=
    hdμ.sub (tendsto_finsetSum _ fun i _ => (hfst i).smul (hdB i))
  set uu : (Fin d → ℝ) × V → (Fc →L[ℝ] Fc) := fun p =>
    (famConstraintDeriv μh B p.1 p.2).comp R₀ with huu
  have huc : ContinuousAt uu p₀ := hDh.clm_comp continuousAt_const
  have hu0 : uu p₀ = 1 := by
    change (famConstraintDeriv μh B (0 : Fin d → ℝ) v₀).comp R₀ = 1
    rw [famConstraintDeriv_zero, hR₀]
  have hunit : ∀ᶠ p in 𝓝 p₀, IsUnit (uu p) :=
    huc.eventually (by rw [hu0]; exact Units.isOpen.mem_nhds isUnit_one)
  have hinv : ContinuousAt (fun p => Ring.inverse (uu p)) p₀ := by
    have h1 : ContinuousAt Ring.inverse (uu p₀) := by
      rw [hu0]; exact NormedRing.inverse_continuousAt (1 : (Fc →L[ℝ] Fc)ˣ)
    exact ContinuousAt.comp (g := Ring.inverse) (f := uu) h1 huc
  set cc : (Fin d → ℝ) × V → (Fc →L[ℝ] ℝ) := fun p =>
    (fderiv ℝ T p.2).comp (R₀.comp (Ring.inverse (uu p))) with hcc
  have hccc : ContinuousAt cc p₀ := hdT.clm_comp (continuousAt_const.clm_comp hinv)
  have hmult : ∀ p : (Fin d → ℝ) × V, IsUnit (uu p) → ∀ c : Fc →L[ℝ] ℝ,
      fderiv ℝ T p.2 = c.comp (famConstraintDeriv μh B p.1 p.2) → c = cc p := by
    intro p hp c hc
    have h1 : uu p * Ring.inverse (uu p) = 1 := Ring.mul_inverse_cancel _ hp
    refine ContinuousLinearMap.ext fun y => ?_
    have h2 : uu p (Ring.inverse (uu p) y) = y := congrArg (fun L : Fc →L[ℝ] Fc => L y) h1
    change c y = fderiv ℝ T p.2 (R₀ (Ring.inverse (uu p) y))
    rw [hc]
    change c y = c (uu p (Ring.inverse (uu p) y))
    rw [h2]
  -- the neighbourhood
  have hN : ∀ᶠ p : (Fin d → ℝ) × V in 𝓝 p₀, p.2 ∈ Ω ∧ IsUnit (uu p) ∧
      ∀ c : Fc →L[ℝ] ℝ, famConstraint μh B p.1 p.2 = 0 →
        fderiv ℝ T p.2 = c.comp (famConstraintDeriv μh B p.1 p.2) → (p.1, (p.2, c)) ∈ W₁ := by
    by_cases hP : μh v₀ = 0 ∧ fderiv ℝ T v₀ = (cc p₀).comp (fderiv ℝ μh v₀)
    · have hq : ((p₀.1, (p₀.2, cc p₀)) : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ))) ∈ W₁ :=
        ⟨hv₀, surjective_fderiv_famGradient hΩ hT hμ hB hv₀ hsurj (cc p₀)
          (hSC (cc p₀) hP.1 hP.2)⟩
      have hΘ : ContinuousAt (fun p : (Fin d → ℝ) × V =>
          ((p.1, (p.2, cc p)) : (Fin d → ℝ) × (V × (Fc →L[ℝ] ℝ)))) p₀ :=
        continuousAt_fst.prodMk (continuousAt_snd.prodMk hccc)
      filter_upwards [hΩev, hunit, hΘ.preimage_mem_nhds (hW₁.mem_nhds hq)] with p h1 h2 h3
      exact ⟨h1, h2, fun c _ hc => by rw [hmult p h2 c hc]; exact h3⟩
    · rcases not_and_or.1 hP with h | h
      · have hcon : ContinuousAt (fun p : (Fin d → ℝ) × V => famConstraint μh B p.1 p.2) p₀ := by
          have hμc : ContinuousAt (fun p : (Fin d → ℝ) × V => μh p.2) p₀ :=
            ContinuousAt.comp (g := μh) (f := Prod.snd) (x := p₀)
              (hμ1 v₀ hv₀).continuousAt continuousAt_snd
          have hBc : ∀ i, ContinuousAt (fun p : (Fin d → ℝ) × V => B i p.2) p₀ := fun i =>
            ContinuousAt.comp (g := B i) (f := Prod.snd) (x := p₀)
              (hB1 v₀ hv₀ i).continuousAt continuousAt_snd
          exact hμc.sub (tendsto_finsetSum _ fun i _ => (hfst i).smul (hBc i))
        have hne : ∀ᶠ p in 𝓝 p₀, famConstraint μh B p.1 p.2 ≠ 0 :=
          hcon.eventually_ne (by rw [hp₀]; simpa [famConstraint_zero] using h)
        filter_upwards [hΩev, hunit, hne] with p h1 h2 h3
        exact ⟨h1, h2, fun c h0 _ => absurd h0 h3⟩
      · have hcon : ContinuousAt (fun p : (Fin d → ℝ) × V =>
            fderiv ℝ T p.2 - (cc p).comp (famConstraintDeriv μh B p.1 p.2)) p₀ :=
          hdT.sub (hccc.clm_comp hDh)
        have hne : ∀ᶠ p in 𝓝 p₀,
            fderiv ℝ T p.2 - (cc p).comp (famConstraintDeriv μh B p.1 p.2) ≠ 0 := by
          refine hcon.eventually_ne ?_
          rw [hp₀]
          simp only [famConstraintDeriv_zero]
          exact sub_ne_zero.2 h
        filter_upwards [hΩev, hunit, hne] with p h1 h2 h3
        refine ⟨h1, h2, fun c _ hc => absurd ?_ h3⟩
        rw [← hmult p h2 c hc]
        exact sub_eq_zero.2 hc
  obtain ⟨S₁, S₂, hS₁, h0S₁, hS₂, hvS₂, hsub⟩ := mem_nhds_prod_iff'.1 hN
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hS₁ 0 h0S₁
  refine ⟨ε, hε, S₂ ∩ Ω, hS₂.inter hΩ, ⟨hvS₂, hv₀⟩, inter_subset_right, ?_⟩
  filter_upwards [hae] with lam hlam hlε v hv hv0
  obtain ⟨-, hu, hW⟩ := hsub (show ((lam, v) : (Fin d → ℝ) × V) ∈ S₁ ×ˢ S₂ from
    ⟨hball (mem_ball_zero_iff.2 hlε), hv.1⟩)
  have hh := hasFDerivAt_famConstraint (hμ1 v hv.2) (hB1 v hv.2) lam
  rw [hh.fderiv]
  refine ⟨surjective_of_isUnit_comp hu, fun c hc => ?_⟩
  have hq := hW c hv0 hc
  have hcrit : fderiv ℝ (lagrangian T (famConstraint μh B lam)) (v, c) = 0 :=
    (fderiv_lagrangian_eq_zero_iff (hT1 v hv.2) hh.differentiableAt c).2
      ⟨hv0, by rw [hh.fderiv]; exact hc⟩
  exact hlam (v, c) hq hcrit

end Sard

end Polyfold
