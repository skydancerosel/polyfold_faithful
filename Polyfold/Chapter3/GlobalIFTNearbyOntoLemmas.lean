import Polyfold.Chapter3.GlobalIFTNearbySurj

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Theorem 3.54 (1), the surjectivity of `f'(y)` at the nearby zeros: the elementary lemmas.**

# The finite-dimensional lemmas of the surjectivity argument

## The text, paraphrased

(Proof of Theorem 3.54, (4)) "For every `y ∈ V` satisfying `f(y) = 0` ... `f'(y)` is surjective.
Property (4) follows from Corollary 3.41 and from Lemma 3.55."  The text's argument has a gap
(Finding 100: Corollary 3.41 gives the surjectivity of the *filled* derivative `Dg(z₀)`, and
passing to the intrinsic linearization needs condition (3) of Definition 3.4 at `z₀`).  The repair
(Findings 180–189) solves, for a fixed zero `z₀` and a fixed smooth `λ`, the perturbed equation
`g(u) + μ ρ(r(u)) λ = 0` along a one-sided `C¹`-curve `u(μ)` through `z₀`; the curve lies in the
retract `O` by condition (2) of the filler, so its velocity `ξ` is tangent to `O` and
`Dg(z₀) ξ = −ρ(z₀) λ`.

## What is formalized

The elementary parts of that argument, with no sc-structure involved:

* `Polyfold.exists_inward_of_isInGoodPosition` (**an interior direction from good position**): a
  nonzero finite-dimensional subspace `N` in good position (Definition 3.21) to the partial
  quadrant `C_z` at a point `z ∈ C` contains a vector `v` with `z + t(v + ζ) ∈ C` for all small
  `t ≥ 0` and all small `ζ`.
* `Polyfold.inward_add_smul`: such inward directions form a cone stable under the addition of
  arbitrary vectors after rescaling.
* `Polyfold.exists_curve_of_inward` (**a one-sided curve of zeros of a `C¹`-map on a partial
  quadrant**): for `H : (−μ*, μ*) × (N₀ ∩ C̃) → ℝᴺ` of class `C¹` with `H(0, a₀) = 0`,
  `D_aH(0, a₀)` onto, and an inward direction `α₀` with `DH(0, a₀)(1, α₀) = 0`, there is a
  continuous curve `a : [0, μ₀) → N₀ ∩ C̃`, `a(0) = a₀`, right-differentiable at `0` with
  `a'(0⁺) = α₀` and `H(μ, a(μ)) = 0`: a contraction `ζ ↦ ζ − S H(μ, a₀ + μα₀ + ζ)` on the ball
  of radius `cμ` in a complement of `ker D_aH(0, a₀)`.
* `Polyfold.hasDerivWithinAt_smul_right_of_continuousWithinAt`: `μ ↦ μ k(μ)` has the right
  derivative `k(0)` at `0` for `k` continuous at `0`.
* `Polyfold.StrongRetr.mem_O_of_perturbed_zero` (**zeros of the perturbed filler lie in `O`**):
  `g(u) + μ ρ(r(u)) λ = 0` gives `ρ(r(u)) g(u) = g(u)`, so `u ∈ O` by condition (2) of
  Definition 3.4.

## What the text leaves implicit, and the choices made (the findings)

None of these lemmas is in the text (Findings 180–189).  The interior direction needs `N ≠ 0`:
for the trivial subspace the good-position condition is empty, and the case `d = 0` of Theorem
3.54 (1) is treated separately (the zero set near `x₀` is `{x₀}`).
-/

open Set Filter Topology Function Module ContinuousLinearMap Metric Asymptotics

noncomputable section

namespace Polyfold

/-! ### A finite minimum -/

/-- A finite family of positive reals has a positive lower bound. -/
lemma exists_pos_le_of_forall_pos_fin {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ m > 0, ∀ i, m ≤ f i := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1, one_pos, fun i => (h.false i).elim⟩
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
    exact ⟨f i₀, hf i₀, fun i => hi₀ i (Finset.mem_univ i)⟩

/-! ### An interior direction from good position -/

section Inward

variable {E : ScBanach} {n : ℕ} {W : ScBanach} {C : Set (E 0)}

/-- **An interior direction of the partial quadrant `C_z` inside a subspace in good position.**
Let `C = {x | ∀ i, ℓ_i(x) ≥ 0}` be a partial quadrant with the coordinate functionals
`ℓ_i = (T·)_i` of a presentation `T`, `z ∈ C`, and `N ≠ 0` a subspace in good position to the
partial quadrant `C_z = {v | ℓ_i(v) ≥ 0 for all i with ℓ_i(z) = 0}` at `z`.  Then there is `v ∈ N`
with `z + t(v + ζ) ∈ C` for all `t ∈ [0, t₀]` and all `‖ζ‖ < η`.

Proof: let `y ∈ N` be an interior point of `N ∩ C_z` in `N`.  For an active index `i`
(`ℓ_i(z) = 0`), `ℓ_i(y) > 0`: otherwise `ℓ_i(y) = 0` and, since `y ± tu ∈ C_z` for `u ∈ N` and
small `t`, `ℓ_i` vanishes on `N`; a good complement `P` then satisfies `ℓ_i(p) = 0` for all
`p ∈ P` (scale a nonzero `n₀ ∈ N ∩ C_z` so that `‖p‖ ≤ ε‖n₀‖`; then `n₀ ± p ∈ C_z`), so
`ℓ_i = 0` on `N ⊕ P = E`, which is absurd.  So `ℓ_i(y) ≥ m > 0` for the active `i` and
`ℓ_i(z) ≥ m` for the others, and `ℓ_i(z + t(y + ζ)) ≥ 0` for all `i` when `‖ζ‖` and `t` are
small. -/
theorem exists_inward_of_isInGoodPosition (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0) {z : E 0} (hz : z ∈ C) {N : Submodule ℝ (E 0)}
    (hN0 : N ≠ ⊥) (hN : IsInGoodPosition E (partialQuadrantAtWith T z) N) :
    ∃ v ∈ N, ∃ η > 0, ∃ t₀ > 0, ∀ ζ : E 0, ‖ζ‖ < η → ∀ t ∈ Icc (0 : ℝ) t₀,
      z + t • (v + ζ) ∈ C := by
  classical
  set ℓ := coordCLMWith T with hℓ
  have hmemC : ∀ x, x ∈ C ↔ ∀ i, 0 ≤ ℓ i x := mem_iff_coordCLMWith T hT
  have hmemCz : ∀ x, x ∈ partialQuadrantAtWith T z ↔ ∀ i, ℓ i z = 0 → 0 ≤ ℓ i x :=
    mem_partialQuadrantAtWith_iff_coordCLMWith T z
  have hcone : ∀ x ∈ partialQuadrantAtWith T z, ∀ s : ℝ, 0 ≤ s →
      s • x ∈ partialQuadrantAtWith T z := fun x hx s hs => by
    rw [hmemCz] at hx ⊢
    intro i hi
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg hs (hx i hi)
  obtain ⟨y, hy⟩ := hN.interior_nonempty
  obtain ⟨Pc, hPc⟩ := hN.exists_goodComplement
  obtain ⟨ε, hε, hgood⟩ := hPc.exists_eps
  obtain ⟨η₁, hη₁, hη₁'⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy)
  have hball : ∀ n' : N, ‖n' - y‖ < η₁ → (n' : E 0) ∈ partialQuadrantAtWith T z :=
    fun n' hn' => hη₁' (by rwa [mem_ball, dist_eq_norm])
  have hyCz : (y : E 0) ∈ partialQuadrantAtWith T z := hball y (by rw [sub_self, norm_zero]; exact hη₁)
  -- an active functional vanishing at `y` vanishes on `N`
  have hvan : ∀ i, ℓ i z = 0 → ℓ i y = 0 → ∀ u ∈ N, ℓ i u = 0 := by
    intro i hiz hiy u hu
    have key : ∀ t : ℝ, |t| * ‖u‖ < η₁ → 0 ≤ t * ℓ i u := by
      intro t ht
      have hmem := hball (y + t • ⟨u, hu⟩) (by
        have hun : ‖(⟨u, hu⟩ : N)‖ = ‖u‖ := rfl
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hun]
        exact ht)
      have := (hmemCz _).1 hmem i hiz
      rw [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, hiy, zero_add,
        smul_eq_mul] at this
      exact this
    set t : ℝ := η₁ / (2 * (‖u‖ + 1)) with ht
    have htpos : 0 < t := by positivity
    have htu : t * ‖u‖ < η₁ := by
      rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg u]
    have h1 := key t (by rw [abs_of_pos htpos]; exact htu)
    have h2 := key (-t) (by rw [abs_neg, abs_of_pos htpos]; exact htu)
    nlinarith
  -- the active functionals are positive at `y`
  have hpos : ∀ i, ℓ i z = 0 → 0 < ℓ i y := by
    intro i hiz
    by_contra hneg
    have hiy : ℓ i y = 0 := le_antisymm (not_lt.1 hneg) ((hmemCz _).1 hyCz i hiz)
    have hvanN := hvan i hiz hiy
    -- a nonzero `n₀ ∈ N ∩ C_z`
    obtain ⟨n₀, hn₀N, hn₀Cz, hn₀0⟩ : ∃ n₀ ∈ N, n₀ ∈ partialQuadrantAtWith T z ∧ n₀ ≠ 0 := by
      by_cases hy0 : (y : E 0) = 0
      · obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
        refine ⟨u, hu, ?_, hu0⟩
        -- `N ⊆ C_z`: a ball around `y = 0` in `N` lies in `C_z`, which is a cone
        set s : ℝ := η₁ / (2 * (‖u‖ + 1)) with hs
        have hspos : 0 < s := by positivity
        have hmem := hball (y + s • ⟨u, hu⟩) (by
          have hun : ‖(⟨u, hu⟩ : N)‖ = ‖u‖ := rfl
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hspos, hun, hs,
            div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg u])
        have h1 : ((y + s • ⟨u, hu⟩ : N) : E 0) = s • u := by
          rw [Submodule.coe_add, hy0, zero_add]; rfl
        rw [h1] at hmem
        have := hcone _ hmem s⁻¹ (inv_nonneg.2 hspos.le)
        rwa [smul_smul, inv_mul_cancel₀ hspos.ne', one_smul] at this
      · exact ⟨y, y.2, hyCz, hy0⟩
    have hn₀norm : 0 < ‖n₀‖ := norm_pos_iff.2 hn₀0
    -- `ℓ i` vanishes on the good complement
    have hvanP : ∀ p ∈ Pc, ℓ i p = 0 := by
      intro p hp
      have hboth : ∀ q ∈ Pc, ‖q‖ = ‖p‖ → 0 ≤ ℓ i q := by
        intro q hq hqn
        set s : ℝ := ‖p‖ / (ε * ‖n₀‖) with hs
        have hs0 : 0 ≤ s := by positivity
        have hle : ‖q‖ ≤ ε * ‖s • n₀‖ := by
          have : ε * ‖s • n₀‖ = ‖p‖ := by
            rw [norm_smul, Real.norm_of_nonneg hs0, hs]
            field_simp
          rw [hqn, this]
        have hsn := hcone n₀ hn₀Cz s hs0
        have := (hgood (s • n₀) (N.smul_mem s hn₀N) q hq hle).1 hsn
        have h2 := (hmemCz _).1 this i hiz
        rw [map_add, map_smul, hvanN n₀ hn₀N, smul_zero, zero_add] at h2
        exact h2
      have h1 := hboth p hp rfl
      have h2 := hboth (-p) (Pc.neg_mem hp) (norm_neg p)
      rw [map_neg] at h2
      linarith
    -- so `ℓ i = 0` on `N ⊕ P = E`
    have hzero : ∀ x : E 0, ℓ i x = 0 := by
      intro x
      have hx : x ∈ N ⊔ Pc := by rw [hPc.isCompl.sup_eq_top]; trivial
      obtain ⟨u, hu, p, hp, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add, hvanN u hu, hvanP p hp, add_zero]
    -- but `ℓ i (T⁻¹(e_i, 0)) = 1`
    have h1 := hzero ((T 0).symm (Pi.single i 1, 0))
    rw [hℓ, coordCLMWith_apply, ContinuousLinearEquiv.apply_symm_apply] at h1
    simp at h1
  -- the uniform bound `m` and the operator bound `K₀`
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_of_forall_pos_fin
    (fun i => if ℓ i z = 0 then ℓ i y else ℓ i z) (fun i => by
      by_cases hi : ℓ i z = 0
      · rw [if_pos hi]; exact hpos i hi
      · rw [if_neg hi]
        exact lt_of_le_of_ne ((hmemC z).1 hz i) (Ne.symm hi))
  have hmy : ∀ i, ℓ i z = 0 → m ≤ ℓ i y := fun i hi => by
    have := hmle i; rwa [if_pos hi] at this
  have hmz : ∀ i, ℓ i z ≠ 0 → m ≤ ℓ i z := fun i hi => by
    have := hmle i; rwa [if_neg hi] at this
  set K₀ : ℝ := ‖(T 0 : E 0 →L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W) 0)‖ with hK₀
  have hK₀0 : 0 ≤ K₀ := norm_nonneg _
  have hℓb : ∀ i (x : E 0), |ℓ i x| ≤ K₀ * ‖x‖ := by
    intro i x
    rw [hℓ, coordCLMWith_apply]
    calc |(T 0 x).1 i| = ‖(T 0 x).1 i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖(T 0 x).1‖ := norm_le_pi_norm _ i
      _ ≤ ‖T 0 x‖ := norm_fst_le _
      _ ≤ ‖(T 0 : E 0 →L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W) 0)‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm (T 0 : E 0 →L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W) 0) x
      _ = K₀ * ‖x‖ := rfl
  set η : ℝ := m / (2 * (K₀ + 1)) with hη
  have hηpos : 0 < η := by positivity
  have hηK : K₀ * η ≤ m / 2 := by
    rw [hη, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  set t₀ : ℝ := m / ((K₀ + 1) * (‖y‖ + η) + 1) with ht₀
  have ht₀pos : 0 < t₀ := by positivity
  refine ⟨y, y.2, η, hηpos, t₀, ht₀pos, fun ζ hζ t ht => ?_⟩
  rw [hmemC]
  intro i
  rw [map_add, map_smul, map_add, smul_eq_mul]
  have hζb : |ℓ i ζ| ≤ K₀ * η := (hℓb i ζ).trans (by gcongr)
  have hyb : |ℓ i y| ≤ K₀ * ‖y‖ := hℓb i y
  by_cases hi : ℓ i z = 0
  · rw [hi, zero_add]
    have h1 : m / 2 ≤ ℓ i y + ℓ i ζ := by
      have := hmy i hi
      have := abs_le.1 hζb
      linarith
    exact mul_nonneg ht.1 (by linarith)
  · have h1 := hmz i hi
    have h2 : |t * (ℓ i y + ℓ i ζ)| ≤ t₀ * (K₀ * (‖y‖ + η)) := by
      rw [abs_mul, abs_of_nonneg ht.1]
      refine mul_le_mul ht.2 ?_ (abs_nonneg _) ht₀pos.le
      calc |ℓ i y + ℓ i ζ| ≤ |ℓ i y| + |ℓ i ζ| := abs_add_le _ _
        _ ≤ K₀ * ‖y‖ + K₀ * η := add_le_add hyb hζb
        _ = K₀ * (‖y‖ + η) := by ring
    have h3 : t₀ * (K₀ * (‖y‖ + η)) < m := by
      rw [ht₀, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg y]
    have := abs_le.1 h2
    linarith

/-- Inward directions are stable under the addition of an arbitrary vector after rescaling: if
`a₀ + t(α + β) ∈ C̃` for `t ∈ [0, t₀]`, `‖β‖ < η`, then for every `a₁` and `s ≥ (‖a₁‖ + 1)/η`
the vector `α₀ = a₁ + s α` satisfies `a₀ + t(α₀ + β) ∈ C̃` for `t ∈ [0, t₀/s]`, `‖β‖ < 1`. -/
theorem inward_add_smul {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {Ct : Set P}
    {a₀ α : P} {η t₀ : ℝ} (hη : 0 < η)
    (hin : ∀ β : P, ‖β‖ < η → ∀ t ∈ Icc (0 : ℝ) t₀, a₀ + t • (α + β) ∈ Ct) (a₁ : P) :
    ∃ s > 0, ∀ β : P, ‖β‖ < 1 → ∀ t ∈ Icc (0 : ℝ) (t₀ / s), a₀ + t • (a₁ + s • α + β) ∈ Ct := by
  set s : ℝ := (‖a₁‖ + 1) / η + 1 with hs
  have hspos : 0 < s := by positivity
  have hsη : (‖a₁‖ + 1) / s < η := by
    rw [div_lt_iff₀ hspos, hs]
    have : 0 < (‖a₁‖ + 1) / η := by positivity
    calc ‖a₁‖ + 1 = η * ((‖a₁‖ + 1) / η) := by field_simp
      _ < η * ((‖a₁‖ + 1) / η + 1) := by nlinarith
  refine ⟨s, hspos, fun β hβ t ht => ?_⟩
  have hβ' : ‖s⁻¹ • (a₁ + β)‖ < η := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hspos.le, ← div_eq_inv_mul]
    calc ‖a₁ + β‖ / s ≤ (‖a₁‖ + 1) / s := by
          gcongr
          exact (norm_add_le _ _).trans (by linarith)
      _ < η := hsη
  have hts : t * s ∈ Icc (0 : ℝ) t₀ := by
    refine ⟨mul_nonneg ht.1 hspos.le, ?_⟩
    have := ht.2
    rwa [le_div_iff₀ hspos] at this
  have := hin _ hβ' (t * s) hts
  convert this using 2
  simp only [smul_add, smul_smul]
  rw [mul_assoc, mul_inv_cancel₀ hspos.ne', mul_one]
  abel

end Inward

/-! ### A one-sided curve of zeros of a `C¹`-map on a partial quadrant -/

section Curve

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

omit [FiniteDimensional ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] in
/-- The map `(μ, ζ) ↦ (μ, a₀ + μ α₀ + ζ)` stays close to `(0, a₀)`. -/
lemma dist_curve_le {a₀ α₀ : P} {μ : ℝ} (hμ : 0 ≤ μ) {ζ : P} {c : ℝ} (hζ : ‖ζ‖ ≤ c * μ) :
    dist ((μ, a₀ + μ • α₀ + ζ) : ℝ × P) (0, a₀) ≤ μ * (1 + ‖α₀‖ + c) := by
  rw [Prod.dist_eq, dist_zero_right, dist_eq_norm, Real.norm_of_nonneg hμ]
  have hc : 0 ≤ c * μ := (norm_nonneg ζ).trans hζ
  refine max_le (by nlinarith [norm_nonneg α₀]) ?_
  calc ‖a₀ + μ • α₀ + ζ - a₀‖ = ‖μ • α₀ + ζ‖ := by congr 1; abel
    _ ≤ ‖μ • α₀‖ + ‖ζ‖ := norm_add_le _ _
    _ ≤ μ * ‖α₀‖ + c * μ := by rw [norm_smul, Real.norm_of_nonneg hμ]; exact add_le_add le_rfl hζ
    _ ≤ μ * (1 + ‖α₀‖ + c) := by nlinarith

/-- **A one-sided curve of zeros inside the quadrant** (the finite-dimensional implicit function
theorem at a boundary point, in the direction of an inward vector).  Let `C̃ ⊆ P` be convex,
`Ω` open, `D = Ω ∩ (ℝ × C̃)`, `H : D → Q` of class `C¹` with `H(0, a₀) = 0`, `D_aH(0, a₀)` onto,
and `α₀` an inward direction at `a₀` (`a₀ + t(α₀ + β) ∈ C̃` for `t ∈ [0, t₀]`, `‖β‖ < η`) with
`DH(0, a₀)(1, α₀) = 0`.  Then there are `μ₀ > 0` and `a : ℝ → P` with `a(0) = a₀`, right
derivative `α₀` at `0`, and `(μ, a(μ)) ∈ D`, `H(μ, a(μ)) = 0` for `0 ≤ μ < μ₀`.

Proof: with a right inverse `S` of `M₀ = D_aH(0, a₀)` and `Z = range S`, the map
`T_μ(ζ) = ζ − S H(μ, a₀ + μα₀ + ζ)` is a `1/2`-contraction of the ball of radius `cμ` in `Z`
(`c = η/2`; the mean value inequality with the continuity of `DH` at `(0, a₀)`), mapping it into
itself because `‖T_μ(0)‖ = ‖S H(μ, a₀ + μα₀)‖ = o(μ)` (differentiability of `H` at `(0, a₀)` in
the direction `(1, α₀)`).  Its fixed point `ζ(μ)` satisfies `‖ζ(μ)‖ ≤ 2‖T_μ(0)‖ = o(μ)`, and
`a(μ) = a₀ + μα₀ + ζ(μ)`. -/
theorem exists_curve_of_inward {Ct : Set P} (hCt : Convex ℝ Ct) {Ω : Set (ℝ × P)} (hΩ : IsOpen Ω)
    {a₀ : P} (ha₀ : a₀ ∈ Ct) (h0Ω : ((0 : ℝ), a₀) ∈ Ω) {H : ℝ × P → Q}
    (hH : ContDiffOn ℝ 1 H (Ω ∩ univ ×ˢ Ct)) (hH0 : H (0, a₀) = 0)
    (hsurj : Surjective ((fderivWithin ℝ H (Ω ∩ univ ×ˢ Ct) (0, a₀)).comp
      (ContinuousLinearMap.inr ℝ ℝ P)))
    {α₀ : P} (hα₀ : fderivWithin ℝ H (Ω ∩ univ ×ˢ Ct) (0, a₀) (1, α₀) = 0)
    {η t₀ : ℝ} (hη : 0 < η) (ht₀ : 0 < t₀)
    (hin : ∀ β : P, ‖β‖ < η → ∀ t ∈ Icc (0 : ℝ) t₀, a₀ + t • (α₀ + β) ∈ Ct) :
    ∃ μ₀ > 0, ∃ a : ℝ → P, a 0 = a₀ ∧ HasDerivWithinAt a α₀ (Ici 0) 0 ∧
      ∀ μ ∈ Ico 0 μ₀, (μ, a μ) ∈ Ω ∩ univ ×ˢ Ct ∧ H (μ, a μ) = 0 := by
  classical
  set D := Ω ∩ univ ×ˢ Ct with hDdef
  have h0D : ((0 : ℝ), a₀) ∈ D := ⟨h0Ω, mem_univ _, ha₀⟩
  -- `C̃` has nonempty interior, so `D` has unique differentiability
  have hint : (interior (univ ×ˢ Ct : Set (ℝ × P))).Nonempty := by
    rw [interior_prod_eq, interior_univ]
    refine ⟨(0, a₀ + t₀ • α₀), mem_univ _, mem_interior_iff_mem_nhds.2 ?_⟩
    refine Metric.mem_nhds_iff.2 ⟨t₀ * η, by positivity, fun b hb => ?_⟩
    rw [mem_ball, dist_eq_norm] at hb
    have hβ : ‖t₀⁻¹ • (b - (a₀ + t₀ • α₀))‖ < η := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg ht₀.le, ← div_eq_inv_mul, div_lt_iff₀ ht₀]
      linarith
    have := hin _ hβ t₀ ⟨ht₀.le, le_rfl⟩
    convert this using 1
    rw [smul_add, smul_smul, mul_inv_cancel₀ ht₀.ne', one_smul]
    abel
  have hD : UniqueDiffOn ℝ D := by
    rw [hDdef, inter_comm]
    exact (uniqueDiffOn_convex (convex_univ.prod hCt) hint).inter hΩ
  set DH := fderivWithin ℝ H D with hDHdef
  have hDHc : ContinuousOn DH D := hH.continuousOn_fderivWithin hD le_rfl
  have hDHd : ∀ p ∈ D, HasFDerivWithinAt H (DH p) D p := fun p hp =>
    (hH.differentiableOn one_ne_zero p hp).hasFDerivWithinAt
  set M₀ : P →L[ℝ] Q := (DH (0, a₀)).comp (ContinuousLinearMap.inr ℝ ℝ P) with hM₀
  -- a right inverse `S` of `M₀` and the complement `Z = range S`
  obtain ⟨S₀, hS₀⟩ := (M₀ : P →ₗ[ℝ] Q).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hsurj)
  set S : Q →L[ℝ] P := LinearMap.toContinuousLinearMap S₀ with hS
  have hMS : ∀ q, M₀ (S q) = q := fun q => by
    have := LinearMap.congr_fun hS₀ q
    exact this
  set Z : Submodule ℝ P := LinearMap.range (S : Q →ₗ[ℝ] P) with hZ
  have hZc : IsClosed (Z : Set P) := Z.closed_of_finiteDimensional
  have hSmem : ∀ q, S q ∈ Z := fun q => ⟨q, rfl⟩
  have hSM : ∀ ζ ∈ Z, S (M₀ ζ) = ζ := by
    rintro _ ⟨q, rfl⟩
    change S (M₀ (S q)) = S q
    rw [hMS]
  -- the constants
  set c : ℝ := η / 2 with hc
  have hcpos : 0 < c := by positivity
  have hcη : c < η := by rw [hc]; linarith
  set κ : ℝ := 1 / (2 * (‖S‖ + 1)) with hκ
  have hκpos : 0 < κ := by positivity
  have hSκ : ‖S‖ * κ ≤ 1 / 2 := by
    rw [hκ, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [norm_nonneg S]
  -- continuity of `DH` at `(0, a₀)`
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousWithinAt_iff.1 (hDHc _ h0D) κ hκpos
  -- the open set `Ω` around `(0, a₀)`
  obtain ⟨ε₀, hε₀, hε₀'⟩ := Metric.isOpen_iff.1 hΩ _ h0Ω
  set L : ℝ := 1 + ‖α₀‖ + c with hL
  have hLpos : 0 < L := by positivity
  -- points `(μ, a₀ + μα₀ + ζ)` with `‖ζ‖ ≤ cμ`, `0 ≤ μ ≤ t₀`, `μ L < ε₀` lie in `D`
  have hmemD : ∀ μ : ℝ, 0 ≤ μ → μ ≤ t₀ → μ * L < ε₀ → ∀ ζ : P, ‖ζ‖ ≤ c * μ →
      ((μ, a₀ + μ • α₀ + ζ) : ℝ × P) ∈ D := by
    intro μ hμ hμt hμε ζ hζ
    refine ⟨hε₀' ?_, mem_univ _, ?_⟩
    · rw [mem_ball]
      exact (dist_curve_le hμ hζ).trans_lt hμε
    · show a₀ + μ • α₀ + ζ ∈ Ct
      rcases hμ.lt_or_eq with hμ' | hμ'
      · have hβ : ‖μ⁻¹ • ζ‖ < η := by
          rw [norm_smul, norm_inv, Real.norm_of_nonneg hμ, ← div_eq_inv_mul, div_lt_iff₀ hμ']
          nlinarith
        have := hin _ hβ μ ⟨hμ, hμt⟩
        have h1 : a₀ + μ • (α₀ + μ⁻¹ • ζ) = a₀ + μ • α₀ + ζ := by
          rw [smul_add, smul_smul, mul_inv_cancel₀ hμ'.ne', one_smul, add_assoc]
        rwa [h1] at this
      · subst hμ'
        have : ζ = 0 := by
          rw [mul_zero] at hζ
          exact norm_le_zero_iff.1 hζ
        rw [this, zero_smul, add_zero, add_zero]
        exact ha₀
  -- little-o: `H(μ, a₀ + μ α₀) = o(μ)` as `μ → 0⁺`
  set μ₁ : ℝ := min t₀ (ε₀ / L) with hμ₁
  have hμ₁pos : 0 < μ₁ := lt_min ht₀ (by positivity)
  have hcurveD : MapsTo (fun μ : ℝ => ((μ, a₀ + μ • α₀) : ℝ × P)) (Ico 0 μ₁) D := by
    intro μ hμ
    have h1 := hmemD μ hμ.1 (hμ.2.le.trans (min_le_left _ _)) (by
      have := hμ.2.trans_le (min_le_right _ _)
      rwa [lt_div_iff₀ hLpos] at this) 0 (by rw [norm_zero]; exact mul_nonneg hcpos.le hμ.1)
    simpa using h1
  have hlo : HasDerivWithinAt (fun μ : ℝ => H (μ, a₀ + μ • α₀)) 0 (Ici 0) 0 := by
    have hγ : HasDerivWithinAt (fun μ : ℝ => ((μ, a₀ + μ • α₀) : ℝ × P)) ((1 : ℝ), α₀)
        (Ico 0 μ₁) 0 := by
      refine HasDerivWithinAt.prodMk (hasDerivWithinAt_id _ _) ?_
      simpa using ((hasDerivWithinAt_id (0 : ℝ) (Ico 0 μ₁)).smul_const α₀).const_add a₀
    have h0' : HasFDerivWithinAt H (DH (0, a₀)) D
        ((fun μ : ℝ => ((μ, a₀ + μ • α₀) : ℝ × P)) 0) := by
      simpa using hDHd _ h0D
    have h1 := h0'.comp_hasDerivWithinAt (0 : ℝ) hγ hcurveD
    rw [show DH (0, a₀) ((1 : ℝ), α₀) = 0 from hα₀] at h1
    exact h1.mono_of_mem_nhdsWithin (Ico_mem_nhdsGE hμ₁pos)
  rw [hasDerivWithinAt_iff_isLittleO] at hlo
  simp only [zero_smul, smul_zero, add_zero, sub_zero, hH0] at hlo
  have hlo' := isLittleO_iff.1 hlo (show (0 : ℝ) < c * κ by positivity)
  obtain ⟨μ₂, hμ₂, hμ₂'⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hlo')
  have hsmall : ∀ μ ∈ Ico (0 : ℝ) μ₂, ‖H (μ, a₀ + μ • α₀)‖ ≤ c * κ * μ := by
    intro μ hμ
    have := hμ₂' (y := μ) (by rw [dist_zero_right, Real.norm_of_nonneg hμ.1]; exact hμ.2) hμ.1
    rwa [Real.norm_of_nonneg hμ.1] at this
  -- the radius `μ₀`
  set μ₀ : ℝ := min (min μ₁ μ₂) (δ₁ / L) with hμ₀
  have hμ₀pos : 0 < μ₀ := lt_min (lt_min hμ₁pos hμ₂) (by positivity)
  have hμ₀t : μ₀ ≤ t₀ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hμ₀ε : ∀ μ, 0 ≤ μ → μ < μ₀ → μ * L < ε₀ := fun μ hμ hμ' => by
    have := hμ'.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
    rwa [lt_div_iff₀ hLpos] at this
  have hμ₀δ : ∀ μ, 0 ≤ μ → μ < μ₀ → μ * L < δ₁ := fun μ hμ hμ' => by
    have := hμ'.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ hLpos] at this
  have hμ₀₂ : μ₀ ≤ μ₂ := (min_le_left _ _).trans (min_le_right _ _)
  -- the fixed point for each `μ ∈ (0, μ₀)`
  have hfix : ∀ μ ∈ Ioo (0 : ℝ) μ₀, ∃ ζ ∈ Z, ‖ζ‖ ≤ c * μ ∧
      ‖ζ‖ ≤ 2 * ‖S (H (μ, a₀ + μ • α₀))‖ ∧ H (μ, a₀ + μ • α₀ + ζ) = 0 := by
    intro μ hμ
    have hμ0 : 0 ≤ μ := hμ.1.le
    have hμt : μ ≤ t₀ := hμ.2.le.trans hμ₀t
    have hμε := hμ₀ε μ hμ0 hμ.2
    have hμδ := hμ₀δ μ hμ0 hμ.2
    set Bμ : Set P := (Z : Set P) ∩ closedBall 0 (c * μ) with hBμ
    have hBc : IsClosed Bμ := hZc.inter isClosed_closedBall
    have hBconv : Convex ℝ Bμ := Z.convex.inter (convex_closedBall 0 _)
    have hmemB : ∀ ζ, ζ ∈ Bμ ↔ ζ ∈ Z ∧ ‖ζ‖ ≤ c * μ := fun ζ => by
      rw [hBμ, mem_inter_iff, mem_closedBall, dist_zero_right]; rfl
    have h0B : (0 : P) ∈ Bμ := (hmemB 0).2 ⟨Z.zero_mem, by rw [norm_zero]; positivity⟩
    set Tμ : P → P := fun ζ => ζ - S (H (μ, a₀ + μ • α₀ + ζ)) with hTμ
    -- the mean value inequality for `Φ(ζ) = H(μ, a₀ + μα₀ + ζ) − M₀ ζ`
    set Φ : P → Q := fun ζ => H (μ, a₀ + μ • α₀ + ζ) - M₀ ζ with hΦ
    have hΦd : ∀ ζ ∈ Bμ, HasFDerivWithinAt Φ
        ((DH (μ, a₀ + μ • α₀ + ζ)).comp (ContinuousLinearMap.inr ℝ ℝ P) - M₀) Bμ ζ := by
      intro ζ hζ
      have hζ' := (hmemB ζ).1 hζ
      have hpD : ((μ, a₀ + μ • α₀ + ζ) : ℝ × P) ∈ D := hmemD μ hμ0 hμt hμε ζ hζ'.2
      have haff : HasFDerivWithinAt (fun ζ' : P => ((μ, a₀ + μ • α₀ + ζ') : ℝ × P))
          (ContinuousLinearMap.inr ℝ ℝ P) Bμ ζ := by
        have := ((ContinuousLinearMap.inr ℝ ℝ P).hasFDerivWithinAt (s := Bμ) (x := ζ)).const_add
          ((μ, a₀ + μ • α₀) : ℝ × P)
        refine this.congr (fun ζ' _ => ?_) ?_ <;> simp
      have hmaps : MapsTo (fun ζ' : P => ((μ, a₀ + μ • α₀ + ζ') : ℝ × P)) Bμ D := fun ζ' hζ' =>
        hmemD μ hμ0 hμt hμε ζ' ((hmemB ζ').1 hζ').2
      have h1 := (hDHd _ hpD).comp ζ haff hmaps
      exact h1.sub (M₀.hasFDerivWithinAt)
    have hΦb : ∀ ζ ∈ Bμ,
        ‖(DH (μ, a₀ + μ • α₀ + ζ)).comp (ContinuousLinearMap.inr ℝ ℝ P) - M₀‖ ≤ κ := by
      intro ζ hζ
      have hζ' := (hmemB ζ).1 hζ
      have hpD : ((μ, a₀ + μ • α₀ + ζ) : ℝ × P) ∈ D := hmemD μ hμ0 hμt hμε ζ hζ'.2
      have hpδ : dist ((μ, a₀ + μ • α₀ + ζ) : ℝ × P) (0, a₀) < δ₁ :=
        (dist_curve_le hμ0 hζ'.2).trans_lt hμδ
      have hclose := hδ₁' hpD hpδ
      rw [dist_eq_norm] at hclose
      refine ContinuousLinearMap.opNorm_le_bound _ hκpos.le fun v => ?_
      have : ((DH (μ, a₀ + μ • α₀ + ζ)).comp (ContinuousLinearMap.inr ℝ ℝ P) - M₀) v =
          (DH (μ, a₀ + μ • α₀ + ζ) - DH (0, a₀)) ((0 : ℝ), v) := by
        simp [hM₀]
      rw [this]
      calc ‖(DH (μ, a₀ + μ • α₀ + ζ) - DH (0, a₀)) ((0 : ℝ), v)‖
          ≤ ‖DH (μ, a₀ + μ • α₀ + ζ) - DH (0, a₀)‖ * ‖((0 : ℝ), v)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ κ * ‖v‖ := by
            rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg v)]
            exact mul_le_mul_of_nonneg_right hclose.le (norm_nonneg v)
    have hΦlip : ∀ ζ ∈ Bμ, ∀ ζ' ∈ Bμ, ‖Φ ζ' - Φ ζ‖ ≤ κ * ‖ζ' - ζ‖ := fun ζ hζ ζ' hζ' =>
      hBconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hΦd hΦb hζ hζ'
    -- `T_μ` is a `1/2`-contraction on `Bμ`
    have hTlip : ∀ ζ ∈ Bμ, ∀ ζ' ∈ Bμ, ‖Tμ ζ' - Tμ ζ‖ ≤ 1 / 2 * ‖ζ' - ζ‖ := by
      intro ζ hζ ζ' hζ'
      have hζZ := ((hmemB ζ).1 hζ).1
      have hζ'Z := ((hmemB ζ').1 hζ').1
      have hid : Tμ ζ' - Tμ ζ = -(S (Φ ζ' - Φ ζ)) := by
        simp only [hTμ, hΦ, map_sub]
        rw [hSM _ hζ'Z, hSM _ hζZ]
        abel
      rw [hid, norm_neg]
      calc ‖S (Φ ζ' - Φ ζ)‖ ≤ ‖S‖ * ‖Φ ζ' - Φ ζ‖ := S.le_opNorm _
        _ ≤ ‖S‖ * (κ * ‖ζ' - ζ‖) := by gcongr; exact hΦlip ζ hζ ζ' hζ'
        _ = (‖S‖ * κ) * ‖ζ' - ζ‖ := by ring
        _ ≤ 1 / 2 * ‖ζ' - ζ‖ := by gcongr
    have hT0 : ‖Tμ 0‖ ≤ c / 2 * μ := by
      simp only [hTμ, add_zero, zero_sub, norm_neg]
      calc ‖S (H (μ, a₀ + μ • α₀))‖ ≤ ‖S‖ * ‖H (μ, a₀ + μ • α₀)‖ := S.le_opNorm _
        _ ≤ ‖S‖ * (c * κ * μ) := by
            gcongr; exact hsmall μ ⟨hμ0, hμ.2.trans_le hμ₀₂⟩
        _ = (‖S‖ * κ) * (c * μ) := by ring
        _ ≤ 1 / 2 * (c * μ) := by gcongr
        _ = c / 2 * μ := by ring
    have hTmaps : MapsTo Tμ Bμ Bμ := by
      intro ζ hζ
      have hζ' := (hmemB ζ).1 hζ
      refine (hmemB _).2 ⟨Z.sub_mem hζ'.1 (hSmem _), ?_⟩
      calc ‖Tμ ζ‖ ≤ ‖Tμ ζ - Tμ 0‖ + ‖Tμ 0‖ := norm_le_norm_sub_add _ _
        _ ≤ 1 / 2 * ‖ζ - 0‖ + c / 2 * μ := add_le_add (hTlip 0 h0B ζ hζ) hT0
        _ ≤ 1 / 2 * (c * μ) + c / 2 * μ := by rw [sub_zero]; gcongr; exact hζ'.2
        _ = c * μ := by ring
    have hcontr : ContractingWith (1 / 2 : NNReal) (hTmaps.restrict Tμ Bμ Bμ) := by
      refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun ζ ζ' => ?_⟩
      rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
      have := hTlip ζ'.1 ζ'.2 ζ.1 ζ.2
      simpa using this
    obtain ⟨ζ, hζB, hζfix, -⟩ :=
      ContractingWith.exists_fixedPoint' hBc.isComplete hTmaps hcontr h0B (edist_ne_top _ _)
    have hζ' := (hmemB ζ).1 hζB
    refine ⟨ζ, hζ'.1, hζ'.2, ?_, ?_⟩
    · have h1 : ‖ζ‖ ≤ ‖Tμ ζ - Tμ 0‖ + ‖Tμ 0‖ := by
        rw [show Tμ ζ = ζ from hζfix]; exact norm_le_norm_sub_add _ _
      have h2 := hTlip 0 h0B ζ hζB
      rw [sub_zero] at h2
      have h3 : ‖Tμ 0‖ = ‖S (H (μ, a₀ + μ • α₀))‖ := by
        simp [hTμ]
      rw [h3] at h1
      linarith
    · have := hζfix
      simp only [IsFixedPt, hTμ] at this
      have h1 : S (H (μ, a₀ + μ • α₀ + ζ)) = 0 := by
        have := congrArg (fun x => ζ - x) this
        simpa using this
      have := congrArg M₀ h1
      rwa [hMS, map_zero] at this
  -- the curve
  choose! ζf hζZ hζc hζo hζH using hfix
  set a : ℝ → P := fun μ => a₀ + μ • α₀ + (if μ ∈ Ioo (0 : ℝ) μ₀ then ζf μ else 0) with ha
  refine ⟨μ₀, hμ₀pos, a, by simp [ha], ?_, fun μ hμ => ?_⟩
  · rw [hasDerivWithinAt_iff_isLittleO]
    have hbig : (fun μ => a μ - a 0 - (μ - 0) • α₀) =O[𝓝[Ici 0] 0]
        fun μ => S (H (μ, a₀ + μ • α₀)) := by
      refine IsBigO.of_bound 2 ?_
      have hev : ∀ᶠ μ in 𝓝[Ici 0] 0, μ ∈ Ico 0 μ₀ := Ico_mem_nhdsGE hμ₀pos
      filter_upwards [hev] with μ hμ
      have heq : a μ - a 0 - (μ - 0) • α₀ = if μ ∈ Ioo (0 : ℝ) μ₀ then ζf μ else 0 := by
        have h0' : a 0 = a₀ := by simp [ha]
        rw [h0', sub_zero]
        change a₀ + μ • α₀ + (if μ ∈ Ioo (0 : ℝ) μ₀ then ζf μ else 0) - a₀ - μ • α₀ = _
        abel
      rw [heq]
      by_cases hμ' : μ ∈ Ioo (0 : ℝ) μ₀
      · rw [if_pos hμ']; exact hζo μ hμ'
      · rw [if_neg hμ', norm_zero]; positivity
    have hsmall' : (fun μ => S (H (μ, a₀ + μ • α₀))) =o[𝓝[Ici 0] 0] fun μ => μ - 0 := by
      have := (S.isBigO_comp (fun μ : ℝ => H (μ, a₀ + μ • α₀)) (𝓝[Ici 0] 0)).trans_isLittleO hlo
      simpa using this
    exact hbig.trans_isLittleO hsmall'
  · rcases hμ.1.lt_or_eq with hμ' | hμ'
    · have hμI : μ ∈ Ioo (0 : ℝ) μ₀ := ⟨hμ', hμ.2⟩
      have haμ : a μ = a₀ + μ • α₀ + ζf μ := by
        change a₀ + μ • α₀ + (if μ ∈ Ioo (0 : ℝ) μ₀ then ζf μ else 0) = _
        rw [if_pos hμI]
      rw [haμ]
      exact ⟨hmemD μ hμ.1 (hμ.2.le.trans hμ₀t) (hμ₀ε μ hμ.1 hμ.2) _ (hζc μ hμI), hζH μ hμI⟩
    · subst hμ'
      have ha0 : a 0 = a₀ := by simp [ha]
      rw [ha0]
      exact ⟨h0D, hH0⟩

end Curve

/-! ### One-sided derivatives -/

/-- `μ ↦ μ k(μ)` has the right derivative `k(0)` at `0` when `k` is continuous at `0` from the
right. -/
theorem hasDerivWithinAt_smul_right_of_continuousWithinAt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {k : ℝ → F} (hk : ContinuousWithinAt k (Ici 0) 0) :
    HasDerivWithinAt (fun μ : ℝ => μ • k μ) (k 0) (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  have hev := Metric.continuousWithinAt_iff.1 hk c hc
  obtain ⟨δ, hδ, hδ'⟩ := hev
  have hev' : ∀ᶠ μ in 𝓝[Ici (0 : ℝ)] (0 : ℝ), dist μ 0 < δ ∧ μ ∈ Ici (0 : ℝ) := by
    refine Filter.Eventually.and ?_ self_mem_nhdsWithin
    exact mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds 0 hδ)
  filter_upwards [hev'] with μ ⟨hμδ, hμ⟩
  have h1 := hδ' hμ hμδ
  rw [dist_eq_norm] at h1
  simp only [zero_smul, sub_zero]
  calc ‖μ • k μ - μ • k 0‖ = ‖μ‖ * ‖k μ - k 0‖ := by rw [← smul_sub, norm_smul]
    _ ≤ ‖μ‖ * c := mul_le_mul_of_nonneg_left h1.le (norm_nonneg _)
    _ = c * ‖μ‖ := mul_comm _ _

/-- Uniqueness of right derivatives at `0`. -/
theorem eq_of_hasDerivWithinAt_Ici {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {a b : F} (ha : HasDerivWithinAt f a (Ici 0) 0)
    (hb : HasDerivWithinAt f b (Ici 0) 0) : a = b :=
  (uniqueDiffWithinAt_Ici 0).eq_deriv _ ha hb

/-! ### Zeros of the perturbed filler lie in the retract -/

namespace StrongRetr

variable {E F : ScBanach} {U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-- **Zeros of `g + μ ρ(r(·)) λ` lie in `O`** (condition (2) of Definition 3.4): if
`g(u) + μ ρ(r(u)) λ = 0` then `ρ(r(u)) g(u) = −μ ρ(r(u))² λ = −μ ρ(r(u)) λ = g(u)`, so `u ∈ O`
whenever condition (2) holds at `u`. -/
theorem mem_O_of_perturbed_zero (hR : IsStrongBundleRetraction U R) {g : E 0 → F 0} {u : E 0}
    (hu : u ∈ U) (h2 : g u = ρ R (r R u) (g u) → u ∈ r R '' U) {μ : ℝ} {k : F 0}
    (hzero : g u + μ • ρ R (r R u) k = 0) : u ∈ r R '' U := by
  refine h2 ?_
  have hlin := ρ_isLinear hR (r_mem hR hu)
  have hg : g u = -(μ • ρ R (r R u) k) := eq_neg_of_add_eq_zero_left hzero
  rw [hg, hlin.map_neg, hlin.map_smul, ρ_ρ hR ⟨u, hu, rfl⟩]

end StrongRetr

end Polyfold
