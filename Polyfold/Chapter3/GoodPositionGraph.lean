import Polyfold.Chapter3.GoodPosition

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, Appendix 3.8.1,
Lemma 3.70: the degeneracy index along the graph of a `C^1`-map over `N ∩ C` with vanishing
derivative at `0`.

# The degeneracy index on the graph of `τ`

## The text, paraphrased

(Lemma 3.70) Let `N ⊆ E = ℝⁿ ⊕ W` be in good position to `C = [0,∞)ⁿ ⊕ W` with good complement
`Y`, and `τ : N ∩ C → Y₁` a `C^1`-map with `τ(0) = 0`, `Dτ(0) = 0`.  Then
`d_{N ∩ C}(v) = d_C(v + τ(v))` for all `v ∈ N ∩ C ∖ N ∩ W` close to `0`.  *Proof.*  `|τ(v)| ≤ γ|v|`
near `0`, so `v + τ(v) ∈ C`.  If `dim N = 1`, `N = ℝ·e` with all coordinates of `e` positive, and
`v_j + τ_j(v) > 0` follows from `τ(v) = o(|v|)`.  If `dim N ≥ 2`, in the basis
`e^j = (a^j, b^j, w^j)` of the complement `Ñ` of `N ∩ W` (with `a^j` the standard basis of `ℝᵐ`
and `b^j_i > 0`), `τ_j(v) = 0` for `j ≤ m` (Lemma 3.65), and for `j > m` the function
`g_j(v') = (T⁻¹v' + τ(T⁻¹v'))_j ≥ 0` on `C' = [0,∞)ᵐ ⊕ ℝᵏ⁻ᵐ` has `∂_i g_j = b_{ij} + Dτ_j(v)e_i > 0`
near `0` for a direction `e_i` with `v'_i > 0`, so `g_j(v') = 0` would force `g_j < 0` just before
`v'` along `e_i`.

## What is formalized

* `Polyfold.exists_rayDecomp`: the **ray decomposition** of `N ∩ C` read off the normal form of
  Proposition 3.22 (`Polyfold.QuadrantNormalForm`): finitely many nonzero `u_i ∈ N ∩ C` such that
  every `v ∈ N ∩ C ∖ N ∩ W` has `v − s u_i ∈ N ∩ C` for some `i` and `s > 0` with `s|u_i| ≤ c|v|`
  (the text's basis `e^j` of `Ñ`; it covers `dim N = 1` as well).
* `Polyfold.exists_lipschitz_small` (`Dτ(0) = 0` makes `τ` `η`-Lipschitz near `0` for every
  `η > 0`), `Polyfold.lemma_3_70_core` (**Lemma 3.70 in coordinates**: `v + τ(v) ∈ C`, and for
  `v ∉ N ∩ W` the vanishing coordinates of `v + τ(v)` are those of `v`), `Polyfold.lemma_3_70`
  (**Lemma 3.70** in the model `ℝⁿ ⊕ W`, with Proposition 3.69 (1) for `d_{N ∩ C}(v) = d_C(v)`).

## What the text leaves implicit, and the choices made (the findings)

* **The directional-derivative argument is replaced by a mean value estimate**: for `j ∉ Σ`,
  `(v + τ(v))_j = (w + τ(w))_j + s·(u_i)_j + (τ(v) − τ(w))_j` with `w = v − s u_i ∈ N ∩ C`, where
  the first term is `≥ 0` (`w + τ(w) ∈ C`), the second is `s·b` with `b = (u_i)_j > 0`, and the
  third is bounded by `s‖ℓ_j‖‖u_i‖η` with `η` small (`Dτ(0) = 0`); so `(v + τ(v))_j > 0`.  The
  margin `η` is a positive lower bound of finitely many positive numbers
  (`Polyfold.exists_pos_le_of_forall_pos`).  This is the text's argument (monotonicity of `g_j`
  along `e_i` from `v' − v'_i e_i`, where `g_j ≥ 0`) in integrated form; the two cases
  `dim N = 1`, `dim N ≥ 2` are unified by the ray decomposition.
* **The smallness of `τ` must hold on the whole segment `[v − s u_i, v]`**, which lies in
  `N ∩ C ∩ B(0, (1 + c)|v|)`: the radius of the lemma is `ρ/(1 + c)` where `ρ` is the radius on
  which `‖Dτ‖ ≤ η`; the text says "close to `0`".
* **"`τ : N ∩ C → Y₁`"**: the sc-level of the values plays no role; `τ` is a `C^1`-map into `Y`
  (`ContDiffOn ℝ 1 τ (N ∩ C)` with `fderivWithin` at `0` equal to `0`, `N ∩ C` convex with
  nonempty interior so that the derivative is unique).
* The coordinate functionals are taken continuous (`ℓ : Fin n → V →L[ℝ] ℝ`) since the estimate
  `|ℓ_j(τ(v) − τ(w))| ≤ ‖ℓ_j‖‖τ(v) − τ(w)‖` is needed; in the model they are the coordinates.
-/

open Set Filter Topology Function Module

set_option linter.unusedSectionVars false

noncomputable section

namespace Polyfold

/-- A finite family of positive reals has a positive lower bound. -/
lemma exists_pos_le_of_forall_pos {α : Type*} (s : Finset α) (F : α → ℝ)
    (hF : ∀ a ∈ s, 0 < F a) : ∃ m > 0, ∀ a ∈ s, m ≤ F a := by
  classical
  rcases s.eq_empty_or_nonempty with hs | hs
  · exact ⟨1, one_pos, fun a ha => by rw [hs] at ha; exact absurd ha (Finset.notMem_empty a)⟩
  · obtain ⟨a₀, ha₀s, ha₀⟩ := Finset.exists_min_image s F hs
    exact ⟨F a₀, hF a₀ ha₀s, fun a ha => ha₀ a ha⟩

section Core

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
variable (ℓ : Fin n → V →ₗ[ℝ] ℝ) (N : Submodule ℝ V)

lemma quadCone_convex : Convex ℝ (quadCone ℓ N) := by
  intro x hx y hy s t hs ht _
  exact add_mem_quadCone ℓ N (smul_mem_quadCone ℓ N hx hs) (smul_mem_quadCone ℓ N hy ht)

/-- **The ray decomposition of the cone `N ∩ C`** (the text's basis `e^j = (a^j, b^j, w^j)` of
`Ñ`, p. 126): finitely many nonzero `u_i ∈ N ∩ C` such that every `v ∈ N ∩ C ∖ N ∩ W` has some
`v − s u_i ∈ N ∩ C` with `s > 0` and `s|u_i| ≤ c|v|`. -/
theorem exists_rayDecomp [FiniteDimensional ℝ N] (hNF : QuadrantNormalForm ℓ N) :
    ∃ (m : ℕ) (u : Fin m → N) (c : ℝ), 0 ≤ c ∧
      (∀ i, u i ∈ quadCone ℓ N ∧ u i ≠ 0) ∧
      ∀ v ∈ quadCone ℓ N, v ∉ nullSpace ℓ N →
        ∃ (i : Fin m) (s : ℝ), 0 < s ∧ s * ‖u i‖ ≤ c * ‖v‖ ∧ v - s • u i ∈ quadCone ℓ N := by
  classical
  obtain ⟨k, N₀, e, h1, -, h3, -⟩ := hNF
  let eL : N ≃L[ℝ] (Fin k → ℝ) × N₀ := e.toContinuousLinearEquiv
  have heL : ∀ x, eL x = e x := fun x => rfl
  set u : Fin k → N := fun j => e.symm (Pi.single j 1, 0) with hu
  have heu : ∀ j, e (u j) = (Pi.single j 1, 0) := fun j => e.apply_symm_apply _
  refine ⟨k, u, ‖(eL : N →L[ℝ] (Fin k → ℝ) × N₀)‖ * ∑ j, ‖u j‖, by positivity,
    fun j => ⟨?_, ?_⟩, ?_⟩
  · rw [h1, heu]
    intro j'
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · intro h
    have := heu j
    rw [h, map_zero] at this
    have := congrFun (congrArg Prod.fst this) j
    simp at this
  · intro v hv hvW
    have hne : (e v).1 ≠ 0 := fun h => hvW ((h3 v).1 h)
    obtain ⟨j, hj⟩ : ∃ j, (e v).1 j ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    have hpos : 0 < (e v).1 j := lt_of_le_of_ne ((h1 v).1 hv j) (Ne.symm hj)
    refine ⟨j, (e v).1 j, hpos, ?_, ?_⟩
    · have h1' : (e v).1 j ≤ ‖e v‖ :=
        le_trans (le_abs_self _) ((norm_le_pi_norm (e v).1 j).trans (norm_fst_le (e v)))
      have h2' : ‖e v‖ ≤ ‖(eL : N →L[ℝ] (Fin k → ℝ) × N₀)‖ * ‖v‖ := by
        rw [← heL]; exact (eL : N →L[ℝ] (Fin k → ℝ) × N₀).le_opNorm v
      have h3' : ‖u j‖ ≤ ∑ j', ‖u j'‖ :=
        Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
      calc (e v).1 j * ‖u j‖ ≤ (‖(eL : N →L[ℝ] (Fin k → ℝ) × N₀)‖ * ‖v‖) * ∑ j', ‖u j'‖ :=
            mul_le_mul (h1'.trans h2') h3' (norm_nonneg _) (by positivity)
        _ = (‖(eL : N →L[ℝ] (Fin k → ℝ) × N₀)‖ * ∑ j', ‖u j'‖) * ‖v‖ := by ring
    · rw [h1]
      intro j'
      rw [map_sub, map_smul, heu]
      simp only [Prod.fst_sub, Prod.smul_fst, Pi.sub_apply, Pi.smul_apply, Pi.single_apply,
        smul_eq_mul]
      split_ifs with hjj
      · subst hjj; simp
      · simp only [mul_zero, sub_zero]; exact (h1 v).1 hv j'

end Core

/-! ### Lemma 3.70 -/

section Graph

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
variable (ℓ : Fin n → V →L[ℝ] ℝ) (N : Submodule ℝ V) [FiniteDimensional ℝ N]

/-- The functionals as linear maps, for the API of `GoodPosition.lean`. -/
abbrev ℓlin : Fin n → V →ₗ[ℝ] ℝ := fun i => (ℓ i : V →ₗ[ℝ] ℝ)

/-- The smallness of `τ` given by `Dτ(0) = 0`: for every `η > 0`, `τ` is `η`-Lipschitz on
`N ∩ C` near `0`. -/
lemma exists_lipschitz_small (hint : (interior (quadCone (ℓlin ℓ) N)).Nonempty) (τ : N → V)
    (hτ : ContDiffOn ℝ 1 τ (quadCone (ℓlin ℓ) N))
    (hDτ0 : fderivWithin ℝ τ (quadCone (ℓlin ℓ) N) 0 = 0) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ v ∈ quadCone (ℓlin ℓ) N, ∀ w ∈ quadCone (ℓlin ℓ) N, ‖v‖ < ρ → ‖w‖ < ρ →
      ‖τ v - τ w‖ ≤ η * ‖v - w‖ := by
  have hUD : UniqueDiffOn ℝ (quadCone (ℓlin ℓ) N) :=
    uniqueDiffOn_convex (quadCone_convex _ _) hint
  have hcont := (hτ.fderivWithin hUD (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuousOn 0
    (zero_mem_quadCone _ _)
  rw [ContinuousWithinAt, hDτ0, Metric.tendsto_nhdsWithin_nhds] at hcont
  obtain ⟨ρ, hρ, hρ'⟩ := hcont η hη
  refine ⟨ρ, hρ, fun v hv w hw hvρ hwρ => ?_⟩
  have hconv : Convex ℝ (quadCone (ℓlin ℓ) N ∩ Metric.ball 0 ρ) :=
    (quadCone_convex _ _).inter (convex_ball 0 ρ)
  refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun z => fderivWithin ℝ τ (quadCone (ℓlin ℓ) N) z)
    (fun z hz => ((hτ.differentiableOn one_ne_zero) z hz.1).hasFDerivWithinAt.mono
      inter_subset_left)
    (fun z hz => ?_) hconv ⟨hw, by rwa [Metric.mem_ball, dist_zero_right]⟩
    ⟨hv, by rwa [Metric.mem_ball, dist_zero_right]⟩
  have hz2 : dist z 0 < ρ := Metric.mem_ball.1 hz.2
  have := hρ' hz.1 hz2
  rw [dist_zero_right] at this
  exact this.le

/-- **Lemma 3.70, in coordinates.**  `N` in good position (complement `P`, constant `ε`),
`τ : N → V` with values in `P`, of class `C^1` on `N ∩ C` with `τ(0) = 0`, `Dτ(0) = 0`.  Then for
`v ∈ N ∩ C` near `0`: `v + τ(v) ∈ C`, and if `v ∉ N ∩ W` the vanishing coordinates of `v + τ(v)` are those of
`v` (so `d_{N ∩ C}(v) = d_C(v + τ(v))`). -/
theorem lemma_3_70_core (P : Submodule ℝ V) (hNP : IsCompl N P) {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ x ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖x‖ →
      ((∀ i, 0 ≤ ℓ i x) ↔ ∀ i, 0 ≤ ℓ i (x + p)))
    (hℓ : ∀ (s : Finset (Fin n)) (k : Fin n → ℝ), ∃ v : V, ∀ i ∈ s, ℓ i v = k i)
    (hint : (interior (quadCone (ℓlin ℓ) N)).Nonempty) (τ : N → V) (hτP : ∀ v, τ v ∈ P)
    (hτ : ContDiffOn ℝ 1 τ (quadCone (ℓlin ℓ) N)) (hτ0 : τ 0 = 0)
    (hDτ0 : fderivWithin ℝ τ (quadCone (ℓlin ℓ) N) 0 = 0) :
    ∃ ρ > 0, ∀ v ∈ quadCone (ℓlin ℓ) N, ‖v‖ < ρ →
      (∀ i, 0 ≤ ℓ i ((v : V) + τ v)) ∧
      (v ∉ nullSpace (ℓlin ℓ) N → ∀ i, (ℓ i (v : V) = 0 ↔ ℓ i ((v : V) + τ v) = 0)) := by
  classical
  set D := quadCone (ℓlin ℓ) N with hD
  have hNF : QuadrantNormalForm (ℓlin ℓ) N :=
    exists_quadrantNormalForm (ℓlin ℓ) N P hNP hε hgood hℓ hint
  obtain ⟨m, u, c, hc, hu, hdec⟩ := exists_rayDecomp (ℓlin ℓ) N hNF
  -- the positivity margin `η`
  set F : Fin m × Fin n → ℝ := fun p =>
    if p.2 ∈ vanIdx (ℓlin ℓ) N then 1 else ℓ p.2 (u p.1) / (‖ℓ p.2‖ * ‖u p.1‖ + 1) with hF
  have hFpos : ∀ p, 0 < F p := by
    intro p
    simp only [hF]
    split_ifs with hp
    · exact one_pos
    · exact div_pos (pos_of_not_mem_vanIdx (ℓlin ℓ) N (hu p.1).1 (hu p.1).2 hp) (by positivity)
  obtain ⟨η, hη, hηF⟩ := exists_pos_le_of_forall_pos Finset.univ F fun p _ => hFpos p
  have hηb : ∀ (i : Fin m) (j : Fin n), j ∉ vanIdx (ℓlin ℓ) N →
      min η ε * (‖ℓ j‖ * ‖u i‖) < ℓ j (u i) := by
    intro i j hj
    have h1 := hηF (i, j) (Finset.mem_univ _)
    simp only [hF, if_neg hj] at h1
    have hb : 0 < ℓ j (u i) := pos_of_not_mem_vanIdx (ℓlin ℓ) N (hu i).1 (hu i).2 hj
    have hX : 0 ≤ ‖ℓ j‖ * ‖u i‖ := by positivity
    calc min η ε * (‖ℓ j‖ * ‖u i‖) ≤ η * (‖ℓ j‖ * ‖u i‖) := by gcongr; exact min_le_left _ _
      _ ≤ ℓ j (u i) / (‖ℓ j‖ * ‖u i‖ + 1) * (‖ℓ j‖ * ‖u i‖) := by gcongr
      _ < ℓ j (u i) := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
  obtain ⟨ρ, hρ, hlip⟩ := exists_lipschitz_small ℓ N hint τ hτ hDτ0 (lt_min hη hε)
  -- (a) `z + τ(z) ∈ C` for `z ∈ N ∩ C`, `|z| < ρ`
  have hmemC : ∀ z ∈ D, ‖z‖ < ρ → ∀ i, 0 ≤ ℓ i ((z : V) + τ z) := by
    intro z hz hzρ
    have hb : ‖τ z‖ ≤ ε * ‖z‖ := by
      have := hlip z hz 0 (zero_mem_quadCone _ _) hzρ (by simpa using hρ)
      rw [hτ0, sub_zero, sub_zero] at this
      calc ‖τ z‖ ≤ min η ε * ‖z‖ := this
        _ ≤ ε * ‖z‖ := by gcongr; exact min_le_right _ _
    exact (hgood z z.2 (τ z) (hτP z) hb).1 hz
  refine ⟨ρ / (1 + c), by positivity, fun v hv hvρ => ⟨hmemC v hv ?_, fun hvW i => ?_⟩⟩
  · calc ‖v‖ < ρ / (1 + c) := hvρ
      _ ≤ ρ := by rw [div_le_iff₀ (by positivity)]; nlinarith
  by_cases hi : i ∈ vanIdx (ℓlin ℓ) N
  · -- `ℓ_i(τ v) = 0` by Lemma 3.65
    have := lemma_3_65 (ℓlin ℓ) N P hε hgood (hτP v) hi
    change ℓ i (τ v) = 0 at this
    rw [map_add, this, add_zero]
  · -- both sides positive
    have hv0 : v ≠ 0 := fun h => hvW (by rw [h]; exact Submodule.zero_mem _)
    have hpos1 : 0 < ℓ i (v : V) := pos_of_not_mem_vanIdx (ℓlin ℓ) N hv hv0 hi
    obtain ⟨i₀, s, hs, hsb, hwD⟩ := hdec v hv hvW
    have hwρ : ‖v - s • u i₀‖ < ρ := by
      calc ‖v - s • u i₀‖ ≤ ‖v‖ + ‖s • u i₀‖ := norm_sub_le _ _
        _ = ‖v‖ + s * ‖u i₀‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]
        _ ≤ ‖v‖ + c * ‖v‖ := by linarith
        _ = (1 + c) * ‖v‖ := by ring
        _ < (1 + c) * (ρ / (1 + c)) := by gcongr
        _ = ρ := by field_simp
    have hvρ' : ‖v‖ < ρ := by
      calc ‖v‖ < ρ / (1 + c) := hvρ
        _ ≤ ρ := by rw [div_le_iff₀ (by positivity)]; nlinarith
    have hwC := hmemC _ hwD hwρ i
    have hlipvw := hlip v hv _ hwD hvρ' hwρ
    have hdiff : ‖v - (v - s • u i₀)‖ = s * ‖u i₀‖ := by
      rw [sub_sub_cancel, norm_smul, Real.norm_of_nonneg hs.le]
    rw [hdiff] at hlipvw
    have hb := hηb i₀ i hi
    -- `ℓ_i(v + τ v) = ℓ_i(w + τ w) + s ℓ_i(u) + ℓ_i(τ v − τ w)`
    have hsplit : ℓ i ((v : V) + τ v) = ℓ i (((v - s • u i₀ : N) : V) + τ (v - s • u i₀)) +
        s * ℓ i (u i₀) + ℓ i (τ v - τ (v - s • u i₀)) := by
      simp only [map_add, map_sub, Submodule.coe_sub, Submodule.coe_smul, map_smul, smul_eq_mul]
      ring
    have hbound : |ℓ i (τ v - τ (v - s • u i₀))| ≤ ‖ℓ i‖ * (min η ε * (s * ‖u i₀‖)) := by
      rw [← Real.norm_eq_abs]
      calc ‖ℓ i (τ v - τ (v - s • u i₀))‖ ≤ ‖ℓ i‖ * ‖τ v - τ (v - s • u i₀)‖ :=
            (ℓ i).le_opNorm _
        _ ≤ ‖ℓ i‖ * (min η ε * (s * ‖u i₀‖)) := by gcongr
    have hpos2 : 0 < ℓ i ((v : V) + τ v) := by
      rw [hsplit]
      have := neg_abs_le (ℓ i (τ v - τ (v - s • u i₀)))
      have hkey : ‖ℓ i‖ * (min η ε * (s * ‖u i₀‖)) < s * ℓ i (u i₀) := by
        have : ‖ℓ i‖ * (min η ε * (s * ‖u i₀‖)) = s * (min η ε * (‖ℓ i‖ * ‖u i₀‖)) := by ring
        rw [this]
        exact mul_lt_mul_of_pos_left hb hs
      linarith
    exact ⟨fun h => absurd h hpos1.ne', fun h => absurd h hpos2.ne'⟩

end Graph

/-! ### Lemma 3.70 in the model `ℝⁿ ⊕ W` -/

section Model

variable {n : ℕ} {W : ScBanach}

/-- The coordinate functionals of the model `ℝⁿ ⊕ W`, as continuous linear maps. -/
def coordCLM (i : Fin n) : ((ScBanach.const (Fin n → ℝ)).prod W) 0 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (W 0))

@[simp] lemma coordCLM_apply (i : Fin n) (x : ((ScBanach.const (Fin n → ℝ)).prod W) 0) :
    coordCLM (W := W) i x = x.1 i := rfl

lemma quadCone_coordCLM (N : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)) :
    quadCone (ℓlin (coordCLM (W := W))) N = (Subtype.val ⁻¹' quadrant n W 0 : Set N) := by
  ext v; exact Iff.rfl

/-- **Lemma 3.70**: `N` in good position to `C = [0,∞)ⁿ ⊕ W` with good complement `Y`, and
`τ : N ∩ C → Y` of class `C^1` with `τ(0) = 0`, `Dτ(0) = 0`.  Then for `v ∈ N ∩ C` close to `0`,
`v + τ(v) ∈ C`, and `d_{N ∩ C}(v) = d_C(v + τ(v))` if `v ∉ N ∩ W`.  (The text's `τ : N ∩ C → Y₁`:
the level plays no role in the degeneracy index.) -/
theorem lemma_3_70 {N : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)}
    [FiniteDimensional ℝ N] (hN : IsInGoodPosition _ (quadrant n W 0) N)
    {Y : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)}
    (hY : IsGoodComplement _ (quadrant n W 0) N Y)
    (τ : N → ((ScBanach.const (Fin n → ℝ)).prod W) 0) (hτY : ∀ v, τ v ∈ Y)
    (hτ : ContDiffOn ℝ 1 τ (Subtype.val ⁻¹' quadrant n W 0)) (hτ0 : τ 0 = 0)
    (hDτ0 : fderivWithin ℝ τ (Subtype.val ⁻¹' quadrant n W 0) 0 = 0) :
    ∃ ρ > 0, ∀ v : N, (v : ((ScBanach.const (Fin n → ℝ)).prod W) 0) ∈ quadrant n W 0 → ‖v‖ < ρ →
      ((v : ((ScBanach.const (Fin n → ℝ)).prod W) 0) + τ v ∈ quadrant n W 0) ∧
      ((v : (Fin n → ℝ) × W 0).1 ≠ 0 →
        degIndex (ScBanach.const N) (Subtype.val ⁻¹' quadrant n W 0) v =
          degIndex _ (quadrant n W 0) ((v : ((ScBanach.const (Fin n → ℝ)).prod W) 0) + τ v)) := by
  classical
  have hDeq := quadCone_coordCLM (W := W) N
  obtain ⟨ε, hε, hgood⟩ := hY.exists_eps
  have hℓ : ∀ (s : Finset (Fin n)) (k : Fin n → ℝ),
      ∃ v : ((ScBanach.const (Fin n → ℝ)).prod W) 0, ∀ i ∈ s, coordCLM (W := W) i v = k i :=
    fun s k => ⟨(k, 0), fun i _ => rfl⟩
  rw [← hDeq] at hτ hDτ0
  have hint : (interior (quadCone (ℓlin (coordCLM (W := W))) N)).Nonempty := by
    rw [hDeq]; exact hN.interior_nonempty
  obtain ⟨ρ, hρ, hmain⟩ := lemma_3_70_core (coordCLM (W := W)) N Y hY.isCompl hε hgood hℓ hint τ
    hτY hτ hτ0 hDτ0
  refine ⟨ρ, hρ, fun v hv hvρ => ?_⟩
  have hvD : v ∈ quadCone (ℓlin (coordCLM (W := W))) N := by rw [hDeq]; exact hv
  obtain ⟨hmem', hiff⟩ := hmain v hvD hvρ
  have hmem : (v : ((ScBanach.const (Fin n → ℝ)).prod W) 0) + τ v ∈ quadrant n W 0 := hmem'
  refine ⟨hmem, fun hv1 => ?_⟩
  have hvW : v ∉ nullSpace (ℓlin (coordCLM (W := W))) N := fun h => by
    rw [mem_nullSpace] at h
    exact hv1 (funext fun i => h i)
  rw [(proposition_3_69 hN hv).1 hv1, degIndex_quadrant hv, degIndex_quadrant hmem]
  change (Finset.univ.filter fun i => (v : (Fin n → ℝ) × W 0).1 i = 0).card =
    (Finset.univ.filter fun i => ((v : (Fin n → ℝ) × W 0) + τ v).1 i = 0).card
  congr 1
  exact Finset.filter_congr fun i _ => hiff hvW i

end Model

end Polyfold
