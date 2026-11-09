import Polyfold.Chapter3.GoodPositionGraph
import Polyfold.Chapter2.Tame

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6 and
Appendix 3.8.3, **Lemma 3.6.9 (preprint 3.55)**: good position is preserved along the graph of a `C^1`-map
`τ : N ∩ C → Y` with `τ(0) = 0`, `Dτ(0) = 0`.

# Good position along a graph

## The text, paraphrased

(Lemma 3.6.9 (preprint 3.55)) Let `C ⊆ E` be a partial quadrant, `N ⊆ E` a finite-dimensional smooth subspace in
good position to `C` with good complement `Y`, `V ⊆ N ∩ C` a relatively open neighbourhood of `0`
and `τ : V → Y₁` of class `C^1` with `τ(0) = 0`, `Dτ(0) = 0`.  Then there is a relatively open
neighbourhood `V' ⊆ V` of `0` such that for `v ∈ V'`: (1) `v + τ(v) ∈ C₁`; (2) `Y` is a topological
complement of `N_v = {n + Dτ(v)n | n ∈ N}`; (3) there is `γ_v > 0` such that for `n ∈ N_v`, `y ∈ Y`
with `|y|₀ ≤ γ_v|n|₀`, `n ∈ C_x` iff `n + y ∈ C_x`, where `x = v + τ(v)`.

*Proof (Appendix 3.8.3).*  `|τ(v)|₀ ≤ γ|v|₀` near `0` gives (1) by the good-complement property
(67b).  (2) is linear algebra, using `Dτ(v)n ∈ Y`.  For (3), if `v ∈ N ∩ W` then `τ_i(v) = 0`
(both `v ± τ(v) ∈ C`) so `C_x = C`, and the estimate (69)
`|y + Dτ(v)n|₀ ≤ (γ_v + εγ_v + ε)|n|₀ ≤ γ|n|₀` (with `|Dτ(v)n|₀ ≤ ε|n|₀`, `ε < γ/2`) transfers the
statement from `N` to `N_v`; if `v ∉ N ∩ W`, in the normal form of Proposition 3.1.25 (preprint 3.22) the good
complement lies in `{0}^m ⊕ ℝ^{n−m} ⊕ W` (Lemma 3.8.8 (preprint 3.65)) and `x_j > 0` for `j > m` (Lemma 3.8.13 (preprint 3.70)), so
`C_x` depends only on coordinates on which `Y` vanishes.

## What is formalized

* `Polyfold.tangentConeAt_subset_of_subset_closed`, `Polyfold.fderivWithin_mem_of_mapsTo`:
  the derivative within `s` at a point of unique differentiability of a map with values in a
  **closed** subspace `P` takes its values in `P` (the text's "`Dτ(v)n ∈ Y`").
* `Polyfold.graphSpace N L = {n + L n | n ∈ N}` (the text's `N_v` for `L = Dτ(v)`).
* `Polyfold.lemma_3_6_9_core`: **Lemma 3.6.9 (preprint 3.55) in coordinates** (`ℓ_i` the coordinate functionals,
  `N ∩ C = {ℓ_i ≥ 0 on N}`, `C_x = {ℓ_i ≥ 0 for the `i` with `ℓ_i(x) = 0}`).
* `Polyfold.lemma_3_6_9_preprint`: **Lemma 3.6.9 (preprint 3.55)** in the model `E = ℝⁿ ⊕ W`, `C = [0,∞)ⁿ ⊕ W`: for `v ∈ N ∩ C`
  near `0`, `v + τ(v) ∈ C` and `Y` is a good complement (`IsGoodComplement`, which contains the
  algebraic splitting (2) and the constant (3)) of `N_v` with respect to the partial quadrant
  `C_{v + τ(v)}` (`partialQuadrantAtWith`).

## What the text leaves implicit, and the choices made (the findings)

* **Added hypothesis: `Y` is closed.**  The text's `Y = Y₀` is a topological complement, hence
  closed; `Dτ(v)n ∈ Y` (used in (2) and (3)) fails for a non-closed algebraic complement.  With
  `Y` closed, "topological complement" in (2) is the algebraic `IsCompl` together with the
  closedness of both summands (`N_v` is finite-dimensional).
* **The constant `γ_v` is uniform in `v`**: `γ_v = ε₀/4` with `ε₀ = min(ε, 1)` works for every
  `v` in the neighbourhood (on which `‖Dτ(v)‖ ≤ ε₀/4`), since
  `γ_v(1 + ε₀/4) + ε₀/4 ≤ ε₀`; the text chooses `γ_v` after `v`.
* **The case `v ∉ N ∩ W` needs no normal form**: if `ℓ_i(v) = 0` for some `i` then `i ∈ Σ` (the
  index set of Proposition 3.1.25 (preprint 3.22)), so `ℓ_i` vanishes on `Y` by Lemma 3.8.8 (preprint 3.65), and by Lemma 3.8.13 (preprint 3.70)
  `ℓ_i(x) = 0 ↔ ℓ_i(v) = 0`; hence `ℓ_i(h + y) = ℓ_i(h)` for all `i` with `ℓ_i(x) = 0`, and the
  equivalence in (3) holds for every `γ_v`.  The two cases `dim N = 1`, `dim N > 1` of the text are
  not needed.
* **"`τ : V → Y₁`" and "`v + τ(v) ∈ C₁`"**: the sc-level plays no role (as in Lemma 3.8.13 (preprint 3.70)); `τ` is a
  `C^1`-map into `Y ⊆ E₀` and (1) is `v + τ(v) ∈ C`.
-/

open Set Filter Topology Function Module

set_option linter.unusedSectionVars false

noncomputable section

namespace Polyfold

/-! ### Derivatives of maps into a closed subspace -/

section Tangent

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The tangent cone of a subset of a closed subspace `P` at a point of `P` lies in `P`. -/
lemma tangentConeAt_subset_of_subset_closed {P : Submodule ℝ V} (hP : IsClosed (P : Set V))
    {s : Set V} (hs : s ⊆ P) {x : V} (hx : x ∈ P) : tangentConeAt ℝ s x ⊆ P := by
  intro y hy
  obtain ⟨α, l, hl, c, d, -, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hy
  refine hP.mem_of_tendsto hcd ?_
  filter_upwards [hds] with k hk
  have h1 : d k ∈ P := by
    have := P.sub_mem (hs hk) hx
    rwa [add_sub_cancel_left] at this
  exact P.smul_mem _ h1

/-- The derivative within `s` at a point of unique differentiability of a map with values in a
closed subspace `P` takes its values in `P`. -/
lemma fderivWithin_mem_of_mapsTo {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {τ : W → V} {L : W →L[ℝ] V} {s : Set W} {v : W} (h : HasFDerivWithinAt τ L s v)
    (hs : UniqueDiffWithinAt ℝ s v) {P : Submodule ℝ V} (hP : IsClosed (P : Set V))
    (hτ : ∀ x ∈ s, τ x ∈ P) (hv : v ∈ s) (w : W) : L w ∈ P := by
  have h1 : tangentConeAt ℝ s v ⊆ (P.comap (L : W →ₗ[ℝ] V) : Set W) := fun y hy =>
    tangentConeAt_subset_of_subset_closed hP (image_subset_iff.2 hτ) (hτ v hv)
      (h.mapsTo_tangent_cone hy)
  have h2 : (Submodule.span ℝ (tangentConeAt ℝ s v) : Set W) ⊆ P.comap (L : W →ₗ[ℝ] V) :=
    Submodule.span_le.2 h1
  have h3 : IsClosed (P.comap (L : W →ₗ[ℝ] V) : Set W) := hP.preimage L.continuous
  have h4 := h3.closure_subset_iff.2 h2
  rw [hs.dense_tangentConeAt.closure_eq] at h4
  exact h4 (mem_univ w)

end Tangent

/-! ### Lemma 3.6.9 (preprint 3.55) in coordinates -/

section Core

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
variable (ℓ : Fin n → V →L[ℝ] ℝ) (N : Submodule ℝ V) [FiniteDimensional ℝ N]

/-- The subspace `N_L = {n + L n | n ∈ N}` (the text's `N_v` for `L = Dτ(v)`). -/
def graphSpace (L : N →L[ℝ] V) : Submodule ℝ V :=
  LinearMap.range (N.subtype + (L : N →ₗ[ℝ] V))

lemma mem_graphSpace {L : N →L[ℝ] V} {h : V} :
    h ∈ graphSpace N L ↔ ∃ w : N, (w : V) + L w = h := Iff.rfl

lemma add_mem_graphSpace (L : N →L[ℝ] V) (w : N) : (w : V) + L w ∈ graphSpace N L := ⟨w, rfl⟩

instance (L : N →L[ℝ] V) : FiniteDimensional ℝ (graphSpace N L) :=
  LinearMap.finiteDimensional_range _

/-- `N_L` is closed. -/
lemma graphSpace_isClosed (L : N →L[ℝ] V) : IsClosed (graphSpace N L : Set V) :=
  (graphSpace N L).closed_of_finiteDimensional

/-- `E = N_L ⊕ P` whenever `E = N ⊕ P` and `L` takes values in `P`. -/
lemma graphSpace_isCompl (P : Submodule ℝ V) (hNP : IsCompl N P) (L : N →L[ℝ] V)
    (hLP : ∀ w, L w ∈ P) : IsCompl (graphSpace N L) P := by
  refine IsCompl.of_eq ?_ ?_
  · rw [eq_bot_iff]
    rintro h ⟨⟨w, rfl⟩, hh⟩
    change (w : V) + L w ∈ P at hh
    have hw : (w : V) ∈ P := by
      have := P.sub_mem hh (hLP w)
      rwa [add_sub_cancel_right] at this
    have h0 : (w : V) ∈ N ⊓ P := ⟨w.2, hw⟩
    rw [hNP.inf_eq_bot, Submodule.mem_bot] at h0
    have hw0 : w = 0 := Subtype.ext h0
    show (w : V) + L w ∈ ⊥
    rw [Submodule.mem_bot, hw0, map_zero, Submodule.coe_zero, add_zero]
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ N ⊔ P := by rw [hNP.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    exact Submodule.mem_sup.2 ⟨a + L ⟨a, ha⟩, add_mem_graphSpace N L ⟨a, ha⟩, b - L ⟨a, ha⟩,
      P.sub_mem hb (hLP _), by abel⟩

/-- **Lemma 3.6.9 (preprint 3.55), in coordinates.**  `N` in good position (complement `P`, closed, constant `ε`),
`τ : N → V` with values in `P`, of class `C^1` on `N ∩ C` with `τ(0) = 0`, `Dτ(0) = 0`.  Then for
`v ∈ N ∩ C` near `0`, with `x = v + τ(v)` and `N_v = {n + Dτ(v)n}`: (1) `x ∈ C`; (2) `E = N_v ⊕ P`;
(3) there is `γ > 0` such that for `h ∈ N_v`, `y ∈ P` with `‖y‖ ≤ γ‖h‖`, `h ∈ C_x ↔ h + y ∈ C_x`,
where `C_x = {z | ℓ_i(z) ≥ 0 whenever ℓ_i(x) = 0}`. -/
theorem lemma_3_6_9_core (P : Submodule ℝ V) (hNP : IsCompl N P) (hPc : IsClosed (P : Set V))
    {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ x ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖x‖ →
      ((∀ i, 0 ≤ ℓ i x) ↔ ∀ i, 0 ≤ ℓ i (x + p)))
    (hℓ : ∀ (s : Finset (Fin n)) (k : Fin n → ℝ), ∃ v : V, ∀ i ∈ s, ℓ i v = k i)
    (hint : (interior (quadCone (ℓlin ℓ) N)).Nonempty) (τ : N → V) (hτP : ∀ v, τ v ∈ P)
    (hτ : ContDiffOn ℝ 1 τ (quadCone (ℓlin ℓ) N)) (hτ0 : τ 0 = 0)
    (hDτ0 : fderivWithin ℝ τ (quadCone (ℓlin ℓ) N) 0 = 0) :
    ∃ ρ > 0, ∀ v ∈ quadCone (ℓlin ℓ) N, ‖v‖ < ρ →
      (∀ i, 0 ≤ ℓ i ((v : V) + τ v)) ∧
      IsCompl (graphSpace N (fderivWithin ℝ τ (quadCone (ℓlin ℓ) N) v)) P ∧
      ∃ γ > 0, ∀ h ∈ graphSpace N (fderivWithin ℝ τ (quadCone (ℓlin ℓ) N) v), ∀ y ∈ P,
        ‖y‖ ≤ γ * ‖h‖ →
        ((∀ i, ℓ i ((v : V) + τ v) = 0 → 0 ≤ ℓ i h) ↔
          ∀ i, ℓ i ((v : V) + τ v) = 0 → 0 ≤ ℓ i (h + y)) := by
  classical
  set D := quadCone (ℓlin ℓ) N with hD
  have hUD : UniqueDiffOn ℝ D := uniqueDiffOn_convex (quadCone_convex _ _) hint
  -- the constant `ε₀ = min ε 1`
  set ε₀ := min ε 1 with hε₀def
  have hε₀ : 0 < ε₀ := lt_min hε one_pos
  have hε₀ε : ε₀ ≤ ε := min_le_left _ _
  have hε₀1 : ε₀ ≤ 1 := min_le_right _ _
  have hgood₀ : ∀ x ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε₀ * ‖x‖ →
      ((∀ i, 0 ≤ ℓ i x) ↔ ∀ i, 0 ≤ ℓ i (x + p)) := fun x hx p hp hle =>
    hgood x hx p hp (hle.trans (mul_le_mul_of_nonneg_right hε₀ε (norm_nonneg x)))
  -- Lemma 3.8.13 (preprint 3.70): `v + τ(v) ∈ C`, and the vanishing coordinates
  obtain ⟨ρ₁, hρ₁, h70⟩ := lemma_3_8_13_core ℓ N P hNP hε hgood hℓ hint τ hτP hτ hτ0 hDτ0
  -- `‖τ v‖ ≤ ε₀ ‖v‖` near `0`
  obtain ⟨ρ₂, hρ₂, hlip⟩ := exists_lipschitz_small ℓ N hint τ hτ hDτ0 hε₀
  -- `‖Dτ(v)‖ ≤ ε₀ / 4` near `0`
  have hcont := (hτ.fderivWithin hUD (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuousOn 0
    (zero_mem_quadCone _ _)
  rw [ContinuousWithinAt, hDτ0, Metric.tendsto_nhdsWithin_nhds] at hcont
  obtain ⟨ρ₃, hρ₃, hρ₃'⟩ := hcont (ε₀ / 4) (by positivity)
  refine ⟨min ρ₁ (min ρ₂ ρ₃), by positivity, fun v hv hvρ => ?_⟩
  have hvρ₁ : ‖v‖ < ρ₁ := lt_of_lt_of_le hvρ (min_le_left _ _)
  have hvρ₂ : ‖v‖ < ρ₂ := lt_of_lt_of_le hvρ ((min_le_right _ _).trans (min_le_left _ _))
  have hvρ₃ : ‖v‖ < ρ₃ := lt_of_lt_of_le hvρ ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hmem, hvan⟩ := h70 v hv hvρ₁
  set L := fderivWithin ℝ τ D v with hL
  have hLnorm : ‖L‖ ≤ ε₀ / 4 := by
    have := hρ₃' hv (by rwa [dist_zero_right])
    rw [dist_zero_right] at this
    exact this.le
  have hLP : ∀ w : N, L w ∈ P := fun w =>
    fderivWithin_mem_of_mapsTo ((hτ.differentiableOn one_ne_zero) v hv).hasFDerivWithinAt
      (hUD v hv) hPc (fun x _ => hτP x) hv w
  have hτv : ‖τ v‖ ≤ ε₀ * ‖v‖ := by
    have := hlip v hv 0 (zero_mem_quadCone _ _) hvρ₂ (by rwa [norm_zero])
    rwa [hτ0, sub_zero, sub_zero] at this
  refine ⟨hmem, graphSpace_isCompl N P hNP L hLP, ?_⟩
  by_cases hvW : v ∈ nullSpace (ℓlin ℓ) N
  · -- the case `v ∈ N ∩ W`: `C_x = C`
    have hv0 : ∀ i, ℓ i (v : V) = 0 := (mem_nullSpace _ _).1 hvW
    have hx0 : ∀ i, ℓ i ((v : V) + τ v) = 0 := by
      intro i
      have h1 := (hgood₀ v v.2 (τ v) (hτP v) hτv).1 hv i
      have h2 := (hgood₀ v v.2 (-τ v) (P.neg_mem (hτP v)) (by rwa [norm_neg])).1 hv i
      rw [map_add, hv0, zero_add] at h1 h2 ⊢
      rw [map_neg] at h2
      linarith
    have hC : ∀ z, (∀ i, ℓ i ((v : V) + τ v) = 0 → 0 ≤ ℓ i z) ↔ ∀ i, 0 ≤ ℓ i z := fun z =>
      forall_congr' fun i => ⟨fun H => H (hx0 i), fun H _ => H⟩
    refine ⟨ε₀ / 4, by positivity, ?_⟩
    rintro h ⟨w, rfl⟩ y hy hle
    rw [hC, hC]
    have hLw : ‖L w‖ ≤ ε₀ / 4 * ‖w‖ := L.le_of_opNorm_le hLnorm w
    have hLw' : ‖L w‖ ≤ ε₀ * ‖w‖ := hLw.trans (by gcongr; linarith)
    have hh : ‖(w : V) + L w‖ ≤ 5 / 4 * ‖w‖ := by
      calc ‖(w : V) + L w‖ ≤ ‖(w : V)‖ + ‖L w‖ := norm_add_le _ _
        _ ≤ ‖w‖ + ε₀ / 4 * ‖w‖ := by rw [Submodule.norm_coe]; gcongr
        _ ≤ 5 / 4 * ‖w‖ := by nlinarith [norm_nonneg w]
    have hyL : ‖y + L w‖ ≤ ε₀ * ‖w‖ := by
      calc ‖y + L w‖ ≤ ‖y‖ + ‖L w‖ := norm_add_le _ _
        _ ≤ ε₀ / 4 * (5 / 4 * ‖w‖) + ε₀ / 4 * ‖w‖ :=
          add_le_add (hle.trans (mul_le_mul_of_nonneg_left hh (by positivity))) hLw
        _ ≤ ε₀ * ‖w‖ := by nlinarith [norm_nonneg w]
    have e1 := hgood₀ w w.2 (L w) (hLP w) hLw'
    have e2 := hgood₀ w w.2 (y + L w) (P.add_mem hy (hLP w)) hyL
    have heq : (w : V) + L w + y = (w : V) + (y + L w) := by abel
    show (∀ i, 0 ≤ ℓ i ((w : V) + L w)) ↔ ∀ i, 0 ≤ ℓ i ((w : V) + L w + y)
    rw [heq, ← e2, ← e1]
  · -- the case `v ∉ N ∩ W`: the relevant coordinates vanish on `P`
    refine ⟨1, one_pos, fun h _ y hy _ => ?_⟩
    have hv0 : v ≠ 0 := fun h0 => hvW (by rw [h0]; exact (nullSpace _ _).zero_mem)
    have hzero : ∀ i, ℓ i ((v : V) + τ v) = 0 → ℓ i y = 0 := by
      intro i hi
      have hiv : ℓ i (v : V) = 0 := (hvan hvW i).2 hi
      have hiS : i ∈ vanIdx (ℓlin ℓ) N := (mem_vanIdx _ _).2 ⟨v, hv, hv0, hiv⟩
      exact lemma_3_8_8 (ℓlin ℓ) N P hε hgood hy hiS
    exact forall_congr' fun i => imp_congr_right fun hi => by
      rw [map_add, hzero i hi, add_zero]

end Core

/-! ### Lemma 3.6.9 (preprint 3.55) in the model `ℝⁿ ⊕ W` -/

section Model

variable {n : ℕ} {W : ScBanach}

/-- **Lemma 3.6.9 (preprint 3.55)**: `N` in good position to `C = [0,∞)ⁿ ⊕ W` with closed good complement `Y`, and
`τ : N ∩ C → Y` of class `C^1` with `τ(0) = 0`, `Dτ(0) = 0`.  Then for `v ∈ N ∩ C` close to `0`:
(1) `v + τ(v) ∈ C`; (2), (3) `Y` is a good complement of `N_v = {n + Dτ(v)n | n ∈ N}` with respect
to the partial quadrant `C_{v + τ(v)}` (in particular `E = N_v ⊕ Y`, both closed).
Added hypothesis: `Y` closed (the text's `Y = Y₀` is a topological complement). -/
theorem lemma_3_6_9_preprint {N : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)}
    [FiniteDimensional ℝ N] (hN : IsInGoodPosition _ (quadrant n W 0) N)
    {Y : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)}
    (hY : IsGoodComplement _ (quadrant n W 0) N Y)
    (hYc : IsClosed (Y : Set (((ScBanach.const (Fin n → ℝ)).prod W) 0)))
    (τ : N → ((ScBanach.const (Fin n → ℝ)).prod W) 0) (hτY : ∀ v, τ v ∈ Y)
    (hτ : ContDiffOn ℝ 1 τ (Subtype.val ⁻¹' quadrant n W 0)) (hτ0 : τ 0 = 0)
    (hDτ0 : fderivWithin ℝ τ (Subtype.val ⁻¹' quadrant n W 0) 0 = 0) :
    ∃ ρ > 0, ∀ v : N, (v : ((ScBanach.const (Fin n → ℝ)).prod W) 0) ∈ quadrant n W 0 → ‖v‖ < ρ →
      ((v : ((ScBanach.const (Fin n → ℝ)).prod W) 0) + τ v ∈ quadrant n W 0) ∧
      IsGoodComplement _
        (partialQuadrantAtWith (ScIso.refl _) ((v : ((ScBanach.const (Fin n → ℝ)).prod W) 0) + τ v))
        (graphSpace N (fderivWithin ℝ τ (Subtype.val ⁻¹' quadrant n W 0) v)) Y := by
  classical
  have hDeq := quadCone_coordCLM (W := W) N
  obtain ⟨ε, hε, hgood⟩ := hY.exists_eps
  have hℓ : ∀ (s : Finset (Fin n)) (k : Fin n → ℝ),
      ∃ v : ((ScBanach.const (Fin n → ℝ)).prod W) 0, ∀ i ∈ s, coordCLM (W := W) i v = k i :=
    fun s k => ⟨(k, 0), fun i _ => rfl⟩
  rw [← hDeq] at hτ hDτ0 ⊢
  have hint : (interior (quadCone (ℓlin (coordCLM (W := W))) N)).Nonempty := by
    rw [hDeq]; exact hN.interior_nonempty
  obtain ⟨ρ, hρ, hmain⟩ := lemma_3_6_9_core (coordCLM (W := W)) N Y hY.isCompl hYc hε hgood hℓ hint
    τ hτY hτ hτ0 hDτ0
  refine ⟨ρ, hρ, fun v hv hvρ => ?_⟩
  have hvD : v ∈ quadCone (ℓlin (coordCLM (W := W))) N := by rw [hDeq]; exact hv
  obtain ⟨hmem, hcompl, γ, hγ, hgoodv⟩ := hmain v hvD hvρ
  refine ⟨hmem, hcompl, γ, hγ, fun h hh y hy hle => ?_⟩
  exact hgoodv h hh y hy hle

end Model

end Polyfold
