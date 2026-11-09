import Polyfold.Chapter3.GoodPosition

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, Appendix 3.8.5:
Theorem 3.8.22 (preprint 3.78) (an implicit function theorem in partial quadrants) with Lemmas 3.8.23–3.8.26 (preprint 3.79–3.82).

# The implicit function theorem in partial quadrants

## The text, paraphrased

(Theorem 3.8.22 (preprint 3.78)) Let `U` be a relatively open neighbourhood of `0` in the partial quadrant
`C = [0,∞)ᵏ ⊕ ℝⁿ⁻ᵏ ⊆ ℝⁿ` and `f : U → ℝᴺ` of class `C^j`, `j ≥ 1`, with `f(0) = 0`, `Df(0)` onto,
and the kernel `K = ker Df(0)` in good position to `C` with good complement `Y`, `ℝⁿ = K ⊕ Y`.
Then there are an open neighbourhood `V` of `0` in the partial quadrant `K ∩ C`, a `C^j`-map
`τ : V → Y` and constants `ε, σ > 0` with (1) `τ(0) = 0`, `Dτ(0) = 0`, `k + τ(k) ∈ U` for `k ∈ V`;
(2) `|τ(k)| ≤ σ` if `k ∈ V`, `|k| ≤ ε`; (3) if `f(k + y) = 0` for `k ∈ V`, `|k| ≤ ε`, `y ∈ Y`,
`|y| ≤ σ`, then `y = τ(k)`.  *Proof.*  Replacing `f` by `(Df(0)|Y)⁻¹ ∘ f` one has
`f(k, y) = y − B(k, y)` with `B(0) = 0`, `DB(0) = 0` ((71)–(72)).  (Lemma 3.8.23 (preprint 3.79)) On
`(B_K(a) ⊕ B_Y(b)) ∩ C ⊆ U`, `B(k, ·)` is a `1/2`-contraction, so `f(k, y) = f(k, y')` forces
`y = y'`.  (Lemma 3.8.24 (preprint 3.80)) `|B(k, y)| ≤ ε|k|` for `|y| ≤ ε|k|`, with `ε` the good position constant,
so `B(k, ·)` maps `X_k = B̄_Y(ε|k|)` into itself (`k + y ∈ C` for `y ∈ X_k` by good position) and
has a unique fixed point `τ(k) ∈ X_k`.  (Lemma 3.8.25 (preprint 3.81)) `τ` is continuous with `|τ(k)| ≤ ε|k|/2`.
(Lemma 3.8.26 (preprint 3.82)) `τ` is `C^1` with `Dτ(k) = (1 − D₂B(k, τ k))⁻¹ D₁B(k, τ k)`; for `C^j` iterate with
`f⁽¹⁾(k, h, y, η) = (y − B(k, y), η − DB(k, y)(h, η))`.

## What is formalized

* `Polyfold.ContractionData` (the normalized data on `K × Y`: convex `C` with nonempty interior,
  relatively open `U ∋ 0`, `B ∈ C^j(U)` with `B(0) = 0`, `DB(0) = 0`, the good position estimate
  and the interior condition) and `Polyfold.Radii` (the constants `ε`, `a`, `b` of Lemmas
  3.79–3.80, `Polyfold.ContractionData.exists_radii`).
* `Polyfold.Radii.τ` (the fixed point), `Radii.eq_τ` (uniqueness), `Radii.norm_τ_le`,
  `Radii.norm_τ_sub_le_global` (**Lemma 3.8.25 (preprint 3.81)**, Lipschitz on all of `V₀` with the constant
  `ε/(1 + ε)`; `Radii.norm_τ_sub_le_eps`, the text's constant `ε`; `Radii.lipschitzOnWith_τ`),
  `Radii.norm_τ_sub_le` (the earlier form, constant `1 + 2ε`), `Radii.hasFDerivWithinAt_τ`,
  `Radii.fderivWithin_τ` (**Lemma 3.8.26 (preprint 3.82)**, the derivative formula), `Radii.contDiffOn_τ`
  (`τ ∈ C^j`).
* `Polyfold.ContractionData.exists_solution` (**Theorem 3.8.22 (preprint 3.78) in normalized form**) and
  `Polyfold.theorem_3_8_22` (**Theorem 3.8.22 (preprint 3.78)**), for a finite-dimensional `V` in place of `ℝⁿ`, `f`
  into any normed space, `C^j` in Mathlib's sense (`ContDiffOn ℝ j f U`; equal to Definition
  3.71 by `Polyfold.isSc1_iff_contDiffOn_of_isRelOpenInQuadrant` and Chapter 1).

## What the text leaves implicit, and the choices made (the findings)

* **Theorem 3.8.22 (preprint 3.78) (1) does not state `f(k + τ(k)) = 0`**, and (3) does not state `k + y ∈ U`;
  both are needed to make sense of the statement (`f` is defined on `U`) and are included.
* **Only the convexity of `C` and the nonemptiness of its interior are used**, not the partial
  quadrant structure: `ContractionData.exists_solution` is stated for a convex `C`.  The quadrant
  enters only through the good position hypothesis.
* **The regularity induction** of Lemma 3.8.26 (preprint 3.82) (iterating `f ↦ f⁽¹⁾`) is replaced by bootstrapping
  the derivative formula: `Dτ = Φ ∘ (id, τ)` with `Φ(p) = (1 − D₂B(p))⁻¹ D₁B(p)` of class `C^{j−1}`
  on the region `R` (inversion is smooth on units), so `τ ∈ C^i` gives `τ ∈ C^{i+1}` for `i < j`
  (`Radii.contDiffOn_τ`).  This also removes the text's "on a possibly smaller neighbourhood `V`
  of `0`": `τ` is `C^j` on the whole `V₀ = {k ∈ K ∩ C | |k| < a}`.
* **Lemma 3.8.25 (preprint 3.81)'s estimate `|τ(k) − τ(k₀)| ≤ ε|k − k₀|`** uses the point `(k, τ(k₀))` of the
  region `R`, which the text does not check; it lies in `R` when `|τ(k₀)| ≤ ε|k|`, e.g. when
  `|k₀| ≤ 2|k|` (as `|τ(k₀)| ≤ ε|k₀|/2`).  The estimate nevertheless holds on all of `V₀`: if
  `|k₀| > 2|k|`, then `|k| < 2|k₀|` and the same argument with `k` and `k₀` exchanged (through
  `(k₀, τ(k)) ∈ R`) applies.  Each case gives `|τ(k) − τ(k₀)| ≤ (1/2)|τ(k) − τ(k₀)| + c₀|k − k₀|`,
  so the constant is `2c₀ = ε/(1 + ε) < ε` (`Radii.norm_τ_sub_le_global`; round-trip item
  V3.66).  The first Lean proof (`Radii.norm_τ_sub_le`) treated the second case through
  `|τ(k)| + |τ(k₀)|` and only obtained the constant `1 + 2ε`.
* **The fixed-point set `X_k = B̄_Y(ε|k|)` depends on `k`** (it must, since `(k, y) ∈ C` is needed
  for `B(k, y)` to be defined); the parametrized Banach fixed point theorem of Theorems 3.3.2 (preprint 3.29)/3.40
  (`Polyfold.exists_fixedPoint_continuousOn`, fixed set) does not apply, and continuity is proved
  by hand (Lemma 3.8.25 (preprint 3.81)).
* **Lemma 3.8.26 (preprint 3.82), the differentiability**: the text's remainder `R(δk)` and `A(δk)` are organised
  here as the little-o composition `(B ∘ g)(k') − B(g k) − DB(g k)(g k' − g k) = o(|g k' − g k|)`
  with `g(k') = (k', τ(k'))` Lipschitz (`hasFDerivWithinAt_τ`), which is the same estimate.
* The derivative `Dτ(0) = 0` in (1): `Dτ(0) = (1 − D₂B(0))⁻¹ D₁B(0) = 0` since `DB(0) = 0`.
-/

open Set Filter Topology Function Module Asymptotics

set_option linter.unusedSectionVars false

noncomputable section

namespace Polyfold

section Core

variable {K Y : Type} [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- The data of the proof of Theorem 3.8.22 (preprint 3.78) after the normalization `f ↦ (Df(0)|Y)⁻¹ ∘ f` (p. 142,
(71)–(72)): on `K × Y` the convex set `Cp` (the partial quadrant `C`) with nonempty interior, the
relatively open `Up ∋ 0`, and `B` of class `C^j` on `Up` with `B(0) = 0`, `DB(0) = 0`, such that the
solutions of `f = 0` are the fixed points `y = B(k, y)`.  `K` is in good position to `C` with good
complement `Y` (`good`), and `K ∩ C` has nonempty interior in `K`. -/
structure ContractionData (Cp Up : Set (K × Y)) (B : K × Y → Y) (j : ℕ) : Prop where
  convex : Convex ℝ Cp
  interior_nonempty : (interior Cp).Nonempty
  relOpen : ∃ O : Set (K × Y), IsOpen O ∧ Up = O ∩ Cp
  zero_mem_U : (0 : K × Y) ∈ Up
  one_le : 1 ≤ j
  contDiffOn : ContDiffOn ℝ j B Up
  B_zero : B 0 = 0
  deriv_zero : fderivWithin ℝ B Up 0 = 0
  good : ∃ ε > 0, ∀ (k : K) (y : Y), ‖y‖ ≤ ε * ‖k‖ → ((k, 0) ∈ Cp ↔ (k, y) ∈ Cp)
  interior_K_nonempty : (interior {k : K | ((k, 0) : K × Y) ∈ Cp}).Nonempty

/-- The constants of Lemmas 3.8.23–3.8.24 (preprint 3.79–3.80): `ε` of the good position, radii `a` (in `K`) and `b` (in `Y`)
with `εa ≤ b`, such that the region `R = {|k| ≤ a, |y| ≤ b} ∩ C` lies in `U` and `‖DB‖ ≤ c₀` on it,
`c₀ = ε / (2(1 + ε))`. -/
structure Radii (Cp Up : Set (K × Y)) (B : K × Y → Y) where
  ε : ℝ
  a : ℝ
  b : ℝ
  ε_pos : 0 < ε
  a_pos : 0 < a
  b_pos : 0 < b
  εa_le : ε * a ≤ b
  good : ∀ (k : K) (y : Y), ‖y‖ ≤ ε * ‖k‖ → ((k, 0) ∈ Cp ↔ (k, y) ∈ Cp)
  region_sub : ∀ p : K × Y, ‖p.1‖ ≤ a → ‖p.2‖ ≤ b → p ∈ Cp → p ∈ Up
  deriv_bound : ∀ p : K × Y, ‖p.1‖ ≤ a → ‖p.2‖ ≤ b → p ∈ Cp →
    ‖fderivWithin ℝ B Up p‖ ≤ ε / (2 * (1 + ε))

variable {Cp Up : Set (K × Y)} {B : K × Y → Y} {j : ℕ}

namespace ContractionData

variable (h : ContractionData Cp Up B j)
include h

lemma zero_mem : (0 : K × Y) ∈ Cp := by
  obtain ⟨O, -, hU⟩ := h.relOpen
  have := h.zero_mem_U
  rw [hU] at this
  exact this.2

lemma uniqueDiffOn_U : UniqueDiffOn ℝ Up := by
  obtain ⟨O, hO, hU⟩ := h.relOpen
  rw [hU, inter_comm]
  exact (uniqueDiffOn_convex h.convex h.interior_nonempty).inter hO

lemma one_le' : (1 : WithTop ℕ∞) ≤ j := by exact_mod_cast h.one_le

lemma hasFDerivWithinAt {p : K × Y} (hp : p ∈ Up) :
    HasFDerivWithinAt B (fderivWithin ℝ B Up p) Up p :=
  ((h.contDiffOn.differentiableOn (by have := h.one_le; exact_mod_cast (show j ≠ 0 by omega)))
    p hp).hasFDerivWithinAt

lemma contDiffOn_deriv : ContDiffOn ℝ (j - 1 : ℕ) (fderivWithin ℝ B Up) Up := by
  refine h.contDiffOn.fderivWithin h.uniqueDiffOn_U ?_
  have := h.one_le
  exact_mod_cast (show (j - 1 : ℕ) + 1 ≤ j by omega)

lemma continuousOn_deriv : ContinuousOn (fderivWithin ℝ B Up) Up :=
  (h.contDiffOn.fderivWithin h.uniqueDiffOn_U (by exact_mod_cast h.one_le :
    (0 : WithTop ℕ∞) + 1 ≤ j)).continuousOn

/-- The constants exist (Lemmas 3.8.23, 3.8.24 (preprint 3.79, 3.80)). -/
theorem exists_radii : Nonempty (Radii Cp Up B) := by
  obtain ⟨ε, hε, hgood⟩ := h.good
  obtain ⟨O, hO, hU⟩ := h.relOpen
  set c₀ : ℝ := ε / (2 * (1 + ε)) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  -- continuity of `DB` at `0` within `Up`, `DB 0 = 0`
  have hcont := h.continuousOn_deriv 0 h.zero_mem_U
  rw [ContinuousWithinAt, h.deriv_zero, Metric.tendsto_nhdsWithin_nhds] at hcont
  obtain ⟨δ, hδ, hδ'⟩ := hcont c₀ hc₀pos
  -- `O` contains a ball around `0`
  have h0O : (0 : K × Y) ∈ O := by
    have := h.zero_mem_U; rw [hU] at this; exact this.1
  obtain ⟨δ', hδ'pos, hball⟩ := Metric.isOpen_iff.1 hO 0 h0O
  set r : ℝ := min δ δ' / 2 with hr
  have hrpos : 0 < r := by positivity
  have hrδ : r < δ := by
    have := min_le_left δ δ'; rw [hr]; linarith
  have hrδ' : r < δ' := by
    have := min_le_right δ δ'; rw [hr]; linarith
  refine ⟨⟨ε, r / (1 + ε), r, hε, by positivity, hrpos, ?_, hgood, ?_, ?_⟩⟩
  · rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  · intro p hp1 hp2 hpC
    rw [hU]
    refine ⟨hball ?_, hpC⟩
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def]
    have ha : r / (1 + ε) ≤ r := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    exact (max_le (hp1.trans ha) hp2).trans_lt hrδ'
  · intro p hp1 hp2 hpC
    have hpU : p ∈ Up := by
      rw [hU]
      refine ⟨hball ?_, hpC⟩
      rw [Metric.mem_ball, dist_zero_right, Prod.norm_def]
      have ha : r / (1 + ε) ≤ r := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      exact (max_le (hp1.trans ha) hp2).trans_lt hrδ'
    have hdist : dist p 0 < δ := by
      rw [dist_zero_right, Prod.norm_def]
      have ha : r / (1 + ε) ≤ r := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      exact (max_le (hp1.trans ha) hp2).trans_lt hrδ
    have := hδ' hpU hdist
    rw [dist_zero_right] at this
    exact this.le

end ContractionData

namespace Radii

variable (S : Radii Cp Up B)

/-- The contraction constant `c₀ = ε / (2(1 + ε))`. -/
def c₀ : ℝ := S.ε / (2 * (1 + S.ε))

lemma c₀_pos : 0 < S.c₀ := by unfold c₀; have := S.ε_pos; positivity

lemma c₀_le_half : S.c₀ ≤ 1 / 2 := by
  unfold c₀
  rw [div_le_iff₀ (by have := S.ε_pos; positivity)]
  have := S.ε_pos; nlinarith

lemma c₀_mul : S.c₀ * (1 + S.ε) = S.ε / 2 := by
  unfold c₀
  have : (1 + S.ε) ≠ 0 := by have := S.ε_pos; positivity
  field_simp

/-- The region `R = {|k| ≤ a, |y| ≤ b} ∩ C`. -/
def R : Set (K × Y) := {p | ‖p.1‖ ≤ S.a ∧ ‖p.2‖ ≤ S.b ∧ p ∈ Cp}

/-- The parameter domain `V₀ = {k ∈ K ∩ C | |k| < a}`. -/
def V₀ : Set K := {k | ‖k‖ < S.a ∧ ((k, 0) : K × Y) ∈ Cp}

lemma R_sub_U {p : K × Y} (hp : p ∈ S.R) : p ∈ Up := S.region_sub p hp.1 hp.2.1 hp.2.2

lemma zero_mem_V₀ (h : ContractionData Cp Up B j) : (0 : K) ∈ S.V₀ :=
  ⟨by rw [norm_zero]; exact S.a_pos, h.zero_mem⟩

lemma mem_R_of_mem_V₀ {k : K} (hk : k ∈ S.V₀) {y : Y} (hy : ‖y‖ ≤ S.ε * ‖k‖) : (k, y) ∈ S.R := by
  refine ⟨hk.1.le, ?_, (S.good k y hy).1 hk.2⟩
  calc ‖y‖ ≤ S.ε * ‖k‖ := hy
    _ ≤ S.ε * S.a := mul_le_mul_of_nonneg_left hk.1.le S.ε_pos.le
    _ ≤ S.b := S.εa_le

lemma convex_norm_fst_le (a : ℝ) : Convex ℝ {p : K × Y | ‖p.1‖ ≤ a} := by
  intro p hp q hq s t hs ht hst
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst] at hp hq ⊢
  calc ‖s • p.1 + t • q.1‖ ≤ ‖s • p.1‖ + ‖t • q.1‖ := norm_add_le _ _
    _ = s * ‖p.1‖ + t * ‖q.1‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
    _ ≤ s * a + t * a := by gcongr
    _ = a := by rw [← add_mul, hst, one_mul]

lemma convex_norm_snd_le (b : ℝ) : Convex ℝ {p : K × Y | ‖p.2‖ ≤ b} := by
  intro p hp q hq s t hs ht hst
  simp only [Set.mem_ofPred_eq, Prod.snd_add, Prod.smul_snd] at hp hq ⊢
  calc ‖s • p.2 + t • q.2‖ ≤ ‖s • p.2‖ + ‖t • q.2‖ := norm_add_le _ _
    _ = s * ‖p.2‖ + t * ‖q.2‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
    _ ≤ s * b + t * b := by gcongr
    _ = b := by rw [← add_mul, hst, one_mul]

lemma R_convex (h : ContractionData Cp Up B j) : Convex ℝ S.R :=
  (convex_norm_fst_le S.a).inter ((convex_norm_snd_le S.b).inter h.convex)

lemma zero_mem_R (h : ContractionData Cp Up B j) : (0 : K × Y) ∈ S.R :=
  ⟨by simp [S.a_pos.le], by simp [S.b_pos.le], h.zero_mem⟩

/-- The mean value inequality on `R` (Lemma 3.8.23 (preprint 3.79) (73), Lemma 3.8.24 (preprint 3.80) (74)). -/
lemma norm_sub_le (h : ContractionData Cp Up B j) {p q : K × Y} (hp : p ∈ S.R) (hq : q ∈ S.R) :
    ‖B q - B p‖ ≤ S.c₀ * ‖q - p‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun _ hx => (h.hasFDerivWithinAt (S.R_sub_U hx)).mono fun _ hz => S.R_sub_U hz)
    (fun x hx => S.deriv_bound x hx.1 hx.2.1 hx.2.2) (S.R_convex h) hp hq

lemma norm_B_le (h : ContractionData Cp Up B j) {p : K × Y} (hp : p ∈ S.R) :
    ‖B p‖ ≤ S.c₀ * ‖p‖ := by
  have := S.norm_sub_le h (S.zero_mem_R h) hp
  rwa [h.B_zero, sub_zero, sub_zero] at this

lemma norm_B_sub_le_snd (h : ContractionData Cp Up B j) {k : K} {y y' : Y} (hy : (k, y) ∈ S.R)
    (hy' : (k, y') ∈ S.R) : ‖B (k, y) - B (k, y')‖ ≤ 1 / 2 * ‖y - y'‖ := by
  have := S.norm_sub_le h hy' hy
  have hn : ‖((k, y) : K × Y) - (k, y')‖ = ‖y - y'‖ := by
    rw [Prod.norm_def]; simp
  rw [hn] at this
  calc ‖B (k, y) - B (k, y')‖ ≤ S.c₀ * ‖y - y'‖ := this
    _ ≤ 1 / 2 * ‖y - y'‖ := by gcongr; exact S.c₀_le_half

lemma norm_B_sub_le_fst (h : ContractionData Cp Up B j) {k k' : K} {y : Y} (hk : (k, y) ∈ S.R)
    (hk' : (k', y) ∈ S.R) : ‖B (k, y) - B (k', y)‖ ≤ S.c₀ * ‖k - k'‖ := by
  have := S.norm_sub_le h hk' hk
  have hn : ‖((k, y) : K × Y) - (k', y)‖ = ‖k - k'‖ := by
    rw [Prod.norm_def]; simp
  rwa [hn] at this

/-- `B(k, ·)` maps the ball `X_k = {|y| ≤ ε|k|}` into itself (Lemma 3.8.24 (preprint 3.80)). -/
lemma mapsTo_ball (h : ContractionData Cp Up B j) {k : K} (hk : k ∈ S.V₀) :
    MapsTo (fun y => B (k, y)) (Metric.closedBall (0 : Y) (S.ε * ‖k‖))
      (Metric.closedBall (0 : Y) (S.ε * ‖k‖)) := by
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right] at hy ⊢
  have hR := S.mem_R_of_mem_V₀ hk hy
  calc ‖B (k, y)‖ ≤ S.c₀ * ‖((k, y) : K × Y)‖ := S.norm_B_le h hR
    _ ≤ S.c₀ * ((1 + S.ε) * ‖k‖) := by
        refine mul_le_mul_of_nonneg_left ?_ S.c₀_pos.le
        rw [Prod.norm_def]
        refine max_le ?_ ?_
        · nlinarith [norm_nonneg k, S.ε_pos]
        · nlinarith [norm_nonneg k, S.ε_pos]
    _ = S.ε / 2 * ‖k‖ := by rw [← mul_assoc, S.c₀_mul]
    _ ≤ S.ε * ‖k‖ := by nlinarith [norm_nonneg k, S.ε_pos]

/-- Existence of the fixed point `τ(k) ∈ X_k` (Banach). -/
lemma exists_fixed (h : ContractionData Cp Up B j) {k : K} (hk : k ∈ S.V₀) :
    ∃ y : Y, ‖y‖ ≤ S.ε * ‖k‖ ∧ B (k, y) = y := by
  have : CompleteSpace Y := FiniteDimensional.complete ℝ Y
  have hsf : MapsTo (fun y => B (k, y)) (Metric.closedBall (0 : Y) (S.ε * ‖k‖))
    (Metric.closedBall (0 : Y) (S.ε * ‖k‖)) := S.mapsTo_ball h hk
  have hsc : IsComplete (Metric.closedBall (0 : Y) (S.ε * ‖k‖)) :=
    Metric.isClosed_closedBall.isComplete
  have hcontr : ContractingWith (1 / 2 : NNReal) (hsf.restrict _ _ _) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun y y' => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have hy2 : y.1 ∈ Metric.closedBall (0 : Y) (S.ε * ‖k‖) := y.2
    have hy2' : y'.1 ∈ Metric.closedBall (0 : Y) (S.ε * ‖k‖) := y'.2
    rw [Metric.mem_closedBall, dist_zero_right] at hy2 hy2'
    have := S.norm_B_sub_le_snd h (S.mem_R_of_mem_V₀ hk hy2) (S.mem_R_of_mem_V₀ hk hy2')
    simpa using this
  have h0 : (0 : Y) ∈ Metric.closedBall (0 : Y) (S.ε * ‖k‖) := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_zero]
    exact mul_nonneg S.ε_pos.le (norm_nonneg k)
  obtain ⟨y, hy, hfix, -⟩ := hcontr.exists_fixedPoint' hsc hsf h0 (edist_ne_top _ _)
  rw [Metric.mem_closedBall, dist_zero_right] at hy
  exact ⟨y, hy, hfix⟩

open scoped Classical in
/-- The solution map `τ : V₀ → Y` (extended by `0`). -/
def τ (h : ContractionData Cp Up B j) (k : K) : Y :=
  if hk : k ∈ S.V₀ then (S.exists_fixed h hk).choose else 0

variable (h : ContractionData Cp Up B j)

lemma norm_τ_le_eps {k : K} (hk : k ∈ S.V₀) : ‖S.τ h k‖ ≤ S.ε * ‖k‖ := by
  simp only [τ, dif_pos hk]
  exact (S.exists_fixed h hk).choose_spec.1

lemma τ_fixed {k : K} (hk : k ∈ S.V₀) : B (k, S.τ h k) = S.τ h k := by
  simp only [τ, dif_pos hk]
  exact (S.exists_fixed h hk).choose_spec.2

lemma τ_mem_R {k : K} (hk : k ∈ S.V₀) : (k, S.τ h k) ∈ S.R :=
  S.mem_R_of_mem_V₀ hk (S.norm_τ_le_eps h hk)

/-- Lemma 3.8.25 (preprint 3.81): `|τ(k)| ≤ ε|k|/2`. -/
lemma norm_τ_le {k : K} (hk : k ∈ S.V₀) : ‖S.τ h k‖ ≤ S.ε / 2 * ‖k‖ := by
  have h1 := S.norm_B_le h (S.τ_mem_R h hk)
  rw [S.τ_fixed h hk] at h1
  calc ‖S.τ h k‖ ≤ S.c₀ * ‖((k, S.τ h k) : K × Y)‖ := h1
    _ ≤ S.c₀ * ((1 + S.ε) * ‖k‖) := by
        refine mul_le_mul_of_nonneg_left ?_ S.c₀_pos.le
        rw [Prod.norm_def]
        refine max_le ?_ ?_
        · nlinarith [norm_nonneg k, S.ε_pos]
        · have := S.norm_τ_le_eps h hk
          nlinarith [norm_nonneg k, S.ε_pos]
    _ = S.ε / 2 * ‖k‖ := by rw [← mul_assoc, S.c₀_mul]

lemma τ_zero : S.τ h 0 = 0 := by
  have := S.norm_τ_le_eps h (S.zero_mem_V₀ h)
  rw [norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

/-- Uniqueness: a fixed point `y` with `(k, y) ∈ R` is `τ(k)` (Lemma 3.8.23 (preprint 3.79), last sentence). -/
lemma eq_τ {k : K} (hk : k ∈ S.V₀) {y : Y} (hy : (k, y) ∈ S.R) (hfix : B (k, y) = y) :
    y = S.τ h k := by
  have := S.norm_B_sub_le_snd h hy (S.τ_mem_R h hk)
  rw [hfix, S.τ_fixed h hk] at this
  have h2 : ‖y - S.τ h k‖ ≤ 0 := by linarith
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)

/-- Lemma 3.8.25 (preprint 3.81), the Lipschitz estimate, in a weaker form (with the constant `1 + 2ε`, the case
`|k₀| > 2|k|` bounded through `|τ(k)| + |τ(k₀)|`).  The text's `ε|k − k₀|` holds on all of `V₀`,
even with the constant `ε/(1 + ε)`: `norm_τ_sub_le_global`, `norm_τ_sub_le_eps`. -/
lemma norm_τ_sub_le {k k₀ : K} (hk : k ∈ S.V₀) (hk₀ : k₀ ∈ S.V₀) :
    ‖S.τ h k - S.τ h k₀‖ ≤ (1 + 2 * S.ε) * ‖k - k₀‖ := by
  by_cases hcase : ‖k₀‖ ≤ 2 * ‖k‖
  · -- `(k, τ k₀) ∈ R`
    have hmem : (k, S.τ h k₀) ∈ S.R := by
      refine S.mem_R_of_mem_V₀ hk ?_
      have := S.norm_τ_le h hk₀
      nlinarith [S.ε_pos]
    have h1 := S.norm_B_sub_le_snd h (S.τ_mem_R h hk) hmem
    have h2 := S.norm_B_sub_le_fst h hmem (S.τ_mem_R h hk₀)
    rw [S.τ_fixed h hk] at h1
    rw [S.τ_fixed h hk₀] at h2
    have h3 : ‖S.τ h k - S.τ h k₀‖ ≤ ‖S.τ h k - B (k, S.τ h k₀)‖ + ‖B (k, S.τ h k₀) - S.τ h k₀‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h4 := S.c₀_le_half
    have h5 : 0 ≤ ‖k - k₀‖ := norm_nonneg _
    nlinarith [S.ε_pos]
  · push Not at hcase
    have h1 := S.norm_τ_le h hk
    have h2 := S.norm_τ_le h hk₀
    have h3 : ‖S.τ h k - S.τ h k₀‖ ≤ ‖S.τ h k‖ + ‖S.τ h k₀‖ := _root_.norm_sub_le _ _
    have h4 : ‖k₀‖ - ‖k‖ ≤ ‖k - k₀‖ := by
      have := norm_sub_norm_le k₀ k
      rwa [norm_sub_rev] at this
    nlinarith [S.ε_pos, norm_nonneg k, norm_nonneg k₀]

/-- Lemma 3.8.25 (preprint 3.81), the case `|k₀| ≤ 2|k|` of `norm_τ_sub_le_global` (round-trip item V3.66): then
`(k, τ(k₀))` lies in the region `R` (`|τ(k₀)| ≤ ε|k₀|/2 ≤ ε|k|`), and
`τ(k) − τ(k₀) = [B(k, τ k) − B(k, τ k₀)] + [B(k, τ k₀) − B(k₀, τ k₀)]` gives
`|τ(k) − τ(k₀)| ≤ (1/2)|τ(k) − τ(k₀)| + c₀|k − k₀|`. -/
lemma norm_τ_sub_le_of_norm_le {k k₀ : K} (hk : k ∈ S.V₀) (hk₀ : k₀ ∈ S.V₀)
    (hcase : ‖k₀‖ ≤ 2 * ‖k‖) :
    ‖S.τ h k - S.τ h k₀‖ ≤ S.ε / (1 + S.ε) * ‖k - k₀‖ := by
  have hε := S.ε_pos
  have hmem : (k, S.τ h k₀) ∈ S.R := by
    refine S.mem_R_of_mem_V₀ hk ?_
    have := S.norm_τ_le h hk₀
    nlinarith
  have h1 := S.norm_B_sub_le_snd h (S.τ_mem_R h hk) hmem
  have h2 := S.norm_B_sub_le_fst h hmem (S.τ_mem_R h hk₀)
  rw [S.τ_fixed h hk] at h1
  rw [S.τ_fixed h hk₀] at h2
  have h3 : ‖S.τ h k - S.τ h k₀‖ ≤ ‖S.τ h k - B (k, S.τ h k₀)‖ + ‖B (k, S.τ h k₀) - S.τ h k₀‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h4 : 2 * S.c₀ = S.ε / (1 + S.ε) := by
    unfold c₀
    have : (1 + S.ε) ≠ 0 := by positivity
    field_simp
  rw [← h4]
  have h5 : 0 ≤ ‖k - k₀‖ := norm_nonneg _
  nlinarith

/-- **Lemma 3.8.25 (preprint 3.81), the Lipschitz estimate on all of `V₀`** (round-trip item V3.66): for all
`k, k₀ ∈ V₀`, `|τ(k) − τ(k₀)| ≤ ε/(1 + ε)·|k − k₀|`.  If `|k₀| ≤ 2|k|` this is
`norm_τ_sub_le_of_norm_le`; otherwise `|k| < 2|k₀|`, and the same lemma applies with `k` and `k₀`
exchanged.  (The text proves `ε|k − k₀|` through `(k, τ(k₀)) ∈ R`, which it does not check; the
exchange covers the case where it fails.) -/
theorem norm_τ_sub_le_global {k k₀ : K} (hk : k ∈ S.V₀) (hk₀ : k₀ ∈ S.V₀) :
    ‖S.τ h k - S.τ h k₀‖ ≤ S.ε / (1 + S.ε) * ‖k - k₀‖ := by
  by_cases hcase : ‖k₀‖ ≤ 2 * ‖k‖
  · exact S.norm_τ_sub_le_of_norm_le h hk hk₀ hcase
  · have hcase' : ‖k‖ ≤ 2 * ‖k₀‖ := by
      have := not_le.1 hcase
      nlinarith [norm_nonneg k, norm_nonneg k₀]
    rw [norm_sub_rev, norm_sub_rev k]
    exact S.norm_τ_sub_le_of_norm_le h hk₀ hk hcase'

/-- **Lemma 3.8.25 (preprint 3.81) as stated**: `|τ(k) − τ(k₀)| ≤ ε|k − k₀|` for all `k, k₀ ∈ V₀` (from
`norm_τ_sub_le_global`, `ε/(1 + ε) ≤ ε`; round-trip item V3.66). -/
theorem norm_τ_sub_le_eps {k k₀ : K} (hk : k ∈ S.V₀) (hk₀ : k₀ ∈ S.V₀) :
    ‖S.τ h k - S.τ h k₀‖ ≤ S.ε * ‖k - k₀‖ := by
  have hε := S.ε_pos
  refine (S.norm_τ_sub_le_global h hk hk₀).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact div_le_self hε.le (by linarith)

/-- `τ` is `ε/(1 + ε)`-Lipschitz on `V₀` (Lemma 3.8.25 (preprint 3.81), `norm_τ_sub_le_global`; round-trip item
V3.66). -/
theorem lipschitzOnWith_τ :
    LipschitzOnWith ⟨S.ε / (1 + S.ε), by have := S.ε_pos; positivity⟩ (S.τ h) S.V₀ :=
  LipschitzOnWith.of_dist_le_mul fun k hk k₀ hk₀ => by
    rw [dist_eq_norm, dist_eq_norm]
    exact S.norm_τ_sub_le_global h hk hk₀

lemma continuousOn_τ : ContinuousOn (S.τ h) S.V₀ :=
  (LipschitzOnWith.of_dist_le_mul (K := ⟨1 + 2 * S.ε, by have := S.ε_pos; positivity⟩)
    fun k hk k₀ hk₀ => by
      rw [dist_eq_norm, dist_eq_norm]
      exact S.norm_τ_sub_le h hk hk₀).continuousOn

/-! ### The derivative of `τ` (Lemma 3.8.26 (preprint 3.82)) -/

variable (Up B) in
/-- `D₁B(p) = DB(p) ∘ inl : K → Y`. -/
def D₁ (p : K × Y) : K →L[ℝ] Y := (fderivWithin ℝ B Up p).comp (ContinuousLinearMap.inl ℝ K Y)

variable (Up B) in
/-- `D₂B(p) = DB(p) ∘ inr : Y → Y`. -/
def D₂ (p : K × Y) : Y →L[ℝ] Y := (fderivWithin ℝ B Up p).comp (ContinuousLinearMap.inr ℝ K Y)

lemma norm_D₂_le {p : K × Y} (hp : p ∈ S.R) : ‖D₂ Up B p‖ ≤ S.c₀ := by
  refine ContinuousLinearMap.opNorm_le_bound _ S.c₀_pos.le fun y => ?_
  change ‖fderivWithin ℝ B Up p ((0 : K), y)‖ ≤ S.c₀ * ‖y‖
  calc ‖fderivWithin ℝ B Up p ((0 : K), y)‖
      ≤ ‖fderivWithin ℝ B Up p‖ * ‖(((0 : K), y) : K × Y)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ S.c₀ * ‖y‖ := by
        rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
        exact mul_le_mul_of_nonneg_right (S.deriv_bound p hp.1 hp.2.1 hp.2.2) (norm_nonneg _)

lemma norm_D₂_lt_one {p : K × Y} (hp : p ∈ S.R) : ‖D₂ Up B p‖ < 1 :=
  (S.norm_D₂_le hp).trans_lt (S.c₀_le_half.trans_lt (by norm_num))

variable (Up B) in
/-- `M(p) = (1 − D₂B(p))⁻¹` (the Neumann series, `‖D₂B‖ ≤ 1/2`). -/
def M (p : K × Y) : Y →L[ℝ] Y := Ring.inverse (1 - D₂ Up B p)

lemma M_mul {p : K × Y} (hp : p ∈ S.R) : M Up B p * (1 - D₂ Up B p) = 1 :=
  Ring.inverse_mul_cancel _ (Units.oneSub (D₂ Up B p) (S.norm_D₂_lt_one hp)).isUnit

variable (Up B) in
/-- The candidate derivative `Φ(p) = (1 − D₂B(p))⁻¹ D₁B(p)` (the formula of Lemma 3.8.26 (preprint 3.82)). -/
def Φ (p : K × Y) : K →L[ℝ] Y := (M Up B p).comp (D₁ Up B p)

lemma convex_CK (h : ContractionData Cp Up B j) : Convex ℝ {k : K | ((k, 0) : K × Y) ∈ Cp} :=
  h.convex.linear_preimage (LinearMap.inl ℝ K Y)

lemma uniqueDiffOn_V₀ (h : ContractionData Cp Up B j) : UniqueDiffOn ℝ S.V₀ := by
  have : S.V₀ = {k : K | ((k, 0) : K × Y) ∈ Cp} ∩ Metric.ball 0 S.a := by
    ext k; simp [V₀, Metric.mem_ball, and_comm]
  rw [this]
  exact (uniqueDiffOn_convex (convex_CK h) h.interior_K_nonempty).inter Metric.isOpen_ball

variable (h : ContractionData Cp Up B j)

/-- **Lemma 3.8.26 (preprint 3.82), the differentiability**: `τ` is differentiable within `V₀` at `k` with derivative
`Φ(k, τ(k)) = (1 − D₂B(k, τ k))⁻¹ D₁B(k, τ k)`. -/
theorem hasFDerivWithinAt_τ {k : K} (hk : k ∈ S.V₀) :
    HasFDerivWithinAt (S.τ h) (Φ Up B (k, S.τ h k)) S.V₀ k := by
  have hpR : (k, S.τ h k) ∈ S.R := S.τ_mem_R h hk
  have hB := h.hasFDerivWithinAt (S.R_sub_U hpR)
  rw [hasFDerivWithinAt_iff_isLittleO] at hB ⊢
  have hg_tend : Tendsto (fun k' => ((k', S.τ h k') : K × Y)) (𝓝[S.V₀] k) (𝓝[Up] (k, S.τ h k)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, eventually_nhdsWithin_of_forall fun k' hk' => S.R_sub_U (S.τ_mem_R h hk')⟩
    exact continuousWithinAt_id.prodMk ((S.continuousOn_τ h) k hk)
  have h1 := hB.comp_tendsto hg_tend
  have h2 : (fun k' => ((k', S.τ h k') : K × Y) - (k, S.τ h k)) =O[𝓝[S.V₀] k]
      (fun k' => k' - k) := by
    refine IsBigO.of_bound (1 + 2 * S.ε) (eventually_nhdsWithin_of_forall fun k' hk' => ?_)
    change ‖((k' - k, S.τ h k' - S.τ h k) : K × Y)‖ ≤ (1 + 2 * S.ε) * ‖k' - k‖
    rw [Prod.norm_def]
    refine max_le ?_ (S.norm_τ_sub_le h hk' hk)
    nlinarith [S.ε_pos, norm_nonneg (k' - k)]
  have h3 := h1.trans_isBigO h2
  have h4 := ((M Up B (k, S.τ h k)).isBigO_comp _ (𝓝[S.V₀] k)).trans_isLittleO h3
  refine h4.congr' (eventually_nhdsWithin_of_forall fun k' hk' => ?_) EventuallyEq.rfl
  simp only [Function.comp_apply]
  have e1 : B (k', S.τ h k') = S.τ h k' := S.τ_fixed h hk'
  have e2 : B (k, S.τ h k) = S.τ h k := S.τ_fixed h hk
  have e3 : fderivWithin ℝ B Up (k, S.τ h k) (((k', S.τ h k') : K × Y) - (k, S.τ h k)) =
      D₁ Up B (k, S.τ h k) (k' - k) + D₂ Up B (k, S.τ h k) (S.τ h k' - S.τ h k) := by
    have : ((k', S.τ h k') : K × Y) - (k, S.τ h k) =
        ContinuousLinearMap.inl ℝ K Y (k' - k) +
          ContinuousLinearMap.inr ℝ K Y (S.τ h k' - S.τ h k) := by
      simp
    rw [this, map_add]; rfl
  rw [e1, e2, e3]
  have e4 : S.τ h k' - S.τ h k -
        (D₁ Up B (k, S.τ h k) (k' - k) + D₂ Up B (k, S.τ h k) (S.τ h k' - S.τ h k)) =
      (1 - D₂ Up B (k, S.τ h k)) (S.τ h k' - S.τ h k) - D₁ Up B (k, S.τ h k) (k' - k) := by
    simp only [sub_apply, one_apply_eq_self]; abel
  rw [e4, map_sub, ← mul_apply_eq_comp, S.M_mul hpR, one_apply_eq_self]
  rfl

theorem fderivWithin_τ {k : K} (hk : k ∈ S.V₀) :
    fderivWithin ℝ (S.τ h) S.V₀ k = Φ Up B (k, S.τ h k) :=
  (S.hasFDerivWithinAt_τ h hk).fderivWithin (S.uniqueDiffOn_V₀ h k hk)

/-! ### Regularity (Lemma 3.8.26 (preprint 3.82), the induction) -/

include h in
/-- `Φ` is of class `C^{j−1}` on `R`: `DB` is `C^{j−1}` and inversion is smooth on units. -/
theorem contDiffOn_Φ : ContDiffOn ℝ (j - 1 : ℕ) (Φ Up B) S.R := by
  have hDB : ContDiffOn ℝ (j - 1 : ℕ) (fderivWithin ℝ B Up) S.R :=
    h.contDiffOn_deriv.mono fun p hp => S.R_sub_U hp
  have hD₁ : ContDiffOn ℝ (j - 1 : ℕ) (D₁ Up B) S.R := hDB.clm_comp contDiffOn_const
  have hD₂ : ContDiffOn ℝ (j - 1 : ℕ) (D₂ Up B) S.R := hDB.clm_comp contDiffOn_const
  have hM : ContDiffOn ℝ (j - 1 : ℕ) (M Up B) S.R := by
    intro p hp
    have h1 : ContDiffWithinAt ℝ (j - 1 : ℕ) (fun q => 1 - D₂ Up B q) S.R p :=
      (contDiffOn_const.sub hD₂) p hp
    have h2 : ContDiffAt ℝ (j - 1 : ℕ) (Ring.inverse : (Y →L[ℝ] Y) → (Y →L[ℝ] Y))
        ((Units.oneSub (D₂ Up B p) (S.norm_D₂_lt_one hp) : (Y →L[ℝ] Y)ˣ) : Y →L[ℝ] Y) :=
      contDiffAt_ringInverse ℝ _
    exact h2.contDiffWithinAt.comp p h1 (mapsTo_univ _ _)
  exact hM.clm_comp hD₁

/-- **Lemma 3.8.26 (preprint 3.82)**: `τ` is of class `C^j` on `V₀`.  (The text iterates `f ↦ f⁽¹⁾`; here the
derivative formula `Dτ = Φ ∘ (id, τ)` is bootstrapped: `τ ∈ C^i` gives `Dτ ∈ C^i`, so
`τ ∈ C^{i+1}`.) -/
theorem contDiffOn_τ : ContDiffOn ℝ j (S.τ h) S.V₀ := by
  have key : ∀ i : ℕ, i ≤ j → ContDiffOn ℝ i (S.τ h) S.V₀ := by
    intro i
    induction i with
    | zero => intro _; exact contDiffOn_zero.2 (S.continuousOn_τ h)
    | succ i ih =>
      intro hi
      have hV := S.uniqueDiffOn_V₀ h
      rw [show ((i + 1 : ℕ) : WithTop ℕ∞) = (i : WithTop ℕ∞) + 1 by push_cast; rfl]
      refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hV).2
        ⟨fun hω => absurd hω (by simp), fun k => Φ Up B (k, S.τ h k), ?_,
          fun k hk => S.hasFDerivWithinAt_τ h hk⟩
      have hΦ : ContDiffOn ℝ i (Φ Up B) S.R :=
        (S.contDiffOn_Φ h).of_le (by exact_mod_cast (show i ≤ j - 1 by omega))
      exact hΦ.comp (contDiffOn_id.prodMk (ih (by omega))) fun k hk => S.τ_mem_R h hk
  exact key j le_rfl

end Radii

/-- **Theorem 3.8.22 (preprint 3.78) in the normalized form** (after `f ↦ (Df(0)|Y)⁻¹ ∘ f`, on `K × Y`): the fixed
point equation `y = B(k, y)` has a solution `τ : V' → Y` of class `C^j` on a relatively open
neighbourhood `V'` of `0` in `K ∩ C`, with `τ(0) = 0`, `Dτ(0) = 0`, `(k, τ k) ∈ U`, bounded by `σ`
for `|k| ≤ ε`, and unique among the solutions `(k, y) ∈ U` with `|k| ≤ ε`, `|y| ≤ σ`. -/
theorem ContractionData.exists_solution (h : ContractionData Cp Up B j) :
    ∃ (V' : Set K) (τ : K → Y) (ε σ : ℝ),
      (∃ O : Set K, IsOpen O ∧ V' = O ∩ {k | ((k, 0) : K × Y) ∈ Cp}) ∧ (0 : K) ∈ V' ∧
      ContDiffOn ℝ j τ V' ∧ τ 0 = 0 ∧ fderivWithin ℝ τ V' 0 = 0 ∧
      (∀ k ∈ V', (k, τ k) ∈ Up ∧ B (k, τ k) = τ k) ∧
      0 < ε ∧ 0 < σ ∧ (∀ k ∈ V', ‖k‖ ≤ ε → ‖τ k‖ ≤ σ) ∧
      (∀ k ∈ V', ‖k‖ ≤ ε → ∀ y : Y, ‖y‖ ≤ σ → (k, y) ∈ Up → B (k, y) = y → y = τ k) := by
  obtain ⟨S⟩ := h.exists_radii
  refine ⟨S.V₀, S.τ h, S.a, S.b, ⟨Metric.ball 0 S.a, Metric.isOpen_ball, ?_⟩, S.zero_mem_V₀ h,
    S.contDiffOn_τ h, S.τ_zero h, ?_, fun k hk => ⟨S.R_sub_U (S.τ_mem_R h hk), S.τ_fixed h hk⟩,
    S.a_pos, S.b_pos, fun k hk _ => ?_, fun k hk _ y hy hyU hfix => ?_⟩
  · ext k; simp [Radii.V₀, Metric.mem_ball]
  · rw [S.fderivWithin_τ h (S.zero_mem_V₀ h), S.τ_zero h]
    change (Radii.M Up B (0, 0)).comp (Radii.D₁ Up B (0, 0)) = 0
    have : Radii.D₁ Up B ((0 : K), (0 : Y)) = 0 := by
      change (fderivWithin ℝ B Up 0).comp _ = 0
      rw [h.deriv_zero, ContinuousLinearMap.zero_comp]
    rw [this, ContinuousLinearMap.comp_zero]
  · calc ‖S.τ h k‖ ≤ S.ε / 2 * ‖k‖ := S.norm_τ_le h hk
      _ ≤ S.ε * S.a := by nlinarith [S.ε_pos, norm_nonneg k, hk.1.le]
      _ ≤ S.b := S.εa_le
  · have hyC : (k, y) ∈ Cp := by
      obtain ⟨O, -, hU⟩ := h.relOpen
      rw [hU] at hyU
      exact hyU.2
    exact S.eq_τ h hk ⟨hk.1.le, hy, hyC⟩ hfix

end Core

/-! ### Theorem 3.8.22 (preprint 3.78) -/

section Theorem378

variable {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Theorem 3.8.22 (preprint 3.78) (implicit function theorem in partial quadrants)**: `U` a relatively open
neighbourhood of `0` in the partial quadrant `C` of the finite-dimensional space `V` (the text:
`C = [0,∞)ᵏ ⊕ ℝⁿ⁻ᵏ ⊆ ℝⁿ`), `f : U → F` of class `C^j` (`j ≥ 1`) with `f(0) = 0`, `Df(0)` onto,
`K = ker Df(0)` in good position to `C` with good complement `Y`.  Then there are a relatively open
neighbourhood `V'` of `0` in `K ∩ C`, a `C^j`-map `τ : V' → Y` and `ε, σ > 0` with (1) `τ(0) = 0`,
`Dτ(0) = 0`, `k + τ(k) ∈ U` (and `f(k + τ(k)) = 0`, implicit in the text) for `k ∈ V'`; (2)
`|τ(k)| ≤ σ` for `k ∈ V'`, `|k| ≤ ε`; (3) if `f(k + y) = 0` with `k ∈ V'`, `|k| ≤ ε`, `y ∈ Y`,
`|y| ≤ σ` (and `k + y ∈ U`, implicit in the text), then `y = τ(k)`.

Only the convexity of `C` and the nonemptiness of its interior are used
(`Polyfold.ContractionData.exists_solution`). -/
theorem theorem_3_8_22 {C U : Set V} (hU : IsRelOpenInQuadrant (ScBanach.const V) C U)
    (h0 : (0 : V) ∈ U) {f : V → F} {j : ℕ} (hj : 1 ≤ j) (hf : ContDiffOn ℝ j f U) (hf0 : f 0 = 0)
    (hsurj : Function.Surjective (fderivWithin ℝ f U 0)) {K Y : Submodule ℝ V}
    (hK : K = LinearMap.ker (fderivWithin ℝ f U 0 : V →ₗ[ℝ] F))
    (hKC : IsInGoodPosition (ScBanach.const V) C K)
    (hY : IsGoodComplement (ScBanach.const V) C K Y) :
    ∃ (V' : Set K) (τ : K → Y) (ε σ : ℝ),
      (∃ O : Set K, IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' C) ∧ (0 : K) ∈ V' ∧
      ContDiffOn ℝ j τ V' ∧ τ 0 = 0 ∧ fderivWithin ℝ τ V' 0 = 0 ∧
      (∀ k ∈ V', (k : V) + τ k ∈ U ∧ f ((k : V) + τ k) = 0) ∧
      0 < ε ∧ 0 < σ ∧ (∀ k ∈ V', ‖k‖ ≤ ε → ‖τ k‖ ≤ σ) ∧
      (∀ k ∈ V', ‖k‖ ≤ ε → ∀ y ∈ Y, ‖y‖ ≤ σ → (k : V) + y ∈ U → f ((k : V) + y) = 0 →
        y = τ k) := by
  classical
  set L : V →L[ℝ] F := fderivWithin ℝ f U 0 with hL
  have hKY : IsCompl K Y := hY.isCompl
  -- the identification `K × Y ≅ V`
  let add : (K × Y) ≃L[ℝ] V := (Submodule.prodEquivOfIsCompl K Y hKY).toContinuousLinearEquiv
  have hadd : ∀ p : K × Y, add p = (p.1 : V) + p.2 := fun p => by
    change (Submodule.prodEquivOfIsCompl K Y hKY).toContinuousLinearEquiv p = _
    rw [LinearEquiv.coe_toContinuousLinearEquiv', Submodule.coe_prodEquivOfIsCompl']
  have hadd' : ∀ p : K × Y, (add : K × Y →L[ℝ] V) p = (p.1 : V) + p.2 := fun p => hadd p
  -- `L|_Y : Y → F` is an isomorphism
  have hLK : ∀ k : K, L k = 0 := fun k => by
    have : (k : V) ∈ LinearMap.ker (L : V →ₗ[ℝ] F) := hK ▸ k.2
    exact LinearMap.mem_ker.1 this
  have hinj : Function.Injective (L ∘ₗ Y.subtype : Y →ₗ[ℝ] F) := by
    intro y y' hyy'
    have h1 : L ((y : V) - y') = 0 := by
      rw [map_sub]; exact sub_eq_zero.2 hyy'
    have h2 : ((y : V) - y') ∈ K := by rw [hK]; exact LinearMap.mem_ker.2 h1
    have h3 : ((y : V) - y') ∈ Y := Y.sub_mem y.2 y'.2
    have h4 : ((y : V) - y') = 0 := by
      have := hKY.disjoint.le_bot ⟨h2, h3⟩
      simpa using this
    exact Subtype.ext (sub_eq_zero.1 h4)
  have hsurjY : Function.Surjective (L ∘ₗ Y.subtype : Y →ₗ[ℝ] F) := by
    intro z
    obtain ⟨x, hx⟩ := hsurj z
    have hx' : x ∈ K ⊔ Y := by rw [hKY.sup_eq_top]; trivial
    obtain ⟨k, hk, y, hy, rfl⟩ := Submodule.mem_sup.1 hx'
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [map_add, hLK ⟨k, hk⟩, zero_add] at hx
    exact hx
  let LY : Y ≃L[ℝ] F := (LinearEquiv.ofBijective _ ⟨hinj, hsurjY⟩).toContinuousLinearEquiv
  have hLY : ∀ y : Y, LY y = L y := fun y => rfl
  set Linv : F →L[ℝ] Y := (LY.symm : F →L[ℝ] Y) with hLinv
  have hLinvL : ∀ y : Y, Linv (L y) = y := fun y => by
    rw [← hLY]; exact LY.symm_apply_apply y
  -- the normalized map `B(k, y) = y − L⁻¹ f(k + y)`
  set Cp : Set (K × Y) := add ⁻¹' C with hCp
  set Up : Set (K × Y) := add ⁻¹' U with hUp
  set B : K × Y → Y := fun p => p.2 - Linv (f (add p)) with hB
  obtain ⟨O, hO, hUO⟩ := hU.relOpen
  have hCconv : Convex ℝ C := hU.isPartialQuadrant.convex
  have hCint : (interior C).Nonempty := by
    have := hU.isPartialQuadrant.interior_lvlSet_nonempty 0
    rwa [ScBanach.lvlSet_const] at this
  have hCpconv : Convex ℝ Cp := hCconv.linear_preimage (add : K × Y →ₗ[ℝ] V)
  have hCpint : (interior Cp).Nonempty := by
    have hpre : (add : K × Y → V) ⁻¹' interior C = interior (add ⁻¹' C) := by
      simpa using add.toHomeomorph.preimage_interior C
    rw [hCp, ← hpre]
    exact hCint.preimage add.surjective
  have hUpeq : Up = add ⁻¹' O ∩ Cp := by rw [hUp, hCp, hUO, preimage_inter]
  have h0Up : (0 : K × Y) ∈ Up := by
    change add 0 ∈ U
    rw [map_zero]; exact h0
  have hUpUD : UniqueDiffWithinAt ℝ Up 0 := by
    rw [hUpeq, inter_comm]
    refine (uniqueDiffWithinAt_convex hCpconv hCpint (subset_closure ?_)).inter
      ((hO.preimage add.continuous).mem_nhds ?_)
    · have := h0Up; rw [hUpeq] at this; exact this.2
    · have := h0Up; rw [hUpeq] at this; exact this.1
  have hBcd : ContDiffOn ℝ j B Up := by
    have h1 : ContDiffOn ℝ j (f ∘ add) Up :=
      hf.comp (add : K × Y →L[ℝ] V).contDiff.contDiffOn fun p hp => hp
    exact contDiff_snd.contDiffOn.sub (h1.continuousLinearMap_comp Linv)
  have hLf : HasFDerivWithinAt f L U (add 0) := by
    rw [map_zero]
    exact ((hf.differentiableOn (by exact_mod_cast (show j ≠ 0 by omega))) 0 h0).hasFDerivWithinAt
  have hBderiv : HasFDerivWithinAt B
      (ContinuousLinearMap.snd ℝ K Y - Linv.comp (L.comp (add : K × Y →L[ℝ] V))) Up 0 := by
    refine hasFDerivWithinAt_snd.sub ?_
    exact Linv.hasFDerivAt.comp_hasFDerivWithinAt (x := (0 : K × Y))
      (hLf.comp (0 : K × Y) (add : K × Y →L[ℝ] V).hasFDerivWithinAt fun p hp => hp)
  have hBderiv0 :
      ContinuousLinearMap.snd ℝ K Y - Linv.comp (L.comp (add : K × Y →L[ℝ] V)) = 0 := by
    refine ContinuousLinearMap.ext fun p => ?_
    simp only [sub_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.comp_apply, zero_apply]
    rw [hadd', map_add, hLK, zero_add, hLinvL, sub_self]
  have hdata : ContractionData Cp Up B j :=
    { convex := hCpconv
      interior_nonempty := hCpint
      relOpen := ⟨add ⁻¹' O, hO.preimage add.continuous, hUpeq⟩
      zero_mem_U := h0Up
      one_le := hj
      contDiffOn := hBcd
      B_zero := by
        change (0 : K × Y).2 - Linv (f (add 0)) = 0
        rw [map_zero, hf0, map_zero]; simp
      deriv_zero := by rw [hBderiv.fderivWithin hUpUD, hBderiv0]
      good := by
        obtain ⟨ε, hε, hgood⟩ := hY.exists_eps
        refine ⟨ε, hε, fun k y hy => ?_⟩
        have := hgood k k.2 y y.2 hy
        change add (k, 0) ∈ C ↔ add (k, y) ∈ C
        rw [hadd, hadd]
        simpa using this
      interior_K_nonempty := by
        have : {k : K | ((k, 0) : K × Y) ∈ Cp} = Subtype.val ⁻¹' C := by
          ext k
          change add (k, 0) ∈ C ↔ _
          rw [hadd]; simp
        rw [this]; exact hKC.interior_nonempty }
  obtain ⟨V', τ, ε, σ, ⟨O', hO', hV'⟩, h0V', hτcd, hτ0, hDτ0, hsol, hε, hσ, hbound, huniq⟩ :=
    hdata.exists_solution
  have hCK : {k : K | ((k, 0) : K × Y) ∈ Cp} = Subtype.val ⁻¹' C := by
    ext k
    change add (k, 0) ∈ C ↔ _
    rw [hadd]; simp
  have hfix_iff : ∀ (k : K) (y : Y), B (k, y) = y ↔ f ((k : V) + y) = 0 := fun k y => by
    change y - Linv (f (add (k, y))) = y ↔ _
    rw [hadd, sub_eq_self]
    constructor
    · intro h
      have h2 : LY (Linv (f ((k : V) + y))) = f ((k : V) + y) := LY.apply_symm_apply _
      rw [h, map_zero] at h2
      exact h2.symm
    · intro h; rw [h, map_zero]
  refine ⟨V', τ, ε, σ, ⟨O', hO', by rw [hV', hCK]⟩, h0V', hτcd, hτ0, hDτ0, fun k hk => ?_, hε, hσ,
    hbound, fun k hk hkε y hy hyσ hyU hfy => ?_⟩
  · obtain ⟨h1, h2⟩ := hsol k hk
    refine ⟨?_, (hfix_iff k (τ k)).1 h2⟩
    have : add (k, τ k) ∈ U := h1
    rwa [hadd] at this
  · have := huniq k hk hkε ⟨y, hy⟩ hyσ (by show add (k, ⟨y, hy⟩) ∈ U; rw [hadd]; exact hyU)
      ((hfix_iff k ⟨y, hy⟩).2 hfy)
    exact congrArg Subtype.val this

end Theorem378

end Polyfold
