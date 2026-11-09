import Polyfold.Chapter3.GermIFTSmooth
import Polyfold.Chapter3.GermFillingChart
import Polyfold.Chapter3.NonVacuity
import Polyfold.Chapter3.StrongBundleSections
import Polyfold.Chapter1.ExpositionLemmas

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
Definitions 3.1.1–3.1.2 (preprint 3.1–3.2) (sc-germs of neighbourhoods and sc-smooth germs) against Definitions 3.1.6, 3.1.11 (preprint 3.6, 3.11)
(filled versions and sc-Fredholm germs): **what the text's germs with shrinking levels are, and
where the project's whole-chart data differ from them.**  Follow-up of the round-trip audit
(items V3.5, V3.9, V3.13, V3.43, V3.45; Findings, Chapter 3, items 220–221 and 260–269).

# Germs versus the whole chart

## The text, paraphrased

(Definition 3.1.1 (preprint 3.1)) An sc-germ of neighbourhoods `O(C, 0)` is a decreasing sequence `U₀ ⊃ U₁ ⊃ ⋯`
with `U_m` relatively open in `C ∩ E_m`; the sizes of the `U_m` may shrink with `m`.
(Definition 3.1.2 (preprint 3.2)) An sc^k-germ is sc^k on these sets.  (Definition 3.1.6 (preprint 3.6)) `(f, x₀)` has a filling if
the section germ `Φ ∘ f ∘ φ⁻¹` has a filling `(g, 0)` — an sc-smooth section **germ** of
`U ◁ F → U` with conditions (1)–(3) of Definition 3.1.4 (preprint 3.4) near `0`.  (Definition 3.1.11 (preprint 3.11)) `(f, x₀)` is an
sc-Fredholm germ if it has a filled version `(g, 0)` and a **local** sc⁺-section `s` with
`s(0) = g(0)` such that `g − s` is conjugated by a strong bundle isomorphism to a basic germ.
(Definition 3.1.16 (preprint 3.14) (1)) The section `f` itself is sc-smooth on all of `X`.

## What is formalized

* **The example of Findings item 221, machine-checked** (`Polyfold.GermVsChart`): the function
  `f(x) = Σ_n c_n (x − a_n)^{n+1} |x − a_n|`, `a_n = 1/(n + 2)`, `c_n = (4(n + 2))^{−(n+2)}`, is
  `C^k` on `(−1/(k+2), 1/(k+2))` for every `k` (`GermVsChart.contDiffOn_f`) and `C^{n+2}` on no
  open set containing `a_n` (`GermVsChart.not_contDiffOn_f`).  In the constant scale `ℝ` it is an
  **sc-smooth germ** on the germ of neighbourhoods `U_m = (−1/(m+2), 1/(m+2))`
  (`GermVsChart.isScSmoothGerm_f`, through the locality lemma `isScSmoothGerm_of_levels` of
  `GermIFTSmooth.lean`) but **sc-smooth on no open `U ∋ 0`** (`GermVsChart.not_isScSmooth_f`);
  `Polyfold.exists_isScSmoothGerm_not_isScSmooth` packages this.  Shrinking the chart (restricting
  `U` on level `0`) never produces a germ whose levels shrink with `m`.
* **The text's germ reading of Definitions 3.1.6 and 3.1.11 (preprint 3.6 and 3.11)**: `Polyfold.IsFillingGerm` (a filling in
  the sense of Definition 3.1.4 (preprint 3.4) with `g` an sc-smooth germ on a germ of neighbourhoods `G ⊆ U`,
  conditions (1), (2) near `0`, condition (3) for a derivative family of the sc¹-germ
  `y ↦ [1 − ρ(r(y))]g(y)` on `G`), `Polyfold.IsScPlusGerm` (a local sc⁺-section: an sc-smooth germ
  into `F¹`), and `Polyfold.StrongBundle.IsScFredholmGerm` (**Definition 3.1.11 (preprint 3.11), germ reading**:
  the project's `IsScFredholmGermWholeChart` with `IsFilledVersion` and the whole-`U` sc⁺-section replaced by
  these germs; the strong bundle isomorphism `Ψ : U ◁ F → U' ◁ F'` and the basic germ `h` as in
  `IsConjugateToBasicGerm`).
* **Project ⇒ text**: `Polyfold.IsFilledVersion.isFillingGerm`,
  `Polyfold.StrongBundle.IsScFredholmGermWholeChart.isScFredholmGerm` (the audit's `proj_to_B`,
  `proj_to_parts`, cleaned up).
* **Text ⇒ project when the germs are whole-chart**: `Polyfold.IsFillingGerm.isFilledVersion`
  (a filling whose `g` is sc-smooth on the whole `U` is a filled version: `[1 − ρ(r(·))]g` is
  sc¹ on `U` by the chain rule, and its linearization at `0` is the germ's by uniqueness), and
  the **reduction** `Polyfold.StrongBundle.isScFredholmGerm_iff_germG_wholeChart`: `(f, x₀)` is an
  sc-Fredholm germ in the project's sense **iff** it is one in the text's germ sense with the
  filled version `g` and the sc⁺-section `s` sc-smooth on the whole `U ∩ E_m` of the chart.  So
  the whole difference between the two readings is the regularity of `g` and `s` on
  `U ∩ E_m` away from the shrinking germ.
* **The filled version is harmless for a trivial retraction** (`K = U ◁ F`, `R = id` on `U ⊕ F`):
  `Polyfold.isStrongBundleRetraction_id_of_relOpen`, `Polyfold.isFilledVersion_id` (a map
  sc-smooth on `U` is its own filled version), `Polyfold.IsConjugateToBasicGerm.congr_nhds`, and
  `Polyfold.exists_wholeChart_filledVersion_of_id`: for `R = id`, the text's germ filling `g̃` of an
  `f̂` sc-smooth on `U` can be replaced by the whole-chart `g = f̂` in the data of Definition 3.1.11 (preprint 3.11)
  (same `s`, same conjugation, `f̂ = g̃` near `0` by condition (1)).  Since `f` is sc-smooth on all
  of `X` (Definition 3.1.16 (preprint 3.14) (1)), for charts with trivial retraction the open question below is
  about the sc⁺-section `s` alone.

## What the text leaves implicit, and the choices made (the findings)

* **The germ reading.**  "`(g, 0)` is a section germ", "a local sc⁺-section `s`": sc-smooth germs
  on germs of neighbourhoods `G ⊆ U` of Definition 3.1.1 (preprint 3.1) (`IsFillingGerm`, `IsScPlusGerm`).  The
  strong bundle isomorphism `Ψ : U ◁ F → U' ◁ F'` is kept on the whole `U` of the chart as in
  `IsConjugateToBasicGerm`: germ data on a relatively open `U₀ ⊆ U` and on `U` carry the same
  information near `0` (`ConjugationData.ofSubset`, `IsConjugateToBasicGerm.of_subset`,
  `Chapter3/RestrictOpenGerms.lean`), which is harmless for level-`0` neighbourhoods; only germs
  whose levels shrink with `m` escape restriction.  The
  text's tameness of the chart (Definition 3.1.4 (preprint 3.4) is stated for tame strong local bundles) is not
  imposed, as in `IsScFredholmGermWholeChart`.
* **Condition (3) for a germ** needs a derivative at `0` of `[1 − ρ(r(·))]g`, i.e. that this map
  is an sc¹-germ; its derivative family at `0` is unique (`IsSc1GermWith.eq_of_uniqueDiffWithinAt`),
  so `IsFillingGerm` quantifies over a derivative family `Dk` of the germ and uses `Dk 0`.
* **The open question** (Findings item 260): whether the germ reading is equivalent to the
  project's for sections of strong bundles (sc-smooth on all of `X`), i.e. whether a germ
  sc⁺-section `s` (and, for non-trivial retractions, a germ filling `g`) can always be traded for
  whole-chart ones after changing `Ψ` and `h`.  Not settled here in either direction; the
  reduction above states precisely what is missing.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

/-! ### The example of item 221: `C^k` on `(−1/(k+2), 1/(k+2))` for every `k`, `C^∞` near no point
of a sequence converging to `0` -/

namespace GermVsChart

/-- `H k a x = (x − a)^k |x − a|`: of class `C^k` on `ℝ`, not `C^{k+1}` near `a`. -/
def H (k : ℕ) (a : ℝ) (x : ℝ) : ℝ := (x - a) ^ k * |x - a|

lemma continuous_H (k : ℕ) (a : ℝ) : Continuous (H k a) := by
  unfold H
  exact ((continuous_id.sub continuous_const).pow k).mul (continuous_id.sub continuous_const).abs

/-- `(x − a)|x − a|` has derivative `2|x − a|` at every point. -/
lemma hasDerivAt_mul_abs (a x : ℝ) :
    HasDerivAt (fun y => (y - a) * |y - a|) (2 * |x - a|) x := by
  rcases lt_trichotomy x a with hlt | heq | hgt
  · have h1 : HasDerivAt (fun y => -((y - a) ^ 2)) (-(2 * (x - a))) x := by
      have h := (hasDerivAt_pow 2 (x - a)).comp x ((hasDerivAt_id x).sub_const a)
      refine ((h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_).neg
      · rfl
      · norm_num
    refine (h1.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [Iio_mem_nhds hlt] with y hy
      rw [abs_of_neg (sub_neg.2 hy)]; ring
    · rw [abs_of_neg (sub_neg.2 hlt)]; ring
  · subst heq
    rw [sub_self, abs_zero, mul_zero, hasDerivAt_iff_tendsto_slope_zero]
    have h1 : (fun t : ℝ => t⁻¹ • ((x + t - x) * |x + t - x| - (x - x) * |x - x|)) =ᶠ[𝓝[≠] 0]
        fun t => |t| := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [add_sub_cancel_left, sub_self, abs_zero, mul_zero, sub_zero, smul_eq_mul]
      rw [inv_mul_cancel_left₀ ht]
    rw [tendsto_congr' h1]
    simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · have h1 : HasDerivAt (fun y => (y - a) ^ 2) (2 * (x - a)) x := by
      have h := (hasDerivAt_pow 2 (x - a)).comp x ((hasDerivAt_id x).sub_const a)
      refine (h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
      · rfl
      · norm_num
    refine (h1.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [Ioi_mem_nhds hgt] with y hy
      rw [abs_of_pos (sub_pos.2 hy)]; ring
    · rw [abs_of_pos (sub_pos.2 hgt)]

/-- `H (k+1) a` has derivative `(k + 2) H k a` at every point. -/
lemma hasDerivAt_H_succ (k : ℕ) (a x : ℝ) :
    HasDerivAt (H (k + 1) a) (((k : ℝ) + 2) * H k a x) x := by
  have h1 : HasDerivAt (fun y => (y - a) ^ k) ((k : ℝ) * (x - a) ^ (k - 1)) x := by
    have h := (hasDerivAt_pow k (x - a)).comp x ((hasDerivAt_id x).sub_const a)
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
    · rfl
    · simp
  have h2 := h1.mul (hasDerivAt_mul_abs a x)
  refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [H, Pi.mul_apply]; ring
  · simp only [H]
    cases k with
    | zero => simp
    | succ k =>
      rw [Nat.add_sub_cancel]
      push_cast
      ring

lemma deriv_H_succ (k : ℕ) (a : ℝ) : deriv (H (k + 1) a) = fun x => ((k : ℝ) + 2) * H k a x :=
  funext fun x => (hasDerivAt_H_succ k a x).deriv

/-- `H k a` is of class `C^k`. -/
lemma contDiff_H (k : ℕ) (a : ℝ) : ContDiff ℝ k (H k a) := by
  induction k with
  | zero => exact contDiff_zero.2 (continuous_H 0 a)
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_H_succ k a x).differentiableAt,
      fun h => (WithTop.natCast_ne_top k h).elim, ?_⟩
    rw [deriv_H_succ]
    exact contDiff_const.mul ih

/-- The iterated derivatives of `H k a`: `H k a^{(l)} = (k+1)!/(k+1−l)! · H (k−l) a` for `l ≤ k`. -/
lemma iteratedDeriv_H (k : ℕ) (a : ℝ) : ∀ l ≤ k, iteratedDeriv l (H k a) =
    fun x => (((k + 1).descFactorial l : ℕ) : ℝ) * H (k - l) a x := by
  intro l
  induction l with
  | zero => intro _; funext x; simp [iteratedDeriv_zero]
  | succ l ih =>
    intro hl
    rw [iteratedDeriv_succ, ih (by omega)]
    obtain ⟨j, hj⟩ : ∃ j, k - l = j + 1 := ⟨k - l - 1, by omega⟩
    rw [hj]
    funext x
    rw [deriv_const_mul _ (hasDerivAt_H_succ j a x).differentiableAt, deriv_H_succ]
    have e1 : k - (l + 1) = j := by omega
    have e2 : k + 1 - l = j + 2 := by omega
    rw [e1, Nat.descFactorial_succ, e2]
    push_cast
    ring

lemma abs_H (k : ℕ) (a x : ℝ) : |H k a x| = |x - a| ^ (k + 1) := by
  simp [H, abs_mul, abs_pow, abs_abs, pow_succ]

lemma abs_H_le {k : ℕ} {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    |H k a x| ≤ 2 ^ (k + 1) := by
  rw [abs_H]
  have : |x - a| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  gcongr

/-- `H k a` is not `C^{k+1}` on any open set containing `a` (`H 0 a = |· − a|` is not
differentiable at `a`, and `H (k+1) a' = (k+2) H k a`). -/
theorem not_contDiffOn_H (k : ℕ) (a : ℝ) : ∀ {U : Set ℝ}, IsOpen U → a ∈ U →
    ¬ ContDiffOn ℝ (k + 1) (H k a) U := by
  induction k with
  | zero =>
    intro U hU ha h
    have h1 : DifferentiableAt ℝ (H 0 a) a :=
      ((contDiffOn_succ_iff_deriv_of_isOpen (n := 0) hU).1 (by exact_mod_cast h)).1.differentiableAt
        (hU.mem_nhds ha)
    have h2 : DifferentiableAt ℝ (H 0 a ∘ fun y : ℝ => y + a) 0 := by
      have h1' : DifferentiableAt ℝ (H 0 a) ((fun y : ℝ => y + a) 0) := by simpa using h1
      exact h1'.comp 0 (differentiableAt_id.add_const a)
    have h3 : (H 0 a ∘ fun y : ℝ => y + a) = (abs : ℝ → ℝ) := by
      funext y; simp [H]
    rw [h3] at h2
    exact not_differentiableAt_abs_zero h2
  | succ k ih =>
    intro U hU ha h
    have h1 := ((contDiffOn_succ_iff_deriv_of_isOpen (n := ((k + 1 : ℕ) : WithTop ℕ∞)) hU).1
      (by exact_mod_cast h)).2.2
    rw [deriv_H_succ] at h1
    refine ih hU ha ?_
    have h2 := h1.const_smul (((k : ℝ) + 2)⁻¹)
    refine h2.congr fun x _ => ?_
    simp only [smul_eq_mul]
    field_simp

/-- The singular points `a n = 1/(n+2)`. -/
def a (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

/-- The coefficients `c n = (4(n+2))^{−(n+2)}`. -/
def c (n : ℕ) : ℝ := (4 * ((n : ℝ) + 2))⁻¹ ^ (n + 2)

/-- The `n`-th term `c n · H (n+1) (a n)`: `C^{n+1}`, not `C^{n+2}` near `a n`. -/
def term (n : ℕ) (x : ℝ) : ℝ := c n * H (n + 1) (a n) x

/-- The example: `f = Σ_n term n`. -/
def f (x : ℝ) : ℝ := ∑' n, term n x

lemma a_pos (n : ℕ) : 0 < a n := by unfold a; positivity

lemma a_le_half (n : ℕ) : a n ≤ 1 / 2 := by
  unfold a
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

lemma a_mem_Ioo (n : ℕ) : a n ∈ Ioo (-1 : ℝ) 1 :=
  ⟨by linarith [a_pos n], by linarith [a_le_half n]⟩

lemma a_injective : Injective a := by
  intro m n h
  unfold a at h
  rw [one_div, one_div, inv_inj] at h
  exact_mod_cast (add_right_cancel h)

lemma c_pos (n : ℕ) : 0 < c n := by unfold c; positivity

lemma iteratedDeriv_term (n l : ℕ) (hl : l ≤ n + 1) : iteratedDeriv l (term n) =
    fun x => c n * ((((n + 2).descFactorial l : ℕ) : ℝ) * H (n + 1 - l) (a n) x) := by
  funext x
  unfold term
  rw [iteratedDeriv_const_mul_field (c n) (H (n + 1) (a n)), iteratedDeriv_H (n + 1) (a n) l hl]

/-- The uniform bound `|term n^{(l)}(x)| ≤ 2^{−(n+2)}` on `(−1, 1)` for `l ≤ n + 1`. -/
lemma norm_iteratedDeriv_term_le (n l : ℕ) (hl : l ≤ n + 1) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ‖iteratedDeriv l (term n) x‖ ≤ (1 / 2 : ℝ) ^ (n + 2) := by
  rw [iteratedDeriv_term n l hl, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (c_pos n), abs_of_nonneg (Nat.cast_nonneg _)]
  have hd : (((n + 2).descFactorial l : ℕ) : ℝ) ≤ ((n : ℝ) + 2) ^ (n + 2) := by
    calc (((n + 2).descFactorial l : ℕ) : ℝ) ≤ (((n + 2) ^ l : ℕ) : ℝ) := by
          exact_mod_cast Nat.descFactorial_le_pow _ _
      _ = ((n : ℝ) + 2) ^ l := by push_cast; ring
      _ ≤ ((n : ℝ) + 2) ^ (n + 2) := pow_le_pow_right₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
          (by omega)
  have hH : |H (n + 1 - l) (a n) x| ≤ 2 ^ (n + 2) := by
    refine (abs_H_le (a_pos n).le (by linarith [a_le_half n]) hx).trans ?_
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hc0 : 0 ≤ c n := (c_pos n).le
  calc c n * ((((n + 2).descFactorial l : ℕ) : ℝ) * |H (n + 1 - l) (a n) x|)
      ≤ c n * (((n : ℝ) + 2) ^ (n + 2) * 2 ^ (n + 2)) := by gcongr
    _ = (1 / 2 : ℝ) ^ (n + 2) := by
        unfold c
        rw [← mul_pow, ← mul_pow]
        congr 1
        field_simp
        ring

lemma summable_bound : Summable fun n : ℕ => (1 / 2 : ℝ) ^ (n + 2) :=
  (summable_nat_add_iff 2).2 (summable_geometric_of_lt_one (by norm_num) (by norm_num))

lemma summable_term {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : Summable fun n => term n x :=
  Summable.of_norm_bounded summable_bound fun n => by
    have := norm_iteratedDeriv_term_le n 0 (by omega) hx
    rwa [iteratedDeriv_zero] at this

/-- `C^N` of a series on an open preconnected set, from `C^N` terms with summable uniform bounds
on the derivatives up to order `N` (the set version of `contDiff_tsum`, by induction on `N`
with `contDiffOn_succ_iff_deriv_of_isOpen` and `hasDerivAt_tsum_of_isPreconnected`). -/
theorem contDiffOn_tsum_of_isOpen {s : Set ℝ} (hs : IsOpen s) (hsc : IsPreconnected s) :
    ∀ (N : ℕ) {g : ℕ → ℝ → ℝ} {u : ℕ → ℕ → ℝ}, (∀ j, ContDiffOn ℝ N (g j) s) →
      (∀ l ≤ N, Summable (u l)) → (∀ l ≤ N, ∀ j, ∀ x ∈ s, ‖iteratedDeriv l (g j) x‖ ≤ u l j) →
      ContDiffOn ℝ N (fun x => ∑' j, g j x) s
  | 0, g, u, hg, hu, hb => by
    simp only [Nat.cast_zero, contDiffOn_zero] at hg ⊢
    exact continuousOn_tsum hg (hu 0 le_rfl) fun j x hx => by
      simpa [iteratedDeriv_zero] using hb 0 le_rfl j x hx
  | N + 1, g, u, hg, hu, hb => by
    rcases s.eq_empty_or_nonempty with hse | ⟨y₀, hy₀⟩
    · rw [hse]; exact contDiffOn_empty
    have hg' : ∀ j, ContDiffOn ℝ N (deriv (g j)) s := fun j =>
      ((contDiffOn_succ_iff_deriv_of_isOpen (n := (N : WithTop ℕ∞)) hs).1
        (by exact_mod_cast hg j)).2.2
    have hder : ∀ y ∈ s, HasDerivAt (fun z => ∑' j, g j z) (∑' j, deriv (g j) y) y := by
      intro y hy
      refine hasDerivAt_tsum_of_isPreconnected (hu 1 (by omega)) hs hsc
        (fun j z hz => ?_) (fun j z hz => ?_) hy₀ ?_ hy
      · exact (((contDiffOn_succ_iff_deriv_of_isOpen (n := (N : WithTop ℕ∞)) hs).1
          (by exact_mod_cast hg j)).1.differentiableAt (hs.mem_nhds hz)).hasDerivAt
      · simpa [iteratedDeriv_one] using hb 1 (by omega) j z hz
      · exact Summable.of_norm_bounded (hu 0 (by omega)) fun j => by
          simpa [iteratedDeriv_zero] using hb 0 (by omega) j y₀ hy₀
    rw [show ((N + 1 : ℕ) : WithTop ℕ∞) = (N : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_deriv_of_isOpen hs]
    refine ⟨fun y hy => (hder y hy).differentiableAt.differentiableWithinAt,
      fun h => (WithTop.natCast_ne_top N h).elim, ?_⟩
    have ih := contDiffOn_tsum_of_isOpen hs hsc N (g := fun j => deriv (g j))
      (u := fun l => u (l + 1))
      hg' (fun l hl => hu (l + 1) (by omega)) (fun l hl j x hx => by
        rw [← iteratedDeriv_succ']; exact hb (l + 1) (by omega) j x hx)
    exact ih.congr fun y hy => (hder y hy).deriv

lemma contDiff_term (n : ℕ) : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (term n) := by
  unfold term
  exact contDiff_const.mul (contDiff_H (n + 1) (a n))

/-- `term m` is `C^N` for `N ≤ m + 1`. -/
lemma contDiffOn_term_of_le (m N : ℕ) (h : N ≤ m + 1) :
    ContDiffOn ℝ N (term m) (Ioo (-1 : ℝ) 1) := by
  have hle : (N : WithTop ℕ∞) ≤ ((m + 1 : ℕ) : WithTop ℕ∞) := Nat.cast_le.2 h
  exact ((contDiff_term m).of_le hle).contDiffOn

lemma summable_bound_shift (k : ℕ) :
    Summable fun j : ℕ => (1 / 2 : ℝ) ^ (j + (k + 1) + 2) :=
  (summable_nat_add_iff (f := fun n : ℕ => (1 / 2 : ℝ) ^ (n + 2)) (k + 1)).2 summable_bound

/-- The tail `Σ_{n ≥ k+1} term n` is `C^N` on `(−1, 1)` for `N ≤ k + 2`. -/
lemma contDiffOn_tail (k N : ℕ) (hN : N ≤ k + 2) :
    ContDiffOn ℝ N (fun x => ∑' j, term (j + (k + 1)) x) (Ioo (-1 : ℝ) 1) := by
  have h1 : ∀ j : ℕ, ContDiffOn ℝ N (term (j + (k + 1))) (Ioo (-1 : ℝ) 1) :=
    fun j => contDiffOn_term_of_le (j + (k + 1)) N (by omega)
  have h2 : ∀ l : ℕ, l ≤ N → Summable fun j : ℕ => (1 / 2 : ℝ) ^ (j + (k + 1) + 2) :=
    fun _ _ => summable_bound_shift k
  have h3 : ∀ l : ℕ, l ≤ N → ∀ j : ℕ, ∀ x ∈ Ioo (-1 : ℝ) 1,
      ‖iteratedDeriv l (term (j + (k + 1))) x‖ ≤ (1 / 2 : ℝ) ^ (j + (k + 1) + 2) :=
    fun l hl j x hx => norm_iteratedDeriv_term_le (j + (k + 1)) l (by omega) hx
  exact contDiffOn_tsum_of_isOpen isOpen_Ioo isPreconnected_Ioo N h1 h2 h3

/-- `term n` is `C^∞` away from `a n`. -/
lemma contDiffOn_term_of_ne (n : ℕ) (N : ℕ) : ContDiffOn ℝ N (term n) {x | x ≠ a n} := by
  unfold term H
  refine contDiffOn_const.mul (ContDiffOn.mul ?_ ?_)
  · exact (contDiffOn_id.sub contDiffOn_const).pow _
  · have := (contDiffOn_id.sub contDiffOn_const).abs (n := (N : ℕ∞))
      (fun x (hx : x ∈ {x : ℝ | x ≠ a n}) => sub_ne_zero.2 hx)
    exact_mod_cast this

/-- The level sets of the germ: `U_k = (−1/(k+2), 1/(k+2))`. -/
def Uk (k : ℕ) : Set ℝ := Ioo (-(1 / ((k : ℝ) + 2))) (1 / ((k : ℝ) + 2))

lemma zero_mem_Uk (k : ℕ) : (0 : ℝ) ∈ Uk k :=
  ⟨by rw [neg_lt_zero]; positivity, by positivity⟩

lemma Uk_mono {j k : ℕ} (h : j ≤ k) : Uk k ⊆ Uk j := by
  have : 1 / ((k : ℝ) + 2) ≤ 1 / ((j : ℝ) + 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (j : ℝ) ≤ k := by exact_mod_cast h
    linarith
  exact Ioo_subset_Ioo (neg_le_neg this) this

lemma Uk_subset_Ioo (k : ℕ) : Uk k ⊆ Ioo (-1 : ℝ) 1 := by
  have h1 : 1 / ((k : ℝ) + 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  exact Ioo_subset_Ioo (by linarith) (by linarith)

lemma a_not_mem_Uk {n k : ℕ} (h : n ≤ k) : a n ∉ Uk k := by
  intro ha
  have : 1 / ((k : ℝ) + 2) ≤ a n := by
    unfold a
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (n : ℝ) ≤ k := by exact_mod_cast h
    linarith
  exact absurd ha.2 (not_lt.2 this)

lemma f_eq_split (k : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    f x = ∑ n ∈ Finset.range k, term n x + ∑' n, term (n + k) x :=
  ((summable_term hx).sum_add_tsum_nat_add k).symm

/-- **`f` is `C^k` on `(−1/(k+2), 1/(k+2))`**: the terms `n ≤ k` are smooth there (their singular
points `a n ≥ 1/(k+2)` lie outside), the tail `n ≥ k + 1` is `C^{k+2}` on `(−1, 1)`. -/
theorem contDiffOn_f (k : ℕ) : ContDiffOn ℝ k f (Uk k) := by
  have h1 : ContDiffOn ℝ k (fun x => ∑ n ∈ Finset.range (k + 1), term n x) (Uk k) := by
    refine ContDiffOn.sum fun n hn => ?_
    refine (contDiffOn_term_of_ne n k).mono fun x hx hxa => ?_
    exact a_not_mem_Uk (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) (hxa ▸ hx)
  have h2 := (contDiffOn_tail k k (by omega)).mono (Uk_subset_Ioo k)
  exact (h1.add h2).congr fun x hx => f_eq_split (k + 1) (Uk_subset_Ioo k hx)

/-- **`f` is not `C^{n+2}` on any open set containing `a n`**: all the other terms are `C^{n+2}`
near `a n`, and `term n` is not. -/
theorem not_contDiffOn_f (n : ℕ) {U : Set ℝ} (hU : IsOpen U) (ha : a n ∈ U) :
    ¬ ContDiffOn ℝ (n + 2) f U := by
  intro hf
  set V : Set ℝ := U ∩ Ioo (-1) 1 ∩ ⋂ m ∈ Finset.range n, {x | x ≠ a m} with hV
  have hVo : IsOpen V :=
    (hU.inter isOpen_Ioo).inter (isOpen_biInter_finset fun m _ => isOpen_ne)
  have haV : a n ∈ V := by
    refine ⟨⟨ha, a_mem_Ioo n⟩, mem_iInter₂.2 fun m hm => ?_⟩
    exact a_injective.ne (Finset.mem_range.1 hm).ne'
  have hsplit : ∀ x ∈ Ioo (-1 : ℝ) 1,
      f x = ∑ m ∈ Finset.range n, term m x + term n x + ∑' m, term (m + (n + 1)) x := by
    intro x hx; rw [f_eq_split (n + 1) hx, Finset.sum_range_succ]
  have hhead : ContDiffOn ℝ (n + 2) (fun x => ∑ m ∈ Finset.range n, term m x) V :=
    ContDiffOn.sum fun m hm => (contDiffOn_term_of_ne m (n + 2)).mono fun x hx =>
      (mem_iInter₂.1 hx.2) m hm
  have htail : ContDiffOn ℝ (n + 2) (fun x => ∑' m, term (m + (n + 1)) x) V :=
    (contDiffOn_tail n (n + 2) le_rfl).mono fun x hx => hx.1.2
  have hterm : ContDiffOn ℝ (n + 2) (term n) V := by
    have := (hf.mono fun x hx => hx.1.1).sub (hhead.add htail)
    refine this.congr fun x hx => ?_
    rw [hsplit x hx.1.2]; ring
  have hH : ContDiffOn ℝ (n + 2) (H (n + 1) (a n)) V := by
    have := hterm.const_smul (c n)⁻¹
    refine this.congr fun x _ => ?_
    simp only [term, smul_eq_mul]
    field_simp [(c_pos n).ne']
  exact not_contDiffOn_H (n + 1) (a n) hVo haV (by exact_mod_cast hH)

/-- Every open `U ∋ 0` contains some `a n`. -/
lemma exists_a_mem {U : Set ℝ} (hU : IsOpen U) (h0 : (0 : ℝ) ∈ U) : ∃ n, a n ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n, hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (a_pos n)]
  unfold a
  calc 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    _ < ε := hn

/-! ### The constant scale `ℝ`: sc^k maps are `C^k` maps -/

/-- On the constant scales the level maps are the map itself. -/
lemma levelMap_const {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
    (g : V → V') (m : ℕ) :
    levelMap (E := ScBanach.const V) (F := ScBanach.const V') g m = g :=
  funext fun x => levelMap_eq_of_toBase_eq (by rw [ScBanach.const_toBase, ScBanach.const_toBase])

/-- An open subset of a finite-dimensional space is an sc-domain of the constant scale. -/
lemma isScDomain_const_of_isOpen {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {U : Set V} (hU : IsOpen U) : IsScDomain (ScBanach.const V) U where
  relOpenConvex m := ⟨U, univ, hU, convex_univ, by rw [ScBanach.lvlSet_const, inter_univ]⟩
  uniqueDiffWithinAt m x hx := by
    rw [ScBanach.lvlSet_const] at hx ⊢; exact hU.uniqueDiffWithinAt hx

lemma isSc0_const_of_continuousOn {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
    {U : Set V} {g : V → V'} (hg : ContinuousOn g U) :
    IsSc0 (ScBanach.const V) (ScBanach.const V') U g where
  mem_range m x _ := ⟨g ((ScBanach.const V).toBase m x), ScBanach.const_toBase _ _ _⟩
  continuousOn m := by rw [levelMap_const, ScBanach.lvlSet_const]; exact hg

/-- A `C^k` map on an open set is sc^k for the constant scales (Proposition 1.2.4 (preprint 1.19)). -/
lemma isSck_const_of_contDiffOn {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
    {U : Set V} (hU : IsOpen U) {g : V → V'} (k : ℕ) (hg : ContDiffOn ℝ k g U) :
    IsSck k (ScBanach.const V) (ScBanach.const V') U g := by
  cases k with
  | zero =>
    exact isSc0_const_of_continuousOn (by rw [Nat.cast_zero, contDiffOn_zero] at hg; exact hg)
  | succ k =>
    refine proposition_1_2_4 (isScDomain_const_of_isOpen hU)
      (isSc0_const_of_continuousOn hg.continuousOn) fun m => ?_
    rw [levelMap_const, ScBanach.lvlSet_const]
    exact_mod_cast hg

/-! ### The germ `U_m = (−1/(m+2), 1/(m+2))` and the conclusion -/

/-- The germ of neighbourhoods `U_m = (−1/(m+2), 1/(m+2))` of `0` in the constant scale `ℝ`. -/
def Gex : ScNbhdGerm (ScBanach.const ℝ) univ where
  U m := Uk m
  nested m _ hx := Uk_mono (Nat.le_succ m) hx
  zero_mem m := zero_mem_Uk m
  relOpen m := ⟨Uk m, isOpen_Ioo, by rw [ScBanach.lvlSet_univ, inter_univ]⟩

/-- **`f` is an sc-smooth germ** on `U_m = (−1/(m+2), 1/(m+2))` in the constant scale `ℝ`: for
every `j` it is sc^j on the open set `U_j` (`C^j` there), and the germ lies in `U_j` from level
`j` on (the locality lemma `isScSmoothGerm_of_levels`). -/
theorem isScSmoothGerm_f :
    IsScSmoothGerm (E := ScBanach.const ℝ) (F := ScBanach.const ℝ) Gex f := by
  refine isScSmoothGerm_of_levels (F := ScBanach.const ℝ) (isQuadrantLike_univ _) Gex f fun j => ?_
  have hUj : ∃ O : Set ((ScBanach.const ℝ) 0), IsOpen O ∧ Uk j = O ∩ univ :=
    ⟨Uk j, isOpen_Ioo, (inter_univ _).symm⟩
  have h0 : (0 : (ScBanach.const ℝ) 0) ∈ Uk j := zero_mem_Uk j
  refine ⟨ScNbhdGerm.ofSet hUj h0, fun m x hx => ?_, ?_⟩
  · rw [ScNbhdGerm.ofSet_U, ScBanach.lvlSet_const]
    exact Uk_mono (by omega) hx
  · exact IsSck.isSckGerm (isQuadrantLike_univ _) hUj h0
      (isSck_const_of_contDiffOn isOpen_Ioo j (contDiffOn_f j))

/-- **`f` is sc-smooth on no open set `U ∋ 0`**: sc^{n+2} on `U` would make it `C^{n+2}` on `U`
(Proposition 1.2.3 (preprint 1.18)), and `U` contains some `a n`. -/
theorem not_isScSmooth_f {U : Set ℝ} (hU : IsOpen U) (h0 : (0 : ℝ) ∈ U) :
    ¬ IsScSmooth (E := ScBanach.const ℝ) (F := ScBanach.const ℝ) U f := by
  intro hf
  obtain ⟨n, hn⟩ := exists_a_mem hU h0
  have h1 := (hf (n + 2)).contDiffOn_base (isScDomain_const_of_isOpen hU)
  rw [ScBanach.lvlSet_const] at h1
  have e : f ∘ ⇑((ScBanach.const ℝ).toBase (n + 2)) = f :=
    funext fun x => congrArg f (ScBanach.const_toBase ℝ _ x)
  rw [e] at h1
  exact not_contDiffOn_f n hU hn (by exact_mod_cast h1)

end GermVsChart

/-- **The example of Findings item 221, machine-checked**: in the constant scale `ℝ` there is an
sc-smooth germ (Definition 3.1.2 (preprint 3.2)) on a germ of neighbourhoods of `0` (Definition 3.1.1 (preprint 3.1), here
`U_m = (−1/(m+2), 1/(m+2))`) which is sc-smooth on no open neighbourhood of `0`.  Restricting a
chart on level `0` therefore cannot turn the text's germs into the project's whole-chart data
(round-trip items V3.9, V3.43). -/
theorem exists_isScSmoothGerm_not_isScSmooth :
    ∃ (G : ScNbhdGerm (ScBanach.const ℝ) univ) (g : ℝ → ℝ),
      IsScSmoothGerm (E := ScBanach.const ℝ) (F := ScBanach.const ℝ) G g ∧
      ∀ U : Set ℝ, IsOpen U → (0 : ℝ) ∈ U →
        ¬ IsScSmooth (E := ScBanach.const ℝ) (F := ScBanach.const ℝ) U g :=
  ⟨GermVsChart.Gex, GermVsChart.f, GermVsChart.isScSmoothGerm_f,
    fun _ hU h0 => GermVsChart.not_isScSmooth_f hU h0⟩

/-! ### Definitions 3.1.6 and 3.1.11 (preprint 3.6 and 3.11) in the text's germ reading

`fillDefect`, `IsFillingGerm`, `IsScPlusGerm` are in `Chapter3/GermFilling.lean`; the comparison
with `IsFilledVersion` and the trivial retraction are in `Chapter3/GermFillingChart.lean`. -/

/-! ### Definition 3.1.11 (preprint 3.11) in the germ reading, for sections of strong bundles

`StrongBundle.IsScFredholmGerm`, `StrongBundle.IsScFredholmGermWholeChart.isScFredholmGerm` and
`StrongBundle.isScFredholmGerm_iff_germG_wholeChart` are in `Chapter3/GermFillingChart.lean`. -/


end Polyfold
