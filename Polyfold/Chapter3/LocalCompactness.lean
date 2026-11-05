import Polyfold.Chapter3.GermIFT

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
Definition 3.7 (basic germs), Theorem 3.12 (local compactness for sc-Fredholm germs) and
Corollary 3.13 **in their local form**, which is Theorem 3.40 of §3.5 (local regularity and
compactness) together with the compactness argument the text calls "an immediate consequence".

# Local regularity and compactness of the solution set

## The text, paraphrased

(Definition 3.7) A basic germ is an sc-smooth germ `f : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W` with `f(0) = 0` whose
`W`-component is `P ∘ f(a, w) = w − B(a, w)` with `B(0, 0) = 0` and
`|B(a, w) − B(a, w')|_m ≤ ε|w − w'|_m` for `(a, w), (a, w')` close enough to `(0, 0)` on level `m`.
(Theorem 3.40) Let `f = h + s` on a relatively open `U ∋ 0` of `C`, `h` a basic germ, `s` an
sc⁺-germ with `s(0) = 0`, `S = {f = 0}`.  Then there are relatively open neighbourhoods
`U ⊃ O(0) ⊃ O(1) ⊃ …` of `0` on level `0` with `cl_{C₀}(S ∩ O(m)) ⊆ C_m` for every `m`.
(Theorem 3.12) For an sc-Fredholm germ `(f, x₀)` with `f(x₀) = 0` there are nested open
neighbourhoods `O(i)` of `x₀` in `X₀` such that `cl_{X₀}({x ∈ O(i) | f(x) = 0})` is a compact
subset of `X_i`; "an immediate consequence of Theorem 3.40".  (Corollary 3.13) If `f(x_k) = 0`
and `x_k → x` in `X₀`, then `x_k ∈ X_m` for `k` large and `x_k → x` in `X_m`, for every `m`.

## What is formalized

* `Polyfold.exists_fixedPoint_continuousOn`: the **parametrized Banach fixed point theorem** the
  text invokes in Theorems 3.29 and 3.40 (fixed point continuous in the parameter, unique in the
  contraction region).
* `Polyfold.IsBasicGerm` (**Definition 3.7**, on a germ of neighbourhoods, for a finite-dimensional
  `Q` in place of `ℝᴺ` and any quadrant-like `C̃ ⊆ P`).
* `Polyfold.IsSc0ContractionGerm.exists_lift` (**the induction of Theorem 3.40**): for the solutions
  of `w = B(a, w) − s(a, w)` with `|a|, |w|₀ ≤ τ_m`, a lift to level `m` bounded in `W_m`,
  continuous from the level-`0` topology into `E_m`.
* `Polyfold.theorem_3_40_compactness` (**Theorem 3.40 and the local Theorem 3.12**): for any
  `S ⊆ {w = B(a, w) − s(a, w)}` there are nested open neighbourhoods `O(i)` of `0` in `E₀` such
  that `cl_{E₀}(S ∩ O(i)) = ι_i(K_i)` with `K_i ⊆ E_i` compact; `theorem_3_40_regularity`
  (`S ∩ O(i) ⊆ E_i`); `theorem_3_12_local` for a basic germ plus an sc⁺-germ;
  `corollary_3_13_local` (**Corollary 3.13** for `x_k → 0`).

## What the text leaves implicit, and the choices made (the findings)

* **Theorem 3.12 and Corollary 3.13 are stated for sc-Fredholm germs on tame strong bundles over
  M-polyfolds** (Definitions 2.50, 3.4, 3.6, 3.11).  This file proves their local content, the
  local Theorem 3.40 — the solution set of a filled version, conjugated to a basic germ after
  subtracting an sc⁺-section, in a strong bundle chart.  The global statements are in
  `SectionCompactness.lean` (`Polyfold.theorem_3_12_wholeChart`, `Polyfold.corollary_3_13_wholeChart`,
  `Polyfold.corollary_3_13_section_wholeChart`, on the definitions of `StrongBundleSections.lean`): the
  passage from the local statement to the M-polyfold one goes through the chart, the filler and
  the fibre maps of the conjugating strong bundle isomorphism (`Ψ ∘ (g − s) ∘ ψ⁻¹ = 0 ⟺ g = s`,
  hence the `s` of Theorem 3.40 is the push-forward of the sc⁺-section of Definition 3.11), and
  the continuity of the inverse chart `O_i → X_i` for the level topology.
* **The compactness of Theorem 3.12 is not in Theorem 3.40**, which only states regularity
  `cl(S ∩ O(m)) ⊆ C_m`.  Compactness in `E_i` of `cl(S ∩ O(i))` needs: the solutions in `O(i)`
  lie in level `i + 1` with `|w|_{i+1}` bounded (so their `W_i`-part is precompact by the
  compactness of `W_{i+1} → W_i`), the solution set is closed, and the level-`i` lift is
  continuous for the level-`0` topology (the convergence upgrade in the proof of Theorem 3.40).
  The sets `O(i)` here are the balls of radius `τ_{i+1}`, one level ahead of the text's.
* **The induction step of Theorem 3.40 ("now clear … left to the reader")** needs more than the
  level-`1` step shows: the bound `|P ∘ s(a, w)|_{m+1} ≤ τ'_{m+1}/4` requires `(a, w)` small on
  level `m`, while `O(m+1)` only controls level `0`.  The smallness on level `m` of a solution
  comes from the continuity at `0` of the level-`m` lift `(a, w) ↦ (a, δ_m(a, P∘s(a, w)))` — the
  same continuity that gives the convergence upgrade.  So the two statements must be proved
  together, by induction (`exists_lift`): existence of the level-`m` lift, its bound, and its
  continuity from the level-`0` topology.
* **The constants.** The level-`(m+1)` contraction radius is taken so small that the level-`0`
  image of the level-`(m+1)` ball lies in the level-`0` contraction ball
  (`τ'_{m+1} < τ_0/c_{m+1}`, the text's `τ'_1 < τ_0/c_1`), so that the level-`(m+1)` fixed point
  and the given solution agree by the level-`0` uniqueness.
* **Hypotheses on the data.** `C̃` must be closed (true for partial quadrants) for the solution
  set to be closed in `E₀`; the text's closure is taken in `C₀`.  Of `f` only the `W`-component
  is used, and of it only: `B` sc⁰ with the contraction estimates (not sc-smooth), `s` sc⁰ into
  `W¹` (the sc⁺ property on every level) with `s(0) = 0`.  The `ℝᴺ`-component only shrinks `S`.
* The sets `O(i)` of the text are "relatively open neighbourhoods of `0` in `C` on level `0`"
  (Theorem 3.40) and "open neighbourhoods of `x₀` in `X₀`" (Theorem 3.12); here `O(i)` is open in
  `E₀` and `S ⊆ C₀` is arbitrary inside the solution set, which gives both.
-/

open Set Filter Topology Function Asymptotics Metric

noncomputable section

namespace Polyfold

/-! ### The parametrized Banach fixed point theorem -/

/-- **The parametrized Banach fixed point theorem** (used in Theorems 3.29 and 3.40): if
`g l : K → K` is a `1/2`-contraction on the closed nonempty `K` for every parameter `l ∈ Λ'`, and
`l ↦ g l x` is continuous on `Λ'` for every `x ∈ K`, then the fixed point `φ l ∈ K` of `g l`
depends continuously on `l ∈ Λ'`, and is the only fixed point of `g l` in `K`. -/
theorem exists_fixedPoint_continuousOn {Λ X : Type} [TopologicalSpace Λ] [MetricSpace X]
    [CompleteSpace X] {K : Set X} (hK : IsClosed K) (hne : K.Nonempty) {Λ' : Set Λ}
    {g : Λ → X → X} (hmaps : ∀ l ∈ Λ', MapsTo (g l) K K)
    (hcontr : ∀ l ∈ Λ', ∀ x ∈ K, ∀ y ∈ K, dist (g l x) (g l y) ≤ 1 / 2 * dist x y)
    (hcont : ∀ x ∈ K, ContinuousOn (fun l => g l x) Λ') :
    ∃ φ : Λ → X, (∀ l ∈ Λ', φ l ∈ K ∧ g l (φ l) = φ l) ∧ ContinuousOn φ Λ' ∧
      ∀ l ∈ Λ', ∀ x ∈ K, g l x = x → x = φ l := by
  classical
  have hex : ∀ l ∈ Λ', ∃ x ∈ K, g l x = x := by
    intro l hl
    have hsc : IsComplete K := hK.isComplete
    have hc : ContractingWith (1 / 2 : NNReal) ((hmaps l hl).restrict (g l) K K) := by
      refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
      rw [Subtype.dist_eq, Subtype.dist_eq]
      simpa using hcontr l hl x.1 x.2 y.1 y.2
    obtain ⟨y, hy, hfix, -⟩ := hc.exists_fixedPoint' hsc (hmaps l hl) hne.some_mem (edist_ne_top _ _)
    exact ⟨y, hy, hfix⟩
  have huniq : ∀ l ∈ Λ', ∀ x ∈ K, ∀ y ∈ K, g l x = x → g l y = y → x = y := by
    intro l hl x hx y hy hx' hy'
    have := hcontr l hl x hx y hy
    rw [hx', hy'] at this
    have h2 : dist x y ≤ 0 := by linarith
    exact dist_le_zero.1 h2
  set φ : Λ → X := fun l => if h : l ∈ Λ' then (hex l h).choose else hne.some with hφ
  have hφspec : ∀ l ∈ Λ', φ l ∈ K ∧ g l (φ l) = φ l := fun l hl => by
    simp only [hφ, dif_pos hl]; exact (hex l hl).choose_spec
  refine ⟨φ, hφspec, fun l hl => ?_, fun l hl x hx hfix => huniq l hl x hx _ (hφspec l hl).1 hfix
    (hφspec l hl).2⟩
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hc := hcont (φ l) (hφspec l hl).1 l hl
  rw [ContinuousWithinAt, Metric.tendsto_nhds] at hc
  filter_upwards [hc (ε / 2) (half_pos hε), self_mem_nhdsWithin] with l' h1 hl'
  have h2 := hcontr l' hl' (φ l') (hφspec l' hl').1 (φ l) (hφspec l hl).1
  rw [(hφspec l' hl').2] at h2
  have h3 : dist (φ l') (φ l) ≤ dist (φ l') (g l' (φ l)) + dist (g l' (φ l)) (φ l) :=
    dist_triangle _ _ _
  rw [(hφspec l hl).2] at h1
  linarith

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}

/-! ### Definition 3.7: basic germs -/

/-- **Definition 3.7**: `f : O(C̃ ⊕ W, 0) → Q ⊕ W` (`Q` finite-dimensional, the text's `ℝᴺ`) is a
**basic germ** if it is an sc-smooth germ with `f(0) = 0` whose `W`-component has the form
`P ∘ f(a, w) = w − B(a, w)` with `B` an sc⁰-contraction germ (Definition 3.28: `B(0, 0) = 0` and
`|B(a, w) − B(a, w')|_m ≤ ε|w − w'|_m` near `(0, 0)` on every level). -/
structure IsBasicGerm {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    (Ct : Set P) (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ))
    (f : P × W 0 → Q × W 0) (B : P × W 0 → W 0) : Prop where
  isScSmooth : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) G f
  f_zero : f 0 = 0
  snd_eq : ∀ x ∈ G.U 0, (f x).2 = x.2 - B x
  contraction : IsSc0ContractionGerm Ct G B

/-! ### The level-`m` contractions with parameter `(a, z)` -/

namespace IsSc0ContractionGerm

variable {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {B : P × W 0 → W 0}
  (h : IsSc0ContractionGerm Ct G B)

/-- The level-`m` contraction radius: within the radius of Definition 3.28, and so small that the
level-`0` image of the level-`m` ball lies in the level-`0` contraction ball
(the text's `τ'_1 < τ_0/c_1`). -/
def crad (m : ℕ) : ℝ := min (h.rad m) (h.rad 0 / (‖W.toBase m‖ + 1))

lemma crad_pos (m : ℕ) : 0 < h.crad m :=
  lt_min (h.rad_pos m) (div_pos (h.rad_pos 0) (by positivity))

lemma crad_le (m : ℕ) : h.crad m ≤ h.rad m := min_le_left _ _

lemma crad_zero_le : h.crad 0 ≤ h.rad 0 := h.crad_le 0

lemma norm_toBase_lt_rad {m : ℕ} {y : W m} (hy : ‖y‖ ≤ h.crad m / 2) : ‖W.toBase m y‖ < h.rad 0 := by
  have h1 : h.crad m ≤ h.rad 0 / (‖W.toBase m‖ + 1) := min_le_right _ _
  have hr := h.rad_pos 0
  calc ‖W.toBase m y‖ ≤ ‖W.toBase m‖ * ‖y‖ := (W.toBase m).le_opNorm y
    _ ≤ (‖W.toBase m‖ + 1) * (h.rad 0 / (‖W.toBase m‖ + 1) / 2) := by
        gcongr
        · linarith [norm_nonneg (W.toBase m)]
        · exact hy.trans (by gcongr)
    _ = h.rad 0 / 2 := by field_simp
    _ < h.rad 0 := by linarith

/-- `(a, w) ∈ U_m` for `a ∈ C̃`, `|a| < r_m`, `|w|_m < r_m`. -/
lemma mem_G_of_lt {m : ℕ} {a : P} (ha : a ∈ Ct) (ha' : ‖a‖ < h.rad m) {w : W m}
    (hw : ‖w‖ < h.rad m) : ((a, w) : (ScBanach.paramProd P W) m) ∈ G.U m :=
  (h.rad_spec m a ha ha' w w hw hw).1

/-- The level-`m` contraction estimate. -/
lemma contr_of_lt {m : ℕ} {a : P} (ha : a ∈ Ct) (ha' : ‖a‖ < h.rad m) {w w' : W m}
    (hw : ‖w‖ < h.rad m) (hw' : ‖w'‖ < h.rad m) :
    ‖levelB B m (a, w) - levelB B m (a, w')‖ ≤ 1 / 2 * ‖w - w'‖ :=
  (h.rad_spec m a ha ha' w w' hw hw').2

/-- A radius `ρ_m ≤ r_m` with `|B_m(a, 0)|_m ≤ r_m/8` for `a ∈ C̃`, `|a| < ρ_m`. -/
lemma exists_cprad (m : ℕ) : ∃ ρ > 0, ρ ≤ h.crad m ∧
    ∀ a ∈ Ct, ‖a‖ < ρ → ‖levelB B m (a, 0)‖ ≤ h.crad m / 8 := by
  have hc := h.isSc0.continuousOn m 0 (G.zero_mem m)
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨ρ, hρ, hρ'⟩ := hc (h.crad m / 8) (by have := h.crad_pos m; positivity)
  refine ⟨min ρ (h.crad m), lt_min hρ (h.crad_pos m), min_le_right _ _, fun a ha haρ => ?_⟩
  have ha1 : ‖a‖ < h.rad m := (haρ.trans_le (min_le_right _ _)).trans_le (h.crad_le m)
  have hmem : ((a, (0 : W m)) : (ScBanach.paramProd P W) m) ∈ G.U m :=
    h.mem_G_of_lt ha ha1 (by rw [norm_zero]; exact h.rad_pos m)
  have := hρ' hmem (by
    rw [dist_zero_right, Prod.norm_mk, norm_zero]
    exact (max_eq_left (norm_nonneg a)).le.trans_lt (haρ.trans_le (min_le_left _ _)))
  rw [dist_eq_norm, h.levelB_zero_eq, sub_zero] at this
  exact this.le

include h in
/-- The parameter radius `ρ_m` of `exists_cprad`. -/
def cprad (m : ℕ) : ℝ := (h.exists_cprad m).choose

lemma cprad_pos (m : ℕ) : 0 < h.cprad m := (h.exists_cprad m).choose_spec.1

lemma cprad_le (m : ℕ) : h.cprad m ≤ h.crad m := (h.exists_cprad m).choose_spec.2.1

lemma cprad_spec (m : ℕ) : ∀ a ∈ Ct, ‖a‖ < h.cprad m → ‖levelB B m (a, 0)‖ ≤ h.crad m / 8 :=
  (h.exists_cprad m).choose_spec.2.2

include h in
/-- The parameter region `Σ_m = {(a, z) | a ∈ C̃, |a| < ρ_m, |z|_m ≤ r_m/8}` of the level-`m`
contraction `w ↦ B_m(a, w) − z` on the closed ball `K_m = B̄_m(r_m/2)`. -/
def Sigma (m : ℕ) : Set (P × W m) := {p | p.1 ∈ Ct ∧ ‖p.1‖ < h.cprad m ∧ ‖p.2‖ ≤ h.crad m / 8}

include h in
/-- The closed ball `K_m = B̄_m(r_m/2)` of the level-`m` contraction. -/
def cBall (m : ℕ) : Set (W m) := Metric.closedBall 0 (h.crad m / 2)

/-- The level-`m` contraction with parameter `(a, z)`: `w ↦ B_m(a, w) − z`. -/
def gmap (B₀ : P × W 0 → W 0) (m : ℕ) (p : P × W m) (w : W m) : W m := levelB B₀ m (p.1, w) - p.2

lemma gmap_mapsTo {m : ℕ} {p : P × W m} (hp : p ∈ h.Sigma m) :
    MapsTo (gmap B m p) (h.cBall m) (h.cBall m) := by
  intro w hw
  rw [cBall, Metric.mem_closedBall, dist_zero_right] at hw ⊢
  have hr := h.crad_pos m
  have ha' : ‖p.1‖ < h.rad m := (hp.2.1.trans_le (h.cprad_le m)).trans_le (h.crad_le m)
  have hw' : ‖w‖ < h.rad m := (hw.trans_lt (by linarith)).trans_le (h.crad_le m)
  have h0 : ‖(0 : W m)‖ < h.rad m := by rw [norm_zero]; exact h.rad_pos m
  have hc := h.contr_of_lt hp.1 ha' hw' h0
  rw [sub_zero] at hc
  have hB0 := h.cprad_spec m p.1 hp.1 hp.2.1
  calc ‖gmap B m p w‖ = ‖levelB B m (p.1, w) - p.2‖ := rfl
    _ ≤ ‖levelB B m (p.1, w) - levelB B m (p.1, 0)‖ + ‖levelB B m (p.1, 0)‖ + ‖p.2‖ := by
        have h1 := norm_sub_le (levelB B m (p.1, w)) p.2
        have h2 := norm_le_norm_sub_add (levelB B m (p.1, w)) (levelB B m (p.1, 0))
        linarith
    _ ≤ 1 / 2 * (h.crad m / 2) + h.crad m / 8 + h.crad m / 8 := by
        have h4 : ‖levelB B m (p.1, w) - levelB B m (p.1, 0)‖ ≤ 1 / 2 * (h.crad m / 2) :=
          hc.trans (by linarith)
        linarith [hp.2.2]
    _ = h.crad m / 2 := by ring

lemma gmap_contr {m : ℕ} {p : P × W m} (hp : p ∈ h.Sigma m) {w w' : W m} (hw : w ∈ h.cBall m)
    (hw' : w' ∈ h.cBall m) : dist (gmap B m p w) (gmap B m p w') ≤ 1 / 2 * dist w w' := by
  rw [cBall, Metric.mem_closedBall, dist_zero_right] at hw hw'
  have hr := h.crad_pos m
  have ha' : ‖p.1‖ < h.rad m := (hp.2.1.trans_le (h.cprad_le m)).trans_le (h.crad_le m)
  rw [dist_eq_norm, dist_eq_norm, gmap, gmap, sub_sub_sub_cancel_right]
  exact h.contr_of_lt hp.1 ha' ((hw.trans_lt (by linarith)).trans_le (h.crad_le m))
    ((hw'.trans_lt (by linarith)).trans_le (h.crad_le m))

lemma gmap_continuousOn {m : ℕ} {w : W m} (hw : w ∈ h.cBall m) :
    ContinuousOn (fun p => gmap B m p w) (h.Sigma m) := by
  rw [cBall, Metric.mem_closedBall, dist_zero_right] at hw
  have hr := h.crad_pos m
  refine ContinuousOn.sub ?_ continuousOn_snd
  refine (h.isSc0.continuousOn m).comp (f := fun p : P × W m => ((p.1, w) : (ScBanach.paramProd P W) m))
    (Continuous.continuousOn (by fun_prop)) fun p hp => ?_
  exact h.mem_G_of_lt hp.1 ((hp.2.1.trans_le (h.cprad_le m)).trans_le (h.crad_le m))
    ((hw.trans_lt (by linarith)).trans_le (h.crad_le m))

/-- **The level-`m` fixed point `δ_m(a, z)` of Theorem 3.40**: the solution of
`w = B_m(a, w) − z` in `K_m`, continuous on `Σ_m`, unique in `K_m`. -/
lemma exists_delta (m : ℕ) : ∃ δ : P × W m → W m,
    (∀ p ∈ h.Sigma m, δ p ∈ h.cBall m ∧ gmap B m p (δ p) = δ p) ∧
      ContinuousOn δ (h.Sigma m) ∧ ∀ p ∈ h.Sigma m, ∀ w ∈ h.cBall m, gmap B m p w = w → w = δ p :=
  exists_fixedPoint_continuousOn Metric.isClosed_closedBall
    ⟨0, Metric.mem_closedBall_self (by have := h.crad_pos m; positivity)⟩
    (fun p hp => h.gmap_mapsTo hp) (fun p hp w hw w' hw' => h.gmap_contr hp hw hw')
    fun w hw => h.gmap_continuousOn hw

include h in
/-- The level-`m` fixed point `δ_m : P × W_m → W_m`. -/
def delta (m : ℕ) : P × W m → W m := (h.exists_delta m).choose

lemma delta_mem {m : ℕ} {p : P × W m} (hp : p ∈ h.Sigma m) : h.delta m p ∈ h.cBall m :=
  ((h.exists_delta m).choose_spec.1 p hp).1

lemma norm_delta_le {m : ℕ} {p : P × W m} (hp : p ∈ h.Sigma m) : ‖h.delta m p‖ ≤ h.crad m / 2 := by
  have := h.delta_mem hp
  rwa [cBall, Metric.mem_closedBall, dist_zero_right] at this

lemma delta_fixed {m : ℕ} {p : P × W m} (hp : p ∈ h.Sigma m) :
    levelB B m (p.1, h.delta m p) - p.2 = h.delta m p :=
  ((h.exists_delta m).choose_spec.1 p hp).2

lemma delta_continuousOn (m : ℕ) : ContinuousOn (h.delta m) (h.Sigma m) :=
  (h.exists_delta m).choose_spec.2.1

end IsSc0ContractionGerm

/-! ### The solution set and its level-`m` lifts (the induction of Theorem 3.40) -/

/-- The solutions of `w = B(a, w) − s(a, w)` with `a ∈ C̃`, `|a| ≤ τ`, `|w|₀ ≤ τ`. -/
def solSet (Ct : Set P) (B : P × W 0 → W 0) (s : P × W 0 → W 1) (τ : ℝ) :
    Set ((ScBanach.paramProd P W) 0) :=
  {x | x.1 ∈ Ct ∧ ‖x.1‖ ≤ τ ∧ ‖x.2‖ ≤ τ ∧ x.2 = B x - W.toBase 1 (s x)}

lemma solSet_mono {B : P × W 0 → W 0} {s : P × W 0 → W 1} {τ τ' : ℝ} (hτ : τ ≤ τ') :
    solSet Ct B s τ ⊆ solSet Ct B s τ' :=
  fun _ hx => ⟨hx.1, hx.2.1.trans hτ, hx.2.2.1.trans hτ, hx.2.2.2⟩

/-- `s_m(0) = 0`. -/
lemma levelMap_s_zero {s : P × W 0 → W 1} (hs0 : s 0 = 0) (m : ℕ) :
    levelMap (E := ScBanach.paramProd P W) (F := W.shift) s m 0 = 0 := by
  apply levelMap_eq_of_toBase_eq
  rw [map_zero, map_zero, hs0]

namespace IsSc0ContractionGerm

variable {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {B : P × W 0 → W 0}
  (h : IsSc0ContractionGerm Ct G B) {s : P × W 0 → W 1}

lemma solSet_subset_G {τ : ℝ} (hτ : τ ≤ h.crad 0 / 2) {x : (ScBanach.paramProd P W) 0}
    (hx : x ∈ solSet Ct B s τ) : x ∈ G.U 0 := by
  have hr := h.crad_pos 0
  have h0 := h.crad_zero_le
  exact h.mem_G_of_lt (m := 0) hx.1 (by linarith [hx.2.1]) (w := x.2) (by linarith [hx.2.2.1])

include h in
lemma zero_mem_solSet (hs0 : s 0 = 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    (0 : (ScBanach.paramProd P W) 0) ∈ solSet Ct B s τ := by
  refine ⟨?_, by show ‖(0 : P)‖ ≤ τ; rw [norm_zero]; exact hτ,
    by show ‖(0 : W 0)‖ ≤ τ; rw [norm_zero]; exact hτ, ?_⟩
  · have := G.U_subset 0 (G.zero_mem 0)
    rw [ScBanach.lvlSet_zero] at this
    exact this.1
  · show (0 : W 0) = B 0 - W.toBase 1 (s 0)
    rw [hs0, map_zero, sub_zero]
    exact h.B_zero.symm

lemma isClosed_solSet (hCt : IsClosed Ct) (hs : IsSc0Germ (F := W.shift) G s) {τ : ℝ}
    (hτ : τ ≤ h.crad 0 / 2) : IsClosed (solSet Ct B s τ) := by
  have hA : IsClosed {x : (ScBanach.paramProd P W) 0 | x.1 ∈ Ct ∧ ‖x.1‖ ≤ τ ∧ ‖x.2‖ ≤ τ} := by
    refine IsClosed.inter (hCt.preimage continuous_fst) (IsClosed.inter ?_ ?_)
    · exact isClosed_le (continuous_norm.comp continuous_fst) continuous_const
    · exact isClosed_le (continuous_norm.comp continuous_snd) continuous_const
  have hsub : {x : (ScBanach.paramProd P W) 0 | x.1 ∈ Ct ∧ ‖x.1‖ ≤ τ ∧ ‖x.2‖ ≤ τ} ⊆ G.U 0 := by
    intro x hx
    have hr := h.crad_pos 0
    have h0 := h.crad_zero_le
    exact h.mem_G_of_lt (m := 0) hx.1 (by linarith [hx.2.1]) (w := x.2) (by linarith [hx.2.2])
  have hcont : ContinuousOn (fun x : (ScBanach.paramProd P W) 0 => x.2 - (B x - W.toBase 1 (s x)))
      {x | x.1 ∈ Ct ∧ ‖x.1‖ ≤ τ ∧ ‖x.2‖ ≤ τ} := by
    refine continuousOn_snd.sub ((h.isSc0.continuousOn_base.mono hsub).sub ?_)
    exact (W.toBase 1).continuous.comp_continuousOn (hs.continuousOn_base.mono hsub)
  have := hcont.preimage_isClosed_of_isClosed hA (isClosed_singleton (x := (0 : W 0)))
  convert this using 1
  ext x
  simp only [solSet, Set.mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, sub_eq_zero]
  tauto

/-- **The induction of Theorem 3.40**: for every `m` there is `τ_m > 0` and a lift
`L_m : E₀ → E_m` such that for every solution `x = (a, w)` with `a ∈ C̃`, `|a|, |w|₀ ≤ τ_m`:
`ι_m(L_m x) = x`, `L_m x ∈ U_m`, `|(L_m x)_W|_m ≤ r_m/2`, and `L_m` is continuous on this
solution set for the level-`0` topology.  Step `m → m+1`: `L_{m+1} x = (a, δ_{m+1}(a, s_m(L_m x)))`
with `τ_{m+1}` so small that `|s_m(L_m x)|_{m+1} ≤ r_{m+1}/8` (continuity of `L_m` and of `s_m`
at `0`); `ι_{m+1}(L_{m+1} x) = x` by the level-`0` uniqueness. -/
theorem exists_lift (hCt : IsClosed Ct) (hs : IsSc0Germ (F := W.shift) G s) (hs0 : s 0 = 0) :
    ∀ m : ℕ, ∃ τ > 0, τ ≤ h.crad 0 / 2 ∧ ∃ L : (ScBanach.paramProd P W) 0 → (ScBanach.paramProd P W) m,
      (∀ x ∈ solSet Ct B s τ, (ScBanach.paramProd P W).toBase m (L x) = x ∧ L x ∈ G.U m ∧
        ‖(L x).2‖ ≤ h.crad m / 2) ∧ ContinuousOn L (solSet Ct B s τ)
  | 0 => by
    refine ⟨h.crad 0 / 2, by have := h.crad_pos 0; positivity, le_rfl, id, fun x hx => ?_,
      continuousOn_id⟩
    exact ⟨rfl, h.solSet_subset_G le_rfl hx, hx.2.2.1⟩
  | m + 1 => by
    obtain ⟨τ, hτ, hτ0, L, hL, hLc⟩ := exists_lift hCt hs hs0 m
    have hr : 0 < h.crad (m + 1) := h.crad_pos (m + 1)
    have hρ : 0 < h.cprad (m + 1) := h.cprad_pos (m + 1)
    -- continuity of `s_m` at `0` within `U_m`
    have hsc := hs.continuousOn m 0 (G.zero_mem m)
    rw [Metric.continuousWithinAt_iff] at hsc
    obtain ⟨η, hη, hη'⟩ := hsc (h.crad (m + 1) / 8) (by positivity)
    -- continuity of `L` at `0` within the solution set
    have hL0 : L 0 = 0 := by
      apply (ScBanach.paramProd P W).toBase_injective m
      rw [(hL 0 (h.zero_mem_solSet hs0 hτ.le)).1, map_zero]
    have hLc0 := hLc 0 (h.zero_mem_solSet hs0 hτ.le)
    rw [Metric.continuousWithinAt_iff] at hLc0
    obtain ⟨θ, hθ, hθ'⟩ := hLc0 η hη
    set τ' := min τ (min (h.cprad (m + 1) / 2) (θ / 2)) with hτ'_def
    have hτ'pos : 0 < τ' := lt_min hτ (lt_min (by positivity) (by positivity))
    have hτ'τ : τ' ≤ τ := min_le_left _ _
    have hτ'ρ : τ' < h.cprad (m + 1) :=
      lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
    have hτ'θ : τ' < θ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
    -- the data at a solution `x`
    have key : ∀ x ∈ solSet Ct B s τ', (L x).1 = x.1 ∧ L x ∈ G.U m ∧
        ((L x).1, levelMap (E := ScBanach.paramProd P W) (F := W.shift) s m (L x)) ∈ h.Sigma (m + 1) := by
      intro x hx
      have hx' : x ∈ solSet Ct B s τ := solSet_mono hτ'τ hx
      obtain ⟨hLx, hLU, -⟩ := hL x hx'
      have ha : (L x).1 = x.1 := by
        have := congrArg Prod.fst hLx
        rwa [ScBanach.paramProd_toBase] at this
      refine ⟨ha, hLU, ?_⟩
      have hxθ : dist x 0 < θ := by
        rw [dist_zero_right, Prod.norm_def]
        exact lt_of_le_of_lt (max_le hx.2.1 hx.2.2.1) hτ'θ
      have hLη : dist (L x) (L 0) < η := hθ' hx' hxθ
      rw [hL0, dist_zero_right] at hLη
      have hsη := hη' hLU (by rwa [dist_zero_right])
      rw [levelMap_s_zero hs0 m, dist_zero_right] at hsη
      exact ⟨ha ▸ hx.1, by rw [ha]; exact lt_of_le_of_lt hx.2.1 hτ'ρ, hsη.le⟩
    refine ⟨τ', hτ'pos, hτ'τ.trans hτ0,
      fun x => ((L x).1, h.delta (m + 1) ((L x).1, levelMap (E := ScBanach.paramProd P W) (F := W.shift) s m (L x))),
      fun x hx => ?_, ?_⟩
    · obtain ⟨ha, hLU, hSig⟩ := key x hx
      have hx' : x ∈ solSet Ct B s τ := solSet_mono hτ'τ hx
      rw [ha] at hSig
      set z := levelMap (E := ScBanach.paramProd P W) (F := W.shift) s m (L x) with hz
      have hdK := h.norm_delta_le hSig
      have hdfix := h.delta_fixed hSig
      simp only at hdfix
      have hdU : ((x.1, h.delta (m + 1) (x.1, z)) : (ScBanach.paramProd P W) (m + 1)) ∈ G.U (m + 1) :=
        h.mem_G_of_lt hSig.1 ((hSig.2.1.trans_le (h.cprad_le _)).trans_le (h.crad_le _))
          ((hdK.trans_lt (by linarith)).trans_le (h.crad_le _))
      refine ⟨?_, ?_, ?_⟩
      rotate_left
      · show ((L x).1, h.delta (m + 1) ((L x).1, z)) ∈ G.U (m + 1)
        rw [ha]; exact hdU
      · show ‖h.delta (m + 1) ((L x).1, z)‖ ≤ h.crad (m + 1) / 2
        rw [ha]; exact hdK
      -- `ι_{m+1}(a, d) = (a, w)` by the level-`0` uniqueness
      show (ScBanach.paramProd P W).toBase (m + 1) ((L x).1, h.delta (m + 1) ((L x).1, z)) = x
      rw [ScBanach.paramProd_toBase, ha]
      refine Prod.ext rfl ?_
      show W.toBase (m + 1) (h.delta (m + 1) (x.1, z)) = x.2
      set d := h.delta (m + 1) (x.1, z) with hd
      -- `w' = B(a, w') − s(x)` for `w' = ι_{m+1} d`
      have hz0 : W.toBase (m + 1) z = W.toBase 1 (s x) := by
        rw [W.shift_toBase, hz, hs.toBase_levelMap hLU, (hL x hx').1]
      have hw'eq : W.toBase (m + 1) d = B (x.1, W.toBase (m + 1) d) - W.toBase 1 (s x) := by
        have := congrArg (W.toBase (m + 1)) hdfix
        rw [map_sub, h.isSc0.toBase_levelMap hdU, ScBanach.paramProd_toBase, hz0] at this
        exact this.symm
      have hxeq : x.2 = B (x.1, x.2) - W.toBase 1 (s x) := hx.2.2.2
      -- both lie in the level-`0` contraction ball
      have hr0 := h.rad_pos 0
      have h0 := h.crad_zero_le
      have hx2 : ‖x.2‖ < h.rad 0 := by linarith [hx.2.2.1, hτ'τ, hτ0]
      have hw'0 : ‖W.toBase (m + 1) d‖ < h.rad 0 := h.norm_toBase_lt_rad hdK
      have ha0 : ‖x.1‖ < h.rad 0 := by linarith [hx.2.1, hτ'τ, hτ0]
      have hc := h.contr_of_lt (m := 0) hx.1 ha0 hx2 hw'0
      rw [levelB_zero, levelB_zero] at hc
      have hdiff : x.2 - W.toBase (m + 1) d = B (x.1, x.2) - B (x.1, W.toBase (m + 1) d) :=
        calc x.2 - W.toBase (m + 1) d
            = (B (x.1, x.2) - W.toBase 1 (s x)) - (B (x.1, W.toBase (m + 1) d) - W.toBase 1 (s x)) := by
              rw [← hxeq, ← hw'eq]
          _ = B (x.1, x.2) - B (x.1, W.toBase (m + 1) d) := sub_sub_sub_cancel_right _ _ _
      rw [← hdiff] at hc
      have h2 : ‖x.2 - W.toBase (m + 1) d‖ ≤ 0 := by linarith
      exact (sub_eq_zero.1 (norm_le_zero_iff.1 h2)).symm
    · -- continuity of the lift
      have hsub : solSet Ct B s τ' ⊆ solSet Ct B s τ := solSet_mono hτ'τ
      refine ContinuousOn.prodMk (continuous_fst.comp_continuousOn (hLc.mono hsub)) ?_
      refine (h.delta_continuousOn (m + 1)).comp ?_ fun x hx => (key x hx).2.2
      refine ContinuousOn.prodMk (continuous_fst.comp_continuousOn (hLc.mono hsub)) ?_
      exact (hs.continuousOn m).comp (hLc.mono hsub) fun x hx => (key x hx).2.1

end IsSc0ContractionGerm

/-! ### Theorem 3.40 and the local Theorem 3.12 -/

variable {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {B : P × W 0 → W 0}
  {s : P × W 0 → W 1}

/-- `ι_m : W_m → W₀` is a compact operator for `m ≥ 1`. -/
lemma ScBanach.toBase_succ_isCompactOperator (W : ScBanach) (m : ℕ) :
    IsCompactOperator (W.toBase (m + 1)) :=
  (W.incl_isCompactOperator m).clm_comp (W.toBase m)

/-- The compactness of the set of level-`(m+1)` lifts: a sequence of lifts has a subsequence
converging in `E_{m+1}`, because the parameters lie in a compact ball of `P`, the `W₀`-parts in
the compact image of a `W_{m+1}`-ball, and the lift is continuous for the level-`0` topology. -/
lemma IsSc0ContractionGerm.isCompact_lift_image (h : IsSc0ContractionGerm Ct G B)
    (hCt : IsClosed Ct) (hs : IsSc0Germ (F := W.shift) G s) {m : ℕ} {τ : ℝ} (hτ0 : τ ≤ h.crad 0 / 2)
    {L : (ScBanach.paramProd P W) 0 → (ScBanach.paramProd P W) (m + 1)}
    (hL : ∀ x ∈ solSet Ct B s τ, (ScBanach.paramProd P W).toBase (m + 1) (L x) = x ∧
      L x ∈ G.U (m + 1) ∧ ‖(L x).2‖ ≤ h.crad (m + 1) / 2)
    (hLc : ContinuousOn L (solSet Ct B s τ)) : IsCompact (L '' solSet Ct B s τ) := by
  obtain ⟨Kc, hKc, hKc'⟩ := (W.toBase_succ_isCompactOperator m).image_closedBall_subset_compact
    (f := (W.toBase (m + 1) : W (m + 1) →ₗ[ℝ] W 0)) (h.crad (m + 1) / 2)
  have hcl := h.isClosed_solSet hCt hs hτ0
  refine IsSeqCompact.isCompact fun y hy => ?_
  choose x hx hxy using hy
  have hmem : ∀ n, x n ∈ (Metric.closedBall (0 : P) τ ×ˢ Kc : Set (P × W 0)) := by
    intro n
    refine ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact (hx n).2.1, hKc' ⟨(L (x n)).2, ?_, ?_⟩⟩
    · rw [Metric.mem_closedBall, dist_zero_right]; exact (hL _ (hx n)).2.2
    · have := congrArg Prod.snd (hL _ (hx n)).1
      rwa [ScBanach.paramProd_toBase] at this
  obtain ⟨xl, -, φ, hφ, hlim⟩ := ((isCompact_closedBall (0 : P) τ).prod hKc).tendsto_subseq hmem
  have hxl : xl ∈ solSet Ct B s τ :=
    hcl.mem_of_tendsto hlim (Eventually.of_forall fun n => hx (φ n))
  refine ⟨L xl, ⟨xl, hxl, rfl⟩, φ, hφ, ?_⟩
  have h1 : Tendsto (x ∘ φ) atTop (𝓝[solSet Ct B s τ] xl) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hx (φ n)⟩
  have h2 := (hLc xl hxl).tendsto.comp h1
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply, hxy]

/-- **Theorem 3.40 (local regularity and compactness), with the compactness of Theorem 3.12**:
let `B` be an sc⁰-contraction germ on `O(C̃ ⊕ W, 0)` (`C̃` closed), `s` an sc⁺-germ (`s : U_m → W_{m+1}`
continuous on every level) with `s(0) = 0`, and `S` any set of solutions of `w = B(a, w) − s(a, w)`
in `U₀`.  Then there are nested open neighbourhoods `O(i)` of `0` in `E₀` such that for every
`i` the closure of `S ∩ O(i)` in `E₀` is `ι_i(K_i)` for a compact `K_i ⊆ E_i`; in particular
`S ∩ O(i) ⊆ E_i`. -/
theorem theorem_3_40_compactness (h : IsSc0ContractionGerm Ct G B) (hCt : IsClosed Ct)
    (hs : IsSc0Germ (F := W.shift) G s) (hs0 : s 0 = 0) {S : Set ((ScBanach.paramProd P W) 0)}
    (hS : ∀ x ∈ S, x ∈ G.U 0 ∧ x.2 = B x - W.toBase 1 (s x)) :
    ∃ O : ℕ → Set ((ScBanach.paramProd P W) 0), (∀ i, IsOpen (O i)) ∧ (∀ i, (0 : P × W 0) ∈ O i) ∧
      (∀ i, O (i + 1) ⊆ O i) ∧
      ∀ i, ∃ K : Set ((ScBanach.paramProd P W) i), IsCompact K ∧
        closure (S ∩ O i) = (ScBanach.paramProd P W).toBase i '' K := by
  classical
  have hlift := h.exists_lift hCt hs hs0
  choose τ hτpos hτ0 L hL hLc using hlift
  -- decreasing radii `ρ i ≤ τ (i + 1)`
  let ρ : ℕ → ℝ := fun i => Nat.rec (τ 1) (fun i r => min r (τ (i + 2))) i
  have hρ_succ : ∀ i, ρ (i + 1) = min (ρ i) (τ (i + 2)) := fun i => rfl
  have hρpos : ∀ i, 0 < ρ i := by
    intro i; induction i with
    | zero => exact hτpos 1
    | succ i ih => rw [hρ_succ]; exact lt_min ih (hτpos _)
  have hρle : ∀ i, ρ i ≤ τ (i + 1) := by
    intro i; cases i with
    | zero => exact le_rfl
    | succ i => rw [hρ_succ]; exact min_le_right _ _
  have hρanti : ∀ i, ρ (i + 1) ≤ ρ i := fun i => by rw [hρ_succ]; exact min_le_left _ _
  refine ⟨fun i => Metric.ball (0 : P) (ρ i) ×ˢ Metric.ball (0 : W 0) (ρ i),
    fun i => Metric.isOpen_ball.prod Metric.isOpen_ball,
    fun i => ⟨Metric.mem_ball_self (hρpos i), Metric.mem_ball_self (hρpos i)⟩,
    fun i => prod_mono (Metric.ball_subset_ball (hρanti i)) (Metric.ball_subset_ball (hρanti i)),
    fun i => ?_⟩
  -- the solutions in `O(i)` lie in the closed solution set of radius `τ (i+1)`
  have hsub : S ∩ (Metric.ball (0 : P) (ρ i) ×ˢ Metric.ball (0 : W 0) (ρ i)) ⊆
      solSet Ct B s (τ (i + 1)) := by
    intro x ⟨hxS, hxO⟩
    obtain ⟨hxU, hxeq⟩ := hS x hxS
    have hCt' : x.1 ∈ Ct := by
      have := G.U_subset 0 hxU
      rw [ScBanach.lvlSet_zero] at this
      exact this.1
    rw [mem_prod, Metric.mem_ball, Metric.mem_ball, dist_zero_right, dist_zero_right] at hxO
    exact ⟨hCt', (hxO.1.trans_le (hρle i)).le, (hxO.2.trans_le (hρle i)).le, hxeq⟩
  have hcl : closure (S ∩ (Metric.ball (0 : P) (ρ i) ×ˢ Metric.ball (0 : W 0) (ρ i))) ⊆
      solSet Ct B s (τ (i + 1)) :=
    (h.isClosed_solSet hCt hs (hτ0 _)).closure_subset_iff.2 hsub
  -- the compact set of lifts on level `i + 1`, pushed to level `i`
  have hK' := h.isCompact_lift_image hCt hs (hτ0 (i + 1)) (hL (i + 1)) (hLc (i + 1))
  set Cl := closure (S ∩ (Metric.ball (0 : P) (ρ i) ×ˢ Metric.ball (0 : W 0) (ρ i))) with hCl
  refine ⟨(ScBanach.paramProd P W).incl i '' (L (i + 1) '' solSet Ct B s (τ (i + 1))) ∩ (ScBanach.paramProd P W).toBase i ⁻¹' Cl,
    (hK'.image ((ScBanach.paramProd P W).incl i).continuous).inter_right (isClosed_closure.preimage ((ScBanach.paramProd P W).toBase i).continuous),
    ?_⟩
  rw [image_inter_preimage, image_image, image_image]
  have himg : ∀ x ∈ solSet Ct B s (τ (i + 1)),
      (ScBanach.paramProd P W).toBase i ((ScBanach.paramProd P W).incl i (L (i + 1) x)) = x :=
    fun x hx => (hL (i + 1) x hx).1
  refine (subset_inter (fun x hx => ?_) subset_rfl).antisymm inter_subset_right
  exact ⟨x, hcl hx, himg x (hcl hx)⟩

/-- **Theorem 3.40, the regularity statement**: `S ∩ O(i) ⊆ E_i` (indeed `cl(S ∩ O(i)) ⊆ E_i`). -/
theorem theorem_3_40_regularity (h : IsSc0ContractionGerm Ct G B) (hCt : IsClosed Ct)
    (hs : IsSc0Germ (F := W.shift) G s) (hs0 : s 0 = 0) {S : Set ((ScBanach.paramProd P W) 0)}
    (hS : ∀ x ∈ S, x ∈ G.U 0 ∧ x.2 = B x - W.toBase 1 (s x)) :
    ∃ O : ℕ → Set ((ScBanach.paramProd P W) 0), (∀ i, IsOpen (O i)) ∧ (∀ i, (0 : P × W 0) ∈ O i) ∧
      (∀ i, O (i + 1) ⊆ O i) ∧
      ∀ i, ∀ x ∈ closure (S ∩ O i), x ∈ range ((ScBanach.paramProd P W).toBase i) := by
  obtain ⟨O, hO, h0, hnest, hK⟩ := theorem_3_40_compactness h hCt hs hs0 hS
  refine ⟨O, hO, h0, hnest, fun i x hx => ?_⟩
  obtain ⟨K, -, hKeq⟩ := hK i
  rw [hKeq] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact ⟨y, rfl⟩

/-- **Theorem 3.12 in its local form** (the solution set of a basic germ plus an sc⁺-germ, the
local model of an sc-Fredholm germ by Definition 3.11): for a basic germ `f : O(C̃ ⊕ W, 0) → Q ⊕ W`
(`C̃` closed) and an sc⁺-germ `s` with `s(0) = 0`, there are nested open neighbourhoods `O(i)` of
`0` such that the `E₀`-closure of `{x ∈ O(i) | f(x) + s(x) = 0}` is a compact subset of `E_i`. -/
theorem theorem_3_12_local {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [FiniteDimensional ℝ Q] {f : P × W 0 → Q × W 0} (hf : IsBasicGerm Ct G f B) (hCt : IsClosed Ct)
    {s : P × W 0 → Q × W 1}
    (hs : IsSc0Germ (E := ScBanach.paramProd P W) (F := (ScBanach.paramProd Q W).shift) G s)
    (hs0 : s 0 = 0) :
    ∃ O : ℕ → Set ((ScBanach.paramProd P W) 0), (∀ i, IsOpen (O i)) ∧ (∀ i, (0 : P × W 0) ∈ O i) ∧
      (∀ i, O (i + 1) ⊆ O i) ∧
      ∀ i, ∃ K : Set ((ScBanach.paramProd P W) i), IsCompact K ∧
        closure ({x ∈ G.U 0 | f x + ((ScBanach.paramProd Q W).toBase 1 (s x)) = 0} ∩ O i) =
          (ScBanach.paramProd P W).toBase i '' K := by
  -- the `W`-component of `s` is an sc⁺-germ
  have hsW : IsSc0Germ (E := ScBanach.paramProd P W) (F := W.shift) G (fun x => (s x).2) :=
    (ScBanach.sndOp (ScBanach.const Q) W.shift).isSc0Germ _ |>.comp hs (G.mapsToGerm_full _)
  have hsW0 : (s 0).2 = 0 := by rw [hs0]; rfl
  refine theorem_3_40_compactness hf.contraction hCt hsW hsW0 fun x hx => ⟨hx.1, ?_⟩
  have h2 := congrArg Prod.snd hx.2
  rw [ScBanach.paramProd_toBase] at h2
  change (f x).2 + W.toBase 1 (s x).2 = 0 at h2
  rw [hf.snd_eq x hx.1] at h2
  have : x.2 - B x + W.toBase 1 (s x).2 = 0 := h2
  rw [sub_add_eq_add_sub, sub_eq_zero] at this
  exact eq_sub_of_add_eq this

/-- **Corollary 3.13 in its local form**: if `x_k` are solutions (of `w = B(a, w) − s(a, w)` in
`U₀`) converging to `0` on level `0`, then for every `m` the `x_k` lie in `E_m` for `k` large and
converge to `0` in `E_m`. -/
theorem corollary_3_13_local (h : IsSc0ContractionGerm Ct G B) (hCt : IsClosed Ct)
    (hs : IsSc0Germ (F := W.shift) G s) (hs0 : s 0 = 0) {x : ℕ → (ScBanach.paramProd P W) 0}
    (hx : ∀ n, x n ∈ G.U 0 ∧ (x n).2 = B (x n) - W.toBase 1 (s (x n)))
    (hlim : Tendsto x atTop (𝓝 0)) (m : ℕ) :
    ∃ y : ℕ → (ScBanach.paramProd P W) m,
      (∀ᶠ n in atTop, (ScBanach.paramProd P W).toBase m (y n) = x n) ∧ Tendsto y atTop (𝓝 0) := by
  classical
  obtain ⟨O, hO, h0, -, hK⟩ := theorem_3_40_compactness h hCt hs hs0 (S := range x)
    (by rintro _ ⟨n, rfl⟩; exact hx n)
  obtain ⟨K, hKc, hKeq⟩ := hK m
  have hev : ∀ᶠ n in atTop, x n ∈ O m := hlim.eventually ((hO m).mem_nhds (h0 m))
  have hmem : ∀ n, x n ∈ O m → x n ∈ (ScBanach.paramProd P W).toBase m '' K := fun n hn => by
    rw [← hKeq]; exact subset_closure ⟨⟨n, rfl⟩, hn⟩
  refine ⟨fun n => if hn : x n ∈ O m then (hmem n hn).choose else 0, ?_, ?_⟩
  · filter_upwards [hev] with n hn
    rw [dif_pos hn]; exact (hmem n hn).choose_spec.2
  · -- every subsequence has a sub-subsequence converging to `0`
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    have hev' : ∀ᶠ k in atTop, x (ns k) ∈ O m := hns.eventually hev
    -- the lifts lie in `K ∪ {0}`, compact
    have hK0 : IsCompact (K ∪ {0}) := hKc.union isCompact_singleton
    have hmemK : ∀ k, (if hn : x (ns k) ∈ O m then (hmem _ hn).choose else 0) ∈ K ∪ {0} := by
      intro k
      by_cases hn : x (ns k) ∈ O m
      · rw [dif_pos hn]; exact Or.inl (hmem _ hn).choose_spec.1
      · rw [dif_neg hn]; exact Or.inr rfl
    obtain ⟨yl, -, ms, hms, hlim'⟩ := hK0.tendsto_subseq hmemK
    refine ⟨ms, ?_⟩
    -- the limit maps to `0`, so it is `0`
    have h1 : Tendsto (fun k => (ScBanach.paramProd P W).toBase m
        (if hn : x (ns (ms k)) ∈ O m then (hmem _ hn).choose else 0)) atTop (𝓝 ((ScBanach.paramProd P W).toBase m yl)) :=
      (((ScBanach.paramProd P W).toBase m).continuous.tendsto _).comp hlim'
    have h2 : Tendsto (fun k => (ScBanach.paramProd P W).toBase m
        (if hn : x (ns (ms k)) ∈ O m then (hmem _ hn).choose else 0)) atTop (𝓝 0) := by
      have h3 : Tendsto (fun k => x (ns (ms k))) atTop (𝓝 0) :=
        hlim.comp (hns.comp hms.tendsto_atTop)
      refine h3.congr' ?_
      filter_upwards [hms.tendsto_atTop.eventually hev'] with k hk
      rw [dif_pos hk]; exact ((hmem _ hk).choose_spec.2).symm
    have hyl : yl = 0 := by
      have := tendsto_nhds_unique h1 h2
      exact (ScBanach.paramProd P W).toBase_injective m (by rw [this, map_zero])
    rw [hyl] at hlim'
    exact hlim'

end Polyfold
