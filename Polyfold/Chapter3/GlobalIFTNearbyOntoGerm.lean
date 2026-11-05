import Polyfold.Chapter3.GlobalIFTNearbyOntoLemmas
import Polyfold.Chapter3.LocalSolvability
import Polyfold.Chapter3.ParamPerturbation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Theorem 3.54 (1), the surjectivity of `f'(y)` at the nearby zeros: the `λ`-extended contraction
germ.**

# The perturbed contraction germ with `λ`-independent parameter regions

## The text, paraphrased

Nothing in the text: the argument repairs the gap of Finding 100 (see `GlobalIFTNearbyOntoLemmas.lean`).
In the normal form of Theorem 3.38 (`ShiftedBasicData`: `g : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W` sc-smooth with
`g¹ = (G₁, w − B(a, w))` a basic germ on the index-raised structure), an sc⁺-perturbation
`e : O(C̃ ⊕ W, 0) → (ℝᴺ ⊕ W)¹` is added with a real parameter `μ`: the `W`-component of
`g + μ ι e` is `w − B_μ(a, w)` with `B_μ(a, w) = B(a, w) − μ P e(a, w)`.

## What is formalized

* `Polyfold.perturbEW` (`P e` on level `1`) and `ShiftedBasicData.eW_isScSmoothGerm` (it is sc-smooth on the
  index-raised germ: Proposition 1.17 for germs).
* `ShiftedBasicData.Radii`: **explicit `1/4`-contraction regions** `{‖a‖ < ν_m} × {‖w‖_{m+1} < ρ_m}`
  of the contraction `B` of `g¹`, with `‖B(a, 0)‖ ≤ ρ_m/8` and radii compatible with the
  inclusions; `exists_radii`: they exist below any prescribed radii (from Definition 3.28 with
  `ε = 1/4` and the continuity of `B` at `0`).  **They do not depend on the perturbation.**
* `ShiftedBasicData.perturbGerm`, `perturbB`, `perturbB_isScSmoothGerm`: the germ
  `(μ, a, w) ↦ B(a, w) − μ P e(a, w)` on `O((ℝ × C̃) ⊕ W¹, 0)`, sc-smooth (`IsScSmooth.smul`,
  Proposition 1.19, for the factor `μ`).
* `ShiftedBasicData.perturbContraction` (**Lemma 3 of the argument**): with the bounds
  `‖P e(a, w)‖_{m+1} ≤ c_m`, `‖P e(a, w) − P e(a, w')‖_{m+1} ≤ c_m ‖w − w'‖_{m+1}` on the regions,
  `B_μ` is a contraction germ in the working form `ContractionGerm` with the regions
  `(−μ_m, μ_m) × {‖a‖ < ν_m}`, `{‖w‖ < ρ_m}`, `{‖w‖ ≤ ρ_m/2}`, where only the `μ`-intervals
  depend on the constants `c_m`: `|μ| c_m ≤ 1/4` turns the `1/4`-contraction of `B` into a
  `1/2`-contraction of `B_μ`, and `|μ| c_m ≤ ρ_m/8` keeps the closed balls invariant.
* `perturbContraction_isSc1GermWith`: Theorem 3.30 for it (the solution germ `δ_μ(μ, a)` is sc¹
  on the re-indexed germ), and the identification `δ_μ(0, a) = w` of a fixed point `w` of
  `B(a, ·)` in the region (`perturbContraction_sol_zero`).

## What the text leaves implicit, and the choices made (the findings)

The point of the construction (Finding 182): Theorem 3.30 is applied **at the centre `0`** to the
`λ`-extended germ; the `a`-regions `N(m) = {‖a‖ < ν_m}` are those of `B` and do not depend on
`λ`, so a nearby zero `(a₀, w₀)` of `g` with `‖a₀‖ < ν_3`, `‖w₀‖_1 < ρ_0` lies in the region of
`C¹`-regularity of `δ_μ` for **every** `λ`.  The working form `IsSc0ContractionGerm.toContractionGerm`
is not used for `B_μ`, since its radii would depend on `λ`.
-/

open Set Filter Topology Function Module ContinuousLinearMap Metric

noncomputable section

namespace Polyfold

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P} {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [FiniteDimensional ℝ Q]

/-! ### The perturbation on the index-raised structure -/

/-- The `W`-component `P e` of an sc⁺-perturbation `e : U → (ℝᴺ ⊕ W)¹`, as a map
`U¹ → W¹` on level `1`: `eW(a, w) = (e(a, w))_W ∈ W₁`. -/
def perturbEW (e : P × W 0 → Q × W 1) : P × W 1 → W 1 :=
  fun x => (e ((ScBanach.paramProd P W).toBase 1 x)).2

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] in
lemma perturbEW_apply (e : P × W 0 → Q × W 1) (x : P × W 1) :
    perturbEW e x = (e ((ScBanach.paramProd P W).toBase 1 x)).2 := rfl

/-- The projection `((μ, a), w) ↦ (a, w)` as an sc-operator. -/
def perturbProj (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (W : ScBanach) :
    ScOperator (ScBanach.paramProd (ℝ × P) W.shift) (ScBanach.paramProd P W.shift) where
  lvl m := ((ContinuousLinearMap.snd ℝ ℝ P).comp
    (ContinuousLinearMap.fst ℝ (ℝ × P) (W (m + 1)))).prod (ContinuousLinearMap.snd ℝ (ℝ × P) (W (m + 1)))
  incl_comm _ _ := rfl

@[simp] lemma perturbProj_apply (m : ℕ) (p : (ScBanach.paramProd (ℝ × P) W.shift) m) :
    perturbProj P W m p = ((p.1.2, p.2) : P × W (m + 1)) := rfl

/-- The projection `((μ, a), w) ↦ μ` as an sc-operator. -/
def perturbMuProj (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (W : ScBanach) : ScOperator (ScBanach.paramProd (ℝ × P) W.shift) (ScBanach.const ℝ) where
  lvl m := (ContinuousLinearMap.fst ℝ ℝ P).comp (ContinuousLinearMap.fst ℝ (ℝ × P) (W (m + 1)))
  incl_comm _ _ := rfl

@[simp] lemma perturbMuProj_apply (m : ℕ) (p : (ScBanach.paramProd (ℝ × P) W.shift) m) :
    perturbMuProj P W m p = p.1.1 := rfl

/-- `ℝ × C̃` is quadrant-like in `ℝ × P`. -/
lemma isQuadrantLike_perturb (hC : IsQuadrantLike (ScBanach.const P) Ct) :
    IsQuadrantLike (ScBanach.const (ℝ × P)) (univ ×ˢ Ct) := by
  obtain ⟨h0, hc, hi⟩ := isQuadrantLike_const_iff.1 hC
  refine isQuadrantLike_const_iff.2 ⟨⟨mem_univ _, h0⟩, convex_univ.prod hc, ?_⟩
  rw [interior_prod_eq, interior_univ]
  exact univ_nonempty.prod hi

namespace ShiftedBasicData

variable (𝒟 : ShiftedBasicData Ct W Q)

variable (hC : IsQuadrantLike (ScBanach.const P) Ct)
include hC

/-- The index-raised perturbation `levelMap e 1` is sc-smooth on `G₁` (Proposition 1.17 for
germs, transported from `G₀¹` to `G₁` by `G₁_U`). -/
theorem levelMap_e_isScSmoothGerm {e : P × W 0 → Q × W 1}
    (he : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := (ScBanach.paramProd Q W).shift)
      𝒟.G₀ e) :
    IsScSmoothGerm (E := ScBanach.paramProd P W.shift) (F := ((ScBanach.paramProd Q W).shift).shift)
      𝒟.G₁ (levelMap (E := ScBanach.paramProd P W) (F := (ScBanach.paramProd Q W).shift) e 1) := by
  intro k
  have h1 := IsSckGerm.shift (hC.paramProd W) (he k)
  refine IsSckGerm.of_U_eq (G₁ := 𝒟.G₀.shift) (hC.paramProd W).shift (fun m => ?_) h1
  rw [ScNbhdGerm.shift_U, 𝒟.G₁_U]

omit hC in
/-- `eW = pr_W ∘ ι ∘ (levelMap e 1)` on `G₁`. -/
theorem eW_eq_on {e : P × W 0 → Q × W 1}
    (he : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := (ScBanach.paramProd Q W).shift)
      𝒟.G₀ e) {x : P × W 1} (hx : x ∈ 𝒟.G₁.U 0) :
    perturbEW e x = ScBanach.wPartOp Q W 0 (ScBanach.shiftIncl ((ScBanach.paramProd Q W).shift) 0
      (levelMap (E := ScBanach.paramProd P W) (F := (ScBanach.paramProd Q W).shift) e 1 x)) := by
  have hx1 : x ∈ 𝒟.G₀.U 1 := by rw [← 𝒟.G₁_U 0]; exact hx
  have h1 := (he 0).incl_levelMap (m := 0) hx1
  rw [levelMap_zero] at h1
  rw [perturbEW_apply, ScBanach.wPartOp_apply]
  change (e ((ScBanach.paramProd P W).toBase 1 x)).2 =
    (((ScBanach.paramProd Q W).shift).incl 0
      (levelMap (E := ScBanach.paramProd P W) (F := (ScBanach.paramProd Q W).shift) e 1 x)).2
  rw [h1]
  rfl

/-- **`P e` is sc-smooth on the index-raised germ `G₁`.** -/
theorem eW_isScSmoothGerm {e : P × W 0 → Q × W 1}
    (he : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := (ScBanach.paramProd Q W).shift)
      𝒟.G₀ e) :
    IsScSmoothGerm (E := ScBanach.paramProd P W.shift) (F := W.shift) 𝒟.G₁ (perturbEW e) := by
  have hC' : IsQuadrantLike (ScBanach.paramProd P W.shift) (Ct ×ˢ univ) := hC.paramProd W.shift
  intro k
  have h1 := 𝒟.levelMap_e_isScSmoothGerm hC he k
  have h2 := IsSckGerm.operator_comp hC' (ScBanach.shiftIncl ((ScBanach.paramProd Q W).shift)) h1
  have h3 := IsSckGerm.operator_comp hC' (ScBanach.wPartOp Q W) h2
  refine IsSckGerm.congr hC' (fun x hx => ?_) h3
  exact (𝒟.eW_eq_on he hx).symm

omit hC in
/-- The level-`m` map of `eW` on the index-raised structure: `(levelMap e m (ι x))_W`. -/
theorem levelB_eW {e : P × W 0 → Q × W 1}
    (he : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := (ScBanach.paramProd Q W).shift)
      𝒟.G₀ e) {m : ℕ} {x : P × W (m + 1)} (hx : x ∈ 𝒟.G₁.U m) :
    levelB (W := W.shift) (perturbEW e) m x =
      (levelMap (E := ScBanach.paramProd P W) (F := (ScBanach.paramProd Q W).shift) e m
        ((ScBanach.paramProd P W).incl m x)).2 := by
  have hx1 : x ∈ 𝒟.G₀.U (m + 1) := by rw [← 𝒟.G₁_U m]; exact hx
  have hxm : (ScBanach.paramProd P W).incl m x ∈ 𝒟.G₀.U m := 𝒟.G₀.nested m x hx1
  apply levelMap_eq_of_toBase_eq
  have h1 := (he 0).toBase_levelMap hxm
  have h2 := congrArg Prod.snd h1
  rw [ScBanach.paramProd_shift_toBase] at h2
  dsimp only at h2
  have hkey : (ScBanach.paramProd P W).toBase m ((ScBanach.paramProd P W).incl m x) =
      (ScBanach.paramProd P W).toBase 1 ((ScBanach.paramProd P W.shift).toBase m x) := by
    rw [← ScScale.toBase_succ]
    exact (ScBanach.paramProd P W).shift_toBase m x
  change W.shift.toBase m (levelMap (E := ScBanach.paramProd P W)
    (F := (ScBanach.paramProd Q W).shift) e m ((ScBanach.paramProd P W).incl m x)).2 =
    (e ((ScBanach.paramProd P W).toBase 1 ((ScBanach.paramProd P W.shift).toBase m x))).2
  exact h2.trans (congrArg (fun y => (e y).2) hkey)

omit hC

/-! ### The contraction regions of `B` -/

/-- **Explicit `1/4`-contraction regions of the contraction `B` of `g¹`**: radii `ν m` in `P` and
`ρ m` in `W_{m+1}` such that for `a ∈ C̃`, `‖a‖ < ν m`, `‖w‖, ‖w'‖ < ρ m`: `(a, w) ∈ U¹_m`,
`‖B(a, w) − B(a, w')‖ ≤ ¼‖w − w'‖`, `‖B(a, 0)‖ ≤ ρ m / 8`; `ν` decreasing and `ρ` compatible
with the inclusions. -/
structure Radii (𝒟 : ShiftedBasicData Ct W Q) where
  ν : ℕ → ℝ
  ρ : ℕ → ℝ
  ν_pos : ∀ m, 0 < ν m
  ρ_pos : ∀ m, 0 < ρ m
  ν_anti : ∀ m, ν (m + 1) ≤ ν m
  ρ_incl : ∀ m (w : W (m + 2)), ‖w‖ ≤ ρ (m + 1) / 2 → ‖W.incl (m + 1) w‖ ≤ ρ m / 2
  mem_G : ∀ m, ∀ a ∈ Ct, ‖a‖ < ν m → ∀ w : W (m + 1), ‖w‖ < ρ m →
    ((a, w) : P × W (m + 1)) ∈ 𝒟.G₁.U m
  contr : ∀ m, ∀ a ∈ Ct, ‖a‖ < ν m → ∀ w w' : W (m + 1), ‖w‖ < ρ m → ‖w'‖ < ρ m →
    ‖levelB (W := W.shift) 𝒟.B m (a, w) - levelB (W := W.shift) 𝒟.B m (a, w')‖ ≤
      1 / 4 * ‖w - w'‖
  B_zero_small : ∀ m, ∀ a ∈ Ct, ‖a‖ < ν m →
    ‖levelB (W := W.shift) 𝒟.B m (a, (0 : W (m + 1)))‖ ≤ ρ m / 8

namespace Radii

variable {𝒟} (R : 𝒟.Radii)

lemma ν_anti_le {m n : ℕ} (h : m ≤ n) : R.ν n ≤ R.ν m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (R.ν_anti _).trans ih

end Radii

/-- `B_m(0, 0) = 0`. -/
lemma levelB_B_zero (m : ℕ) : levelB (W := W.shift) 𝒟.B m 0 = 0 := by
  apply levelMap_eq_of_toBase_eq
  rw [map_zero, map_zero]
  exact 𝒟.basic.contraction.B_zero.symm

/-- **The regions exist below any prescribed radii**: from Definition 3.28 with `ε = 1/4`
(`IsSc0ContractionGerm.contraction`) and the continuity of `B_m` at `(0, 0)`. -/
theorem exists_radii (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) :
    ∃ R : 𝒟.Radii, ∀ m, R.ν m ≤ δ m ∧ R.ρ m ≤ δ m := by
  classical
  have hcontr := 𝒟.basic.contraction
  choose r hr hr' using fun m => hcontr.contraction (1 / 4) (by norm_num) m
  -- the radii `ρ`
  let ρ : ℕ → ℝ := fun m => Nat.rec (min (r 0) (δ 0))
    (fun m ρm => min (min (r (m + 1)) (δ (m + 1))) (ρm / (‖W.incl (m + 1)‖ + 1))) m
  have hρ0 : ρ 0 = min (r 0) (δ 0) := rfl
  have hρs : ∀ m, ρ (m + 1) = min (min (r (m + 1)) (δ (m + 1))) (ρ m / (‖W.incl (m + 1)‖ + 1)) :=
    fun m => rfl
  have hρpos : ∀ m, 0 < ρ m := by
    intro m
    induction m with
    | zero => rw [hρ0]; exact lt_min (hr 0) (hδ 0)
    | succ m ih => rw [hρs]; exact lt_min (lt_min (hr _) (hδ _)) (by positivity)
  have hρr : ∀ m, ρ m ≤ r m := by
    intro m
    cases m with
    | zero => rw [hρ0]; exact min_le_left _ _
    | succ m => rw [hρs]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hρδ : ∀ m, ρ m ≤ δ m := by
    intro m
    cases m with
    | zero => rw [hρ0]; exact min_le_right _ _
    | succ m => rw [hρs]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hρincl : ∀ m (w : W (m + 2)), ‖w‖ ≤ ρ (m + 1) / 2 → ‖W.incl (m + 1) w‖ ≤ ρ m / 2 := by
    intro m w hw
    have h1 : ρ (m + 1) ≤ ρ m / (‖W.incl (m + 1)‖ + 1) := by rw [hρs]; exact min_le_right _ _
    calc ‖W.incl (m + 1) w‖ ≤ ‖W.incl (m + 1)‖ * ‖w‖ := (W.incl (m + 1)).le_opNorm w
      _ ≤ ‖W.incl (m + 1)‖ * (ρ (m + 1) / 2) := by gcongr
      _ ≤ ‖W.incl (m + 1)‖ * (ρ m / (‖W.incl (m + 1)‖ + 1) / 2) := by gcongr
      _ ≤ ρ m / 2 := by
          rw [div_div, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          have := hρpos m
          nlinarith [norm_nonneg (W.incl (m + 1))]
  -- continuity of `B_m` at `(0, 0)`: the radii `ν'`
  have hcont : ∀ m, ∃ ν' > 0, ∀ a ∈ Ct, ‖a‖ < ν' → ‖a‖ < r m →
      ‖levelB (W := W.shift) 𝒟.B m (a, (0 : W (m + 1)))‖ ≤ ρ m / 8 := by
    intro m
    have hc := hcontr.isSc0.continuousOn m 0 (𝒟.G₁.zero_mem m)
    rw [Metric.continuousWithinAt_iff] at hc
    obtain ⟨ν', hν', hν''⟩ := hc (ρ m / 8) (by have := hρpos m; positivity)
    refine ⟨ν', hν', fun a ha haν har => ?_⟩
    have hmem : ((a, (0 : W (m + 1))) : P × W (m + 1)) ∈ 𝒟.G₁.U m :=
      (hr' m a ha har 0 0 (by rw [norm_zero]; exact hr m) (by rw [norm_zero]; exact hr m)).1
    have h1 := hν'' hmem (by
      rw [dist_zero_right, Prod.norm_def, norm_zero]
      exact (max_eq_left (norm_nonneg a)).le.trans_lt haν)
    rw [dist_eq_norm] at h1
    have h0 : levelMap (E := ScBanach.paramProd P W.shift) (F := W.shift) 𝒟.B m 0 = 0 :=
      𝒟.levelB_B_zero m
    rw [h0, sub_zero] at h1
    exact h1.le
  choose ν' hν' hν'' using hcont
  -- the radii `ν`
  let ν : ℕ → ℝ := fun m => Nat.rec (min (min (r 0) (δ 0)) (ν' 0))
    (fun m νm => min νm (min (min (r (m + 1)) (δ (m + 1))) (ν' (m + 1)))) m
  have hν0 : ν 0 = min (min (r 0) (δ 0)) (ν' 0) := rfl
  have hνs : ∀ m, ν (m + 1) = min (ν m) (min (min (r (m + 1)) (δ (m + 1))) (ν' (m + 1))) :=
    fun m => rfl
  have hνpos : ∀ m, 0 < ν m := by
    intro m
    induction m with
    | zero => rw [hν0]; exact lt_min (lt_min (hr 0) (hδ 0)) (hν' 0)
    | succ m ih => rw [hνs]; exact lt_min ih (lt_min (lt_min (hr _) (hδ _)) (hν' _))
  have hνle : ∀ m, ν m ≤ min (min (r m) (δ m)) (ν' m) := by
    intro m
    cases m with
    | zero => rw [hν0]
    | succ m => rw [hνs]; exact min_le_right _ _
  have hνr : ∀ m, ν m ≤ r m := fun m => (hνle m).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνδ : ∀ m, ν m ≤ δ m := fun m => (hνle m).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hνν' : ∀ m, ν m ≤ ν' m := fun m => (hνle m).trans (min_le_right _ _)
  have hνanti : ∀ m, ν (m + 1) ≤ ν m := fun m => by rw [hνs]; exact min_le_left _ _
  refine ⟨⟨ν, ρ, hνpos, hρpos, hνanti, hρincl, ?_, ?_, ?_⟩, fun m => ⟨hνδ m, hρδ m⟩⟩
  · intro m a ha haν w hw
    exact (hr' m a ha (haν.trans_le (hνr m)) w w (hw.trans_le (hρr m)) (hw.trans_le (hρr m))).1
  · intro m a ha haν w w' hw hw'
    exact (hr' m a ha (haν.trans_le (hνr m)) w w' (hw.trans_le (hρr m)) (hw'.trans_le (hρr m))).2
  · intro m a ha haν
    exact hν'' m a ha (haν.trans_le (hνν' m)) (haν.trans_le (hνr m))

/-! ### The perturbed germ -/

/-- The germ of neighbourhoods `{((μ, a), w) | (a, w) ∈ U¹_m}` of `0` in `(ℝ × C̃) ⊕ W¹`. -/
def perturbGerm : ScNbhdGerm (ScBanach.paramProd (ℝ × P) W.shift) ((univ ×ˢ Ct) ×ˢ univ) where
  U m := {p | ((p.1.2, p.2) : P × W (m + 1)) ∈ 𝒟.G₁.U m}
  nested m p hp := 𝒟.G₁.nested m _ hp
  zero_mem m := 𝒟.G₁.zero_mem m
  relOpen m := by
    obtain ⟨O, hO, hU⟩ := 𝒟.G₁.relOpen m
    refine ⟨(fun p : (ℝ × P) × W (m + 1) => ((p.1.2, p.2) : P × W (m + 1))) ⁻¹' O,
      hO.preimage (by fun_prop), ?_⟩
    ext p
    change ((p.1.2, p.2) : P × W (m + 1)) ∈ 𝒟.G₁.U m ↔ _
    rw [hU, ScBanach.paramProd_lvlSet, ScBanach.paramProd_lvlSet]
    simp [mem_prod]

@[simp] lemma mem_perturbGerm_U {m : ℕ} {p : (ScBanach.paramProd (ℝ × P) W.shift) m} :
    p ∈ 𝒟.perturbGerm.U m ↔ ((p.1.2, p.2) : P × W (m + 1)) ∈ 𝒟.G₁.U m := Iff.rfl

lemma perturbProj_mapsToGerm : 𝒟.perturbGerm.MapsToGerm 𝒟.G₁ (perturbProj P W 0) := by
  intro m p hp
  rw [ScOperator.levelMap_eq]
  exact hp

/-- The perturbed contraction map `B_μ(a, w) = B(a, w) − μ P e(a, w)` on `(ℝ × P) ⊕ W₁`. -/
def perturbB (e : P × W 0 → Q × W 1) : (ℝ × P) × W 1 → W 1 :=
  fun p => 𝒟.B (p.1.2, p.2) - p.1.1 • perturbEW e (p.1.2, p.2)

lemma perturbB_apply (e : P × W 0 → Q × W 1) (p : (ℝ × P) × W 1) :
    𝒟.perturbB e p = 𝒟.B (p.1.2, p.2) - p.1.1 • perturbEW e (p.1.2, p.2) := rfl

lemma perturbB_zero (e : P × W 0 → Q × W 1) : 𝒟.perturbB e (0, 0) = 0 := by
  rw [perturbB_apply]
  change 𝒟.B (0, 0) - (0 : ℝ) • perturbEW e (0, 0) = 0
  rw [𝒟.basic.contraction.B_zero, zero_smul, sub_zero]

include hC in
/-- **`B_μ` is sc-smooth on the perturbed germ**: `B ∘ π` and `(μ, P e ∘ π) ↦ μ · P e` with the
sc-smooth scalar multiplication (Proposition 1.19). -/
theorem perturbB_isScSmoothGerm {e : P × W 0 → Q × W 1}
    (he : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := (ScBanach.paramProd Q W).shift)
      𝒟.G₀ e) :
    IsScSmoothGerm (E := ScBanach.paramProd (ℝ × P) W.shift) (F := W.shift) 𝒟.perturbGerm
      (𝒟.perturbB e) := by
  have hC' : IsQuadrantLike (ScBanach.paramProd P W.shift) (Ct ×ˢ univ) := hC.paramProd W.shift
  have hC₁ : IsQuadrantLike (ScBanach.paramProd (ℝ × P) W.shift) ((univ ×ˢ Ct) ×ˢ univ) :=
    (isQuadrantLike_perturb hC).paramProd W.shift
  -- `B ∘ π` and `eW ∘ π`
  have hB : IsScSmoothGerm (E := ScBanach.paramProd (ℝ × P) W.shift) (F := W.shift) 𝒟.perturbGerm
      (𝒟.B ∘ perturbProj P W 0) :=
    IsScSmoothGerm.comp hC₁ hC' (𝒟.B_isScSmooth hC) ((perturbProj P W).isScSmoothGerm _ hC₁)
      𝒟.perturbProj_mapsToGerm
  have heW : IsScSmoothGerm (E := ScBanach.paramProd (ℝ × P) W.shift) (F := W.shift) 𝒟.perturbGerm
      (perturbEW e ∘ perturbProj P W 0) :=
    IsScSmoothGerm.comp hC₁ hC' (𝒟.eW_isScSmoothGerm hC he) ((perturbProj P W).isScSmoothGerm _ hC₁)
      𝒟.perturbProj_mapsToGerm
  -- the scalar multiplication as a germ on all of `ℝ ⊕ W¹`
  have hsmul : IsScSmoothGerm (E := (ScBanach.const ℝ).prod W.shift) (F := W.shift)
      (ScNbhdGerm.ofSet (C := univ) (U := univ) ⟨univ, isOpen_univ, (univ_inter _).symm⟩
        (mem_univ 0)) (fun p => p.1 • p.2) :=
    IsScSmooth.isScSmoothGerm (isQuadrantLike_univ _) _ _ (isScSmooth_smul W.shift)
  have hpair : IsScSmoothGerm (E := ScBanach.paramProd (ℝ × P) W.shift)
      (F := (ScBanach.const ℝ).prod W.shift) 𝒟.perturbGerm
      (pairMap (F := ScBanach.const ℝ) (G := W.shift) (perturbMuProj P W 0)
        (perturbEW e ∘ perturbProj P W 0)) :=
    IsScSmoothGerm.pair (F := ScBanach.const ℝ) (G := W.shift) hC₁
      ((perturbMuProj P W).isScSmoothGerm _ hC₁) heW
  have hmul : IsScSmoothGerm (E := ScBanach.paramProd (ℝ × P) W.shift) (F := W.shift)
      𝒟.perturbGerm ((fun p : ((ScBanach.const ℝ).prod W.shift) 0 => p.1 • p.2) ∘
        pairMap (F := ScBanach.const ℝ) (G := W.shift) (perturbMuProj P W 0)
          (perturbEW e ∘ perturbProj P W 0)) :=
    IsScSmoothGerm.comp hC₁ (isQuadrantLike_univ _) hsmul hpair fun _ _ _ => by
      rw [ScNbhdGerm.ofSet_U]; exact mem_univ _
  have hneg := fun k => IsSckGerm.operator_comp hC₁ W.shift.negOp (hmul k)
  have hpair2 : IsScSmoothGerm (E := ScBanach.paramProd (ℝ × P) W.shift)
      (F := W.shift.prod W.shift) 𝒟.perturbGerm
      (pairMap (F := W.shift) (G := W.shift) (𝒟.B ∘ perturbProj P W 0)
        (W.shift.negOp 0 ∘ ((fun p : ((ScBanach.const ℝ).prod W.shift) 0 => p.1 • p.2) ∘
          pairMap (F := ScBanach.const ℝ) (G := W.shift) (perturbMuProj P W 0)
            (perturbEW e ∘ perturbProj P W 0)))) :=
    IsScSmoothGerm.pair (F := W.shift) (G := W.shift) hC₁ hB hneg
  intro k
  have hadd := IsSckGerm.operator_comp hC₁ W.shift.addOp (hpair2 k)
  refine IsSckGerm.congr hC₁ (fun p _ => ?_) hadd
  simp only [Function.comp_apply, pairMap, perturbB_apply]
  rw [sub_eq_add_neg]
  rfl

include hC in
/-- The level-`m` map of `B_μ`: `B_m(a, w) − μ (P e)_m(a, w)`. -/
theorem levelB_perturbB {e : P × W 0 → Q × W 1}
    (he : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := (ScBanach.paramProd Q W).shift)
      𝒟.G₀ e) {m : ℕ} {p : (ℝ × P) × W (m + 1)} (hp : p ∈ 𝒟.perturbGerm.U m) :
    levelB (W := W.shift) (𝒟.perturbB e) m p =
      levelB (W := W.shift) 𝒟.B m (p.1.2, p.2) -
        p.1.1 • levelB (W := W.shift) (perturbEW e) m (p.1.2, p.2) := by
  have hp' : ((p.1.2, p.2) : P × W (m + 1)) ∈ 𝒟.G₁.U m := hp
  apply levelMap_eq_of_toBase_eq
  rw [map_sub, map_smul]
  have h1 : W.shift.toBase m (levelB (W := W.shift) 𝒟.B m (p.1.2, p.2)) =
      𝒟.B ((ScBanach.paramProd P W.shift).toBase m (p.1.2, p.2)) :=
    ((𝒟.B_isScSmooth hC) 0).toBase_levelMap hp'
  have h2 : W.shift.toBase m (levelB (W := W.shift) (perturbEW e) m (p.1.2, p.2)) =
      perturbEW e ((ScBanach.paramProd P W.shift).toBase m (p.1.2, p.2)) :=
    ((𝒟.eW_isScSmoothGerm hC he) 0).toBase_levelMap hp'
  rw [h1, h2, perturbB_apply, ScBanach.paramProd_toBase, ScBanach.paramProd_toBase]

/-! ### The `μ`-intervals -/

/-- The radii of the `μ`-intervals: `μ_m ≤ min(1/4, ρ_j/8)/(c_j + 1)` for `j ≤ m`. -/
def perturbMu (R : 𝒟.Radii) (c : ℕ → ℝ) : ℕ → ℝ := fun m =>
  Nat.rec (min (1 / 4) (R.ρ 0 / 8) / (c 0 + 1))
    (fun m μm => min μm (min (1 / 4) (R.ρ (m + 1) / 8) / (c (m + 1) + 1))) m

lemma perturbMu_zero (R : 𝒟.Radii) (c : ℕ → ℝ) :
    𝒟.perturbMu R c 0 = min (1 / 4) (R.ρ 0 / 8) / (c 0 + 1) := rfl

lemma perturbMu_succ (R : 𝒟.Radii) (c : ℕ → ℝ) (m : ℕ) :
    𝒟.perturbMu R c (m + 1) =
      min (𝒟.perturbMu R c m) (min (1 / 4) (R.ρ (m + 1) / 8) / (c (m + 1) + 1)) := rfl

lemma perturbMu_pos (R : 𝒟.Radii) (c : ℕ → ℝ) (hc : ∀ m, 0 ≤ c m) (m : ℕ) :
    0 < 𝒟.perturbMu R c m := by
  induction m with
  | zero =>
    rw [perturbMu_zero]
    have := R.ρ_pos 0; have := hc 0
    positivity
  | succ m ih =>
    rw [perturbMu_succ]
    have := R.ρ_pos (m + 1); have := hc (m + 1)
    exact lt_min ih (by positivity)

lemma perturbMu_anti (R : 𝒟.Radii) (c : ℕ → ℝ) (m : ℕ) :
    𝒟.perturbMu R c (m + 1) ≤ 𝒟.perturbMu R c m := by
  rw [perturbMu_succ]; exact min_le_left _ _

lemma perturbMu_le (R : 𝒟.Radii) (c : ℕ → ℝ) (m : ℕ) :
    𝒟.perturbMu R c m ≤ min (1 / 4) (R.ρ m / 8) / (c m + 1) := by
  cases m with
  | zero => rw [perturbMu_zero]
  | succ m => rw [perturbMu_succ]; exact min_le_right _ _

/-- `μ_m c_m ≤ 1/4` and `μ_m c_m ≤ ρ_m / 8`. -/
lemma perturbMu_mul_le (R : 𝒟.Radii) (c : ℕ → ℝ) (hc : ∀ m, 0 ≤ c m) (m : ℕ) :
    𝒟.perturbMu R c m * c m ≤ 1 / 4 ∧ 𝒟.perturbMu R c m * c m ≤ R.ρ m / 8 := by
  have h1 := 𝒟.perturbMu_le R c m
  have hc0 := hc m
  have hρ := R.ρ_pos m
  have hmin : 0 ≤ min (1 / 4) (R.ρ m / 8) := le_min (by norm_num) (by positivity)
  have h2 : 𝒟.perturbMu R c m * c m ≤ min (1 / 4) (R.ρ m / 8) := by
    calc 𝒟.perturbMu R c m * c m ≤ min (1 / 4) (R.ρ m / 8) / (c m + 1) * c m := by gcongr
      _ = min (1 / 4) (R.ρ m / 8) * (c m / (c m + 1)) := by ring
      _ ≤ min (1 / 4) (R.ρ m / 8) * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; linarith
      _ = min (1 / 4) (R.ρ m / 8) := mul_one _
  exact ⟨h2.trans (min_le_left _ _), h2.trans (min_le_right _ _)⟩

/-! ### The perturbed contraction germ (Lemma 3) -/

variable (R : 𝒟.Radii) {e : P × W 0 → Q × W 1}
  (he : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := (ScBanach.paramProd Q W).shift)
    𝒟.G₀ e)
  (c : ℕ → ℝ) (hc : ∀ m, 0 ≤ c m)
  (hce : ∀ m, ∀ a ∈ Ct, ‖a‖ < R.ν m → ∀ w w' : W (m + 1), ‖w‖ < R.ρ m → ‖w'‖ < R.ρ m →
    ‖levelB (W := W.shift) (perturbEW e) m (a, w)‖ ≤ c m ∧
    ‖levelB (W := W.shift) (perturbEW e) m (a, w) - levelB (W := W.shift) (perturbEW e) m (a, w')‖ ≤
      c m * ‖w - w'‖)

include hC he hc hce in
/-- **The `λ`-extended contraction germ, in the working form** (Lemma 3 of the argument): with
the parameter regions `(−μ_m, μ_m) × {‖a‖ < ν_m}`, the balls `{‖w‖ < ρ_m}` and the closed balls
`{‖w‖ ≤ ρ_m/2}` in `W_{m+1}`, the map `B_μ(a, w) = B(a, w) − μ P e(a, w)` is a `1/2`-contraction
in `w` mapping the closed balls into themselves: `‖B_μ(a, w) − B_μ(a, w')‖ ≤ (¼ + |μ| c_m)‖w − w'‖`
and `‖B_μ(a, w)‖ ≤ ¼ · ρ_m/2 + ρ_m/8 + |μ| c_m ≤ ρ_m/2`.  The regions in `a` and `w` are those
of `B` (`Radii`) and do not depend on `e`. -/
def perturbContraction : ContractionGerm (ℝ × P) (univ ×ˢ Ct) W.shift where
  B := 𝒟.perturbB e
  G := 𝒟.perturbGerm
  B_zero := 𝒟.perturbB_zero e
  isSc0 := (𝒟.perturbB_isScSmoothGerm hC he).isSckGerm 0
  N m := Ioo (-𝒟.perturbMu R c m) (𝒟.perturbMu R c m) ×ˢ ball (0 : P) (R.ν m)
  N_open _ := isOpen_Ioo.prod isOpen_ball
  N_zero m := by
    have := 𝒟.perturbMu_pos R c hc m
    refine ⟨⟨?_, ?_⟩, mem_ball_self (R.ν_pos m)⟩
    · show -𝒟.perturbMu R c m < (0 : ℝ); linarith
    · show (0 : ℝ) < 𝒟.perturbMu R c m; exact this
  N_anti m := by
    refine prod_mono (Ioo_subset_Ioo ?_ (𝒟.perturbMu_anti R c m)) (ball_subset_ball (R.ν_anti m))
    linarith [𝒟.perturbMu_anti R c m]
  O m := ball (0 : W (m + 1)) (R.ρ m)
  K m := closedBall (0 : W (m + 1)) (R.ρ m / 2)
  O_open _ := isOpen_ball
  K_closed _ := isClosed_closedBall
  K_zero m := mem_closedBall_self (by have := R.ρ_pos m; positivity)
  K_sub m := closedBall_subset_ball (by have := R.ρ_pos m; linarith)
  K_incl m w hw := by
    rw [mem_closedBall, dist_zero_right] at hw ⊢
    exact R.ρ_incl m w hw
  mem_G m a ha w hw := by
    rw [mem_ball, dist_zero_right] at hw
    have haν : ‖a.2‖ < R.ν m := by have := ha.1.2; rwa [mem_ball, dist_zero_right] at this
    exact R.mem_G m a.2 ha.2.2 haν w hw
  mapsTo m a ha w hw := by
    rw [mem_closedBall, dist_zero_right] at hw ⊢
    have hμ : |a.1| < 𝒟.perturbMu R c m := abs_lt.2 ha.1.1
    have haC : a.2 ∈ Ct := ha.2.2
    have haν : ‖a.2‖ < R.ν m := by have := ha.1.2; rwa [mem_ball, dist_zero_right] at this
    have hρ := R.ρ_pos m
    have hwρ : ‖w‖ < R.ρ m := hw.trans_lt (by linarith)
    have h0ρ : ‖(0 : W (m + 1))‖ < R.ρ m := by rw [norm_zero]; exact hρ
    have hmem : ((a, w) : (ℝ × P) × W (m + 1)) ∈ 𝒟.perturbGerm.U m := R.mem_G m a.2 haC haν w hwρ
    change ‖levelB (W := W.shift) (𝒟.perturbB e) m (a, w)‖ ≤ R.ρ m / 2
    rw [𝒟.levelB_perturbB hC he hmem]
    have h1 := R.contr m a.2 haC haν w 0 hwρ h0ρ
    have h2 := R.B_zero_small m a.2 haC haν
    have h3 := (hce m a.2 haC haν w w hwρ hwρ).1
    have h4 := (𝒟.perturbMu_mul_le R c hc m).2
    have h5 : |a.1| * c m ≤ R.ρ m / 8 :=
      (mul_le_mul_of_nonneg_right hμ.le (hc m)).trans h4
    calc ‖levelB (W := W.shift) 𝒟.B m (a.2, w) - a.1 • levelB (W := W.shift) (perturbEW e) m (a.2, w)‖
        ≤ ‖levelB (W := W.shift) 𝒟.B m (a.2, w)‖ +
          ‖a.1 • levelB (W := W.shift) (perturbEW e) m (a.2, w)‖ := norm_sub_le _ _
      _ ≤ (‖levelB (W := W.shift) 𝒟.B m (a.2, w) - levelB (W := W.shift) 𝒟.B m (a.2, 0)‖ +
            ‖levelB (W := W.shift) 𝒟.B m (a.2, 0)‖) + |a.1| * c m := by
          rw [norm_smul, Real.norm_eq_abs]
          exact add_le_add (norm_le_norm_sub_add _ _)
            (mul_le_mul_of_nonneg_left h3 (abs_nonneg _))
      _ ≤ (1 / 4 * ‖w - 0‖ + R.ρ m / 8) + R.ρ m / 8 := add_le_add (add_le_add h1 h2) h5
      _ ≤ R.ρ m / 2 := by rw [sub_zero]; linarith
  contr m a ha w hw w' hw' := by
    rw [mem_ball, dist_zero_right] at hw hw'
    have hμ : |a.1| < 𝒟.perturbMu R c m := abs_lt.2 ha.1.1
    have haC : a.2 ∈ Ct := ha.2.2
    have haν : ‖a.2‖ < R.ν m := by have := ha.1.2; rwa [mem_ball, dist_zero_right] at this
    have hmem : ((a, w) : (ℝ × P) × W (m + 1)) ∈ 𝒟.perturbGerm.U m := R.mem_G m a.2 haC haν w hw
    have hmem' : ((a, w') : (ℝ × P) × W (m + 1)) ∈ 𝒟.perturbGerm.U m :=
      R.mem_G m a.2 haC haν w' hw'
    rw [𝒟.levelB_perturbB hC he hmem, 𝒟.levelB_perturbB hC he hmem']
    have h1 := R.contr m a.2 haC haν w w' hw hw'
    have h3 := (hce m a.2 haC haν w w' hw hw').2
    have h4 := (𝒟.perturbMu_mul_le R c hc m).1
    have h5 : |a.1| * c m ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hμ.le (hc m)).trans h4
    have hid : levelB (W := W.shift) 𝒟.B m (a.2, w) -
        a.1 • levelB (W := W.shift) (perturbEW e) m (a.2, w) -
        (levelB (W := W.shift) 𝒟.B m (a.2, w') -
          a.1 • levelB (W := W.shift) (perturbEW e) m (a.2, w')) =
        (levelB (W := W.shift) 𝒟.B m (a.2, w) - levelB (W := W.shift) 𝒟.B m (a.2, w')) -
          a.1 • (levelB (W := W.shift) (perturbEW e) m (a.2, w) -
            levelB (W := W.shift) (perturbEW e) m (a.2, w')) := by
      rw [smul_sub]; abel
    rw [hid]
    calc ‖(levelB (W := W.shift) 𝒟.B m (a.2, w) - levelB (W := W.shift) 𝒟.B m (a.2, w')) -
          a.1 • (levelB (W := W.shift) (perturbEW e) m (a.2, w) -
            levelB (W := W.shift) (perturbEW e) m (a.2, w'))‖
        ≤ ‖levelB (W := W.shift) 𝒟.B m (a.2, w) - levelB (W := W.shift) 𝒟.B m (a.2, w')‖ +
          ‖a.1 • (levelB (W := W.shift) (perturbEW e) m (a.2, w) -
            levelB (W := W.shift) (perturbEW e) m (a.2, w'))‖ := norm_sub_le _ _
      _ ≤ 1 / 4 * ‖w - w'‖ + |a.1| * (c m * ‖w - w'‖) := by
          rw [norm_smul, Real.norm_eq_abs]
          exact add_le_add h1 (mul_le_mul_of_nonneg_left h3 (abs_nonneg _))
      _ = (1 / 4 + |a.1| * c m) * ‖w - w'‖ := by ring
      _ ≤ 1 / 2 * ‖w - w'‖ := by
          gcongr
          linarith

include hC he hc hce

@[simp] lemma perturbContraction_B : (𝒟.perturbContraction hC R he c hc hce).B = 𝒟.perturbB e := rfl

@[simp] lemma perturbContraction_G :
    (𝒟.perturbContraction hC R he c hc hce).G = 𝒟.perturbGerm := rfl

@[simp] lemma perturbContraction_N (m : ℕ) :
    (𝒟.perturbContraction hC R he c hc hce).N m =
      Ioo (-𝒟.perturbMu R c m) (𝒟.perturbMu R c m) ×ˢ ball (0 : P) (R.ν m) := rfl

@[simp] lemma perturbContraction_O (m : ℕ) :
    (𝒟.perturbContraction hC R he c hc hce).O m = ball (0 : W (m + 1)) (R.ρ m) := rfl

@[simp] lemma perturbContraction_K (m : ℕ) :
    (𝒟.perturbContraction hC R he c hc hce).K m = closedBall (0 : W (m + 1)) (R.ρ m / 2) := rfl

/-- `(μ, a) ∈ N(m) ∩ (ℝ × C̃)` iff `|μ| < μ_m`, `‖a‖ < ν_m`, `a ∈ C̃`. -/
lemma mem_perturbContraction_N_iff (m : ℕ) (p : ℝ × P) :
    p ∈ (𝒟.perturbContraction hC R he c hc hce).N m ∩ (univ ×ˢ Ct) ↔
      |p.1| < 𝒟.perturbMu R c m ∧ ‖p.2‖ < R.ν m ∧ p.2 ∈ Ct := by
  rw [perturbContraction_N, mem_inter_iff, mem_prod, mem_prod, mem_Ioo, mem_ball, dist_zero_right,
    abs_lt]
  simp only [mem_univ, true_and]
  tauto

/-- **Theorem 3.30 for the perturbed germ**: the solution germ `δ_e(μ, a)` is sc¹ on the
re-indexed germ `((−μ_{m+1}, μ_{m+1}) × {‖a‖ < ν_{m+1}}) ∩ (ℝ × C̃)`, with the derivative family
`solDeriv`. -/
theorem perturbContraction_isSc1GermWith :
    IsSc1GermWith ((𝒟.perturbContraction hC R he c hc hce).germ (isQuadrantLike_perturb hC) 1)
      (𝒟.perturbContraction hC R he c hc hce).sol
      ((𝒟.perturbContraction hC R he c hc hce).solDeriv
        (D := scDerivGerm 𝒟.perturbGerm (𝒟.perturbB e))) :=
  (𝒟.perturbContraction hC R he c hc hce).isSc1GermWith_sol (isQuadrantLike_perturb hC)
    (((𝒟.perturbB_isScSmoothGerm hC he).isSckGerm 1).1.isSc1GermWith_scDerivGerm)

/-- **At `μ = 0` the solution germ is the fixed point of `B(a, ·)`**: a fixed point `w ∈ W₁` of
`B(a, ·)` with `‖w‖ < ρ_0` and `‖a‖ < ν_0`, `a ∈ C̃`, is `δ_e(0, a)` (uniqueness in `O(0)`). -/
theorem perturbContraction_sol_zero {a : P} (ha : a ∈ Ct) (haν : ‖a‖ < R.ν 0) {w : W 1}
    (hw : ‖w‖ < R.ρ 0) (hfix : 𝒟.B (a, w) = w) :
    (𝒟.perturbContraction hC R he c hc hce).sol ((0 : ℝ), a) = w := by
  symm
  refine (𝒟.perturbContraction hC R he c hc hce).eq_sol ?_ ?_ ?_
  · rw [mem_perturbContraction_N_iff]
    exact ⟨by rw [abs_zero]; exact 𝒟.perturbMu_pos R c hc 0, haν, ha⟩
  · rw [perturbContraction_O, mem_ball, dist_zero_right]; exact hw
  · rw [perturbContraction_B, perturbB_apply]
    change 𝒟.B (a, w) - (0 : ℝ) • perturbEW e (a, w) = w
    rw [zero_smul, sub_zero, hfix]

end ShiftedBasicData

end Polyfold
