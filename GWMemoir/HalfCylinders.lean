import GWMemoir.Skeleton

/-!
# Memoir §2.4: half-cylinders

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §2.4, pp. 43–49.

**Continuous maps.**  The domains of the gluing constructions: the half-cylinders `ℝ⁺ × S¹`
(`HalfP`) and `ℝ⁻ × S¹` (`HalfN`), the finite cylinder `Z_a = [0,R] × S¹` (`Zcyl R`), and the
infinite cylinder `C_a` in its coordinates `[s,t]` (`ℝ × S¹`), with the identification
`[s,t] = [s',t']`, `s' = s - R`, `t' = t - ϑ` (`sh`, `ush`).  `S¹ = ℝ/ℤ` with its Haar probability
measure.  `LimTop f c`, `LimBot f c`: the limits `s → ±∞` uniformly in `t`, as in the asymptotic
matching conditions of the memoir (p. 45).

**Weighted Sobolev spaces** (Memoir p. 49).  For `δ` strictly increasing with `δ₀ ≥ 0`:

* `scCyl δ`: the sc-Banach space `E_m = H^{3+m,δ_m}(ℝ × S¹)` of the project's cylinder spaces
  (`Polyfold/Chapter1/Cylinder*`), with the density of the test functions.
* `scRestr δ I`: the restriction of `H^{3+m,δ_m}(ℝ × S¹)` to `I × S¹`, as the quotient sc-Banach
  space of `scCyl δ` by the closed subspace of the maps vanishing on `I × S¹`
  (Proposition 1.1.8 of the book, `ScBanach.quotient`).  Its level `m` is
  `H^{3+m,δ_m}(ℝ × S¹) / {u : u = 0 on I × S¹}` (`mem_levelSub_vanishH`).
* `scHalfPos δ`, `scHalfNeg δ`, `scFin δ R`: `I = (0,∞)`, `(-∞,0)`, `(0,R)`, i.e.
  `H^{3+m,δ_m}(ℝ^± × S¹)` and `H^{3+m}(Z_a)`.
* `scPair δ`: the space `E` of pairs with an asymptotic constant, `u^± = c + r^±`,
  `r^± ∈ H^{3+m,δ_m}(ℝ^± × S¹)`, as `ℝ ⊕ H^{3,δ₀}(ℝ⁺ × S¹) ⊕ H^{3,δ₀}(ℝ⁻ × S¹)`.

Why restrictions and not closed subspaces: the maps on `ℝ⁺ × S¹` vanishing on `s < 0` form a
closed subspace of `H^{3+m,δ_m}(ℝ × S¹)`, but they have vanishing traces at `s = 0`, so that
subspace is smaller than `H^{3+m,δ_m}(ℝ⁺ × S¹)`.  The restriction space consists of the
restrictions of maps on the whole cylinder; it agrees with the intrinsic space on the half-cylinder
by the extension theorem for half-spaces (a reflection across `s = 0`), with an equivalent norm.
That theorem is classical and is not formalized here; the gluing constructions only evaluate maps
on `ℝ^± × S¹`, so they are defined on the restriction spaces.  On `Z_a` the weight is bounded, so
`H^{3+m,δ_m}` restricted to `Z_a` is `H^{3+m}(Z_a)` with an equivalent norm.  The norm on `scPair`
is the maximum of `|c|`, `‖r⁺‖`, `‖r⁻‖`, equivalent to the memoir's `(|c|² + ‖r⁺‖² + ‖r⁻‖²)^{1/2}`.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace GWMemoir.Neck

variable {R : ℝ} (ϑ : ℝ)
/-! ## 1. Domains, extensions and uniform asymptotic limits -/

/-- The circle `S¹ = ℝ/ℤ`, with its Haar probability measure. -/
abbrev S1 := UnitAddCircle

/-- The positive half-cylinder `ℝ⁺ × S¹`. -/
abbrev HalfP := Ici (0 : ℝ) × S1

/-- The negative half-cylinder `ℝ⁻ × S¹`. -/
abbrev HalfN := Iic (0 : ℝ) × S1

/-- The finite cylinder `Z_a = [0,R] × S¹`, in the coordinates `[s,t]`. -/
abbrev Zcyl (R : ℝ) := Icc (0 : ℝ) R × S1

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A map on `ℝ⁺ × S¹`, extended to `ℝ × S¹` by `f(s,t) = f(0,t)` for `s < 0` (only used where
the coefficients vanish). -/
def extP (f : HalfP → V) (x : ℝ × S1) : V := f (⟨max x.1 0, mem_Ici.2 (le_max_right _ _)⟩, x.2)

/-- A map on `ℝ⁻ × S¹`, extended to `ℝ × S¹` by `f(s,t) = f(0,t)` for `s > 0`. -/
def extN (f : HalfN → V) (x : ℝ × S1) : V := f (⟨min x.1 0, mem_Iic.2 (min_le_right _ _)⟩, x.2)

/-- A map on `Z_a`, extended to `ℝ × S¹` through the projection `ℝ → [0,R]`. -/
def extZ (hR : 0 ≤ R) (f : Zcyl R → V) (x : ℝ × S1) : V := f (projIcc 0 R hR x.1, x.2)

lemma extP_of_nonneg (f : HalfP → V) {s : ℝ} (hs : 0 ≤ s) (t : S1) :
    extP f (s, t) = f (⟨s, hs⟩, t) := by
  simp only [extP]; congr 2; exact Subtype.ext (max_eq_left hs)

lemma extP_mk (f : HalfP → V) (z : HalfP) : extP f (z.1.1, z.2) = f z :=
  extP_of_nonneg f z.1.2 z.2

lemma extN_of_nonpos (f : HalfN → V) {s : ℝ} (hs : s ≤ 0) (t : S1) :
    extN f (s, t) = f (⟨s, hs⟩, t) := by
  simp only [extN]; congr 2; exact Subtype.ext (min_eq_left hs)

lemma extN_mk (f : HalfN → V) (z : HalfN) : extN f (z.1.1, z.2) = f z :=
  extN_of_nonpos f z.1.2 z.2

lemma extZ_of_mem (hR : 0 ≤ R) (f : Zcyl R → V) {s : ℝ} (hs : s ∈ Icc 0 R) (t : S1) :
    extZ hR f (s, t) = f (⟨s, hs⟩, t) := by
  simp only [extZ, projIcc_of_mem hR hs]

lemma extZ_mk (hR : 0 ≤ R) (f : Zcyl R → V) (z : Zcyl R) : extZ hR f (z.1.1, z.2) = f z := by
  simp only [extZ, projIcc_val]

lemma continuous_extP {f : HalfP → V} (hf : Continuous f) : Continuous (extP f) :=
  hf.comp (((continuous_fst.max continuous_const).subtype_mk _).prodMk continuous_snd)

lemma continuous_extN {f : HalfN → V} (hf : Continuous f) : Continuous (extN f) :=
  hf.comp (((continuous_fst.min continuous_const).subtype_mk _).prodMk continuous_snd)

lemma continuous_extZ (hR : 0 ≤ R) {f : Zcyl R → V} (hf : Continuous f) :
    Continuous (extZ hR f) :=
  hf.comp ((continuous_projIcc.comp continuous_fst).prodMk continuous_snd)

variable (R)

/-- The identification of `C_a`: `[s,t] ↦ [s',t'] = (s - R, t - ϑ)`. -/
def sh (x : ℝ × S1) : ℝ × S1 := (x.1 - R, x.2 - (ϑ : S1))

/-- Its inverse `(s',t') ↦ (s' + R, t' + ϑ)`. -/
def ush (x : ℝ × S1) : ℝ × S1 := (x.1 + R, x.2 + (ϑ : S1))

variable {R ϑ}

@[simp] lemma sh_ush (x : ℝ × S1) : sh R ϑ (ush R ϑ x) = x := by
  simp [sh, ush]

@[simp] lemma ush_sh (x : ℝ × S1) : ush R ϑ (sh R ϑ x) = x := by
  simp [sh, ush]

lemma continuous_sh : Continuous (sh R ϑ) :=
  (continuous_fst.sub continuous_const).prodMk (continuous_snd.sub continuous_const)

lemma continuous_ush : Continuous (ush R ϑ) :=
  (continuous_fst.add continuous_const).prodMk (continuous_snd.add continuous_const)

/-- `f(s,t) → c` as `s → +∞`, uniformly in `t`. -/
def LimTop (f : ℝ × S1 → V) (c : V) : Prop := ∀ ε > 0, ∃ S, ∀ x : ℝ × S1, S ≤ x.1 → ‖f x - c‖ < ε

/-- `f(s,t) → c` as `s → -∞`, uniformly in `t`. -/
def LimBot (f : ℝ × S1 → V) (c : V) : Prop := ∀ ε > 0, ∃ S, ∀ x : ℝ × S1, x.1 ≤ S → ‖f x - c‖ < ε

lemma LimTop.add {f g : ℝ × S1 → V} {c d : V} (hf : LimTop f c) (hg : LimTop g d) :
    LimTop (f + g) (c + d) := fun ε hε => by
  obtain ⟨S, hS⟩ := hf (ε / 2) (by linarith)
  obtain ⟨T, hT⟩ := hg (ε / 2) (by linarith)
  refine ⟨max S T, fun x hx => ?_⟩
  have h1 := hS x (le_of_max_le_left hx)
  have h2 := hT x (le_of_max_le_right hx)
  calc ‖(f + g) x - (c + d)‖ = ‖(f x - c) + (g x - d)‖ := by simp only [Pi.add_apply]; abel_nf
    _ ≤ ‖f x - c‖ + ‖g x - d‖ := norm_add_le _ _
    _ < ε := by linarith

lemma LimBot.add {f g : ℝ × S1 → V} {c d : V} (hf : LimBot f c) (hg : LimBot g d) :
    LimBot (f + g) (c + d) := fun ε hε => by
  obtain ⟨S, hS⟩ := hf (ε / 2) (by linarith)
  obtain ⟨T, hT⟩ := hg (ε / 2) (by linarith)
  refine ⟨min S T, fun x hx => ?_⟩
  have h1 := hS x (le_trans hx (min_le_left _ _))
  have h2 := hT x (le_trans hx (min_le_right _ _))
  calc ‖(f + g) x - (c + d)‖ = ‖(f x - c) + (g x - d)‖ := by simp only [Pi.add_apply]; abel_nf
    _ ≤ ‖f x - c‖ + ‖g x - d‖ := norm_add_le _ _
    _ < ε := by linarith

lemma LimTop.smul {f : ℝ × S1 → V} {c : V} (hf : LimTop f c) (r : ℝ) :
    LimTop (r • f) (r • c) := fun ε hε => by
  obtain ⟨S, hS⟩ := hf (ε / (|r| + 1)) (by positivity)
  refine ⟨S, fun x hx => ?_⟩
  have h := hS x hx
  rw [Pi.smul_apply, ← smul_sub, norm_smul, Real.norm_eq_abs]
  calc |r| * ‖f x - c‖ ≤ (|r| + 1) * ‖f x - c‖ := by nlinarith [norm_nonneg (f x - c)]
    _ < (|r| + 1) * (ε / (|r| + 1)) := by gcongr
    _ = ε := by field_simp

lemma LimBot.smul {f : ℝ × S1 → V} {c : V} (hf : LimBot f c) (r : ℝ) :
    LimBot (r • f) (r • c) := fun ε hε => by
  obtain ⟨S, hS⟩ := hf (ε / (|r| + 1)) (by positivity)
  refine ⟨S, fun x hx => ?_⟩
  have h := hS x hx
  rw [Pi.smul_apply, ← smul_sub, norm_smul, Real.norm_eq_abs]
  calc |r| * ‖f x - c‖ ≤ (|r| + 1) * ‖f x - c‖ := by nlinarith [norm_nonneg (f x - c)]
    _ < (|r| + 1) * (ε / (|r| + 1)) := by gcongr
    _ = ε := by field_simp

lemma LimTop.zero : LimTop (0 : ℝ × S1 → V) 0 := fun ε hε => ⟨0, fun x _ => by simpa using hε⟩

lemma LimBot.zero : LimBot (0 : ℝ × S1 → V) 0 := fun ε hε => ⟨0, fun x _ => by simpa using hε⟩

lemma LimTop.congr {f g : ℝ × S1 → V} {c : V} (hf : LimTop f c) {S₀ : ℝ}
    (h : ∀ x : ℝ × S1, S₀ ≤ x.1 → g x = f x) : LimTop g c := fun ε hε => by
  obtain ⟨S, hS⟩ := hf ε hε
  exact ⟨max S S₀, fun x hx => by
    rw [h x (le_of_max_le_right hx)]; exact hS x (le_of_max_le_left hx)⟩

lemma LimBot.congr {f g : ℝ × S1 → V} {c : V} (hf : LimBot f c) {S₀ : ℝ}
    (h : ∀ x : ℝ × S1, x.1 ≤ S₀ → g x = f x) : LimBot g c := fun ε hε => by
  obtain ⟨S, hS⟩ := hf ε hε
  exact ⟨min S S₀, fun x hx => by
    rw [h x (le_trans hx (min_le_right _ _))]; exact hS x (le_trans hx (min_le_left _ _))⟩

lemma LimBot.comp_sh {f : ℝ × S1 → V} {c : V} (hf : LimBot f c) :
    LimBot (fun x => f (sh R ϑ x)) c := fun ε hε => by
  obtain ⟨S, hS⟩ := hf ε hε
  exact ⟨S + R, fun x hx => hS _ (by simp only [sh]; linarith)⟩

lemma LimBot.comp_ush {f : ℝ × S1 → V} {c : V} (hf : LimBot f c) :
    LimBot (fun x => f (ush R ϑ x)) c := fun ε hε => by
  obtain ⟨S, hS⟩ := hf ε hε
  exact ⟨S - R, fun x hx => hS _ (by simp only [ush]; linarith)⟩

lemma LimTop.const_add {f : ℝ × S1 → V} {c : V} (hf : LimTop f c) (d : V) :
    LimTop (fun x => f x + d) (c + d) := fun ε hε => by
  obtain ⟨S, hS⟩ := hf ε hε
  exact ⟨S, fun x hx => by rw [add_sub_add_right_eq_sub]; exact hS x hx⟩

lemma LimBot.const_add {f : ℝ × S1 → V} {c : V} (hf : LimBot f c) (d : V) :
    LimBot (fun x => f x + d) (c + d) := fun ε hε => by
  obtain ⟨S, hS⟩ := hf ε hε
  exact ⟨S, fun x hx => by rw [add_sub_add_right_eq_sub]; exact hS x hx⟩

lemma LimTop.neg {f : ℝ × S1 → V} {c : V} (hf : LimTop f c) : LimTop (fun x => -f x) (-c) :=
  fun ε hε => by
  obtain ⟨S, hS⟩ := hf ε hε
  exact ⟨S, fun x hx => by rw [← neg_sub', norm_neg]; exact hS x hx⟩

/-! ## 2. Weighted Sobolev spaces on the half-cylinders -/

section Sobolev

open Polyfold Polyfold.CylinderSobolev

variable (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

include h0 hmono in
lemma δ_nonneg (m : ℕ) : 0 ≤ δ m := h0.trans (hmono.monotone (Nat.zero_le m))

/-- The inclusions of `scaleGW` do not change the underlying `L²` class. -/
lemma val_toBase : ∀ (m : ℕ) (u : (scaleGW δ h0 hmono) m),
    H.val ((scaleGW δ h0 hmono).toBase m u) = H.val u
  | 0, _ => rfl
  | m + 1, u => by
    rw [ScScale.toBase_succ, val_toBase m]; rfl

lemma toBase_toH_GW {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) (m : ℕ) :
    (scaleGW δ h0 hmono).toBase m (toH (3 + m) (δ_nonneg δ h0 hmono m) hφ) =
      toH 3 (δ_nonneg δ h0 hmono 0) hφ := by
  apply valCLM_injective (m := 3) (hδ := δ_nonneg δ h0 hmono 0)
  have := val_toBase δ h0 hmono m (toH (3 + m) (δ_nonneg δ h0 hmono m) hφ)
  exact this

/-- `E_m = H^{3+m,δ_m}(ℝ × S¹)` as an sc-Banach space (Memoir p. 49; `δ₀ ≥ 0`). -/
def scCyl : ScBanach where
  toScScale := scaleGW δ h0 hmono
  dense_smooth m := by
    refine (dense_test (3 + m) (δ_nonneg δ h0 hmono m)).mono ?_
    rintro _ ⟨φ, hφ, rfl⟩
    refine (scaleGW δ h0 hmono).mem_smoothLvl_iff.2 fun j =>
      ⟨toH (3 + j) (δ_nonneg δ h0 hmono j) hφ, ?_⟩
    rw [toBase_toH_GW, toBase_toH_GW]

lemma scCyl_lvl (m : ℕ) : (scCyl δ h0 hmono) m = H (3 + m) (δ_nonneg δ h0 hmono m) := rfl

variable {δ h0 hmono}

/-- Multiplication by the indicator of `I × S¹`, on `L²(ℝ × S¹)`. -/
def indOp (I : Set ℝ) (hI : MeasurableSet I) : Lp ℝ 2 cyl →L[ℝ] Lp ℝ 2 cyl :=
  mulOp (fun x => I.indicator 1 x.1)
    ((measurable_one.indicator hI).comp measurable_fst).aestronglyMeasurable 1
    (fun x => by
      by_cases h : x.1 ∈ I <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h])

/-- The `L²` maps vanishing on `I × S¹`. -/
def vanishLp (I : Set ℝ) (hI : MeasurableSet I) : Submodule ℝ (Lp ℝ 2 cyl) :=
  LinearMap.ker (indOp I hI : Lp ℝ 2 cyl →ₗ[ℝ] Lp ℝ 2 cyl)

lemma mem_vanishLp {I : Set ℝ} {hI : MeasurableSet I} {f : Lp ℝ 2 cyl} :
    f ∈ vanishLp I hI ↔ ∀ᵐ x ∂cyl, x.1 ∈ I → f x = 0 := by
  rw [vanishLp, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Lp.eq_zero_iff_ae_eq_zero]
  have h := coeFn_mulOp (fun x => I.indicator 1 x.1)
    ((measurable_one.indicator hI).comp measurable_fst).aestronglyMeasurable 1
    (fun x => by
      by_cases h : x.1 ∈ I <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]) f
  constructor
  · intro h0'
    filter_upwards [h, h0'] with x h1 h2 hx
    have := h1.symm.trans h2
    simpa [Set.indicator_of_mem hx] using this
  · intro h0'
    filter_upwards [h, h0'] with x h1 h2
    change indOp I hI f x = 0
    rw [show indOp I hI f x = _ from h1]
    by_cases hx : x.1 ∈ I
    · simp [Set.indicator_of_mem hx, h2 hx]
    · simp [Set.indicator_of_notMem hx]

lemma isClosed_vanishLp (I : Set ℝ) (hI : MeasurableSet I) :
    IsClosed (vanishLp I hI : Set (Lp ℝ 2 cyl)) :=
  ContinuousLinearMap.isClosed_ker (indOp I hI)

variable (δ h0 hmono)

/-- The maps of `E₀ = H^{3,δ₀}(ℝ × S¹)` vanishing on `I × S¹`. -/
def vanishH (I : Set ℝ) (hI : MeasurableSet I) : Submodule ℝ ((scCyl δ h0 hmono) 0) :=
  (vanishLp I hI).comap (valCLM 3 (δ_nonneg δ h0 hmono 0) : H 3 _ →ₗ[ℝ] Lp ℝ 2 cyl)

lemma isClosed_vanishH (I : Set ℝ) (hI : MeasurableSet I) :
    IsClosed (vanishH δ h0 hmono I hI : Set ((scCyl δ h0 hmono) 0)) :=
  (isClosed_vanishLp I hI).preimage (valCLM 3 _).continuous

/-- The level `m` of the vanishing subspace: the `u ∈ H^{3+m,δ_m}` vanishing on `I × S¹`. -/
lemma mem_levelSub_vanishH {I : Set ℝ} {hI : MeasurableSet I} {m : ℕ}
    {u : (scCyl δ h0 hmono) m} :
    u ∈ (scCyl δ h0 hmono).levelSub (vanishH δ h0 hmono I hI) m ↔ H.val u ∈ vanishLp I hI := by
  rw [ScBanach.mem_levelSub]
  have := val_toBase δ h0 hmono m u
  exact Iff.of_eq (congrArg (· ∈ vanishLp I hI) this)

/-- `H^{3+m,δ_m}(ℝ × S¹)` restricted to `I × S¹`: the quotient sc-Banach space by the maps
vanishing on `I × S¹` (Proposition 1.1.8 of the book, 2021 p. 9). -/
def scRestr (I : Set ℝ) (hI : MeasurableSet I) : ScBanach :=
  (scCyl δ h0 hmono).quotient (isClosed_vanishH δ h0 hmono I hI)

/-- `H^{3+m,δ_m}(ℝ⁺ × S¹)`, `m ≥ 0` (Memoir p. 49). -/
def scHalfPos : ScBanach := scRestr δ h0 hmono (Ioi 0) measurableSet_Ioi

/-- `H^{3+m,δ_m}(ℝ⁻ × S¹)`, `m ≥ 0` (Memoir p. 49). -/
def scHalfNeg : ScBanach := scRestr δ h0 hmono (Iio 0) measurableSet_Iio

/-- `H^{3+m}(Z_a)`, `Z_a = [0,R] × S¹` (Memoir p. 50). -/
def scFin (R : ℝ) : ScBanach := scRestr δ h0 hmono (Ioo 0 R) measurableSet_Ioo

/-- The space `E` of pairs `(u⁺,u⁻)` with `u^± - c ∈ H^{3+m,δ_m}(ℝ^± × S¹)` for a common constant
`c` (Memoir p. 49), as `ℝ ⊕ H^{3+m,δ_m}(ℝ⁺ × S¹) ⊕ H^{3+m,δ_m}(ℝ⁻ × S¹)`; real-valued, the
`ℝ²ⁿ`-valued space being its `2n`-fold product. -/
def scPair : ScBanach :=
  (ScBanach.const ℝ).prod ((scHalfPos δ h0 hmono).prod (scHalfNeg δ h0 hmono))

/-- `H^{3+m,δ_m}_c(C_a)`: maps `u` on `C_a` with `u - (1 - 2β_a) c ∈ H^{3+m,δ_m}(C_a)`, as
`ℝ ⊕ H^{3+m,δ_m}(ℝ × S¹)` in the coordinates `[s,t]` (Memoir p. 50). -/
def scCylC : ScBanach := (ScBanach.const ℝ).prod (scCyl δ h0 hmono)

/-- The sc-Banach space `G^a = H³(Z_a) ⊕ H^{3,δ₀}_c(C_a)` of Memoir p. 50, `a ≠ 0`. -/
def scG (R : ℝ) : ScBanach := (scFin δ h0 hmono R).prod (scCylC δ h0 hmono)

/-- **Weighted Sobolev spaces on the half-cylinders** (Memoir p. 49): for `δ` strictly increasing
with `δ₀ ≥ 0`, the levels `H^{3+m,δ_m}(ℝ^± × S¹)` form sc-Banach spaces: Banach spaces with
compact injective inclusions and the smooth points dense in every level. -/
theorem halfCylinder_isScBanach :
    (∀ m, IsCompactOperator ((scHalfPos δ h0 hmono).incl m)) ∧
      (∀ m, Function.Injective ((scHalfPos δ h0 hmono).incl m)) ∧
      (∀ m, Dense ((scHalfPos δ h0 hmono).smoothLvl m)) ∧
      (∀ m, IsCompactOperator ((scHalfNeg δ h0 hmono).incl m)) ∧
      (∀ m, Function.Injective ((scHalfNeg δ h0 hmono).incl m)) ∧
      (∀ m, Dense ((scHalfNeg δ h0 hmono).smoothLvl m)) :=
  ⟨(scHalfPos δ h0 hmono).incl_isCompactOperator, (scHalfPos δ h0 hmono).incl_injective,
    (scHalfPos δ h0 hmono).dense_smooth, (scHalfNeg δ h0 hmono).incl_isCompactOperator,
    (scHalfNeg δ h0 hmono).incl_injective, (scHalfNeg δ h0 hmono).dense_smooth⟩

end Sobolev

end GWMemoir.Neck
