import GWMemoir.FredholmSections

/-!
# Propositions 4.7, 4.23, 4.25 and the filled version (Proposition 4.8)

Hofer–Wysocki–Zehnder, *Applications of Polyfold Theory I*, §§4.2–4.5 (pp. 101–122), in the local
coordinates `q = (a, v, η) ∈ O ⊆ N ⊕ E ⊕ E` of a good uniformizer, read against the book's
Theorem 3.7.1 (memoir Proposition 4.26, `GWMemoir.memoir_proposition_4_26`).

## The memoir, paraphrased

(Proposition 4.7) The Cauchy–Riemann section is sc-smooth and regularizing in the local
coordinates.  (Proposition 4.8) The filled map `f : O → F` is sc-smooth, a filled version, and for
an sc⁺-section `s` with `s(0) = f(0)` the germ `f − s` is conjugated near `0` to an
sc⁰-contraction germ.  (Proposition 4.23) (1) At smooth points near `0`, `Df(a, v, η)` is
sc-Fredholm of constant index `d`; (2) for fixed `m` and small `(a, v)`, `η ↦ f(a, v, η)` is `C¹`
from `E_m` to `F_m`; (3) for a finite-dimensional sc-complemented `K` in the `η`-space, sequences
`(a_j, v_j, k_j)`, `k_j ∈ K`, converging on level `m`, and bounded `h_j` with
`D₃f(a_j, v_j, k_j)h_j = y_j + z_j`, `y_j → 0` on level `m`, `z_j` bounded on level `m + 1`, have
`h_j` with a convergent subsequence on level `m`.  (Proposition 4.25)
`|[D₃f(a, v, 0) − D₃f(a, v, η)]h|_m ≤ λ|h|_m` for `(a, v, η)` small on level `m`.  The proof of
Proposition 4.8 (p. 121) takes `b = (a, v, k)` and gets the estimate (3) of Proposition 4.26 with
`2λ`.

## What is formalized

The coordinates are an sc-splitting `E = A ⊕ H` with `A` finite-dimensional (`(a, v)`) and `H`
the `η`-space; `D₃f(p)h` is `Df(p)h` for `h ∈ H`.

* `Prop_4_7`, `Prop_4_23` (three bullets as printed, bullet (2) on every level for fixed small
  `(a, v)`), `Prop_4_25`, `Prop_4_8` (sc-smooth, and `f − f(0)` conjugated near `0` to a basic
  germ).
* `compactnessCondition371_of_prop_4_23` (bullet (3) with `K = B ∩ H` gives condition (2) of
  Theorem 3.7.1), `derivCondition371_of_prop_4_25` (the `2λ` estimate of p. 121 gives condition
  (3) of Theorem 3.7.1).
* **`memoir_proposition_4_8_of_4_23`**: Propositions 4.7 (sc-smoothness), 4.23 and 4.25 give
  Proposition 4.8, through Proposition 4.26 (Theorem 3.7.1), for any sc-splitting `E = B ⊕ X`
  with `A ⊆ B`, `X ⊆ H`, `B` finite-dimensional and `ker Df(0) ⊆ B`.
* `prop_4_23_id`, `prop_4_25_id`, `memoir_proposition_4_8_id`: the hypotheses hold for the
  identity of `ℝ` (`A = 0`, `H = ℝ`).

## Readings

* Bullet (2) of Proposition 4.23 (`C¹` for each fixed `(a, v)`) does not give the uniform
  estimate (3) of Theorem 3.7.1; the memoir's proof of Proposition 4.8 uses Proposition 4.25 for
  it, and so does `memoir_proposition_4_8_of_4_23`.  Bullet (2) is stated and not used.
* "Small on level `m`" in Proposition 4.25 is read with `(a, v)` measured on level `0` (all
  norms agree on the finite-dimensional `A`) and `η` on level `m`, the point being on level
  `m + 1` for `D₃f` on level `m` (as for Proposition 4.26 (3)).
* Bullet (3) is read for every finite-dimensional `K ⊆ H` of smooth points (the memoir notes
  that the points of `K` are smooth); the proof uses `K = B ∩ H`.
* The constant `s = f(0)` is the book's order of Definition 3.1.11 (fill, then subtract).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace GWMemoir

open Polyfold

variable {E F : ScBanach} (U : Set (E 0)) (f : E 0 → F 0) (A H : Submodule ℝ (E 0))

/-- **Memoir Proposition 4.7, p. 102**, in local coordinates: `f` is sc-smooth and regularizing
(`f(q) ∈ F_{m+1}` for `q ∈ O_m` forces `q ∈ O_{m+1}`). -/
def Prop_4_7 : Prop :=
  IsScSmooth U f ∧ ∀ (m : ℕ) (x : E m), x ∈ E.lvlSet U m →
    f (E.toBase m x) ∈ range (F.toBase (m + 1)) → E.toBase m x ∈ range (E.toBase (m + 1))

/-- **Memoir Proposition 4.23, p. 118**, as printed, for `f` sc-smooth on `U`. -/
def Prop_4_23 (hf : IsScSmooth U f) : Prop :=
  -- (1) sc-Fredholm of constant index at smooth points
  ((∀ (x : E 1) (hx : x ∈ E.lvlSet U 1) (hs : x ∈ E.smoothLvl 1),
      IsScFredholm (derivOpAt hf hx hs)) ∧
    ∀ (x : E 1) (hx : x ∈ E.lvlSet U 1) (hs : x ∈ E.smoothLvl 1)
      (x' : E 1) (hx' : x' ∈ E.lvlSet U 1) (hs' : x' ∈ E.smoothLvl 1),
      scIndex (derivOpAt hf hx hs) = scIndex (derivOpAt hf hx' hs')) ∧
  -- (2) `η ↦ f(a, v, η)` is `C¹` on level `m` for fixed small `(a, v)`
  (∀ m : ℕ, ∃ r > 0, ∀ a : E m, E.toBase m a ∈ A → ‖E.toBase m a‖ < r →
    ContDiffOn ℝ 1 (fun η : E.levelSub H m => levelMap f m (a + η))
      {η | a + (η : E m) ∈ E.lvlSet U m}) ∧
  -- (3) the compactness property for `D₃f` along `A ⊕ K`
  (∀ (K : Submodule ℝ (E 0)), FiniteDimensional ℝ K → K ≤ H → K ≤ E.smooth →
    ∀ (m : ℕ) (p : ℕ → E (m + 1)) (p₀ : E m) (h : ℕ → E m) (y : ℕ → F m) (z : ℕ → F (m + 1)),
      (∀ j, E.toBase (m + 1) (p j) ∈ A ⊔ K ∧ p j ∈ E.lvlSet U (m + 1)) →
      E.toBase m p₀ ∈ U → Tendsto (fun j => E.incl m (p j)) atTop (𝓝 p₀) →
      (∀ j, h j ∈ E.levelSub H m) → (∃ M : ℝ, ∀ j, ‖h j‖ ≤ M) →
      (∀ j, levelDeriv (scDeriv U f) m (p j) (h j) = y j + F.incl m (z j)) →
      Tendsto y atTop (𝓝 0) → (∃ M : ℝ, ∀ j, ‖z j‖ ≤ M) →
      ∃ (h₀ : E m) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (h ∘ φ) atTop (𝓝 h₀))

/-- **Memoir Proposition 4.25, p. 121**: `|[D₃f(a, v, 0) − D₃f(a, v, η)]h|_m ≤ λ|h|_m` for
`(a, v)` small and `η ∈ H_{m+1}` small on level `m`. -/
def Prop_4_25 : Prop :=
  ∀ m : ℕ, ∀ lam > 0, ∃ r > 0, ∀ a : E (m + 1), E.toBase (m + 1) a ∈ A →
    ‖E.toBase (m + 1) a‖ < r → a ∈ E.lvlSet U (m + 1) →
    ∀ η : E (m + 1), η ∈ E.levelSub H (m + 1) → ‖E.incl m η‖ < r →
    a + η ∈ E.lvlSet U (m + 1) → ∀ h : E m, h ∈ E.levelSub H m →
      ‖levelDeriv (scDeriv U f) m a h - levelDeriv (scDeriv U f) m (a + η) h‖ ≤ lam * ‖h‖

/-- **Memoir Proposition 4.8, p. 104** (in the coordinates): `f` is sc-smooth and, with the
constant `s = f(0)`, the germ `f − s` is conjugated near `0` to a basic germ (the memoir's
sc⁰-contraction germ, the book's Definition 3.1.7). -/
def Prop_4_8 : Prop :=
  IsScSmooth U f ∧ ∃ V : Set (E 0), IsOpen V ∧ (0 : E 0) ∈ V ∧
    IsConjugateToBasicGerm (U ∩ V) fun u => f u - f 0

variable {U f A H}

/-! ### Finite-dimensional levels -/

/-- On a finite-dimensional subspace of smooth points the level-`m` norm is bounded by the
level-`0` norm. -/
theorem exists_norm_le_of_mem {B : Submodule ℝ (E 0)} [FiniteDimensional ℝ B]
    (hBs : B ≤ E.smooth) (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x : E m, E.toBase m x ∈ B → ‖x‖ ≤ C * ‖E.toBase m x‖ := by
  refine ⟨‖ScBanach.liftB hBs m‖, norm_nonneg _, fun x hx => ?_⟩
  have e : x = ScBanach.liftB hBs m ⟨E.toBase m x, hx⟩ :=
    E.toBase_injective m (by rw [ScBanach.toBase_liftB])
  calc ‖x‖ = ‖ScBanach.liftB hBs m ⟨E.toBase m x, hx⟩‖ := by rw [← e]
    _ ≤ ‖ScBanach.liftB hBs m‖ * ‖(⟨E.toBase m x, hx⟩ : B)‖ := (ScBanach.liftB hBs m).le_opNorm _
    _ = ‖ScBanach.liftB hBs m‖ * ‖E.toBase m x‖ := rfl

/-! ### From Proposition 4.25 to condition (3) of Theorem 3.7.1 -/

/-- **The `2λ` estimate of p. 121**: Proposition 4.25 gives condition (3) of Theorem 3.7.1 for a
splitting `E = B ⊕ X` with `A ⊆ B`, `X ⊆ H`: for `b = (a, v, k)` and `x ∈ X`,
`|[D₂f(b, x) − D₂f(b, 0)]h| ≤ |[D₃f(a, v, η) − D₃f(a, v, 0)]h| + |[D₃f(a, v, 0) − D₃f(a, v, k)]h|`. -/
theorem derivCondition371_of_prop_4_25 (hU : IsOpen U) (h0 : (0 : E 0) ∈ U)
    (hAH : E.IsScSplitting A H) [FiniteDimensional ℝ A] {B X : Submodule ℝ (E 0)}
    (hBX : E.IsScSplitting B X) [FiniteDimensional ℝ B] (hXH : X ≤ H)
    (h425 : Prop_4_25 U f A H) : DerivCondition371 U f B X := by
  intro m ε hε
  obtain ⟨r₀, hr₀, H₀⟩ := h425 m (ε / 2) (half_pos hε)
  have hAs : A ≤ E.smooth := (E.proposition_1_1_7_iff A).1 hAH.1
  have hBs : B ≤ E.smooth := (E.proposition_1_1_7_iff B).1 hBX.1
  obtain ⟨CB, hCB0, hCB⟩ := exists_norm_le_of_mem hBs m
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  set P := ScBanach.splitProjB hAH
  set CP := ‖P‖
  set CL := ‖ScBanach.liftB hAs m‖
  set D := CB + CL * CP + CP + 1 with hD
  have hDpos : 0 < D := by positivity
  refine ⟨min (r₀ / 2) (min (r₀ / (2 * D)) (ρ / D)), by positivity, ?_⟩
  intro b hbB hb x hx hbU hbxU hxr h hh
  have hb1 : ‖E.toBase (m + 1) b‖ < r₀ / (2 * D) := hb.trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hb2 : ‖E.toBase (m + 1) b‖ < ρ / D := hb.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hx1 : ‖E.incl m x‖ < r₀ / 2 := hxr.trans_le (min_le_left _ _)
  have hDb1 : D * ‖E.toBase (m + 1) b‖ < r₀ / 2 := by
    have e : D * (r₀ / (2 * D)) = r₀ / 2 := by field_simp
    exact (mul_lt_mul_of_pos_left hb1 hDpos).trans_eq e
  have hDb2 : D * ‖E.toBase (m + 1) b‖ < ρ := by
    have e : D * (ρ / D) = ρ := by field_simp
    exact (mul_lt_mul_of_pos_left hb2 hDpos).trans_eq e
  have hnb := norm_nonneg (E.toBase (m + 1) b)
  -- the `A`-part `a` and the `H`-part `k` of `b`
  set a₀ : A := P (E.toBase (m + 1) b)
  set a : E (m + 1) := ScBanach.liftB hAs (m + 1) a₀
  have hta : E.toBase (m + 1) a = a₀ := ScBanach.toBase_liftB hAs (m + 1) a₀
  have hka : b - a ∈ E.levelSub H (m + 1) := ScBanach.sub_liftB_mem hAs hAH (m + 1) b
  have hna₀ : ‖(a₀ : E 0)‖ ≤ CP * ‖E.toBase (m + 1) b‖ := P.le_opNorm _
  have hCPD : CP ≤ D := by
    have : 0 ≤ CL * CP := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    linarith
  have ha₀D : ‖(a₀ : E 0)‖ ≤ D * ‖E.toBase (m + 1) b‖ :=
    hna₀.trans (mul_le_mul_of_nonneg_right hCPD hnb)
  have haU : a ∈ E.lvlSet U (m + 1) := by
    rw [ScBanach.mem_lvlSet, hta]
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    exact ha₀D.trans_lt hDb2
  have hta' : ‖E.toBase (m + 1) a‖ < r₀ := by
    rw [hta]; linarith
  -- the level-`m` norm of `k = b − a`
  have hinclb : ‖E.incl m b‖ ≤ CB * ‖E.toBase (m + 1) b‖ := by
    have := hCB (E.incl m b) (by rw [← E.toBase_succ]; exact hbB)
    rwa [← E.toBase_succ] at this
  have hincla : ‖E.incl m a‖ ≤ CL * (CP * ‖E.toBase (m + 1) b‖) := by
    rw [ScBanach.incl_liftB]
    exact ((ScBanach.liftB hAs m).le_opNorm a₀).trans
      (mul_le_mul_of_nonneg_left hna₀ (norm_nonneg _))
  have hk : ‖E.incl m (b - a)‖ < r₀ / 2 := by
    rw [map_sub]
    refine (norm_sub_le _ _).trans_lt ?_
    have e : D * ‖E.toBase (m + 1) b‖ = CB * ‖E.toBase (m + 1) b‖ +
        CL * (CP * ‖E.toBase (m + 1) b‖) + (CP + 1) * ‖E.toBase (m + 1) b‖ := by
      rw [hD]; ring
    have : 0 ≤ (CP + 1) * ‖E.toBase (m + 1) b‖ := by positivity
    linarith
  have hkx : ‖E.incl m (b - a + x)‖ < r₀ := by
    rw [map_add]
    refine (norm_add_le _ _).trans_lt ?_
    linarith
  have hxH : x ∈ E.levelSub H (m + 1) := hXH hx
  have hkxH : b - a + x ∈ E.levelSub H (m + 1) := add_mem hka hxH
  have hhH : h ∈ E.levelSub H m := hXH hh
  have e1 : a + (b - a) = b := by abel
  have e2 : a + (b - a + x) = b + x := by abel
  have I1 := H₀ a (hta ▸ a₀.2) hta' haU (b - a) hka (hk.trans (half_lt_self hr₀))
    (by rw [e1]; exact hbU) h hhH
  have I2 := H₀ a (hta ▸ a₀.2) hta' haU (b - a + x) hkxH hkx (by rw [e2]; exact hbxU) h hhH
  rw [e1] at I1
  rw [e2] at I2
  calc ‖levelDeriv (scDeriv U f) m b h - levelDeriv (scDeriv U f) m (b + x) h‖
      = ‖(levelDeriv (scDeriv U f) m a h - levelDeriv (scDeriv U f) m (b + x) h) -
          (levelDeriv (scDeriv U f) m a h - levelDeriv (scDeriv U f) m b h)‖ := by
        congr 1; abel
    _ ≤ ‖levelDeriv (scDeriv U f) m a h - levelDeriv (scDeriv U f) m (b + x) h‖ +
          ‖levelDeriv (scDeriv U f) m a h - levelDeriv (scDeriv U f) m b h‖ := norm_sub_le _ _
    _ ≤ ε / 2 * ‖h‖ + ε / 2 * ‖h‖ := add_le_add I2 I1
    _ = ε * ‖h‖ := by ring

/-! ### From Proposition 4.23 (3) to condition (2) of Theorem 3.7.1 -/

/-- `B ⊆ A ⊕ (B ∩ H)` when `A ⊆ B` and `E = A ⊕ H`. -/
theorem le_sup_inf_of_split (hAH : E.IsScSplitting A H) {B : Submodule ℝ (E 0)} (hAB : A ≤ B) :
    B ≤ A ⊔ (B ⊓ H) := by
  intro v hv
  refine Submodule.mem_sup.2 ⟨ScBanach.splitProjB hAH v, (ScBanach.splitProjB hAH v).2,
    v - ScBanach.splitProjB hAH v, ⟨B.sub_mem hv (hAB (ScBanach.splitProjB hAH v).2),
      ScBanach.sub_splitProjB_mem hAH v⟩, by abel⟩

/-- **Proposition 4.23 (3) gives condition (2) of Theorem 3.7.1** for a splitting `E = B ⊕ X` with
`A ⊆ B` and `X ⊆ H` (take `K = B ∩ H`; on the finite-dimensional `B` convergence on level `0` is
convergence on level `m`). -/
theorem compactnessCondition371_of_prop_4_23 (hf : IsScSmooth U f)
    (hAH : E.IsScSplitting A H) {B X : Submodule ℝ (E 0)} (hBX : E.IsScSplitting B X)
    [FiniteDimensional ℝ B] (hAB : A ≤ B) (hXH : X ≤ H) (h423 : Prop_4_23 U f A H hf) :
    CompactnessCondition371 U f B X := by
  have hBs : B ≤ E.smooth := (E.proposition_1_1_7_iff B).1 hBX.1
  refine ⟨1, one_pos, fun m b b₀ η y z hb hb₀B hb₀U _ hbt hη hηb hD hy hz => ?_⟩
  have hK : B ⊓ H ≤ E.smooth := inf_le_left.trans hBs
  have hlift : ∀ j, E.incl m (b j) = ScBanach.liftB hBs m ⟨E.toBase (m + 1) (b j), (hb j).1⟩ :=
    fun j => E.toBase_injective m (by rw [ScBanach.toBase_liftB, ← E.toBase_succ])
  have hconv : Tendsto (fun j => E.incl m (b j)) atTop
      (𝓝 (ScBanach.liftB hBs m ⟨b₀, hb₀B⟩)) := by
    simp only [hlift]
    exact ((ScBanach.liftB hBs m).continuous.tendsto _).comp (tendsto_subtype_rng.2 hbt)
  exact h423.2.2 (B ⊓ H) inferInstance inf_le_right hK m b _ η y z
    (fun j => ⟨le_sup_inf_of_split hAH hAB (hb j).1, (hb j).2⟩)
    (by rw [ScBanach.toBase_liftB]; exact hb₀U) hconv (fun j => hXH (hη j)) hηb hD hy hz

/-! ### Proposition 4.8 -/

/-- **Memoir Propositions 4.7, 4.23 and 4.25 give Proposition 4.8** (memoir §4.5, p. 121), through
memoir Proposition 4.26 (the book's Theorem 3.7.1): for an sc-splitting `E = B ⊕ X` with
`A ⊆ B`, `X ⊆ H`, `B` finite-dimensional and `ker Df(0) ⊆ B` (the memoir's `b = (a, v, k)`), the
filled map is sc-smooth and `f − f(0)` is conjugated near `0` to a basic germ. -/
theorem memoir_proposition_4_8_of_4_23 (hUo : IsOpen U) (h0 : (0 : E 0) ∈ U)
    (h47 : Prop_4_7 U f) (h423 : Prop_4_23 U f A H h47.1) (h425 : Prop_4_25 U f A H)
    (hAH : E.IsScSplitting A H) [FiniteDimensional ℝ A] {B X : Submodule ℝ (E 0)}
    (hBX : E.IsScSplitting B X) [FiniteDimensional ℝ B] (hAB : A ≤ B) (hXH : X ≤ H)
    (hker : LinearMap.ker (scDeriv U f 0 : E 0 →ₗ[ℝ] F 0) ≤ B) : Prop_4_8 U f :=
  ⟨h47.1, memoir_proposition_4_26 hUo h0 h47.1 h423.1.1 h423.1.2 hBX hker
    (compactnessCondition371_of_prop_4_23 h47.1 hAH hBX hAB hXH h423)
    (derivCondition371_of_prop_4_25 hUo h0 hAH hBX hXH h425)⟩

/-! ### Witness: the identity of `ℝ` -/

section Witness

/-- `ℝ` with the constant sc-structure. -/
abbrev Er : ScBanach := ScBanach.const ℝ

theorem isScSmooth_id_Er : IsScSmooth (E := Er) (F := Er) univ id :=
  isScSmooth_of_bijective_toBase (bijective_toBase_const ℝ) (bijective_toBase_const ℝ)
    (isScDomain_univ _) contDiffOn_id

theorem scDeriv_id_Er : scDeriv (E := Er) (F := Er) univ id = fun _ => ContinuousLinearMap.id ℝ ℝ :=
  funext fun v => by rw [scDeriv_univ_const (V := ℝ) (V' := ℝ) contDiff_id v, fderiv_id]

theorem derivOpAt_id_Er {x : Er 1} (hx : x ∈ Er.lvlSet univ 1) (hs : x ∈ Er.smoothLvl 1) :
    derivOpAt isScSmooth_id_Er hx hs = ScOperator.id Er :=
  ScOperator.ext_base (by rw [derivOpAt_zero, scDeriv_id_Er]; rfl)

/-- Proposition 4.7 holds for the identity of `ℝ`. -/
theorem prop_4_7_id : Prop_4_7 (E := Er) (F := Er) univ id :=
  ⟨isScSmooth_id_Er, fun m _ _ _ => (bijective_toBase_const ℝ (m + 1)).2 _⟩

/-- Proposition 4.23 holds for the identity of `ℝ`, with `A = 0`, `H = ℝ`. -/
theorem prop_4_23_id : Prop_4_23 (E := Er) (F := Er) univ id ⊥ ⊤ isScSmooth_id_Er := by
  refine ⟨⟨fun x hx hs => ?_, fun x hx hs x' hx' hs' => ?_⟩, fun m => ⟨1, one_pos, ?_⟩, ?_⟩
  · rw [derivOpAt_id_Er]; exact isScFredholm_id _
  · rw [derivOpAt_id_Er, derivOpAt_id_Er]
  · intro a _ _
    have e : (fun η : Er.levelSub ⊤ m => levelMap (E := Er) (F := Er) id m (a + η)) =
        fun η : Er.levelSub ⊤ m => a + (η : Er m) := funext fun η => levelMap_eq_of_toBase_eq rfl
    rw [e]
    exact (contDiff_const.add (Er.levelSub ⊤ m).subtypeL.contDiff).contDiffOn
  · intro K _ _ _ m p p₀ h y z _ _ _ _ ⟨M, hM⟩ _ _ _
    have : ProperSpace (Er m) := inferInstanceAs (ProperSpace ℝ)
    obtain ⟨h₀, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (x := h)
      (Metric.isBounded_closedBall (x := (0 : Er m)) (r := M))
      fun j => by rw [Metric.mem_closedBall, dist_zero_right]; exact hM j
    exact ⟨h₀, φ, hφ, hlim⟩

/-- Proposition 4.25 holds for the identity of `ℝ` (`Df` is constant). -/
theorem prop_4_25_id : Prop_4_25 (E := Er) (F := Er) univ id ⊥ ⊤ := by
  intro m lam hlam
  refine ⟨1, one_pos, fun a _ _ _ η _ _ _ h _ => ?_⟩
  have e : levelDeriv (scDeriv (E := Er) (F := Er) univ id) m a =
      levelDeriv (scDeriv (E := Er) (F := Er) univ id) m (a + η) := by
    rw [scDeriv_id_Er]; rfl
  rw [e, sub_self, norm_zero]
  positivity

/-- **The hypotheses of `memoir_proposition_4_8_of_4_23` hold together** for the identity of `ℝ`
(`A = B = 0`, `H = X = ℝ`), so Proposition 4.8 follows there. -/
theorem memoir_proposition_4_8_id : Prop_4_8 (E := Er) (F := Er) univ id :=
  memoir_proposition_4_8_of_4_23 isOpen_univ (mem_univ _) prop_4_7_id prop_4_23_id prop_4_25_id
    Er.isScSplitting_bot_top Er.isScSplitting_bot_top le_rfl le_rfl (by
      rw [scDeriv_id_Er]
      intro v hv
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_id, LinearMap.id_apply] at hv
      rw [hv]; exact Submodule.zero_mem _)

end Witness

end GWMemoir
