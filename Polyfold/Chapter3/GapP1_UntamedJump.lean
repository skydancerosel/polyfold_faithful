import Polyfold.Chapter1.ScOneNotNormContinuous
import Polyfold.Chapter1.LevelsWeak
import Polyfold.Chapter3.Germ

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I: an sc-smooth
family of projections whose rank jumps, in the weighted sequence space of
`Chapter1/ScOneNotNormContinuous`.
Used by `GapP1_UntamedCounterexample.lean` (gap G.79: 2021 Theorem 3.6.8, p. 136, and 2021
Definitions 3.1.4, 3.6.1, 3.6.3 with untamed germ data).

# A moving rank-one projection `π_t`, sc-smooth in `(t, h)` and zero for `t ≤ 0`

## The text, paraphrased

The text has no numbered item for this.  After Theorem 2.3.16 (p. 40) it notes that M-polyfolds
describe objects with locally varying dimensions and refers to [60], Section 1, Example 1.22, for
the construction (a retraction `(t, u) ↦ (t, π_t u)` built from a bump function moved to infinity
as `t ↓ 0`); strong bundle retractions (Definition 2.6.1, p. 65) may have such fibres.
Proposition 1.2.4 (p. 13) gives sc-smoothness from the classical smoothness of
`f : U_{m+l} → F_m` (class `C^{l+1}`).

## What is formalized

* `Polyfold.Jump.Family V` (**a jump family** on an sc-Banach space `V`): operators
  `A_m(t) : V_m → V_m` and `A'_m(t) : V_{m+1} → V_m`, compatible with the inclusions, with
  `(t, h) ↦ A_m(t)h` continuous on every level, `t ↦ A_m(t)|_{V_{m+1}}` differentiable in the
  operator norm with derivative `A'_m(t)`, and `(s, t, h) ↦ s A'(t)h : ℝ² ⊕ V¹ → V` sc-smooth.
  `Family.isScSmooth_map`: **`(t, h) ↦ A(t)h : ℝ ⊕ V → V` is sc-smooth**; `Family.shift` (the
  family on `V¹`), `Family.isScSmooth_shift_map`.  Nothing is asked of `t ↦ A_m(t)` in the
  operator norm of one level, so the rank may jump.
* The concrete family `Polyfold.Jump.family : Family X` on `X = ScOneExample.X` (weighted `c₀`,
  `|x|_m = sup (k+1)^m |x_k|`): `π_t = ℓ_t ⊗ e(t)` with `e(t) = Σ_i Λ(2ⁱ t) e_{K_i}`,
  `ℓ_t = Σ_i Λ(2ⁱ t) δ_{K_i}`, positions `K_i = 16ⁱ − 1` (`Jump.pos`) and the profile
  `Λ(s) = cos(π/2 · S(s − 1)) · sin(π/2 · S(2s − 1))` (`Jump.prof`, `S = Real.smoothTransition`).
  On levels it is `Jump.T j g b t` (the `j`-th `t`-derivative, from level `b + g` to level `b`):
  `T_inclOp`, `inclOp_T` (compatibility with the inclusions), `hasDerivAt_T` (differentiable in
  the operator norm when `j + 2 ≤ 4g`: one level pays for one derivative), `continuous_T_zero`
  (strong continuity on one level), `isScSmooth_deriv` (Proposition 1.2.4 for
  `(s, t, h) ↦ s π'(t)h`).
* The projection on level `0`, `Polyfold.Jump.proj t`: `proj_of_nonpos` (`π_t = 0` for `t ≤ 0`),
  `exists_proj_eq` (for `0 < t < 1`, `π_t = ℓ ⊗ e` with `ℓ(e) = 1` and
  `e = cos θ e_{K_{n+1}} + sin θ e_{K_n}`), `proj_proj` (`π_t² = π_t` for `t < 1`),
  `proj_ne_zero`, `eq_zero_of_proj_eq`, `T_one_one_of_nonpos` (`π'(t) = 0` for `t ≤ 0`).

## What the text leaves implicit, and the choices made

* **Proposition 1.2.4 does not apply to `(t, h) ↦ π_t h` itself**: on one level it is not `C¹`
  (it is not norm-continuous in `t`).  The sc-smoothness is proved by induction on the tangent
  map: `T(π) = (π¹, δt · π'(t)h + π_t δh)`, where `π¹` is the family of the shifted space and
  `(s, t, h) ↦ s π'(t)h : ℝ² ⊕ V¹ → V` is covered by Proposition 1.2.4.
* **A sequence space instead of weighted Sobolev spaces.**  The bump moves through the positions
  `K_i = 16ⁱ − 1`, where the weight `1/(k+1)` of the scale is exactly `16⁻ⁱ`; at `t ≈ 2⁻ⁱ` a
  `t`-derivative costs `2ⁱ` and one level gains `16⁻ⁱ`.  The ratio of consecutive weights is
  bounded, which the strong continuity on one level needs.
* **Instances.**  For `c₀` and `ℓ^∞` the algebraic instances are available both directly and
  through the norms; the operator spaces are written `Jump.CLM V W`, an abbreviation of
  `V →L[ℝ] W` elaborated with normed-space arguments, so that one instance path is used.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold
namespace Jump

/-! ### Families of operators which lose one level per `t`-derivative -/

/-- **A jump family on an sc-Banach space `V`**: operators `A_m(t) : V_m → V_m` (the level maps
of `(t, h) ↦ A(t)h`) and `A'_m(t) : V_{m+1} → V_m` (the `t`-derivative, which loses one level),
compatible with the inclusions, such that `(t, h) ↦ A_m(t)h` is continuous on every level (strong
continuity), `t ↦ A_m(t)|_{V_{m+1}}` is differentiable in the operator norm with derivative
`A'_m(t)`, `t ↦ A'_m(t)` is norm-continuous, and `(s, t, h) ↦ s A'(t)h : ℝ² ⊕ V¹ → V` is
sc-smooth.  Nothing is asked of `t ↦ A_m(t)` in the operator norm of one level: the rank of
`A_m(t)` may jump. -/
structure Family (V : ScBanach) where
  /-- The level-`m` operator `A_m(t)`. -/
  A : ∀ m, ℝ → V m →L[ℝ] V m
  /-- The `t`-derivative `A'_m(t) : V_{m+1} → V_m`. -/
  A' : ∀ m, ℝ → V (m + 1) →L[ℝ] V m
  incl_A : ∀ m t (x : V (m + 1)), V.incl m (A (m + 1) t x) = A m t (V.incl m x)
  incl_A' : ∀ m t (x : V (m + 1 + 1)), V.incl m (A' (m + 1) t x) = A' m t (V.incl (m + 1) x)
  cont_A : ∀ m, Continuous fun p : ℝ × V m => A m p.1 p.2
  cont_A' : ∀ m, Continuous (A' m)
  deriv_A : ∀ m t, HasDerivAt (fun s => (A m s).comp (V.incl m)) (A' m t) t
  smooth_A' : IsScSmooth (E := (ScBanach.const (ℝ × ℝ)).prod V.shift) (F := V) univ
    (fun p => p.1.1 • A' 0 p.1.2 p.2)

namespace Family

variable {V : ScBanach} (J : Family V)

/-- The map `(t, h) ↦ A(t)h : ℝ ⊕ V → V`. -/
def map : ((ScBanach.const ℝ).prod V) 0 → V 0 := fun p => J.A 0 p.1 p.2

/-- The map `(s, t, h) ↦ s A'(t)h : ℝ² ⊕ V¹ → V`. -/
def map' : ((ScBanach.const (ℝ × ℝ)).prod V.shift) 0 → V 0 := fun p => p.1.1 • J.A' 0 p.1.2 p.2

lemma toBase_A : ∀ (m : ℕ) (t : ℝ) (y : V m), V.toBase m (J.A m t y) = J.A 0 t (V.toBase m y)
  | 0, _, _ => rfl
  | m + 1, t, y => by
    rw [V.toBase_succ, J.incl_A, toBase_A m, ← V.toBase_succ]

lemma toBase_A' : ∀ (m : ℕ) (t : ℝ) (y : V (m + 1)),
    V.toBase m (J.A' m t y) = J.A' 0 t (V.shift.toBase m y)
  | 0, _, _ => rfl
  | m + 1, t, y => by
    rw [V.toBase_succ, J.incl_A', toBase_A' m]; rfl

lemma levelMap_map (m : ℕ) (x : ((ScBanach.const ℝ).prod V) m) :
    levelMap J.map m x = J.A m x.1 x.2 := by
  refine levelMap_eq_of_toBase_eq ?_
  rw [J.toBase_A, ScBanach.prod_toBase, ScBanach.const_toBase]; rfl

/-- `(t, h) ↦ A(t)h` is sc⁰. -/
theorem isSc0_map : IsSc0 ((ScBanach.const ℝ).prod V) V univ J.map where
  mem_range m x _ := ⟨J.A m x.1 x.2, by
    rw [J.toBase_A, ScBanach.prod_toBase, ScBanach.const_toBase]; rfl⟩
  continuousOn m := by
    have : levelMap J.map m = fun x : ℝ × V m => J.A m x.1 x.2 := funext (J.levelMap_map m)
    rw [this]; exact (J.cont_A m).continuousOn

/-- The jump family of the shifted space `V¹`. -/
def shift : Family V.shift where
  A m := J.A (m + 1)
  A' m := J.A' (m + 1)
  incl_A m := J.incl_A (m + 1)
  incl_A' m := J.incl_A' (m + 1)
  cont_A m := J.cont_A (m + 1)
  cont_A' m := J.cont_A' (m + 1)
  deriv_A m := J.deriv_A (m + 1)
  smooth_A' := by
    have h := IsScSmooth.shift (isScDomain_univ _) J.smooth_A'
    have hset : ((ScBanach.const (ℝ × ℝ)).prod V.shift).lvlSet univ 1 = univ := by
      exact eq_univ_of_forall fun x => mem_univ _
    rw [hset] at h
    refine IsScSmooth.congr (isScDomain_univ _) (fun p _ => ?_) h
    refine levelMap_eq_of_toBase_eq ?_
    change V.incl 0 (p.1.1 • J.A' 1 p.1.2 p.2) = p.1.1 • J.A' 0 p.1.2 (V.incl 1 p.2)
    rw [map_smul, J.incl_A']

/-- The derivative family of `(t, h) ↦ A(t)h`: `(δt, δh) ↦ δt A'(t)h + A(t)δh` at
`(t, h) ∈ ℝ ⊕ V₁`. -/
def D (x : ((ScBanach.const ℝ).prod V) 1) : ((ScBanach.const ℝ).prod V) 0 →L[ℝ] V 0 :=
  (ContinuousLinearMap.fst ℝ ℝ (V 0)).smulRight (J.A' 0 x.1 x.2) +
    (J.A 0 x.1).comp (ContinuousLinearMap.snd ℝ ℝ (V 0))

lemma D_apply (x : ((ScBanach.const ℝ).prod V) 1) (q : ((ScBanach.const ℝ).prod V) 0) :
    J.D x q = q.1 • J.A' 0 x.1 x.2 + J.A 0 x.1 q.2 := rfl

/-- The level-`1` form of `(t, h) ↦ A(t)h` is differentiable, with derivative `D`. -/
lemma hasFDerivAt_map (x : ((ScBanach.const ℝ).prod V) 1) :
    HasFDerivAt (J.map ∘ ((ScBanach.const ℝ).prod V).toBase 1)
      ((J.D x).comp (((ScBanach.const ℝ).prod V).toBase 1)) x := by
  have hc : HasFDerivAt (fun p : ℝ × V 1 => (J.A 0 p.1).comp (V.incl 0))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (J.A' 0 x.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ (V 1))) x :=
    (J.deriv_A 0 x.1).hasFDerivAt.comp x hasFDerivAt_fst
  have hu : HasFDerivAt (fun p : ℝ × V 1 => p.2) (ContinuousLinearMap.snd ℝ ℝ (V 1)) x :=
    hasFDerivAt_snd
  refine (hc.clm_apply hu).congr_fderiv ?_
  have hb : ∀ q : ℝ × V 1, ((ScBanach.const ℝ).prod V).toBase 1 q = (q.1, V.incl 0 q.2) :=
    fun _ => rfl
  ext q
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, hb, map_zero]
    change _ = (1 : ℝ) • J.A' 0 x.1 x.2 + J.A 0 x.1 0
    simp
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hb]
    change _ = (0 : ℝ) • J.A' 0 x.1 x.2 + J.A 0 x.1 (V.incl 0 q)
    simp

/-- The level maps of the tangent map of `(t, h) ↦ A(t)h`. -/
def tangentLvl (m : ℕ) (x : ((ScBanach.const ℝ).prod V).tangent m) : V.tangent m :=
  (J.A (m + 1) x.1.1 x.1.2, x.2.1 • J.A' m x.1.1 x.1.2 + J.A m x.1.1 x.2.2)

lemma toBase_tangentLvl (m : ℕ) (x : ((ScBanach.const ℝ).prod V).tangent m) :
    V.tangent.toBase m (J.tangentLvl m x) =
      tangentMapWith J.map J.D (((ScBanach.const ℝ).prod V).tangent.toBase m x) := by
  rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase]
  refine Prod.ext ?_ ?_
  · change V.shift.toBase m (J.A (m + 1) x.1.1 x.1.2) =
      levelMap J.map 1 (((ScBanach.const ℝ).prod V.shift).toBase m x.1)
    rw [J.levelMap_map, ScBanach.prod_toBase, ScBanach.const_toBase]
    exact J.shift.toBase_A m x.1.1 x.1.2
  · change V.toBase m (x.2.1 • J.A' m x.1.1 x.1.2 + J.A m x.1.1 x.2.2) =
      J.D (((ScBanach.const ℝ).prod V.shift).toBase m x.1)
        (((ScBanach.const ℝ).prod V).toBase m x.2)
    rw [D_apply, ScBanach.prod_toBase, ScBanach.prod_toBase, ScBanach.const_toBase,
      ScBanach.const_toBase, map_add, map_smul, J.toBase_A', J.toBase_A]

lemma continuous_tangentLvl (m : ℕ) : Continuous (J.tangentLvl m) := by
  refine Continuous.prodMk ?_ (Continuous.add ?_ ?_)
  · exact (J.cont_A (m + 1)).comp continuous_fst
  · refine Continuous.smul (continuous_fst.comp continuous_snd) ?_
    exact ((J.cont_A' m).comp (continuous_fst.comp continuous_fst)).clm_apply
      (continuous_snd.comp continuous_fst)
  · exact (J.cont_A m).comp
      ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))

/-- `(t, h) ↦ A(t)h` is sc¹ with the derivative family `D`. -/
theorem isSc1With_map : IsSc1With univ J.map J.D where
  isSc0 := J.isSc0_map
  hasFDerivWithinAt x _ := (J.hasFDerivAt_map x).hasFDerivWithinAt
  tangent_isSc0 :=
    { mem_range := fun m x _ => ⟨J.tangentLvl m x, J.toBase_tangentLvl m x⟩
      continuousOn := fun m => by
        have : levelMap (tangentMapWith J.map J.D) m = J.tangentLvl m :=
          funext fun x => levelMap_eq_of_toBase_eq (J.toBase_tangentLvl m x)
        rw [this]; exact (J.continuous_tangentLvl m).continuousOn }

/-- `((t, h), (δt, δh)) ↦ ((δt, t), h)`. -/
def opL1 (V : ScBanach) : ScOperator ((ScBanach.const ℝ).prod V).tangent
    ((ScBanach.const (ℝ × ℝ)).prod V.shift) where
  lvl m := ((((ContinuousLinearMap.fst ℝ ℝ (V m)).comp
      (ContinuousLinearMap.snd ℝ (ℝ × V (m + 1)) (ℝ × V m))).prod
    ((ContinuousLinearMap.fst ℝ ℝ (V (m + 1))).comp
      (ContinuousLinearMap.fst ℝ (ℝ × V (m + 1)) (ℝ × V m)))).prod
    ((ContinuousLinearMap.snd ℝ ℝ (V (m + 1))).comp
      (ContinuousLinearMap.fst ℝ (ℝ × V (m + 1)) (ℝ × V m))))
  incl_comm _ _ := rfl

/-- `((t, h), (δt, δh)) ↦ (t, δh)`. -/
def opL2 (V : ScBanach) : ScOperator ((ScBanach.const ℝ).prod V).tangent
    ((ScBanach.const ℝ).prod V) where
  lvl m := ((ContinuousLinearMap.fst ℝ ℝ (V (m + 1))).comp
      (ContinuousLinearMap.fst ℝ (ℝ × V (m + 1)) (ℝ × V m))).prod
    ((ContinuousLinearMap.snd ℝ ℝ (V m)).comp
      (ContinuousLinearMap.snd ℝ (ℝ × V (m + 1)) (ℝ × V m)))
  incl_comm _ _ := rfl

/-- **A jump family is sc-smooth**: `(t, h) ↦ A(t)h : ℝ ⊕ V → V` is sc^k for every `k`.  Induction
on `k` over all jump families: the tangent map is the pair of the map of the shifted family and
`δt A'(t)h + A(t)δh`, and `(s, t, h) ↦ s A'(t)h` is sc-smooth by hypothesis. -/
theorem isSck_map : ∀ (k : ℕ) {V : ScBanach} (J : Family V),
    IsSck k ((ScBanach.const ℝ).prod V) V univ J.map
  | 0, _, J => J.isSc0_map
  | k + 1, V, J => by
    have hU := isScDomain_univ ((ScBanach.const ℝ).prod V)
    have hT := hU.tangentSet
    refine ⟨J.isSc1With_map.isSc1, ?_⟩
    refine IsSck.congr hT
      (IsSc1.tangentMap_eqOn J.isSc1With_map (hU.uniqueDiffWithinAt 1)).symm ?_
    have h1 : IsSck k ((ScBanach.const ℝ).prod V).tangent V.shift
        (((ScBanach.const ℝ).prod V).tangentSet univ)
        (J.shift.map ∘ (((ScBanach.const ℝ).prod V).shift.fstOp ((ScBanach.const ℝ).prod V)) 0) :=
      IsSck.comp hT (isScDomain_univ _) (isSck_map k J.shift)
        ((ScOperator.isScSmooth _ hT) k) (mapsTo_univ _ _)
    have h2 : IsSck k ((ScBanach.const ℝ).prod V).tangent V
        (((ScBanach.const ℝ).prod V).tangentSet univ) (J.map' ∘ (opL1 V) 0) :=
      IsSck.comp hT (isScDomain_univ _) (J.smooth_A' k)
        ((ScOperator.isScSmooth _ hT) k) (mapsTo_univ _ _)
    have h3 : IsSck k ((ScBanach.const ℝ).prod V).tangent V
        (((ScBanach.const ℝ).prod V).tangentSet univ) (J.map ∘ (opL2 V) 0) :=
      IsSck.comp hT (isScDomain_univ _) (isSck_map k J)
        ((ScOperator.isScSmooth _ hT) k) (mapsTo_univ _ _)
    refine IsSck.congr hT (fun p _ => ?_) (IsSck.scPair hT h1 (IsSck.add hT h2 h3))
    refine Prod.ext ?_ rfl
    exact (J.levelMap_map 1 p.1).symm

/-- A jump family is sc-smooth. -/
theorem isScSmooth_map : IsScSmooth univ J.map := fun k => isSck_map k J

/-- The jump family of the shifted space is sc-smooth: `(t, h) ↦ A₁(t)h : ℝ ⊕ V¹ → V¹`. -/
theorem isScSmooth_shift_map : IsScSmooth univ J.shift.map := J.shift.isScSmooth_map

end Family

/-! ### Generic facts (stated for abstract normed spaces) -/

/-- `V →L[ℝ] W`, elaborated with the instances coming from the norms.  (For `c₀` and `ℓ^∞` the
algebraic instances are also available directly; writing the operator spaces through this
abbreviation keeps one instance path.) -/
abbrev CLM (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] : Type _ := V →L[ℝ] W

/-- `D a + p U b + q N b`. -/
def three {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V]
    [NormedSpace ℝ V] (D U N : P →L[ℝ] V) (p q : ℝ) (a b : P) : V := D a + p • U b + q • N b


theorem hasDerivAt_three {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (D U N : P →L[ℝ] V) (p q : ℝ) {a b : ℝ → P}
    {a' b' : P} {t : ℝ} (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => three D U N p q (a s) (b s)) (three D U N p q a' b') t :=
  ((D.hasFDerivAt.comp_hasDerivAt t ha).add
    ((U.hasFDerivAt.comp_hasDerivAt t hb).const_smul p)).add
    ((N.hasFDerivAt.comp_hasDerivAt t hb).const_smul q)

theorem continuous_three {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (D U N : P →L[ℝ] V) (p q : ℝ) {a b : ℝ → P}
    (ha : Continuous a) (hb : Continuous b) :
    Continuous fun s => three D U N p q (a s) (b s) :=
  ((D.continuous.comp ha).add ((U.continuous.comp hb).const_smul p)).add
    ((N.continuous.comp hb).const_smul q)

/-- A chain of derivatives ending in a continuous map gives `C^n`. -/
theorem contDiff_of_chain {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : ℕ → ℝ → V) :
    ∀ (n j : ℕ), (∀ i, j ≤ i → i < j + n → ∀ t, HasDerivAt (F i) (F (i + 1) t) t) →
      Continuous (F (j + n)) → ContDiff ℝ n (F j)
  | 0, j, _, hc => by rw [Nat.cast_zero, contDiff_zero]; exact hc
  | n + 1, j, hd, hc => by
    have hder : deriv (F j) = F (j + 1) := funext fun t => (hd j le_rfl (by omega) t).deriv
    rw [Nat.cast_succ, contDiff_succ_iff_deriv, hder]
    refine ⟨fun t => (hd j le_rfl (by omega) t).differentiableAt, by simp, ?_⟩
    exact contDiff_of_chain F n (j + 1) (fun i hi hi' => hd i (by omega) (by omega))
      (by rw [show j + 1 + n = j + (n + 1) by omega]; exact hc)

theorem contDiff_smul_apply {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {n : WithTop ℕ∞} {A : ℝ → V →L[ℝ] W}
    (hA : ContDiff ℝ n A) : ContDiff ℝ n fun x : (ℝ × ℝ) × V => x.1.1 • A x.1.2 x.2 :=
  (contDiff_fst.fst).smul ((hA.comp contDiff_fst.snd).clm_apply contDiff_snd)

theorem continuous_smul_apply {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {A : ℝ → V →L[ℝ] W}
    (hA : Continuous A) : Continuous fun x : (ℝ × ℝ) × V => x.1.1 • A x.1.2 x.2 :=
  (continuous_fst.comp continuous_fst).smul
    ((hA.comp (continuous_snd.comp continuous_fst)).clm_apply continuous_snd)

/-! ### The profile -/

/-- The profile `Λ(s) = cos(π/2 · S(s − 1)) · sin(π/2 · S(2s − 1))`. -/
def prof (s : ℝ) : ℝ :=
  Real.cos (Real.pi / 2 * Real.smoothTransition (s - 1)) *
    Real.sin (Real.pi / 2 * Real.smoothTransition (2 * s - 1))

lemma contDiff_prof : ContDiff ℝ ∞ prof := by
  have h1 : ContDiff ℝ ∞ fun s : ℝ => Real.pi / 2 * Real.smoothTransition (s - 1) :=
    contDiff_const.mul (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))
  have h2 : ContDiff ℝ ∞ fun s : ℝ => Real.pi / 2 * Real.smoothTransition (2 * s - 1) :=
    contDiff_const.mul (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const))
  exact (Real.contDiff_cos.comp h1).mul (Real.contDiff_sin.comp h2)

lemma prof_of_le_half {s : ℝ} (hs : s ≤ 1 / 2) : prof s = 0 := by
  unfold prof
  rw [Real.smoothTransition.zero_of_nonpos (x := 2 * s - 1) (by linarith), mul_zero, Real.sin_zero,
    mul_zero]

lemma prof_of_two_le {s : ℝ} (hs : 2 ≤ s) : prof s = 0 := by
  unfold prof
  rw [Real.smoothTransition.one_of_one_le (x := s - 1) (by linarith), mul_one, Real.cos_pi_div_two,
    zero_mul]

lemma prof_of_one_le {s : ℝ} (hs : 1 ≤ s) :
    prof s = Real.cos (Real.pi / 2 * Real.smoothTransition (s - 1)) := by
  unfold prof
  rw [Real.smoothTransition.one_of_one_le (x := 2 * s - 1) (by linarith), mul_one,
    Real.sin_pi_div_two, mul_one]

lemma prof_of_le_one {s : ℝ} (hs : s ≤ 1) :
    prof s = Real.sin (Real.pi / 2 * Real.smoothTransition (2 * s - 1)) := by
  unfold prof
  rw [Real.smoothTransition.zero_of_nonpos (x := s - 1) (by linarith), mul_zero, Real.cos_zero,
    one_mul]

/-- For `0 < t < 1` exactly two consecutive values `Λ(2ⁱ t)` can be non-zero, and they are
`(sin θ, cos θ)` with `0 ≤ θ ≤ π/2`. -/
lemma exists_angle {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ∃ (n : ℕ) (θ : ℝ), 0 ≤ θ ∧ θ ≤ Real.pi / 2 ∧ prof (2 ^ (n + 1) * t) = Real.cos θ ∧
      prof (2 ^ n * t) = Real.sin θ ∧ ∀ i, i ≠ n → i ≠ n + 1 → prof (2 ^ i * t) = 0 := by
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := 1 / t) (y := (2 : ℝ))
    (by rw [le_div_iff₀ h0]; linarith) one_lt_two
  have hle : (2 : ℝ) ^ n * t ≤ 1 := by rwa [le_div_iff₀ h0] at hn1
  have hlt : 1 < (2 : ℝ) ^ (n + 1) * t := by rwa [div_lt_iff₀ h0] at hn2
  have hs : (2 : ℝ) ^ (n + 1) * t = 2 * (2 ^ n * t) := by ring
  have hpos : 0 < (2 : ℝ) ^ n * t := by positivity
  refine ⟨n, Real.pi / 2 * Real.smoothTransition (2 ^ (n + 1) * t - 1),
    mul_nonneg (by positivity) (Real.smoothTransition.nonneg _), ?_, prof_of_one_le hlt.le, ?_, ?_⟩
  · calc Real.pi / 2 * Real.smoothTransition (2 ^ (n + 1) * t - 1) ≤ Real.pi / 2 * 1 :=
        mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) (by positivity)
      _ = Real.pi / 2 := mul_one _
  · rw [prof_of_le_one hle, hs]
  · intro i hi hi'
    rcases lt_or_gt_of_ne hi with h | h
    · -- `i < n`: `2ⁱ t ≤ 2ⁿ t / 2 ≤ 1/2`
      refine prof_of_le_half ?_
      have : (2 : ℝ) ^ n = 2 ^ (n - i - 1) * 2 * 2 ^ i := by
        rw [← pow_succ, ← pow_add]; congr 1; omega
      have h2 : (1 : ℝ) ≤ 2 ^ (n - i - 1) := one_le_pow₀ one_le_two
      have h3 : 0 < (2 : ℝ) ^ i * t := by positivity
      rw [this] at hle
      nlinarith
    · -- `i ≥ n + 2`: `2ⁱ t ≥ 2 · 2^{n+1} t ≥ 2`
      refine prof_of_two_le ?_
      have hi2 : n + 2 ≤ i := by omega
      have : (2 : ℝ) ^ i = 2 ^ (i - (n + 2)) * 2 * 2 ^ (n + 1) := by
        rw [mul_assoc, ← pow_succ', ← pow_add]; congr 1; omega
      have h2 : (1 : ℝ) ≤ 2 ^ (i - (n + 2)) := one_le_pow₀ one_le_two
      rw [this]
      nlinarith

lemma prof_two_pow_of_nonpos {t : ℝ} (ht : t ≤ 0) (i : ℕ) : prof (2 ^ i * t) = 0 :=
  prof_of_le_half (by
    have : (2 : ℝ) ^ i * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) ht
    linarith)

lemma hasCompactSupport_prof : HasCompactSupport prof :=
  HasCompactSupport.intro (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2)) fun x hx => by
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · exact prof_of_le_half h.le
    · exact prof_of_two_le h.le

/-- `Φ₀ = Λ²`: the diagonal coefficient. -/
def phi0 (s : ℝ) : ℝ := prof s * prof s

/-- `Φ₁(s) = Λ(s) Λ(2s)`: the off-diagonal coefficient. -/
def phi1 (s : ℝ) : ℝ := prof s * prof (2 * s)

/-- A profile: smooth with compact support. -/
structure IsProfile (φ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ φ
  compact : HasCompactSupport φ

lemma isProfile_phi0 : IsProfile phi0 :=
  ⟨contDiff_prof.mul contDiff_prof, hasCompactSupport_prof.mul_left⟩

lemma isProfile_phi1 : IsProfile phi1 :=
  ⟨contDiff_prof.mul (contDiff_prof.comp (contDiff_const.mul contDiff_id)),
    hasCompactSupport_prof.mul_right⟩

namespace IsProfile

variable {φ : ℝ → ℝ} (hφ : IsProfile φ)
include hφ

lemma contDiff_iter (j : ℕ) : ContDiff ℝ ∞ (deriv^[j] φ) := by
  induction j with
  | zero => exact hφ.contDiff
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact ((contDiff_succ_iff_deriv (n := ∞)).1 (by simpa using ih)).2.2

lemma hasDerivAt_iter (j : ℕ) (s : ℝ) : HasDerivAt (deriv^[j] φ) (deriv^[j + 1] φ s) s := by
  rw [Function.iterate_succ_apply']
  exact ((hφ.contDiff_iter j).differentiable (by simp)).differentiableAt.hasDerivAt

lemma compact_iter (j : ℕ) : HasCompactSupport (deriv^[j] φ) := by
  induction j with
  | zero => exact hφ.compact
  | succ j ih => rw [Function.iterate_succ_apply']; exact ih.deriv

lemma exists_bound (j : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, |deriv^[j] φ s| ≤ M := by
  obtain ⟨C, hC⟩ := (hφ.contDiff_iter j).continuous.bounded_above_of_compact_support
    (hφ.compact_iter j)
  exact ⟨C, (abs_nonneg _).trans (hC 0), hC⟩

/-- A bound for the `j`-th derivative. -/
def bd (j : ℕ) : ℝ := (hφ.exists_bound j).choose

lemma bd_nonneg (j : ℕ) : 0 ≤ hφ.bd j := (hφ.exists_bound j).choose_spec.1

lemma abs_le_bd (j : ℕ) (s : ℝ) : |deriv^[j] φ s| ≤ hφ.bd j := (hφ.exists_bound j).choose_spec.2 s

lemma abs_sub_le (j : ℕ) (x y : ℝ) :
    |deriv^[j] φ y - deriv^[j] φ x| ≤ hφ.bd (j + 1) * |y - x| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := deriv^[j] φ)
    (f' := deriv^[j + 1] φ) (s := univ) (x := x) (y := y) (C := hφ.bd (j + 1))
    (fun z _ => (hφ.hasDerivAt_iter j z).hasDerivWithinAt) (fun z _ => hφ.abs_le_bd (j + 1) z)
    convex_univ (mem_univ _) (mem_univ _)
  simpa [Real.norm_eq_abs] using this

/-- Second-order Taylor bound. -/
lemma abs_taylor_le (j : ℕ) (x δ : ℝ) :
    |deriv^[j] φ (x + δ) - deriv^[j] φ x - δ * deriv^[j + 1] φ x| ≤ hφ.bd (j + 2) * δ ^ 2 := by
  have hd : ∀ z ∈ (univ : Set ℝ), HasDerivWithinAt
      (fun z => deriv^[j] φ z - z * deriv^[j + 1] φ x)
      (deriv^[j + 1] φ z - deriv^[j + 1] φ x) univ z := fun z _ =>
    ((hφ.hasDerivAt_iter j z).sub (by simpa using (hasDerivAt_id z).mul_const _)).hasDerivWithinAt
  have hb : ∀ z ∈ segment ℝ x (x + δ), ‖deriv^[j + 1] φ z - deriv^[j + 1] φ x‖ ≤
      hφ.bd (j + 2) * |δ| := fun z hz => by
    rw [Real.norm_eq_abs]
    refine (hφ.abs_sub_le (j + 1) x z).trans (mul_le_mul_of_nonneg_left ?_ (hφ.bd_nonneg _))
    rw [segment_eq_image'] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    simp only [add_sub_cancel_left, smul_eq_mul]
    rw [abs_mul, abs_of_nonneg hθ.1]
    exact mul_le_of_le_one_left (abs_nonneg _) hθ.2
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => deriv^[j] φ z - z * deriv^[j + 1] φ x)
    (s := segment ℝ x (x + δ)) (x := x) (y := x + δ)
    (fun z hz => (hd z (mem_univ _)).mono (subset_univ _)) hb (convex_segment _ _)
    (left_mem_segment _ _ _) (right_mem_segment _ _ _)
  rw [Real.norm_eq_abs] at this
  calc |deriv^[j] φ (x + δ) - deriv^[j] φ x - δ * deriv^[j + 1] φ x|
      = |deriv^[j] φ (x + δ) - (x + δ) * deriv^[j + 1] φ x -
          (deriv^[j] φ x - x * deriv^[j + 1] φ x)| := by congr 1; ring
    _ ≤ hφ.bd (j + 2) * |δ| * ‖x + δ - x‖ := this
    _ = hφ.bd (j + 2) * δ ^ 2 := by
        rw [add_sub_cancel_left, Real.norm_eq_abs, mul_assoc, abs_mul_abs_self, sq]

end IsProfile

open ScOneExample

/-! ### Operators on `c₀` -/

/-- `ℓ^∞`, the coefficient sequences. -/
abbrev Linf : Type := BoundedContinuousFunction ℕ ℝ

/-- A bounded sequence as an element of `ℓ^∞` (`0` if the sequence is unbounded). -/
def bcf (f : ℕ → ℝ) : Linf :=
  open Classical in
  if h : ∃ C, ∀ i, ‖f i‖ ≤ C then
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete f h.choose h.choose_spec
  else 0

lemma bcf_apply {f : ℕ → ℝ} {C : ℝ} (h : ∀ i, |f i| ≤ C) (i : ℕ) : bcf f i = f i := by
  have h' : ∃ C, ∀ i, ‖f i‖ ≤ C := ⟨C, h⟩
  unfold bcf
  rw [dif_pos h']; rfl

lemma norm_bcf_le {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, |f i| ≤ C) : ‖bcf f‖ ≤ C :=
  (BoundedContinuousFunction.norm_le hC).2 fun i => by
    rw [bcf_apply h, Real.norm_eq_abs]; exact h i

lemma abs_apply_le (a : Linf) (i : ℕ) : |a i| ≤ ‖a‖ := by
  rw [← Real.norm_eq_abs]; exact a.norm_coe_le_norm i

/-- The diagonal operator `y ↦ (a_i y_i)`, linear and continuous in `a ∈ ℓ^∞`. -/
def dg : CLM Linf (CLM c0 c0) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun (a : Linf) (y : c0) => mkC0 (fun k => a k * y k) (by
        refine squeeze_zero_norm (a := fun k => ‖a‖ * |y k|) (fun k => ?_) ?_
        · rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_apply_le a k) (abs_nonneg _)
        · simpa using ((tendsto_c0 y).abs.const_mul ‖a‖)))
      (fun a a' y => by ext k; simp [add_mul])
      (fun r a y => by ext k; simp [mul_assoc])
      (fun a y y' => by ext k; simp [mul_add])
      (fun r a y => by ext k; simp; ring))
    1 (fun a y => by
      rw [one_mul]
      refine norm_le_of_forall (by positivity) fun k => ?_
      change |a k * y k| ≤ ‖a‖ * ‖y‖
      rw [abs_mul]
      exact mul_le_mul (abs_apply_le a k) (abs_apply_le_norm y k) (abs_nonneg _) (norm_nonneg _))

@[simp] lemma dg_apply (a : Linf) (y : c0) (k : ℕ) : dg a y k = a k * y k := rfl

lemma dg_eq_diag (a : Linf) : dg a = diag (fun k => a k) (abs_apply_le a) := by
  ext y k; rfl

/-- The left shift `(y_i) ↦ (y_{i+1})`. -/
def lsh : CLM c0 c0 :=
  LinearMap.mkContinuous
    { toFun := fun y => mkC0 (fun i => y (i + 1)) ((tendsto_add_atTop_iff_nat 1).2 (tendsto_c0 y))
      map_add' := fun y z => by ext k; simp
      map_smul' := fun r y => by ext k; simp }
    1 (fun y => by
      rw [one_mul]
      exact norm_le_of_forall (norm_nonneg _) fun k => abs_apply_le_norm y (k + 1))

@[simp] lemma lsh_apply (y : c0) (i : ℕ) : lsh y i = y (i + 1) := rfl

/-- The right shift `(y_i) ↦ (0, y_0, y_1, …)`. -/
def rsh : CLM c0 c0 :=
  LinearMap.mkContinuous
    { toFun := fun y => mkC0 (fun i => Nat.casesOn i 0 fun i => y i)
        ((tendsto_add_atTop_iff_nat 1).1 (tendsto_c0 y))
      map_add' := fun y z => by ext k; cases k <;> simp
      map_smul' := fun r y => by ext k; cases k <;> simp }
    1 (fun y => by
      rw [one_mul]
      refine norm_le_of_forall (norm_nonneg _) fun k => ?_
      cases k with
      | zero => simp
      | succ k => exact abs_apply_le_norm y k)

@[simp] lemma rsh_apply_zero (y : c0) : rsh y 0 = 0 := rfl

@[simp] lemma rsh_apply_succ (y : c0) (i : ℕ) : rsh y (i + 1) = y i := rfl

/-- The positions `K_i = 16ⁱ − 1`, where the weight `w = 1/(k+1)` is exactly `16⁻ⁱ`. -/
def pos (i : ℕ) : ℕ := 16 ^ i - 1

lemma pos_add_one (i : ℕ) : pos i + 1 = 16 ^ i :=
  Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))

/-- The index of a position: `idx (K_i) = i`. -/
def idx (k : ℕ) : ℕ := Nat.log 16 (k + 1)

lemma idx_pos (i : ℕ) : idx (pos i) = i := by
  unfold idx; rw [pos_add_one]; exact Nat.log_pow (by norm_num) i

lemma pos_injective : Injective pos := fun i j h => by
  have := congrArg idx h
  rwa [idx_pos, idx_pos] at this

lemma eq_pos_of {k : ℕ} (h : 16 ^ idx k = k + 1) : k = pos (idx k) := by
  unfold pos; omega

lemma tendsto_pos : Tendsto pos atTop atTop := by
  refine tendsto_atTop_mono (fun i => ?_) tendsto_id
  have : i < 16 ^ i := Nat.lt_pow_self (by norm_num)
  change i ≤ 16 ^ i - 1
  omega

lemma tendsto_idx : Tendsto idx atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨16 ^ b, fun k hk =>
    Nat.le_log_of_pow_le (by norm_num) (hk.trans (Nat.le_succ k))⟩

/-- Sampling at the positions: `(y_k) ↦ (y_{K_i})_i`. -/
def smp : CLM c0 c0 :=
  LinearMap.mkContinuous
    { toFun := fun y => mkC0 (fun i => y (pos i)) ((tendsto_c0 y).comp tendsto_pos)
      map_add' := fun y z => by ext k; simp
      map_smul' := fun r y => by ext k; simp }
    1 (fun y => by
      rw [one_mul]
      exact norm_le_of_forall (norm_nonneg _) fun k => abs_apply_le_norm y (pos k))

@[simp] lemma smp_apply (y : c0) (i : ℕ) : smp y i = y (pos i) := rfl

/-- Embedding at the positions: `(z_i) ↦` the sequence with `z_i` at `K_i` and `0` elsewhere. -/
def emb : CLM c0 c0 :=
  LinearMap.mkContinuous
    { toFun := fun z => mkC0 (fun k => if 16 ^ idx k = k + 1 then z (idx k) else 0) (by
        refine squeeze_zero_norm (a := fun k => |z (idx k)|) (fun k => ?_) ?_
        · split_ifs
          · exact le_of_eq (Real.norm_eq_abs _)
          · simp
        · simpa using ((tendsto_c0 z).comp tendsto_idx).abs)
      map_add' := fun y z => by
        ext k
        simp only [mkC0_apply, ZeroAtInftyContinuousMap.coe_add, Pi.add_apply]
        split_ifs <;> simp
      map_smul' := fun r y => by
        ext k
        simp only [mkC0_apply, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply,
          RingHom.id_apply]
        split_ifs <;> simp }
    1 (fun z => by
      rw [one_mul]
      refine norm_le_of_forall (norm_nonneg _) fun k => ?_
      change |if 16 ^ idx k = k + 1 then z (idx k) else 0| ≤ ‖z‖
      split_ifs
      · exact abs_apply_le_norm z _
      · simp)

lemma emb_apply_pos (z : c0) (i : ℕ) : emb z (pos i) = z i := by
  change (if 16 ^ idx (pos i) = pos i + 1 then z (idx (pos i)) else 0) = z i
  rw [idx_pos, if_pos (pos_add_one i).symm]

lemma emb_apply_of_not (z : c0) {k : ℕ} (h : 16 ^ idx k ≠ k + 1) : emb z k = 0 := if_neg h

/-- Two elements of `c₀` agree if they agree at the positions and off the positions. -/
lemma c0_ext_pos {x y : c0} (h1 : ∀ i, x (pos i) = y (pos i))
    (h2 : ∀ k, 16 ^ idx k ≠ k + 1 → x k = y k) : x = y := by
  ext k
  by_cases h : 16 ^ idx k = k + 1
  · rw [eq_pos_of h]; exact h1 _
  · exact h2 k h

/-- The weights at the positions, `ϖ_i = 16⁻ⁱ`, as an element of `ℓ^∞`. -/
def wgt : Linf := bcf fun i => (1 / 16 : ℝ) ^ i

lemma wgt_apply (i : ℕ) : wgt i = (1 / 16 : ℝ) ^ i :=
  bcf_apply (C := 1) (fun i => by
    rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (by norm_num) (by norm_num)) i

lemma w_pos_eq (i : ℕ) : w (pos i) = (1 / 16 : ℝ) ^ i := by
  unfold w
  have : ((pos i : ℕ) : ℝ) + 1 = (16 : ℝ) ^ i := by
    have := congrArg (Nat.cast (R := ℝ)) (pos_add_one i)
    push_cast at this; exact this
  rw [this, one_div_pow]

lemma inclOp_apply (y : c0) (k : ℕ) : inclOp y k = w k * y k := rfl

lemma smp_inclOp (y : c0) : smp (inclOp y) = dg wgt (smp y) := by
  ext i
  rw [smp_apply, inclOp_apply, dg_apply, smp_apply, wgt_apply, w_pos_eq]

lemma inclOp_emb (z : c0) : inclOp (emb z) = emb (dg wgt z) := by
  refine c0_ext_pos (fun i => ?_) fun k hk => ?_
  · rw [inclOp_apply, emb_apply_pos, emb_apply_pos, dg_apply, wgt_apply, w_pos_eq]
  · rw [inclOp_apply, emb_apply_of_not _ hk, emb_apply_of_not _ hk, mul_zero]

lemma lsh_dg_wgt (z : c0) : lsh (dg wgt z) = (1 / 16 : ℝ) • dg wgt (lsh z) := by
  ext i
  simp only [lsh_apply, dg_apply, wgt_apply, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  ring

lemma dg_wgt_rsh (z : c0) : dg wgt (rsh z) = (1 / 16 : ℝ) • rsh (dg wgt z) := by
  ext i
  cases i with
  | zero => simp
  | succ i =>
    simp only [rsh_apply_succ, dg_apply, wgt_apply, ZeroAtInftyContinuousMap.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    ring

lemma dg_dg (a b : Linf) (z : c0) : dg a (dg b z) = dg (a * b) z := by
  ext k
  simp only [dg_apply, BoundedContinuousFunction.coe_mul, Pi.mul_apply]
  ring

/-- `a ↦ P ∘ dg a ∘ Q`, linear and continuous in `a ∈ ℓ^∞`. -/
def sand (P Q : CLM c0 c0) : CLM Linf (CLM c0 c0) :=
  ((ContinuousLinearMap.compL ℝ c0 c0 c0 P).comp
    ((ContinuousLinearMap.compL ℝ c0 c0 c0).flip Q)).comp dg

lemma sand_apply (P Q : CLM c0 c0) (a : Linf) (y : c0) : sand P Q a y = P (dg a (Q y)) := rfl

/-- The diagonal part: coordinate `K_i` from coordinate `K_i`. -/
def opD : CLM Linf (CLM c0 c0) := sand emb smp

/-- The upper part: coordinate `K_i` from coordinate `K_{i+1}`. -/
def opU : CLM Linf (CLM c0 c0) := sand emb (lsh.comp smp)

/-- The lower part: coordinate `K_{i+1}` from coordinate `K_i`. -/
def opN : CLM Linf (CLM c0 c0) := sand (emb.comp rsh) smp

lemma opD_apply (a : Linf) (y : c0) : opD a y = emb (dg a (smp y)) := rfl

lemma opU_apply (a : Linf) (y : c0) : opU a y = emb (dg a (lsh (smp y))) := rfl

lemma opN_apply (a : Linf) (y : c0) : opN a y = emb (rsh (dg a (smp y))) := rfl

lemma opD_inclOp (a : Linf) (y : c0) : opD a (inclOp y) = opD (a * wgt) y := by
  rw [opD_apply, opD_apply, smp_inclOp, dg_dg]

lemma opU_inclOp (a : Linf) (y : c0) : opU a (inclOp y) = (1 / 16 : ℝ) • opU (a * wgt) y := by
  rw [opU_apply, opU_apply, smp_inclOp, lsh_dg_wgt, map_smul, map_smul, dg_dg]

lemma opN_inclOp (a : Linf) (y : c0) : opN a (inclOp y) = opN (a * wgt) y := by
  rw [opN_apply, opN_apply, smp_inclOp, dg_dg]

lemma inclOp_opD (a : Linf) (y : c0) : inclOp (opD a y) = opD (a * wgt) y := by
  rw [opD_apply, opD_apply, inclOp_emb, dg_dg, mul_comm]

lemma inclOp_opU (a : Linf) (y : c0) : inclOp (opU a y) = opU (a * wgt) y := by
  rw [opU_apply, opU_apply, inclOp_emb, dg_dg, mul_comm]

lemma inclOp_opN (a : Linf) (y : c0) : inclOp (opN a y) = (1 / 16 : ℝ) • opN (a * wgt) y := by
  rw [opN_apply, opN_apply, inclOp_emb, dg_wgt_rsh, map_smul, dg_dg, mul_comm]

/-! ### Dyadic coefficient curves in `ℓ^∞` -/

/-- The coefficients `2^{ij} 16^{-ig} φ^{(j)}(2ⁱ t)`. -/
def seq (φ : ℝ → ℝ) (j g : ℕ) (t : ℝ) (i : ℕ) : ℝ :=
  (2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) * deriv^[j] φ (2 ^ i * t)

lemma coef_nonneg (i j g : ℕ) : 0 ≤ (2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) := by positivity

lemma coef_le {j g : ℕ} (h : j ≤ 4 * g) (i : ℕ) :
    (2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) ≤ 1 := by
  have h1 : (2 : ℝ) ^ (i * j) ≤ 16 ^ (i * g) := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ one_le_two (by nlinarith [Nat.mul_le_mul_left i h])
  rw [one_div_pow, mul_one_div]
  exact (div_le_one (by positivity)).2 h1

lemma seq_succ_j (φ : ℝ → ℝ) (j g : ℕ) (t : ℝ) (i : ℕ) :
    seq φ (j + 1) g t i =
      (2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) * (2 ^ i * deriv^[j + 1] φ (2 ^ i * t)) := by
  unfold seq
  rw [Nat.mul_succ, pow_add]; ring

lemma seq_succ_g (φ : ℝ → ℝ) (j g : ℕ) (t : ℝ) (i : ℕ) :
    seq φ j (g + 1) t i = seq φ j g t i * (1 / 16 : ℝ) ^ i := by
  unfold seq
  rw [Nat.mul_succ, pow_add]; ring

/-- The coefficient curve in `ℓ^∞`. -/
def bs (φ : ℝ → ℝ) (j g : ℕ) (t : ℝ) : Linf := bcf (seq φ j g t)

namespace IsProfile

variable {φ : ℝ → ℝ} (hφ : IsProfile φ)
include hφ

lemma abs_seq_le {j g : ℕ} (h : j ≤ 4 * g) (t : ℝ) (i : ℕ) : |seq φ j g t i| ≤ hφ.bd j := by
  unfold seq
  rw [abs_mul, abs_of_nonneg (coef_nonneg i j g)]
  calc (2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) * |deriv^[j] φ (2 ^ i * t)|
      ≤ 1 * hφ.bd j := mul_le_mul (coef_le h i) (hφ.abs_le_bd j _) (abs_nonneg _) zero_le_one
    _ = hφ.bd j := one_mul _

lemma bs_apply {j g : ℕ} (h : j ≤ 4 * g) (t : ℝ) (i : ℕ) : bs φ j g t i = seq φ j g t i :=
  bcf_apply (hφ.abs_seq_le h t) i

lemma bs_succ_g {j g : ℕ} (h : j ≤ 4 * g) (t : ℝ) : bs φ j (g + 1) t = bs φ j g t * wgt := by
  ext i
  rw [BoundedContinuousFunction.coe_mul, Pi.mul_apply, hφ.bs_apply (by omega), hφ.bs_apply h,
    wgt_apply, seq_succ_g]

lemma norm_bs_sub_le {j g : ℕ} (h : j + 1 ≤ 4 * g) (t t' : ℝ) :
    ‖bs φ j g t' - bs φ j g t‖ ≤ hφ.bd (j + 1) * |t' - t| := by
  refine (BoundedContinuousFunction.norm_le (mul_nonneg (hφ.bd_nonneg _) (abs_nonneg _))).2
    fun i => ?_
  rw [BoundedContinuousFunction.coe_sub, Pi.sub_apply, hφ.bs_apply (by omega),
    hφ.bs_apply (by omega), Real.norm_eq_abs]
  unfold seq
  rw [← mul_sub, abs_mul, abs_of_nonneg (coef_nonneg i j g)]
  have h1 := hφ.abs_sub_le j (2 ^ i * t) (2 ^ i * t')
  have h2 : |(2 : ℝ) ^ i * t' - 2 ^ i * t| = 2 ^ i * |t' - t| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  rw [h2] at h1
  have h3 : (2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) * 2 ^ i ≤ 1 := by
    have := coef_le h i
    rwa [Nat.mul_succ, pow_add, mul_right_comm] at this
  calc (2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) *
        |deriv^[j] φ (2 ^ i * t') - deriv^[j] φ (2 ^ i * t)|
      ≤ (2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) * (hφ.bd (j + 1) * (2 ^ i * |t' - t|)) :=
        mul_le_mul_of_nonneg_left h1 (coef_nonneg i j g)
    _ = ((2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) * 2 ^ i) * (hφ.bd (j + 1) * |t' - t|) := by ring
    _ ≤ 1 * (hφ.bd (j + 1) * |t' - t|) :=
        mul_le_mul_of_nonneg_right h3 (mul_nonneg (hφ.bd_nonneg _) (abs_nonneg _))
    _ = hφ.bd (j + 1) * |t' - t| := one_mul _

lemma continuous_bs {j g : ℕ} (h : j + 1 ≤ 4 * g) : Continuous (bs φ j g) :=
  (LipschitzWith.of_dist_le' (K := hφ.bd (j + 1)) fun t' t => by
    rw [dist_eq_norm, Real.dist_eq]; exact hφ.norm_bs_sub_le h t t').continuous

lemma norm_bs_taylor_le {j g : ℕ} (h : j + 2 ≤ 4 * g) (t t' : ℝ) :
    ‖bs φ j g t' - bs φ j g t - (t' - t) • bs φ (j + 1) g t‖ ≤ hφ.bd (j + 2) * (t' - t) ^ 2 := by
  refine (BoundedContinuousFunction.norm_le (mul_nonneg (hφ.bd_nonneg _) (sq_nonneg _))).2
    fun i => ?_
  rw [BoundedContinuousFunction.coe_sub, Pi.sub_apply, BoundedContinuousFunction.coe_sub,
    Pi.sub_apply, BoundedContinuousFunction.coe_smul, hφ.bs_apply (by omega),
    hφ.bs_apply (by omega)]
  change ‖seq φ j g t' i - seq φ j g t i - (t' - t) • bs φ (j + 1) g t i‖ ≤ _
  rw [hφ.bs_apply (by omega), Real.norm_eq_abs, seq_succ_j]
  unfold seq
  have h1 := hφ.abs_taylor_le j (2 ^ i * t) (2 ^ i * (t' - t))
  rw [show (2 : ℝ) ^ i * t + 2 ^ i * (t' - t) = 2 ^ i * t' by ring] at h1
  have h3 : (2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) * (2 ^ i) ^ 2 ≤ 1 := by
    have := coef_le h i
    rw [Nat.mul_succ, Nat.mul_succ, pow_add, pow_add] at this
    calc (2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) * (2 ^ i) ^ 2
        = 2 ^ (i * j) * 2 ^ i * 2 ^ i * (1 / 16) ^ (i * g) := by ring
      _ ≤ 1 := this
  have e : (2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) * deriv^[j] φ (2 ^ i * t') -
      (2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) * deriv^[j] φ (2 ^ i * t) -
      (t' - t) • ((2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) *
        (2 ^ i * deriv^[j + 1] φ (2 ^ i * t))) =
      (2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) * (deriv^[j] φ (2 ^ i * t') -
        deriv^[j] φ (2 ^ i * t) - 2 ^ i * (t' - t) * deriv^[j + 1] φ (2 ^ i * t)) := by
    rw [smul_eq_mul]; ring
  rw [e, abs_mul, abs_of_nonneg (coef_nonneg i j g)]
  calc (2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) * |deriv^[j] φ (2 ^ i * t') -
        deriv^[j] φ (2 ^ i * t) - 2 ^ i * (t' - t) * deriv^[j + 1] φ (2 ^ i * t)|
      ≤ (2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) * (hφ.bd (j + 2) * (2 ^ i * (t' - t)) ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (coef_nonneg i j g)
    _ = ((2 : ℝ) ^ (i * j) * (1 / 16 : ℝ) ^ (i * g) * (2 ^ i) ^ 2) *
          (hφ.bd (j + 2) * (t' - t) ^ 2) := by ring
    _ ≤ 1 * (hφ.bd (j + 2) * (t' - t) ^ 2) :=
        mul_le_mul_of_nonneg_right h3 (mul_nonneg (hφ.bd_nonneg _) (sq_nonneg _))
    _ = hφ.bd (j + 2) * (t' - t) ^ 2 := one_mul _

/-- One level pays for one derivative: `t ↦ (2^{ij} 16^{-ig} φ^{(j)}(2ⁱ t))_i ∈ ℓ^∞` is
differentiable when `j + 2 ≤ 4g`. -/
lemma hasDerivAt_bs {j g : ℕ} (h : j + 2 ≤ 4 * g) (t : ℝ) :
    HasDerivAt (bs φ j g) (bs φ (j + 1) g t) t := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hM : 0 < hφ.bd (j + 2) + 1 := by linarith [hφ.bd_nonneg (j + 2)]
  filter_upwards [Metric.ball_mem_nhds t (div_pos hc hM)] with t' ht'
  rw [Metric.mem_ball, Real.dist_eq] at ht'
  refine (hφ.norm_bs_taylor_le h t t').trans ?_
  rw [Real.norm_eq_abs, ← sq_abs, sq, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  calc hφ.bd (j + 2) * |t' - t| ≤ (hφ.bd (j + 2) + 1) * (c / (hφ.bd (j + 2) + 1)) :=
        mul_le_mul (by linarith) ht'.le (abs_nonneg _) hM.le
    _ = c := by field_simp

/-- Strong continuity on one level: `(t, z) ↦ (φ(2ⁱ t) z_i)_i` is continuous on `ℝ × c₀`. -/
lemma continuous_dg_bs : Continuous fun p : ℝ × c0 => dg (bs φ 0 0 p.1) p.2 := by
  have hc : ∀ (s : ℝ) (k : ℕ), |seq φ 0 0 s k| ≤ hφ.bd 0 := fun s k =>
    hφ.abs_seq_le (j := 0) (g := 0) le_rfl s k
  have := continuous_diag_family (fun s => seq φ 0 0 s) hc fun k => by
    unfold seq
    exact continuous_const.mul (hφ.contDiff.continuous.comp (continuous_const.mul continuous_id))
  refine this.congr fun p => ?_
  ext k
  rw [ScOneExample.diag_apply, dg_apply, hφ.bs_apply (j := 0) (g := 0) le_rfl]

end IsProfile

/-! ### The operators `T j g b t` -/

/-- The `j`-th `t`-derivative of the moving projection, from level `b + g` to level `b`, in the
level coordinates: at the position `K_i` it is
`2^{ij} 16^{-ig} (Φ₀^{(j)}(2ⁱt) y_{K_i} + 16^{-(b+g)} Φ₁^{(j)}(2ⁱt) y_{K_{i+1}})
  + 16^b 2^{(i-1)j} 16^{-(i-1)g} Φ₁^{(j)}(2^{i-1}t) y_{K_{i-1}}`. -/
def T (j g b : ℕ) (t : ℝ) : CLM c0 c0 :=
  three (P := Linf) (V := CLM c0 c0) opD opU opN ((1 / 16 : ℝ) ^ (b + g)) ((16 : ℝ) ^ b)
    (bs phi0 j g t) (bs phi1 j g t)

lemma T_apply (j g b : ℕ) (t : ℝ) (y : c0) :
    T j g b t y = opD (bs phi0 j g t) y + ((1 / 16 : ℝ) ^ (b + g)) • opU (bs phi1 j g t) y +
      ((16 : ℝ) ^ b) • opN (bs phi1 j g t) y := rfl

/-- Lowering the source level: `T j g b t ∘ ι = T j (g+1) b t`. -/
lemma T_inclOp {j g : ℕ} (h : j ≤ 4 * g) (b : ℕ) (t : ℝ) (y : c0) :
    T j g b t (inclOp y) = T j (g + 1) b t y := by
  rw [T_apply, T_apply, opD_inclOp, opU_inclOp, opN_inclOp, isProfile_phi0.bs_succ_g h,
    isProfile_phi1.bs_succ_g h, smul_smul, ← add_assoc b g 1, pow_succ]

/-- Lowering the target level: `ι ∘ T j g (b+1) t = T j (g+1) b t`. -/
lemma inclOp_T {j g : ℕ} (h : j ≤ 4 * g) (b : ℕ) (t : ℝ) (y : c0) :
    inclOp (T j g (b + 1) t y) = T j (g + 1) b t y := by
  rw [T_apply, T_apply, map_add, map_add, map_smul, map_smul, inclOp_opD, inclOp_opU, inclOp_opN,
    isProfile_phi0.bs_succ_g h, isProfile_phi1.bs_succ_g h, smul_smul]
  congr 2
  · ring_nf
  · rw [pow_succ]; ring

lemma hasDerivAt_T {j g : ℕ} (h : j + 2 ≤ 4 * g) (b : ℕ) (t : ℝ) :
    HasDerivAt (T j g b) (T (j + 1) g b t) t :=
  hasDerivAt_three (P := Linf) (V := CLM c0 c0) opD opU opN _ _
    (isProfile_phi0.hasDerivAt_bs h t) (isProfile_phi1.hasDerivAt_bs h t)

lemma continuous_T {j g : ℕ} (h : j + 1 ≤ 4 * g) (b : ℕ) : Continuous (T j g b) :=
  continuous_three (P := Linf) (V := CLM c0 c0) opD opU opN _ _
    (isProfile_phi0.continuous_bs h) (isProfile_phi1.continuous_bs h)

lemma contDiff_T (n j g b : ℕ) (h : j + n + 1 ≤ 4 * g) : ContDiff ℝ n (T j g b) :=
  contDiff_of_chain (V := CLM c0 c0) (fun i => T i g b) n j
    (fun i _ hi t => hasDerivAt_T (by omega) b t) (continuous_T (by omega) b)

/-- Strong continuity on one level. -/
lemma continuous_T_zero (b : ℕ) : Continuous fun p : ℝ × c0 => T 0 0 b p.1 p.2 := by
  have h0 : Continuous fun p : ℝ × c0 => opD (bs phi0 0 0 p.1) p.2 :=
    emb.continuous.comp (isProfile_phi0.continuous_dg_bs.comp
      (continuous_fst.prodMk (smp.continuous.comp continuous_snd)))
  have h1 : Continuous fun p : ℝ × c0 => opU (bs phi1 0 0 p.1) p.2 :=
    emb.continuous.comp (isProfile_phi1.continuous_dg_bs.comp
      (continuous_fst.prodMk ((lsh.comp smp).continuous.comp continuous_snd)))
  have h2 : Continuous fun p : ℝ × c0 => opN (bs phi1 0 0 p.1) p.2 :=
    (emb.comp rsh).continuous.comp (isProfile_phi1.continuous_dg_bs.comp
      (continuous_fst.prodMk (smp.continuous.comp continuous_snd)))
  exact (h0.add (h1.const_smul _)).add (h2.const_smul _)

/-! ### The jump family on the weighted sequence space -/

lemma X_toBase_T_one : ∀ (m : ℕ) (t : ℝ) (y : X (m + 1)),
    X.toBase m (T 1 1 m t y) = T 1 1 0 t (X.shift.toBase m y)
  | 0, _, _ => rfl
  | m + 1, t, y => by
    rw [X.toBase_succ]
    change X.toBase m (inclOp (T 1 1 (m + 1) t y)) = _
    rw [inclOp_T (by norm_num), ← T_inclOp (by norm_num), X_toBase_T_one m]; rfl

lemma T_one_inclK (m : ℕ) (t : ℝ) : ∀ (l : ℕ) (y : X.shift (m + l)),
    T 1 1 m t (X.shift.inclK m l y) = T 1 (1 + l) m t y
  | 0, _ => rfl
  | l + 1, y => by
    rw [ScScale.inclK_succ, T_one_inclK m t l]
    change T 1 (1 + l) m t (inclOp y) = _
    rw [T_inclOp (by omega)]; rfl

/-- `(s, t, h) ↦ s π'(t)h : ℝ² ⊕ X¹ → X` is sc-smooth (Proposition 1.2.4: from level `m + l + 1`
to level `m` it is of class `C^{l+1}`). -/
theorem isScSmooth_deriv :
    IsScSmooth (E := (ScBanach.const (ℝ × ℝ)).prod X.shift) (F := X) univ
      (fun p => p.1.1 • T 1 1 0 p.1.2 p.2) := by
  have hlvl : ∀ (m : ℕ) (x : ((ScBanach.const (ℝ × ℝ)).prod X.shift) m),
      levelMap (E := (ScBanach.const (ℝ × ℝ)).prod X.shift) (F := X)
        (fun p => p.1.1 • T 1 1 0 p.1.2 p.2) m x = x.1.1 • T 1 1 m x.1.2 x.2 := fun m x => by
    refine levelMap_eq_of_toBase_eq ?_
    rw [map_smul, X_toBase_T_one, ScBanach.prod_toBase, ScBanach.const_toBase]
  have hsc0 : IsSc0 ((ScBanach.const (ℝ × ℝ)).prod X.shift) X univ
      (fun p => p.1.1 • T 1 1 0 p.1.2 p.2) :=
    { mem_range := fun m x _ => ⟨x.1.1 • T 1 1 m x.1.2 x.2, by
        rw [map_smul, X_toBase_T_one, ScBanach.prod_toBase, ScBanach.const_toBase]⟩
      continuousOn := fun m => by
        rw [funext (hlvl m)]
        exact (continuous_smul_apply (V := c0) (W := c0)
          (continuous_T (by norm_num) m)).continuousOn }
  refine IsScSmooth.of_contDiffOn_levels_text (isScDomain_univ _) hsc0 fun m l => ?_
  have hcomp : levelMap (E := (ScBanach.const (ℝ × ℝ)).prod X.shift) (F := X)
        (fun p => p.1.1 • T 1 1 0 p.1.2 p.2) m ∘
        ((ScBanach.const (ℝ × ℝ)).prod X.shift).inclK m l =
      fun x : (ℝ × ℝ) × c0 => x.1.1 • T 1 (1 + l) m x.1.2 x.2 := by
    funext x
    have hincl : ∀ (l : ℕ) (x : ((ScBanach.const (ℝ × ℝ)).prod X.shift) (m + l)),
        ((ScBanach.const (ℝ × ℝ)).prod X.shift).inclK m l x = (x.1, X.shift.inclK m l x.2) := by
      intro l
      induction l with
      | zero => intro x; rfl
      | succ l ih => intro x; rw [ScScale.inclK_succ, ih]; rfl
    rw [Function.comp_apply, hlvl, hincl, T_one_inclK]
  rw [hcomp]
  refine ContDiff.contDiffOn ?_
  have hT : ContDiff ℝ ((l + 1 : ℕ) : WithTop ℕ∞) (T 1 (1 + l) m) :=
    contDiff_T (l + 1) 1 (1 + l) m (by omega)
  exact contDiff_smul_apply (V := c0) (W := c0) (by exact_mod_cast hT)

/-- **The jump family on `X`**: `A_m(t) = T 0 0 m t` (the moving projection on level `m`) and
`A'_m(t) = T 1 1 m t`. -/
def family : Family X where
  A m t := T 0 0 m t
  A' m t := T 1 1 m t
  incl_A m t x := by
    change inclOp (T 0 0 (m + 1) t x) = T 0 0 m t (inclOp x)
    rw [inclOp_T (j := 0) (g := 0) le_rfl, T_inclOp (j := 0) (g := 0) le_rfl]
  incl_A' m t x := by
    change inclOp (T 1 1 (m + 1) t x) = T 1 1 m t (inclOp x)
    rw [inclOp_T (by norm_num), T_inclOp (by norm_num)]
  cont_A m := continuous_T_zero m
  cont_A' m := continuous_T (by norm_num) m
  deriv_A m t := by
    have h : (fun s => (T 0 0 m s).comp (X.incl m)) = T 0 1 m :=
      funext fun s => ContinuousLinearMap.ext fun y => T_inclOp (j := 0) (g := 0) le_rfl m s y
    rw [h]; exact hasDerivAt_T (by norm_num) m t
  smooth_A' := isScSmooth_deriv

/-! ### The derivative family vanishes for `t ≤ 0` -/

lemma phi0_of_le_half {s : ℝ} (hs : s ≤ 1 / 2) : phi0 s = 0 := by
  unfold phi0; rw [prof_of_le_half hs, mul_zero]

lemma phi1_of_le_half {s : ℝ} (hs : s ≤ 1 / 2) : phi1 s = 0 := by
  unfold phi1; rw [prof_of_le_half hs, zero_mul]

lemma deriv_eq_zero_of_nonpos {φ : ℝ → ℝ} (h : ∀ s, s ≤ 1 / 2 → φ s = 0) {s : ℝ} (hs : s ≤ 0) :
    deriv φ s = 0 := by
  have he : φ =ᶠ[𝓝 s] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds (show s < 1 / 2 by linarith)] with x hx
    exact h x hx.le
  rw [he.deriv_eq]; simp

lemma IsProfile.bs_one_of_nonpos {φ : ℝ → ℝ} (hφ : IsProfile φ) (h : ∀ s, s ≤ 1 / 2 → φ s = 0)
    {t : ℝ} (ht : t ≤ 0) : bs φ 1 1 t = 0 := by
  ext i
  rw [hφ.bs_apply (j := 1) (g := 1) (by norm_num)]
  unfold seq
  rw [Function.iterate_one,
    deriv_eq_zero_of_nonpos h (mul_nonpos_of_nonneg_of_nonpos (by positivity) ht), mul_zero]
  rfl

/-- `π'(t) = 0` for `t ≤ 0`. -/
theorem T_one_one_of_nonpos {t : ℝ} (ht : t ≤ 0) (b : ℕ) : T 1 1 b t = 0 := by
  unfold T three
  rw [isProfile_phi0.bs_one_of_nonpos (fun s => phi0_of_le_half) ht,
    isProfile_phi1.bs_one_of_nonpos (fun s => phi1_of_le_half) ht]
  simp

lemma family_A'_zero (t : ℝ) : family.A' 0 t = T 1 1 0 t := rfl

/-! ### The moving projection on level `0`: a rank-one projection for `0 < t < 1` -/

/-- The moving projection `π_t` on level `0`. -/
def proj (t : ℝ) : CLM c0 c0 := T 0 0 0 t

lemma family_A_zero (t : ℝ) : family.A 0 t = proj t := rfl

lemma family_map_apply (p : ((ScBanach.const ℝ).prod X) 0) : family.map p = proj p.1 p.2 := rfl

lemma bs_zero_apply {φ : ℝ → ℝ} (hφ : IsProfile φ) (t : ℝ) (i : ℕ) :
    bs φ 0 0 t i = φ (2 ^ i * t) := by
  rw [hφ.bs_apply (j := 0) (g := 0) le_rfl]; unfold seq; simp

lemma proj_apply (t : ℝ) (y : c0) :
    proj t y = opD (bs phi0 0 0 t) y + opU (bs phi1 0 0 t) y + opN (bs phi1 0 0 t) y := by
  change T 0 0 0 t y = _
  rw [T_apply]; simp

lemma proj_apply_of_not (t : ℝ) (y : c0) {k : ℕ} (h : 16 ^ idx k ≠ k + 1) : proj t y k = 0 := by
  rw [proj_apply, opD_apply, opU_apply, opN_apply]
  change emb _ k + emb _ k + emb _ k = 0
  rw [emb_apply_of_not _ h, emb_apply_of_not _ h, emb_apply_of_not _ h]; simp

lemma phi1_two_pow (t : ℝ) (i : ℕ) :
    phi1 (2 ^ i * t) = prof (2 ^ i * t) * prof (2 ^ (i + 1) * t) := by
  unfold phi1; rw [pow_succ]; congr 2; ring

lemma proj_apply_pos_zero (t : ℝ) (y : c0) :
    proj t y (pos 0) = prof (2 ^ 0 * t) * (prof (2 ^ 0 * t) * y (pos 0) +
      prof (2 ^ 1 * t) * y (pos 1)) := by
  rw [proj_apply, opD_apply, opU_apply, opN_apply]
  change emb _ (pos 0) + emb _ (pos 0) + emb _ (pos 0) = _
  rw [emb_apply_pos, emb_apply_pos, emb_apply_pos, dg_apply, dg_apply, rsh_apply_zero, smp_apply,
    lsh_apply, smp_apply, bs_zero_apply isProfile_phi0, bs_zero_apply isProfile_phi1, phi1_two_pow]
  unfold phi0; ring

lemma proj_apply_pos_succ (t : ℝ) (y : c0) (i : ℕ) :
    proj t y (pos (i + 1)) = prof (2 ^ (i + 1) * t) * (prof (2 ^ (i + 1) * t) * y (pos (i + 1)) +
      prof (2 ^ (i + 2) * t) * y (pos (i + 2)) + prof (2 ^ i * t) * y (pos i)) := by
  rw [proj_apply, opD_apply, opU_apply, opN_apply]
  change emb _ (pos (i + 1)) + emb _ (pos (i + 1)) + emb _ (pos (i + 1)) = _
  rw [emb_apply_pos, emb_apply_pos, emb_apply_pos, dg_apply, dg_apply, rsh_apply_succ, dg_apply,
    smp_apply, lsh_apply, smp_apply, smp_apply, bs_zero_apply isProfile_phi0,
    bs_zero_apply isProfile_phi1, bs_zero_apply isProfile_phi1, phi1_two_pow, phi1_two_pow]
  unfold phi0; ring

/-- `π_t = 0` for `t ≤ 0`. -/
theorem proj_of_nonpos {t : ℝ} (ht : t ≤ 0) (y : c0) : proj t y = 0 := by
  refine c0_ext_pos (fun i => ?_) fun k hk => proj_apply_of_not t y hk
  cases i with
  | zero => rw [proj_apply_pos_zero, prof_two_pow_of_nonpos ht]; simp
  | succ i => rw [proj_apply_pos_succ, prof_two_pow_of_nonpos ht]; simp

lemma unitVec_apply (j k : ℕ) : unitVec j k = if k = j then 1 else 0 := rfl

lemma unitVec_pos_of_not (i : ℕ) {k : ℕ} (h : 16 ^ idx k ≠ k + 1) : unitVec (pos i) k = 0 := by
  rw [unitVec_apply, if_neg]
  rintro rfl
  exact h (by rw [idx_pos, pos_add_one])

lemma unitVec_pos_pos (i j : ℕ) : unitVec (pos i) (pos j) = if j = i then 1 else 0 := by
  rw [unitVec_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg fun h' => h (pos_injective h')]

/-- The direction `e = cos θ e_{K_{n+1}} + sin θ e_{K_n}`. -/
def dir (n : ℕ) (θ : ℝ) : c0 := Real.cos θ • unitVec (pos (n + 1)) + Real.sin θ • unitVec (pos n)

/-- The functional `ℓ(y) = cos θ y_{K_{n+1}} + sin θ y_{K_n}`. -/
def lin (n : ℕ) (θ : ℝ) (y : c0) : ℝ := Real.cos θ * y (pos (n + 1)) + Real.sin θ * y (pos n)

lemma dir_apply_pos (n : ℕ) (θ : ℝ) (i : ℕ) :
    dir n θ (pos i) = if i = n + 1 then Real.cos θ else if i = n then Real.sin θ else 0 := by
  unfold dir
  simp only [ZeroAtInftyContinuousMap.coe_add, ZeroAtInftyContinuousMap.coe_smul, Pi.add_apply,
    Pi.smul_apply, unitVec_pos_pos, smul_eq_mul]
  by_cases h1 : i = n + 1
  · subst h1; simp
  · by_cases h2 : i = n
    · subst h2; simp
    · simp [h1, h2]

lemma dir_apply_of_not (n : ℕ) (θ : ℝ) {k : ℕ} (h : 16 ^ idx k ≠ k + 1) : dir n θ k = 0 := by
  unfold dir
  simp [unitVec_pos_of_not _ h]

lemma lin_dir (n : ℕ) (θ : ℝ) : lin n θ (dir n θ) = 1 := by
  unfold lin
  rw [dir_apply_pos, dir_apply_pos, if_pos rfl, if_neg (by omega), if_pos rfl, ← sq, ← sq,
    Real.cos_sq_add_sin_sq]

lemma lin_smul (n : ℕ) (θ : ℝ) (c : ℝ) (y : c0) : lin n θ (c • y) = c * lin n θ y := by
  unfold lin
  simp only [ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]; ring

/-- If `Λ(2^{n+1} t) = cos θ`, `Λ(2ⁿ t) = sin θ` and the other `Λ(2ⁱ t)` vanish, then
`π_t = ℓ ⊗ e`. -/
theorem proj_eq_of_angle {t : ℝ} {n : ℕ} {θ : ℝ} (hc : prof (2 ^ (n + 1) * t) = Real.cos θ)
    (hs : prof (2 ^ n * t) = Real.sin θ)
    (h0 : ∀ i, i ≠ n → i ≠ n + 1 → prof (2 ^ i * t) = 0) (y : c0) :
    proj t y = lin n θ y • dir n θ := by
  refine c0_ext_pos (fun i => ?_) fun k hk => ?_
  · rw [ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, dir_apply_pos]
    unfold lin
    by_cases h1 : i = n + 1
    · subst h1
      rw [if_pos rfl, proj_apply_pos_succ, hc, hs, h0 (n + 2) (by omega) (by omega)]; ring
    · rw [if_neg h1]
      by_cases h2 : i = n
      · subst h2
        rw [if_pos rfl]
        cases i with
        | zero => rw [proj_apply_pos_zero, hc, hs]; ring
        | succ i =>
          rw [proj_apply_pos_succ, hc, hs, h0 i (by omega) (by omega)]; ring
      · rw [if_neg h2, mul_zero]
        cases i with
        | zero => rw [proj_apply_pos_zero, h0 0 h2 h1]; ring
        | succ i => rw [proj_apply_pos_succ, h0 (i + 1) h2 h1]; ring
  · rw [proj_apply_of_not t y hk, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply,
      dir_apply_of_not n θ hk, smul_zero]

/-- **For `0 < t < 1` the moving projection has rank one**: `π_t = ℓ ⊗ e` with `ℓ(e) = 1` and
`0 ≤ θ ≤ π/2`. -/
theorem exists_proj_eq {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ∃ (n : ℕ) (θ : ℝ), 0 ≤ θ ∧ θ ≤ Real.pi / 2 ∧ ∀ y, proj t y = lin n θ y • dir n θ := by
  obtain ⟨n, θ, hθ0, hθ1, hc, hs, hz⟩ := exists_angle h0 h1
  exact ⟨n, θ, hθ0, hθ1, proj_eq_of_angle hc hs hz⟩

/-- `π_t ∘ π_t = π_t` for `t < 1`. -/
theorem proj_proj {t : ℝ} (h1 : t < 1) (y : c0) : proj t (proj t y) = proj t y := by
  rcases le_or_gt t 0 with h0 | h0
  · rw [proj_of_nonpos h0, proj_of_nonpos h0]
  · obtain ⟨n, θ, -, -, h⟩ := exists_proj_eq h0 h1
    rw [h, h, lin_smul, lin_dir, mul_one]

lemma pos_of_angle {θ a b : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) (ha : 0 < a) (hb : 0 < b) :
    0 < Real.cos θ * a + Real.sin θ * b := by
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ1⟩
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
  rcases hc.eq_or_lt with h | h
  · have h2 := Real.cos_sq_add_sin_sq θ
    rw [← h] at h2
    have hs' : 0 < Real.sin θ := lt_of_le_of_ne hs fun h' => by rw [← h'] at h2; norm_num at h2
    rw [← h]; nlinarith
  · have := mul_pos h ha
    nlinarith [mul_nonneg hs hb.le]

lemma dir_ne_zero (n : ℕ) (θ : ℝ) : dir n θ ≠ 0 := fun h => by
  have := lin_dir n θ
  rw [h] at this
  unfold lin at this
  simp at this

/-- `π_t v ≠ 0` for `0 < t < 1` when `v` is positive at the positions. -/
theorem proj_ne_zero {t : ℝ} (h0 : 0 < t) (h1 : t < 1) {v : c0} (hv : ∀ i, 0 < v (pos i)) :
    proj t v ≠ 0 := by
  obtain ⟨n, θ, hθ0, hθ1, h⟩ := exists_proj_eq h0 h1
  rw [h]
  exact smul_ne_zero (pos_of_angle hθ0 hθ1 (hv _) (hv _)).ne' (dir_ne_zero n θ)

/-- A fixed vector of `π_t` (`t < 1`) annihilated by a functional which is positive on the unit
vectors at the positions is `0`. -/
theorem eq_zero_of_proj_eq {t : ℝ} (h1 : t < 1) {ν : c0 →L[ℝ] ℝ}
    (hν : ∀ i, 0 < ν (unitVec (pos i))) {y : c0} (hy : proj t y = y) (hνy : ν y = 0) : y = 0 := by
  rcases le_or_gt t 0 with h0 | h0
  · rw [← hy, proj_of_nonpos h0]
  · obtain ⟨n, θ, hθ0, hθ1, h⟩ := exists_proj_eq h0 h1
    rw [h] at hy
    have hνe : 0 < ν (dir n θ) := by
      unfold dir
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      exact pos_of_angle hθ0 hθ1 (hν _) (hν _)
    rw [← hy, map_smul, smul_eq_mul] at hνy
    have hl : lin n θ y = 0 := (mul_eq_zero.1 hνy).resolve_right hνe.ne'
    rw [← hy, hl, zero_smul]

end Jump
end Polyfold
