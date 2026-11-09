import Polyfold.Chapter4.ScPlus
import Polyfold.Chapter3.TangentGerm

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §4.1,
Proposition 4.1.9 (preprint 4.9) with Lemmas 4.1.12 and 4.1.13 (preprint 4.11 and 4.12) *(book 2017: Proposition 4.2, Lemmas 4.4, 4.5; see
`BookConcordance.md`)*.

# An sc⁺-retract near a point is the graph of a map on its tangent space

## The text, paraphrased

(Proposition 4.1.9 (preprint 4.9)) Let `(O, C, E)` be an sc⁺-retract, `t : U → U` an sc⁺-retraction of the
relatively open `U ⊆ C` onto `O`, `0 ∈ O`, and let the tangent space `T₀O` (finite-dimensional by
Lemma 4.1.7 (preprint 4.7)) be in good position to `C`, with a good complement `Y`, `E = T₀O ⊕ Y`; let
`p = Dt(0) : E → T₀O` be "the sc-projection".  Then there are open neighbourhoods `U₀` of `0` in
`O` and `V` of `0` in `T₀O ∩ C` such that `p : U₀ → V` is an sc-diffeomorphism; `(V, T₀O ∩ C, T₀O)`
is a local model by Proposition 3.1.25 (preprint 3.22).  *Proof in the text*: the section `f(u) = (1 − p)(u − t(u))`
of `U ◁ Y` is sc-Fredholm (Lemma 4.1.11 (preprint 4.10)), with `f(0) = 0`, `Df(0) = 1 − p`, kernel `T₀O` and image
`Y`; Theorem 3.5.11 (preprint 3.47) describes the solutions near `0` as the graph `{a + δ(a) | a ∈ V}` of an
sc-smooth `δ : V → Y`.  (Lemma 4.1.12 (preprint 4.11)) Every small solution `a + y` has `y = δ(a)`: on level `1`,
`y − δ(a) = (1 − p)[t(a + y) − t(a + δ(a))]` and `‖(1 − p)Dt(u)‖_{L(E₁)} ≤ 1/2` near `0` since
`(1 − p)Dt(0) = 0` ((76)–(77)).  (Lemma 4.1.13 (preprint 4.12)) `a + δ(a) ∈ O`: with `a₁ = p t(a + δ(a))`,
`t(a₁ + δ(a)) = t(a + δ(a))` and `Dt(0)(a₁ − a) = a₁ − a`, the level-`1` estimate
`‖Dt(v) − Dt(0)‖ ≤ 1/2` forces `a₁ = a`.  Then `p` is an sc-diffeomorphism from
`U₀ = {a + δ(a) | a ∈ V}` onto `V` with inverse `a ↦ a + δ(a)`.

## What is formalized

* `Polyfold.proposition_4_1_9` (**Proposition 4.1.9 (preprint 4.9)**): for the sc⁺-retraction `t` onto `O ∋ 0`,
  `N = T₀O`, a closed good complement `Y` and the projection `p : E → N` along `Y`, there are an
  open `W ∋ 0` in `E`, a relatively open `V ∋ 0` in the partial quadrant `N ∩ C` of `N`, and
  `Γ : V → E` sc-smooth on `V` (set sense, on the fixed `V`) with `p ∘ Γ = 1` on `V`,
  `Γ(a) − a ∈ Y`, `Γ(V) = O ∩ W`, `Γ ∘ p = 1` on `O ∩ W`, `Γ(0) = 0`, and `p`, `Γ` sc-smooth
  between the retracts `(O ∩ W, C, E)` and `(V, N ∩ C, N)` (Definition 2.1.14 (preprint 2.7)): the
  sc-diffeomorphism `p : O ∩ W → V` with inverse `Γ`.
* `Polyfold.GraphData` (the data), `GraphData.exists_contraction_radius` (**Lemma 4.1.12 (preprint 4.11)**, the
  level-`(k+1)` contraction estimate `‖(1 − p)(u' − u)‖ ≤ ‖1 − p‖θ‖u' − u‖` on `O_{k+1}` near `0`,
  and `GraphData.eq_of_p_eq`: two points of `O` near `0` with the same projection coincide),
  `GraphData.exists_graph_point` (**Lemma 4.1.13 (preprint 4.12)**: existence of `a + δ(a) ∈ O` by a level-`1`
  contraction), `GraphData.p_mem_C` (`p(O ∩ W) ⊆ C`), `GraphData.Nbhd` and
  `GraphData.exists_nbhd` (the neighbourhoods `W`, `V` and the map `Γ`).
* The regularity of `Γ` on the fixed `V`: `GraphData.Nbhd.continuousOn_Γ_lvl` (continuous into
  every level), `GraphData.Nbhd.hasFDerivWithinAt_Γ_lvl` (the frame formula
  `DΓ(a) = Dt(Γ(a))|_N ∘ (p ∘ Dt(Γ(a))|_N)⁻¹` on every level), `GraphData.Nbhd.contDiffOn_Γ_lvl`
  (the `C^k`-bootstrap), `GraphData.Nbhd.isScSmooth_Γ`; the abstract step
  `Polyfold.hasFDerivWithinAt_of_projection` / `norm_sub_le_of_projection` (a continuous right
  inverse of a projection with values in a "retract" is Lipschitz and differentiable); the
  level data of an sc⁺-retraction (`ScRetraction.lvlMap`, `lvlDeriv`,
  `ScRetraction.IsScPlus.exists_mvt`: the mean value estimate on `C_{k+1} ∩ B(u₀, r)`);
  Proposition 1.2.3 (preprint 1.18) for the tangent map of the lift (`GraphData.contDiffOn_lvlDeriv_apply`);
  `Polyfold.finiteDimensional_tangentSpace_zero` (Lemma 4.1.7 (preprint 4.7) (ii) in the form used here).

## What the text leaves implicit, and the choices made

* **`p = Dt(0)` is not the projection along `Y`.**  `Dt(0)` is a projection onto `T₀O` along
  `ker Dt(0)`, and nothing relates `ker Dt(0)` to the chosen good complement `Y`; the proof of
  Lemma 4.1.13 (preprint 4.12) writes `t(a + δ(a)) = p t(a + δ(a)) + δ(a)` with `δ(a) ∈ Y`, which needs `p` to be
  the projection along `Y`.  Here `p` is **the projection along `Y`** (`p = 1` on `N`, `p = 0`
  on `Y`, two hypotheses of `proposition_4_1_9`); the identities the proof uses, `(1 − p)Dt(0) = 0`
  and `Dt(0) = 1` on `N`, hold for it (`GraphData.qL_lvlDeriv_zero`, `lvlDeriv_zero_of_mem_N`).
* **`Y` is closed** (added hypothesis, as in Findings Chapter 3, items 81 and 93): otherwise `p`
  is not continuous.  With `N` finite-dimensional, `E = N ⊕ Y` is then a topological splitting.
* **The direct proof.**  The text's route through Lemma 4.1.11 (preprint 4.10) and Theorem 3.5.11 (preprint 3.47) produces `δ` only
  as an sc-smooth *germ* (neighbourhoods depending on the level and the order of
  differentiability, Findings Chapter 3, items 2 and 82) and with a good complement of Corollary
  3.47's own choice, not `Y`; the claim of an sc-diffeomorphism on fixed open sets, with inverse
  `a ↦ a + δ(a)` sc-smooth on the fixed `V`, needs a direct argument.  It uses the sc⁺ property:
  `t : U_{k+1} → E_{k+1}` is `C¹` with `Dt(x) ∈ L(E_{k+1})` continuous in the operator norm
  (Proposition 1.2.1 (preprint 1.16) for the lift `t¹ : U → E¹`), so the mean value estimate
  `‖(t z' − t z) − Dt(u₀)(z' − z)‖ ≤ θ‖z' − z‖` holds on `C_{k+1} ∩ B(u₀, r)` on every level.
  Uniqueness and existence are the text's Lemmas 4.1.12 and 4.1.13 (preprint 4.11 and 4.12) on level `1` (the existence by a
  contraction for `y ↦ (1 − p)t(a + y)` on `{y ∈ Y₁ | ‖y‖₁ ≤ ε'‖a‖₁}`, a set on which `a + y ∈ C`
  by the good complement property; the text takes `δ` from Theorem 3.5.11 (preprint 3.47) instead).  The step
  `p(O ∩ W) ⊆ C`, which the text does not address, follows from `|(1 − p)u|₀ ≤ ε|p(u)|₀` and the
  good complement property.  The regularity on the fixed `V`: `Γ` is continuous into every level
  because `t : U_m → E_{m+1}` is continuous and `Γ = t ∘ Γ`; `Γ` is differentiable into every
  level with the frame formula, by the mean value estimate at `u₀ = Γ(a)` (not at `0`) and the
  projection onto `T_{u₀}O` along `Y`, which exists since `T_{u₀}O ∩ Y = 0` (the level-`1`
  estimate again); and derivatives of `t` are only applied to the finite-dimensional smooth `N`,
  so the level loss of `Tt` (Proposition 1.2.3 (preprint 1.18)) does not accumulate: `Γ` is `C^{k+1}` into every
  level as soon as it is `C^k` into every level.  The criterion `IsScSmooth.of_contDiffOn_levels`
  (Proposition 1.2.4 (preprint 1.19)) closes.
* The neighbourhood `U₀ = {a + δ(a) | a ∈ V}` "open in `O`" is `O ∩ W` with `W` open in `E₀`
  (`W = B(0, δ₀) ∩ p⁻¹(V')`); the level-`1` control `‖u‖₁ < r` of its points comes from the
  continuity of `t : U → E₁` at `0` and `u = t(u)` — the sc⁺ property a second time.
* `[FiniteDimensional ℝ N]` is a hypothesis of the statement (needed to form the sc-Banach space
  `N` with its constant structure); it is Lemma 4.1.7 (preprint 4.7) (ii), `finiteDimensional_tangentSpace_zero`.
* The mean value estimate is proved on the convex set `C_{k+1} ∩ B(u₀, r)` (contained in `U_{k+1}`
  for `r` small) rather than on `U_{k+1}`, which need not be convex; the text's integral (77) is
  the mean value inequality.
-/

open Set Filter Topology Function Metric
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### A mean value estimate -/

/-- **The mean value estimate** behind Lemmas 4.1.12 and 4.1.13 (preprint 4.11 and 4.12) (the text's (76)–(77)): if `s` is
differentiable within the convex set `S` with derivative `D`, continuous at `u₀ ∈ S` in the
operator norm, then for every `θ > 0` there is `r > 0` with
`‖(s z' − s z) − Ds(u₀)(z' − z)‖ ≤ θ‖z' − z‖` for all `z, z' ∈ S ∩ B(u₀, r)`. -/
theorem exists_norm_sub_sub_le_of_hasFDerivWithinAt {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {S : Set X} (hS : Convex ℝ S) {s : X → X} {D : X → X →L[ℝ] X}
    (hd : ∀ x ∈ S, HasFDerivWithinAt s (D x) S x) {u₀ : X}
    (hD : ContinuousWithinAt D S u₀) {θ : ℝ} (hθ : 0 < θ) :
    ∃ r > 0, ∀ z ∈ S, ∀ z' ∈ S, ‖z - u₀‖ < r → ‖z' - u₀‖ < r →
      ‖(s z' - s z) - D u₀ (z' - z)‖ ≤ θ * ‖z' - z‖ := by
  obtain ⟨r, hr, hr'⟩ := Metric.continuousWithinAt_iff.1 hD θ hθ
  refine ⟨r, hr, fun z hz z' hz' hzr hz'r => ?_⟩
  set S' := S ∩ ball u₀ r with hS'
  have hS'c : Convex ℝ S' := hS.inter (convex_ball u₀ r)
  have hf : ∀ x ∈ S', HasFDerivWithinAt (fun x => s x - D u₀ x) (D x - D u₀) S' x :=
    fun x hx => ((hd x hx.1).mono inter_subset_left).sub (D u₀).hasFDerivWithinAt
  have hb : ∀ x ∈ S', ‖D x - D u₀‖ ≤ θ := fun x hx => by
    have := hr' hx.1 (mem_ball.1 hx.2)
    rw [dist_eq_norm] at this
    exact this.le
  have hzS : z ∈ S' := ⟨hz, mem_ball.2 (by rwa [dist_eq_norm])⟩
  have hz'S : z' ∈ S' := ⟨hz', mem_ball.2 (by rwa [dist_eq_norm])⟩
  have := hS'c.norm_image_sub_le_of_norm_hasFDerivWithin_le hf hb hzS hz'S
  convert this using 2
  rw [map_sub]
  abel

/-! ### The level data of an sc⁺-retraction

For an sc⁺-retraction `t : U → U` the lift `t¹ = ι⁻¹ ∘ t : U → E¹` is sc-smooth, so by
Proposition 1.2.1 (preprint 1.16) the map `t : U_{k+1} → E_{k+1}` is `C¹` with a derivative
`Dt_{k+1}(x) ∈ L(E_{k+1}, E_{k+1})` depending continuously on `x ∈ U_{k+1}` in the operator norm.
These are the level maps `T.lvlMap k` and derivatives `T.lvlDeriv k` below; for `k = 0` they are
the maps `t : U₁ → E₁` and `Dt(u) ∈ L(E₁, E₁)` of the text's (76). -/

section LevelData

variable {E : ScBanach} {C : Set (E 0)} (T : ScRetraction E C)

/-- The lift `t¹ : U → E¹`, `x ↦ t(x) ∈ E₁`, of an sc⁺-retraction. -/
def ScRetraction.liftOne : E 0 → E 1 := E.liftOne ∘ T

/-- The derivative family of the lift `t¹`. -/
def ScRetraction.liftDeriv : E 1 → E 0 →L[ℝ] E 1 :=
  scDeriv (E := E) (F := E.shift) T.U T.liftOne

/-- The map `t : U_{k+1} → E_{k+1}` induced on level `k + 1`. -/
def ScRetraction.lvlMap (k : ℕ) : E (k + 1) → E (k + 1) :=
  levelMap (E := E) (F := E.shift) T.liftOne k ∘ E.incl k

/-- The derivative `Dt(x) ∈ L(E_{k+1}, E_{k+1})` of `t : U_{k+1} → E_{k+1}` at `x ∈ U_{k+1}`. -/
def ScRetraction.lvlDeriv (k : ℕ) (x : E (k + 1)) : E (k + 1) →L[ℝ] E (k + 1) :=
  (levelDeriv (E := E) (F := E.shift) T.liftDeriv k x).comp (E.incl k)

variable {T} (hT : T.IsScPlus)
include hT

lemma ScRetraction.IsScPlus.isScSmooth_liftOne :
    IsScSmooth (E := E) (F := E.shift) T.U T.liftOne :=
  hT.isScSmooth_lift

lemma ScRetraction.IsScPlus.isSc1With_liftOne :
    IsSc1With (E := E) (F := E.shift) T.U T.liftOne T.liftDeriv :=
  hT.isScSmooth_lift.isSc1.isSc1With_scDeriv

/-- `t : U_{k+1} → E_{k+1}` is differentiable at `x ∈ U_{k+1}` with derivative `Dt(x)`
(Proposition 1.2.1 (preprint 1.16) for the lift). -/
theorem ScRetraction.IsScPlus.hasFDerivWithinAt_lvlMap (k : ℕ) {x : E (k + 1)}
    (hx : x ∈ E.lvlSet T.U (k + 1)) :
    HasFDerivWithinAt (T.lvlMap k) (T.lvlDeriv k x) (E.lvlSet T.U (k + 1)) x :=
  hT.isSc1With_liftOne.hasFDerivWithinAt_level T.isScDomain hx

/-- `x ↦ Dt(x) ∈ L(E_{k+1}, E_{k+1})` is continuous on `U_{k+1}` in the operator norm
(Proposition 1.2.1 (preprint 1.16) (1)). -/
theorem ScRetraction.IsScPlus.continuousOn_lvlDeriv (k : ℕ) :
    ContinuousOn (T.lvlDeriv k) (E.lvlSet T.U (k + 1)) :=
  hT.isSc1With_liftOne.continuousOn_levelDeriv_clm k

/-- `t : U_{k+1} → E_{k+1}` is continuous. -/
theorem ScRetraction.IsScPlus.continuousOn_lvlMap (k : ℕ) :
    ContinuousOn (T.lvlMap k) (E.lvlSet T.U (k + 1)) := by
  have := hT.isScSmooth_liftOne.isSc1.isSc0.continuousOn k
  exact this.comp (E.incl k).continuous.continuousOn fun x hx => hx

/-- `t` fixes the points of `O_{k+1}` on level `k + 1`. -/
theorem ScRetraction.IsScPlus.lvlMap_eq_self (k : ℕ) {u : E (k + 1)}
    (hu : E.toBase (k + 1) u ∈ T.retract) : T.lvlMap k u = u := by
  have hu' : E.incl k u ∈ E.lvlSet T.U k := T.retract_subset hu
  have h0 := hT.isScSmooth_liftOne.isSc1.isSc0
  apply E.shift.toBase_injective k
  change E.shift.toBase k (levelMap (E := E) (F := E.shift) T.liftOne k (E.incl k u)) = _
  rw [h0.toBase_levelMap hu']
  change E.liftOne (T (E.toBase (k + 1) u)) = _
  rw [T.apply_eq_self_of_mem_retract hu, E.shift_toBase, E.liftOne_toBase]

/-- The level-`k+1` map is `t` on `U_{k+1}`: `ι_{k+1} ∘ t_{k+1} = t ∘ ι_{k+1}`. -/
theorem ScRetraction.IsScPlus.toBase_lvlMap (k : ℕ) {x : E (k + 1)}
    (hx : x ∈ E.lvlSet T.U (k + 1)) :
    E.toBase (k + 1) (T.lvlMap k x) = T (E.toBase (k + 1) x) := by
  have hx' : E.incl k x ∈ E.lvlSet T.U k := hx
  have h0 := hT.isScSmooth_liftOne.isSc1.isSc0
  rw [E.shift_toBase]
  change E.toBase 1 (E.shift.toBase k (levelMap (E := E) (F := E.shift) T.liftOne k (E.incl k x))) =
    _
  rw [h0.toBase_levelMap hx']
  change E.toBase 1 (E.liftOne (T (E.toBase (k + 1) x))) = _
  exact E.toBase_liftOne (hT.mem_range _ hx)

/-- `ι₁ ∘ Dt¹(x) = Dt(x)` on `U₁`: the derivative of the lift is the derivative of `t` (chain rule
for `t = ι ∘ t¹` and the uniqueness of the sc-derivative on an sc-domain). -/
theorem ScRetraction.IsScPlus.toBase_liftDeriv {x : E 1} (hx : x ∈ E.lvlSet T.U 1) (v : E 0) :
    E.toBase 1 (T.liftDeriv x v) = scDeriv T.U T x v := by
  have hU := T.isScDomain
  have hgsc := hT.isScSmooth_liftOne
  have hfg : EqOn (E.shiftIncl 0 ∘ T.liftOne) T T.U := fun y hy => hT.toBase_lift hy
  have h1 := scDeriv_comp_apply_of_isScDomain hU (isScDomain_univ _) hgsc.isSc1
    ((E.shiftIncl.isScSmooth (isScDomain_univ _)).isSc1) (mapsTo_univ _ _) hx v
  rw [ScOperator.scDeriv_eq _ (isScDomain_univ _) (mem_univ _)] at h1
  have h2 : scDeriv T.U (E.shiftIncl 0 ∘ T.liftOne) x v = scDeriv T.U T x v := by
    have hsc : IsScSmooth T.U (E.shiftIncl 0 ∘ T.liftOne) := IsScSmooth.comp hU (isScDomain_univ _)
      (E.shiftIncl.isScSmooth (isScDomain_univ _)) hgsc (mapsTo_univ _ _)
    have hf1 : IsSc1With T.U T (scDeriv T.U (E.shiftIncl 0 ∘ T.liftOne)) :=
      hsc.isSc1.isSc1With_scDeriv.congr hfg
    exact congrArg (fun L : E 0 →L[ℝ] E 0 => L v)
      (IsSc1.scDeriv_eqOn hf1 (hU.uniqueDiffWithinAt 1) hx).symm
  rw [← h2, ← h1]
  rfl

/-- The level-`k+1` derivative is the restriction of `Dt`: `ι_{k+1} ∘ Dt_{k+1}(x) = Dt(x) ∘ ι_{k+1}`
for `x ∈ U_{k+1}` (Lemma 3.H of the exposition for the lift). -/
theorem ScRetraction.IsScPlus.toBase_lvlDeriv (k : ℕ) {x : E (k + 1)}
    (hx : x ∈ E.lvlSet T.U (k + 1)) (v : E (k + 1)) :
    E.toBase (k + 1) (T.lvlDeriv k x v) =
      scDeriv T.U T (E.shift.toBase k x) (E.toBase (k + 1) v) := by
  have h := hT.isSc1With_liftOne.toBase_levelDeriv hx (E.incl k v)
  have hx1 : E.shift.toBase k x ∈ E.lvlSet T.U 1 := E.mem_lvlSet_shift_toBase.2 hx
  rw [E.shift_toBase]
  change E.toBase 1 (E.shift.toBase k
    (levelDeriv (E := E) (F := E.shift) T.liftDeriv k x (E.incl k v))) = _
  rw [h, hT.toBase_liftDeriv hx1]
  rfl

/-- `Dt_{k+1}(u)` is a projection for `u ∈ O_{k+1}` (`Dt(u) ∘ Dt(u) = Dt(u)` on `O₁`). -/
theorem ScRetraction.IsScPlus.lvlDeriv_lvlDeriv (k : ℕ) {u : E (k + 1)}
    (hu : E.toBase (k + 1) u ∈ T.retract) (v : E (k + 1)) :
    T.lvlDeriv k u (T.lvlDeriv k u v) = T.lvlDeriv k u v := by
  have huU : u ∈ E.lvlSet T.U (k + 1) := T.retract_subset hu
  have hu1 : E.shift.toBase k u ∈ E.lvlSet T.retract 1 := by
    rw [ScBanach.mem_lvlSet, ← E.shift_toBase]; exact hu
  apply E.toBase_injective (k + 1)
  rw [hT.toBase_lvlDeriv k huU, hT.toBase_lvlDeriv k huU]
  exact congrArg (fun L : E 0 →L[ℝ] E 0 => L (E.toBase (k + 1) v)) (T.scDeriv_comp_self hu1)

omit hT in
/-- A ball around `u₀ ∈ U_{k+1}` in `E_{k+1}` meets `C_{k+1}` inside `U_{k+1}`. -/
theorem ScRetraction.exists_ball_inter_subset (k : ℕ) {u₀ : E (k + 1)}
    (hu₀ : u₀ ∈ E.lvlSet T.U (k + 1)) :
    ∃ r₀ > 0, E.lvlSet C (k + 1) ∩ ball u₀ r₀ ⊆ E.lvlSet T.U (k + 1) := by
  obtain ⟨O', hO', hU⟩ := T.relOpen.relOpen
  have hu₀' : u₀ ∈ E.lvlSet O' (k + 1) := by
    rw [ScBanach.mem_lvlSet] at hu₀ ⊢; rw [hU] at hu₀; exact hu₀.1
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 (E.isOpen_lvlSet hO' (k + 1)) u₀ hu₀'
  refine ⟨r₀, hr₀, fun z hz => ?_⟩
  rw [ScBanach.mem_lvlSet, hU]
  exact ⟨hball hz.2, hz.1⟩

omit hT in
/-- Points of `U` lie in `C`. -/
lemma ScRetraction.lvlSet_U_subset_lvlSet_C (m : ℕ) : E.lvlSet T.U m ⊆ E.lvlSet C m := by
  obtain ⟨O', -, hU⟩ := T.relOpen.relOpen
  intro x hx
  rw [ScBanach.mem_lvlSet, hU] at hx
  exact hx.2

/-- **The mean value estimate for an sc⁺-retraction** (the text's (76)–(77), on every level): for
`u₀ ∈ U_{k+1}` and `θ > 0` there is `r > 0` such that `C_{k+1} ∩ B(u₀, r) ⊆ U_{k+1}` and
`‖(t z' − t z) − Dt(u₀)(z' − z)‖_{k+1} ≤ θ‖z' − z‖_{k+1}` for `z, z' ∈ C_{k+1} ∩ B(u₀, r)`. -/
theorem ScRetraction.IsScPlus.exists_mvt (k : ℕ) {u₀ : E (k + 1)}
    (hu₀ : u₀ ∈ E.lvlSet T.U (k + 1)) {θ : ℝ} (hθ : 0 < θ) :
    ∃ r > 0, E.lvlSet C (k + 1) ∩ ball u₀ r ⊆ E.lvlSet T.U (k + 1) ∧
      (∀ z ∈ E.lvlSet C (k + 1), ‖z - u₀‖ < r → ‖T.lvlDeriv k z - T.lvlDeriv k u₀‖ ≤ θ) ∧
      ∀ z ∈ E.lvlSet C (k + 1), ∀ z' ∈ E.lvlSet C (k + 1), ‖z - u₀‖ < r → ‖z' - u₀‖ < r →
        ‖(T.lvlMap k z' - T.lvlMap k z) - T.lvlDeriv k u₀ (z' - z)‖ ≤ θ * ‖z' - z‖ := by
  obtain ⟨r₀, hr₀, hsub⟩ := T.exists_ball_inter_subset k hu₀
  set S := E.lvlSet C (k + 1) ∩ ball u₀ r₀ with hS
  have hSc : Convex ℝ S :=
    (T.relOpen.isPartialQuadrant.convex_lvlSet (k + 1)).inter (convex_ball u₀ r₀)
  have hu₀S : u₀ ∈ S := ⟨T.lvlSet_U_subset_lvlSet_C (k + 1) hu₀, mem_ball_self hr₀⟩
  have hd : ∀ x ∈ S, HasFDerivWithinAt (T.lvlMap k) (T.lvlDeriv k x) S x := fun x hx =>
    (hT.hasFDerivWithinAt_lvlMap k (hsub hx)).mono hsub
  have hD : ContinuousWithinAt (T.lvlDeriv k) S u₀ :=
    ((hT.continuousOn_lvlDeriv k).mono hsub) u₀ hu₀S
  obtain ⟨r, hr, hest⟩ := exists_norm_sub_sub_le_of_hasFDerivWithinAt hSc hd hD hθ
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.continuousWithinAt_iff.1 hD θ hθ
  refine ⟨min (min r r₀) r₁, lt_min (lt_min hr hr₀) hr₁, fun z hz => hsub ⟨hz.1, ?_⟩,
    fun z hz hzr => ?_, fun z hz z' hz' hzr hz'r => ?_⟩
  · exact mem_ball.2 (lt_of_lt_of_le (mem_ball.1 hz.2) ((min_le_left _ _).trans (min_le_right _ _)))
  · have hzS : z ∈ S := ⟨hz, mem_ball.2 (by
      rw [dist_eq_norm]; exact hzr.trans_le ((min_le_left _ _).trans (min_le_right _ _)))⟩
    have := hr₁' hzS (by rw [dist_eq_norm]; exact hzr.trans_le (min_le_right _ _))
    rw [dist_eq_norm] at this
    exact this.le
  · have hzr' : ‖z - u₀‖ < min r r₀ := hzr.trans_le (min_le_left _ _)
    have hz'r' : ‖z' - u₀‖ < min r r₀ := hz'r.trans_le (min_le_left _ _)
    have hzS : z ∈ S :=
      ⟨hz, mem_ball.2 (by rw [dist_eq_norm]; exact hzr'.trans_le (min_le_right _ _))⟩
    have hz'S : z' ∈ S :=
      ⟨hz', mem_ball.2 (by rw [dist_eq_norm]; exact hz'r'.trans_le (min_le_right _ _))⟩
    exact hest z hzS z' hz'S (hzr'.trans_le (min_le_left _ _)) (hz'r'.trans_le (min_le_left _ _))

end LevelData

/-! ### The data of Proposition 4.1.9 (preprint 4.9)

The sc⁺-retraction `t` onto `O ∋ 0`, the tangent space `N = T₀O`, a closed good complement `Y`
(**added hypothesis**: the text's "sc-complement"; closedness is what makes the projection
continuous, as in Findings Chapter 3, items 81 and 93), and the projection `p : E → N` along `Y`
(**not** `Dt(0)`, see the module docstring). -/

/-- The data of Proposition 4.1.9 (preprint 4.9): an sc⁺-retraction `t : U → U` onto `O ∋ 0` in the partial
quadrant `C ⊆ E`, the tangent space `N = T₀O`, a closed good complement `Y` of `N`, and the
continuous projection `p : E → N` along `Y` (`p = 1` on `N`, `p = 0` on `Y`). -/
structure GraphData (E : ScBanach) (C : Set (E 0)) where
  /-- The sc⁺-retraction `t`. -/
  T : ScRetraction E C
  isScPlus : T.IsScPlus
  zero_mem : (0 : E 0) ∈ T.retract
  /-- The tangent space `N = T₀O`. -/
  N : Submodule ℝ (E 0)
  N_eq : (N : Set (E 0)) = tangentSpace E C T.retract 0
  goodPosition : IsInGoodPosition E C N
  /-- The good complement `Y`. -/
  Y : Submodule ℝ (E 0)
  goodComplement : IsGoodComplement E C N Y
  isClosed_Y : IsClosed (Y : Set (E 0))
  /-- The projection `p : E → N` along `Y`. -/
  p : E 0 →L[ℝ] N
  p_apply_N : ∀ n : N, p n = n
  p_apply_Y : ∀ y ∈ Y, p y = 0

namespace GraphData

variable {E : ScBanach} {C : Set (E 0)} (d : GraphData E C)

lemma zero_mem_lvlSet_retract (m : ℕ) : (0 : E m) ∈ E.lvlSet d.T.retract m := by
  rw [ScBanach.mem_lvlSet, map_zero]; exact d.zero_mem

lemma zero_mem_lvlSet_U (m : ℕ) : (0 : E m) ∈ E.lvlSet d.T.U m :=
  d.T.lvlSet_retract_subset m (d.zero_mem_lvlSet_retract m)

/-- `N = Dt(0)E` (Lemma 4.1.7 (preprint 4.7) (ii) and the remark after Definition 2.3.12 (preprint 2.17)). -/
theorem N_eq_range : d.N = LinearMap.range (scDeriv d.T.U d.T 0 : E 0 →ₗ[ℝ] E 0) :=
  SetLike.coe_injective
    (d.N_eq.trans (tangentSpace_eq_coe_submodule d.T (d.zero_mem_lvlSet_retract 1)))

/-- **Lemma 4.1.7 (preprint 4.7) (ii)**: `N = T₀O` is finite-dimensional. -/
instance finiteDimensional : FiniteDimensional ℝ d.N := by
  have := lemma_4_1_7_ii d.isScPlus (d.zero_mem_lvlSet_retract 1)
  exact Submodule.finiteDimensional_of_le d.N_eq_range.le

lemma scDeriv_zero_mem (v : E 0) : scDeriv d.T.U d.T 0 v ∈ d.N := by
  rw [d.N_eq_range]; exact ⟨v, rfl⟩

lemma scDeriv_zero_of_mem {n : E 0} (hn : n ∈ d.N) : scDeriv d.T.U d.T 0 n = n := by
  rw [d.N_eq_range] at hn
  obtain ⟨v, rfl⟩ := hn
  exact congrArg (fun L : E 0 →L[ℝ] E 0 => L v)
    (d.T.scDeriv_comp_self (d.zero_mem_lvlSet_retract 1))

/-- `N ⊆ E_∞`: `Dt(0)` is an sc⁺-operator and `N` consists of its fixed vectors
(Lemma 4.1.7 (preprint 4.7) (ii): "the tangent space `T₀O` is a smooth subspace"). -/
theorem smooth : d.N ≤ E.smooth := by
  have h0s : (0 : E 1) ∈ E.smoothLvl 1 := by
    change E.toBase 1 (0 : E 1) ∈ (E.smooth : Set (E 0))
    rw [map_zero]; exact E.smooth.zero_mem
  obtain ⟨S, hS⟩ := d.isScPlus.exists_scPlus_deriv d.T.isScDomain (d.zero_mem_lvlSet_U 1) h0s
  intro n hn
  rw [ScScale.mem_smooth_iff]
  intro m
  induction m with
  | zero => exact ⟨n, rfl⟩
  | succ m ih =>
    obtain ⟨y, hy⟩ := ih
    have := (S.isScPlus (isScDomain_univ E)).mem_range_succ m (x := y) (mem_univ _)
    rw [hy, hS, d.scDeriv_zero_of_mem hn] at this
    exact this

lemma isCompl : IsCompl d.N d.Y := d.goodComplement.isCompl

/-- `Y = ker p`. -/
theorem mem_Y_iff {x : E 0} : x ∈ d.Y ↔ d.p x = 0 := by
  refine ⟨d.p_apply_Y x, fun hx => ?_⟩
  have hsup : x ∈ d.N ⊔ d.Y := by rw [d.isCompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨n, hn, y, hy, rfl⟩ := Submodule.mem_sup.1 hsup
  have h1 : d.p n = 0 := by
    have := hx; rwa [map_add, d.p_apply_Y y hy, add_zero] at this
  have h2 : d.p n = ⟨n, hn⟩ := d.p_apply_N ⟨n, hn⟩
  have h3 : n = 0 := by
    have := congrArg (fun z : d.N => (z : E 0)) (h2.symm.trans h1)
    simpa using this
  rw [h3, zero_add]; exact hy

lemma sub_p_mem_Y (x : E 0) : x - d.p x ∈ d.Y := by
  rw [d.mem_Y_iff, map_sub, d.p_apply_N, sub_self]

lemma p_coe_mem_N (x : E 0) : (d.p x : E 0) ∈ d.N := (d.p x).2

/-- The lift `N → E_m` (`N ⊆ E_∞` is finite-dimensional, so the lift is continuous). -/
def liftN (m : ℕ) : d.N →L[ℝ] E m := LinearMap.toContinuousLinearMap (finSmoothLift d.smooth m)

@[simp] lemma toBase_liftN (m : ℕ) (n : d.N) : E.toBase m (d.liftN m n) = n :=
  toBase_finSmoothLift d.smooth m n

lemma liftN_eq_iff {m : ℕ} {n : d.N} {v : E m} : d.liftN m n = v ↔ E.toBase m v = n := by
  constructor
  · rintro rfl; exact d.toBase_liftN m n
  · intro h; apply E.toBase_injective m; rw [d.toBase_liftN, h]

/-- The projection `p` on level `m`, `E_m → N ⊆ E_m`. -/
def pL (m : ℕ) : E m →L[ℝ] E m := (d.liftN m).comp (d.p.comp (E.toBase m))

/-- The complementary projection `1 − p` on level `m`. -/
def qL (m : ℕ) : E m →L[ℝ] E m := ContinuousLinearMap.id ℝ (E m) - d.pL m

lemma toBase_pL (m : ℕ) (v : E m) : E.toBase m (d.pL m v) = d.p (E.toBase m v) :=
  d.toBase_liftN m _

lemma qL_apply (m : ℕ) (v : E m) : d.qL m v = v - d.pL m v := rfl

lemma toBase_qL (m : ℕ) (v : E m) : E.toBase m (d.qL m v) = E.toBase m v - d.p (E.toBase m v) := by
  rw [qL_apply, map_sub, toBase_pL]

lemma toBase_qL_mem_Y (m : ℕ) (v : E m) : E.toBase m (d.qL m v) ∈ d.Y := by
  rw [toBase_qL]; exact d.sub_p_mem_Y _

lemma pL_of_mem_N {m : ℕ} {v : E m} (hv : E.toBase m v ∈ d.N) : d.pL m v = v := by
  apply E.toBase_injective m
  rw [toBase_pL]
  have := d.p_apply_N ⟨_, hv⟩
  exact congrArg (fun z : d.N => (z : E 0)) this

lemma pL_of_mem_Y {m : ℕ} {v : E m} (hv : E.toBase m v ∈ d.Y) : d.pL m v = 0 := by
  apply E.toBase_injective m
  rw [toBase_pL, d.p_apply_Y _ hv, map_zero]; rfl

lemma qL_of_mem_N {m : ℕ} {v : E m} (hv : E.toBase m v ∈ d.N) : d.qL m v = 0 := by
  rw [qL_apply, d.pL_of_mem_N hv, sub_self]

lemma qL_of_mem_Y {m : ℕ} {v : E m} (hv : E.toBase m v ∈ d.Y) : d.qL m v = v := by
  rw [qL_apply, d.pL_of_mem_Y hv, sub_zero]

lemma qL_eq_zero_iff {m : ℕ} {v : E m} : d.qL m v = 0 ↔ E.toBase m v ∈ d.N := by
  refine ⟨fun h => ?_, d.qL_of_mem_N⟩
  have := d.toBase_qL m v
  rw [h, map_zero] at this
  have h2 : E.toBase m v = d.p (E.toBase m v) := by
    have := this.symm; rwa [sub_eq_zero] at this
  rw [h2]; exact d.p_coe_mem_N _

lemma qL_add_pL (m : ℕ) (v : E m) : d.qL m v + d.pL m v = v := by
  rw [qL_apply, sub_add_cancel]

/-- `(1 − p) ∘ Dt(0) = 0` on every level: the range of `Dt(0)` is `N`. -/
lemma qL_lvlDeriv_zero (k : ℕ) (v : E (k + 1)) : d.qL (k + 1) (d.T.lvlDeriv k 0 v) = 0 := by
  rw [d.qL_eq_zero_iff, d.isScPlus.toBase_lvlDeriv k (d.zero_mem_lvlSet_U (k + 1)), map_zero]
  exact d.scDeriv_zero_mem _

/-- `Dt(0) = 1` on `N`, on every level. -/
lemma lvlDeriv_zero_of_mem_N (k : ℕ) {v : E (k + 1)} (hv : E.toBase (k + 1) v ∈ d.N) :
    d.T.lvlDeriv k 0 v = v := by
  apply E.toBase_injective (k + 1)
  rw [d.isScPlus.toBase_lvlDeriv k (d.zero_mem_lvlSet_U (k + 1)), map_zero,
    d.scDeriv_zero_of_mem hv]

lemma norm_coe (n : d.N) : ‖(n : E 0)‖ = ‖n‖ := rfl

/-! ### The good complement constant -/

/-- The constant `ε` of the good complement `Y` (Definition 3.1.24 (preprint 3.21)). -/
def eps : ℝ := d.goodComplement.exists_eps.choose

lemma eps_pos : 0 < d.eps := d.goodComplement.exists_eps.choose_spec.1

lemma eps_spec {x : E 0} (hx : x ∈ d.N) {y : E 0} (hy : y ∈ d.Y) (h : ‖y‖ ≤ d.eps * ‖x‖) :
    x ∈ C ↔ x + y ∈ C :=
  d.goodComplement.exists_eps.choose_spec.2 x hx y hy h

/-- The level-`1` version of `ε`: `|y|₀ ≤ ‖ι₁‖‖y‖₁` and `‖a‖₁ ≤ ‖lift‖|a|₀` for `a ∈ N`, so
`‖y‖₁ ≤ ε'‖a‖₁` implies `|y|₀ ≤ ε|a|₀`. -/
def eps' : ℝ := d.eps / (‖E.toBase 1‖ * ‖d.liftN 1‖ + 1)

lemma eps'_pos : 0 < d.eps' := by
  unfold eps'; have := d.eps_pos; positivity

lemma norm_toBase_le_eps_mul {a : d.N} {y : E 1} (hy : ‖y‖ ≤ d.eps' * ‖d.liftN 1 a‖) :
    ‖E.toBase 1 y‖ ≤ d.eps * ‖(a : E 0)‖ := by
  have h1 : ‖E.toBase 1 y‖ ≤ ‖E.toBase 1‖ * ‖y‖ := (E.toBase 1).le_opNorm y
  have h2 : ‖d.liftN 1 a‖ ≤ ‖d.liftN 1‖ * ‖a‖ := (d.liftN 1).le_opNorm a
  have h3 : ‖E.toBase 1‖ * ‖d.liftN 1‖ * d.eps' ≤ d.eps := by
    unfold eps'
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have := d.eps_pos
    nlinarith [norm_nonneg (E.toBase 1), norm_nonneg (d.liftN 1)]
  have h4 : ‖y‖ ≤ d.eps' * (‖d.liftN 1‖ * ‖a‖) :=
    hy.trans (mul_le_mul_of_nonneg_left h2 d.eps'_pos.le)
  rw [norm_coe]
  calc ‖E.toBase 1 y‖ ≤ ‖E.toBase 1‖ * ‖y‖ := h1
    _ ≤ ‖E.toBase 1‖ * (d.eps' * (‖d.liftN 1‖ * ‖a‖)) := by gcongr
    _ = (‖E.toBase 1‖ * ‖d.liftN 1‖ * d.eps') * ‖a‖ := by ring
    _ ≤ d.eps * ‖a‖ := by gcongr

/-! ### Lemma 4.1.12 (preprint 4.11): the contraction estimate near `0` -/

/-- **The contraction estimate of Lemma 4.1.12 (preprint 4.11)** (on level `k + 1`): for `θ > 0` there is `r > 0`
with `C_{k+1} ∩ B(0, r) ⊆ U_{k+1}`, `‖Dt(z) − Dt(0)‖ ≤ θ` on `C_{k+1} ∩ B(0, r)`, the mean value
estimate `‖(t z' − t z) − Dt(0)(z' − z)‖ ≤ θ‖z' − z‖` there, and for `u, u' ∈ O_{k+1} ∩ B(0, r)`
the text's (77): `‖(1 − p)(u' − u)‖ ≤ ‖1 − p‖ θ ‖u' − u‖`. -/
theorem exists_contraction_radius (k : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ r > 0, E.lvlSet C (k + 1) ∩ ball 0 r ⊆ E.lvlSet d.T.U (k + 1) ∧
      (∀ z ∈ E.lvlSet C (k + 1), ‖z‖ < r → ‖d.T.lvlDeriv k z - d.T.lvlDeriv k 0‖ ≤ θ) ∧
      (∀ z ∈ E.lvlSet C (k + 1), ∀ z' ∈ E.lvlSet C (k + 1), ‖z‖ < r → ‖z'‖ < r →
        ‖(d.T.lvlMap k z' - d.T.lvlMap k z) - d.T.lvlDeriv k 0 (z' - z)‖ ≤ θ * ‖z' - z‖) ∧
      ∀ u ∈ E.lvlSet d.T.retract (k + 1), ∀ u' ∈ E.lvlSet d.T.retract (k + 1),
        ‖u‖ < r → ‖u'‖ < r → ‖d.qL (k + 1) (u' - u)‖ ≤ ‖d.qL (k + 1)‖ * θ * ‖u' - u‖ := by
  obtain ⟨r, hr, hsub, hder, hmvt⟩ := d.isScPlus.exists_mvt k (d.zero_mem_lvlSet_U (k + 1)) hθ
  simp only [sub_zero] at hder hmvt
  refine ⟨r, hr, hsub, hder, hmvt, fun u hu u' hu' hur hu'r => ?_⟩
  have huC : u ∈ E.lvlSet C (k + 1) :=
    d.T.lvlSet_U_subset_lvlSet_C (k + 1) (d.T.lvlSet_retract_subset (k + 1) hu)
  have hu'C : u' ∈ E.lvlSet C (k + 1) :=
    d.T.lvlSet_U_subset_lvlSet_C (k + 1) (d.T.lvlSet_retract_subset (k + 1) hu')
  have h := hmvt u huC u' hu'C hur hu'r
  rw [d.isScPlus.lvlMap_eq_self k hu, d.isScPlus.lvlMap_eq_self k hu'] at h
  have hq : d.qL (k + 1) (u' - u) = d.qL (k + 1) ((u' - u) - d.T.lvlDeriv k 0 (u' - u)) := by
    rw [map_sub (d.qL (k + 1)) (u' - u) (d.T.lvlDeriv k 0 (u' - u)), d.qL_lvlDeriv_zero, sub_zero]
  rw [hq]
  calc ‖d.qL (k + 1) ((u' - u) - d.T.lvlDeriv k 0 (u' - u))‖
      ≤ ‖d.qL (k + 1)‖ * ‖(u' - u) - d.T.lvlDeriv k 0 (u' - u)‖ := (d.qL (k + 1)).le_opNorm _
    _ ≤ ‖d.qL (k + 1)‖ * (θ * ‖u' - u‖) := by gcongr
    _ = ‖d.qL (k + 1)‖ * θ * ‖u' - u‖ := by ring

/-- **Lemma 4.1.12 (preprint 4.11)** (the uniqueness step): two points `u, u' ∈ O_{k+1}` with the same projection
`p(u) = p(u')` and `‖(1 − p)(u' − u)‖ ≤ c‖u' − u‖`, `c < 1`, coincide. -/
theorem eq_of_p_eq {m : ℕ} {u u' : E m} {c : ℝ} (hc : c < 1)
    (hq : ‖d.qL m (u' - u)‖ ≤ c * ‖u' - u‖)
    (hp : d.p (E.toBase m u) = d.p (E.toBase m u')) : u' = u := by
  have hY : E.toBase m (u' - u) ∈ d.Y := by
    rw [d.mem_Y_iff, map_sub, map_sub, hp, sub_self]
  have h1 : d.qL m (u' - u) = u' - u := d.qL_of_mem_Y hY
  rw [h1] at hq
  have : (1 - c) * ‖u' - u‖ ≤ 0 := by linarith
  have h0 : ‖u' - u‖ ≤ 0 := by
    by_contra h
    push Not at h
    have : 0 < (1 - c) * ‖u' - u‖ := mul_pos (by linarith) h
    linarith
  rw [← sub_eq_zero]
  exact norm_le_zero_iff.1 h0

/-! ### Lemma 4.1.13 (preprint 4.12): existence of the graph point `a + δ(a)` -/

/-- **Lemma 4.1.13 (preprint 4.12)** (existence, by a level-`1` contraction): under the contraction estimate with
constant `θ` on `C₁ ∩ B(0, r)`, `θ < 1`, `‖1 − p‖θ < 1` and `‖1 − p‖ θ (1 + ε') ≤ ε'`, there is
`ρ > 0` such that for every `a ∈ N ∩ C` with `‖a‖₁ < ρ` there is `u ∈ O₁` with `p(u) = a`,
`u − a ∈ Y`, `‖u − a‖₁ ≤ ε'‖a‖₁` and `‖u‖₁ < r`: `u = a + δ(a)` is the fixed point of
`y ↦ (1 − p) t(a + y)` on `{y ∈ Y₁ | ‖y‖₁ ≤ ε'‖a‖₁}`, and `u ∈ O` because
`t(u) − u ∈ N` and `Dt(0) = 1` on `N` force `t(u) = u` (the text's argument `a₁ = a`). -/
theorem exists_graph_point {θ r : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hθ2 : ‖d.qL 1‖ * θ < 1) (hθ3 : ‖d.qL 1‖ * θ * (1 + d.eps') ≤ d.eps') (hr : 0 < r)
    (hsub : E.lvlSet C 1 ∩ ball 0 r ⊆ E.lvlSet d.T.U 1)
    (hmvt : ∀ z ∈ E.lvlSet C 1, ∀ z' ∈ E.lvlSet C 1, ‖z‖ < r → ‖z'‖ < r →
      ‖(d.T.lvlMap 0 z' - d.T.lvlMap 0 z) - d.T.lvlDeriv 0 0 (z' - z)‖ ≤ θ * ‖z' - z‖) :
    ∃ ρ > 0, ∀ a : d.N, (a : E 0) ∈ C → ‖d.liftN 1 a‖ < ρ →
      ∃ u : E 1, E.toBase 1 u ∈ d.T.retract ∧ d.p (E.toBase 1 u) = a ∧
        E.toBase 1 u - a ∈ d.Y ∧ ‖u - d.liftN 1 a‖ ≤ d.eps' * ‖d.liftN 1 a‖ ∧ ‖u‖ < r := by
  have hε' := d.eps'_pos
  set cq := ‖d.qL 1‖ with hcq
  have hcq0 : 0 ≤ cq := norm_nonneg _
  -- `t₁` is continuous at `0`
  have ht0 : d.T.lvlMap 0 0 = 0 := d.isScPlus.lvlMap_eq_self 0 (by rw [map_zero]; exact d.zero_mem)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1
    ((d.isScPlus.continuousOn_lvlMap 0) 0 (d.zero_mem_lvlSet_U 1)) r hr
  set r' := min r δ with hr'
  have hr'pos : 0 < r' := lt_min hr hδ
  refine ⟨r' / (1 + d.eps'), by positivity, fun a haC ha => ?_⟩
  set â := d.liftN 1 a with hâ
  have hâa : E.toBase 1 â = a := d.toBase_liftN 1 a
  have hâN : E.toBase 1 â ∈ d.N := by rw [hâa]; exact a.2
  have h0C : (0 : E 1) ∈ E.lvlSet C 1 := d.T.lvlSet_U_subset_lvlSet_C 1 (d.zero_mem_lvlSet_U 1)
  -- the complete set `B = {y ∈ Y₁ | ‖y‖₁ ≤ ε'‖a‖₁}`
  set B : Set (E 1) := {y | E.toBase 1 y ∈ d.Y ∧ ‖y‖ ≤ d.eps' * ‖â‖} with hB
  have hBclosed : IsClosed B :=
    (d.isClosed_Y.preimage (E.toBase 1).continuous).inter
      (isClosed_le continuous_norm continuous_const)
  have h0B : (0 : E 1) ∈ B := ⟨by rw [map_zero]; exact d.Y.zero_mem, by
    rw [norm_zero]; positivity⟩
  -- (F1): `a + y ∈ C₁ ∩ B(0, r')` for `y ∈ B`
  have hF1 : ∀ y ∈ B, â + y ∈ E.lvlSet C 1 ∧ ‖â + y‖ < r' := by
    intro y hy
    constructor
    · rw [ScBanach.mem_lvlSet, map_add, hâa]
      exact (d.eps_spec a.2 hy.1 (d.norm_toBase_le_eps_mul hy.2)).1 haC
    · calc ‖â + y‖ ≤ ‖â‖ + ‖y‖ := norm_add_le _ _
        _ ≤ ‖â‖ + d.eps' * ‖â‖ := by gcongr; exact hy.2
        _ = (1 + d.eps') * ‖â‖ := by ring
        _ < (1 + d.eps') * (r' / (1 + d.eps')) := by gcongr
        _ = r' := by field_simp
  have hF1' : ∀ y ∈ B, â + y ∈ E.lvlSet d.T.U 1 ∧ ‖â + y‖ < r := fun y hy =>
    ⟨hsub ⟨(hF1 y hy).1, mem_ball.2 (by
      rw [dist_zero_right]; exact (hF1 y hy).2.trans_le (min_le_left _ _))⟩,
      (hF1 y hy).2.trans_le (min_le_left _ _)⟩
  -- the contraction `Φ(y) = (1 − p) t(a + y)`
  set Φ : E 1 → E 1 := fun y => d.qL 1 (d.T.lvlMap 0 (â + y)) with hΦ
  have hmaps : MapsTo Φ B B := by
    intro y hy
    refine ⟨d.toBase_qL_mem_Y 1 _, ?_⟩
    have h := hmvt 0 h0C (â + y) (hF1 y hy).1 (by rw [norm_zero]; exact hr) (hF1' y hy).2
    simp only [ht0, sub_zero] at h
    have hΦy : Φ y = d.qL 1 (d.T.lvlMap 0 (â + y) - d.T.lvlDeriv 0 0 (â + y)) := by
      rw [map_sub (d.qL 1) (d.T.lvlMap 0 (â + y)) (d.T.lvlDeriv 0 0 (â + y)), d.qL_lvlDeriv_zero,
        sub_zero]
    rw [hΦy]
    calc ‖d.qL 1 (d.T.lvlMap 0 (â + y) - d.T.lvlDeriv 0 0 (â + y))‖
        ≤ cq * ‖d.T.lvlMap 0 (â + y) - d.T.lvlDeriv 0 0 (â + y)‖ := (d.qL 1).le_opNorm _
      _ ≤ cq * (θ * ‖â + y‖) := by gcongr
      _ ≤ cq * (θ * ((1 + d.eps') * ‖â‖)) := by
          gcongr
          calc ‖â + y‖ ≤ ‖â‖ + ‖y‖ := norm_add_le _ _
            _ ≤ ‖â‖ + d.eps' * ‖â‖ := by gcongr; exact hy.2
            _ = (1 + d.eps') * ‖â‖ := by ring
      _ = (cq * θ * (1 + d.eps')) * ‖â‖ := by ring
      _ ≤ d.eps' * ‖â‖ := by gcongr
  have hlip : ∀ y ∈ B, ∀ y' ∈ B, ‖Φ y' - Φ y‖ ≤ (cq * θ) * ‖y' - y‖ := by
    intro y hy y' hy'
    have h := hmvt (â + y) (hF1 y hy).1 (â + y') (hF1 y' hy').1 (hF1' y hy).2 (hF1' y' hy').2
    rw [add_sub_add_left_eq_sub] at h
    have hΦ' : Φ y' - Φ y = d.qL 1 ((d.T.lvlMap 0 (â + y') - d.T.lvlMap 0 (â + y)) -
        d.T.lvlDeriv 0 0 (y' - y)) := by
      rw [map_sub (d.qL 1) (d.T.lvlMap 0 (â + y') - d.T.lvlMap 0 (â + y))
        (d.T.lvlDeriv 0 0 (y' - y)), d.qL_lvlDeriv_zero, sub_zero, map_sub]
    rw [hΦ']
    calc ‖d.qL 1 ((d.T.lvlMap 0 (â + y') - d.T.lvlMap 0 (â + y)) - d.T.lvlDeriv 0 0 (y' - y))‖
        ≤ cq * ‖(d.T.lvlMap 0 (â + y') - d.T.lvlMap 0 (â + y)) - d.T.lvlDeriv 0 0 (y' - y)‖ :=
          (d.qL 1).le_opNorm _
      _ ≤ cq * (θ * ‖y' - y‖) := by gcongr
      _ = (cq * θ) * ‖y' - y‖ := by ring
  set K : NNReal := ⟨cq * θ, by positivity⟩ with hK
  have hK1 : K < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_one]
    exact hθ2
  have hlipK : LipschitzOnWith K Φ B := LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => by
    rw [dist_eq_norm, dist_eq_norm]
    exact hlip y' hy' y hy
  obtain ⟨y, hyB, hfix, -, -⟩ := ContractingWith.exists_fixedPoint' hBclosed.isComplete hmaps
    ⟨hK1, hlipK.mapsToRestrict hmaps⟩ h0B (edist_ne_top _ _)
  have hfix' : d.qL 1 (d.T.lvlMap 0 (â + y)) = y := hfix
  -- the point `u = a + y` and its image `w = t(u)`
  set u := â + y with hu
  have huU : u ∈ E.lvlSet d.T.U 1 := (hF1' y hyB).1
  have hur : ‖u‖ < r := (hF1' y hyB).2
  have hur' : ‖u‖ < r' := (hF1 y hyB).2
  have huC : u ∈ E.lvlSet C 1 := (hF1 y hyB).1
  set w := d.T.lvlMap 0 u with hw
  have hwO : E.toBase 1 w ∈ d.T.retract := by
    rw [hw, d.isScPlus.toBase_lvlMap 0 huU]
    exact d.T.apply_mem_retract huU
  have hwC : w ∈ E.lvlSet C 1 :=
    d.T.lvlSet_U_subset_lvlSet_C 1 (d.T.lvlSet_retract_subset 1 hwO)
  have hwr : ‖w‖ < r := by
    have := hδ' huU (by rw [dist_zero_right]; exact hur'.trans_le (min_le_right _ _))
    rwa [ht0, dist_zero_right] at this
  have hqu : d.qL 1 u = y := by
    rw [hu, map_add, d.qL_of_mem_N hâN, d.qL_of_mem_Y hyB.1, zero_add]
  have hwuN : E.toBase 1 (w - u) ∈ d.N := by
    rw [← d.qL_eq_zero_iff, map_sub, hfix', hqu, sub_self]
  have hD : d.T.lvlDeriv 0 0 (w - u) = w - u := d.lvlDeriv_zero_of_mem_N 0 hwuN
  have hest := hmvt u huC w hwC hur hwr
  rw [d.isScPlus.lvlMap_eq_self 0 hwO, hD, ← hw, sub_self, zero_sub, norm_neg] at hest
  have hwu : w = u := by
    have h1 : (1 - θ) * ‖w - u‖ ≤ 0 := by linarith
    have h0 : ‖w - u‖ ≤ 0 := by
      by_contra h
      push Not at h
      have : 0 < (1 - θ) * ‖w - u‖ := mul_pos (by linarith) h
      linarith
    rw [← sub_eq_zero]
    exact norm_le_zero_iff.1 h0
  refine ⟨u, ?_, ?_, ?_, ?_, hur⟩
  · rw [d.T.mem_retract_iff]
    refine ⟨huU, ?_⟩
    rw [← d.isScPlus.toBase_lvlMap 0 huU, ← hw, hwu]
  · rw [hu, map_add, hâa, map_add, d.p_apply_N, d.p_apply_Y _ hyB.1, add_zero]
  · rw [hu, map_add, hâa, add_sub_cancel_left]
    exact hyB.1
  · rw [hu, add_sub_cancel_left]
    exact hyB.2

/-! ### `p(O ∩ W) ⊆ C`: the projections of points of `O` near `0` lie in the partial quadrant -/

/-- **The projection of a point of `O` near `0` lies in `C`** (a step the text omits: the target
`V ⊆ T₀O ∩ C` of `p` must contain `p(u)`): if `‖(1 − p)u‖₁ ≤ κ‖u‖₁` with `κ ≤ 1/2` and
`2‖ι₁‖κ‖lift‖ ≤ ε`, then `|(1 − p)u|₀ ≤ ε|p(u)|₀`, so `p(u) ∈ C ↔ u ∈ C` by the good complement
property, and `u ∈ O ⊆ C`. -/
theorem p_mem_C {u : E 1} (hu : u ∈ E.lvlSet d.T.retract 1) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 1 / 2) (hκ' : 2 * ‖E.toBase 1‖ * κ * ‖d.liftN 1‖ ≤ d.eps)
    (hq : ‖d.qL 1 u‖ ≤ κ * ‖u‖) : (d.p (E.toBase 1 u) : E 0) ∈ C := by
  set n : d.N := d.p (E.toBase 1 u) with hn
  have hy : E.toBase 1 (d.qL 1 u) ∈ d.Y := d.toBase_qL_mem_Y 1 u
  have hdecomp : E.toBase 1 u = (n : E 0) + E.toBase 1 (d.qL 1 u) := by
    rw [d.toBase_qL, hn]; abel
  have hpL : d.pL 1 u = d.liftN 1 n := rfl
  have h1a : ‖d.pL 1 u‖ ≤ ‖d.liftN 1‖ * ‖n‖ := by rw [hpL]; exact (d.liftN 1).le_opNorm n
  have h1 : ‖u‖ ≤ ‖d.liftN 1‖ * ‖n‖ + κ * ‖u‖ := by
    calc ‖u‖ = ‖d.pL 1 u + d.qL 1 u‖ := by rw [add_comm, d.qL_add_pL]
      _ ≤ ‖d.pL 1 u‖ + ‖d.qL 1 u‖ := norm_add_le _ _
      _ ≤ ‖d.liftN 1‖ * ‖n‖ + κ * ‖u‖ := add_le_add h1a hq
  have h2 : ‖u‖ ≤ 2 * ‖d.liftN 1‖ * ‖n‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hκ (norm_nonneg u), norm_nonneg u]
  have h3 : ‖E.toBase 1 (d.qL 1 u)‖ ≤ d.eps * ‖(n : E 0)‖ := by
    rw [norm_coe]
    calc ‖E.toBase 1 (d.qL 1 u)‖ ≤ ‖E.toBase 1‖ * ‖d.qL 1 u‖ := (E.toBase 1).le_opNorm _
      _ ≤ ‖E.toBase 1‖ * (κ * (2 * ‖d.liftN 1‖ * ‖n‖)) := by
          gcongr; exact hq.trans (mul_le_mul_of_nonneg_left h2 hκ0)
      _ = (2 * ‖E.toBase 1‖ * κ * ‖d.liftN 1‖) * ‖n‖ := by ring
      _ ≤ d.eps * ‖n‖ := by gcongr
  have huC : E.toBase 1 u ∈ C :=
    d.T.lvlSet_U_subset_lvlSet_C 1 (d.T.lvlSet_retract_subset 1 hu)
  rw [hdecomp] at huC
  exact (d.eps_spec n.2 hy h3).2 huC

/-! ### The neighbourhoods `W`, `V` and the graph map `Γ` -/

/-- **The conclusion of Proposition 4.1.9 (preprint 4.9) before regularity**: an open `W ∋ 0` in `E`, an open
`V' ∋ 0` in `N` (so that `V = V' ∩ C` is a relatively open neighbourhood of `0` in `N ∩ C`) and the
map `Γ : V → O ∩ W`, `Γ(a) = a + δ(a)`, with `p ∘ Γ = 1` on `V`, `Γ ∘ p = 1` on `O ∩ W`,
`Γ(a) − a ∈ Y`, and `p(O ∩ W) ⊆ V`.  The radius `r` controls the level-`1` size of the points of
`O ∩ W` and of `Γ(V)`: `‖Γ(a)‖₁ < r`, `C₁ ∩ B(0, r) ⊆ U₁`, and `‖Dt(z) − Dt(0)‖_{L(E₁)} ≤ θ₀`
on `C₁ ∩ B(0, r)` (used for the regularity of `Γ`). -/
structure Nbhd (d : GraphData E C) (θ₀ : ℝ) where
  r : ℝ
  r_pos : 0 < r
  ball_subset : E.lvlSet C 1 ∩ ball 0 r ⊆ E.lvlSet d.T.U 1
  deriv_bound : ∀ z ∈ E.lvlSet C 1, ‖z‖ < r → ‖d.T.lvlDeriv 0 z - d.T.lvlDeriv 0 0‖ ≤ θ₀
  W : Set (E 0)
  isOpen_W : IsOpen W
  zero_mem_W : (0 : E 0) ∈ W
  V' : Set d.N
  isOpen_V' : IsOpen V'
  zero_mem_V' : (0 : d.N) ∈ V'
  Γ : d.N → E 0
  Γ_mem : ∀ a ∈ V' ∩ Subtype.val ⁻¹' C, Γ a ∈ d.T.retract
  Γ_mem_W : ∀ a ∈ V' ∩ Subtype.val ⁻¹' C, Γ a ∈ W
  p_Γ : ∀ a ∈ V' ∩ Subtype.val ⁻¹' C, d.p (Γ a) = a
  Γ_sub_mem_Y : ∀ a ∈ V' ∩ Subtype.val ⁻¹' C, Γ a - a ∈ d.Y
  norm_liftOne_Γ_lt : ∀ a ∈ V' ∩ Subtype.val ⁻¹' C, ‖E.liftOne (Γ a)‖ < r
  p_mem_V : ∀ u ∈ d.T.retract ∩ W, d.p u ∈ V' ∩ Subtype.val ⁻¹' C
  Γ_p : ∀ u ∈ d.T.retract ∩ W, Γ (d.p u) = u
  qL_bound : ∀ u ∈ E.lvlSet d.T.retract 1, ∀ u' ∈ E.lvlSet d.T.retract 1, ‖u‖ < r → ‖u'‖ < r →
    ‖d.qL 1 (u' - u)‖ ≤ 1 / 2 * ‖u' - u‖

namespace Nbhd

variable {d} {θ₀ : ℝ} (n : d.Nbhd θ₀)

/-- The relatively open neighbourhood `V = V' ∩ (N ∩ C)` of `0` in `N ∩ C`. -/
def V : Set d.N := n.V' ∩ Subtype.val ⁻¹' C

lemma V_relOpen : ∃ O : Set d.N, IsOpen O ∧ n.V = O ∩ Subtype.val ⁻¹' C :=
  ⟨n.V', n.isOpen_V', rfl⟩

lemma zero_mem_V : (0 : d.N) ∈ n.V :=
  ⟨n.zero_mem_V', by
    change ((0 : d.N) : E 0) ∈ C
    rw [Submodule.coe_zero]
    exact d.T.lvlSet_U_subset_lvlSet_C 0 (d.zero_mem_lvlSet_U 0)⟩

lemma V_subset : n.V ⊆ Subtype.val ⁻¹' C := inter_subset_right

/-- `Γ(V) = O ∩ W`. -/
theorem image_V : n.Γ '' n.V = d.T.retract ∩ n.W := by
  ext u
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨n.Γ_mem a ha, n.Γ_mem_W a ha⟩
  · intro hu
    exact ⟨d.p u, n.p_mem_V u hu, n.Γ_p u hu⟩

lemma Γ_zero : n.Γ 0 = 0 := by
  have h := n.Γ_p 0 ⟨d.zero_mem, n.zero_mem_W⟩
  rwa [map_zero] at h

/-- `p` is injective on `O ∩ W`. -/
theorem injOn_p : InjOn d.p (d.T.retract ∩ n.W) := fun u hu u' hu' h => by
  rw [← n.Γ_p u hu, ← n.Γ_p u' hu', h]

end Nbhd

/-- **Lemmas 4.1.12 and 4.1.13 (preprint 4.11 and 4.12) assembled**: for every `θ₀ > 0` the data `Nbhd` exist.  The constant
`θ` of the contraction is chosen below `θ₀`, below `ε'/(2(‖1 − p‖ + 1)(1 + ε'))` (existence and
uniqueness) and below `ε/(2‖ι₁‖‖lift‖(‖1 − p‖ + 1) + 1)` (so that `p(O ∩ W) ⊆ C`). -/
theorem exists_nbhd {θ₀ : ℝ} (hθ₀ : 0 < θ₀) : Nonempty (d.Nbhd θ₀) := by
  have hε := d.eps_pos
  have hε' := d.eps'_pos
  set cq := ‖d.qL 1‖ with hcq
  set c₁ := ‖E.toBase 1‖ with hc₁
  set cN := ‖d.liftN 1‖ with hcN
  have hcq0 : 0 ≤ cq := norm_nonneg (d.qL 1)
  have hc₁0 : 0 ≤ c₁ := norm_nonneg (E.toBase 1)
  have hcN0 : 0 ≤ cN := norm_nonneg (d.liftN 1)
  -- the constant `θ`
  set θ₁ := d.eps' / (2 * (cq + 1) * (1 + d.eps')) with hθ₁
  set θ₂ := d.eps / (2 * c₁ * cN * (cq + 1) + 1) with hθ₂
  have hθ₁pos : 0 < θ₁ := by positivity
  have hθ₂pos : 0 < θ₂ := by positivity
  set θ := min θ₀ (min θ₁ θ₂) with hθ
  have hθpos : 0 < θ := lt_min hθ₀ (lt_min hθ₁pos hθ₂pos)
  have hθθ₀ : θ ≤ θ₀ := min_le_left _ _
  have hθθ₁ : θ ≤ θ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hθθ₂ : θ ≤ θ₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hA : cq * θ₁ * (1 + d.eps') ≤ d.eps' / 2 := by
    rw [hθ₁, show cq * (d.eps' / (2 * (cq + 1) * (1 + d.eps'))) * (1 + d.eps') =
      d.eps' * cq / (2 * (cq + 1)) from by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hB : cq * θ₁ ≤ 1 / 2 := by
    rw [hθ₁, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hC : θ₁ ≤ 1 / 2 := by
    rw [hθ₁, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hD : 2 * c₁ * (cq * θ₂) * cN ≤ d.eps := by
    rw [hθ₂, show 2 * c₁ * (cq * (d.eps / (2 * c₁ * cN * (cq + 1) + 1))) * cN =
      d.eps * (2 * c₁ * cq * cN) / (2 * c₁ * cN * (cq + 1) + 1) from by field_simp]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hc₁0 hcN0) hcq0, mul_nonneg hc₁0 hcN0]
  have hθlt1 : θ < 1 := by linarith
  have hcqθ : cq * θ ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hθθ₁ hcq0).trans hB
  have hcqθ1 : cq * θ < 1 := by linarith
  have hcqθε : cq * θ * (1 + d.eps') ≤ d.eps' := by
    calc cq * θ * (1 + d.eps') ≤ cq * θ₁ * (1 + d.eps') := by gcongr
      _ ≤ d.eps' / 2 := hA
      _ ≤ d.eps' := by linarith
  have hstep2 : 2 * c₁ * (cq * θ) * cN ≤ d.eps := by
    calc 2 * c₁ * (cq * θ) * cN ≤ 2 * c₁ * (cq * θ₂) * cN := by gcongr
      _ ≤ d.eps := hD
  -- the contraction radius and the graph points
  obtain ⟨r, hr, hsub, hder, hmvt, hqL⟩ := d.exists_contraction_radius 0 hθpos
  obtain ⟨ρ, hρ, hex⟩ := d.exists_graph_point hθpos hθlt1 hcqθ1 hcqθε hr hsub hmvt
  choose! u hu using hex
  -- continuity of the lift `t¹ : U → E₁` at `0`
  have hg0 : d.T.liftOne 0 = 0 := by
    change E.liftOne (d.T 0) = 0
    rw [d.T.apply_eq_self_of_mem_retract d.zero_mem]
    exact (E.liftOne_eq_iff ⟨0, map_zero _⟩).2 (map_zero _)
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.continuousWithinAt_iff.1
    ((d.isScPlus.isScSmooth_liftOne.isSc1.isSc0.continuousOn_base) 0 (d.zero_mem_lvlSet_U 0)) r hr
  -- the radius `ρ'` of `V'`
  set ρ' := min ρ (min (r / (1 + d.eps')) (δ₀ / (c₁ * (1 + d.eps') + 1))) with hρ'
  have hρ'pos : 0 < ρ' := lt_min hρ (lt_min (by positivity) (by positivity))
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  have hρ'r : ρ' ≤ r / (1 + d.eps') := (min_le_right _ _).trans (min_le_left _ _)
  have hρ'δ : ρ' ≤ δ₀ / (c₁ * (1 + d.eps') + 1) := (min_le_right _ _).trans (min_le_right _ _)
  set V' : Set d.N := {a | ‖d.liftN 1 a‖ < ρ'} with hV'
  have hV'open : IsOpen V' :=
    isOpen_lt (continuous_norm.comp (d.liftN 1).continuous) continuous_const
  set W : Set (E 0) := ball 0 δ₀ ∩ d.p ⁻¹' V' with hW
  -- the points `u(a)` for `a ∈ V = V' ∩ C`
  have hu' : ∀ a ∈ V' ∩ Subtype.val ⁻¹' C, E.toBase 1 (u a) ∈ d.T.retract ∧
      d.p (E.toBase 1 (u a)) = a ∧ E.toBase 1 (u a) - a ∈ d.Y ∧
      ‖u a - d.liftN 1 a‖ ≤ d.eps' * ‖d.liftN 1 a‖ ∧ ‖u a‖ < r := fun a ha =>
    hu a ha.2 (ha.1.trans_le hρ'ρ)
  have hnorm_u : ∀ a ∈ V' ∩ Subtype.val ⁻¹' C, ‖u a‖ ≤ (1 + d.eps') * ‖d.liftN 1 a‖ := by
    intro a ha
    calc ‖u a‖ = ‖d.liftN 1 a + (u a - d.liftN 1 a)‖ := by rw [add_sub_cancel]
      _ ≤ ‖d.liftN 1 a‖ + ‖u a - d.liftN 1 a‖ := norm_add_le _ _
      _ ≤ ‖d.liftN 1 a‖ + d.eps' * ‖d.liftN 1 a‖ := by gcongr; exact (hu' a ha).2.2.2.1
      _ = (1 + d.eps') * ‖d.liftN 1 a‖ := by ring
  -- the lift of a point of `O ∩ W` to level `1`
  have hlift : ∀ u₀ ∈ d.T.retract ∩ W, E.toBase 1 (E.liftOne u₀) = u₀ ∧
      E.liftOne u₀ ∈ E.lvlSet d.T.retract 1 ∧ ‖E.liftOne u₀‖ < r := by
    intro u₀ hu₀
    have hU : u₀ ∈ d.T.U := d.T.retract_subset hu₀.1
    have h1 : E.toBase 1 (E.liftOne u₀) = u₀ := by
      have := d.isScPlus.mem_range u₀ hU
      rw [d.T.apply_eq_self_of_mem_retract hu₀.1] at this
      exact E.toBase_liftOne this
    refine ⟨h1, by rw [ScBanach.mem_lvlSet, h1]; exact hu₀.1, ?_⟩
    have := hδ₀' hU (by rw [dist_zero_right]; exact mem_ball_zero_iff.1 hu₀.2.1)
    rw [hg0, dist_zero_right] at this
    have h2 : d.T.liftOne u₀ = E.liftOne u₀ := by
      change E.liftOne (d.T u₀) = E.liftOne u₀
      rw [d.T.apply_eq_self_of_mem_retract hu₀.1]
    rwa [h2] at this
  refine ⟨⟨r, hr, hsub, fun z hz hzr => (hder z hz hzr).trans hθθ₀, W,
    Metric.isOpen_ball.inter (hV'open.preimage d.p.continuous),
    ⟨mem_ball_self hδ₀, by
      change d.p 0 ∈ V'
      rw [map_zero]; change ‖d.liftN 1 0‖ < ρ'; rw [map_zero, norm_zero]; exact hρ'pos⟩,
    V', hV'open, by change ‖d.liftN 1 0‖ < ρ'; rw [map_zero, norm_zero]; exact hρ'pos,
    fun a => E.toBase 1 (u a), fun a ha => (hu' a ha).1, fun a ha => ?_,
    fun a ha => (hu' a ha).2.1, fun a ha => (hu' a ha).2.2.1,
    fun a ha => by rw [E.liftOne_toBase]; exact (hu' a ha).2.2.2.2,
    fun u₀ hu₀ => ?_, fun u₀ hu₀ => ?_, fun u hu u' hu' hur hu'r => ?_⟩⟩
  · -- `Γ(a) ∈ W`
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff]
      have h1 : ‖E.toBase 1 (u a)‖ ≤ c₁ * ((1 + d.eps') * ‖d.liftN 1 a‖) :=
        ((E.toBase 1).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hnorm_u a ha) hc₁0)
      have h2 : ‖d.liftN 1 a‖ ≤ ρ' := ha.1.le
      have h3 : c₁ * (1 + d.eps') * ρ' ≤ δ₀ * (c₁ * (1 + d.eps')) / (c₁ * (1 + d.eps') + 1) := by
        calc c₁ * (1 + d.eps') * ρ' ≤ c₁ * (1 + d.eps') * (δ₀ / (c₁ * (1 + d.eps') + 1)) := by
              gcongr
          _ = δ₀ * (c₁ * (1 + d.eps')) / (c₁ * (1 + d.eps') + 1) := by ring
      have h4 : δ₀ * (c₁ * (1 + d.eps')) / (c₁ * (1 + d.eps') + 1) < δ₀ := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      calc ‖E.toBase 1 (u a)‖ ≤ c₁ * ((1 + d.eps') * ‖d.liftN 1 a‖) := h1
        _ ≤ c₁ * ((1 + d.eps') * ρ') := by gcongr
        _ = c₁ * (1 + d.eps') * ρ' := by ring
        _ < δ₀ := h3.trans_lt h4
    · change d.p (E.toBase 1 (u a)) ∈ V'
      rw [(hu' a ha).2.1]; exact ha.1
  · -- `p(u₀) ∈ V`
    obtain ⟨h1, h2, h3⟩ := hlift u₀ hu₀
    refine ⟨hu₀.2.2, ?_⟩
    change (d.p u₀ : E 0) ∈ C
    rw [← h1]
    have hq := hqL 0 (d.zero_mem_lvlSet_retract 1) (E.liftOne u₀) h2
      (by rw [norm_zero]; exact hr) h3
    simp only [sub_zero] at hq
    exact d.p_mem_C h2 (by positivity) hcqθ (by rw [← hc₁, ← hcN]; exact hstep2) hq
  · -- `Γ(p(u₀)) = u₀`
    obtain ⟨h1, h2, h3⟩ := hlift u₀ hu₀
    have ha : d.p u₀ ∈ V' ∩ Subtype.val ⁻¹' C := by
      refine ⟨hu₀.2.2, ?_⟩
      change (d.p u₀ : E 0) ∈ C
      rw [← h1]
      have hq := hqL 0 (d.zero_mem_lvlSet_retract 1) (E.liftOne u₀) h2
        (by rw [norm_zero]; exact hr) h3
      simp only [sub_zero] at hq
      exact d.p_mem_C h2 (by positivity) hcqθ (by rw [← hc₁, ← hcN]; exact hstep2) hq
    obtain ⟨hO, hp, -, -, hr'⟩ := hu' _ ha
    have hq := hqL 0 (d.zero_mem_lvlSet_retract 1) (u (d.p u₀)) hO
      (by rw [norm_zero]; exact hr) hr'
    have hq' := hqL _ h2 _ hO h3 hr'
    have heq : u (d.p u₀) = E.liftOne u₀ := d.eq_of_p_eq hcqθ1 hq' (by rw [h1, hp])
    change E.toBase 1 (u (d.p u₀)) = u₀
    rw [heq, h1]
  · -- the contraction estimate with constant `1/2`
    calc ‖d.qL 1 (u' - u)‖ ≤ ‖d.qL 1‖ * θ * ‖u' - u‖ := hqL u hu u' hu' hur hu'r
      _ ≤ 1 / 2 * ‖u' - u‖ := by gcongr

end GraphData

/-! ### The inverse of a projection on a retract is Lipschitz and differentiable

The abstract step behind the regularity of `Γ = (p|_{O ∩ W})⁻¹`: on a convex set `S` in a normed
space, let `s` be differentiable at `u₀` within `S` with `‖(s z' − s z) − Ds(u₀)(z' − z)‖ ≤
θ‖z' − z‖` on `S`, let `O_S = {s = 1}`, and let `q : X → Z`, `B : Z → X` be continuous linear with
`q ∘ B = 1` and `(1 − B q) ∘ Ds(u₀) = 0`.  If `θ‖1 − Bq‖ ≤ 1/2`, then `‖u' − u‖ ≤ 2‖B‖‖q(u' − u)‖`
on `O_S` and every continuous right inverse `Γ` of `q` with values in `O_S` is differentiable
at `z₀ = q(u₀)` with derivative `B`. -/

section InverseProjection

variable {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z]

/-- The Lipschitz estimate `‖u' − u‖ ≤ 2‖B‖‖q(u' − u)‖` for fixed points `u, u'` of `s`. -/
theorem norm_sub_le_of_projection {S : Set X} {s : X → X} {D₀ : X →L[ℝ] X} {θ : ℝ}
    (hmvt : ∀ z ∈ S, ∀ z' ∈ S, ‖(s z' - s z) - D₀ (z' - z)‖ ≤ θ * ‖z' - z‖)
    (q : X →L[ℝ] Z) (B : Z →L[ℝ] X) (hπD : ∀ x, D₀ x - B (q (D₀ x)) = 0)
    (hθ : θ * ‖ContinuousLinearMap.id ℝ X - B.comp q‖ ≤ 1 / 2)
    {u u' : X} (hu : u ∈ S) (hu' : u' ∈ S) (hsu : s u = u) (hsu' : s u' = u') :
    ‖u' - u‖ ≤ 2 * ‖B‖ * ‖q (u' - u)‖ := by
  set π := ContinuousLinearMap.id ℝ X - B.comp q with hπ
  have hπapply : ∀ x, π x = x - B (q x) := fun x => rfl
  have hπD' : ∀ x, π (D₀ x) = 0 := fun x => by rw [hπapply]; exact hπD x
  have h := hmvt u hu u' hu'
  rw [hsu, hsu'] at h
  have hπ1 : π (u' - u) = π ((u' - u) - D₀ (u' - u)) := by
    rw [map_sub π (u' - u) (D₀ (u' - u)), hπD', sub_zero]
  have hπ2 : ‖π (u' - u)‖ ≤ 1 / 2 * ‖u' - u‖ := by
    rw [hπ1]
    calc ‖π ((u' - u) - D₀ (u' - u))‖ ≤ ‖π‖ * ‖(u' - u) - D₀ (u' - u)‖ := π.le_opNorm _
      _ ≤ ‖π‖ * (θ * ‖u' - u‖) := by gcongr
      _ = (θ * ‖π‖) * ‖u' - u‖ := by ring
      _ ≤ 1 / 2 * ‖u' - u‖ := by gcongr
  have hdecomp : u' - u = B (q (u' - u)) + π (u' - u) := by rw [hπapply]; abel
  have : ‖u' - u‖ ≤ ‖B‖ * ‖q (u' - u)‖ + 1 / 2 * ‖u' - u‖ := by
    calc ‖u' - u‖ = ‖B (q (u' - u)) + π (u' - u)‖ := by rw [← hdecomp]
      _ ≤ ‖B (q (u' - u))‖ + ‖π (u' - u)‖ := norm_add_le _ _
      _ ≤ ‖B‖ * ‖q (u' - u)‖ + 1 / 2 * ‖u' - u‖ := add_le_add (B.le_opNorm _) hπ2
  linarith

/-- The differentiability of a continuous right inverse `Γ` of `q` with values in the fixed points
of `s`: `DΓ(z₀) = B`. -/
theorem hasFDerivWithinAt_of_projection {S : Set X} {s : X → X} {D₀ : X →L[ℝ] X} {θ : ℝ}
    {u₀ : X} (hmvt : ∀ z ∈ S, ∀ z' ∈ S, ‖(s z' - s z) - D₀ (z' - z)‖ ≤ θ * ‖z' - z‖)
    (hdiff : HasFDerivWithinAt s D₀ S u₀)
    (q : X →L[ℝ] Z) (B : Z →L[ℝ] X) (hπD : ∀ x, D₀ x - B (q (D₀ x)) = 0)
    (hθ : θ * ‖ContinuousLinearMap.id ℝ X - B.comp q‖ ≤ 1 / 2)
    (hu₀ : u₀ ∈ S) (hsu₀ : s u₀ = u₀) {Γ : Z → X} {W : Set Z} {z₀ : Z} (hz₀ : z₀ ∈ W)
    (hΓ₀ : Γ z₀ = u₀) (hΓ : ∀ z ∈ W, Γ z ∈ S ∧ s (Γ z) = Γ z ∧ q (Γ z) = z)
    (hcont : ContinuousWithinAt Γ W z₀) : HasFDerivWithinAt Γ B W z₀ := by
  set π := ContinuousLinearMap.id ℝ X - B.comp q with hπ
  have hπapply : ∀ x, π x = x - B (q x) := fun x => rfl
  have hπD' : ∀ x, π (D₀ x) = 0 := fun x => by rw [hπapply]; exact hπD x
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  set c' := c / (2 * ‖π‖ * ‖B‖ + 1) with hc'
  have hc'pos : 0 < c' := by positivity
  have h1 := hasFDerivWithinAt_iff_isLittleO.1 hdiff
  rw [Asymptotics.isLittleO_iff] at h1
  have h2 := h1 hc'pos
  have htend : Tendsto Γ (𝓝[W] z₀) (𝓝[S] u₀) := by
    have := hcont.tendsto_nhdsWithin fun z hz => (hΓ z hz).1
    rwa [hΓ₀] at this
  have hqu₀ : q u₀ = z₀ := by rw [← hΓ₀]; exact (hΓ z₀ hz₀).2.2
  filter_upwards [htend.eventually h2, self_mem_nhdsWithin] with z hz hzW
  obtain ⟨hzS, hsz, hqz⟩ := hΓ z hzW
  rw [hsz, hsu₀] at hz
  have hlip := norm_sub_le_of_projection hmvt q B hπD hθ hu₀ hzS hsu₀ hsz
  have hq : q (Γ z - u₀) = z - z₀ := by rw [map_sub, hqz, hqu₀]
  have hkey : Γ z - Γ z₀ - B (z - z₀) = π (Γ z - u₀) := by
    rw [hπapply, hΓ₀, hq]
  have hπ1 : π (Γ z - u₀) = π ((Γ z - u₀) - D₀ (Γ z - u₀)) := by
    rw [map_sub π (Γ z - u₀) (D₀ (Γ z - u₀)), hπD', sub_zero]
  have hcc : 2 * ‖π‖ * ‖B‖ * c' ≤ c := by
    calc 2 * ‖π‖ * ‖B‖ * c' = c * (2 * ‖π‖ * ‖B‖ / (2 * ‖π‖ * ‖B‖ + 1)) := by rw [hc']; ring
      _ ≤ c * 1 := by
          gcongr
          exact div_le_one_of_le₀ (by linarith) (by positivity)
      _ = c := mul_one c
  rw [hkey, hπ1]
  calc ‖π ((Γ z - u₀) - D₀ (Γ z - u₀))‖ ≤ ‖π‖ * ‖(Γ z - u₀) - D₀ (Γ z - u₀)‖ := π.le_opNorm _
    _ ≤ ‖π‖ * (c' * ‖Γ z - u₀‖) := by gcongr
    _ ≤ ‖π‖ * (c' * (2 * ‖B‖ * ‖q (Γ z - u₀)‖)) := by gcongr
    _ = (2 * ‖π‖ * ‖B‖ * c') * ‖z - z₀‖ := by rw [hq]; ring
    _ ≤ c * ‖z - z₀‖ := by gcongr

end InverseProjection

/-! ### The frame `B_u = Dt(u)|_N ∘ (p ∘ Dt(u)|_N)⁻¹` at a point `u ∈ O` near `0`

For `u ∈ O₁` with `‖Dt(u) − Dt(0)‖_{L(E₁)} ≤ θ₀`, `θ₀` small: `A(u) = p ∘ Dt(u)|_N : N → N` is
invertible (it is `1 + O(θ₀)`), and `T_uO ∩ Y = 0`.  The frame `B_u = Dt(u) ∘ (A(u))⁻¹ : N → T_uO`
is the inverse of `p|_{T_uO}`, and `DΓ(a) = B_{Γ(a)}` (the "frame formula"). -/

namespace GraphData

variable {E : ScBanach} {C : Set (E 0)} (d : GraphData E C)

/-- `A(u) = p ∘ Dt(u)|_N : N → N`. -/
def A (u : E 1) : d.N →L[ℝ] d.N := d.p.comp ((scDeriv d.T.U d.T u).comp d.N.subtypeL)

lemma A_apply (u : E 1) (n : d.N) : (d.A u n : E 0) = d.p (scDeriv d.T.U d.T u n) := rfl

/-- `M(u) = A(u)⁻¹` (the junk value of `ContinuousLinearMap.inverse` if `A(u)` is not
invertible). -/
def M (u : E 1) : d.N →L[ℝ] d.N := (d.A u).inverse

/-- The frame `B_u = Dt(u) ∘ M(u) : N → E`. -/
def frame (u : E 1) : d.N →L[ℝ] E 0 := (scDeriv d.T.U d.T u).comp (d.N.subtypeL.comp (d.M u))

lemma frame_apply (u : E 1) (n : d.N) : d.frame u n = scDeriv d.T.U d.T u (d.M u n) := rfl

lemma liftN_shift_inclK (j k : ℕ) (n' : d.N) :
    E.shift.inclK j k (d.liftN (j + k + 1) n') = d.liftN (j + 1) n' := by
  symm
  rw [d.liftN_eq_iff, E.shift_toBase, E.shift.toBase_inclK, ← E.shift_toBase, d.toBase_liftN]

/-- The frame on level `k + 1`, at a lift `x ∈ O_{k+1}` of `u`. -/
def frameL (k : ℕ) (x : E (k + 1)) : d.N →L[ℝ] E (k + 1) :=
  (d.T.lvlDeriv k x).comp ((d.liftN (k + 1)).comp (d.M (E.shift.toBase k x)))

lemma frameL_apply (k : ℕ) (x : E (k + 1)) (n : d.N) :
    d.frameL k x n = d.T.lvlDeriv k x (d.liftN (k + 1) (d.M (E.shift.toBase k x) n)) := rfl

lemma toBase_frameL (k : ℕ) {x : E (k + 1)} (hx : x ∈ E.lvlSet d.T.U (k + 1)) (n : d.N) :
    E.toBase (k + 1) (d.frameL k x n) = d.frame (E.shift.toBase k x) n := by
  rw [frameL_apply, d.isScPlus.toBase_lvlDeriv k hx, d.toBase_liftN, frame_apply]

/-- `Dt(u) n − n = ι₁ (Dt₁(u) − Dt₁(0)) (lift n)` for `n ∈ N`. -/
lemma scDeriv_sub_eq {u : E 1} (hu : u ∈ E.lvlSet d.T.U 1) (n : d.N) :
    scDeriv d.T.U d.T u n - n =
      E.toBase 1 ((d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0) (d.liftN 1 n)) := by
  rw [sub_apply, map_sub, d.isScPlus.toBase_lvlDeriv 0 hu,
    d.isScPlus.toBase_lvlDeriv 0 (d.zero_mem_lvlSet_U 1), d.toBase_liftN]
  change scDeriv d.T.U d.T u n - n = scDeriv d.T.U d.T u n - scDeriv d.T.U d.T 0 n
  rw [d.scDeriv_zero_of_mem n.2]

/-- The smallness condition on `θ₀` for the frame: `‖p‖‖ι₁‖‖lift‖θ₀ ≤ 1/2` and `‖1 − p‖θ₀ < 1`. -/
def FrameSmall (θ₀ : ℝ) : Prop :=
  ‖d.p‖ * ‖E.toBase 1‖ * ‖d.liftN 1‖ * θ₀ ≤ 1 / 2 ∧ ‖d.qL 1‖ * θ₀ < 1

lemma exists_frameSmall : ∃ θ₀ > 0, d.FrameSmall θ₀ := by
  refine ⟨1 / (2 * (‖d.p‖ * ‖E.toBase 1‖ * ‖d.liftN 1‖ + ‖d.qL 1‖ + 1)), by positivity, ?_, ?_⟩
  · rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [norm_nonneg d.p, norm_nonneg (E.toBase 1), norm_nonneg (d.liftN 1),
      norm_nonneg (d.qL 1), mul_nonneg (mul_nonneg (norm_nonneg d.p) (norm_nonneg (E.toBase 1)))
        (norm_nonneg (d.liftN 1))]
  · rw [mul_one_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg d.p, norm_nonneg (E.toBase 1), norm_nonneg (d.liftN 1),
      norm_nonneg (d.qL 1), mul_nonneg (mul_nonneg (norm_nonneg d.p) (norm_nonneg (E.toBase 1)))
        (norm_nonneg (d.liftN 1))]

variable {d}

/-- **(L1)** `A(u)` is injective: `‖A(u)n − n‖ ≤ ½‖n‖`. -/
theorem A_injective {θ₀ : ℝ} (hθ₀ : d.FrameSmall θ₀) {u : E 1} (hu : u ∈ E.lvlSet d.T.U 1)
    (hder : ‖d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0‖ ≤ θ₀) : Function.Injective (d.A u) := by
  have hbound : ∀ n : d.N, ‖d.A u n - n‖ ≤ 1 / 2 * ‖n‖ := by
    intro n
    have h1 : (d.A u n - n : d.N) = d.p (scDeriv d.T.U d.T u n - n) := by
      rw [map_sub, d.p_apply_N]; rfl
    rw [h1, d.scDeriv_sub_eq hu n]
    have hθ0 : 0 ≤ θ₀ := le_trans (norm_nonneg _) hder
    calc ‖d.p (E.toBase 1 ((d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0) (d.liftN 1 n)))‖
        ≤ ‖d.p‖ * ‖E.toBase 1 ((d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0) (d.liftN 1 n))‖ :=
          d.p.le_opNorm _
      _ ≤ ‖d.p‖ * (‖E.toBase 1‖ * ‖(d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0) (d.liftN 1 n)‖) := by
          gcongr; exact (E.toBase 1).le_opNorm _
      _ ≤ ‖d.p‖ * (‖E.toBase 1‖ * (θ₀ * ‖d.liftN 1 n‖)) := by
          gcongr
          exact ((d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right hder (norm_nonneg _))
      _ ≤ ‖d.p‖ * (‖E.toBase 1‖ * (θ₀ * (‖d.liftN 1‖ * ‖n‖))) := by
          gcongr; exact (d.liftN 1).le_opNorm n
      _ = (‖d.p‖ * ‖E.toBase 1‖ * ‖d.liftN 1‖ * θ₀) * ‖n‖ := by ring
      _ ≤ 1 / 2 * ‖n‖ := by gcongr; exact hθ₀.1
  intro n n' h
  have h2 := hbound (n - n')
  rw [map_sub, h, sub_self, zero_sub, norm_neg] at h2
  have h3 : ‖n - n'‖ ≤ 0 := by linarith
  rw [← sub_eq_zero]
  exact norm_le_zero_iff.1 h3

/-- `A(u)` as a continuous linear equivalence (finite dimension: injective ⇒ bijective). -/
def Aeq {θ₀ : ℝ} (hθ₀ : d.FrameSmall θ₀) {u : E 1} (hu : u ∈ E.lvlSet d.T.U 1)
    (hder : ‖d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0‖ ≤ θ₀) : d.N ≃L[ℝ] d.N :=
  ContinuousLinearEquiv.ofBijective (d.A u) (LinearMap.ker_eq_bot.2 (A_injective hθ₀ hu hder))
    (LinearMap.range_eq_top.2 (LinearMap.injective_iff_surjective.1 (A_injective hθ₀ hu hder)))

lemma coe_Aeq {θ₀ : ℝ} (hθ₀ : d.FrameSmall θ₀) {u : E 1} (hu : u ∈ E.lvlSet d.T.U 1)
    (hder : ‖d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0‖ ≤ θ₀) :
    (Aeq hθ₀ hu hder : d.N →L[ℝ] d.N) = d.A u := rfl

lemma M_eq_symm {θ₀ : ℝ} (hθ₀ : d.FrameSmall θ₀) {u : E 1} (hu : u ∈ E.lvlSet d.T.U 1)
    (hder : ‖d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0‖ ≤ θ₀) :
    d.M u = ((Aeq hθ₀ hu hder).symm : d.N →L[ℝ] d.N) := by
  rw [M, ← coe_Aeq hθ₀ hu hder, ContinuousLinearMap.inverse_equiv]

/-- `A(u) ∘ M(u) = 1`. -/
theorem A_M {θ₀ : ℝ} (hθ₀ : d.FrameSmall θ₀) {u : E 1} (hu : u ∈ E.lvlSet d.T.U 1)
    (hder : ‖d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0‖ ≤ θ₀) (n : d.N) : d.A u (d.M u n) = n := by
  rw [M_eq_symm hθ₀ hu hder]
  exact (Aeq hθ₀ hu hder).apply_symm_apply n

/-- `p ∘ B_u = 1`. -/
theorem p_frame {θ₀ : ℝ} (hθ₀ : d.FrameSmall θ₀) {u : E 1} (hu : u ∈ E.lvlSet d.T.U 1)
    (hder : ‖d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0‖ ≤ θ₀) (n : d.N) : d.p (d.frame u n) = n :=
  A_M hθ₀ hu hder n

/-- **(L2)** `T_uO ∩ Y = 0`: a vector `v ∈ Y` with `Dt(u)v = v` vanishes (on level `1`,
`v = (1 − p)v = (1 − p)(Dt(u) − Dt(0))v`). -/
theorem eq_zero_of_mem_Y_of_scDeriv_eq {θ₀ : ℝ} (hθ₀ : d.FrameSmall θ₀) {u : E 1}
    (hu : u ∈ E.lvlSet d.T.U 1) (hder : ‖d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0‖ ≤ θ₀) {w : E 0}
    (hY : scDeriv d.T.U d.T u w ∈ d.Y) (hfix : scDeriv d.T.U d.T u (scDeriv d.T.U d.T u w) =
      scDeriv d.T.U d.T u w) : scDeriv d.T.U d.T u w = 0 := by
  set vv : E 1 := d.T.liftDeriv u w with hvv
  have hvvv : E.toBase 1 vv = scDeriv d.T.U d.T u w := d.isScPlus.toBase_liftDeriv hu w
  have hDvv : d.T.lvlDeriv 0 u vv = vv := by
    apply E.toBase_injective 1
    rw [d.isScPlus.toBase_lvlDeriv 0 hu, hvvv]
    exact hfix
  have hq : d.qL 1 vv = vv := d.qL_of_mem_Y (by rw [hvvv]; exact hY)
  have hvv' : vv = d.qL 1 ((d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0) vv) := by
    rw [sub_apply, map_sub, d.qL_lvlDeriv_zero, sub_zero, hDvv, hq]
  have hest : ‖vv‖ ≤ (‖d.qL 1‖ * θ₀) * ‖vv‖ := by
    calc ‖vv‖ = ‖d.qL 1 ((d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0) vv)‖ := by rw [← hvv']
      _ ≤ ‖d.qL 1‖ * ‖(d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0) vv‖ := (d.qL 1).le_opNorm _
      _ ≤ ‖d.qL 1‖ * (θ₀ * ‖vv‖) := by
          gcongr
          exact ((d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right hder (norm_nonneg _))
      _ = (‖d.qL 1‖ * θ₀) * ‖vv‖ := by ring
  have hvv0 : vv = 0 := by
    have h1 : (1 - ‖d.qL 1‖ * θ₀) * ‖vv‖ ≤ 0 := by linarith
    have h0 : ‖vv‖ ≤ 0 := by
      by_contra h
      push Not at h
      have : 0 < (1 - ‖d.qL 1‖ * θ₀) * ‖vv‖ := mul_pos (by linarith [hθ₀.2]) h
      linarith
    exact norm_le_zero_iff.1 h0
  rw [← hvvv, hvv0, map_zero]

/-- `(1 − B_u p) ∘ Dt(u) = 0` for `u ∈ O₁`: `Dt(u)x − B_u(p(Dt(u)x))` lies in `T_uO ∩ Y`. -/
theorem scDeriv_sub_frame {θ₀ : ℝ} (hθ₀ : d.FrameSmall θ₀) {u : E 1}
    (hu : u ∈ E.lvlSet d.T.retract 1) (hder : ‖d.T.lvlDeriv 0 u - d.T.lvlDeriv 0 0‖ ≤ θ₀)
    (x : E 0) : scDeriv d.T.U d.T u x - d.frame u (d.p (scDeriv d.T.U d.T u x)) = 0 := by
  have huU : u ∈ E.lvlSet d.T.U 1 := d.T.lvlSet_retract_subset 1 hu
  have hidem : ∀ y, scDeriv d.T.U d.T u (scDeriv d.T.U d.T u y) = scDeriv d.T.U d.T u y :=
    fun y => congrArg (fun L : E 0 →L[ℝ] E 0 => L y) (d.T.scDeriv_comp_self hu)
  set n := d.p (scDeriv d.T.U d.T u x) with hn
  -- the difference is `Dt(u)` of `x − M(u) n`
  have hdiff : scDeriv d.T.U d.T u x - d.frame u n = scDeriv d.T.U d.T u (x - d.M u n) := by
    rw [frame_apply, map_sub]
  rw [hdiff]
  apply eq_zero_of_mem_Y_of_scDeriv_eq hθ₀ huU hder
  · rw [d.mem_Y_iff, ← hdiff, map_sub, ← hn, p_frame hθ₀ huU hder, sub_self]
  · exact hidem _

/-- `Dt(u) ∘ B_u = B_u`. -/
theorem scDeriv_frame {u : E 1} (hu : u ∈ E.lvlSet d.T.retract 1) (n : d.N) :
    scDeriv d.T.U d.T u (d.frame u n) = d.frame u n :=
  congrArg (fun L : E 0 →L[ℝ] E 0 => L (d.M u n)) (d.T.scDeriv_comp_self hu)

/-- The level-`(k+1)` frame at `x ∈ O_{k+1}`: `q ∘ B = 1` for `q = p ∘ ι_{k+1}`. -/
theorem p_toBase_frameL {θ₀ : ℝ} (hθ₀ : d.FrameSmall θ₀) {k : ℕ} {x : E (k + 1)}
    (hx : x ∈ E.lvlSet d.T.retract (k + 1))
    (hder : ‖d.T.lvlDeriv 0 (E.shift.toBase k x) - d.T.lvlDeriv 0 0‖ ≤ θ₀) (n : d.N) :
    d.p (E.toBase (k + 1) (d.frameL k x n)) = n := by
  have hxU : x ∈ E.lvlSet d.T.U (k + 1) := d.T.lvlSet_retract_subset (k + 1) hx
  have hu : E.shift.toBase k x ∈ E.lvlSet d.T.U 1 := E.mem_lvlSet_shift_toBase.2 hxU
  rw [d.toBase_frameL k hxU, p_frame hθ₀ hu hder]

/-- `(1 − B q) ∘ Dt_{k+1}(x) = 0` on level `k + 1`. -/
theorem lvlDeriv_sub_frameL {θ₀ : ℝ} (hθ₀ : d.FrameSmall θ₀) {k : ℕ} {x : E (k + 1)}
    (hx : x ∈ E.lvlSet d.T.retract (k + 1))
    (hder : ‖d.T.lvlDeriv 0 (E.shift.toBase k x) - d.T.lvlDeriv 0 0‖ ≤ θ₀) (v : E (k + 1)) :
    d.T.lvlDeriv k x v - d.frameL k x (d.p (E.toBase (k + 1) (d.T.lvlDeriv k x v))) = 0 := by
  have hxU : x ∈ E.lvlSet d.T.U (k + 1) := d.T.lvlSet_retract_subset (k + 1) hx
  have hu : E.shift.toBase k x ∈ E.lvlSet d.T.retract 1 := by
    rw [ScBanach.mem_lvlSet, ← E.shift_toBase]; exact hx
  apply E.toBase_injective (k + 1)
  rw [map_sub, d.toBase_frameL k hxU, d.isScPlus.toBase_lvlDeriv k hxU, map_zero]
  exact scDeriv_sub_frame hθ₀ hu hder _

/-! ### The lifts `Γ_m : V → E_m` and their continuity -/

namespace Nbhd

variable {θ₀ : ℝ} (n : d.Nbhd θ₀)

/-- `(V, N ∩ C, N)` is a local model: `N ∩ C` is a partial quadrant in `N` (Proposition 3.1.25 (preprint 3.22))
and `V` is relatively open in it. -/
theorem V_isRelOpenInQuadrant :
    IsRelOpenInQuadrant (ScBanach.const d.N) (Subtype.val ⁻¹' C) n.V :=
  ⟨proposition_3_1_25 d.T.relOpen.isPartialQuadrant d.goodPosition, n.V_relOpen⟩

theorem isScDomain_V : IsScDomain (ScBanach.const d.N) n.V := n.V_isRelOpenInQuadrant.isScDomain

theorem uniqueDiffOn_V : UniqueDiffOn ℝ n.V := n.isScDomain_V.uniqueDiffWithinAt 0

/-- The lift `Γ_m : V → E_m` of `Γ` (`Γ(V) ⊆ O ⊆ E_∞`; a junk value off `V`). -/
def Γ_lvl (m : ℕ) (a : d.N) : E m := Function.invFun (E.toBase m) (n.Γ a)

lemma Γ_mem_smooth {a : d.N} (ha : a ∈ n.V) : n.Γ a ∈ E.smooth :=
  lemma_4_1_7_i d.isScPlus (n.Γ_mem a ha)

lemma toBase_Γ_lvl (m : ℕ) {a : d.N} (ha : a ∈ n.V) : E.toBase m (n.Γ_lvl m a) = n.Γ a :=
  Function.invFun_eq ((ScScale.mem_smooth_iff _).1 (n.Γ_mem_smooth ha) m)

lemma Γ_lvl_eq_iff {m : ℕ} {a : d.N} (ha : a ∈ n.V) {v : E m} :
    n.Γ_lvl m a = v ↔ E.toBase m v = n.Γ a := by
  constructor
  · rintro rfl; exact n.toBase_Γ_lvl m ha
  · intro h; apply E.toBase_injective m; rw [n.toBase_Γ_lvl m ha, h]

lemma levelMap_Γ_eq (m : ℕ) (a : d.N) :
    levelMap (E := ScBanach.const d.N) (F := E) n.Γ m a = n.Γ_lvl m a := by
  change Function.invFun (E.toBase m) (n.Γ ((ScBanach.const d.N).toBase m a)) = _
  rw [ScBanach.const_toBase]; rfl

lemma Γ_lvl_zero (a : d.N) : n.Γ_lvl 0 a = n.Γ a :=
  Function.leftInverse_invFun (E.toBase_injective 0) (n.Γ a)

lemma Γ_lvl_one (a : d.N) : n.Γ_lvl 1 a = E.liftOne (n.Γ a) := rfl

lemma Γ_lvl_mem_retract (m : ℕ) {a : d.N} (ha : a ∈ n.V) :
    n.Γ_lvl m a ∈ E.lvlSet d.T.retract m := by
  rw [ScBanach.mem_lvlSet, n.toBase_Γ_lvl m ha]; exact n.Γ_mem a ha

lemma Γ_lvl_mem_U (m : ℕ) {a : d.N} (ha : a ∈ n.V) : n.Γ_lvl m a ∈ E.lvlSet d.T.U m :=
  d.T.lvlSet_retract_subset m (n.Γ_lvl_mem_retract m ha)

lemma Γ_lvl_mem_C (m : ℕ) {a : d.N} (ha : a ∈ n.V) : n.Γ_lvl m a ∈ E.lvlSet C m :=
  d.T.lvlSet_U_subset_lvlSet_C m (n.Γ_lvl_mem_U m ha)

lemma norm_Γ_lvl_one_lt {a : d.N} (ha : a ∈ n.V) : ‖n.Γ_lvl 1 a‖ < n.r := by
  rw [Γ_lvl_one]; exact n.norm_liftOne_Γ_lt a ha

lemma shift_toBase_Γ_lvl (k : ℕ) {a : d.N} (ha : a ∈ n.V) :
    E.shift.toBase k (n.Γ_lvl (k + 1) a) = n.Γ_lvl 1 a :=
  ((n.Γ_lvl_eq_iff ha).2 (by rw [← E.shift_toBase, n.toBase_Γ_lvl _ ha])).symm

lemma shift_inclK_Γ_lvl (j k : ℕ) {a : d.N} (ha : a ∈ n.V) :
    E.shift.inclK j k (n.Γ_lvl (j + k + 1) a) = n.Γ_lvl (j + 1) a :=
  ((n.Γ_lvl_eq_iff ha).2 (by
    rw [E.shift_toBase, E.shift.toBase_inclK, ← E.shift_toBase, n.toBase_Γ_lvl _ ha])).symm

lemma deriv_bound_Γ (k : ℕ) {a : d.N} (ha : a ∈ n.V) :
    ‖d.T.lvlDeriv 0 (E.shift.toBase k (n.Γ_lvl (k + 1) a)) - d.T.lvlDeriv 0 0‖ ≤ θ₀ := by
  rw [n.shift_toBase_Γ_lvl k ha]
  exact n.deriv_bound _ (n.Γ_lvl_mem_C 1 ha) (n.norm_Γ_lvl_one_lt ha)

/-- `Γ₁` is Lipschitz on `V`: from the contraction estimate `‖(1 − p)(u' − u)‖₁ ≤ ½‖u' − u‖₁`
and `p(u' − u) = a' − a`. -/
theorem norm_Γ_lvl_one_sub_le {a a' : d.N} (ha : a ∈ n.V) (ha' : a' ∈ n.V) :
    ‖n.Γ_lvl 1 a' - n.Γ_lvl 1 a‖ ≤ 2 * ‖d.liftN 1‖ * ‖a' - a‖ := by
  set u := n.Γ_lvl 1 a with hu
  set u' := n.Γ_lvl 1 a' with hu'
  have hq := n.qL_bound u (n.Γ_lvl_mem_retract 1 ha) u' (n.Γ_lvl_mem_retract 1 ha')
    (n.norm_Γ_lvl_one_lt ha) (n.norm_Γ_lvl_one_lt ha')
  have hpL : d.pL 1 (u' - u) = d.liftN 1 (a' - a) := by
    change d.liftN 1 (d.p (E.toBase 1 (u' - u))) = _
    rw [map_sub, hu, hu', n.toBase_Γ_lvl 1 ha, n.toBase_Γ_lvl 1 ha', map_sub, n.p_Γ a ha,
      n.p_Γ a' ha']
  have h1 : ‖u' - u‖ ≤ ‖d.liftN 1‖ * ‖a' - a‖ + 1 / 2 * ‖u' - u‖ := by
    calc ‖u' - u‖ = ‖d.pL 1 (u' - u) + d.qL 1 (u' - u)‖ := by rw [add_comm, d.qL_add_pL]
      _ ≤ ‖d.pL 1 (u' - u)‖ + ‖d.qL 1 (u' - u)‖ := norm_add_le _ _
      _ ≤ ‖d.liftN 1‖ * ‖a' - a‖ + 1 / 2 * ‖u' - u‖ := by
          gcongr
          rw [hpL]; exact (d.liftN 1).le_opNorm _
  linarith

theorem continuousOn_Γ_lvl_one : ContinuousOn (n.Γ_lvl 1) n.V := by
  refine LipschitzOnWith.continuousOn (K := ⟨2 * ‖d.liftN 1‖, by positivity⟩) ?_
  refine LipschitzOnWith.of_dist_le_mul fun a ha a' ha' => ?_
  rw [dist_eq_norm, dist_eq_norm]
  exact n.norm_Γ_lvl_one_sub_le ha' ha

/-- `Γ_{k+1} = t ∘ Γ_k` with `t : U_k → E_{k+1}` the sc⁺-lift (`Γ(a) = t(Γ(a))`). -/
theorem Γ_lvl_succ (k : ℕ) {a : d.N} (ha : a ∈ n.V) :
    n.Γ_lvl (k + 1) a = levelMap (E := E) (F := E.shift) d.T.liftOne k (n.Γ_lvl k a) := by
  rw [n.Γ_lvl_eq_iff ha, E.shift_toBase,
    d.isScPlus.isScSmooth_liftOne.isSc1.isSc0.toBase_levelMap (n.Γ_lvl_mem_U k ha),
    n.toBase_Γ_lvl k ha]
  change E.toBase 1 (E.liftOne (d.T (n.Γ a))) = n.Γ a
  rw [d.T.apply_eq_self_of_mem_retract (n.Γ_mem a ha)]
  exact E.toBase_liftOne ((ScScale.mem_smooth_iff _).1 (n.Γ_mem_smooth ha) 1)

/-- `Γ` is continuous into every level `E_m` on `V` (the sc⁺-lift `t : U_k → E_{k+1}` is
continuous). -/
theorem continuousOn_Γ_lvl (m : ℕ) : ContinuousOn (n.Γ_lvl m) n.V := by
  induction m with
  | zero =>
    refine ((E.toBase 1).continuous.comp_continuousOn n.continuousOn_Γ_lvl_one).congr
      fun a ha => ?_
    rw [Function.comp_apply, n.toBase_Γ_lvl 1 ha, n.Γ_lvl_zero]
  | succ k ih =>
    have h := d.isScPlus.isScSmooth_liftOne.isSc1.isSc0.continuousOn k
    refine (h.comp ih fun a ha => n.Γ_lvl_mem_U k ha).congr fun a ha => ?_
    rw [Function.comp_apply, n.Γ_lvl_succ k ha]

theorem continuousOn_Γ : ContinuousOn n.Γ n.V := by
  have := n.continuousOn_Γ_lvl 0
  refine this.congr fun a _ => ?_
  rw [n.Γ_lvl_zero]

/-! ### The derivative of `Γ`: the frame formula `DΓ(a) = B_{Γ(a)}` on every level -/

/-- **`Γ_{k+1}` is differentiable on `V` with derivative the frame at `Γ(a)`**: Lemma A
(`hasFDerivWithinAt_of_projection`) at `u₀ = Γ_{k+1}(a₀)` on the convex set
`C_{k+1} ∩ B(u₀, r)` of the mean value estimate, with `q = p ∘ ι_{k+1}` and `B` the level-`(k+1)`
frame; `Γ_{k+1}` is continuous, so it stays in `B(u₀, r)` near `a₀`. -/
theorem hasFDerivWithinAt_Γ_lvl (hθ₀ : d.FrameSmall θ₀) (k : ℕ) {a₀ : d.N} (ha₀ : a₀ ∈ n.V) :
    HasFDerivWithinAt (n.Γ_lvl (k + 1)) (d.frameL k (n.Γ_lvl (k + 1) a₀)) n.V a₀ := by
  set x := n.Γ_lvl (k + 1) a₀ with hx
  have hxO : x ∈ E.lvlSet d.T.retract (k + 1) := n.Γ_lvl_mem_retract (k + 1) ha₀
  have hxU : x ∈ E.lvlSet d.T.U (k + 1) := n.Γ_lvl_mem_U (k + 1) ha₀
  have hxC : x ∈ E.lvlSet C (k + 1) := n.Γ_lvl_mem_C (k + 1) ha₀
  have hder := n.deriv_bound_Γ k ha₀
  set B := d.frameL k x with hB
  set q : E (k + 1) →L[ℝ] d.N := d.p.comp (E.toBase (k + 1)) with hq
  have hqB : ∀ n', q (B n') = n' := fun n' => p_toBase_frameL hθ₀ hxO hder n'
  have hπD : ∀ v, d.T.lvlDeriv k x v - B (q (d.T.lvlDeriv k x v)) = 0 := fun v =>
    lvlDeriv_sub_frameL hθ₀ hxO hder v
  set π := ContinuousLinearMap.id ℝ (E (k + 1)) - B.comp q with hπ
  set θ := 1 / (2 * (‖π‖ + 1)) with hθ
  have hθpos : 0 < θ := by positivity
  have hθπ : θ * ‖π‖ ≤ 1 / 2 := by
    rw [hθ, one_div, inv_mul_eq_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg π]
  obtain ⟨r, hr, hsub, -, hmvt⟩ := d.isScPlus.exists_mvt k hxU hθpos
  set S := E.lvlSet C (k + 1) ∩ ball x r with hS
  have hmvt' : ∀ z ∈ S, ∀ z' ∈ S,
      ‖(d.T.lvlMap k z' - d.T.lvlMap k z) - d.T.lvlDeriv k x (z' - z)‖ ≤ θ * ‖z' - z‖ :=
    fun z hz z' hz' => hmvt z hz.1 z' hz'.1 (mem_ball_iff_norm.1 hz.2) (mem_ball_iff_norm.1 hz'.2)
  have hdiff : HasFDerivWithinAt (d.T.lvlMap k) (d.T.lvlDeriv k x) S x :=
    (d.isScPlus.hasFDerivWithinAt_lvlMap k hxU).mono hsub
  have hxS : x ∈ S := ⟨hxC, mem_ball_self hr⟩
  have hsx : d.T.lvlMap k x = x := d.isScPlus.lvlMap_eq_self k hxO
  set Wl := n.V ∩ n.Γ_lvl (k + 1) ⁻¹' ball x r with hWl
  have hWl : Wl ∈ 𝓝[n.V] a₀ :=
    inter_mem self_mem_nhdsWithin
      ((n.continuousOn_Γ_lvl (k + 1) a₀ ha₀).preimage_mem_nhdsWithin (ball_mem_nhds x hr))
  have ha₀W : a₀ ∈ Wl := ⟨ha₀, mem_ball_self hr⟩
  have hΓ : ∀ z ∈ Wl, n.Γ_lvl (k + 1) z ∈ S ∧ d.T.lvlMap k (n.Γ_lvl (k + 1) z) = n.Γ_lvl (k + 1) z ∧
      q (n.Γ_lvl (k + 1) z) = z := fun z hz =>
    ⟨⟨n.Γ_lvl_mem_C (k + 1) hz.1, hz.2⟩,
      d.isScPlus.lvlMap_eq_self k (n.Γ_lvl_mem_retract (k + 1) hz.1),
      by rw [hq, ContinuousLinearMap.comp_apply, n.toBase_Γ_lvl (k + 1) hz.1, n.p_Γ z hz.1]⟩
  have hcont : ContinuousWithinAt (n.Γ_lvl (k + 1)) Wl a₀ :=
    (n.continuousOn_Γ_lvl (k + 1)).mono inter_subset_left a₀ ha₀W
  have := hasFDerivWithinAt_of_projection hmvt' hdiff q B hπD hθπ hxS hsx ha₀W rfl hΓ hcont
  exact this.mono_of_mem_nhdsWithin hWl

end Nbhd

/-! ### The `C^k`-bootstrap along the finite-dimensional `N`

`DΓ(a) = Dt(Γ(a))|_N ∘ (p ∘ Dt(Γ(a))|_N)⁻¹` on every level.  Derivatives of `t` are only applied to
vectors of the smooth finite-dimensional `N`, so the level loss of `Tt` (Proposition 1.2.3 (preprint 1.18)) does not
accumulate: if `Γ` is `C^k` into every level then `a ↦ Dt(Γ(a))|_N ∈ L(N, E_{j+1})` is `C^k`
(it factors through `Tt¹ : (TU)_{j+k} → (TE¹)_j`, which is `C^k`, and `Γ_{j+k+1}`), and so `Γ` is
`C^{k+1}` into every level. -/

variable (d) in
/-- **Proposition 1.2.3 (preprint 1.18) for the tangent map of the lift `t¹`**: `(x, w) ↦ Dt_{j+1}(x) w` is `C^k`
on `U_{j+k+1} × E_{j+k+1}` (through the inclusions into level `j + 1`). -/
theorem contDiffOn_lvlDeriv_apply (j k : ℕ) :
    ContDiffOn ℝ k (fun q : E (j + k + 1) × E (j + k + 1) =>
      d.T.lvlDeriv j (E.shift.inclK j k q.1) (E.shift.inclK j k q.2))
      (E.lvlSet d.T.U (j + k + 1) ×ˢ univ) := by
  set g := d.T.liftOne with hg
  have hg1 : IsSc1With (E := E) (F := E.shift) d.T.U g d.T.liftDeriv :=
    d.isScPlus.isSc1With_liftOne
  have hTg : IsScSmooth (E := E.tangent) (F := E.shift.tangent) (E.tangentSet d.T.U)
      (tangentMap (E := E) (F := E.shift) d.T.U g) :=
    (isScSmooth_iff.1 d.isScPlus.isScSmooth_liftOne).2
  have hk := (hTg k).contDiffOn_levels d.T.isScDomain.tangentSet j
  rw [ScBanach.lvlSet_tangentSet] at hk
  have hL : ContDiffOn ℝ k (fun q : E (j + k + 1) × E (j + k + 1) =>
      ((q.1, E.incl (j + k) q.2) : E.tangent (j + k))) (E.lvlSet d.T.U (j + k + 1) ×ˢ univ) :=
    contDiffOn_fst.prodMk ((E.incl (j + k)).contDiff.comp_contDiffOn contDiffOn_snd)
  have hmaps : MapsTo (fun q : E (j + k + 1) × E (j + k + 1) =>
      ((q.1, E.incl (j + k) q.2) : E.tangent (j + k)))
      (E.lvlSet d.T.U (j + k + 1) ×ˢ univ) (E.lvlSet d.T.U (j + k + 1) ×ˢ univ) :=
    fun q hq => ⟨hq.1, mem_univ _⟩
  have := (hk.comp hL hmaps).snd
  refine this.congr fun q hq => ?_
  have hp : E.tangent.inclK j k ((q.1, E.incl (j + k) q.2) : E.tangent (j + k)) ∈
      E.tangent.lvlSet (E.tangentSet d.T.U) j := by
    rw [ScBanach.mem_lvlSet_tangentSet, E.tangent_inclK]
    exact E.shift_inclK_mem_lvlSet hq.1
  simp only [Function.comp_apply]
  rw [show tangentMap (E := E) (F := E.shift) d.T.U g =
      tangentMapWith (E := E) (F := E.shift) g d.T.liftDeriv from rfl,
    hg1.levelMap_tangentMapWith hp, E.tangent_inclK]
  change levelDeriv (E := E) (F := E.shift) d.T.liftDeriv j (E.shift.inclK j k q.1)
    (E.incl j (E.shift.inclK j k q.2)) = _
  rw [E.incl_shift_inclK, E.inclK_succ]

namespace Nbhd

variable {θ₀ : ℝ} (n : d.Nbhd θ₀)

/-- `a ↦ Dt(Γ(a))(w(a))` is `C^k` into `E_{j+1}` when `Γ_{j+k+1}` and `w : V → N` are. -/
theorem contDiffOn_lvlDeriv_Γ (j k : ℕ) (hΓ : ContDiffOn ℝ k (n.Γ_lvl (j + k + 1)) n.V)
    {w : d.N → d.N} (hw : ContDiffOn ℝ k w n.V) :
    ContDiffOn ℝ k (fun a => d.T.lvlDeriv j (n.Γ_lvl (j + 1) a) (d.liftN (j + 1) (w a))) n.V := by
  have h := (contDiffOn_lvlDeriv_apply d j k).comp
    (hΓ.prodMk ((d.liftN (j + k + 1)).contDiff.comp_contDiffOn hw))
    (fun a ha => ⟨n.Γ_lvl_mem_U (j + k + 1) ha, mem_univ _⟩)
  refine h.congr fun a ha => ?_
  simp only [Function.comp_apply]
  rw [n.shift_inclK_Γ_lvl j k ha, d.liftN_shift_inclK]

/-- `a ↦ A(Γ(a)) = p ∘ Dt(Γ(a))|_N` is `C^k` when `Γ_{k+1}` is. -/
theorem contDiffOn_A_Γ (k : ℕ) (hΓ : ContDiffOn ℝ k (n.Γ_lvl (0 + k + 1)) n.V) :
    ContDiffOn ℝ k (fun a => d.A (n.Γ_lvl 1 a)) n.V := by
  rw [contDiffOn_clm_apply]
  intro n'
  have h := n.contDiffOn_lvlDeriv_Γ 0 k hΓ (w := fun _ => n') contDiffOn_const
  have h2 := (d.p.comp (E.toBase (0 + 1))).contDiff.comp_contDiffOn h
  refine h2.congr fun a ha => ?_
  change d.p (scDeriv d.T.U d.T (n.Γ_lvl 1 a) n') =
    d.p (E.toBase 1 (d.T.lvlDeriv 0 (n.Γ_lvl 1 a) (d.liftN 1 n')))
  rw [d.isScPlus.toBase_lvlDeriv 0 (n.Γ_lvl_mem_U 1 ha), d.toBase_liftN]
  rfl

/-- `a ↦ M(Γ(a)) = A(Γ(a))⁻¹` is `C^k` when `A ∘ Γ` is (inversion is smooth on the invertible
operators). -/
theorem contDiffOn_M_Γ (hθ₀ : d.FrameSmall θ₀) (k : ℕ)
    (hA : ContDiffOn ℝ k (fun a => d.A (n.Γ_lvl 1 a)) n.V) :
    ContDiffOn ℝ k (fun a => d.M (n.Γ_lvl 1 a)) n.V := by
  intro a ha
  have hinv := contDiffAt_map_inverse (𝕜 := ℝ) (n := k)
    (Aeq hθ₀ (n.Γ_lvl_mem_U 1 ha) (n.deriv_bound _ (n.Γ_lvl_mem_C 1 ha) (n.norm_Γ_lvl_one_lt ha)))
  rw [coe_Aeq] at hinv
  exact hinv.comp_contDiffWithinAt a (hA a ha)

/-- **The `C^k`-bootstrap**: `Γ` is `C^k` into every level `E_{j+1}` on `V`, for every `k`. -/
theorem contDiffOn_Γ_lvl (hθ₀ : d.FrameSmall θ₀) (k : ℕ) :
    ∀ j, ContDiffOn ℝ k (n.Γ_lvl (j + 1)) n.V := by
  induction k with
  | zero => intro j; rw [Nat.cast_zero, contDiffOn_zero]; exact n.continuousOn_Γ_lvl (j + 1)
  | succ k ih =>
    intro j
    rw [Nat.cast_succ, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn n.uniqueDiffOn_V]
    refine ⟨fun h => absurd h (WithTop.natCast_ne_top k),
      fun a => d.frameL j (n.Γ_lvl (j + 1) a), ?_, fun a ha => n.hasFDerivWithinAt_Γ_lvl hθ₀ j ha⟩
    have hA := n.contDiffOn_A_Γ k (ih (0 + k))
    have hM := n.contDiffOn_M_Γ hθ₀ k hA
    rw [contDiffOn_clm_apply]
    intro n'
    have hw : ContDiffOn ℝ k (fun a => d.M (n.Γ_lvl 1 a) n') n.V := hM.clm_apply contDiffOn_const
    refine (n.contDiffOn_lvlDeriv_Γ j k (ih (j + k)) hw).congr fun a ha => ?_
    rw [frameL_apply, n.shift_toBase_Γ_lvl j ha]

theorem contDiffOn_Γ_lvl_succ_infty (hθ₀ : d.FrameSmall θ₀) (j : ℕ) :
    ContDiffOn ℝ ∞ (n.Γ_lvl (j + 1)) n.V := by
  rw [contDiffOn_infty]
  intro k
  exact n.contDiffOn_Γ_lvl hθ₀ k j

theorem contDiffOn_Γ_lvl_infty (hθ₀ : d.FrameSmall θ₀) (m : ℕ) :
    ContDiffOn ℝ ∞ (n.Γ_lvl m) n.V := by
  cases m with
  | zero =>
    refine ((E.toBase 1).contDiff.comp_contDiffOn (n.contDiffOn_Γ_lvl_succ_infty hθ₀ 0)).congr
      fun a ha => ?_
    rw [Function.comp_apply, n.toBase_Γ_lvl 1 ha, n.Γ_lvl_zero]
  | succ j => exact n.contDiffOn_Γ_lvl_succ_infty hθ₀ j

/-- **`Γ : V → E` is sc-smooth on `V`** (in the set sense, on the fixed neighbourhood `V`), by the
criterion for maps from a finite-dimensional domain (`IsScSmooth.of_contDiffOn_levels`). -/
theorem isScSmooth_Γ (hθ₀ : d.FrameSmall θ₀) :
    IsScSmooth (E := ScBanach.const d.N) (F := E) n.V n.Γ := by
  refine IsScSmooth.of_contDiffOn_levels n.isScDomain_V (fun m a ha => ?_) fun m => ?_
  · rw [ScBanach.lvlSet_const] at ha
    rw [ScBanach.const_toBase]
    exact ⟨n.Γ_lvl m a, n.toBase_Γ_lvl m ha⟩
  · rw [ScBanach.lvlSet_const]
    exact (n.contDiffOn_Γ_lvl_infty hθ₀ m).congr fun a _ => n.levelMap_Γ_eq m a

/-! ### The sc-diffeomorphism `p : O ∩ W → V` between the retracts -/

/-- `(O ∩ W, C, E)` is an sc-smooth retract (Proposition 2.3.1 (preprint 2.10) (1)). -/
theorem isScRetract_inter_W : IsScRetract E C (d.T.retract ∩ n.W) :=
  proposition_2_3_1_one d.T.isScRetract n.isOpen_W

/-- `(V, N ∩ C, N)` is an sc-smooth retract (the identity retraction). -/
theorem isScRetract_V : IsScRetract (ScBanach.const d.N) (Subtype.val ⁻¹' C) n.V :=
  n.V_isRelOpenInQuadrant.isScRetract

/-- `p` is sc-smooth `E → N` (a continuous linear map into a finite-dimensional space,
Corollary 1.2.5 (preprint 1.20)). -/
theorem _root_.Polyfold.GraphData.p_isScSmooth :
    IsScSmooth (E := E) (F := ScBanach.const d.N) univ d.p :=
  IsScSmooth.of_contDiffOn_finiteDimensional (isScDomain_univ _) d.p.contDiff.contDiffOn

/-- `p : (O ∩ W, C, E) → (V, N ∩ C, N)` is sc-smooth between the retracts. -/
theorem p_isScSmoothRetractMap :
    IsScSmoothRetractMap E C (d.T.retract ∩ n.W) (ScBanach.const d.N) (Subtype.val ⁻¹' C) n.V
      d.p where
  mapsTo := fun u hu => n.p_mem_V u hu
  comp_isScSmooth R _ := IsScSmooth.comp R.isScDomain (isScDomain_univ _) d.p_isScSmooth
    R.isScSmooth (mapsTo_univ _ _)

/-- `Γ : (V, N ∩ C, N) → (O ∩ W, C, E)` is sc-smooth between the retracts. -/
theorem Γ_isScSmoothRetractMap (hθ₀ : d.FrameSmall θ₀) :
    IsScSmoothRetractMap (ScBanach.const d.N) (Subtype.val ⁻¹' C) n.V E C (d.T.retract ∩ n.W)
      n.Γ where
  mapsTo := fun a ha => ⟨n.Γ_mem a ha, n.Γ_mem_W a ha⟩
  comp_isScSmooth S hS := by
    have hmaps : MapsTo S S.U n.V := fun a ha => hS ▸ S.apply_mem_retract ha
    exact IsScSmooth.comp (E := ScBanach.const d.N) (F := ScBanach.const d.N) (G := E)
      S.isScDomain n.isScDomain_V (n.isScSmooth_Γ hθ₀) S.isScSmooth hmaps

end Nbhd

end GraphData

/-! ### Proposition 4.1.9 (preprint 4.9) -/

/-- **Lemma 4.1.7 (preprint 4.7) (ii) in the form needed by Proposition 4.1.9 (preprint 4.9)**: `T₀O` is finite-dimensional. -/
theorem finiteDimensional_tangentSpace_zero {C : Set (E 0)} (T : ScRetraction E C)
    (hT : T.IsScPlus) (h0 : (0 : E 0) ∈ T.retract) {N : Submodule ℝ (E 0)}
    (hN : (N : Set (E 0)) = tangentSpace E C T.retract 0) : FiniteDimensional ℝ N := by
  have h0' : (0 : E 1) ∈ E.lvlSet T.retract 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have := lemma_4_1_7_ii hT h0'
  exact Submodule.finiteDimensional_of_le
    (SetLike.coe_injective (hN.trans (tangentSpace_eq_coe_submodule T h0'))).le

/-- **Proposition 4.1.9 (preprint 4.9)** (with Lemmas 4.11 and 4.12), by the direct proof.  Let `(O, C, E)` be an
sc⁺-retract, `t : U → U` an sc⁺-retraction onto `O` with `0 ∈ O`, `N = T₀O` (finite-dimensional
by Lemma 4.1.7 (preprint 4.7), `[FiniteDimensional ℝ N]` is `finiteDimensional_tangentSpace_zero`) in good position
to `C`, `Y` a good complement of `N` (**added hypothesis: `Y` closed**), and `p : E → N` the
projection along `Y` (`p = 1` on `N`, `p = 0` on `Y`; the text writes `p = Dt(0)`, see the module
docstring).  Then there are an open `W ∋ 0` in `E` and a relatively open `V ∋ 0` in the partial
quadrant `N ∩ C` of `N` (Proposition 3.1.25 (preprint 3.22)) and a map `Γ : V → E`, sc-smooth on `V`, with
`p ∘ Γ = 1` on `V`, `Γ(a) − a ∈ Y`, `Γ(V) = O ∩ W` and `Γ ∘ p = 1` on `O ∩ W`; so
`p : (O ∩ W, C, E) → (V, N ∩ C, N)` is an sc-diffeomorphism between the retracts, with inverse
`Γ` (both directions sc-smooth in the sense of Definition 2.1.14 (preprint 2.7)). -/
theorem proposition_4_1_9 {C : Set (E 0)} (T : ScRetraction E C) (hT : T.IsScPlus)
    (h0 : (0 : E 0) ∈ T.retract) {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]
    (hN : (N : Set (E 0)) = tangentSpace E C T.retract 0) (hgood : IsInGoodPosition E C N)
    {Y : Submodule ℝ (E 0)} (hY : IsGoodComplement E C N Y) (hYc : IsClosed (Y : Set (E 0)))
    (p : E 0 →L[ℝ] N) (hpN : ∀ n : N, p n = n) (hpY : ∀ y ∈ Y, p y = 0) :
    ∃ (W : Set (E 0)) (V : Set N) (Γ : N → E 0),
      IsOpen W ∧ (0 : E 0) ∈ W ∧
      IsRelOpenInQuadrant (ScBanach.const N) (Subtype.val ⁻¹' C) V ∧ (0 : N) ∈ V ∧
      IsScSmooth (E := ScBanach.const N) (F := E) V Γ ∧
      (∀ a ∈ V, p (Γ a) = a) ∧ (∀ a ∈ V, Γ a - a ∈ Y) ∧ Γ '' V = T.retract ∩ W ∧
      (∀ u ∈ T.retract ∩ W, Γ (p u) = u) ∧ Γ 0 = 0 ∧
      IsScSmoothRetractMap E C (T.retract ∩ W) (ScBanach.const N) (Subtype.val ⁻¹' C) V p ∧
      IsScSmoothRetractMap (ScBanach.const N) (Subtype.val ⁻¹' C) V E C (T.retract ∩ W) Γ := by
  let d : GraphData E C := ⟨T, hT, h0, N, hN, hgood, Y, hY, hYc, p, hpN, hpY⟩
  obtain ⟨θ₀, hθ₀pos, hθ₀⟩ := d.exists_frameSmall
  obtain ⟨n⟩ := d.exists_nbhd hθ₀pos
  exact ⟨n.W, n.V, n.Γ, n.isOpen_W, n.zero_mem_W, n.V_isRelOpenInQuadrant, n.zero_mem_V,
    n.isScSmooth_Γ hθ₀, fun a ha => n.p_Γ a ha, fun a ha => n.Γ_sub_mem_Y a ha, n.image_V,
    fun u hu => n.Γ_p u hu, n.Γ_zero, n.p_isScSmoothRetractMap, n.Γ_isScSmoothRetractMap hθ₀⟩

end Polyfold
