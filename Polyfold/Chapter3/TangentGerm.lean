import Polyfold.Chapter3.GoodPosition
import Polyfold.Chapter3.GermIFT
import Polyfold.Chapter2.SubMPolyfold
import Polyfold.Chapter2.TameRetracts
import Polyfold.Chapter2.TangentMap
import Polyfold.Chapter3.StrongBundleSections
import Polyfold.Chapter2.Metrizable

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.2,
**Definition 3.2.1 (preprint 3.25)** (the `n`-dimensional tangent germ property), **Proposition 3.2.2 (preprint 3.26)** (invariance
under sc-diffeomorphisms) and **Theorem 3.2.3 (preprint 3.27)** (a subset with the tangent germ property is a
tame sub-M-polyfold carrying the structure of a finite-dimensional manifold with boundary with
corners).

# Subsets with tangent structure

## The text, paraphrased

(Definition 3.2.1 (preprint 3.25)) A subset `M` of a tame M-polyfold `X` has the `n`-dimensional tangent germ
property if (1) `M ⊆ X_∞` and (2) every `x ∈ M` has a chart `ϕ : (U, x) → (O, 0)` onto a tame
retract `(O, C, E)`, an `n`-dimensional smooth subspace `N ⊆ E` in good position to `C` with a good
complement `Y`, a relatively open neighbourhood `V` of `0` in `N ∩ C` and a continuous
`δ : V → Y` with (i) `ϕ(M ∩ U) = {v + δ(v) | v ∈ V}` and (ii) `δ : O(N ∩ C, 0) → (Y, 0)` an
sc^∞-germ with `δ(0) = 0`, `Dδ(0) = 0`.  (Proposition 3.2.2 (preprint 3.26)) The property is invariant under
sc-diffeomorphisms.  (Theorem 3.2.3 (preprint 3.27)) Such an `M` is a sub-M-polyfold whose induced structure is
tame and sc-smoothly equivalent to a manifold with boundary with corners; the map
`y ↦ π ∘ ϕ(y)` is a smooth chart of `M` around `x`.

## What is formalized

* `Polyfold.IsScInftyGermAt D δ`: **the reading of "sc^∞-germ" in Definition 3.2.1 (preprint 3.25) (ii)**: for every
  level `m` and every `k` there is a relatively open neighbourhood `V_{m,k}` of `0` in `D = N ∩ C`
  on which `δ` takes values in `E_m` and is `C^k` into `E_m`.  This is exactly what Corollary 3.3.7 (preprint 3.34)
  (`corollary_3_3_7`) and Theorem 3.5.6 (preprint 3.43)/3.47 deliver (Findings 2 and 70): the neighbourhood
  depends on `k` (and `m`).  (For Corollary 3.3.7 (preprint 3.34) the fixed-germ reading also holds:
  `corollary_3_3_7_isScSmoothGerm`, `GermIFTSmooth.lean`, Findings Chapter 3, items 222, 250.)  The reading "one sc-smooth germ on a fixed sequence `(V_m)`"
  (`IsScSmoothGerm` on an `ScNbhdGerm`) implies it (`IsScSmoothGerm.isScInftyGermAt`), and so
  does set-sense sc-smoothness on a fixed neighbourhood (`IsScSmooth.isScInftyGermAt`); so the
  theorems below cover both readings.
* `Polyfold.MPolyfold.TangentGermChart P M x n`: the data of **Definition 3.2.1 (preprint 3.25) (2)** at `x`, and
  `Polyfold.MPolyfold.HasTangentGermProperty P M n` (**Definition 3.2.1 (preprint 3.25)**).
  **Added hypothesis: `Y` is closed** (the text's good complement is an sc-complement, hence
  closed; it is needed for the projection `π : E → N` along `Y` to be continuous, see
  `TangentGermChart.π`).
* `Polyfold.proposition_3_2_2`: **Proposition 3.2.2 (preprint 3.26)** for an sc-diffeomorphism `ψ : X → X'` with
  inverse `ψ'` (`IsScDiffeoOn` on `univ`): `ψ(M)` has the property iff `M` has it; the data at
  `ψ(x)` are the chart `ϕ ∘ ψ⁻¹` (`transportChart`) with the same `N, Y, V, δ`
  (`MPolyfold.TangentGermChart.transport`), and `ψ(M) ⊆ X'_∞` because sc-smooth maps preserve
  the levels (`IsScSmoothOn.mapsTo_levelSet`).
* `Polyfold.MPolyfold.TangentGermChart.IsRegular`: the two conditions under which the text's
  proof of Theorem 3.2.3 (preprint 3.27) goes through, see the findings below: (a) `δ` is sc-smooth on `V` in the
  set sense (not only as a germ at `0`), and (b) the projection `π` along `Y` maps `O` into `C`.
* `Polyfold.theorem_3_2_3_isSubMPolyfold`: **Theorem 3.2.3 (preprint 3.27) (1), first clause**, under `IsRegular`
  at every point: `M` is a sub-M-polyfold, with the text's retraction `s = ϕ⁻¹ ∘ t ∘ ϕ`,
  `t(v + w) = v + δ(v)`.
* `Polyfold.MPolyfold.TangentGermChart.chart`: **Theorem 3.2.3 (preprint 3.27) (2)**: the chart `y ↦ π ∘ ϕ(y)` of
  `M`, modelled on `(V, N ∩ C, N)`; `theorem_3_2_3_isChart` (it is a chart of the induced
  M-polyfold structure of Proposition 2.3.19 (preprint 2.21)), `theorem_3_2_3_isTame` (the induced structure is tame),
  `theorem_3_2_3_isManifoldWithCorners` (an equivalent atlas of finite-dimensional corner charts,
  `MPolyfold.IsManifoldWithCorners`).

## What the text leaves implicit, and the choices made (the findings)

* **"sc^∞-germ" in (ii) is read with `k`-dependent neighbourhoods** (`IsScInftyGermAt`); see
  above.  With this reading, condition (ii) does **not** give an sc-smooth map on a fixed
  neighbourhood of `0`, which is what the retraction `t` of the proof of Theorem 3.2.3 (preprint 3.27) needs
  (Definition 2.3.18 (preprint 2.20) asks for an sc-smooth retraction on a fixed open set).
* **The step "δ is an sc^∞-germ near every `v₀ ∈ V`" of the text's proof fails as stated.**  The
  text linearizes `w ↦ π ∘ ϕ ∘ ψ⁻¹(w + τ(w))` at `0` and asserts that `h ↦ π ∘ T(ϕ ∘ ψ⁻¹)(0)h` is
  an isomorphism `N' → N`; this needs `δ` differentiable at `v₀` (the tangent space of the graph
  at `v₀ + δ(v₀)`), which is known only near `0`.  Example: `X = ℝ²`, `M` a smooth embedded curve
  through `0` tangent to the `x`-axis which has a vertical tangent at `(2, 4)`, chart `ϕ = id`,
  `N` the `x`-axis, `δ = g` with `M = graph g`, `g(s) = s²` near `0`, `g(s) = 4 + (s − 2)^{1/3}` near
  `2`: all conditions of Definition 3.2.1 (preprint 3.25) hold (at `(2, 4)` use the rotated chart), `δ` is smooth
  at `0` but not at `v₀ = 2`, so "`v ↦ ϕ⁻¹(v + δ(v))` is an injective sc-smooth map" and "the map
  `U ∩ M → V, y ↦ π ∘ ϕ(y)` defines a smooth chart" are false on the whole `U`.  The statement is
  saved by shrinking `U` to where `δ` is sc-smooth; formally this is condition (a) of `IsRegular`
  (an added hypothesis here).
* **"`Σ = {v + y ∈ C | v ∈ V, y ∈ Y}` is relatively open in `C`" is false in general.**  Example:
  `E = ℝ³`, `C = [0, ∞)³`, `N = ℝ(1, 1, 1)`, `Y = {x + y − z = 0}` (a good complement, `N ∩ C` a
  ray): `πz ∈ C` iff `x + y ≥ z`, so `Σ` is closed and not open in `C` near `(1, 0, 1)`, and the
  text's `t(v + w) = v + δ(v)` is not defined on a neighbourhood of `0` in `O = C`.  It holds when
  `π(O) ⊆ C` (condition (b) of `IsRegular`).  A closed good complement `Y'` with `π'(C) ⊆ N ∩ C`
  always exists (`exists_goodComplement_projectsInto`, `GoodComplementProjection.lean`, Finding
  131: the projection keeps a set `S` of coordinates `ℓ_i` of the normal form of Proposition 3.1.25 (preprint 3.22),
  `S = Σ` the coordinates vanishing at a nonzero point of `N ∩ C` when `Σ ≠ ∅`, and one kept
  coordinate when `Σ = ∅` and `N ∩ C ≠ N` — the case which the sketch of Finding 83, projecting
  along the `ℓ_i`, `i ∈ Σ`, misses).  For an arbitrary `M` with the tangent germ property,
  `ϕ(M ∩ U)` then has to be re-written as a graph over `N` along `Y'`, which needs the quadrant
  inverse function theorem (Theorem 3.8.15 (preprint 3.72)) and is not done here; for the solution set of an
  sc-Fredholm section the complement is chosen in Theorem 3.5.6 (preprint 3.43) instead
  (`theorem_3_6_8_tangentGermChart_proj_wholeChart`, Findings 130–133).
* **"Manifold with boundary with corners"**: Chapter 4 of the text; here the induced structure is
  called a manifold with corners if it has an equivalent atlas of charts modelled on relatively
  open subsets of partial quadrants of finite-dimensional spaces of dimension `n`
  (`MPolyfold.IsManifoldWithCorners`); its transition maps are then classically smooth by
  `isScSmooth_iff_contDiffOn_const`.
-/

open Set Filter Topology Function Module
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### sc^∞-germs on a finite-dimensional partial quadrant (the reading of Definition 3.2.1 (preprint 3.25) (ii)) -/

section FinGerm

variable {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N] {E : ScBanach}

/-- **The reading of "sc^∞-germ `δ : O(N ∩ C, 0) → (Y, 0)`" of Definition 3.2.1 (preprint 3.25) (ii)**: for every
level `m` and every `k` there is a relatively open neighbourhood `V_{m,k}` of `0` in `D = N ∩ C`
such that `δ(V_{m,k}) ⊆ E_m` and `δ : V_{m,k} → E_m` is of class `C^k`.  The neighbourhood depends
on `k` and `m`, as in Corollary 3.3.7 (preprint 3.34) (Finding 2). -/
def IsScInftyGermAt (D : Set N) (δ : N → E 0) : Prop :=
  ∀ m k : ℕ, ∃ V : Set N, (∃ O : Set N, IsOpen O ∧ V = O ∩ D) ∧ (0 : N) ∈ V ∧
    (∀ v ∈ V, δ v ∈ range (E.toBase m)) ∧
    ContDiffOn ℝ k (levelMap (E := ScBanach.const N) (F := E) δ m) V

/-- The fixed-germ reading implies the `k`-dependent one: an sc-smooth germ on a germ of
neighbourhoods `G` in `N` is `C^k` into `E_m` on `G.U (m + k)` (Proposition 1.2.3 (preprint 1.18) for germs). -/
theorem IsScSmoothGerm.isScInftyGermAt {D : Set N} (hD : IsQuadrantLike (ScBanach.const N) D)
    (G : ScNbhdGerm (ScBanach.const N) D) {δ : N → E 0} (h : IsScSmoothGerm G δ) :
    IsScInftyGermAt D δ := by
  intro m k
  obtain ⟨O, hO, hU⟩ := G.relOpen (m + k)
  refine ⟨G.U (m + k), ⟨O, hO, by rw [hU, ScBanach.lvlSet_const]⟩, G.zero_mem _, fun v hv => ?_, ?_⟩
  · have := (h 0).mem_range m ((ScBanach.const N).inclK m k v) (G.inclK_mem hv)
    rwa [ScBanach.const_toBase, ScBanach.const_inclK] at this
  · refine ((h k).contDiffOn_levels hD m).congr fun v _ => ?_
    rw [Function.comp_apply, ScBanach.const_inclK]

/-- Set-sense sc-smoothness on a relatively open neighbourhood `V` of `0` in `D` implies the
`k`-dependent germ property (with `V_{m,k} = V`). -/
theorem IsScSmooth.isScInftyGermAt {D V : Set N} (hV : IsRelOpenInQuadrant (ScBanach.const N) D V)
    (h0 : (0 : N) ∈ V) {δ : N → E 0} (h : IsScSmooth (E := ScBanach.const N) (F := E) V δ) :
    IsScInftyGermAt D δ := by
  intro m k
  refine ⟨V, hV.relOpen, h0, fun v hv => ?_, ?_⟩
  · have := (h 0).mem_range m v (by rwa [ScBanach.lvlSet_const])
    rwa [ScBanach.const_toBase] at this
  · have := (h k).contDiffOn_levels hV.isScDomain m
    rw [ScBanach.lvlSet_const] at this
    refine this.congr fun v _ => ?_
    rw [Function.comp_apply, ScBanach.const_inclK]

/-- A `k`-dependent sc^∞-germ is continuous at `0` into every level `E_m`, on `V_{m,0}`. -/
theorem IsScInftyGermAt.continuousOn_level {D : Set N} {δ : N → E 0} (h : IsScInftyGermAt D δ)
    (m : ℕ) : ∃ V : Set N, (∃ O : Set N, IsOpen O ∧ V = O ∩ D) ∧ (0 : N) ∈ V ∧
      (∀ v ∈ V, δ v ∈ range (E.toBase m)) ∧
      ContinuousOn (levelMap (E := ScBanach.const N) (F := E) δ m) V := by
  obtain ⟨V, hV, h0, hmem, hc⟩ := h m 0
  exact ⟨V, hV, h0, hmem, by simpa [contDiffOn_zero] using hc⟩

/-- The `C¹`-part of the germ property on level `0`: `δ` is `C¹` near `0` in `D`. -/
theorem IsScInftyGermAt.contDiffOn_one {D : Set N} {δ : N → E 0} (h : IsScInftyGermAt D δ) :
    ∃ V : Set N, (∃ O : Set N, IsOpen O ∧ V = O ∩ D) ∧ (0 : N) ∈ V ∧ ContDiffOn ℝ 1 δ V := by
  obtain ⟨V, hV, h0, -, hc⟩ := h 0 1
  refine ⟨V, hV, h0, hc.congr fun v _ => ?_⟩
  change δ v = Function.invFun (E.toBase 0) (δ ((ScBanach.const N).toBase 0 v))
  rw [ScBanach.const_toBase]
  exact (Function.leftInverse_invFun (E.toBase_injective 0) (δ v)).symm

end FinGerm

/-! ### The inclusion of a finite-dimensional smooth subspace is sc-smooth -/

section Inclusion

variable {E : ScBanach} {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]

/-- The lift `N → E_m` of a smooth finite-dimensional subspace, as a linear map. -/
def finSmoothLift (hN : N ≤ E.smooth) (m : ℕ) : N →ₗ[ℝ] E m :=
  (LinearEquiv.ofInjective (E.toBase m : E m →ₗ[ℝ] E 0) (E.toBase_injective m)).symm.toLinearMap.comp
    (N.subtype.codRestrict (LinearMap.range (E.toBase m : E m →ₗ[ℝ] E 0)) fun v => by
      have := (ScScale.mem_smooth_iff (E := E.toScScale)).1 (hN v.2) m
      obtain ⟨y, hy⟩ := this
      exact ⟨y, hy⟩)

omit [FiniteDimensional ℝ N] in
lemma toBase_finSmoothLift (hN : N ≤ E.smooth) (m : ℕ) (v : N) :
    E.toBase m (finSmoothLift hN m v) = (v : E 0) := by
  set e := LinearEquiv.ofInjective (E.toBase m : E m →ₗ[ℝ] E 0) (E.toBase_injective m) with he
  have key : ∀ y : LinearMap.range (E.toBase m : E m →ₗ[ℝ] E 0),
      (E.toBase m : E m →ₗ[ℝ] E 0) (e.symm y) = (y : E 0) := fun y => by
    have h := congrArg Subtype.val (e.apply_symm_apply y)
    exact h
  exact key _

/-- The inclusion `N → E` of a smooth finite-dimensional subspace is sc-smooth (its level maps are
the linear lifts `N → E_m`, continuous since `N` is finite-dimensional). -/
theorem isScSmooth_subtype_val (hN : N ≤ E.smooth) {V : Set N}
    (hV : IsScDomain (ScBanach.const N) V) :
    IsScSmooth (E := ScBanach.const N) (F := E) V (Subtype.val : N → E 0) := by
  refine IsScSmooth.of_contDiffOn_levels hV (fun m v _ => ?_) fun m => ?_
  · rw [ScBanach.const_toBase]
    exact ⟨finSmoothLift hN m v, toBase_finSmoothLift hN m v⟩
  · have hL : ContDiff ℝ ∞ (finSmoothLift hN m) :=
      (LinearMap.toContinuousLinearMap (finSmoothLift hN m)).contDiff
    refine hL.contDiffOn.congr fun v _ => ?_
    change Function.invFun (E.toBase m) ((((ScBanach.const N).toBase m v : N)) : E 0) =
      finSmoothLift hN m v
    rw [ScBanach.const_toBase]
    apply E.toBase_injective m
    rw [toBase_finSmoothLift, Function.invFun_eq ⟨finSmoothLift hN m v, toBase_finSmoothLift hN m v⟩]

end Inclusion

/-! ### Definition 3.2.1 (preprint 3.25): the tangent germ property -/

namespace MPolyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **Definition 3.2.1 (preprint 3.25) (2), the data at a point `x` of `M`**: a chart `ϕ : (U, x) → (O, 0)` of `X`
onto a tame retract `(O, C, E)`, an `n`-dimensional smooth subspace `N ⊆ E` in good position to `C`
with a good complement `Y` (**added hypothesis: `Y` closed**, the text's sc-complement), a relatively
open neighbourhood `V` of `0` in `N ∩ C` and a continuous map `δ : V → Y` with
(i) `ϕ(M ∩ U) = {v + δ(v) | v ∈ V}` and (ii) `δ` an sc^∞-germ at `0` in the sense of
`IsScInftyGermAt` (`k`-dependent neighbourhoods), `δ(0) = 0`, `Dδ(0) = 0`. -/
structure TangentGermChart (M : Set X) (x : X) (n : ℕ) where
  /-- The chart `ϕ`. -/
  φ : MChart X
  isChart : P.IsChart φ
  mem_source : x ∈ φ.source
  φ_zero : φ x = 0
  tame : IsTameRetract φ.model.E φ.model.C φ.model.O
  /-- The `n`-dimensional subspace `N`. -/
  N : Submodule ℝ (φ.model.E 0)
  finiteDimensional : FiniteDimensional ℝ N
  finrank_eq : finrank ℝ N = n
  smooth : N ≤ φ.model.E.smooth
  goodPosition : IsInGoodPosition φ.model.E φ.model.C N
  /-- The good complement `Y`. -/
  Y : Submodule ℝ (φ.model.E 0)
  goodComplement : IsGoodComplement φ.model.E φ.model.C N Y
  isClosed_Y : IsClosed (Y : Set (φ.model.E 0))
  /-- The relatively open neighbourhood `V` of `0` in `N ∩ C`. -/
  V : Set N
  V_relOpen : ∃ O : Set N, IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' φ.model.C
  zero_mem_V : (0 : N) ∈ V
  /-- The map `δ : V → Y`. -/
  δ : N → φ.model.E 0
  δ_mem_Y : ∀ v, δ v ∈ Y
  continuousOn : ContinuousOn δ V
  image_eq : φ '' (M ∩ φ.source) = (fun v : N => (v : φ.model.E 0) + δ v) '' V
  germ : IsScInftyGermAt (Subtype.val ⁻¹' φ.model.C) δ
  δ_zero : δ 0 = 0
  fderivWithin_zero : fderivWithin ℝ δ (Subtype.val ⁻¹' φ.model.C) 0 = 0

/-- **Definition 3.2.1 (preprint 3.25)**: the subset `M ⊆ X` has the **`n`-dimensional tangent germ property**:
(1) `M ⊆ X_∞`, (2) every point of `M` has the data of `TangentGermChart`. -/
def HasTangentGermProperty (M : Set X) (n : ℕ) : Prop :=
  M ⊆ P.smoothSet ∧ ∀ x ∈ M, Nonempty (P.TangentGermChart M x n)

namespace TangentGermChart

variable {P} {M : Set X} {x : X} {n : ℕ} (d : P.TangentGermChart M x n)

instance : FiniteDimensional ℝ d.N := d.finiteDimensional

/-- `N ∩ C` is a partial quadrant in `N` (Proposition 3.1.25 (preprint 3.22)). -/
theorem isPartialQuadrant : IsPartialQuadrant (ScBanach.const d.N) (Subtype.val ⁻¹' d.φ.model.C) :=
  proposition_3_1_25 d.φ.model.isPartialQuadrant d.goodPosition

/-- `V` is a relatively open subset of the partial quadrant `N ∩ C`. -/
theorem V_isRelOpenInQuadrant :
    IsRelOpenInQuadrant (ScBanach.const d.N) (Subtype.val ⁻¹' d.φ.model.C) d.V :=
  ⟨d.isPartialQuadrant, d.V_relOpen⟩

lemma V_subset : d.V ⊆ Subtype.val ⁻¹' d.φ.model.C := by
  obtain ⟨O, -, hV⟩ := d.V_relOpen; rw [hV]; exact inter_subset_right

/-- `N` and `Y` are topological complements (`Y` closed, `N` finite-dimensional). -/
theorem isTopCompl : Submodule.IsTopCompl d.N d.Y :=
  (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional d.goodComplement.isCompl.symm
    d.isClosed_Y).symm

/-- The projection `π : E → N` along `Y` (continuous since `Y` is closed and `N` finite
dimensional; this is where the added closedness of `Y` is used). -/
def π : d.φ.model.E 0 →L[ℝ] d.N := d.N.projectionOntoL d.Y d.isTopCompl

@[simp] lemma π_apply_coe (v : d.N) : d.π v = v := Submodule.projectionOntoL_apply_left d.isTopCompl v

@[simp] lemma π_apply_Y {y : d.φ.model.E 0} (hy : y ∈ d.Y) : d.π y = 0 :=
  (Submodule.projectionOntoL_apply_eq_zero_iff d.isTopCompl).2 hy

lemma π_graph (v : d.N) : d.π ((v : d.φ.model.E 0) + d.δ v) = v := by
  rw [map_add, π_apply_coe, π_apply_Y d (d.δ_mem_Y v), add_zero]

/-- The graph map `Γ(v) = v + δ(v)`. -/
def Γ : d.N → d.φ.model.E 0 := fun v => (v : d.φ.model.E 0) + d.δ v

lemma Γ_apply (v : d.N) : d.Γ v = (v : d.φ.model.E 0) + d.δ v := rfl

lemma Γ_mem_O {v : d.N} (hv : v ∈ d.V) : d.Γ v ∈ d.φ.model.O := by
  have : d.Γ v ∈ d.φ '' (M ∩ d.φ.source) := by rw [d.image_eq]; exact ⟨v, hv, rfl⟩
  exact d.φ.image_subset_model inter_subset_right this

lemma π_Γ (v : d.N) : d.π (d.Γ v) = v := d.π_graph v

/-- `γ(v) = ϕ⁻¹(v + δ(v)) ∈ M ∩ U` for `v ∈ V`. -/
lemma symm_Γ_mem {v : d.N} (hv : v ∈ d.V) : d.φ.symm (d.Γ v) ∈ M ∩ d.φ.source := by
  have : d.Γ v ∈ d.φ '' (M ∩ d.φ.source) := by rw [d.image_eq]; exact ⟨v, hv, rfl⟩
  obtain ⟨y, hy, hyv⟩ := this
  rw [← hyv, d.φ.symm_apply_apply hy.2]; exact hy

/-- For `y ∈ M ∩ U`, `ϕ(y) = Γ(π ϕ(y))` with `π ϕ(y) ∈ V`. -/
lemma exists_eq_Γ {y : X} (hy : y ∈ M ∩ d.φ.source) : d.π (d.φ y) ∈ d.V ∧ d.φ y = d.Γ (d.π (d.φ y)) := by
  have : d.φ y ∈ (fun v : d.N => (v : d.φ.model.E 0) + d.δ v) '' d.V := by
    rw [← d.image_eq]; exact ⟨y, hy, rfl⟩
  obtain ⟨v, hv, hvy⟩ := this
  have hπ : d.π (d.φ y) = v := by rw [← hvy]; exact d.π_graph v
  exact ⟨hπ ▸ hv, by rw [hπ]; exact hvy.symm⟩

/-- The two conditions under which the text's proof of Theorem 3.2.3 (preprint 3.27) goes through (see the module
docstring): (a) `δ` is sc-smooth on `V` in the set sense; (b) the projection `π` along `Y` maps
the retract `O` into `C` (so that `Σ ∩ O = {z ∈ O | πz ∈ V}` is relatively open in `O`). -/
structure IsRegular : Prop where
  isScSmooth : IsScSmooth (E := ScBanach.const d.N) (F := d.φ.model.E) d.V d.δ
  π_mem : ∀ z ∈ d.φ.model.O, (d.π z : d.φ.model.E 0) ∈ d.φ.model.C

/-- The set `Σ ∩ O = {z ∈ O | πz ∈ V}` of the proof of Theorem 3.2.3 (preprint 3.27). -/
def Sig : Set (d.φ.model.E 0) := {z | z ∈ d.φ.model.O ∧ d.π z ∈ d.V}

/-- The retraction `t(v + w) = v + δ(v)` of the proof of Theorem 3.2.3 (preprint 3.27). -/
def t : d.φ.model.E 0 → d.φ.model.E 0 := fun z => d.Γ (d.π z)

lemma t_apply (z : d.φ.model.E 0) : d.t z = (d.π z : d.φ.model.E 0) + d.δ (d.π z) := rfl

lemma t_mem_Sig {z : d.φ.model.E 0} (hz : z ∈ d.Sig) : d.t z ∈ d.Sig :=
  ⟨d.Γ_mem_O hz.2, by rw [t, π_Γ]; exact hz.2⟩

lemma t_t (z : d.φ.model.E 0) : d.t (d.t z) = d.t z := by
  simp only [t, π_Γ]

lemma t_eq_self_of_mem {y : X} (hy : y ∈ M ∩ d.φ.source) : d.t (d.φ y) = d.φ y :=
  (d.exists_eq_Γ hy).2.symm

/-- The open set `U₀ = ϕ⁻¹(Σ ∩ O) ⊆ U` of `X`. -/
def U₀ : Set X := d.φ.source ∩ d.φ ⁻¹' d.Sig

lemma mem_U₀ : x ∈ d.U₀ := by
  refine ⟨d.mem_source, ?_⟩
  change d.φ x ∈ d.Sig
  rw [d.φ_zero]
  exact ⟨by rw [← d.φ_zero]; exact d.φ.mapsTo_model x d.mem_source, by rw [_root_.map_zero]; exact d.zero_mem_V⟩

lemma Sig_eq (hreg : d.IsRegular) : ∃ O' : Set (d.φ.model.E 0), IsOpen O' ∧ d.Sig = d.φ.model.O ∩ O' := by
  obtain ⟨OV, hOV, hV⟩ := d.V_relOpen
  refine ⟨d.π ⁻¹' OV, hOV.preimage d.π.continuous, ?_⟩
  ext z
  simp only [Sig, mem_ofPred_eq, mem_inter_iff, mem_preimage, hV]
  constructor
  · rintro ⟨hzO, hzV, -⟩; exact ⟨hzO, hzV⟩
  · rintro ⟨hzO, hzV⟩; exact ⟨hzO, hzV, hreg.π_mem z hzO⟩

lemma isOpen_U₀ (hreg : d.IsRegular) : IsOpen d.U₀ := by
  obtain ⟨O', hO', hSig⟩ := d.Sig_eq hreg
  have : d.U₀ = d.φ.source ∩ d.φ ⁻¹' O' := by
    ext y
    simp only [U₀, mem_inter_iff, mem_preimage, hSig]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, d.φ.mapsTo_model y h.1, h.2⟩⟩
  rw [this]
  exact d.φ.continuousOn_toFun.isOpen_inter_preimage d.φ.isOpen_source hO'

lemma image_U₀ : d.φ '' d.U₀ = d.Sig := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy.2
  · intro hz
    refine ⟨d.φ.symm z, ⟨d.φ.symm_mapsTo hz.1, ?_⟩, d.φ.apply_symm_apply hz.1⟩
    change d.φ (d.φ.symm z) ∈ d.Sig
    rwa [d.φ.apply_symm_apply hz.1]

/-- The retraction `s = ϕ⁻¹ ∘ t ∘ ϕ : U₀ → U₀` onto `M ∩ U₀`. -/
def s : X → X := fun y => d.φ.symm (d.t (d.φ y))

lemma s_mem {y : X} (hy : y ∈ d.U₀) : d.s y ∈ M ∩ d.U₀ := by
  have h1 : d.t (d.φ y) ∈ d.Sig := d.t_mem_Sig hy.2
  have h2 : d.φ.symm (d.t (d.φ y)) ∈ M ∩ d.φ.source := d.symm_Γ_mem hy.2.2
  refine ⟨h2.1, h2.2, ?_⟩
  change d.φ (d.φ.symm (d.t (d.φ y))) ∈ d.Sig
  rwa [d.φ.apply_symm_apply h1.1]

lemma s_eq_self {y : X} (hy : y ∈ M ∩ d.U₀) : d.s y = y := by
  rw [s, d.t_eq_self_of_mem ⟨hy.1, hy.2.1⟩, d.φ.symm_apply_apply hy.2.1]

lemma s_s {y : X} (hy : y ∈ d.U₀) : d.s (d.s y) = d.s y := d.s_eq_self (d.s_mem hy)

lemma image_s : d.s '' d.U₀ = M ∩ d.U₀ := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩; exact d.s_mem hz
  · intro hy; exact ⟨y, hy.2, d.s_eq_self hy⟩

/-- The graph map `Γ = ι + δ` is sc-smooth on `V` when `δ` is (set sense). -/
theorem Γ_isScSmooth (hreg : d.IsRegular) :
    IsScSmooth (E := ScBanach.const d.N) (F := d.φ.model.E) d.V d.Γ :=
  IsScSmooth.add d.V_isRelOpenInQuadrant.isScDomain
    (isScSmooth_subtype_val d.smooth d.V_isRelOpenInQuadrant.isScDomain) hreg.isScSmooth

/-- The projection `π` is sc-smooth `E → N` (a continuous linear map into a finite-dimensional
space, Corollary 1.2.5 (preprint 1.20)). -/
theorem π_isScSmooth : IsScSmooth (E := d.φ.model.E) (F := ScBanach.const d.N) univ d.π :=
  IsScSmooth.of_contDiffOn_finiteDimensional (isScDomain_univ _) d.π.contDiff.contDiffOn

/-- **The retraction `t` is sc-smooth `(Σ ∩ O, C, E) → (O, C, E)`**: for a retraction `R` onto
`Σ ∩ O`, `t ∘ R = Γ ∘ π ∘ R` is a composition of sc-smooth maps. -/
theorem t_isScSmoothRetractMap (hreg : d.IsRegular) :
    IsScSmoothRetractMap d.φ.model.E d.φ.model.C d.Sig d.φ.model.E d.φ.model.C d.φ.model.O d.t where
  mapsTo := fun z hz => (d.t_mem_Sig hz).1
  comp_isScSmooth R hR := by
    have hπR : IsScSmooth (E := d.φ.model.E) (F := ScBanach.const d.N) R.U (d.π ∘ R) :=
      IsScSmooth.comp R.isScDomain (isScDomain_univ _) d.π_isScSmooth R.isScSmooth (mapsTo_univ _ _)
    have hmaps : MapsTo (d.π ∘ R) R.U d.V := fun y hy => by
      have : R y ∈ d.Sig := hR ▸ R.apply_mem_retract hy
      exact this.2
    exact IsScSmooth.comp (E := d.φ.model.E) (F := ScBanach.const d.N) (G := d.φ.model.E)
      R.isScDomain d.V_isRelOpenInQuadrant.isScDomain (d.Γ_isScSmooth hreg) hπR hmaps

/-- The retraction `s = ϕ⁻¹ ∘ t ∘ ϕ` is sc-smooth on `U₀` (Definition 2.3.8 (preprint 2.14), in the chart `ϕ`). -/
theorem s_isScSmoothOn (hreg : d.IsRegular) : P.IsScSmoothOn P d.s d.U₀ := by
  have hcont : ContinuousOn d.s d.U₀ := by
    have h1 : ContinuousOn d.t d.Sig :=
      (d.t_isScSmoothRetractMap hreg).continuousOn
        (by obtain ⟨O', hO', hSig⟩ := d.Sig_eq hreg; rw [hSig]; exact proposition_2_3_1_one d.φ.model.isScRetract hO')
    refine d.φ.continuousOn_invFun.comp (h1.comp (d.φ.continuousOn_toFun.mono fun y hy => hy.1) fun y hy => hy.2) ?_
    intro y hy
    exact (d.t_mem_Sig hy.2).1
  refine IsScSmoothOn.of_exists_charts (d.isOpen_U₀ hreg) hcont fun y hy => ?_
  refine ⟨d.φ, d.φ, d.U₀, d.isChart, d.isChart, d.isOpen_U₀ hreg, hy, fun z hz => ⟨hz, hz.1⟩,
    fun z hz => (d.s_mem hz).2.1, ?_⟩
  rw [d.image_U₀]
  refine (d.t_isScSmoothRetractMap hreg).congr fun z hz => ?_
  change d.t z = d.φ (d.φ.symm (d.t (d.φ (d.φ.symm z))))
  rw [d.φ.apply_symm_apply hz.1, d.φ.apply_symm_apply (d.t_mem_Sig hz).1]

end TangentGermChart

/-- **Theorem 3.2.3 (preprint 3.27) (1), first clause**: if every point of `M` has the data of Definition 3.2.1 (preprint 3.25) (2)
satisfying the regularity conditions `IsRegular` (under which the text's proof goes through, see
the module docstring), then `M` is a sub-M-polyfold of `X` (Definition 2.3.18 (preprint 2.20)), with the text's
retraction `s = ϕ⁻¹ ∘ t ∘ ϕ`, `t(v + w) = v + δ(v)`, on `U₀ = ϕ⁻¹(Σ ∩ O)`. -/
theorem _root_.Polyfold.theorem_3_2_3_isSubMPolyfold {M : Set X} {n : ℕ}
    (hM : ∀ x ∈ M, ∃ d : P.TangentGermChart M x n, d.IsRegular) : P.IsSubMPolyfold M := by
  intro a ha
  obtain ⟨d, hreg⟩ := hM a ha
  exact ⟨d.U₀, d.isOpen_U₀ hreg, d.mem_U₀, d.s, fun y hy => (d.s_mem hy).2, d.s_isScSmoothOn hreg,
    fun y hy => d.s_s hy, d.image_s⟩

/-! ### Theorem 3.2.3 (preprint 3.27): the chart `π ∘ ϕ` and the induced structure -/

variable {P}

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **Manifold with boundary with corners of dimension `n`** (Chapter 4 of the text), as far as
Theorem 3.2.3 (preprint 3.27) needs it: the M-polyfold structure has an equivalent atlas all of whose charts are
modelled on relatively open subsets of partial quadrants of finite-dimensional spaces of dimension
`n`; the transition maps are then classically smooth (`isScSmooth_iff_contDiffOn_const`). -/
def IsManifoldWithCorners (Q : MPolyfold X) (n : ℕ) : Prop :=
  ∃ A : MAtlas X, A.Equiv Q.atlas ∧ ∀ χ ∈ A.charts,
    IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O ∧ FiniteDimensional ℝ (χ.model.E 0) ∧
      finrank ℝ (χ.model.E 0) = n

namespace TangentGermChart

variable {M : Set X} {x : X} {n : ℕ} (d : P.TangentGermChart M x n)

/-- The local model `(V, N ∩ C, N)` of the chart `π ∘ ϕ` of `M`. -/
def model : LocalModel :=
  ⟨ScBanach.const d.N, Subtype.val ⁻¹' d.φ.model.C, d.V, d.V_isRelOpenInQuadrant.isScRetract⟩

lemma model_O : d.model.O = d.V := rfl

/-- The model `(V, N ∩ C, N)` is a tame retract (the identity retraction). -/
theorem model_isTameRetract : IsTameRetract d.model.E d.model.C d.model.O :=
  ⟨ScRetraction.id d.V_isRelOpenInQuadrant, image_id _, ScRetraction.id_isTame _⟩

open scoped Classical in
/-- The inverse `γ(v) = ϕ⁻¹(v + δ(v))` of the chart, with the junk value `a₀`. -/
def chartInv (a₀ : M) (v : d.N) : M :=
  if h : v ∈ d.V then ⟨d.φ.symm (d.Γ v), (d.symm_Γ_mem h).1⟩ else a₀

lemma chartInv_val (a₀ : M) {v : d.N} (hv : v ∈ d.V) : (d.chartInv a₀ v).1 = d.φ.symm (d.Γ v) := by
  unfold chartInv; rw [dif_pos hv]

lemma Γ_continuousOn : ContinuousOn d.Γ d.V :=
  continuous_subtype_val.continuousOn.add d.continuousOn

/-- **Theorem 3.2.3 (preprint 3.27) (2), the chart**: `y ↦ π ∘ ϕ(y)` on `M ∩ U₀`, a chart of `M` with the local
model `(V, N ∩ C, N)` (its inverse is `γ(v) = ϕ⁻¹(v + δ(v))`). -/
def chart (hreg : d.IsRegular) (a₀ : M) : MChart M where
  model := d.model
  toPartialEquiv :=
    { toFun := fun y => d.π (d.φ y.1)
      invFun := d.chartInv a₀
      source := {y : M | y.1 ∈ d.U₀}
      target := d.V
      map_source' := fun y hy => hy.2.2
      map_target' := fun (v : d.N) hv => by
        show (d.chartInv a₀ v).1 ∈ d.U₀
        rw [d.chartInv_val a₀ hv]
        refine ⟨(d.symm_Γ_mem hv).2, ?_⟩
        change d.φ (d.φ.symm (d.Γ v)) ∈ d.Sig
        rw [d.φ.apply_symm_apply (d.Γ_mem_O hv)]
        exact ⟨d.Γ_mem_O hv, by rw [π_Γ]; exact hv⟩
      left_inv' := fun y hy => by
        obtain ⟨hv, heq⟩ := d.exists_eq_Γ ⟨y.2, hy.1⟩
        apply Subtype.ext
        rw [d.chartInv_val a₀ hv, ← heq, d.φ.symm_apply_apply hy.1]
      right_inv' := fun (v : d.N) hv => by
        change d.π (d.φ (d.chartInv a₀ v).1) = v
        rw [d.chartInv_val a₀ hv, d.φ.apply_symm_apply (d.Γ_mem_O hv), π_Γ] }
  isOpen_source := (d.isOpen_U₀ hreg).preimage continuous_subtype_val
  target_eq := rfl
  continuousOn_toFun :=
    d.π.continuous.comp_continuousOn
      (d.φ.continuousOn_toFun.comp continuous_subtype_val.continuousOn fun y hy => hy.1)
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    have h1 : ContinuousOn (d.φ.symm ∘ d.Γ) d.V :=
      d.φ.continuousOn_invFun.comp d.Γ_continuousOn fun v hv => d.Γ_mem_O hv
    exact h1.congr fun v hv => by
      change (d.chartInv a₀ v).1 = d.φ.symm (d.Γ v)
      exact d.chartInv_val a₀ hv

variable (hreg : d.IsRegular) (a₀ : M)

lemma chart_source : (d.chart hreg a₀).source = {y : M | y.1 ∈ d.U₀} := rfl

lemma chart_apply (y : M) : d.chart hreg a₀ y = d.π (d.φ y.1) := rfl

lemma chart_symm_apply {v : d.N} (hv : v ∈ d.V) :
    ((d.chart hreg a₀).symm v : X) = d.φ.symm (d.Γ v) := d.chartInv_val a₀ hv

lemma chart_model : (d.chart hreg a₀).model = d.model := rfl

/-- The chart `π ∘ ϕ` is a finite-dimensional corner chart of dimension `n`. -/
theorem chart_isCorner : IsRelOpenInQuadrant (d.chart hreg a₀).model.E (d.chart hreg a₀).model.C
    (d.chart hreg a₀).model.O ∧ FiniteDimensional ℝ ((d.chart hreg a₀).model.E 0) ∧
    finrank ℝ ((d.chart hreg a₀).model.E 0) = n :=
  ⟨d.V_isRelOpenInQuadrant, d.finiteDimensional, d.finrank_eq⟩

/-- The point `x` lies in the source of its chart. -/
lemma mem_chart_source (hx : x ∈ M) : (⟨x, hx⟩ : M) ∈ (d.chart hreg a₀).source := d.mem_U₀

/-! ### Compatibility with the charts of the sub-M-polyfold (Proposition 2.3.19 (preprint 2.21)) -/

/-- The graph map `Γ` as an sc-smooth map between retracts, from a sub-retract `O₁ ⊆ V` of the
model into the retract `O'` of `E` containing its image. -/
theorem Γ_isScSmoothRetractMap (hreg : d.IsRegular) {O₁ : Set d.N} (hO₁ : O₁ ⊆ d.V)
    {O' : Set (d.φ.model.E 0)}
    (hmaps : MapsTo d.Γ O₁ O') :
    IsScSmoothRetractMap (ScBanach.const d.N) (Subtype.val ⁻¹' d.φ.model.C) O₁ d.φ.model.E
      d.φ.model.C O' d.Γ where
  mapsTo := hmaps
  comp_isScSmooth S hS := by
    have hmapsS : MapsTo S S.U d.V := fun u hu => hO₁ (hS ▸ S.apply_mem_retract hu)
    exact IsScSmooth.comp (E := ScBanach.const d.N) (F := ScBanach.const d.N) (G := d.φ.model.E)
      S.isScDomain d.V_isRelOpenInQuadrant.isScDomain (d.Γ_isScSmooth hreg) S.isScSmooth hmapsS

/-- The projection `π` as an sc-smooth map between retracts `(O', C, E) → (univ, univ, N)`. -/
theorem π_isScSmoothRetractMap (O' : Set (d.φ.model.E 0)) (C' : Set d.N) :
    IsScSmoothRetractMap d.φ.model.E d.φ.model.C O' (ScBanach.const d.N) C' univ d.π where
  mapsTo := mapsTo_univ _ _
  comp_isScSmooth R _ :=
    IsScSmooth.comp (E := d.φ.model.E) (F := d.φ.model.E) (G := ScBanach.const d.N) R.isScDomain
      (isScDomain_univ _) d.π_isScSmooth R.isScSmooth (mapsTo_univ _ _)

variable {φ' : MChart X} (d' : P.SubData M) (hφ' : P.IsChart φ') (b₀ : M)

/-- The chart `π ∘ ϕ` of `M` is compatible with every chart of the sub-M-polyfold structure of
Proposition 2.3.19 (preprint 2.21): both transition maps are compositions of the transition map `ϕ' ∘ ϕ⁻¹` of `X`
with `Γ` and `π`. -/
theorem chart_compatible_subChart :
    (d.chart hreg a₀).Compatible (subChart d' hφ' b₀) := by
  set κ := d.chart hreg a₀ with hκ
  set σ := subChart d' hφ' b₀ with hσ
  have hκsrc : ∀ y : M, y ∈ κ.source ↔ y.1 ∈ d.U₀ := fun y => Iff.rfl
  have hσsrc : ∀ y : M, y ∈ σ.source ↔ y.1 ∈ d'.shrink φ' := fun y => Iff.rfl
  have hcompat := d.isChart.compatible hφ' (P := P)
  have hcompat' := hφ'.compatible d.isChart (P := P)
  -- the overlap seen in `κ` lies in `V`, and `Γ` maps it into the overlap of `ϕ` and `ϕ'`
  have hovV : κ.overlap σ ⊆ d.V := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy.1.2.2
  have hΓov : MapsTo d.Γ (κ.overlap σ) (d.φ.overlap φ') := by
    rintro _ ⟨y, hy, rfl⟩
    rw [chart_apply, ← (d.exists_eq_Γ ⟨y.2, hy.1.1⟩).2]
    exact d.φ.mem_overlap φ' hy.1.1 (d'.shrink_subset_source φ' hy.2)
  constructor
  · -- `κ → σ`: `ϕ' ∘ ϕ⁻¹ ∘ Γ`
    have h1 := (hcompat.1.comp (d.Γ_isScSmoothRetractMap hreg hovV hΓov) (d.φ.isScRetract_overlap φ'))
    refine (h1.mono_target ?_).congr ?_
    · rintro _ ⟨y, hy, rfl⟩
      have hκy : (κ y : d.N) = d.π (d.φ y.1) := rfl
      have hΓ : d.Γ (d.π (d.φ y.1)) = d.φ y.1 := (d.exists_eq_Γ ⟨y.2, hy.1.1⟩).2.symm
      change d.φ.transition φ' (d.Γ (κ y)) ∈ σ.overlap κ
      rw [hκy, hΓ, MChart.transition_apply _ _ hy.1.1]
      exact ⟨y, ⟨hy.2, hy.1⟩, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      have hκy : (κ y : d.N) = d.π (d.φ y.1) := rfl
      have hΓ : d.Γ (d.π (d.φ y.1)) = d.φ y.1 := (d.exists_eq_Γ ⟨y.2, hy.1.1⟩).2.symm
      change φ' (d.φ.symm (d.Γ (κ y))) = σ (κ.symm (κ y))
      rw [κ.symm_apply_apply hy.1, hκy, hΓ, d.φ.symm_apply_apply hy.1.1]
      rfl
  · -- `σ → κ`: `π ∘ ϕ ∘ ϕ'⁻¹`
    have hsub : σ.overlap κ ⊆ φ'.overlap d.φ := by
      rintro _ ⟨y, hy, rfl⟩
      exact φ'.mem_overlap d.φ (d'.shrink_subset_source φ' hy.1) hy.2.1
    have h1 := hcompat'.1.mono_source (φ'.isScRetract_overlap d.φ) hsub
    have h2 := (d.π_isScSmoothRetractMap (d.φ.overlap φ') (Subtype.val ⁻¹' d.φ.model.C)).comp h1
      (d.φ.isScRetract_overlap φ')
    show IsScSmoothRetractMap φ'.model.E φ'.model.C (σ.overlap κ) (ScBanach.const d.N)
      (Subtype.val ⁻¹' d.φ.model.C) (κ.overlap σ) (σ.transition κ)
    refine (h2.mono_target ?_).congr ?_
    · rintro _ ⟨y, hy, rfl⟩
      change d.π (φ'.transition d.φ (φ' y.1)) ∈ κ.overlap σ
      rw [MChart.transition_apply _ _ (d'.shrink_subset_source φ' hy.1)]
      exact ⟨y, ⟨hy.2, hy.1⟩, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      change d.π (φ'.transition d.φ (φ' y.1)) = κ (σ.symm (σ y))
      rw [MChart.transition_apply _ _ (d'.shrink_subset_source φ' hy.1), σ.symm_apply_apply hy.1]
      rfl

end TangentGermChart

/-! ### Theorem 3.2.3 (preprint 3.27): the induced structure -/

section Thm327

variable (P) {M : Set X} {n : ℕ}

/-- The charts `π ∘ ϕ` of all the regular data of Definition 3.2.1 (preprint 3.25) (2). -/
def tangentCharts : Set (MChart M) :=
  {κ | ∃ (x : X) (_ : x ∈ M) (d : P.TangentGermChart M x n) (hreg : d.IsRegular) (a₀ : M),
    κ = d.chart hreg a₀}

/-- Every chart `π ∘ ϕ` is a chart of the induced M-polyfold structure of Proposition 2.3.19 (preprint 2.21)
(**Theorem 3.27 (2)**: "a smooth chart on `M` around the point `x`", here: a chart of the
induced structure, modelled on `(V, N ∩ C, N)`). -/
theorem theorem_3_2_3_isChart [ParacompactSpace M]
    (hM : ∀ x ∈ M, ∃ d : P.TangentGermChart M x n, d.IsRegular) {x : X}
    (d : P.TangentGermChart M x n) (hreg : d.IsRegular) (a₀ : M) :
    (subPolyfold (theorem_3_2_3_isSubMPolyfold P hM)).IsChart (d.chart hreg a₀) := by
  rintro _ ⟨d', φ', hφ', b₀, rfl⟩
  exact d.chart_compatible_subChart hreg a₀ d' hφ' b₀

/-- The charts `π ∘ ϕ` are pairwise compatible (through the charts of Proposition 2.3.19 (preprint 2.21)). -/
theorem tangentCharts_compatible [ParacompactSpace M]
    (hM : ∀ x ∈ M, ∃ d : P.TangentGermChart M x n, d.IsRegular) :
    ∀ κ ∈ tangentCharts P (M := M) (n := n), ∀ κ' ∈ tangentCharts P (M := M) (n := n),
      κ.Compatible κ' := by
  rintro _ ⟨x, hx, d, hreg, a₀, rfl⟩ _ ⟨x', hx', d', hreg', a₀', rfl⟩
  have hsub := theorem_3_2_3_isSubMPolyfold P hM
  refine MChart.compatible_of_locally _ _ (subAtlas hsub).charts ?_ ?_ fun y _ => ?_
  · intro χ hχ
    exact theorem_3_2_3_isChart P hM d hreg a₀ χ hχ
  · intro χ hχ
    exact (theorem_3_2_3_isChart P hM d' hreg' a₀' χ hχ).symm
  · exact (subAtlas hsub).cover y

/-- **The atlas of Theorem 3.2.3 (preprint 3.27)**: the charts `π ∘ ϕ`. -/
def germAtlas [ParacompactSpace M] (hM : ∀ x ∈ M, ∃ d : P.TangentGermChart M x n, d.IsRegular)
    (hne : M.Nonempty) : MAtlas M where
  charts := tangentCharts P (M := M) (n := n)
  compatible := tangentCharts_compatible P hM
  cover y := by
    obtain ⟨d, hreg⟩ := hM y.1 y.2
    exact ⟨d.chart hreg ⟨hne.some, hne.some_mem⟩, ⟨y.1, y.2, d, hreg, _, rfl⟩, d.mem_U₀⟩

/-- **Theorem 3.2.3 (preprint 3.27) (1)**, the induced structure: the atlas of the charts `π ∘ ϕ` is equivalent
to the induced atlas of Proposition 2.3.19 (preprint 2.21). -/
theorem theorem_3_2_3_atlas_equiv [ParacompactSpace M]
    (hM : ∀ x ∈ M, ∃ d : P.TangentGermChart M x n, d.IsRegular) (hne : M.Nonempty) :
    (germAtlas P hM hne).Equiv (subPolyfold (theorem_3_2_3_isSubMPolyfold P hM)).atlas := by
  rw [MAtlas.equiv_iff]
  rintro _ ⟨x, hx, d, hreg, a₀, rfl⟩ χ hχ
  exact theorem_3_2_3_isChart P hM d hreg a₀ χ hχ

/-- **Theorem 3.2.3 (preprint 3.27) (1)**: the induced M-polyfold structure on `M` is tame (its charts `π ∘ ϕ` are
modelled on the tame retracts `(V, N ∩ C, N)`). -/
theorem theorem_3_2_3_isTame [ParacompactSpace M]
    (hM : ∀ x ∈ M, ∃ d : P.TangentGermChart M x n, d.IsRegular) (hne : M.Nonempty) :
    (subPolyfold (theorem_3_2_3_isSubMPolyfold P hM)).IsTame := by
  refine ⟨germAtlas P hM hne, theorem_3_2_3_atlas_equiv P hM hne, ?_⟩
  rintro _ ⟨x, hx, d, hreg, a₀, rfl⟩
  exact d.model_isTameRetract

/-- **Theorem 3.2.3 (preprint 3.27) (1)**: the induced M-polyfold structure on `M` is sc-smoothly equivalent to the
structure of an `n`-dimensional manifold with boundary with corners (`IsManifoldWithCorners`). -/
theorem theorem_3_2_3_isManifoldWithCorners [ParacompactSpace M]
    (hM : ∀ x ∈ M, ∃ d : P.TangentGermChart M x n, d.IsRegular) (hne : M.Nonempty) :
    (subPolyfold (theorem_3_2_3_isSubMPolyfold P hM)).IsManifoldWithCorners n := by
  refine ⟨germAtlas P hM hne, theorem_3_2_3_atlas_equiv P hM hne, ?_⟩
  rintro _ ⟨x, hx, d, hreg, a₀, rfl⟩
  exact d.chart_isCorner hreg a₀

/-- **The degeneracy index of `M` in the chart `π ∘ ϕ`** (Theorem 3.2.3 (preprint 3.27) with Lemma 2.4.6 (preprint 2.26) /
Proposition 2.5.6 (preprint 2.36)): since the chart `π ∘ ϕ` has the tame model `(V, N ∩ C, N)`,
`d_M(y) = d_{N ∩ C}(π ∘ ϕ(y))` for `y ∈ M ∩ U₀`.  (Lemma 3.8.13 (preprint 3.70) then gives
`d_{N ∩ C}(v) = d_C(v + δ(v)) = d_X(y)` for `v = π ∘ ϕ(y) ∉ N ∩ W` near `0`, in the model
`E = ℝⁿ ⊕ W`; its transport to a general presentation of `C` is `lemma_3_8_13_general`
(`GapP1_Lemma3813.lean`), and `d_M = d_X` near the centre is `MPolyfold.theorem_3_2_3_degIndex_eq`
(`GapP1_Theorem323Deg.lean`).) -/
theorem theorem_3_2_3_degIndex [ParacompactSpace M]
    (hM : ∀ x ∈ M, ∃ d : P.TangentGermChart M x n, d.IsRegular) {x : X}
    (d : P.TangentGermChart M x n) (hreg : d.IsRegular) (a₀ : M) {y : M} (hy : y.1 ∈ d.U₀) :
    (subPolyfold (theorem_3_2_3_isSubMPolyfold P hM)).degIndex y =
      Polyfold.degIndex (ScBanach.const d.N) (Subtype.val ⁻¹' d.φ.model.C) (d.π (d.φ y.1)) :=
  (subPolyfold (theorem_3_2_3_isSubMPolyfold P hM)).degIndex_eq_chartDegIndex_of_isTameRetract
    (theorem_3_2_3_isChart P hM d hreg a₀) d.model_isTameRetract hy

end Thm327

end MPolyfold

/-- **Theorem 3.2.3 (preprint 3.27)** (under the regularity conditions `IsRegular` at every point, see the module
docstring): a subset `M` of an M-polyfold `X` with the `n`-dimensional tangent germ property is a
sub-M-polyfold of `X` whose induced M-polyfold structure (Proposition 2.3.19 (preprint 2.21)) is tame and equivalent
to the structure of an `n`-dimensional manifold with boundary with corners; the charts are the
maps `y ↦ π ∘ ϕ(y)` of (2). -/
theorem theorem_3_2_3_of_isRegular {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) {M : Set X} {n : ℕ} (hne : M.Nonempty)
    (hM : ∀ x ∈ M, ∃ d : P.TangentGermChart M x n, d.IsRegular) :
    ∃ hsub : P.IsSubMPolyfold M,
      haveI := P.paracompactSpace_subtype M
      (MPolyfold.subPolyfold hsub).IsTame ∧ (MPolyfold.subPolyfold hsub).IsManifoldWithCorners n ∧
      ∀ x (hx : x ∈ M) (d : P.TangentGermChart M x n) (hreg : d.IsRegular) (a₀ : M),
        (MPolyfold.subPolyfold hsub).IsChart (d.chart hreg a₀) ∧
          (⟨x, hx⟩ : M) ∈ (d.chart hreg a₀).source := by
  have := P.paracompactSpace_subtype M
  exact ⟨theorem_3_2_3_isSubMPolyfold P hM, MPolyfold.theorem_3_2_3_isTame P hM hne,
    MPolyfold.theorem_3_2_3_isManifoldWithCorners P hM hne, fun x hx d hreg a₀ =>
      ⟨MPolyfold.theorem_3_2_3_isChart P hM d hreg a₀, d.mem_chart_source hreg a₀ hx⟩⟩


/-! ### Proposition 3.2.2 (preprint 3.26): invariance under sc-diffeomorphisms -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {X' : Type v} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {Q : MPolyfold X'}

@[simp] lemma transportChart_model_E {f : X → X'} {g : X' → X} {U : Set X} {V : Set X'}
    (h : P.IsScDiffeoOn Q f g U V) (ψ : MChart X') : (transportChart h ψ).model.E = ψ.model.E := rfl

@[simp] lemma transportChart_model_C {f : X → X'} {g : X' → X} {U : Set X} {V : Set X'}
    (h : P.IsScDiffeoOn Q f g U V) (ψ : MChart X') : (transportChart h ψ).model.C = ψ.model.C := rfl

lemma transportChart_model_O {f : X → X'} {g : X' → X} {U : Set X} {V : Set X'}
    (h : P.IsScDiffeoOn Q f g U V) (ψ : MChart X') :
    (transportChart h ψ).model.O = ψ '' (V ∩ ψ.source) := rfl

/-- For a global sc-diffeomorphism the transported chart has the model `O` of `ψ`. -/
lemma transportChart_model_O_univ {f : X → X'} {g : X' → X}
    (h : P.IsScDiffeoOn Q f g univ univ) (ψ : MChart X') :
    (transportChart h ψ).model.O = ψ.model.O := by
  rw [transportChart_model_O, univ_inter, ψ.image_source]

namespace TangentGermChart

variable {M : Set X} {x : X} {n : ℕ}

/-- **Proposition 3.2.2 (preprint 3.26), the construction**: the data of Definition 3.2.1 (preprint 3.25) (2) at `x ∈ M` are carried
by an sc-diffeomorphism `ψ : X → X'` (with inverse `ψ'`) to data at `ψ(x) ∈ ψ(M)`: the chart
`ϕ' = ϕ ∘ ψ⁻¹` (`transportChart`), with the same `N`, `Y`, `V`, `δ`. -/
def transport (d : P.TangentGermChart M x n) {ψ : X → X'} {ψ' : X' → X}
    (h : P.IsScDiffeoOn Q ψ ψ' univ univ) : Q.TangentGermChart (ψ '' M) (ψ x) n where
  φ := transportChart h.symm d.φ
  isChart := transportChart_isChart h.symm d.isChart
  mem_source := ⟨mem_univ _, by
    rw [mem_preimage, h.left_inv x (mem_univ _)]; exact d.mem_source⟩
  φ_zero := by
    show d.φ (ψ' (ψ x)) = 0
    rw [h.left_inv x (mem_univ _), d.φ_zero]
  tame := by
    rw [transportChart_model_O_univ]; exact d.tame
  N := d.N
  finiteDimensional := d.finiteDimensional
  finrank_eq := d.finrank_eq
  smooth := d.smooth
  goodPosition := d.goodPosition
  Y := d.Y
  goodComplement := d.goodComplement
  isClosed_Y := d.isClosed_Y
  V := d.V
  V_relOpen := d.V_relOpen
  zero_mem_V := d.zero_mem_V
  δ := d.δ
  δ_mem_Y := d.δ_mem_Y
  continuousOn := d.continuousOn
  image_eq := by
    show (d.φ ∘ ψ') '' (ψ '' M ∩ (univ ∩ ψ' ⁻¹' d.φ.source)) =
      (fun v : d.N => (v : d.φ.model.E 0) + d.δ v) '' d.V
    rw [← d.image_eq, image_comp]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨⟨m, hm, rfl⟩, -, hφ⟩, rfl⟩
      rw [mem_preimage, h.left_inv m (mem_univ _)] at hφ
      rw [h.left_inv m (mem_univ _)]
      exact ⟨hm, hφ⟩
    · rintro ⟨hy, hφ⟩
      refine ⟨ψ y, ⟨⟨y, hy, rfl⟩, mem_univ _, ?_⟩, h.left_inv y (mem_univ _)⟩
      rw [mem_preimage, h.left_inv y (mem_univ _)]; exact hφ
  germ := d.germ
  δ_zero := d.δ_zero
  fderivWithin_zero := d.fderivWithin_zero

end TangentGermChart

end MPolyfold

/-- **Proposition 3.2.2 (preprint 3.26)** (one direction): if `ψ : X → X'` is an sc-diffeomorphism of M-polyfolds
(with inverse `ψ'`) and `M ⊆ X` has the `n`-dimensional tangent germ property, then so does
`ψ(M) ⊆ X'`: `ψ(M) ⊆ X'_∞` since sc-smooth maps preserve the levels, and the data of Definition
3.25 (2) at `ψ(x)` are the chart `ϕ ∘ ψ⁻¹` with the data `N, Y, V, δ` at `x`
(`TangentGermChart.transport`). -/
theorem proposition_3_2_2_image {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {P : MPolyfold X} {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X']
    {Q : MPolyfold X'} {ψ : X → X'} {ψ' : X' → X} (h : P.IsScDiffeoOn Q ψ ψ' univ univ)
    {M : Set X} {n : ℕ} (hM : P.HasTangentGermProperty M n) :
    Q.HasTangentGermProperty (ψ '' M) n := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxs := hM.1 hx
    rw [MPolyfold.smoothSet, mem_iInter] at hxs ⊢
    intro m
    exact (h.isScSmoothOn.mapsTo_levelSet m) ⟨mem_univ _, hxs m⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨d⟩ := hM.2 x hx
    exact ⟨d.transport h⟩

/-- **Proposition 3.2.2 (preprint 3.26)**: the `n`-dimensional tangent germ property is invariant under
sc-diffeomorphisms: if `ψ : X → X'` is an sc-diffeomorphism (with inverse `ψ'`) and
`ψ(M) = M'`, then `M'` has the `n`-dimensional tangent germ property if and only if `M` has it. -/
theorem proposition_3_2_2 {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {P : MPolyfold X} {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X']
    {Q : MPolyfold X'} {ψ : X → X'} {ψ' : X' → X} (h : P.IsScDiffeoOn Q ψ ψ' univ univ)
    {M : Set X} {M' : Set X'} (hM : ψ '' M = M') {n : ℕ} :
    Q.HasTangentGermProperty M' n ↔ P.HasTangentGermProperty M n := by
  constructor
  · intro hM'
    have h1 := proposition_3_2_2_image h.symm hM'
    have hψ'M' : ψ' '' M' = M := by
      rw [← hM, image_image]
      conv_rhs => rw [← image_id M]
      exact image_congr fun x _ => h.left_inv x (mem_univ _)
    rwa [hψ'M'] at h1
  · intro hMP
    rw [← hM]; exact proposition_3_2_2_image h hMP

end Polyfold
