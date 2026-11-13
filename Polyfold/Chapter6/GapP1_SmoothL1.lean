import Polyfold.Chapter1.ExpositionLemmas

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, the bundle `L` of
Lemma 6.6.5 (p. 265; preprint Lemma 6.30, p. 222), gap G.62: the first analytic inputs for `L` as
a *smooth* vector bundle.

# sc-smooth maps from finite dimensions, and the regularity of finite-dimensional ranges

## What is formalized

* `IsScSmooth.contDiffOn_levelMap_const` (**an sc-smooth map from `ℝⁿ` is `C^∞` into every
  level**): for a finite-dimensional `V` with its constant sc-structure and an sc-domain `U ⊆ V`,
  an sc-smooth `f : U → F` maps `U` into every `F_m`, and `f : U → F_m` is `C^∞` for every `m`.
  This is Proposition 1.2.3 (`IsScSmooth.contDiffOn_levels`): `f : U_{m+k} → F_m` is `C^k`, and
  for the constant structure `U_{m+k} = U` and the inclusions are the identity
  (`ScBanach.const_inclK_apply`).  The converse is Proposition 1.2.4
  (`IsScSmooth.of_contDiffOn_levels`); together: `isScSmooth_const_iff`.
* `isScSmooth_tangentLift`: for an sc-smooth `H : U → E` (`U ⊆ ℝⁿ`) and a smooth point `b ∈ E_∞`,
  `q ↦ (H(q), b)`, with `H(q)` read on level `1`, is sc-smooth into `TE = E¹ ⊕ E`.
* `IsSc1With.apply_mem_smooth_of_finiteDimensional` (**regularity of finite-dimensional
  ranges**): if `x` lies on every level of `U` and `Df(x) : E₀ → F₀` has finite-dimensional range,
  then that range consists of smooth points.  `Df(x)` maps `E_m` into `F_m`
  (`IsSc1With.toBase_levelDeriv`), `E_m` is dense in `E₀`, and a finite-dimensional subspace is
  closed.  For an sc-retraction this says that the tangent spaces at smooth points of a
  finite-dimensional retract consist of smooth points.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

section Const

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {F : ScBanach}

/-- For the constant structure the inclusions `E_{m+k} → E_m` are the identity. -/
lemma ScBanach.const_inclK_apply (m : ℕ) : ∀ (k : ℕ) (x : V), (ScBanach.const V).inclK m k x = x
  | 0, _ => rfl
  | k + 1, x => ScBanach.const_inclK_apply m k x

/-- **An sc-smooth map from a finite-dimensional space is `C^∞` into every level** (from
Proposition 1.2.3 (preprint 1.18)): for an sc-domain `U` of `V` with the constant structure and
an sc-smooth `f`, the level map `f : U → F_m` is `C^∞`, for every `m`. -/
theorem IsScSmooth.contDiffOn_levelMap_const {U : Set V} (hU : IsScDomain (ScBanach.const V) U)
    {f : (ScBanach.const V) 0 → F 0} (hf : IsScSmooth U f) (m : ℕ) :
    ContDiffOn ℝ ∞ (fun x : V => levelMap f m x) U := by
  rw [contDiffOn_infty]
  intro k
  have h := hf.contDiffOn_levels hU m k
  rw [ScBanach.lvlSet_const] at h
  refine h.congr fun x _ => ?_
  change levelMap f m x = levelMap f m ((ScBanach.const V).inclK m k x)
  rw [ScBanach.const_inclK_apply]

/-- The level-`0` case: an sc-smooth map from `V` is `C^∞` into `F₀`. -/
theorem IsScSmooth.contDiffOn_const {U : Set V} (hU : IsScDomain (ScBanach.const V) U)
    {f : (ScBanach.const V) 0 → F 0} (hf : IsScSmooth U f) :
    ContDiffOn ℝ ∞ (fun x : V => f x) U :=
  (hf.contDiffOn_levelMap_const hU 0).congr fun x _ => (levelMap_zero f x).symm

/-- An sc⁰ map from `V` maps `U` into every level. -/
theorem IsSc0.mem_range_const {U : Set V} {f : (ScBanach.const V) 0 → F 0}
    (hf : IsSc0 (ScBanach.const V) F U f) (m : ℕ) {x : V} (hx : x ∈ U) :
    f x ∈ range (F.toBase m) := by
  have h := hf.mem_range m x (by rwa [ScBanach.lvlSet_const])
  rwa [ScBanach.const_toBase] at h

/-- On level `m`, the level map of an sc⁰ map from `V` lies over `f`. -/
theorem IsSc0.toBase_levelMap_const {U : Set V} {f : (ScBanach.const V) 0 → F 0}
    (hf : IsSc0 (ScBanach.const V) F U f) (m : ℕ) {x : V} (hx : x ∈ U) :
    F.toBase m (levelMap f m x) = f x := by
  have h := hf.toBase_levelMap (m := m) (x := x) (by rwa [ScBanach.lvlSet_const])
  rwa [ScBanach.const_toBase] at h

/-- **sc-smooth from a finite-dimensional space ⇔ `C^∞` into every level** (Propositions 1.2.3
and 1.2.4 (preprint 1.18, 1.19)). -/
theorem isScSmooth_const_iff {U : Set V} (hU : IsScDomain (ScBanach.const V) U)
    {f : (ScBanach.const V) 0 → F 0} :
    IsScSmooth U f ↔ (∀ m, ∀ x ∈ U, f x ∈ range (F.toBase m)) ∧
      ∀ m, ContDiffOn ℝ ∞ (fun x : V => levelMap f m x) U := by
  refine ⟨fun hf => ⟨fun m x hx => hf.isSc1.isSc0.mem_range_const m hx,
    hf.contDiffOn_levelMap_const hU⟩, fun ⟨h1, h2⟩ => ?_⟩
  refine IsScSmooth.of_contDiffOn_levels hU (fun m x hx => ?_) fun m => ?_
  · rw [ScBanach.const_toBase]
    exact h1 m x (by rwa [ScBanach.lvlSet_const] at hx)
  · rw [ScBanach.lvlSet_const]; exact h2 m

/-- The level-`1` reading of a map into `E`, as a map into `E¹`. -/
theorem IsSc0.shift_toBase_levelMap_const {E : ScBanach} {U : Set V}
    {H : (ScBanach.const V) 0 → E 0} (hH : IsSc0 (ScBanach.const V) E U H) (m : ℕ) {x : V}
    (hx : x ∈ U) :
    E.shift.toBase m (levelMap H (m + 1) x) = levelMap H 1 x := by
  apply E.toBase_injective 1
  rw [← E.shift_toBase, hH.toBase_levelMap_const (m + 1) hx, hH.toBase_levelMap_const 1 hx]

/-- **The lift `q ↦ (H(q), b)` into the tangent is sc-smooth**: for an sc-smooth `H : U → E` on an
sc-domain `U ⊆ V` and a smooth point `b ∈ E_∞`, the map `q ↦ (H(q), b) ∈ TE = E¹ ⊕ E` (with `H(q)`
read on level `1`) is sc-smooth. -/
theorem isScSmooth_tangentLift {E : ScBanach} {U : Set V} (hU : IsScDomain (ScBanach.const V) U)
    {H : (ScBanach.const V) 0 → E 0} (hH : IsScSmooth U H) {b : E 0} (hb : b ∈ E.smooth) :
    IsScSmooth (E := ScBanach.const V) (F := E.tangent) U
      fun q : V => ((levelMap H 1 q, b) : E.tangent 0) := by
  have h0 := hH.isSc1.isSc0
  choose bl hbl using (E.mem_smooth_iff).1 hb
  have hlev : ∀ m, ∀ q ∈ U, levelMap (E := ScBanach.const V) (F := E.tangent)
      (fun q : V => ((levelMap H 1 q, b) : E.tangent 0)) m q =
        ((levelMap H (m + 1) q, bl m) : E.tangent m) := fun m q hq => by
    apply levelMap_eq_of_toBase_eq
    rw [ScBanach.tangent_toBase, ScBanach.const_toBase]
    exact Prod.ext (h0.shift_toBase_levelMap_const m hq) (hbl m)
  refine (isScSmooth_const_iff hU).2 ⟨fun m q hq => ?_, fun m => ?_⟩
  · refine ⟨((levelMap H (m + 1) q, bl m) : E.tangent m), ?_⟩
    rw [ScBanach.tangent_toBase]
    exact Prod.ext (h0.shift_toBase_levelMap_const m hq) (hbl m)
  · refine ContDiffOn.congr ?_ (hlev m)
    exact (hH.contDiffOn_levelMap_const hU (m + 1)).prodMk contDiffOn_const

end Const

/-! ### Regularity of finite-dimensional ranges -/

section Regularity

variable {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0} {D : E 1 → E 0 →L[ℝ] F 0}

/-- `E_m` is dense in `E₀`. -/
theorem ScBanach.dense_range_toBase (E : ScBanach) (m : ℕ) : Dense (range (E.toBase m)) :=
  (E.dense_smooth 0).mono fun _ hx => (E.mem_smooth_iff).1 hx m

/-- **A continuous linear map with finite-dimensional range that maps `E_m` into `F_m` maps `E₀`
into `F_m`**: the image of the dense subspace `E_m` is a subspace of the finite-dimensional range,
hence closed, and it contains the image of the closure. -/
theorem range_subset_range_toBase_of_finiteDimensional (T : E 0 →L[ℝ] F 0)
    [FiniteDimensional ℝ (LinearMap.range (T : E 0 →ₗ[ℝ] F 0))] (m : ℕ)
    (hT : ∀ v : E m, T (E.toBase m v) ∈ range (F.toBase m)) (v : E 0) :
    T v ∈ range (F.toBase m) := by
  set A : Submodule ℝ (F 0) :=
    (LinearMap.range (E.toBase m : E m →ₗ[ℝ] E 0)).map (T : E 0 →ₗ[ℝ] F 0) with hAdef
  have hAle : A ≤ LinearMap.range (T : E 0 →ₗ[ℝ] F 0) := LinearMap.map_le_range
  have : FiniteDimensional ℝ A := Submodule.finiteDimensional_of_le hAle
  have hAc : IsClosed (A : Set (F 0)) := Submodule.closed_of_finiteDimensional A
  have hmem : T v ∈ (A : Set (F 0)) := by
    have hv : v ∈ closure (range (E.toBase m)) := (E.dense_range_toBase m).closure_eq ▸ mem_univ v
    have h1 := map_mem_closure T.continuous hv (t := (A : Set (F 0))) (by
      rintro _ ⟨w, rfl⟩
      exact ⟨E.toBase m w, ⟨w, rfl⟩, rfl⟩)
    rwa [hAc.closure_eq] at h1
  obtain ⟨_, ⟨w, rfl⟩, hw⟩ := hmem
  exact hw ▸ hT w

/-- **Regularity of finite-dimensional ranges**: if `x ∈ U₁` lies on every level of `U` and
`Df(x)` has finite-dimensional range, then `Df(x) v` is a smooth point for every `v ∈ E₀`. -/
theorem IsSc1With.apply_mem_smooth_of_finiteDimensional (h : IsSc1With U f D) {x : E 1}
    (hx : ∀ m, ∃ y ∈ E.lvlSet U (m + 1), E.shift.toBase m y = x)
    [FiniteDimensional ℝ (LinearMap.range (D x : E 0 →ₗ[ℝ] F 0))] (v : E 0) :
    D x v ∈ F.smooth := by
  refine (F.mem_smooth_iff).2 fun m => ?_
  obtain ⟨y, hyU, rfl⟩ := hx m
  refine range_subset_range_toBase_of_finiteDimensional (D (E.shift.toBase m y)) m
    (fun w => ⟨levelDeriv D m y w, h.toBase_levelDeriv hyU w⟩) v

end Regularity

end Polyfold
