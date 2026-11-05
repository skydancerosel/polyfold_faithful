import Polyfold.Chapter3.BasicClassComposition
import Polyfold.Chapter2.Metrizable
import Polyfold.Chapter2.StrongBundleOne
import Polyfold.Chapter2.TangentMap

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §5.2, the
paragraph before **Corollary 5.8** ("a sc-smooth section `f` of the strong bundle `Y → X` defines,
by raising the index, a sc-smooth section `f^i` of `Y^i → X^i`"), with the paragraph after
Definition 2.14 (the M-polyfold `X¹`) and Definitions 2.47–2.52 (strong bundles).

# The shifted strong bundle `P¹ : Y¹ → X¹`

## The text, paraphrased

(Before Corollary 5.8) An sc-smooth section `f` of `Y → X` defines, by raising the index, an
sc-smooth section `f^i` of `Y^i → X^i`.  (Corollary 5.8) `f^i` is an sc-Fredholm section of
`P^i : Y^i → X^i`.  The text never defines `Y^i → X^i` (only `X^i`, after Definition 2.14, and
`Y[i]`, `i = 0, 1`, after Definition 2.51).

## What is formalized

* `IsStrongBundleRetraction.shift` (the index raise `R¹ = strongShift R` of a strong bundle
  retraction is one on `U¹ ◁ F¹`), `strongShift_image` (`R¹(U¹ ◁ F¹) = K_{1,1}`),
  `shift_baseRetraction_retract` (`r¹(U¹) = O¹`).
* `StrongBundleChart.fiberCLE`, `StrongBundleChart.isBanachable_fiber`: the fibre `P⁻¹(x)` of a
  strong bundle chart is linearly homeomorphic to the closed subspace `K_{φ(x)}` of `F₀`
  (hence Banachable); `StrongBundleChart.continuousOn_proj`.
* `MPolyfold.mem_shift_levelSet_iff`, `MPolyfold.mem_shift_smoothSet_iff`: **`(X¹)_m = X_{m+1}`**
  and `(X¹)_∞ = X_∞` (part of gap G.6).
* `MPolyfold.IsScSmoothMap.levelOne`: **an sc-smooth map `X → Z` induces an sc-smooth map
  `X¹ → Z¹`** (the text's "raising the index"; Proposition 1.17 in level charts).
* `StrongBundle.ShiftSpace` (**`Y¹ = Y_{1,1}`**, the level `Y[0]_1` with its level topology),
  `StrongBundle.shiftProj` (**`P¹`**), the fibres `StrongBundle.shiftFiberSubmodule`
  (`P⁻¹(x) ∩ Y_{1,1}`) with the instances `shiftFiber_addCommGroup`, `shiftFiber_module`.
* `StrongBundleChart.shift` (**the index raise `Φ¹ : P¹⁻¹(V¹) → K¹ ⊆ U¹ ◁ F¹` of a strong bundle
  chart**: base chart the level chart `φ¹`, fibre model `F¹`, retraction `R¹`, bundle chart the
  level chart of `Φ` as a chart of `Y[0]`), with `shift_K` (`K¹ = K_{1,1}`), `shift_overlap`,
  `shift_transition`, `toBase_shift_apply`; `StrongBundleChart.Compatible.shift`
  (**compatible charts have compatible index raises**, `[0]` and `[1]` by Proposition 1.17, the
  `F₁`-condition by the level-`1` property of `[1]`).
* `StrongBundle.shift` (**the strong bundle `P¹ : Y¹ → X¹`**, Definition 2.51: continuous
  surjective projection, Banachable fibres, the atlas `shiftAtlas` of the index raises),
  `StrongBundle.isChart_shift`, `StrongBundle.isChart_shift_toMPolyfold0_iff` (**`Y¹[0] = Y[0]¹`**
  as M-polyfolds), `StrongBundle.mem_shift_doubleLevel_iff` (**`(Y¹)_{m,k} = Y_{m+1,k+1}`**).
* `StrongBundle.sectionShift` (**`f¹`**), `StrongBundle.IsScSmoothSection.shift` (**`f¹` is an
  sc-smooth section of `P¹`**), `isZeroAt_sectionShift_iff`, `solutionSet_sectionShift`,
  `regularizing_sectionShift` (`f¹` regularizing when `f` is).

## What the text leaves implicit, and the choices made

* **The definition of `Y^i`.**  `Y¹` is read as the text's double filtration shifted by one,
  `(Y¹)_{m,k} = Y_{m+1,k+1}` (the convention of `E¹`, `(U ◁ F)¹ = U¹ ◁ F¹`): the total space is
  `Y_{1,1}` (not `Y_{0,1} = Y[1]`, nor `Y_{1,2}`), so that `f¹ = f|_{X₁}` takes values in it for
  every sc-smooth `f` (sc-smooth sections map `X_m` into `Y_{m,m}`).  Its topology is that of the
  level `Y[0]_1` of the M-polyfold `Y[0]` (the paragraph after Definition 2.14), which is the
  topology making the charts `Φ¹` homeomorphisms onto `K_{1,1} ⊆ E₁ ⊕ F₁`; Hausdorff and
  paracompact by Theorem 2.16 for `Y[0]`.
* **The fibres.**  `P¹⁻¹(x) = P⁻¹(x) ∩ Y_{1,1}` is a linear subspace of `P⁻¹(x)` (in a chart it is
  the preimage of `F₁` under the linear fibre map), and gets the induced linear structure; its
  Banachable topology is the one of `Y¹`, which is that of `F₁` in a chart (not the subspace
  topology from `P⁻¹(x)`).
* **The charts.**  Strong bundle charts are shifted with a junk value for the inverse (as for
  `MPolyfold.levelChart`); the atlas of `P¹` consists of the index raises of the charts of the atlas
  of `P`, and the index raise of any chart of `P` is a chart of `P¹` (`isChart_shift`).
* **Tameness** is not shifted: `ScRetraction.IsTame` quantifies over *all* presentations of the
  partial quadrant `C¹ ⊆ E¹`, which are not all index raises of presentations of `C`; showing that
  the base retraction `r¹` is tame needs the presentation independence of the degeneracy index and
  of the minimal subspace `E_x` for `C¹`, and that `A ∩ E₁` is an sc-complement of `T_xO¹` when `A`
  is one of `T_xO`.  Not done (no counterexample either).
* **`i ≥ 2`.**  The construction applies to `P¹` itself (`B.shift.shift`), so every fixed `i` is an
  iterate; a uniform family `P^i` indexed by `i` would need a dependent type of strong bundles and
  the identification `(X¹)¹ = X²` as topological spaces (the sets agree by
  `mem_shift_levelSet_iff`), which is not formalized.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

/-! ### The index raise of a strong bundle retraction -/

section Retraction

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

namespace IsStrongBundleRetraction

variable (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
include hU hR

/-- **The index raise of a strong bundle retraction** `R : U ◁ F → U ◁ F` is a strong bundle
retraction `R¹ = strongShift R` on `U¹ ◁ F¹` (the shifted structures `E¹`, `F¹`): a strong bundle
map by `IsStrongBundleMap.shift` (Proposition 1.17), idempotent because `ι R¹ = R ι`. -/
theorem shift :
    IsStrongBundleRetraction (E := E.shift) (F := F.shift) (E.lvlSet U 1) (strongShift R) :=
  { hR.toIsStrongBundleMap.shift hU with
    idem := fun p hp => by
      have hm := (hR.toIsStrongBundleMap.shift hU).mapsTo hp
      apply (E.prod F).toBase_injective 1
      rw [hR.toIsStrongBundleMap.toBase_strongShift hm.1,
        hR.toIsStrongBundleMap.toBase_strongShift hp.1]
      exact hR.idem _ ⟨by rw [ScBanach.prod_toBase]; exact hp.1, mem_univ _⟩ }

omit hU in
/-- `ι R¹(p) = R(ι p)` on `U₁ ⊕ F₁`. -/
lemma toBase_strongShift {p : E 1 × F 1} (hp : E.toBase 1 p.1 ∈ U) :
    (E.prod F).toBase 1 (strongShift R p) = R ((E.prod F).toBase 1 p) :=
  hR.toIsStrongBundleMap.toBase_strongShift hp

omit hU in
/-- `R¹(U¹ ◁ F¹) = K_{1,1}`: the image of the shifted retraction is the level-`1` part of
`K = R(U ◁ F)` in `(E ⊕ F)¹ = E¹ ⊕ F¹`. -/
theorem strongShift_image :
    strongShift R '' (E.lvlSet U 1 ×ˢ (univ : Set (F 1))) =
      (E.prod F).lvlSet (R '' (U ×ˢ univ)) 1 := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [ScBanach.mem_lvlSet, hR.toBase_strongShift hq.1]
    exact ⟨_, ⟨by rw [ScBanach.prod_toBase]; exact hq.1, mem_univ _⟩, rfl⟩
  · intro hp
    rw [ScBanach.mem_lvlSet] at hp
    obtain ⟨q, hq, hqp⟩ := hp
    have hpU : E.toBase 1 p.1 ∈ U := by
      have := (hR.mapsTo hq).1
      rw [hqp, ScBanach.prod_toBase] at this
      exact this
    refine ⟨p, ⟨hpU, mem_univ _⟩, (E.prod F).toBase_injective 1 ?_⟩
    rw [hR.toBase_strongShift hpU, ← hqp, hR.idem q hq]

/-- The base retraction of `R¹` has the retract `O¹ = O ∩ E₁` (`r¹(U¹) = r(U)¹`). -/
theorem shift_baseRetraction_retract :
    ((hR.shift hU).baseRetraction hU.shift).retract =
      E.lvlSet ((hR.baseRetraction hU).retract) 1 := by
  have hb : ∀ {u : E 1}, E.toBase 1 u ∈ U →
      E.toBase 1 ((hR.shift hU).baseRetraction hU.shift u) = hR.baseRetraction hU (E.toBase 1 u) :=
    fun hu => hR.toIsStrongBundleMap.toBase_base_strongShift hu
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [ScBanach.mem_lvlSet, hb hu]
    exact (hR.baseRetraction hU).apply_mem_retract hu
  · intro hz
    have hzU : E.toBase 1 z ∈ U := (hR.baseRetraction hU).retract_subset hz
    refine ⟨z, hzU, E.toBase_injective 1 ?_⟩
    rw [hb hzU]
    exact (hR.baseRetraction hU).apply_eq_self_of_mem_retract hz

end IsStrongBundleRetraction

end Retraction

/-! ### The fibres of a strong bundle chart are Banachable -/

section FiberBanach

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundleChart

variable (c : StrongBundleChart PX P)

/-- The fibre `K_u = {h | (u, h) ∈ K} = {h | Γ(u, h) = h}` of the local strong bundle retract over
`u ∈ O`, as a submodule of `F₀` (the fixed space of the projection `Γ(u, ·)`). -/
def fiberK {u : c.φ.model.E 0} (hu : u ∈ c.U) : Submodule ℝ (c.F 0) :=
  LinearMap.ker ((IsLinearMap.mk' _ (c.isRetraction.fiber_linear u hu)) - LinearMap.id)

/-- `h ∈ K_u` iff `Γ(u, h) = h`. -/
lemma mem_fiberK_iff {u : c.φ.model.E 0} (hu : u ∈ c.U) {h : c.F 0} :
    h ∈ c.fiberK hu ↔ (c.R (u, h)).2 = h := by
  rw [fiberK, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

/-- `O ⊆ U` for a strong bundle chart. -/
lemma O_subset_U : c.φ.model.O ⊆ c.U := by
  rw [← c.base_retract]; exact (c.isRetraction.baseRetraction c.relOpen).retract_subset

/-- `(u, h) ∈ K` iff `Γ(u, h) = h`, for `u ∈ O`. -/
lemma mem_K_iff {u : c.φ.model.E 0} (huO : u ∈ c.φ.model.O) {h : c.F 0} :
    (u, h) ∈ c.K ↔ (c.R (u, h)).2 = h := by
  rw [StrongBundleChart.K, c.isRetraction.mem_image_iff c.relOpen, c.base_retract]
  exact ⟨fun h' => h'.2, fun h' => ⟨huO, h'⟩⟩

/-- The fibre `K_u` is closed in `F₀`: `Γ(u, ·)` is continuous (`R` is sc⁰ on level `0`). -/
lemma isClosed_fiberK {u : c.φ.model.E 0} (hu : u ∈ c.U) :
    IsClosed (c.fiberK hu : Set (c.F 0)) := by
  have hR : ContinuousOn c.R (c.U ×ˢ univ) :=
    c.isRetraction.isScSmooth_zero.isSc1.isSc0.continuousOn_base
  have hc : Continuous fun h : c.F 0 => (c.R (u, h)).2 :=
    continuous_snd.comp (hR.comp_continuous (continuous_const.prodMk continuous_id)
      fun _ => ⟨hu, mem_univ _⟩)
  have : (c.fiberK hu : Set (c.F 0)) = {h | (c.R (u, h)).2 = h} := by
    ext h; exact c.mem_fiberK_iff hu
  rw [this]
  exact isClosed_eq hc continuous_id

/-- A point of the fibre `P⁻¹(x)` lies in the source of the chart. -/
lemma mem_source_of_fiber {x : X} (hx : x ∈ c.φ.source) (v : P ⁻¹' {x}) :
    (v : Y) ∈ c.toPartialEquiv.source := by
  rw [c.source_eq, mem_preimage, show P v = x from v.2]; exact hx

/-- `Φ(v) = (φ(x), Φ(v)₂)` for `v` in the fibre over `x`. -/
lemma apply_fiber {x : X} (hx : x ∈ c.φ.source) (v : P ⁻¹' {x}) :
    c (v : Y) = (c.φ x, (c (v : Y)).2) :=
  Prod.ext (by rw [c.covers _ (c.mem_source_of_fiber hx v), show P v = x from v.2]) rfl

/-- The fibre component of `Φ(v)`, `v ∈ P⁻¹(x)`, lies in `K_{φ(x)}`. -/
lemma snd_mem_fiberK {x : X} (hx : x ∈ c.φ.source) (v : P ⁻¹' {x}) :
    (c (v : Y)).2 ∈ c.fiberK (c.O_subset_U (c.φ.mapsTo_model x hx)) := by
  rw [c.mem_fiberK_iff, ← c.mem_K_iff (c.φ.mapsTo_model x hx), ← c.apply_fiber hx v,
    ← c.image_source]
  exact ⟨_, c.mem_source_of_fiber hx v, rfl⟩

/-- `Φ⁻¹(φ(x), h)` lies in the fibre over `x` for `h ∈ K_{φ(x)}`. -/
lemma symm_mem_fiber {x : X} (hx : x ∈ c.φ.source) {h : c.F 0}
    (hh : h ∈ c.fiberK (c.O_subset_U (c.φ.mapsTo_model x hx))) :
    c.toPartialEquiv.symm (c.φ x, h) ∈ P ⁻¹' {x} := by
  have hK : (c.φ x, h) ∈ c.toPartialEquiv.target := by
    rw [c.target_eq]
    exact (c.mem_K_iff (c.φ.mapsTo_model x hx)).2 ((c.mem_fiberK_iff _).1 hh)
  have hs := c.toPartialEquiv.map_target hK
  have h1 := c.covers _ hs
  rw [c.toPartialEquiv.right_inv hK] at h1
  have hs' : P (c.toPartialEquiv.symm (c.φ x, h)) ∈ c.φ.source := by
    rw [c.source_eq] at hs; exact hs
  exact c.φ.toPartialEquiv.injOn hs' hx h1.symm

/-- **The fibre `P⁻¹(x)` is linearly homeomorphic to the closed subspace `K_{φ(x)}` of `F₀`**
through the strong bundle chart (Definition 2.50: `Φ` is a homeomorphism, linear on the fibres). -/
def fiberCLE {x : X} (hx : x ∈ c.φ.source) :
    (P ⁻¹' {x}) ≃L[ℝ] c.fiberK (c.O_subset_U (c.φ.mapsTo_model x hx)) where
  toFun v := ⟨(c (v : Y)).2, c.snd_mem_fiberK hx v⟩
  invFun h := ⟨c.toPartialEquiv.symm (c.φ x, h), c.symm_mem_fiber hx h.2⟩
  map_add' v w := Subtype.ext ((c.fiber_linear x hx).map_add v w)
  map_smul' a v := Subtype.ext ((c.fiber_linear x hx).map_smul a v)
  left_inv v := by
    apply Subtype.ext
    change c.toPartialEquiv.symm (c.φ x, (c (v : Y)).2) = v
    rw [← c.apply_fiber hx v]
    exact c.toPartialEquiv.left_inv (c.mem_source_of_fiber hx v)
  right_inv h := by
    apply Subtype.ext
    change (c (c.toPartialEquiv.symm (c.φ x, (h : c.F 0)))).2 = h
    have hK : (c.φ x, (h : c.F 0)) ∈ c.toPartialEquiv.target := by
      rw [c.target_eq]
      exact (c.mem_K_iff (c.φ.mapsTo_model x hx)).2 ((c.mem_fiberK_iff _).1 h.2)
    rw [c.toPartialEquiv.right_inv hK]
  continuous_toFun := (c.continuous_fiber x hx).subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine c.continuousOn_invFun.comp_continuous
      (continuous_const.prodMk continuous_subtype_val) fun h => ?_
    rw [c.target_eq]
    exact (c.mem_K_iff (c.φ.mapsTo_model x hx)).2 ((c.mem_fiberK_iff _).1 h.2)

/-- The projection is continuous on the source of a strong bundle chart:
`P = φ⁻¹ ∘ pr₁ ∘ Φ` there. -/
lemma continuousOn_proj : ContinuousOn P c.toPartialEquiv.source := by
  have h1 : ContinuousOn (fun y => c.φ.symm (c y).1) c.toPartialEquiv.source :=
    c.φ.continuousOn_invFun.comp (continuous_fst.comp_continuousOn c.continuousOn_toFun)
      fun y hy => by
        rw [c.covers y hy]
        exact c.φ.mapsTo_model _ (by rw [c.source_eq] at hy; exact hy)
  refine h1.congr fun y hy => ?_
  have hPy : P y ∈ c.φ.source := by rw [c.source_eq] at hy; exact hy
  simp only [c.covers y hy, c.φ.symm_apply_apply hPy]

/-- **The fibres of a strong bundle chart are Banachable**: `P⁻¹(x) ≅ K_{φ(x)}`, a closed subspace
of the Banach space `F₀` (Definition 2.50; used for the shifted strong bundle). -/
theorem isBanachable_fiber {x : X} (hx : x ∈ c.φ.source) : IsBanachable (P ⁻¹' {x}) := by
  have : CompleteSpace (c.fiberK (c.O_subset_U (c.φ.mapsTo_model x hx))) :=
    (c.isClosed_fiberK _).completeSpace_coe
  exact ⟨c.fiberK (c.O_subset_U (c.φ.mapsTo_model x hx)), inferInstance, inferInstance,
    inferInstance, ⟨c.fiberCLE hx⟩⟩

end StrongBundleChart

end FiberBanach

/-! ### The levels of `X¹`: `(X¹)_m = X_{m+1}` -/

/-- `z ∈ E_1` lies in `(E¹)_m` iff `ι z ∈ E_{m+1}`. -/
lemma ScBanach.mem_range_shift_toBase_iff (E : ScBanach) {m : ℕ} (z : E 1) :
    z ∈ range (E.shift.toBase m) ↔ E.toBase 1 z ∈ range (E.toBase (m + 1)) := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, E.shift_toBase m w⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, E.toBase_injective 1 (by rw [← E.shift_toBase, hw])⟩

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **The levels of the M-polyfold `X¹` are those of `X` shifted by one**: `(X¹)_m = X_{m+1}`
(the paragraph after Definition 2.14; part of gap G.6). -/
theorem mem_shift_levelSet_iff {m : ℕ} (x : PX.Level 1) :
    x ∈ PX.shift.levelSet m ↔ PX.levelVal 1 x ∈ PX.levelSet (m + 1) := by
  obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source (PX.levelVal 1 x)
  rw [PX.shift.mem_levelSet_iff (PX.shift_isChart hφ x) (show x ∈ (levelChart hφ x).source from hx),
    PX.mem_levelSet_iff hφ hx, levelChart_apply]
  change levelLift φ 1 (PX.levelVal 1 x) ∈ range (φ.model.E.shift.toBase m) ↔ _
  rw [ScBanach.mem_range_shift_toBase_iff, PX.toBase_levelLift hφ hx (levelVal_mem x)]

/-- `(X¹)_∞ = X_∞`. -/
theorem mem_shift_smoothSet_iff (x : PX.Level 1) :
    x ∈ PX.shift.smoothSet ↔ PX.levelVal 1 x ∈ PX.smoothSet := by
  simp only [MPolyfold.smoothSet, mem_iInter, mem_shift_levelSet_iff]
  constructor
  · intro h m
    cases m with
    | zero => rw [PX.levelSet_zero]; exact mem_univ _
    | succ m => exact h m
  · intro h m; exact h (m + 1)

/-! ### Raising the index of an sc-smooth map -/

section LevelMap

variable {Z : Type v} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}
  {f : X → Z} {f₁ : PX.Level 1 → Q.Level 1}

/-- The level chart maps `V ∩ X₁` onto `φ(V)¹ = φ(V) ∩ E₁`. -/
lemma levelChart_image_preimage {φ : MChart X} (hφ : PX.IsChart φ) (x₀ : PX.Level 1) {V : Set X}
    (hVφ : V ⊆ φ.source) :
    levelChart hφ x₀ '' {x | PX.levelVal 1 x ∈ V} = φ.model.E.lvlSet (φ '' V) 1 := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change φ.model.E.toBase 1 (levelLift φ 1 (PX.levelVal 1 x)) ∈ φ '' V
    rw [PX.toBase_levelLift hφ (hVφ hx) (levelVal_mem x)]
    exact ⟨_, hx, rfl⟩
  · intro hz
    obtain ⟨v, hv, hvz⟩ := hz
    have hzO : φ.model.E.toBase 1 z ∈ φ.model.O := by rw [← hvz]; exact φ.mapsTo_model v (hVφ hv)
    refine ⟨(levelChart hφ x₀).symm z, ?_, (levelChart hφ x₀).apply_symm_apply hzO⟩
    change PX.levelVal 1 ((levelChart hφ x₀).symm z) ∈ V
    rw [levelChart_symm_apply hφ x₀ hzO, ← hvz, φ.symm_apply_apply (hVφ hv)]
    exact hv

/-- The local representative of `f₁` in level charts is the level-`1` map of the local
representative of `f`. -/
lemma levelChart_apply_levelOne (hf₁ : ∀ x, Q.levelVal 1 (f₁ x) = f (PX.levelVal 1 x))
    {φ : MChart X} {ψ : MChart Z} (hφ : PX.IsChart φ) (hψ : Q.IsChart ψ) (x₀ : PX.Level 1)
    (z₀ : Q.Level 1) {x : PX.Level 1} (hx : PX.levelVal 1 x ∈ φ.source)
    (hfx : f (PX.levelVal 1 x) ∈ ψ.source) :
    levelChart hψ z₀ (f₁ x) = levelMap (ψ ∘ f ∘ φ.symm) 1 (levelChart hφ x₀ x) := by
  symm
  apply levelMap_eq_of_toBase_eq
  have hfx' : Q.levelVal 1 (f₁ x) ∈ ψ.source := by rw [hf₁]; exact hfx
  rw [levelChart_apply, levelChart_apply, Q.toBase_levelLift hψ hfx' (levelVal_mem _),
    PX.toBase_levelLift hφ hx (levelVal_mem _), hf₁]
  simp only [Function.comp_apply, φ.symm_apply_apply hx]

/-- **Raising the index of an sc-smooth map** (the text's "a sc-smooth section `f` ... defines,
by raising the index, a sc-smooth section `f^i`", before Corollary 5.8; Proposition 1.17 in
charts): an sc-smooth map `f : X → Z` between M-polyfolds induces an sc-smooth map
`f₁ : X¹ → Z¹` between the level M-polyfolds (any `f₁` with `f₁(x) = f(x)` as points of `Z`).  In
the level charts the local representative of `f₁` is the level-`1` map of that of `f`. -/
theorem IsScSmoothMap.levelOne (hf : PX.IsScSmoothMap Q f)
    (hf₁ : ∀ x, Q.levelVal 1 (f₁ x) = f (PX.levelVal 1 x)) :
    PX.shift.IsScSmoothMap Q.shift f₁ := by
  have hfc : Continuous f := continuousOn_univ.1 hf.continuousOn
  -- the local data at `x`: charts `φ ∋ x`, `ψ ∋ f(x)`, `V = dom φ ∩ f⁻¹(dom ψ)`
  have data : ∀ x : PX.Level 1, ∃ (φ : MChart X) (ψ : MChart Z) (hφ : PX.IsChart φ)
      (hψ : Q.IsChart ψ), PX.levelVal 1 x ∈ φ.source ∧ f (PX.levelVal 1 x) ∈ ψ.source := by
    intro x
    obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source (PX.levelVal 1 x)
    obtain ⟨ψ, hψ, hfx⟩ := Q.exists_isChart_mem_source (f (PX.levelVal 1 x))
    exact ⟨φ, ψ, hφ, hψ, hx, hfx⟩
  have local_ : ∀ {φ : MChart X} {ψ : MChart Z} (hφ : PX.IsChart φ) (hψ : Q.IsChart ψ)
      (x₀ : PX.Level 1) (z₀ : Q.Level 1),
      IsOpen {x : PX.Level 1 | PX.levelVal 1 x ∈ φ.source ∩ f ⁻¹' ψ.source} ∧
      ContinuousOn f₁ {x : PX.Level 1 | PX.levelVal 1 x ∈ φ.source ∩ f ⁻¹' ψ.source} ∧
      IsScSmoothRetractMap (levelChart hφ x₀).model.E (levelChart hφ x₀).model.C
        (levelChart hφ x₀ '' {x : PX.Level 1 | PX.levelVal 1 x ∈ φ.source ∩ f ⁻¹' ψ.source})
        (levelChart hψ z₀).model.E (levelChart hψ z₀).model.C (levelChart hψ z₀).model.O
        (levelChart hψ z₀ ∘ f₁ ∘ (levelChart hφ x₀).symm) := by
    intro φ ψ hφ hψ x₀ z₀
    set V := φ.source ∩ f ⁻¹' ψ.source with hVdef
    have hV : IsOpen V := φ.isOpen_source.inter (ψ.isOpen_source.preimage hfc)
    have hVφ : V ⊆ φ.source := inter_subset_left
    have hsm := hf.smooth φ ψ hφ hψ V hV (fun x hx => ⟨mem_univ _, hx.1⟩) fun x hx => hx.2
    have hO := φ.isScRetract_image hVφ hV
    have hrep : ∀ x : PX.Level 1, PX.levelVal 1 x ∈ V →
        levelChart hψ z₀ (f₁ x) = levelMap (ψ ∘ f ∘ φ.symm) 1 (levelChart hφ x₀ x) :=
      fun x hx => levelChart_apply_levelOne hf₁ hφ hψ x₀ z₀ hx.1 hx.2
    have hmaps : MapsTo (levelChart hφ x₀) {x : PX.Level 1 | PX.levelVal 1 x ∈ V}
        (φ.model.E.lvlSet (φ '' V) 1) := fun x hx => by
      rw [← levelChart_image_preimage hφ x₀ hVφ]; exact ⟨x, hx, rfl⟩
    refine ⟨(continuous_levelVal 1).isOpen_preimage _ hV, ?_, ?_⟩
    · -- `f₁ = (ψ¹)⁻¹ ∘ (ψ ∘ f ∘ φ⁻¹)₁ ∘ φ¹` on `V¹`
      have h1 : ContinuousOn (fun x => (levelChart hψ z₀).symm
          (levelMap (ψ ∘ f ∘ φ.symm) 1 (levelChart hφ x₀ x)))
          {x : PX.Level 1 | PX.levelVal 1 x ∈ V} :=
        (levelChart hψ z₀).continuousOn_invFun.comp
          ((hsm.continuousOn_levelMap hO 1).comp
            ((levelChart hφ x₀).continuousOn_toFun.mono fun x hx => hx.1) hmaps)
          fun x hx => hsm.mapsTo_levelMap hO 1 (hmaps hx)
      refine h1.congr fun x hx => ?_
      have hfx : f₁ x ∈ (levelChart hψ z₀).source := by
        change Q.levelVal 1 (f₁ x) ∈ ψ.source
        rw [hf₁]; exact hx.2
      simp only
      rw [← hrep x hx, (levelChart hψ z₀).symm_apply_apply hfx]
    · rw [levelChart_image_preimage hφ x₀ hVφ]
      refine (hsm.shift hO).congr fun z hz => ?_
      have hzO : φ.model.E.toBase 1 z ∈ φ.model.O := φ.image_subset_model hVφ hz
      have hx : PX.levelVal 1 ((levelChart hφ x₀).symm z) ∈ V := by
        rw [levelChart_symm_apply hφ x₀ hzO]
        obtain ⟨v, hv, hvz⟩ := hz
        rw [← hvz, φ.symm_apply_apply (hVφ hv)]
        exact hv
      have e := hrep _ hx
      rw [(levelChart hφ x₀).apply_symm_apply (z := z) hzO] at e
      exact e.symm
  refine IsScSmoothOn.of_exists_charts isOpen_univ ?_ fun x _ => ?_
  · refine continuousOn_univ.2 (continuous_iff_continuousAt.2 fun x => ?_)
    obtain ⟨φ, ψ, hφ, hψ, hx, hfx⟩ := data x
    obtain ⟨hV1, hcont, -⟩ := local_ hφ hψ x (f₁ x)
    exact hcont.continuousAt (hV1.mem_nhds ⟨hx, hfx⟩)
  · obtain ⟨φ, ψ, hφ, hψ, hx, hfx⟩ := data x
    obtain ⟨hV1, -, hsm⟩ := local_ hφ hψ x (f₁ x)
    refine ⟨levelChart hφ x, levelChart hψ (f₁ x), _, PX.shift_isChart hφ x,
      Q.shift_isChart hψ (f₁ x), hV1, ⟨hx, hfx⟩, fun x' hx' => ⟨mem_univ _, hx'.1⟩,
      fun x' hx' => ?_, hsm⟩
    change Q.levelVal 1 (f₁ x') ∈ ψ.source
    rw [hf₁]; exact hx'.2

end LevelMap

end MPolyfold

/-! ### The total space `Y¹` and the projection `P¹ : Y¹ → X¹` -/

section Bundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)

namespace StrongBundle

variable {B} in
/-- `y ∈ Y[0]_m` iff `Φ(y) ∈ E_m ⊕ F_m`, in any strong bundle chart of `P` around `y` (the level
sets of the M-polyfold `Y[0]` are the diagonal `Y_{m,m}` of the double filtration). -/
lemma mem_levelSet0_iff {c : StrongBundleChart PX P} (hc : B.IsChart c) {y : Y}
    (hy : y ∈ c.toPartialEquiv.source) {m : ℕ} :
    y ∈ B.toMPolyfold0.levelSet m ↔
      (c y).1 ∈ range (c.φ.model.E.toBase m) ∧ (c y).2 ∈ range (c.F.toBase m) := by
  rw [B.toMPolyfold0.mem_levelSet_iff hc.toMChart hy]
  change c y ∈ range ((c.φ.model.E.prod c.F).toBase m) ↔ _
  constructor
  · rintro ⟨w, hw⟩
    rw [ScBanach.prod_toBase] at hw
    exact ⟨⟨w.1, congrArg Prod.fst hw⟩, ⟨w.2, congrArg Prod.snd hw⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨((a, b) : (c.φ.model.E.prod c.F) m), by rw [ScBanach.prod_toBase]; exact Prod.ext ha hb⟩

/-- `P` maps `Y[0]_m` into `X_m` (`P[0]` is sc-smooth). -/
lemma proj_mem_levelSet {y : Y} {m : ℕ} (hy : y ∈ B.toMPolyfold0.levelSet m) :
    P y ∈ PX.levelSet m :=
  B.isScSmoothMap_proj.mapsTo_levelSet m hy

/-- For `x ∈ X₁` and `v ∈ P⁻¹(x)`: `v ∈ Y_{1,1}` iff the fibre component `Φ(v)₂` lies in `F₁`. -/
lemma mem_levelSet0_one_iff_of_fiber {c : StrongBundleChart PX P} (hc : B.IsChart c) {x : X}
    (hx : x ∈ c.φ.source) (hx1 : x ∈ PX.levelSet 1) (v : P ⁻¹' {x}) :
    (v : Y) ∈ B.toMPolyfold0.levelSet 1 ↔ (c (v : Y)).2 ∈ range (c.F.toBase 1) := by
  rw [B.mem_levelSet0_iff hc (c.mem_source_of_fiber hx v), c.apply_fiber hx v]
  exact ⟨fun h => h.2, fun h => ⟨(PX.mem_levelSet_iff c.isChart hx).1 hx1, h⟩⟩

/-- **The total space `Y¹` of the shifted strong bundle**: the level `Y_{1,1} = Y[0]_1` of the
M-polyfold `Y[0]` with its level topology (the paragraph after Definition 2.14), i.e. the
underlying space of the M-polyfold `Y[0]¹`.  Hausdorff and paracompact (Theorem 2.16). -/
abbrev ShiftSpace : Type v := B.toMPolyfold0.Level 1

/-- **The projection `P¹ : Y¹ → X¹`**, `y ↦ P(y)` (`P` maps `Y_{1,1}` into `X₁`). -/
def shiftProj (y : B.ShiftSpace) : PX.Level 1 :=
  PX.levelMk 1 (P (B.toMPolyfold0.levelVal 1 y)) (B.proj_mem_levelSet (MPolyfold.levelVal_mem y))

/-- `P¹(y) = P(y)` as points of `X`. -/
@[simp] lemma levelVal_shiftProj (y : B.ShiftSpace) :
    PX.levelVal 1 (B.shiftProj y) = P (B.toMPolyfold0.levelVal 1 y) := rfl

/-- The fibre `P¹⁻¹(x) = P⁻¹(x) ∩ Y_{1,1}` over `x ∈ X¹`, a submodule of `P⁻¹(x)`. -/
def shiftFiberSubmodule (x : PX.Level 1) : Submodule ℝ (P ⁻¹' {PX.levelVal 1 x}) where
  carrier := {v | (v : Y) ∈ B.toMPolyfold0.levelSet 1}
  add_mem' {v w} hv hw := by
    obtain ⟨c, hc, hxc⟩ := B.exists_chart_mem (PX.levelVal 1 x)
    have hc' := B.isChart_of_mem hc
    have hx1 := MPolyfold.levelVal_mem x
    simp only [mem_ofPred_eq] at hv hw ⊢
    rw [B.mem_levelSet0_one_iff_of_fiber hc' hxc hx1] at hv hw ⊢
    obtain ⟨a, ha⟩ := hv
    obtain ⟨b, hb⟩ := hw
    exact ⟨a + b, by rw [map_add, ha, hb, c.snd_add hxc]⟩
  zero_mem' := by
    obtain ⟨c, hc, hxc⟩ := B.exists_chart_mem (PX.levelVal 1 x)
    simp only [mem_ofPred_eq]
    rw [B.mem_levelSet0_one_iff_of_fiber (B.isChart_of_mem hc) hxc (MPolyfold.levelVal_mem x)]
    exact ⟨0, by rw [map_zero]; exact ((c.fiber_linear _ hxc).map_zero).symm⟩
  smul_mem' a {v} hv := by
    obtain ⟨c, hc, hxc⟩ := B.exists_chart_mem (PX.levelVal 1 x)
    have hc' := B.isChart_of_mem hc
    simp only [mem_ofPred_eq] at hv ⊢
    rw [B.mem_levelSet0_one_iff_of_fiber hc' hxc (MPolyfold.levelVal_mem x)] at hv ⊢
    obtain ⟨b, hb⟩ := hv
    exact ⟨a • b, by rw [map_smul, hb]; exact ((c.fiber_linear _ hxc).map_smul a v).symm⟩

/-- The fibre of `P¹` over `x` as the submodule `P⁻¹(x) ∩ Y_{1,1}` of `P⁻¹(x)`. -/
def shiftFiberEquiv (x : PX.Level 1) : B.shiftProj ⁻¹' {x} ≃ B.shiftFiberSubmodule x where
  toFun y := ⟨⟨B.toMPolyfold0.levelVal 1 (y : B.ShiftSpace), by
      change P _ = PX.levelVal 1 x
      exact congrArg (PX.levelVal 1) (show B.shiftProj y = x from y.2)⟩,
    MPolyfold.levelVal_mem (y : B.ShiftSpace)⟩
  invFun v := ⟨B.toMPolyfold0.levelMk 1 v.1.1 v.2, MPolyfold.level_ext (P := PX) v.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The additive group of the fibre `P¹⁻¹(x) = P⁻¹(x) ∩ Y_{1,1}`. -/
instance shiftFiber_addCommGroup (x : PX.Level 1) : AddCommGroup (B.shiftProj ⁻¹' {x}) :=
  (B.shiftFiberEquiv x).addCommGroup

/-- The real vector space structure of the fibre `P¹⁻¹(x)`. -/
instance shiftFiber_module (x : PX.Level 1) : Module ℝ (B.shiftProj ⁻¹' {x}) :=
  (B.shiftFiberEquiv x).module ℝ

/-- The identification of the fibres of `P¹` is additive. -/
lemma shiftFiberEquiv_add (x : PX.Level 1) (v w : B.shiftProj ⁻¹' {x}) :
    B.shiftFiberEquiv x (v + w) = B.shiftFiberEquiv x v + B.shiftFiberEquiv x w :=
  (B.shiftFiberEquiv x).apply_symm_apply _

/-- The identification of the fibres of `P¹` is homogeneous. -/
lemma shiftFiberEquiv_smul (x : PX.Level 1) (a : ℝ) (v : B.shiftProj ⁻¹' {x}) :
    B.shiftFiberEquiv x (a • v) = a • B.shiftFiberEquiv x v :=
  (B.shiftFiberEquiv x).apply_symm_apply _

/-- The sum in the fibre of `P¹` is the sum in the fibre of `P`. -/
lemma levelVal_shiftFiber_add (x : PX.Level 1) (v w : B.shiftProj ⁻¹' {x}) :
    B.toMPolyfold0.levelVal 1 ((v + w : B.shiftProj ⁻¹' {x}) : B.ShiftSpace) =
      (((B.shiftFiberEquiv x v : P ⁻¹' {PX.levelVal 1 x}) +
        (B.shiftFiberEquiv x w : P ⁻¹' {PX.levelVal 1 x}) : P ⁻¹' {PX.levelVal 1 x}) : Y) := by
  have := congrArg (fun z : B.shiftFiberSubmodule x => ((z : P ⁻¹' {PX.levelVal 1 x}) : Y))
    (B.shiftFiberEquiv_add x v w)
  exact this

/-- The scalar multiple in the fibre of `P¹` is that in the fibre of `P`. -/
lemma levelVal_shiftFiber_smul (x : PX.Level 1) (a : ℝ) (v : B.shiftProj ⁻¹' {x}) :
    B.toMPolyfold0.levelVal 1 ((a • v : B.shiftProj ⁻¹' {x}) : B.ShiftSpace) =
      ((a • (B.shiftFiberEquiv x v : P ⁻¹' {PX.levelVal 1 x}) : P ⁻¹' {PX.levelVal 1 x}) : Y) := by
  have := congrArg (fun z : B.shiftFiberSubmodule x => ((z : P ⁻¹' {PX.levelVal 1 x}) : Y))
    (B.shiftFiberEquiv_smul x a v)
  exact this

end StrongBundle

/-! ### The shifted strong bundle charts `Φ¹ : P¹⁻¹(V¹) → K¹ ⊆ U¹ ◁ F¹` -/

namespace StrongBundleChart

variable {B} {c : StrongBundleChart PX P} (hc : B.IsChart c) (y₀ : B.ShiftSpace)

/-- `ι Φ¹(y) = Φ(y)`: the level chart of `Y[0]` lifts `Φ` to `E₁ ⊕ F₁`. -/
lemma toBase_levelChart {y : B.ShiftSpace}
    (hy : B.toMPolyfold0.levelVal 1 y ∈ c.toPartialEquiv.source) :
    (c.φ.model.E.prod c.F).toBase 1 (MPolyfold.levelChart hc.toMChart y₀ y) =
      c (B.toMPolyfold0.levelVal 1 y) :=
  B.toMPolyfold0.toBase_levelLift hc.toMChart hy (MPolyfold.levelVal_mem y)

/-- The base component of `ι Φ¹(y) = Φ(y)`. -/
lemma toBase_levelChart_fst {y : B.ShiftSpace}
    (hy : B.toMPolyfold0.levelVal 1 y ∈ c.toPartialEquiv.source) :
    c.φ.model.E.toBase 1 (MPolyfold.levelChart hc.toMChart y₀ y).1 =
      (c (B.toMPolyfold0.levelVal 1 y)).1 := by
  exact congrArg Prod.fst (toBase_levelChart hc y₀ hy)

/-- The fibre component of `ι Φ¹(y) = Φ(y)`. -/
lemma toBase_levelChart_snd {y : B.ShiftSpace}
    (hy : B.toMPolyfold0.levelVal 1 y ∈ c.toPartialEquiv.source) :
    c.F.toBase 1 (MPolyfold.levelChart hc.toMChart y₀ y).2 =
      (c (B.toMPolyfold0.levelVal 1 y)).2 := by
  exact congrArg Prod.snd (toBase_levelChart hc y₀ hy)

/-- A point of the fibre of `P¹` over `x ∈ V¹` lies in `P⁻¹(V)`. -/
lemma levelVal_mem_source_of_fiber {x : PX.Level 1} (hx : PX.levelVal 1 x ∈ c.φ.source)
    (v : B.shiftProj ⁻¹' {x}) :
    B.toMPolyfold0.levelVal 1 (v : B.ShiftSpace) ∈ c.toPartialEquiv.source := by
  rw [c.source_eq, mem_preimage, ← B.levelVal_shiftProj, show B.shiftProj v = x from v.2]
  exact hx

/-- `Φ¹` covers the level chart `φ¹` (Definition 2.50 for `Φ¹`). -/
lemma shift_covers (y : B.ShiftSpace)
    (hy : y ∈ (MPolyfold.levelChart hc.toMChart y₀).toPartialEquiv.source) :
    (MPolyfold.levelChart hc.toMChart y₀ y).1 =
      MPolyfold.levelChart c.isChart (B.shiftProj y₀) (B.shiftProj y) := by
  have hy' : B.toMPolyfold0.levelVal 1 y ∈ c.toPartialEquiv.source := hy
  have hPy : PX.levelVal 1 (B.shiftProj y) ∈ c.φ.source := by
    rw [B.levelVal_shiftProj, ← mem_preimage, ← c.source_eq]; exact hy'
  apply c.φ.model.E.toBase_injective 1
  rw [toBase_levelChart_fst hc y₀ hy', MPolyfold.levelChart_apply,
    PX.toBase_levelLift c.isChart hPy (MPolyfold.levelVal_mem _), c.covers _ hy']
  rfl

/-- `Φ¹` is linear on the fibres of `P¹` (Definition 2.50 for `Φ¹`). -/
lemma shift_fiber_linear (x : PX.Level 1) (hx : PX.levelVal 1 x ∈ c.φ.source) :
    IsLinearMap ℝ fun v : B.shiftProj ⁻¹' {x} =>
      (MPolyfold.levelChart hc.toMChart y₀ (v : B.ShiftSpace)).2 := by
  have key : ∀ v : B.shiftProj ⁻¹' {x},
      c.F.toBase 1 (MPolyfold.levelChart hc.toMChart y₀ (v : B.ShiftSpace)).2 =
        (c (B.toMPolyfold0.levelVal 1 (v : B.ShiftSpace))).2 :=
    fun v => toBase_levelChart_snd hc y₀ (levelVal_mem_source_of_fiber hx v)
  refine ⟨fun v w => c.F.toBase_injective 1 ?_, fun a v => c.F.toBase_injective 1 ?_⟩
  · rw [map_add, key, key, key, B.levelVal_shiftFiber_add]
    exact c.snd_add hx _ _
  · rw [map_smul, key, key, B.levelVal_shiftFiber_smul]
    exact (c.fiber_linear _ hx).map_smul a _

/-- **The shifted strong bundle chart** `(Φ¹, P¹⁻¹(V¹), K¹, U¹ ◁ F¹)` of `P¹ : Y¹ → X¹` (the
index raise of the strong bundle chart `Φ` of `P`): the base chart is the level chart
`φ¹ : V₁ → O₁` of `X¹`, the fibre model `F¹`, the strong bundle retraction `R¹ = strongShift R` on
`U¹ ◁ F¹`, and the bundle chart is the level chart `Φ¹ : P⁻¹(V) ∩ Y_{1,1} → K_{1,1}` of the
M-polyfold `Y[0]` (junk value `y₀` for the inverse). -/
def shift : StrongBundleChart PX.shift B.shiftProj where
  φ := MPolyfold.levelChart c.isChart (B.shiftProj y₀)
  isChart := PX.shift_isChart c.isChart _
  F := c.F.shift
  U := c.φ.model.E.lvlSet c.U 1
  R := strongShift c.R
  relOpen := c.relOpen.shift
  isRetraction := c.isRetraction.shift c.relOpen
  base_retract := by
    have h := c.isRetraction.shift_baseRetraction_retract c.relOpen
    rw [c.base_retract] at h
    exact h
  toPartialEquiv := (MPolyfold.levelChart hc.toMChart y₀).toPartialEquiv
  source_eq := by
    ext y
    change B.toMPolyfold0.levelVal 1 y ∈ c.toPartialEquiv.source ↔
      P (B.toMPolyfold0.levelVal 1 y) ∈ c.φ.source
    rw [c.source_eq]; rfl
  target_eq := c.isRetraction.strongShift_image.symm
  continuousOn_toFun := (MPolyfold.levelChart hc.toMChart y₀).continuousOn_toFun
  continuousOn_invFun := (MPolyfold.levelChart hc.toMChart y₀).continuousOn_invFun
  covers := shift_covers hc y₀
  fiber_linear := shift_fiber_linear hc y₀

/-- The base chart of `Φ¹` is the level chart `φ¹`. -/
@[simp] lemma shift_φ : (c.shift hc y₀).φ = MPolyfold.levelChart c.isChart (B.shiftProj y₀) := rfl
/-- The fibre model of `Φ¹` is `F¹`. -/
@[simp] lemma shift_F : (c.shift hc y₀).F = c.F.shift := rfl
/-- The domain of `R¹` is `U¹ = U ∩ E₁`. -/
@[simp] lemma shift_U : (c.shift hc y₀).U = c.φ.model.E.lvlSet c.U 1 := rfl
/-- The strong bundle retraction of `Φ¹` is `R¹`. -/
@[simp] lemma shift_R : (c.shift hc y₀).R = strongShift c.R := rfl

/-- `Φ¹(y)` is the lift of `Φ(y)` to `E₁ ⊕ F₁`. -/
lemma shift_apply (y : B.ShiftSpace) :
    c.shift hc y₀ y =
      MPolyfold.levelLift (c.toMChart B.continuous) 1 (B.toMPolyfold0.levelVal 1 y) :=
  rfl

/-- The domain of `Φ¹` is `P⁻¹(V) ∩ Y_{1,1}`. -/
lemma shift_source :
    (c.shift hc y₀).toPartialEquiv.source =
      {y | B.toMPolyfold0.levelVal 1 y ∈ c.toPartialEquiv.source} := rfl

/-- `K¹ = K_{1,1}`, the level-`1` part of `K`. -/
lemma shift_K : (c.shift hc y₀).K = (c.φ.model.E.prod c.F).lvlSet c.K 1 :=
  c.isRetraction.strongShift_image

/-- `ι Φ¹(y) = Φ(y)` on `P¹⁻¹(V¹)`. -/
lemma toBase_shift_apply {y : B.ShiftSpace}
    (hy : y ∈ (c.shift hc y₀).toPartialEquiv.source) :
    (c.φ.model.E.prod c.F).toBase 1 (c.shift hc y₀ y) = c (B.toMPolyfold0.levelVal 1 y) :=
  toBase_levelChart hc y₀ hy

/-- The base component of `ι Φ¹(y) = Φ(y)`. -/
lemma toBase_shift_apply_fst {y : B.ShiftSpace}
    (hy : y ∈ (c.shift hc y₀).toPartialEquiv.source) :
    c.φ.model.E.toBase 1 (c.shift hc y₀ y).1 = (c (B.toMPolyfold0.levelVal 1 y)).1 :=
  toBase_levelChart_fst hc y₀ hy

/-- The fibre component of `ι Φ¹(y) = Φ(y)`. -/
lemma toBase_shift_apply_snd {y : B.ShiftSpace}
    (hy : y ∈ (c.shift hc y₀).toPartialEquiv.source) :
    c.F.toBase 1 (c.shift hc y₀ y).2 = (c (B.toMPolyfold0.levelVal 1 y)).2 :=
  toBase_levelChart_snd hc y₀ hy

variable {c' : StrongBundleChart PX P} (hc' : B.IsChart c') (y₀' : B.ShiftSpace)

/-- The overlap of shifted charts is the level-`1` part of the overlap. -/
lemma shift_overlap :
    (c.shift hc y₀).overlap (c'.shift hc' y₀') =
      (c.φ.model.E.prod c.F).lvlSet (c.overlap c') 1 :=
  MPolyfold.levelChart_overlap hc.toMChart y₀ hc'.toMChart y₀'

/-- The transition map of shifted charts is the level-`1` map of the transition map. -/
lemma shift_transition {z : (c.φ.model.E.prod c.F) 1}
    (hz : (c.φ.model.E.prod c.F).toBase 1 z ∈ c.K) :
    (c.shift hc y₀).transition (c'.shift hc' y₀') z =
      levelMap (E := c.φ.model.E.prod c.F) (F := c'.φ.model.E.prod c'.F) (c.transition c') 1 z :=
  MPolyfold.levelChart_transition hc.toMChart y₀ hc'.toMChart y₀' hz

/-- `[1]` of a shifted overlap: `K¹[1]`-overlap `= ((K[1])-overlap)¹`. -/
lemma strongShiftOne_shift_overlap :
    strongShiftOne ((c.shift hc y₀).overlap (c'.shift hc' y₀')) =
      (c.φ.model.E.prod c.F.shift).lvlSet (strongShiftOne (c.overlap c')) 1 := by
  rw [shift_overlap]
  rfl

variable {hc y₀ hc' y₀'}

/-- The key computation for `[1]` of the shifted charts: for `p ∈ K¹[1]`-overlap (fibre
component in `F₂`), the shifted transition maps `(p₁, ι p₂)` to a point with fibre component in
`F'₂`, and `[1]` of the shifted transition is the level-`1` map of `[1]` of the transition. -/
lemma shift_transition_one (h : c.Compatible c')
    {p : ((c.shift hc y₀).φ.model.E.prod (c.shift hc y₀).F.shift) 0}
    (hp : p ∈ strongShiftOne ((c.shift hc y₀).overlap (c'.shift hc' y₀'))) :
    ((c.shift hc y₀).transition (c'.shift hc' y₀') (p.1, c.F.shift.toBase 1 p.2)).2 ∈
        range (c'.F.shift.toBase 1) ∧
      shiftFiber ((c.shift hc y₀).transition (c'.shift hc' y₀')) p =
        levelMap (E := c.φ.model.E.prod c.F.shift) (F := c'.φ.model.E.prod c'.F.shift)
          (shiftFiber (c.transition c')) 1 p := by
  have hP := B.continuous
  set T := c.transition c' with hTdef
  set q : (c.φ.model.E.prod c.F) 1 := (p.1, c.F.shift.toBase 1 p.2) with hq
  have hp' : p ∈ (c.φ.model.E.prod c.F.shift).lvlSet (strongShiftOne (c.overlap c')) 1 := by
    rw [← strongShiftOne_shift_overlap]; exact hp
  have hqov : (c.φ.model.E.prod c.F).toBase 1 q ∈ c.overlap c' := hp'
  have hqK : (c.φ.model.E.prod c.F).toBase 1 q ∈ c.K := c.overlap_subset_K c' hqov
  have hT := shift_transition (hc := hc) (y₀ := y₀) hc' y₀' hqK
  set L := levelMap (E := c.φ.model.E.prod c.F) (F := c'.φ.model.E.prod c'.F) T 1 q with hL
  -- `ι T¹(q) = T(ι q)`
  have hι : (c'.φ.model.E.prod c'.F).toBase 1 L = T ((c.φ.model.E.prod c.F).toBase 1 q) :=
    (h.1.isSc0 (c.isScRetract_overlap c' hP)).toBase_levelMap hqov
  -- the `[1]`-transition maps `(E ⊕ F¹)₁` into `(E' ⊕ F'¹)₁`
  have hιp : (c.φ.model.E.prod c.F.shift).toBase 1 p ∈ strongShiftOne (c.overlap c') := hp'
  obtain ⟨w, hw⟩ := h.2.2.1.mem_range_toBase (c.isScRetract_overlap_one c' hP) hιp
    ⟨p, rfl⟩
  have hw2 : c'.F.shift.toBase 1 w.2 =
      Function.invFun (c'.F.toBase 1) (T ((c.φ.model.E.prod c.F).toBase 1 q)).2 := by
    have := congrArg Prod.snd hw
    rw [ScBanach.prod_toBase] at this
    exact this
  have hmem : (T ((c.φ.model.E.prod c.F).toBase 1 q)).2 ∈ range (c'.F.toBase 1) :=
    ⟨L.2, congrArg Prod.snd hι⟩
  have hsnd : L.2 = c'.F.shift.toBase 1 w.2 := by
    apply c'.F.toBase_injective 1
    rw [hw2, Function.invFun_eq hmem]
    exact congrArg Prod.snd hι
  have hTq : (c.shift hc y₀).transition (c'.shift hc' y₀') (p.1, c.F.shift.toBase 1 p.2) = L := hT
  rw [hTq]
  refine ⟨⟨w.2, hsnd.symm⟩, ?_⟩
  symm
  apply levelMap_eq_of_toBase_eq
  refine Prod.ext ?_ ?_
  · change c'.φ.model.E.toBase 1 ((c.shift hc y₀).transition (c'.shift hc' y₀')
      (p.1, c.F.shift.toBase 1 p.2)).1 = (T ((c.φ.model.E.prod c.F).toBase 1 q)).1
    rw [hTq]
    exact congrArg Prod.fst hι
  · change c'.F.shift.toBase 1 (Function.invFun (c'.F.shift.toBase 1)
      ((c.shift hc y₀).transition (c'.shift hc' y₀') (p.1, c.F.shift.toBase 1 p.2)).2) =
        Function.invFun (c'.F.toBase 1) (T ((c.φ.model.E.prod c.F).toBase 1 q)).2
    rw [hTq, hsnd, Function.leftInverse_invFun (c'.F.shift.toBase_injective 1), hw2]

/-- `[1]` of the transition of shifted charts is sc-smooth (Proposition 1.17 for `[1]` of the
transition). -/
theorem shift_compatible_one (h : c.Compatible c') :
    IsScSmoothRetractMap ((c.shift hc y₀).φ.model.E.prod (c.shift hc y₀).F.shift)
      ((c.shift hc y₀).φ.model.C ×ˢ univ)
      (strongShiftOne ((c.shift hc y₀).overlap (c'.shift hc' y₀')))
      ((c'.shift hc' y₀').φ.model.E.prod (c'.shift hc' y₀').F.shift)
      ((c'.shift hc' y₀').φ.model.C ×ˢ univ)
      (strongShiftOne ((c'.shift hc' y₀').overlap (c.shift hc y₀)))
      (shiftFiber ((c.shift hc y₀).transition (c'.shift hc' y₀'))) := by
  have h3 := h.2.2.1.shift (c.isScRetract_overlap_one c' B.continuous)
  have key : IsScSmoothRetractMap ((c.shift hc y₀).φ.model.E.prod (c.shift hc y₀).F.shift)
      ((c.shift hc y₀).φ.model.C ×ˢ univ)
      ((c.φ.model.E.prod c.F.shift).lvlSet (strongShiftOne (c.overlap c')) 1)
      ((c'.shift hc' y₀').φ.model.E.prod (c'.shift hc' y₀').F.shift)
      ((c'.shift hc' y₀').φ.model.C ×ˢ univ)
      ((c'.φ.model.E.prod c'.F.shift).lvlSet (strongShiftOne (c'.overlap c)) 1)
      (shiftFiber ((c.shift hc y₀).transition (c'.shift hc' y₀'))) := by
    refine h3.congr fun p hp => ?_
    have hp' : p ∈ strongShiftOne ((c.shift hc y₀).overlap (c'.shift hc' y₀')) := by
      rw [strongShiftOne_shift_overlap]; exact hp
    exact (shift_transition_one h hp').2.symm
  rw [strongShiftOne_shift_overlap, strongShiftOne_shift_overlap]
  exact key

/-- The `F₁`-condition of Definition 2.50 for the shifted charts (fibre components in `F₂` go to
fibre components in `F'₂`). -/
theorem shift_compatible_range (h : c.Compatible c') :
    ∀ x ∈ (c.shift hc y₀).overlap (c'.shift hc' y₀'),
      x.2 ∈ range ((c.shift hc y₀).F.toBase 1) →
        ((c.shift hc y₀).transition (c'.shift hc' y₀') x).2 ∈
          range ((c'.shift hc' y₀').F.toBase 1) := by
  rintro ⟨x1, x2⟩ hx ⟨w, hw⟩
  change c.F.shift.toBase 1 w = x2 at hw
  subst hw
  have hp : ((x1, w) : ((c.shift hc y₀).φ.model.E.prod (c.shift hc y₀).F.shift) 0) ∈
      strongShiftOne ((c.shift hc y₀).overlap (c'.shift hc' y₀')) := hx
  exact (shift_transition_one h hp).1

/-- **Compatible strong bundle charts have compatible index raises** (Definition 2.50 for the
shifted charts: `(Φ'¹ ∘ (Φ¹)⁻¹)[i]`, `i = 0, 1`, are the level-`1` maps of `(Φ' ∘ Φ⁻¹)[i]`,
sc-smooth by Proposition 1.17; the `F₁`-condition of `[1]` is the level-`1` property of `[1]`). -/
theorem Compatible.shift (h : c.Compatible c') :
    (c.shift hc y₀).Compatible (c'.shift hc' y₀') := by
  have h0 := MPolyfold.levelChart_compatible hc.toMChart y₀ hc'.toMChart y₀'
  exact ⟨h0.1, h0.2, shift_compatible_one h, shift_compatible_one h.symm,
    shift_compatible_range h, shift_compatible_range h.symm⟩

end StrongBundleChart

/-! ### The shifted strong bundle `P¹ : Y¹ → X¹` -/

namespace StrongBundle

/-- The strong bundle atlas of `P¹`: the index raises `Φ¹` of the charts `Φ` of the atlas of `P`
(each with every junk value). -/
def shiftAtlas : StrongBundleAtlas PX.shift B.shiftProj where
  charts := {χ | ∃ (c : StrongBundleChart PX P) (hc : c ∈ B.atlas.charts) (y₀ : B.ShiftSpace),
    χ = c.shift (B.isChart_of_mem hc) y₀}
  compatible := by
    rintro _ ⟨c, hc, y₀, rfl⟩ _ ⟨c', hc', y₀', rfl⟩
    exact (B.atlas.compatible c hc c' hc').shift
  cover y := by
    obtain ⟨c, hc, hy⟩ := B.atlas.cover (B.toMPolyfold0.levelVal 1 y)
    exact ⟨c.shift (B.isChart_of_mem hc) y, ⟨c, hc, y, rfl⟩, hy⟩

/-- `P¹ : Y¹ → X¹` is continuous (it is `(φ¹)⁻¹ ∘ pr₁ ∘ Φ¹` on the chart domains). -/
theorem continuous_shiftProj : Continuous B.shiftProj := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  obtain ⟨χ, hχ, hy⟩ := B.shiftAtlas.cover y
  obtain ⟨c, hc, y₀, rfl⟩ := hχ
  have ho : IsOpen (c.shift (B.isChart_of_mem hc) y₀).toPartialEquiv.source :=
    (MPolyfold.levelChart (B.isChart_of_mem hc).toMChart y₀).isOpen_source
  exact (c.shift (B.isChart_of_mem hc) y₀).continuousOn_proj.continuousAt (ho.mem_nhds hy)

/-- The zero of the fibre of `P¹` over `x`. -/
def shiftZero (x : PX.Level 1) : B.ShiftSpace := (((B.shiftFiberEquiv x).symm 0 :
  B.shiftProj ⁻¹' {x}) : B.ShiftSpace)

/-- The zero of the fibre over `x` lies over `x`. -/
lemma shiftProj_shiftZero (x : PX.Level 1) : B.shiftProj (B.shiftZero x) = x :=
  ((B.shiftFiberEquiv x).symm 0).2

/-- The zero of the fibre of `P¹` is the zero of the fibre of `P`. -/
lemma levelVal_shiftZero (x : PX.Level 1) :
    B.toMPolyfold0.levelVal 1 (B.shiftZero x) = fiberZero P (PX.levelVal 1 x) := rfl

/-- `P¹` is surjective (the zero section lies in `Y_{1,1}` over `X₁`). -/
theorem surjective_shiftProj : Surjective B.shiftProj :=
  fun x => ⟨B.shiftZero x, B.shiftProj_shiftZero x⟩

/-- The fibres of `P¹` are Banachable: `P¹⁻¹(x) ≅ K¹_{φ¹(x)}`, a closed subspace of `F₁`. -/
theorem banachable_shift (x : PX.Level 1) : IsBanachable (B.shiftProj ⁻¹' {x}) := by
  obtain ⟨c, hc, hx⟩ := B.exists_chart_mem (PX.levelVal 1 x)
  exact (c.shift (B.isChart_of_mem hc) (B.shiftZero x)).isBanachable_fiber
    (x := x) hx

/-- **The shifted strong bundle `P¹ : Y¹ → X¹`** (the index raise of the strong bundle
`P : Y → X`; the text's `P^i : Y^i → X^i` for `i = 1` in Corollary 5.8, never defined in the
text): the total space `Y¹ = Y_{1,1}` with the level topology of `Y[0]`, the base the M-polyfold
`X¹` (`MPolyfold.shift`), the projection `P¹ = P|_{Y_{1,1}}`, the fibres
`P⁻¹(x) ∩ Y_{1,1}` (linear subspaces, Banachable as closed subspaces of `F₁` in a chart), and the
strong bundle atlas of the index raises `Φ¹ : P¹⁻¹(V¹) → K¹ ⊆ U¹ ◁ F¹` (`StrongBundleChart.shift`),
so that `(Y¹)_{m,k} = Y_{m+1,k+1}` (`StrongBundle.mem_shift_doubleLevel_iff`). -/
def shift : StrongBundle PX.shift B.shiftProj where
  continuous := B.continuous_shiftProj
  surjective := B.surjective_shiftProj
  banachable := B.banachable_shift
  atlas := B.shiftAtlas

/-- The atlas of `P¹`. -/
@[simp] lemma shift_atlas : B.shift.atlas = B.shiftAtlas := rfl

/-- The index raise of a chart of `P` is a chart of `P¹`. -/
theorem isChart_shift {c : StrongBundleChart PX P} (hc : B.IsChart c) (y₀ : B.ShiftSpace) :
    B.shift.IsChart (c.shift hc y₀) := by
  rintro _ ⟨c', hc', y₀', rfl⟩
  exact (hc c' hc').shift

/-- The index raise of a chart of the atlas of `P` is in the atlas of `P¹`. -/
lemma shift_mem_atlas {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts) (y₀ : B.ShiftSpace) :
    c.shift (B.isChart_of_mem hc) y₀ ∈ B.shift.atlas.charts := ⟨c, hc, y₀, rfl⟩

/-- The chart `Φ¹` of `Y¹[0]` is compatible with the level charts of `Y[0]¹`. -/
lemma shift_toMChart_compatible {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (y₀ : B.ShiftSpace) {ψ : MChart Y} (hψ : B.toMPolyfold0.IsChart ψ) (z₀ : B.ShiftSpace) :
    ((c.shift hc y₀).toMChart B.shift.continuous).Compatible (MPolyfold.levelChart hψ z₀) :=
  MPolyfold.levelChart_compatible hc.toMChart y₀ hψ z₀

/-- **`Y¹[0]` is the M-polyfold `Y[0]¹`**: the charts of the M-polyfold `Y¹[0]` of the shifted
strong bundle are those of the level M-polyfold `(Y[0])¹` (the atlases `{Φ¹}` and
`{(Φ')¹}` are equivalent). -/
theorem isChart_shift_toMPolyfold0_iff (χ : MChart B.ShiftSpace) :
    B.shift.toMPolyfold0.IsChart χ ↔ B.toMPolyfold0.shift.IsChart χ := by
  refine MPolyfold.isChart_congr ?_ χ
  rw [MAtlas.equiv_iff]
  rintro _ ⟨_, ⟨c, hc, y₀, rfl⟩, rfl⟩ _ ⟨ψ, hψ, z₀, rfl⟩
  exact B.shift_toMChart_compatible (B.isChart_of_mem hc) y₀ hψ z₀

end StrongBundle

namespace StrongBundle

/-- **The double filtration of `Y¹` is that of `Y` shifted**: `(Y¹)_{m,k} = Y_{m+1,k+1}`
(`k ≤ m + 1`). -/
theorem mem_shift_doubleLevel_iff (y : B.ShiftSpace) {m k : ℕ} (hk : k ≤ m + 1) :
    y ∈ B.shift.doubleLevel m k ↔ B.toMPolyfold0.levelVal 1 y ∈ B.doubleLevel (m + 1) (k + 1) := by
  obtain ⟨c, hc, hy⟩ := B.atlas.cover (B.toMPolyfold0.levelVal 1 y)
  have hy' : y ∈ (c.shift (B.isChart_of_mem hc) y).toPartialEquiv.source := hy
  rw [B.shift.mem_doubleLevel_iff (B.shift_mem_atlas hc y) hy' hk,
    B.mem_doubleLevel_iff hc hy (by omega)]
  have e1 := c.φ.model.E.mem_range_shift_toBase_iff (m := m)
    (c.shift (B.isChart_of_mem hc) y y).1
  rw [StrongBundleChart.toBase_shift_apply_fst _ _ hy'] at e1
  have e2 := c.F.mem_range_shift_toBase_iff (m := k) (c.shift (B.isChart_of_mem hc) y y).2
  rw [StrongBundleChart.toBase_shift_apply_snd _ _ hy'] at e2
  exact and_congr e1 e2

/-! ### The section `f¹` of `P¹` -/

variable {f : X → Y}

open scoped Classical in
/-- **The section `f¹ : X¹ → Y¹`** of the shifted strong bundle (the text's "a sc-smooth section
`f` ... defines, by raising the index, a sc-smooth section `f^i` of `Y^i → X^i`" for `i = 1`):
`f¹(x) = f(x)` for `x ∈ X₁`.  (Junk value the zero of the fibre if `f(x) ∉ Y_{1,1}`; an sc-smooth
section maps `X₁` into `Y_{1,1}`, `IsScSmoothSection.mem_levelSet`.) -/
def sectionShift (f : X → Y) (x : PX.Level 1) : B.ShiftSpace :=
  if h : f (PX.levelVal 1 x) ∈ B.toMPolyfold0.levelSet 1 then
    B.toMPolyfold0.levelMk 1 _ h
  else B.shiftZero x

variable {B}

/-- An sc-smooth section maps `X_m` into `Y[0]_m = Y_{m,m}`. -/
lemma IsScSmoothSection.mem_levelSet (hf : B.IsScSmoothSection f) {m : ℕ} {x : X}
    (hx : x ∈ PX.levelSet m) : f x ∈ B.toMPolyfold0.levelSet m :=
  hf.2.mapsTo_levelSet m hx

/-- `f¹(x) = f(x)` as points of `Y`, for an sc-smooth section `f`. -/
lemma levelVal_sectionShift (hf : B.IsScSmoothSection f) (x : PX.Level 1) :
    B.toMPolyfold0.levelVal 1 (B.sectionShift f x) = f (PX.levelVal 1 x) := by
  rw [sectionShift, dif_pos (hf.mem_levelSet (MPolyfold.levelVal_mem x))]
  rfl

/-- `f¹` is a section of `P¹`. -/
lemma isSection_sectionShift (hf : IsSection P f) : IsSection B.shiftProj (B.sectionShift f) := by
  intro x
  unfold sectionShift
  split_ifs with h
  · exact MPolyfold.level_ext (P := PX) (hf _)
  · exact B.shiftProj_shiftZero x

/-- **`f¹` is an sc-smooth section of `P¹`** (the text's "by raising the index"): `f¹` is the
level-`1` map of the sc-smooth map `f : X → Y[0]` (`MPolyfold.IsScSmoothMap.levelOne`), and the
M-polyfold `Y¹[0]` is `Y[0]¹` (`StrongBundle.isChart_shift_toMPolyfold0_iff`). -/
theorem IsScSmoothSection.shift (hf : B.IsScSmoothSection f) :
    B.shift.IsScSmoothSection (B.sectionShift f) := by
  refine ⟨isSection_sectionShift hf.1, ?_⟩
  have h := MPolyfold.IsScSmoothMap.levelOne hf.2 (f₁ := B.sectionShift f)
    (levelVal_sectionShift hf)
  exact ⟨h.isOpen, h.continuousOn, fun φ ψ hφ hψ V hV hVU hfV =>
    h.smooth φ ψ hφ ((B.isChart_shift_toMPolyfold0_iff ψ).1 hψ) V hV hVU hfV⟩

/-- The zero section of `P¹` is the zero section of `P` on `X₁`. -/
lemma fiberZero_shiftProj (x : PX.Level 1) : fiberZero B.shiftProj x = B.shiftZero x := rfl

/-- The zeros of `f¹` are the zeros of `f` in `X₁`. -/
theorem isZeroAt_sectionShift_iff (hf : B.IsScSmoothSection f) (x : PX.Level 1) :
    IsZeroAt B.shiftProj (B.sectionShift f) x ↔ IsZeroAt P f (PX.levelVal 1 x) := by
  unfold IsZeroAt
  rw [fiberZero_shiftProj]
  constructor
  · intro h
    have := congrArg (B.toMPolyfold0.levelVal 1) h
    rwa [levelVal_sectionShift hf, levelVal_shiftZero] at this
  · intro h
    apply MPolyfold.level_ext
    rw [levelVal_sectionShift hf, levelVal_shiftZero, h]

/-- The solution set of `f¹` is the part of the solution set of `f` in `X₁`. -/
theorem solutionSet_sectionShift (hf : B.IsScSmoothSection f) :
    solutionSet B.shiftProj (B.sectionShift f) =
      {x : PX.Level 1 | PX.levelVal 1 x ∈ solutionSet P f} := by
  ext x
  exact isZeroAt_sectionShift_iff hf x

/-- **`f¹` is regularizing** when `f` is (Definition 3.14 (2) on `X¹`): `x ∈ (X¹)_m = X_{m+1}` and
`f¹(x) ∈ (Y¹)_{m,m+1} = Y_{m+1,m+2}` give `x ∈ X_{m+2} = (X¹)_{m+1}`. -/
theorem regularizing_sectionShift (hf : B.IsScSmoothSection f)
    (hreg : ∀ m, ∀ x ∈ PX.levelSet m, f x ∈ B.doubleLevel m (m + 1) → x ∈ PX.levelSet (m + 1)) :
    ∀ m, ∀ x ∈ PX.shift.levelSet m, B.sectionShift f x ∈ B.shift.doubleLevel m (m + 1) →
      x ∈ PX.shift.levelSet (m + 1) := by
  intro m x hx hfx
  rw [MPolyfold.mem_shift_levelSet_iff] at hx ⊢
  rw [B.mem_shift_doubleLevel_iff _ (by omega), levelVal_sectionShift hf] at hfx
  exact hreg (m + 1) _ hx hfx

end StrongBundle

end Bundle

end Polyfold
