import Polyfold.Chapter10.LocalRegularityGerm

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §8.4: **Definition 8.4.2** (p. 382, new in the 2021 edition), with Part I's
**Definition 5.3.1** (sc-smooth bump functions) and **Proposition 5.5.3**.  Numbers and pages are
the 2021 text's.

# Cutting off strong bundle isomorphisms of `W|U`

Definition 8.4.2 speaks of strong bundle isomorphisms `B : W|U(x) → W|U(x)`
(`StrongBundle.IsLocalIsoOn`); the formal `EpStrongBundle.IsLR` speaks of strong bundle maps of
`W`.  This file passes from the first to the second near a point, when the base admits sc-smooth
bump functions.

## The construction

In a strong bundle chart `Φ : P⁻¹(V) → K = R(U ◁ F)` over `φ : V → O`, for a smooth point
`u₁ ∈ O` and `χ : O → [0, 1]`, the map
`(u, h) ↦ R(u₁ + χ(u)(u − u₁), χ(u) h)` (`StrongBundleChart.cutMap`) is sc-smooth `K → K` and
`K[1] → K[1]` as soon as the points `u₁ + χ(u)(u − u₁)` stay in the domain of `R`; it is the
identity where `χ = 1` and the constant `(u₁, 0)` where `χ = 0`.  For `χ` with support in `V`,
`StrongBundle.cutOff` is this map over `V` and the constant `0_{x₁}` elsewhere: a strong bundle
map of `Y` (`StrongBundle.isStrongBundleMap_cutOff`), the contraction of `Y` towards the fibre
over `x₁ = φ⁻¹(u₁)`.

## What is proved

* `StrongBundleChart.isScSmoothRetractMap_cutMap`, `isScSmoothRetractMap_cutMapOne`,
  `cutMap_of_eq_one`, `cutMap_of_eq_zero`, `toBase_cutMapOne`.
* `StrongBundle.cutOff`, `cutOffBase`, `cutOff_of_eq_one`, `cutOff_of_eq_zero`,
  **`isStrongBundleMap_cutOff`**.
* **`MPolyfold.AdmitsBumpFunctions.hasLocalIsoExtension`**: if the base admits sc-smooth bump
  functions (Definition 5.3.1), strong bundle isomorphisms of `Y|U` can be cut off: for `U` in a
  chart domain there is `V ∋ x` such that every strong bundle isomorphism `Θ` of `Y|U` agrees
  over `V` with the strong bundle map `Θ ∘ c` of `Y`, `c` a contraction with values in `Y|U`.
* **`EpStrongBundle.IsLR.isLRGerm_of_admitsBumpFunctions`**: over an ep-groupoid whose object
  space admits sc-smooth bump functions, the formal `IsLR` gives the germ form `IsLRGerm` of
  Definition 8.4.2 (`Chapter10/LocalRegularityGerm`).

Witnesses (`Chapter16/OrientationTransportRegularity`):
`HalfSpaceBundle.isLRGerm_of_admitsBumpFunctions_halfSEP` (boundary, non-zero fibres) and
`StrongBundleLocalizationExamples.isLRGerm_of_admitsBumpFunctions_z3SEP` (a base which is not
effective).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

open StrongRetr

/-! ### The contraction in a strong bundle chart -/

section Chart

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundleChart

variable (c : StrongBundleChart PX P) (χ : c.φ.model.E 0 → ℝ) (u₁ : c.φ.model.E 0)

/-- The base point `u₁ + χ(u)(u − u₁)` of the contraction. -/
def cutBase (u : c.φ.model.E 0) : c.φ.model.E 0 := u₁ + χ u • (u - u₁)

/-- **The contraction of `K` towards `(u₁, 0)`**: `(u, h) ↦ R(u₁ + χ(u)(u − u₁), χ(u) h)`. -/
def cutMap : (c.φ.model.E.prod c.F) 0 → (c.φ.model.E.prod c.F) 0 :=
  fun p => c.R (c.cutBase χ u₁ p.1, χ p.1 • p.2)

/-- The contraction on `K[1]`. -/
def cutMapOne : (c.φ.model.E.prod c.F.shift) 0 → (c.φ.model.E.prod c.F.shift) 0 :=
  fun p => shiftFiber c.R ((c.cutBase χ u₁ p.1, χ p.1 • p.2) : (c.φ.model.E.prod c.F.shift) 0)

variable {c χ u₁}
  (hχ : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O realSc univ univ χ)
  (hu₁ : u₁ ∈ c.φ.model.E.smooth) (ha : ∀ u ∈ c.φ.model.O, c.cutBase χ u₁ u ∈ c.U)

include ha in
omit [T2Space Y] [ParacompactSpace Y] in
lemma cutMap_mem_K {p : (c.φ.model.E.prod c.F) 0} (hp : p ∈ c.K) : c.cutMap χ u₁ p ∈ c.K := by
  have hpO : p.1 ∈ c.φ.model.O := by rw [← c.base_K]; exact ⟨p, hp, rfl⟩
  exact ⟨_, ⟨ha _ hpO, mem_univ _⟩, rfl⟩

include hχ hu₁ ha in
omit [T2Space Y] [ParacompactSpace Y] in
/-- The contraction is sc-smooth `K → K`. -/
theorem isScSmoothRetractMap_cutMap :
    IsScSmoothRetractMap (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ) c.K
      (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ) c.K (c.cutMap χ u₁) := by
  refine ⟨fun p hp => cutMap_mem_K ha hp, fun R' hR' => ?_⟩
  have hU := R'.isScDomain
  have hRK : ∀ q ∈ R'.U, R' q ∈ c.K := fun q hq => hR' ▸ R'.apply_mem_retract hq
  have hfst := c.isStrongBundleRetract.isScSmoothRetractMap_fst
  rw [c.base_K] at hfst
  have t := (hχ.comp hfst c.φ.model.isScRetract).comp_isScSmooth R' hR'
  have p := R'.isScSmooth
  have hc₁ : IsScSmooth (E := c.φ.model.E.prod c.F) (F := c.φ.model.E) R'.U fun _ => u₁ :=
    isScSmooth_const_of_mem_smooth hU hu₁
  have b := hc₁.add hU (t.smul hU ((p.fst hU).sub hU hc₁))
  have f := t.smul hU (p.snd hU)
  have hpair := b.scPair hU f
  have hcomp := IsScSmooth.comp hU (c.relOpen.prod_univ c.F).isScDomain
    c.isRetraction.isScSmooth_zero hpair fun q hq =>
      ⟨ha _ (by rw [← c.base_K]; exact ⟨_, hRK q hq, rfl⟩), mem_univ _⟩
  exact hcomp.congr hU fun _ _ => rfl

include ha in
omit [T2Space Y] [ParacompactSpace Y] in
lemma cutMapOne_mem {p : (c.φ.model.E.prod c.F.shift) 0} (hp : p ∈ strongShiftOne c.K) :
    c.cutMapOne χ u₁ p ∈ strongShiftOne c.K := by
  have hpO : p.1 ∈ c.φ.model.O := by rw [← c.base_K]; exact ⟨_, hp, rfl⟩
  have := (c.isRetraction.toScRetractionOne c.relOpen).apply_mem_retract
    (show ((c.cutBase χ u₁ p.1, χ p.1 • p.2) : (c.φ.model.E.prod c.F.shift) 0) ∈ c.U ×ˢ univ from
      ⟨ha _ hpO, mem_univ _⟩)
  rw [c.isRetraction.toScRetractionOne_retract c.relOpen] at this
  exact this

include hχ hu₁ ha in
omit [T2Space Y] [ParacompactSpace Y] in
/-- The contraction is sc-smooth `K[1] → K[1]`. -/
theorem isScSmoothRetractMap_cutMapOne :
    IsScSmoothRetractMap (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ) (strongShiftOne c.K)
      (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ) (strongShiftOne c.K)
      (c.cutMapOne χ u₁) := by
  refine ⟨fun p hp => cutMapOne_mem ha hp, fun R' hR' => ?_⟩
  have hU := R'.isScDomain
  have hRK : ∀ q ∈ R'.U, R' q ∈ strongShiftOne c.K := fun q hq => hR' ▸ R'.apply_mem_retract hq
  have hfst := c.isStrongBundleRetract.isScSmoothRetractMap_fst_one
  rw [c.base_K] at hfst
  have t := (hχ.comp hfst c.φ.model.isScRetract).comp_isScSmooth R' hR'
  have p := R'.isScSmooth
  have hc₁ : IsScSmooth (E := c.φ.model.E.prod c.F.shift) (F := c.φ.model.E) R'.U fun _ => u₁ :=
    isScSmooth_const_of_mem_smooth hU hu₁
  have b := hc₁.add hU (t.smul hU ((p.fst hU).sub hU hc₁))
  have f := t.smul hU (p.snd hU)
  have hpair := b.scPair hU f
  have hcomp := IsScSmooth.comp hU (c.relOpen.prod_univ c.F.shift).isScDomain
    c.isRetraction.isScSmooth_one hpair fun q hq =>
      ⟨ha _ (by rw [← c.base_K]; exact ⟨_, hRK q hq, rfl⟩), mem_univ _⟩
  exact hcomp.congr hU fun _ _ => rfl

omit [T2Space Y] [ParacompactSpace Y] in
/-- Where `χ = 1` the contraction is the identity of `K`. -/
lemma cutMap_of_eq_one {p : (c.φ.model.E.prod c.F) 0} (hp : p ∈ c.K) (h1 : χ p.1 = 1) :
    c.cutMap χ u₁ p = p := by
  obtain ⟨q, hq, rfl⟩ := hp
  unfold cutMap cutBase
  rw [h1, one_smul, one_smul, add_sub_cancel]
  exact c.isRetraction.idem q hq

omit [T2Space Y] [ParacompactSpace Y] in
/-- Where `χ = 0` the contraction is constant, `(u₁, 0)`. -/
lemma cutMap_of_eq_zero (hu₁O : u₁ ∈ c.φ.model.O) {p : (c.φ.model.E.prod c.F) 0}
    (h0 : χ p.1 = 0) : c.cutMap χ u₁ p = (u₁, 0) := by
  obtain ⟨q, hq, hqe⟩ := c.zero_mem_K hu₁O
  unfold cutMap cutBase
  rw [h0, zero_smul, zero_smul, add_zero, ← hqe]
  exact c.isRetraction.idem q hq

include ha in
omit [T2Space Y] [ParacompactSpace Y] in
/-- The contraction on `K[1]` covers the contraction on `K`. -/
lemma toBase_cutMapOne {p : (c.φ.model.E.prod c.F.shift) 0} (hp : p.1 ∈ c.φ.model.O) :
    ((c.cutMapOne χ u₁ p).1, c.F.toBase 1 (c.cutMapOne χ u₁ p).2) =
      c.cutMap χ u₁ (p.1, c.F.toBase 1 p.2) := by
  refine Prod.ext ?_ ?_
  · change (c.R (c.cutBase χ u₁ p.1, c.F.toBase 1 (χ p.1 • p.2))).1 = _
    rw [map_smul]; rfl
  · have := c.isRetraction.toBase_shiftFiber_snd
      (p := ((c.cutBase χ u₁ p.1, χ p.1 • p.2) : (c.φ.model.E.prod c.F.shift) 0)) (ha _ hp)
    change c.F.toBase 1 (shiftFiber c.R _).2 = _
    rw [this, map_smul]; rfl

end StrongBundleChart

end Chart

/-! ### The contraction of a strong bundle towards a fibre -/

section Global

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

namespace StrongBundle

open scoped Classical in
/-- **The contraction of `Y` towards the zero vector over `x₁`**, cut off by `χ`: over the domain
of the strong bundle chart `Φ` it is `Φ⁻¹ ∘ ((u, h) ↦ R(u₁ + χ(u − u₁), χ h)) ∘ Φ`, `u₁ = φ(x₁)`,
and it is the constant `0_{x₁}` elsewhere.  Over `{χ = 1}` it is the identity. -/
def cutOff (c : StrongBundleChart PX P) (χ : X → ℝ) (x₁ : X) (w : Y) : Y :=
  if P w ∈ c.φ.source then
    c.toPartialEquiv.symm (c.cutMap (χ ∘ c.φ.symm) (c.φ x₁) (c w))
  else fiberZero P x₁

variable {c : StrongBundleChart PX P} {χ : X → ℝ} {x₁ : X}
  (ha : ∀ u ∈ c.φ.model.O, c.cutBase (χ ∘ c.φ.symm) (c.φ x₁) u ∈ c.U)

omit [T2Space Y] [ParacompactSpace Y] in
lemma apply_mem_K {w : Y} (hw : P w ∈ c.φ.source) : c w ∈ c.K := by
  rw [← c.image_source]; exact ⟨w, c.mem_source_of_proj hw, rfl⟩

omit [T2Space Y] [ParacompactSpace Y] in
lemma fst_apply_mem_O {w : Y} (hw : P w ∈ c.φ.source) : (c w).1 ∈ c.φ.model.O := by
  rw [c.fst_apply hw]; exact c.φ.mapsTo_model _ hw

include ha in
omit [T2Space Y] [ParacompactSpace Y] in
lemma apply_cutOff {w : Y} (hw : P w ∈ c.φ.source) :
    c (cutOff c χ x₁ w) = c.cutMap (χ ∘ c.φ.symm) (c.φ x₁) (c w) := by
  rw [cutOff, if_pos hw]
  exact c.toPartialEquiv.right_inv
    (by rw [c.target_eq]; exact StrongBundleChart.cutMap_mem_K ha (apply_mem_K hw))

include ha in
omit [T2Space Y] [ParacompactSpace Y] in
lemma cutOff_mem_source {w : Y} (hw : P w ∈ c.φ.source) :
    cutOff c χ x₁ w ∈ c.toPartialEquiv.source := by
  rw [cutOff, if_pos hw]
  exact c.toPartialEquiv.map_target
    (by rw [c.target_eq]; exact StrongBundleChart.cutMap_mem_K ha (apply_mem_K hw))

omit [T2Space Y] [ParacompactSpace Y] in
lemma comp_symm_fst {w : Y} (hw : P w ∈ c.φ.source) : (χ ∘ c.φ.symm) (c w).1 = χ (P w) := by
  rw [Function.comp_apply, c.fst_apply hw, c.φ.symm_apply_apply hw]

include ha in
omit [T2Space Y] [ParacompactSpace Y] in
/-- Over `{χ = 1}` the contraction is the identity. -/
lemma cutOff_of_eq_one {w : Y} (hw : P w ∈ c.φ.source) (h1 : χ (P w) = 1) :
    cutOff c χ x₁ w = w := by
  refine c.toPartialEquiv.injOn (cutOff_mem_source ha hw) (c.mem_source_of_proj hw) ?_
  rw [apply_cutOff ha hw]
  exact StrongBundleChart.cutMap_of_eq_one (apply_mem_K hw) ((comp_symm_fst hw).trans h1)

include ha in
omit [T2Space Y] [ParacompactSpace Y] in
/-- Over `{χ = 0}` the contraction is the constant `0_{x₁}`. -/
lemma cutOff_of_eq_zero (hx₁ : x₁ ∈ c.φ.source) {w : Y} (h0 : χ (P w) = 0) :
    cutOff c χ x₁ w = fiberZero P x₁ := by
  by_cases hw : P w ∈ c.φ.source
  · have hP0 : P (fiberZero P x₁) ∈ c.φ.source := by rw [proj_fiberZero P]; exact hx₁
    refine c.toPartialEquiv.injOn (cutOff_mem_source ha hw) (c.mem_source_of_proj hP0) ?_
    rw [apply_cutOff ha hw, StrongBundleChart.cutMap_of_eq_zero (c.φ.mapsTo_model _ hx₁)
      ((comp_symm_fst hw).trans h0)]
    refine (Prod.ext ?_ (c.snd_fiberZero hx₁)).symm
    rw [c.fst_apply hP0, proj_fiberZero P]
  · rw [cutOff, if_neg hw]

include ha in
omit [T2Space Y] [ParacompactSpace Y] in
/-- The base point of the contraction over the chart domain. -/
lemma proj_cutOff {w : Y} (hw : P w ∈ c.φ.source) :
    P (cutOff c χ x₁ w) =
      c.φ.symm (r c.R (c.cutBase (χ ∘ c.φ.symm) (c.φ x₁) (c.φ (P w)))) := by
  have hs := cutOff_mem_source ha hw
  have hPs : P (cutOff c χ x₁ w) ∈ c.φ.source := by rw [c.source_eq] at hs; exact hs
  have h1 := c.covers _ hs
  rw [apply_cutOff ha hw] at h1
  have h2 : (c.cutMap (χ ∘ c.φ.symm) (c.φ x₁) (c w)).1 =
      r c.R (c.cutBase (χ ∘ c.φ.symm) (c.φ x₁) (c.φ (P w))) := by
    unfold StrongBundleChart.cutMap
    rw [c.isRetraction.apply_fst (ha _ (fst_apply_mem_O hw)), c.fst_apply hw]; rfl
  rw [← h2, h1, c.φ.symm_apply_apply hPs]

/-- The base map of the contraction. -/
def cutOffBase (c : StrongBundleChart PX P) (χ : X → ℝ) (x₁ : X) (y : X) : X :=
  P (cutOff c χ x₁ (fiberZero P y))

include ha in
omit [T2Space Y] [ParacompactSpace Y] in
lemma covers_cutOff (w : Y) : P (cutOff c χ x₁ w) = cutOffBase c χ x₁ (P w) := by
  unfold cutOffBase
  by_cases hw : P w ∈ c.φ.source
  · rw [proj_cutOff ha hw, proj_cutOff ha (by rw [proj_fiberZero P]; exact hw),
      proj_fiberZero P]
  · rw [cutOff, if_neg hw, cutOff, if_neg (by rw [proj_fiberZero P]; exact hw)]

include ha in
omit [T2Space Y] [ParacompactSpace Y] in
/-- The contraction is linear on the fibres. -/
theorem fiber_linear_cutOff (y : X) :
    IsLinearMap ℝ (fiberRestrict P P (cutOffBase c χ x₁) (cutOff c χ x₁) (covers_cutOff ha) y) := by
  by_cases hy : y ∈ c.φ.source
  · have hmem : ∀ v : P ⁻¹' {y}, P (v : Y) ∈ c.φ.source := fun v => by
      rw [show P v = y from v.2]; exact hy
    have hκ : cutOffBase c χ x₁ y ∈ c.φ.source := by
      have := cutOff_mem_source ha (w := fiberZero P y) (by rw [proj_fiberZero P]; exact hy)
      rw [c.source_eq] at this; exact this
    set b := c.cutBase (χ ∘ c.φ.symm) (c.φ x₁) (c.φ y) with hb
    have hbU : b ∈ c.U := ha _ (c.φ.mapsTo_model y hy)
    have key : ∀ v : P ⁻¹' {y}, c (cutOff c χ x₁ v) = c.R (b, χ y • (c (v : Y)).2) := fun v => by
      rw [apply_cutOff ha (hmem v)]
      unfold StrongBundleChart.cutMap
      rw [comp_symm_fst (hmem v), c.fst_apply (hmem v), show P v = y from v.2]
    have hfr : ∀ v : P ⁻¹' {y}, ((fiberRestrict P P (cutOffBase c χ x₁) (cutOff c χ x₁)
        (covers_cutOff ha) y v : P ⁻¹' {cutOffBase c χ x₁ y}) : Y) = cutOff c χ x₁ v := fun _ => rfl
    have hfst : ∀ z : P ⁻¹' {cutOffBase c χ x₁ y}, (c (z : Y)).1 = c.φ (cutOffBase c χ x₁ y) :=
      fun z => by rw [c.fst_apply (by rw [show P z = _ from z.2]; exact hκ), show P z = _ from z.2]
    have hsrc : ∀ z : P ⁻¹' {cutOffBase c χ x₁ y}, (z : Y) ∈ c.toPartialEquiv.source := fun z =>
      c.mem_source_of_proj (by rw [show P z = _ from z.2]; exact hκ)
    constructor
    · intro v w
      refine Subtype.ext (c.toPartialEquiv.injOn (hsrc _) (hsrc _) (Prod.ext ?_ ?_))
      · rw [hfst, hfst]
      · rw [c.snd_add hκ, hfr, hfr, hfr, key, key, key, c.snd_add hy, smul_add,
          (c.isRetraction.fiber_linear b hbU).map_add]
    · intro t v
      refine Subtype.ext (c.toPartialEquiv.injOn (hsrc _) (hsrc _) (Prod.ext ?_ ?_))
      · rw [hfst, hfst]
      · rw [(c.fiber_linear _ hκ).map_smul, hfr, hfr, key, key, (c.fiber_linear y hy).map_smul,
          smul_comm, (c.isRetraction.fiber_linear b hbU).map_smul]
  · have hκ : cutOffBase c χ x₁ y = x₁ := by
      unfold cutOffBase
      rw [cutOff, if_neg (by rw [proj_fiberZero P]; exact hy), proj_fiberZero P]
    have hz : ∀ v : P ⁻¹' {y}, fiberRestrict P P (cutOffBase c χ x₁) (cutOff c χ x₁)
        (covers_cutOff ha) y v = 0 := fun v => Subtype.ext (by
      change cutOff c χ x₁ v = fiberZero P (cutOffBase c χ x₁ y)
      rw [cutOff, if_neg (by rw [show P v = y from v.2]; exact hy), hκ])
    exact ⟨fun v w => by rw [hz, hz, hz, add_zero], fun t v => by rw [hz, hz, smul_zero]⟩

include ha in
/-- The contraction preserves `Y_{0,1}`. -/
theorem mapsTo_oneSet_cutOff (hc : c ∈ B.atlas.charts) :
    MapsTo (cutOff c χ x₁) B.oneSet B.oneSet := by
  intro w hw
  by_cases hP : P w ∈ c.φ.source
  · rw [B.mem_oneSet_iff hc (cutOff_mem_source ha hP), apply_cutOff ha hP]
    obtain ⟨h₁, hh₁⟩ := (B.mem_oneSet_iff hc (c.mem_source_of_proj hP)).1 hw
    have := c.isRetraction.snd_mem_range
      (p := ((c.cutBase (χ ∘ c.φ.symm) (c.φ x₁) (c w).1, (χ ∘ c.φ.symm) (c w).1 • h₁) :
        (c.φ.model.E.prod c.F.shift) 0)) (ha _ (fst_apply_mem_O hP))
    rw [map_smul, hh₁] at this
    exact this
  · rw [cutOff, if_neg hP]; exact B.fiberZero_mem_oneSet x₁

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- `(u, 0)` is a smooth point of `E ⊕ F` for a smooth point `u` of `E`. -/
lemma _root_.Polyfold.ScBanach.mk_zero_mem_smooth_prod {E F : ScBanach} {u : E 0}
    (hu : u ∈ E.smooth) : ((u, 0) : (E.prod F) 0) ∈ (E.prod F).smooth := by
  refine (E.prod F).mem_smooth_iff.2 fun m => ?_
  obtain ⟨y, hy⟩ := E.mem_smooth_iff.1 hu m
  refine ⟨((y, 0) : (E.prod F) m), ?_⟩
  rw [ScBanach.prod_toBase]
  exact Prod.ext hy (map_zero _)

variable (hc : c ∈ B.atlas.charts) (hχ : PX.IsScSmoothMap realPolyfold χ)
  (hχs : tsupport χ ⊆ c.φ.source) (hx₁ : x₁ ∈ c.φ.source)
  (hu₁ : c.φ x₁ ∈ c.φ.model.E.smooth)

include ha hc hχ hχs hx₁ hu₁ in
/-- The contraction is sc-smooth `Y[0] → Y[0]`. -/
theorem isScSmoothMap_cutOff : B.toMPolyfold0.IsScSmoothMap B.toMPolyfold0 (cutOff c χ x₁) := by
  have hG := StrongBundleChart.isScSmoothRetractMap_cutMap (hχ.real_chart c.isChart) hu₁ ha
  have hP0 : P (fiberZero P x₁) ∈ c.φ.source := by rw [proj_fiberZero P]; exact hx₁
  refine MPolyfold.isScSmoothMap_of_local fun w => ?_
  by_cases hw : P w ∈ c.φ.source
  · refine ⟨c.toMChart B.continuous, c.toMChart B.continuous, c.toPartialEquiv.source,
      B.isChart_toMChart hc, B.isChart_toMChart hc, c.isOpen_source B.continuous,
      c.mem_source_of_proj hw, subset_rfl,
      fun w' hw' => cutOff_mem_source ha (by rw [c.source_eq] at hw'; exact hw'), ?_⟩
    have himg : (c.toMChart B.continuous) '' c.toPartialEquiv.source = c.K := c.image_source
    rw [himg]
    refine hG.congr fun k hk => ?_
    have hkt : k ∈ c.toPartialEquiv.target := by rw [c.target_eq]; exact hk
    have hks : P (c.toPartialEquiv.symm k) ∈ c.φ.source := by
      have := c.toPartialEquiv.map_target hkt
      rw [c.source_eq] at this; exact this
    change _ = c (cutOff c χ x₁ (c.toPartialEquiv.symm k))
    rw [apply_cutOff ha hks, c.toPartialEquiv.right_inv hkt]
  · have hwt : P w ∉ tsupport χ := fun h => hw (hχs h)
    obtain ⟨c', hc', hwc'⟩ := B.atlas.cover w
    set V := c'.toPartialEquiv.source ∩ P ⁻¹' (tsupport χ)ᶜ with hV
    have hVo : IsOpen V := (c'.isOpen_source B.continuous).inter
      ((isClosed_tsupport χ).isOpen_compl.preimage B.continuous)
    have hconst : ∀ w' ∈ V, cutOff c χ x₁ w' = fiberZero P x₁ := fun w' hw' =>
      cutOff_of_eq_zero ha hx₁ (image_eq_zero_of_notMem_tsupport hw'.2)
    have hval : c (fiberZero P x₁) = (c.φ x₁, 0) :=
      Prod.ext (by rw [c.fst_apply hP0, proj_fiberZero P]) (c.snd_fiberZero hx₁)
    refine ⟨c'.toMChart B.continuous, c.toMChart B.continuous, V, B.isChart_toMChart hc',
      B.isChart_toMChart hc, hVo, ⟨hwc', hwt⟩, inter_subset_left,
      fun w' hw' => by rw [hconst w' hw']; exact c.mem_source_of_proj hP0, ?_⟩
    have hrep : ∀ z ∈ (c'.toMChart B.continuous) '' V,
        ((c.toMChart B.continuous) ∘ cutOff c χ x₁ ∘ (c'.toMChart B.continuous).symm) z =
          (c.φ x₁, 0) := by
      rintro _ ⟨w', hw', rfl⟩
      change c (cutOff c χ x₁ (c'.toPartialEquiv.symm (c' w'))) = _
      rw [c'.toPartialEquiv.left_inv hw'.1, hconst w' hw', hval]
    refine ⟨fun z hz => ?_, fun R' hR' => ?_⟩
    · rw [hrep z hz]; exact c.zero_mem_K (c.φ.mapsTo_model _ hx₁)
    · exact (isScSmooth_const_of_mem_smooth R'.isScDomain
        (ScBanach.mk_zero_mem_smooth_prod hu₁)).congr R'.isScDomain fun q hq =>
          (hrep _ (hR' ▸ R'.apply_mem_retract hq)).symm

include ha hc hχ hχs hx₁ hu₁ in
/-- The contraction is sc-smooth `Y[1] → Y[1]`. -/
theorem isScSmoothMap_one_cutOff :
    B.toMPolyfold1.IsScSmoothMap B.toMPolyfold1
      (oneRestrict B B (cutOff c χ x₁) (mapsTo_oneSet_cutOff ha hc)) := by
  have hG := StrongBundleChart.isScSmoothRetractMap_cutMapOne (hχ.real_chart c.isChart) hu₁ ha
  have hP0 : P (fiberZero P x₁) ∈ c.φ.source := by rw [proj_fiberZero P]; exact hx₁
  refine MPolyfold.isScSmoothMap_of_local fun y => ?_
  by_cases hw : P (B.oneVal y) ∈ c.φ.source
  · refine ⟨oneChart hc y, oneChart hc y, (oneChart hc y).source, B.isChart_oneChart hc y,
      B.isChart_oneChart hc y, (oneChart hc y).isOpen_source, c.mem_source_of_proj hw,
      subset_rfl, fun y' hy' => ?_, ?_⟩
    · change cutOff c χ x₁ (B.oneVal y') ∈ c.toPartialEquiv.source
      have h1 : B.oneVal y' ∈ c.toPartialEquiv.source := hy'
      rw [c.source_eq] at h1
      exact cutOff_mem_source ha h1
    · rw [(oneChart hc y).image_source]
      refine hG.congr fun z hz => ?_
      have hk : ((z.1, c.F.toBase 1 z.2) : c.φ.model.E 0 × c.F 0) ∈ c.K := hz
      have hkt : ((z.1, c.F.toBase 1 z.2) : c.φ.model.E 0 × c.F 0) ∈ c.toPartialEquiv.target := by
        rw [c.target_eq]; exact hk
      have hks : P (c.toPartialEquiv.symm (z.1, c.F.toBase 1 z.2)) ∈ c.φ.source := by
        have := c.toPartialEquiv.map_target hkt
        rw [c.source_eq] at this; exact this
      have hzO : z.1 ∈ c.φ.model.O := by rw [← c.base_K]; exact ⟨_, hk, rfl⟩
      change c.cutMapOne (χ ∘ c.φ.symm) (c.φ x₁) z =
        c.liftOne (cutOff c χ x₁ (B.oneVal ((oneChart hc y).symm z)))
      rw [oneChart_symm_apply hc y hz]
      unfold StrongBundleChart.liftOne
      rw [apply_cutOff ha hks, c.toPartialEquiv.right_inv hkt,
        ← StrongBundleChart.toBase_cutMapOne ha hzO]
      exact Prod.ext rfl (Function.leftInverse_invFun (c.F.toBase_injective 1) _).symm
  · have hwt : P (B.oneVal y) ∉ tsupport χ := fun h => hw (hχs h)
    obtain ⟨c', hc', hwc'⟩ := B.atlas.cover (B.oneVal y)
    set V := (oneChart hc' y).source ∩ (P ∘ B.oneVal) ⁻¹' (tsupport χ)ᶜ with hV
    have hVo : IsOpen V := (oneChart hc' y).isOpen_source.inter
      ((isClosed_tsupport χ).isOpen_compl.preimage (B.continuous.comp B.continuous_oneVal))
    have hconst : ∀ y' ∈ V, cutOff c χ x₁ (B.oneVal y') = fiberZero P x₁ := fun y' hy' =>
      cutOff_of_eq_zero ha hx₁ (image_eq_zero_of_notMem_tsupport hy'.2)
    set y₁ := B.zeroOne x₁ with hy₁
    refine ⟨oneChart hc' y, oneChart hc y₁, V, B.isChart_oneChart hc' y,
      B.isChart_oneChart hc y₁, hVo, ⟨hwc', hwt⟩, inter_subset_left, fun y' hy' => ?_, ?_⟩
    · change cutOff c χ x₁ (B.oneVal y') ∈ c.toPartialEquiv.source
      rw [hconst y' hy']; exact c.mem_source_of_proj hP0
    · have hrep : ∀ z ∈ (oneChart hc' y) '' V,
          ((oneChart hc y₁) ∘ oneRestrict B B (cutOff c χ x₁) (mapsTo_oneSet_cutOff ha hc) ∘
            (oneChart hc' y).symm) z = (c.φ x₁, 0) := by
        rintro _ ⟨y', hy', rfl⟩
        change c.liftOne (cutOff c χ x₁ (B.oneVal ((oneChart hc' y).symm (oneChart hc' y y')))) = _
        rw [(oneChart hc' y).symm_apply_apply hy'.1, hconst y' hy', liftOne_fiberZero hx₁]
      refine ⟨fun z hz => ?_, fun R' hR' => ?_⟩
      · rw [hrep z hz]
        change (c.φ x₁, c.F.toBase 1 0) ∈ c.K
        rw [map_zero]; exact c.zero_mem_K (c.φ.mapsTo_model _ hx₁)
      · exact (isScSmooth_const_of_mem_smooth R'.isScDomain
          (ScBanach.mk_zero_mem_smooth_prod hu₁)).congr R'.isScDomain fun q hq =>
            (hrep _ (hR' ▸ R'.apply_mem_retract hq)).symm

include ha hc hχ hχs hx₁ hu₁ in
/-- **The contraction is a strong bundle map of `Y`.** -/
theorem isStrongBundleMap_cutOff :
    B.IsStrongBundleMap B (cutOffBase c χ x₁) (cutOff c χ x₁) where
  covers := covers_cutOff ha
  fiber_linear := fiber_linear_cutOff ha
  isScSmoothMap := isScSmoothMap_cutOff ha hc hχ hχs hx₁ hu₁
  mapsTo_oneSet := mapsTo_oneSet_cutOff ha hc
  isScSmoothMap_one := isScSmoothMap_one_cutOff ha hc hχ hχs hx₁ hu₁

end StrongBundle

end Global

/-! ### Strong bundle isomorphisms of `Y|U` can be cut off -/

section Extension

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **With sc-smooth bump functions on the base, strong bundle isomorphisms of `Y|U` can be cut
off** (`StrongBundle.HasLocalIsoExtension`).  In a strong bundle chart around `x`, let `S` be
the intersection of `C` with a ball around `φ(x)`, so small that `S ⊆ U_R` and
`φ⁻¹(r(S)) ⊆ U`; let `u₁ ∈ S ∩ O` be a smooth point and `χ` a bump function with values in
`[0, 1]`, `χ = 1` on a neighbourhood `V` of `x` and `supp χ ⊆ U ∩ φ⁻¹(S)`.  The contraction
`c(w) = Φ⁻¹(R(u₁ + χ(u − u₁), χ h))`, `Φ(w) = (u, h)`, extended by the constant `0_{x₁}`, is a
strong bundle map of `Y` with values in `Y|U` (`S` is convex) and the identity over `V`; for a
strong bundle isomorphism `Θ` of `Y|U` the map `Θ ∘ c` is a strong bundle map of `Y` which
agrees with `Θ` over `V`. -/
theorem MPolyfold.AdmitsBumpFunctions.hasLocalIsoExtension (hbump : PX.AdmitsBumpFunctions) :
    B.HasLocalIsoExtension := by
  intro x O hO hxO
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem B x
  refine ⟨O ∩ c.φ.source, hO.inter c.φ.isOpen_source, ⟨hxO, hxc⟩, inter_subset_left,
    fun U hU hxU _ => ?_⟩
  have hR := c.isRetraction
  set u₀ := c.φ x with hu₀
  have hu₀O : u₀ ∈ c.φ.model.O := c.φ.mapsTo_model x hxc
  have hOU : c.φ.model.O ⊆ c.U := fun z hz =>
    (hR.baseRetraction c.relOpen).retract_subset (by rw [c.base_retract]; exact hz)
  have hrfix : ∀ z ∈ c.φ.model.O, r c.R z = z := fun z hz =>
    (hR.baseRetraction c.relOpen).apply_eq_self_of_mem_retract (by rw [c.base_retract]; exact hz)
  have hrc : ContinuousOn (r c.R) c.U :=
    (hR.baseRetraction c.relOpen).isScSmooth.isSc1.isSc0.continuousOn_base
  have hrO : ∀ u ∈ c.U, r c.R u ∈ c.φ.model.O := fun u hu => c.r_mem_O hu
  obtain ⟨W', hW'o, hUW'⟩ := c.relOpen.relOpen
  have hCq := c.relOpen.isPartialQuadrant
  have hUC : c.U ⊆ c.φ.model.C := fun u hu => by rw [hUW'] at hu; exact hu.2
  have hu₀U : u₀ ∈ c.U := hOU hu₀O
  have hu₀W' : u₀ ∈ W' := by have := hu₀U; rw [hUW'] at this; exact this.1
  -- `φ⁻¹ ∘ r` is continuous on `U_R`
  have hgc : ContinuousOn (c.φ.symm ∘ r c.R) c.U := c.φ.continuousOn_invFun.comp hrc hrO
  have hgx : (c.φ.symm ∘ r c.R) u₀ = x := by
    rw [Function.comp_apply, hrfix u₀ hu₀O, hu₀, c.φ.symm_apply_apply hxc]
  obtain ⟨W'', hW''o, hu₀W'', hW''⟩ : ∃ W'' : Set (c.φ.model.E 0), IsOpen W'' ∧ u₀ ∈ W'' ∧
      W'' ∩ c.U ⊆ (c.φ.symm ∘ r c.R) ⁻¹' U := by
    have h1 := (hgc u₀ hu₀U).preimage_mem_nhdsWithin (hU.mem_nhds (hgx.symm ▸ hxU))
    obtain ⟨W'', hW''o, hu, hsub⟩ := mem_nhdsWithin.1 h1
    exact ⟨W'', hW''o, hu, hsub⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hW'o.inter hW''o) u₀ ⟨hu₀W', hu₀W''⟩
  set S := Metric.ball u₀ δ ∩ c.φ.model.C with hS
  have hSconv : Convex ℝ S := (convex_ball u₀ δ).inter hCq.convex
  have hSU : S ⊆ c.U := fun u hu => by rw [hUW']; exact ⟨(hball hu.1).1, hu.2⟩
  have hSg : ∀ u ∈ S, c.φ.symm (r c.R u) ∈ U := fun u hu => hW'' ⟨(hball hu.1).2, hSU hu⟩
  -- a smooth centre `u₁ ∈ S ∩ O`
  obtain ⟨u₁, hu₁S, hu₁O, hu₁s⟩ : ∃ u₁, u₁ ∈ S ∧ u₁ ∈ c.φ.model.O ∧
      u₁ ∈ c.φ.model.E.smooth := by
    have h1 : r c.R ⁻¹' Metric.ball u₀ δ ∈ 𝓝[c.U] u₀ :=
      (hrc u₀ hu₀U).preimage_mem_nhdsWithin
        (by rw [hrfix u₀ hu₀O]; exact Metric.ball_mem_nhds _ hδ)
    obtain ⟨T, hTo, hu₀T, hTsub⟩ := mem_nhdsWithin.1 h1
    have hcl : u₀ ∈ closure (interior c.φ.model.C) := by
      rw [hCq.convex.closure_interior_eq_closure_of_nonempty_interior
        (hCq.interior_lvlSet_nonempty 0)]
      exact subset_closure (hUC hu₀U)
    obtain ⟨e₀, he₀T, he₀C⟩ := mem_closure_iff.1 hcl (T ∩ W') (hTo.inter hW'o) ⟨hu₀T, hu₀W'⟩
    have hd : Dense (c.φ.model.E.smooth : Set (c.φ.model.E 0)) := c.φ.model.E.dense_smooth 0
    obtain ⟨e, he, hes⟩ := hd.inter_open_nonempty ((T ∩ W') ∩ interior c.φ.model.C)
      ((hTo.inter hW'o).inter _root_.isOpen_interior) ⟨e₀, he₀T, he₀C⟩
    have heU : e ∈ c.U := by rw [hUW']; exact ⟨he.1.2, interior_subset he.2⟩
    refine ⟨r c.R e, ⟨hTsub ⟨he.1.1, heU⟩, hUC (hOU (hrO e heU))⟩, hrO e heU, ?_⟩
    refine c.φ.model.E.mem_smooth_iff.2 fun m => ?_
    obtain ⟨y, hy⟩ := c.φ.model.E.mem_smooth_iff.1 hes m
    exact (hR.preserves_filtration m 0 (Nat.zero_le _) e heU ⟨y, hy⟩ 0 ⟨0, map_zero _⟩).1
  set x₁ := c.φ.symm u₁ with hx₁
  have hx₁c : x₁ ∈ c.φ.source := c.φ.symm_mapsTo hu₁O
  have hφx₁ : c.φ x₁ = u₁ := c.φ.apply_symm_apply hu₁O
  -- the bump function
  have hGo : IsOpen (c.φ.source ∩ c.φ ⁻¹' Metric.ball u₀ δ) :=
    c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source Metric.isOpen_ball
  obtain ⟨χ, hχ, hχ01, -, hχs, hχ1⟩ := proposition_5_5_3 hbump (hU.inter hGo)
    ⟨hxU, hxc, Metric.mem_ball_self hδ⟩
  have hχsrc : tsupport χ ⊆ c.φ.source := fun y hy => (hχs hy).2.1
  have haS : ∀ u ∈ c.φ.model.O, c.cutBase (χ ∘ c.φ.symm) (c.φ x₁) u ∈ S := fun u hu => by
    rw [hφx₁]
    unfold StrongBundleChart.cutBase
    by_cases h0 : χ (c.φ.symm u) = 0
    · rw [Function.comp_apply, h0, zero_smul, add_zero]; exact hu₁S
    · have hsup : c.φ.symm u ∈ tsupport χ := subset_tsupport _ h0
      have huS : u ∈ S := ⟨by
        have := (hχs hsup).2.2
        rwa [mem_preimage, c.φ.apply_symm_apply hu] at this, hUC (hOU hu)⟩
      exact hSconv.add_smul_sub_mem hu₁S huS (hχ01 _)
  have ha : ∀ u ∈ c.φ.model.O, c.cutBase (χ ∘ c.φ.symm) (c.φ x₁) u ∈ c.U :=
    fun u hu => hSU (haS u hu)
  have hC := StrongBundle.isStrongBundleMap_cutOff ha hc hχ hχsrc hx₁c (hφx₁ ▸ hu₁s)
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.1 hχ1
  have hVU : V ⊆ U := fun y hy =>
    (hχs (subset_tsupport _ (by rw [mem_support, hVsub hy]; exact one_ne_zero))).1
  refine ⟨V, hVo, hxV, hVU, fun β Φ hΦ => ?_⟩
  -- the contraction has values in `Y|U`
  have hκU : ∀ y, StrongBundle.cutOffBase c χ x₁ y ∈ U := fun y => by
    unfold StrongBundle.cutOffBase
    by_cases hy : y ∈ c.φ.source
    · rw [StrongBundle.proj_cutOff ha (by rw [proj_fiberZero P]; exact hy), proj_fiberZero P]
      exact hSg _ (haS _ (c.φ.mapsTo_model y hy))
    · rw [StrongBundle.cutOff, if_neg (by rw [proj_fiberZero P]; exact hy), proj_fiberZero P]
      have := hSg u₁ hu₁S
      rwa [hrfix u₁ hu₁O] at this
  have hCU : ∀ w, P (StrongBundle.cutOff c χ x₁ w) ∈ U := fun w => by
    rw [hC.covers]; exact hκU _
  obtain ⟨Ψ, hΨ⟩ := hΦ.isScDiffeoOn_zero
  obtain ⟨Φ₁, Ψ₁, hΦ₁, hΨ₁⟩ := hΦ.isScDiffeoOn_one
  have hcov : ∀ w, P ((Φ ∘ StrongBundle.cutOff c χ x₁) w) =
      (β ∘ StrongBundle.cutOffBase c χ x₁) (P w) := fun w => by
    simp only [Function.comp_apply]
    rw [hΦ.covers (hCU w), hC.covers]
  have hone : MapsTo (Φ ∘ StrongBundle.cutOff c χ x₁) B.oneSet B.oneSet := fun w hw => by
    have h1 := hC.mapsTo_oneSet hw
    have h2 := hΦ₁ (B.oneMk _ h1) (hCU w)
    change Φ (StrongBundle.cutOff c χ x₁ w) ∈ B.oneSet
    rw [show Φ (StrongBundle.cutOff c χ x₁ w) = B.oneVal (Φ₁ (B.oneMk _ h1)) from h2.symm]
    exact B.oneVal_mem _
  refine ⟨β ∘ StrongBundle.cutOffBase c χ x₁, Φ ∘ StrongBundle.cutOff c χ x₁,
    ⟨hcov, fun y => ?_, ?_, hone, ?_⟩, fun w hw => ?_⟩
  · obtain ⟨L, hL⟩ := hΦ.fiber_linear _ (hκU y)
    have : fiberRestrict P P _ _ hcov y = ⇑(L.comp (hC.fiberLinearMap y)) :=
      funext fun v => Subtype.ext (hL (hC.fiberLinearMap y v)).symm
    rw [this]; exact LinearMap.isLinear _
  · exact MPolyfold.IsScSmoothOn.comp hΨ.isScSmoothOn hC.isScSmoothMap fun w _ => hCU w
  · have h := MPolyfold.IsScSmoothOn.comp hΨ₁.isScSmoothOn hC.isScSmoothMap_one
      fun y _ => hCU (B.oneVal y)
    exact h.congr fun y _ => B.oneVal_injective (hΦ₁ _ (hCU (B.oneVal y)))
  · have h1 : χ (P w) = 1 := hVsub hw
    have hsrc : P w ∈ c.φ.source :=
      hχsrc (subset_tsupport _ (by rw [mem_support, h1]; exact one_ne_zero))
    simp only [Function.comp_apply]
    rw [StrongBundle.cutOff_of_eq_one ha hsrc h1]

end Extension

/-! ### The formal local regularity property gives the germ form -/

section Germ

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  {E : EpStrongBundle X B}

/-- **Definition 8.4.2, p. 382: the formal `IsLR` gives the germ form when the object space
admits sc-smooth bump functions** (Definition 5.3.1). -/
theorem EpStrongBundle.IsLR.isLRGerm_of_admitsBumpFunctions (hE : E.IsLR)
    (hbump : X.PObj.AdmitsBumpFunctions) : E.IsLRGerm :=
  hE.isLRGerm hbump.hasLocalIsoExtension

end Germ

end Polyfold
