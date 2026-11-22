import Polyfold.Chapter10.StrongBundleWeakFibredProductPullback
import Polyfold.Chapter10.LocalizationLRBundleBase
import Polyfold.Chapter10.StrongBundleLocalIso

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.6 "A Strong Bundle Version", tools for **Theorem 19.6.13** (p. 900) and the "Alternative
Approach" (pp. 900–905).  Numbers and pages are the 2021 text's.

# Transporting a strong bundle along a homeomorphism; local criteria

## The text, paraphrased

(p. 901) "We see from (19.15) that `H` as well as `H'` define uniquely determined … strong bundle
structures for `p`": a bijection `H : M(Ψ, Ψ') ₛ×ₚ K → M(Ψ̄, Ψ̄')`, linear on the fibres and
covering the identity of `M(Ψ, Ψ')`, carries the strong bundle structure of the fibred product
over to `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')`, characterized by "`H` is a strong bundle isomorphism".
(p. 905) "since each of the target maps is a local strong bundle isomorphism …, it follows that
the identity map is a local strong bundle isomorphism, which implies that it is a strong bundle
isomorphism".

## What is formalized (namespace `Polyfold`)

* `StrongBundleChart.transport e L hL c` and **`StrongBundle.transport B e L hL`**: for a strong
  bundle `P : Y → X`, a homeomorphism `e : Y ≃ₜ Y'` and linear isomorphisms
  `L x : P⁻¹(x) ≃ P'⁻¹(x)` given by `e`, the strong bundle `P' : Y' → X` with the charts
  `Φ ∘ e⁻¹`.  `StrongBundle.mem_oneSet_transport_iff` (`Y'_{0,1} = e(Y_{0,1})`),
  `isStrongBundleMap_transport` (`e` is a strong bundle map covering the identity),
  `isStrongBundleMap_transport_symm` (`e⁻¹` is one), `isStrongBundleIso_transport`.
* `StrongBundle.IsStrongBundleIso.isStrongBundleIsoOn_univ`: a strong bundle isomorphism is
  one in the sense of Chapter 8 over the whole base.
* `StrongBundle.IsStrongBundleMap.of_local`: **a map covering `f`, linear on the fibres, which is
  near every fibre sc-smooth on `[0]` and agrees on `[1]` with an sc-smooth map, is a strong
  bundle map** (smoothness is local).
* `StrongBundle.isStrongBundleIsoOn_univ_of_local`: a strong bundle map covering the identity
  which is near every fibre a local strong bundle isomorphism (with given local inverses), and
  bijective, is a strong bundle isomorphism over the whole base.
* `StrongBundle.isStrongBundleMap_id_of_isStrongBundleIsoOn`,
  `StrongBundle.isStrongBundleIso_id_of_isStrongBundleIsoOn`: **two strong bundle structures on
  the same `P : Y → X` for which a map `S : Y → Y''` covering `f` is, near every point, a local
  strong bundle isomorphism into the same strong bundle agree**: the identity is a strong bundle
  isomorphism (the argument of p. 905).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

/-! ### Transport of a strong bundle along a homeomorphism -/

section Transport

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {Y' : Type*} [TopologicalSpace Y'] {P' : Y' → X}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  (e : Y ≃ₜ Y') (L : ∀ x, P ⁻¹' {x} ≃ₗ[ℝ] P' ⁻¹' {x}) (hL : ∀ x v, (L x v : Y') = e v)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
include hL in
theorem transport_P' (y : Y) : P' (e y) = P y := by
  rw [← hL (P y) ⟨y, rfl⟩]; exact (L (P y) ⟨y, rfl⟩).2

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
include hL in
theorem transport_P (y' : Y') : P (e.symm y') = P' y' := by
  rw [← transport_P' e L hL, e.apply_symm_apply]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
include hL in
theorem transport_symm_val (x : X) (v : P' ⁻¹' {x}) : ((L x).symm v : Y) = e.symm v := by
  rw [← e.symm_apply_apply ((L x).symm v : Y), ← hL, LinearEquiv.apply_symm_apply]

namespace StrongBundleChart

/-- **The transported chart** `Φ ∘ e⁻¹ : P'⁻¹(V) → K`. -/
def transport (c : StrongBundleChart PX P) : StrongBundleChart PX P' where
  φ := c.φ
  isChart := c.isChart
  F := c.F
  U := c.U
  R := c.R
  relOpen := c.relOpen
  isRetraction := c.isRetraction
  base_retract := c.base_retract
  toPartialEquiv :=
    { toFun := fun y => c (e.symm y)
      invFun := fun z => e (c.toPartialEquiv.symm z)
      source := e.symm ⁻¹' c.toPartialEquiv.source
      target := c.toPartialEquiv.target
      map_source' := fun y hy => c.toPartialEquiv.map_source hy
      map_target' := fun z hz => by
        change e.symm (e (c.toPartialEquiv.symm z)) ∈ c.toPartialEquiv.source
        rw [e.symm_apply_apply]; exact c.toPartialEquiv.map_target hz
      left_inv' := fun y hy => by
        rw [c.toPartialEquiv.left_inv hy, e.apply_symm_apply]
      right_inv' := fun z hz => by
        rw [e.symm_apply_apply]; exact c.toPartialEquiv.right_inv hz }
  source_eq := by
    ext y
    change e.symm y ∈ c.toPartialEquiv.source ↔ P' y ∈ c.φ.source
    rw [c.source_eq, mem_preimage, transport_P e L hL]
  target_eq := c.target_eq
  continuousOn_toFun :=
    c.continuousOn_toFun.comp e.symm.continuous.continuousOn fun _ hy => hy
  continuousOn_invFun := e.continuous.comp_continuousOn c.continuousOn_invFun
  covers y hy := by
    change (c (e.symm y)).1 = c.φ (P' y)
    rw [c.covers _ hy, transport_P e L hL]
  fiber_linear x hx := by
    have hc := c.fiber_linear x hx
    refine ⟨fun v w => ?_, fun a v => ?_⟩
    · change (c (e.symm ((v + w : P' ⁻¹' {x}) : Y'))).2 =
        (c (e.symm (v : Y'))).2 + (c (e.symm (w : Y'))).2
      have := hc.map_add ((L x).symm v) ((L x).symm w)
      rw [← map_add] at this
      simp only [transport_symm_val e L hL] at this
      exact this
    · change (c (e.symm ((a • v : P' ⁻¹' {x}) : Y'))).2 = a • (c (e.symm (v : Y'))).2
      have := hc.map_smul a ((L x).symm v)
      rw [← map_smul] at this
      simp only [transport_symm_val e L hL] at this
      exact this

variable {e L hL}

@[simp] theorem transport_apply (c : StrongBundleChart PX P) (y : Y') :
    c.transport e L hL y = c (e.symm y) := rfl

theorem transport_source (c : StrongBundleChart PX P) :
    (c.transport e L hL).toPartialEquiv.source = e.symm ⁻¹' c.toPartialEquiv.source := rfl

theorem transport_symm_apply (c : StrongBundleChart PX P) (z : c.φ.model.E 0 × c.F 0) :
    (c.transport e L hL).toPartialEquiv.symm z = e (c.toPartialEquiv.symm z) := rfl

theorem transport_K (c : StrongBundleChart PX P) : (c.transport e L hL).K = c.K := rfl

theorem transport_overlap (c c' : StrongBundleChart PX P) :
    (c.transport e L hL).overlap (c'.transport e L hL) = c.overlap c' := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨e.symm y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e y, ?_, ?_⟩
    · change e.symm (e y) ∈ c.toPartialEquiv.source ∧ e.symm (e y) ∈ c'.toPartialEquiv.source
      rw [e.symm_apply_apply]; exact hy
    · change c (e.symm (e y)) = c y
      rw [e.symm_apply_apply]

theorem transport_transition (c c' : StrongBundleChart PX P) :
    (c.transport e L hL).transition (c'.transport e L hL) = c.transition c' := by
  funext z
  change c' (e.symm (e (c.toPartialEquiv.symm z))) = c' (c.toPartialEquiv.symm z)
  rw [e.symm_apply_apply]

theorem transport_compatible {c c' : StrongBundleChart PX P} (h : c.Compatible c') :
    (c.transport e L hL).Compatible (c'.transport e L hL) := by
  unfold Compatible
  rw [transport_overlap, transport_overlap, transport_transition, transport_transition]
  exact h

theorem transport_liftOne (c : StrongBundleChart PX P) (y : Y') :
    (c.transport e L hL).liftOne y = c.liftOne (e.symm y) := rfl

end StrongBundleChart

variable [T2Space Y] [ParacompactSpace Y] [T2Space Y'] [ParacompactSpace Y']

namespace StrongBundle

include hL in
/-- The fibres `P'⁻¹(x) ≅ P⁻¹(x)` as topological linear isomorphisms. -/
def transportFiberCLE (x : X) : P ⁻¹' {x} ≃L[ℝ] P' ⁻¹' {x} where
  toLinearEquiv := L x
  continuous_toFun := by
    have : (fun v : P ⁻¹' {x} => L x v) = fun v =>
        ⟨e v, show P' (e v) = x from (transport_P' e L hL (v : Y)).trans v.2⟩ := by
      funext v; exact Subtype.ext (hL x v)
    change Continuous fun v : P ⁻¹' {x} => L x v
    rw [this]
    exact (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    have : (fun v : P' ⁻¹' {x} => (L x).symm v) = fun v =>
        ⟨e.symm v, show P (e.symm v) = x from (transport_P e L hL (v : Y')).trans v.2⟩ := by
      funext v; exact Subtype.ext (transport_symm_val e L hL x v)
    change Continuous fun v : P' ⁻¹' {x} => (L x).symm v
    rw [this]
    exact (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

variable (B : StrongBundle PX P)

/-- **The strong bundle `P' : Y' → X` transported along `e`**: the charts `Φ ∘ e⁻¹`, `Φ` in the
atlas of `B`. -/
def transport : StrongBundle PX P' where
  continuous := by
    have : P' = P ∘ e.symm := funext fun y => (transport_P e L hL y).symm
    rw [this]; exact B.continuous.comp e.symm.continuous
  surjective x := by
    obtain ⟨y, hy⟩ := B.surjective x
    exact ⟨e y, by rw [transport_P' e L hL, hy]⟩
  banachable x := by
    obtain ⟨Bsp, h1, h2, h3, ⟨f⟩⟩ := B.banachable x
    exact ⟨Bsp, h1, h2, h3, ⟨(transportFiberCLE e L hL x).symm.trans f⟩⟩
  atlas :=
    { charts := (StrongBundleChart.transport e L hL) '' B.atlas.charts
      compatible := by
        rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
        exact StrongBundleChart.transport_compatible (B.atlas.compatible c hc c' hc')
      cover y := by
        obtain ⟨c, hc, hy⟩ := B.atlas.cover (e.symm y)
        exact ⟨_, ⟨c, hc, rfl⟩, hy⟩ }

variable {e L hL}

theorem transport_charts :
    (B.transport e L hL).atlas.charts = (StrongBundleChart.transport e L hL) '' B.atlas.charts :=
  rfl

theorem transport_mem_charts {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts) :
    c.transport e L hL ∈ (B.transport e L hL).atlas.charts := ⟨c, hc, rfl⟩

/-- **`Y'_{0,1} = e(Y_{0,1})`.** -/
theorem mem_oneSet_transport_iff (y : Y') :
    y ∈ (B.transport e L hL).oneSet ↔ e.symm y ∈ B.oneSet := by
  obtain ⟨c, hc, hy⟩ := B.atlas.cover (e.symm y)
  rw [(B.transport e L hL).mem_oneSet_iff (B.transport_mem_charts hc)
    (show y ∈ (c.transport e L hL).toPartialEquiv.source from hy), B.mem_oneSet_iff hc hy]
  rfl

theorem mapsTo_oneSet_transport : MapsTo e B.oneSet (B.transport e L hL).oneSet := fun y hy => by
  rw [mem_oneSet_transport_iff, e.symm_apply_apply]; exact hy

theorem mapsTo_oneSet_transport_symm :
    MapsTo e.symm (B.transport e L hL).oneSet B.oneSet := fun y hy =>
  (B.mem_oneSet_transport_iff y).1 hy

/-- `e : Y[0] → Y'[0]` is sc-smooth: in the charts `Φ`, `Φ ∘ e⁻¹` it is the identity of `K`. -/
theorem isScSmoothMap_transport :
    B.toMPolyfold0.IsScSmoothMap (B.transport e L hL).toMPolyfold0 e := by
  refine MPolyfold.isScSmoothMap_of_forall_charts fun y => ?_
  obtain ⟨c, hc, hy⟩ := B.atlas.cover y
  refine ⟨c.toMChart B.continuous, (c.transport e L hL).toMChart (B.transport e L hL).continuous,
    B.isChart_toMChart hc, (B.transport e L hL).isChart_toMChart (B.transport_mem_charts hc), hy,
    fun z hz => ?_, ?_⟩
  · change e.symm (e z) ∈ c.toPartialEquiv.source
    rw [e.symm_apply_apply]; exact hz
  · refine (isScSmoothRetractMap_id _).congr fun z hz => ?_
    have hz' : z ∈ c.toPartialEquiv.target := by
      rw [c.target_eq]; exact hz
    change z = c (e.symm (e (c.toPartialEquiv.symm z)))
    rw [e.symm_apply_apply, c.toPartialEquiv.right_inv hz']

/-- `e⁻¹ : Y'[0] → Y[0]` is sc-smooth. -/
theorem isScSmoothMap_transport_symm :
    (B.transport e L hL).toMPolyfold0.IsScSmoothMap B.toMPolyfold0 e.symm := by
  refine MPolyfold.isScSmoothMap_of_forall_charts fun y => ?_
  obtain ⟨c, hc, hy⟩ := B.atlas.cover (e.symm y)
  refine ⟨(c.transport e L hL).toMChart (B.transport e L hL).continuous, c.toMChart B.continuous,
    (B.transport e L hL).isChart_toMChart (B.transport_mem_charts hc), B.isChart_toMChart hc, hy,
    fun z hz => hz, ?_⟩
  · refine (isScSmoothRetractMap_id _).congr fun z hz => ?_
    have hz' : z ∈ c.toPartialEquiv.target := by
      rw [c.target_eq]; exact hz
    change z = c (e.symm (e (c.toPartialEquiv.symm z)))
    rw [e.symm_apply_apply, c.toPartialEquiv.right_inv hz']

/-- `e[1] : Y[1] → Y'[1]` is sc-smooth: in the charts `Φ[1]`, `(Φ ∘ e⁻¹)[1]` it is the identity
of `K[1]`. -/
theorem isScSmoothMap_one_transport :
    B.toMPolyfold1.IsScSmoothMap (B.transport e L hL).toMPolyfold1
      (oneRestrict B (B.transport e L hL) e B.mapsTo_oneSet_transport) := by
  refine MPolyfold.isScSmoothMap_of_forall_charts fun y => ?_
  obtain ⟨c, hc, hy⟩ := B.atlas.cover (B.oneVal y)
  have hc' := B.transport_mem_charts (e := e) (L := L) (hL := hL) hc
  refine ⟨oneChart hc y, oneChart hc' (oneRestrict B _ e B.mapsTo_oneSet_transport y),
    B.isChart_oneChart hc y, (B.transport e L hL).isChart_oneChart hc' _, hy, fun z hz => ?_, ?_⟩
  · change e.symm (e (B.oneVal z)) ∈ c.toPartialEquiv.source
    rw [e.symm_apply_apply]; exact hz
  · refine (isScSmoothRetractMap_id _).congr fun z hz => ?_
    change z = c.liftOne (e.symm (e (B.oneVal ((oneChart hc y).symm z))))
    rw [e.symm_apply_apply, oneChart_symm_apply hc y hz]
    exact (liftOne_symm (c := c) hz).symm

/-- `e⁻¹[1] : Y'[1] → Y[1]` is sc-smooth. -/
theorem isScSmoothMap_one_transport_symm :
    (B.transport e L hL).toMPolyfold1.IsScSmoothMap B.toMPolyfold1
      (oneRestrict (B.transport e L hL) B e.symm B.mapsTo_oneSet_transport_symm) := by
  refine MPolyfold.isScSmoothMap_of_forall_charts fun y => ?_
  obtain ⟨c, hc, hy⟩ := B.atlas.cover (e.symm ((B.transport e L hL).oneVal y))
  have hc' := B.transport_mem_charts (e := e) (L := L) (hL := hL) hc
  refine ⟨oneChart hc' y, oneChart hc (oneRestrict _ B e.symm B.mapsTo_oneSet_transport_symm y),
    (B.transport e L hL).isChart_oneChart hc' y, B.isChart_oneChart hc _, hy, fun z hz => hz, ?_⟩
  · refine (isScSmoothRetractMap_id _).congr fun z hz => ?_
    change z = c.liftOne (e.symm ((B.transport e L hL).oneVal ((oneChart hc' y).symm z)))
    rw [oneChart_symm_apply hc' y hz]
    change z = c.liftOne (e.symm (e (c.toPartialEquiv.symm (z.1, c.F.toBase 1 z.2))))
    rw [e.symm_apply_apply]
    exact (liftOne_symm (c := c) hz).symm

/-- **`e` is a strong bundle map covering the identity.** -/
theorem isStrongBundleMap_transport : B.IsStrongBundleMap (B.transport e L hL) id e where
  covers y := transport_P' e L hL y
  fiber_linear x := by
    have h : fiberRestrict P P' id e (transport_P' (P := P) (P' := P') e L hL) x =
        fun v => L x v := by
      funext v; exact Subtype.ext (hL x v).symm
    rw [h]; exact (L x).toLinearMap.isLinear
  isScSmoothMap := B.isScSmoothMap_transport
  mapsTo_oneSet := B.mapsTo_oneSet_transport
  isScSmoothMap_one := B.isScSmoothMap_one_transport

/-- **`e⁻¹` is a strong bundle map covering the identity.** -/
theorem isStrongBundleMap_transport_symm :
    (B.transport e L hL).IsStrongBundleMap B id e.symm where
  covers y := transport_P e L hL y
  fiber_linear x := by
    have h : fiberRestrict P' P id e.symm (transport_P (P := P) (P' := P') e L hL) x =
        fun v => (L x).symm v := by
      funext v; exact Subtype.ext (transport_symm_val e L hL x v).symm
    rw [h]; exact (L x).symm.toLinearMap.isLinear
  isScSmoothMap := B.isScSmoothMap_transport_symm
  mapsTo_oneSet := B.mapsTo_oneSet_transport_symm
  isScSmoothMap_one := B.isScSmoothMap_one_transport_symm

/-- **`e` is a strong bundle isomorphism `B → B.transport e` covering the identity** (the
transported structure is characterized by this property). -/
theorem isStrongBundleIso_transport :
    B.IsStrongBundleIso (B.transport e L hL) id e id e.symm :=
  ⟨B.isStrongBundleMap_transport, B.isStrongBundleMap_transport_symm, e.symm_apply_apply,
    e.apply_symm_apply⟩

end StrongBundle

end Transport

/-! ### Strong bundle isomorphisms over the whole base; local criteria -/

section Local

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]

namespace StrongBundle

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {f : X → X'} {Φ : Y → Y'}

/-- **A strong bundle isomorphism is a strong bundle isomorphism over the whole base.** -/
theorem IsStrongBundleIso.isStrongBundleIsoOn_univ {g : X' → X} {Ψ : Y' → Y}
    (h : B.IsStrongBundleIso B' f Φ g Ψ) :
    B.IsStrongBundleIsoOn B' h.toMap univ univ := by
  refine ⟨⟨g, ?_⟩, ⟨Ψ, ?_⟩, ⟨oneRestrict B' B Ψ h.invMap.mapsTo_oneSet, ?_⟩⟩
  · exact ⟨h.toMap.isScSmoothMap_base, h.invMap.isScSmoothMap_base, mapsTo_univ _ _,
      mapsTo_univ _ _, fun x _ => h.base_left_inv x, fun x _ => h.base_right_inv x⟩
  · exact ⟨h.toMap.isScSmoothMap, h.invMap.isScSmoothMap, mapsTo_univ _ _, mapsTo_univ _ _,
      fun y _ => h.left_inv y, fun y _ => h.right_inv y⟩
  · exact ⟨h.toMap.isScSmoothMap_one, h.invMap.isScSmoothMap_one, mapsTo_univ _ _,
      mapsTo_univ _ _, fun y _ => B.oneVal_injective (h.left_inv _),
      fun y _ => B'.oneVal_injective (h.right_inv _)⟩

/-- **Strong bundle maps are local** (smoothness is a local property): a map `Φ` covering `f`,
linear on the fibres, which near every fibre is sc-smooth on `[0]` and agrees on `[1]` with an
sc-smooth map of `Y[1]`, is a strong bundle map. -/
theorem IsStrongBundleMap.of_local (hcov : ∀ y, P' (Φ y) = f (P y))
    (hlin : ∀ x, IsLinearMap ℝ (fiberRestrict P P' f Φ hcov x))
    (hloc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      B.toMPolyfold0.IsScSmoothOn B'.toMPolyfold0 Φ (P ⁻¹' U) ∧
      ∃ Φ₁ : B.One → B'.One, (∀ y, P (B.oneVal y) ∈ U → B'.oneVal (Φ₁ y) = Φ (B.oneVal y)) ∧
        B.toMPolyfold1.IsScSmoothOn B'.toMPolyfold1 Φ₁ ((P ∘ B.oneVal) ⁻¹' U)) :
    B.IsStrongBundleMap B' f Φ := by
  have hmaps : MapsTo Φ B.oneSet B'.oneSet := fun y hy => by
    obtain ⟨U, -, hxU, -, Φ₁, h₁, -⟩ := hloc (P y)
    have := h₁ (B.oneMk y hy) hxU
    rw [oneVal_oneMk] at this
    rw [← this]; exact B'.oneVal_mem _
  refine ⟨hcov, hlin, ?_, hmaps, ?_⟩
  · refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun y _ => ?_
    obtain ⟨U, hU, hxU, h0, -⟩ := hloc (P y)
    exact ⟨P ⁻¹' U, hU.preimage B.continuous, hxU, subset_univ _, h0⟩
  · refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun y _ => ?_
    obtain ⟨U, hU, hxU, -, Φ₁, h₁, h₂⟩ := hloc (P (B.oneVal y))
    refine ⟨(P ∘ B.oneVal) ⁻¹' U, hU.preimage (B.continuous.comp B.continuous_oneVal), hxU,
      subset_univ _, h₂.congr fun z hz => ?_⟩
    apply B'.oneVal_injective
    rw [oneVal_oneRestrict]; exact h₁ z hz

/-- **A map which near every fibre is a local isomorphism (`IsLocalIso₂`) covering `f` is a
strong bundle map.** -/
theorem IsStrongBundleMap.of_isLocalIso₂ (hcov : ∀ y, P' (Φ y) = f (P y))
    (hloc : ∀ x : X, ∃ (U : Set X) (U' : Set X') (g : X' → X) (Ψ : Y' → Y), x ∈ U ∧
      B.IsLocalIso₂ B' f g Φ Ψ U U') :
    B.IsStrongBundleMap B' f Φ := by
  refine IsStrongBundleMap.of_local hcov (fun x => ?_) fun x => ?_
  · obtain ⟨U, U', g, Ψ, hx, hl⟩ := hloc x
    obtain ⟨L, hL⟩ := hl.fiber_linear x hx
    have e : fiberRestrict P P' f Φ hcov x = fun v => L v :=
      funext fun v => Subtype.ext (hL v).symm
    rw [e]; exact L.isLinear
  · obtain ⟨U, U', g, Ψ, hx, hl⟩ := hloc x
    obtain ⟨Φ₁, Ψ₁, h₁, -, h₃⟩ := hl.one
    exact ⟨U, hl.base.isOpen_source, hx, hl.zero.isScSmoothOn, Φ₁, h₁, h₃.isScSmoothOn⟩

/-- **A local isomorphism `Y|U → Y'|U'` (`IsLocalIso₂`) whose map is a strong bundle map is a
strong bundle isomorphism `Y|U → Y'|U'` in the sense of Chapter 8.** -/
theorem IsLocalIso₂.isStrongBundleIsoOn {g : X' → X} {Ψ : Y' → Y} {U : Set X} {U' : Set X'}
    (h : B.IsStrongBundleMap B' f Φ) (hl : B.IsLocalIso₂ B' f g Φ Ψ U U') :
    B.IsStrongBundleIsoOn B' h U U' := by
  obtain ⟨Φ₁, Ψ₁, h₁, -, h₃⟩ := hl.one
  refine ⟨⟨g, hl.base⟩, ⟨Ψ, hl.zero⟩, ⟨Ψ₁, h₃.congr_left fun y hy => ?_⟩⟩
  apply B'.oneVal_injective
  rw [oneVal_oneRestrict]; exact h₁ y hy

/-- **A bijective strong bundle map covering the identity which is near every fibre a local
strong bundle isomorphism is a strong bundle isomorphism over the whole base.** -/
theorem isStrongBundleIsoOn_univ_of_local {X : Type*} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] {PX : MPolyfold X} {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})]
    [∀ x, Module ℝ (P ⁻¹' {x})] {P' : Y' → X} [∀ x, AddCommGroup (P' ⁻¹' {x})]
    [∀ x, Module ℝ (P' ⁻¹' {x})] {B : StrongBundle PX P} {B' : StrongBundle PX P'}
    {Φ : Y → Y'} (h : B.IsStrongBundleMap B' id Φ) (Φinv : Y' → Y)
    (hl : ∀ y, Φinv (Φ y) = y) (hr : ∀ y', Φ (Φinv y') = y')
    (hloc : ∀ x : X, ∃ U : Set X, x ∈ U ∧ B.IsStrongBundleIsoOn B' h U U) :
    B.IsStrongBundleIsoOn B' h univ univ := by
  have hcov' : ∀ y', P (Φinv y') = P' y' := fun y' => by
    rw [← hr y', h.covers, hl]; rfl
  have hmaps1 : MapsTo Φinv B'.oneSet B.oneSet := fun y hy => by
    obtain ⟨U, hxU, hi⟩ := hloc (P' y)
    obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
    have hyU : P' (B'.oneVal (B'.oneMk y hy)) ∈ U := hxU
    have e₁ := congrArg B'.oneVal (hΨ₁.right_inv _ hyU)
    rw [oneVal_oneRestrict, oneVal_oneMk] at e₁
    have : Φinv y = B.oneVal (Ψ₁ (B'.oneMk y hy)) := (congrArg Φinv e₁.symm).trans (hl _)
    rw [this]; exact B.oneVal_mem _
  refine ⟨⟨id, MPolyfold.isScDiffeoOn_id isOpen_univ⟩, ⟨Φinv, ?_⟩,
    ⟨oneRestrict B' B Φinv hmaps1, ?_⟩⟩
  · refine ⟨h.isScSmoothMap, ?_, mapsTo_univ _ _, mapsTo_univ _ _, fun y _ => hl y,
      fun y _ => hr y⟩
    refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun y _ => ?_
    obtain ⟨U, hxU, hi⟩ := hloc (P' y)
    obtain ⟨Ψ, hΨ⟩ := hi.isScDiffeoOn_zero
    refine ⟨P' ⁻¹' U, hΨ.isOpen_target, hxU, subset_univ _, hΨ.isScSmoothOn_inv.congr ?_⟩
    intro z hz
    rw [← hr z, hl, hΨ.left_inv _ (show P (Φinv z) ∈ U by rw [hcov']; exact hz)]
  · refine ⟨h.isScSmoothMap_one, ?_, mapsTo_univ _ _, mapsTo_univ _ _,
      fun y _ => B.oneVal_injective (hl _), fun y _ => B'.oneVal_injective (hr _)⟩
    refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun y _ => ?_
    obtain ⟨U, hxU, hi⟩ := hloc (P' (B'.oneVal y))
    obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
    refine ⟨(P' ∘ B'.oneVal) ⁻¹' U, hΨ₁.isOpen_target, hxU, subset_univ _,
      hΨ₁.isScSmoothOn_inv.congr ?_⟩
    intro z hz
    have hz' : P (B.oneVal (Ψ₁ z)) ∈ U := hΨ₁.mapsTo_inv hz
    apply B.oneVal_injective
    rw [oneVal_oneRestrict]
    have e₁ := congrArg B'.oneVal (hΨ₁.right_inv z hz)
    rw [oneVal_oneRestrict] at e₁
    rw [← e₁, hl]

end StrongBundle

end Local

/-! ### Two structures with the same local strong bundle isomorphisms agree -/

section Unique

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X'' : Type*} [TopologicalSpace X''] [T2Space X''] [ParacompactSpace X''] {PX'' : MPolyfold X''}
  {Y'' : Type*} [TopologicalSpace Y''] [T2Space Y''] [ParacompactSpace Y''] {P'' : Y'' → X''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]

namespace StrongBundle

/-- **The identity between two strong bundle structures with a common local strong bundle
isomorphism is a strong bundle map** (the argument of 2021 p. 905): if `S : Y → Y''` covering `f`
is a strong bundle map for `B₁` and, near every point, a local strong bundle isomorphism for `B₂`,
then `id : B₁ → B₂` is a strong bundle map. -/
theorem isStrongBundleMap_id_of_isStrongBundleIsoOn (B₁ B₂ : StrongBundle PX P)
    {B'' : StrongBundle PX'' P''} {f : X → X''} {S : Y → Y''} (h₁ : B₁.IsStrongBundleMap B'' f S)
    (h₂ : B₂.IsStrongBundleMap B'' f S)
    (hloc₂ : ∀ x : X, ∃ (U : Set X) (U'' : Set X''), x ∈ U ∧ B₂.IsStrongBundleIsoOn B'' h₂ U U'') :
    B₁.IsStrongBundleMap B₂ id id := by
  refine IsStrongBundleMap.of_local (fun _ => rfl) (fun x => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
    fun x => ?_
  obtain ⟨U, U'', hxU, hi⟩ := hloc₂ x
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨Ψ, hΨ⟩ := hi.isScDiffeoOn_zero
  obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
  have hU : IsOpen U := hg.isOpen_source
  refine ⟨U, hU, hxU, ?_, ?_⟩
  · refine (MPolyfold.IsScSmoothOn.comp hΨ.isScSmoothOn_inv
      (h₁.isScSmoothMap.mono (hU.preimage B₁.continuous) (subset_univ _)) fun y hy => ?_).congr
      fun y hy => hΨ.left_inv y hy
    change P'' (S y) ∈ U''
    rw [h₁.covers]; exact hg.mapsTo hy
  · have hmaps : MapsTo (oneRestrict B₁ B'' S h₁.mapsTo_oneSet) ((P ∘ B₁.oneVal) ⁻¹' U)
        ((P'' ∘ B''.oneVal) ⁻¹' U'') := fun y hy => by
      change P'' (S (B₁.oneVal y)) ∈ U''
      rw [h₁.covers]; exact hg.mapsTo hy
    refine ⟨Ψ₁ ∘ oneRestrict B₁ B'' S h₁.mapsTo_oneSet, fun y hy => ?_,
      MPolyfold.IsScSmoothOn.comp hΨ₁.isScSmoothOn_inv
        (h₁.isScSmoothMap_one.mono (hU.preimage (B₁.continuous.comp B₁.continuous_oneVal))
          (subset_univ _)) hmaps⟩
    have hy' : B₁.oneVal y ∈ P ⁻¹' U := hy
    change B₂.oneVal (Ψ₁ (oneRestrict B₁ B'' S h₁.mapsTo_oneSet y)) = B₁.oneVal y
    rw [IsStrongBundleIsoOn.oneVal_inv (h := h₂) hΨ hΨ₁ (hmaps hy)]
    exact hΨ.left_inv _ hy'

/-- **Two strong bundle structures on `P : Y → X` for which `S : Y → Y''` is near every point a
local strong bundle isomorphism agree**: the identity is a strong bundle isomorphism
(2021 p. 905: "since each of the target maps is a local strong bundle isomorphism …, it follows
that the identity map is a local strong bundle isomorphism, which implies that it is a strong
bundle isomorphism"). -/
theorem isStrongBundleIso_id_of_isStrongBundleIsoOn (B₁ B₂ : StrongBundle PX P)
    {B'' : StrongBundle PX'' P''} {f : X → X''} {S : Y → Y''} (h₁ : B₁.IsStrongBundleMap B'' f S)
    (h₂ : B₂.IsStrongBundleMap B'' f S)
    (hloc₁ : ∀ x : X, ∃ (U : Set X) (U'' : Set X''), x ∈ U ∧ B₁.IsStrongBundleIsoOn B'' h₁ U U'')
    (hloc₂ : ∀ x : X, ∃ (U : Set X) (U'' : Set X''), x ∈ U ∧ B₂.IsStrongBundleIsoOn B'' h₂ U U'') :
    B₁.IsStrongBundleIso B₂ id id id id :=
  ⟨isStrongBundleMap_id_of_isStrongBundleIsoOn B₁ B₂ h₁ h₂ hloc₂,
    isStrongBundleMap_id_of_isStrongBundleIsoOn B₂ B₁ h₂ h₁ hloc₁, fun _ => rfl, fun _ => rfl⟩

end StrongBundle

end Unique

end Polyfold
