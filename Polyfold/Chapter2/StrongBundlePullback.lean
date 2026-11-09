import Polyfold.Chapter2.StrongBundle
import Polyfold.Chapter2.Metrizable

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.5,
**Proposition 2.6.8 (preprint 2.54)**: the pull-back of a strong bundle along an sc-smooth map is a strong bundle.

# The pull-back strong bundle

## The text, paraphrased

(Definition 2.6.7 (preprint 2.53)) For a strong bundle `P : Y → X` and an sc-smooth `f : Z → X`,
`f*Y = {(z, y) ∈ Z × Y | P(y) = f(z)}` with `P_f(z, y) = z`.  (Proposition 2.6.8 (preprint 2.54)) "The pull-back
bundle `P_f : f*Y → Z` carries a natural structure of a strong M-polyfold bundle over the
M-polyfold `Z`.  The easy proof is left to the reader" (with a reference to [20], Proposition 4.11).

## What is formalized

* `Polyfold.ScOperator.isScSmoothRetractMap`, `IsScSmoothRetractMap.scPair`, `isScRetract_univ`:
  sc-operators and pairings are sc-smooth between retracts.
* The fibres: `Polyfold.pullbackFiberEquiv` (`P_f⁻¹(z) ≃ P⁻¹(f(z))`), the transported vector
  space structures (instances `pullbackFiber_addCommGroup`, `pullbackFiber_module`), and
  `Polyfold.pullbackFiberCLE` (a linear homeomorphism, so the fibres are Banachable).
* `Polyfold.PullbackChartData`: a strong bundle chart `c` of `Y`, a chart `ψ` of `Z` with
  `f(dom ψ) ⊆ dom φ`, a retraction onto the model of `ψ`, and the sc-smoothness of
  `g = φ ∘ f ∘ ψ⁻¹`; `PullbackChartData.toChart`: the strong bundle chart
  `Φ_f(z, y) = (ψ(z), pr_F Φ(y)) : P_f⁻¹(V_Z) → K_g` with the pulled-back retraction of
  `StrongBundle.lean` (`pullbackRetraction`, `K_g = PullbackChartData.Kg`).
* `StrongBundleChart.isScRetract_overlap`, `isScRetract_overlap_one` (overlaps of strong bundle
  charts are retracts on `[0]` and `[1]`), `PullbackChartData.transition_eqOn` (the transition
  maps of pulled-back charts are `(w, h) ↦ (ψ₂ψ₁⁻¹(w), pr_F(Φ₂Φ₁⁻¹)(g₁(w), h))`),
  `transition_isScSmooth`, `transitionOne_isScSmooth`, `compatible_toChart`.
* `Polyfold.paracompactSpace_pullbackSpace` (`f*Y ⊆ Z × Y` is metrizable, by Theorem 2.3.10 (preprint 2.16) for `Z`
  and `Y[0]`), `Polyfold.pullbackAtlas`, and `Polyfold.proposition_2_6_8` (**Proposition 2.6.8 (preprint 2.54)**).

## What the text leaves implicit, and the choices made

* "Natural structure": the atlas consists of all pulled-back charts (`pullbackAtlas`); any two
  are compatible, so the structure does not depend on choices.
* The paracompactness of `f*Y` (required by Definition 2.6.5 (preprint 2.51)) is not mentioned in the text; it
  follows from the metrizability of `Z` and of `Y[0]` (Theorem 2.3.10 (preprint 2.16)), as the exposition notes.
-/

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

/-! ### Sc-smooth maps between retracts: sc-operators and pairings -/

section RetractMaps

variable {E E₁ E₂ : ScBanach} {C : Set (E 0)} {C₁ : Set (E₁ 0)} {C₂ : Set (E₂ 0)}

/-- An sc-operator is sc-smooth between retracts. -/
theorem ScOperator.isScSmoothRetractMap (T : ScOperator E E₁) {O : Set (E 0)}
    (hO : IsScRetract E C O) {O₁ : Set (E₁ 0)} (hmaps : MapsTo (T 0) O O₁) :
    IsScSmoothRetractMap E C O E₁ C₁ O₁ (T 0) := by
  rw [isScSmoothRetractMap_iff_exists hO]
  obtain ⟨R, hR⟩ := hO
  exact ⟨hmaps, R, hR, IsScSmooth.comp R.isScDomain (isScDomain_univ _)
    (T.isScSmooth (isScDomain_univ _)) R.isScSmooth (mapsTo_univ _ _)⟩

/-- The pairing of sc-smooth maps between retracts is sc-smooth into the product. -/
theorem IsScSmoothRetractMap.scPair {O : Set (E 0)} {O₁ : Set (E₁ 0)} {O₂ : Set (E₂ 0)}
    {f₁ : E 0 → E₁ 0} {f₂ : E 0 → E₂ 0} (h₁ : IsScSmoothRetractMap E C O E₁ C₁ O₁ f₁)
    (h₂ : IsScSmoothRetractMap E C O E₂ C₂ O₂ f₂) {C' O' : Set ((E₁.prod E₂) 0)}
    (hmaps : MapsTo (scPair f₁ f₂) O O') :
    IsScSmoothRetractMap E C O (E₁.prod E₂) C' O' (scPair f₁ f₂) where
  mapsTo := hmaps
  comp_isScSmooth R hR :=
    IsScSmooth.scPair R.isScDomain (h₁.comp_isScSmooth R hR) (h₂.comp_isScSmooth R hR)

/-- The whole space is a retract. -/
lemma isScRetract_univ (E : ScBanach) : IsScRetract E univ univ :=
  (show IsRelOpenInQuadrant E univ univ from
    ⟨isPartialQuadrant_univ E, univ, isOpen_univ, (inter_univ _).symm⟩).isScRetract

end RetractMaps

/-! ### The fibres of the pull-back -/

section PullbackFibres

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w} (P : Y → X) (f : Z → X)

/-- The fibre of `P_f : f*Y → Z` over `z` is the fibre of `P` over `f(z)`. -/
def pullbackFiberEquiv (z : Z) : (pullbackProj P f ⁻¹' {z}) ≃ (P ⁻¹' {f z}) where
  toFun q := ⟨q.1.1.2, by
    have h1 : P q.1.1.2 = f q.1.1.1 := q.1.2
    have h2 : q.1.1.1 = z := q.2
    change P q.1.1.2 = f z
    rw [h1, h2]⟩
  invFun y := ⟨⟨(z, y.1), (y.2 : P y.1 = f z)⟩, rfl⟩
  left_inv q := by
    obtain ⟨⟨⟨z', y⟩, hzy⟩, hz⟩ := q
    have : z' = z := hz
    subst this
    rfl
  right_inv y := rfl

variable [∀ x, AddCommGroup (P ⁻¹' {x})]

instance pullbackFiber_addCommGroup (z : Z) : AddCommGroup (pullbackProj P f ⁻¹' {z}) :=
  (pullbackFiberEquiv P f z).addCommGroup

lemma pullbackFiberEquiv_add (z : Z) (v w : pullbackProj P f ⁻¹' {z}) :
    pullbackFiberEquiv P f z (v + w) = pullbackFiberEquiv P f z v + pullbackFiberEquiv P f z w :=
  (pullbackFiberEquiv P f z).apply_symm_apply _

variable [∀ x, Module ℝ (P ⁻¹' {x})]

instance pullbackFiber_module (z : Z) : Module ℝ (pullbackProj P f ⁻¹' {z}) :=
  (pullbackFiberEquiv P f z).module ℝ

lemma pullbackFiberEquiv_smul (z : Z) (a : ℝ) (v : pullbackProj P f ⁻¹' {z}) :
    pullbackFiberEquiv P f z (a • v) = a • pullbackFiberEquiv P f z v :=
  (pullbackFiberEquiv P f z).apply_symm_apply _

end PullbackFibres

/-! ### The pulled-back strong bundle charts -/

section PullbackChart

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {f : Z → X}

/-- The data from which a strong bundle chart of `f*Y` is pulled back: a strong bundle chart `c` of
`Y`, a chart `ψ` of `Z` with `f(dom ψ) ⊆ dom φ`, a retraction `r_Z` onto the model of `ψ`, and the
sc-smoothness of `g = φ ∘ f ∘ ψ⁻¹ : O_Z → O`. -/
structure PullbackChartData (PX : MPolyfold X) (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})]
    [∀ x, Module ℝ (P ⁻¹' {x})] (PZ : MPolyfold Z) (f : Z → X) where
  c : StrongBundleChart PX P
  ψ : MChart Z
  isChart : PZ.IsChart ψ
  mapsTo : MapsTo f ψ.source c.φ.source
  RZ : ScRetraction ψ.model.E ψ.model.C
  RZ_retract : RZ.retract = ψ.model.O
  smooth : IsScSmoothRetractMap ψ.model.E ψ.model.C ψ.model.O c.φ.model.E c.φ.model.C c.φ.model.O
    (c.φ ∘ f ∘ ψ.symm)

namespace PullbackChartData

variable (d : PullbackChartData PX P PZ f)

/-- `g = φ ∘ f ∘ ψ⁻¹`. -/
def g : d.ψ.model.E 0 → d.c.φ.model.E 0 := d.c.φ ∘ f ∘ d.ψ.symm

lemma g_smooth : IsScSmoothRetractMap d.ψ.model.E d.ψ.model.C d.RZ.retract d.c.φ.model.E
    d.c.φ.model.C (d.c.isRetraction.baseRetraction d.c.relOpen).retract d.g := by
  rw [d.RZ_retract, d.c.base_retract]; exact d.smooth

/-- The pulled-back local strong bundle retract `K_g = {(w, h) | w ∈ O_Z, (g(w), h) ∈ K}`. -/
def Kg : Set (d.ψ.model.E 0 × d.c.F 0) := {p | p.1 ∈ d.RZ.retract ∧ (d.g p.1, p.2) ∈ d.c.K}

lemma image_eq_Kg :
    pullbackRetraction d.c.R d.RZ d.g '' (d.RZ.U ×ˢ univ) = d.Kg :=
  pullback_image d.c.relOpen d.c.isRetraction d.RZ d.g_smooth

lemma mem_c_source {q : pullbackSpace P f} (hq : q.1.1 ∈ d.ψ.source) :
    q.1.2 ∈ d.c.toPartialEquiv.source := by
  rw [d.c.source_eq, mem_preimage, show P q.1.2 = f q.1.1 from q.2]
  exact d.mapsTo hq

lemma g_apply {q : pullbackSpace P f} (hq : q.1.1 ∈ d.ψ.source) :
    d.g (d.ψ q.1.1) = (d.c q.1.2).1 := by
  change d.c.φ (f (d.ψ.symm (d.ψ q.1.1))) = _
  rw [d.ψ.symm_apply_apply hq, d.c.covers _ (d.mem_c_source hq), show P q.1.2 = f q.1.1 from q.2]

lemma mem_Kg {q : pullbackSpace P f} (hq : q.1.1 ∈ d.ψ.source) :
    ((d.ψ q.1.1, (d.c q.1.2).2) : d.ψ.model.E 0 × d.c.F 0) ∈ d.Kg := by
  refine ⟨by rw [d.RZ_retract]; exact d.ψ.mapsTo_model _ hq, ?_⟩
  rw [d.g_apply hq]
  have := d.c.toPartialEquiv.map_source (d.mem_c_source hq)
  rw [d.c.target_eq] at this
  exact this

lemma symm_mem_pullback {k : d.ψ.model.E 0 × d.c.F 0} (hk : k ∈ d.Kg) :
    (d.ψ.symm k.1, d.c.toPartialEquiv.symm (d.g k.1, k.2)) ∈ pullbackSpace P f := by
  have hk1 : k.1 ∈ d.ψ.model.O := by rw [← d.RZ_retract]; exact hk.1
  have hk2 : (d.g k.1, k.2) ∈ d.c.toPartialEquiv.target := by rw [d.c.target_eq]; exact hk.2
  set y := d.c.toPartialEquiv.symm (d.g k.1, k.2)
  have hys : y ∈ d.c.toPartialEquiv.source := d.c.toPartialEquiv.map_target hk2
  have hcov := d.c.covers y hys
  rw [d.c.toPartialEquiv.right_inv hk2] at hcov
  have hyφ : P y ∈ d.c.φ.source := by rw [d.c.source_eq] at hys; exact hys
  have hfφ : f (d.ψ.symm k.1) ∈ d.c.φ.source := d.mapsTo (d.ψ.symm_mapsTo hk1)
  exact d.c.φ.toPartialEquiv.injOn hyφ hfφ hcov.symm

open scoped Classical in
/-- The inverse of the pulled-back chart, `(w, h) ↦ (ψ⁻¹(w), Φ⁻¹(g(w), h))`, with a junk value. -/
def invFun (q₀ : pullbackSpace P f) (k : d.ψ.model.E 0 × d.c.F 0) : pullbackSpace P f :=
  if h : k ∈ d.Kg then ⟨_, d.symm_mem_pullback h⟩ else q₀

lemma invFun_of_mem (q₀ : pullbackSpace P f) {k : d.ψ.model.E 0 × d.c.F 0} (hk : k ∈ d.Kg) :
    (d.invFun q₀ k : Z × Y) = (d.ψ.symm k.1, d.c.toPartialEquiv.symm (d.g k.1, k.2)) := by
  unfold invFun; rw [dif_pos hk]

/-- **Proposition 2.6.8 (preprint 2.54)**, the charts: the strong bundle chart
`Φ_f(z, y) = (ψ(z), pr_F Φ(y)) : P_f⁻¹(V_Z) → K_g` of `f*Y` (exposition, proof of Proposition
2.54). -/
def toChart (q₀ : pullbackSpace P f) : StrongBundleChart PZ (pullbackProj P f) where
  φ := d.ψ
  isChart := d.isChart
  F := d.c.F
  U := d.RZ.U
  R := pullbackRetraction d.c.R d.RZ d.g
  relOpen := d.RZ.relOpen
  isRetraction := isStrongBundleRetraction_pullback d.c.relOpen d.c.isRetraction d.RZ d.g_smooth
  base_retract := by
    rw [← d.RZ_retract]; rfl
  toPartialEquiv :=
    { toFun := fun q => (d.ψ q.1.1, (d.c q.1.2).2)
      invFun := d.invFun q₀
      source := {q | q.1.1 ∈ d.ψ.source}
      target := pullbackRetraction d.c.R d.RZ d.g '' (d.RZ.U ×ˢ univ)
      map_source' := fun q hq => by rw [d.image_eq_Kg]; exact d.mem_Kg hq
      map_target' := fun k hk => by
        rw [d.image_eq_Kg] at hk
        change (d.invFun q₀ k : Z × Y).1 ∈ d.ψ.source
        rw [d.invFun_of_mem q₀ hk]
        exact d.ψ.symm_mapsTo (by rw [← d.RZ_retract]; exact hk.1)
      left_inv' := fun q hq => by
        have hk := d.mem_Kg hq
        apply Subtype.ext
        rw [d.invFun_of_mem q₀ hk]
        change (d.ψ.symm (d.ψ q.1.1), d.c.toPartialEquiv.symm (d.g (d.ψ q.1.1), (d.c q.1.2).2)) =
          q.1
        rw [d.ψ.symm_apply_apply hq, d.g_apply hq, Prod.mk.eta,
          d.c.toPartialEquiv.left_inv (d.mem_c_source hq)]
      right_inv' := fun k hk => by
        rw [d.image_eq_Kg] at hk
        have hk1 : k.1 ∈ d.ψ.model.O := by rw [← d.RZ_retract]; exact hk.1
        have hk2 : (d.g k.1, k.2) ∈ d.c.toPartialEquiv.target := by
          rw [d.c.target_eq]; exact hk.2
        change (d.ψ (d.invFun q₀ k : Z × Y).1, (d.c (d.invFun q₀ k : Z × Y).2).2) = k
        rw [d.invFun_of_mem q₀ hk, d.ψ.apply_symm_apply hk1, d.c.toPartialEquiv.right_inv hk2] }
  source_eq := rfl
  target_eq := rfl
  continuousOn_toFun := by
    refine ContinuousOn.prodMk ?_ ?_
    · exact d.ψ.continuousOn_toFun.comp
        ((continuous_fst.comp continuous_subtype_val).continuousOn) fun q hq => hq
    · exact (continuous_snd.comp_continuousOn d.c.continuousOn_toFun).comp
        ((continuous_snd.comp continuous_subtype_val).continuousOn) fun q hq => d.mem_c_source hq
  continuousOn_invFun := by
    change ContinuousOn (d.invFun q₀) (pullbackRetraction d.c.R d.RZ d.g '' (d.RZ.U ×ˢ univ))
    rw [d.image_eq_Kg]
    have hgc : ContinuousOn d.g d.RZ.retract := by
      have := d.g_smooth.continuousOn ⟨d.RZ, rfl⟩
      exact this
    have h1 : ContinuousOn (fun k : d.ψ.model.E 0 × d.c.F 0 =>
        ((d.ψ.symm k.1, d.c.toPartialEquiv.symm (d.g k.1, k.2)) : Z × Y)) d.Kg := by
      refine ContinuousOn.prodMk ?_ ?_
      · exact d.ψ.continuousOn_invFun.comp continuous_fst.continuousOn fun k hk => by
          rw [← d.RZ_retract]; exact hk.1
      · refine d.c.continuousOn_invFun.comp ?_ fun k hk => by rw [d.c.target_eq]; exact hk.2
        exact (hgc.comp continuous_fst.continuousOn fun k hk => hk.1).prodMk
          continuous_snd.continuousOn
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact h1.congr fun k hk => d.invFun_of_mem q₀ hk
  covers _ _ := rfl
  fiber_linear z hz := by
    constructor
    · intro v w
      have h := (d.c.fiber_linear (f z) (d.mapsTo hz)).map_add
        (pullbackFiberEquiv P f z v) (pullbackFiberEquiv P f z w)
      rw [← pullbackFiberEquiv_add] at h
      exact h
    · intro a v
      have h := (d.c.fiber_linear (f z) (d.mapsTo hz)).map_smul a (pullbackFiberEquiv P f z v)
      rw [← pullbackFiberEquiv_smul] at h
      exact h

lemma toChart_apply (q₀ q : pullbackSpace P f) :
    d.toChart q₀ q = (d.ψ q.1.1, (d.c q.1.2).2) := rfl

lemma toChart_source (q₀ : pullbackSpace P f) :
    (d.toChart q₀).toPartialEquiv.source = {q | q.1.1 ∈ d.ψ.source} := rfl

end PullbackChartData

/-! ### Overlaps of strong bundle charts are retracts -/

namespace StrongBundleChart

variable {Y' : Type*} [TopologicalSpace Y'] {P' : Y' → X}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  (c c' : StrongBundleChart PX P') (hP : Continuous P')

include hP in
lemma overlap_eq_inter : ∃ W, IsOpen W ∧ c.overlap c' = c.K ∩ W := by
  obtain ⟨W, hW, hWeq⟩ := (c.toMChart hP).exists_isOpen_image_eq
    (s := c.toPartialEquiv.source ∩ c'.toPartialEquiv.source) inter_subset_left
    ((c.isOpen_source hP).inter (c'.isOpen_source hP))
  exact ⟨W, hW, hWeq⟩

include hP in
lemma isScRetract_overlap :
    IsScRetract (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ) (c.overlap c') :=
  (c.toMChart hP).isScRetract_overlap (c'.toMChart hP)

include hP in
lemma isScRetract_overlap_one :
    IsScRetract (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ)
      (strongShiftOne (c.overlap c')) := by
  obtain ⟨W, hW, hWeq⟩ := c.overlap_eq_inter c' hP
  have hW' : IsOpen ((c.φ.model.E.prodShiftInclOp c.F 0) ⁻¹' W) :=
    hW.preimage (c.φ.model.E.prodShiftInclOp c.F 0).continuous
  have := proposition_2_3_1_one c.isScRetract_one hW'
  convert this using 1
  rw [hWeq]; rfl

lemma mem_overlap_iff {k : c.φ.model.E 0 × c.F 0} :
    k ∈ c.overlap c' ↔ ∃ y, y ∈ c.toPartialEquiv.source ∧ y ∈ c'.toPartialEquiv.source ∧ c y = k :=
  ⟨fun ⟨y, hy, hk⟩ => ⟨y, hy.1, hy.2, hk⟩, fun ⟨y, h1, h2, hk⟩ => ⟨y, ⟨h1, h2⟩, hk⟩⟩

lemma transition_apply {y : Y'} (hy : y ∈ c.toPartialEquiv.source) :
    c.transition c' (c y) = c' y := by
  change c' (c.toPartialEquiv.symm (c.toPartialEquiv y)) = c' y
  rw [c.toPartialEquiv.left_inv hy]

end StrongBundleChart

/-! ### Compatibility of the pulled-back charts -/

namespace PullbackChartData

variable (d₁ d₂ : PullbackChartData PX P PZ f) (q₁ q₂ : pullbackSpace P f)

lemma mem_overlap_iff {k : d₁.ψ.model.E 0 × d₁.c.F 0} :
    k ∈ (d₁.toChart q₁).overlap (d₂.toChart q₂) ↔ ∃ q : pullbackSpace P f,
      q.1.1 ∈ d₁.ψ.source ∧ q.1.1 ∈ d₂.ψ.source ∧ (d₁.ψ q.1.1, (d₁.c q.1.2).2) = k :=
  StrongBundleChart.mem_overlap_iff _ _

/-- `G₁(w, h) = (g₁(w), h)`. -/
def gPair : (d₁.ψ.model.E.prod d₁.c.F) 0 → (d₁.c.φ.model.E.prod d₁.c.F) 0 :=
  scPair (E := d₁.ψ.model.E.prod d₁.c.F) (F := d₁.c.φ.model.E) (G := d₁.c.F)
    (d₁.g ∘ Prod.fst) Prod.snd

/-- The transition map of two pulled-back charts through those of `Z` and `Y`:
`(w, h) ↦ (ψ₂ ∘ ψ₁⁻¹(w), pr_F (Φ₂ ∘ Φ₁⁻¹)(g₁(w), h))`. -/
def transitionFormula : (d₁.ψ.model.E.prod d₁.c.F) 0 → (d₂.ψ.model.E.prod d₂.c.F) 0 :=
  scPair (E := d₁.ψ.model.E.prod d₁.c.F) (F := d₂.ψ.model.E) (G := d₂.c.F)
    (d₁.ψ.transition d₂.ψ ∘ Prod.fst) (Prod.snd ∘ d₁.c.transition d₂.c ∘ d₁.gPair)

/-- The transition map of two pulled-back charts, written through the transition maps of the
charts of `Z` and of `Y` (exposition, proof of Proposition 2.6.8 (preprint 2.54)). -/
lemma transition_eqOn :
    EqOn (transitionFormula d₁ d₂) ((d₁.toChart q₁).transition (d₂.toChart q₂))
      ((d₁.toChart q₁).overlap (d₂.toChart q₂)) := by
  intro k hk
  obtain ⟨q, hq1, hq2, rfl⟩ := (mem_overlap_iff d₁ d₂ q₁ q₂).1 hk
  rw [show (d₁.ψ q.1.1, (d₁.c q.1.2).2) = d₁.toChart q₁ q from rfl,
    StrongBundleChart.transition_apply _ _
      (show q ∈ (d₁.toChart q₁).toPartialEquiv.source from hq1)]
  change ((d₁.ψ.transition d₂.ψ (d₁.ψ q.1.1)),
    (d₁.c.transition d₂.c (d₁.g (d₁.ψ q.1.1), (d₁.c q.1.2).2)).2) = (d₂.ψ q.1.1, (d₂.c q.1.2).2)
  rw [d₁.ψ.transition_apply d₂.ψ hq1, d₁.g_apply hq1, Prod.mk.eta,
    StrongBundleChart.transition_apply _ _ (d₁.mem_c_source hq1)]

variable {d₁ d₂ q₁ q₂}

lemma fst_mem_overlap {k : d₁.ψ.model.E 0 × d₁.c.F 0}
    (hk : k ∈ (d₁.toChart q₁).overlap (d₂.toChart q₂)) : k.1 ∈ d₁.ψ.overlap d₂.ψ := by
  obtain ⟨q, hq1, hq2, rfl⟩ := (mem_overlap_iff d₁ d₂ q₁ q₂).1 hk
  exact d₁.ψ.mem_overlap d₂.ψ hq1 hq2

lemma fst_mem_retract {k : d₁.ψ.model.E 0 × d₁.c.F 0}
    (hk : k ∈ (d₁.toChart q₁).overlap (d₂.toChart q₂)) : k.1 ∈ d₁.RZ.retract := by
  obtain ⟨q, hq1, -, rfl⟩ := (mem_overlap_iff d₁ d₂ q₁ q₂).1 hk
  rw [d₁.RZ_retract]; exact d₁.ψ.mapsTo_model _ hq1

lemma gPair_mem {k : d₁.ψ.model.E 0 × d₁.c.F 0}
    (hk : k ∈ (d₁.toChart q₁).overlap (d₂.toChart q₂)) :
    d₁.gPair k ∈ d₁.c.overlap d₂.c := by
  obtain ⟨q, hq1, hq2, rfl⟩ := (mem_overlap_iff d₁ d₂ q₁ q₂).1 hk
  change (d₁.g (d₁.ψ q.1.1), (d₁.c q.1.2).2) ∈ _
  rw [d₁.g_apply hq1, Prod.mk.eta]
  exact ⟨q.1.2, ⟨d₁.mem_c_source hq1, d₂.mem_c_source hq2⟩, rfl⟩

lemma transition_mem {k : d₁.ψ.model.E 0 × d₁.c.F 0}
    (hk : k ∈ (d₁.toChart q₁).overlap (d₂.toChart q₂)) :
    (d₁.toChart q₁).transition (d₂.toChart q₂) k ∈ (d₂.toChart q₂).overlap (d₁.toChart q₁) := by
  obtain ⟨q, hq1, hq2, rfl⟩ := (mem_overlap_iff d₁ d₂ q₁ q₂).1 hk
  rw [show (d₁.ψ q.1.1, (d₁.c q.1.2).2) = d₁.toChart q₁ q from rfl,
    StrongBundleChart.transition_apply _ _
      (show q ∈ (d₁.toChart q₁).toPartialEquiv.source from hq1)]
  exact ⟨q, ⟨hq2, hq1⟩, rfl⟩

lemma transition_snd_mem_range (hB : d₁.c.Compatible d₂.c) {k : d₁.ψ.model.E 0 × d₁.c.F 0}
    (hk : k ∈ (d₁.toChart q₁).overlap (d₂.toChart q₂)) (hk2 : k.2 ∈ range (d₁.c.F.toBase 1)) :
    ((d₁.toChart q₁).transition (d₂.toChart q₂) k).2 ∈ range (d₂.c.F.toBase 1) := by
  rw [← transition_eqOn d₁ d₂ q₁ q₂ hk]
  exact hB.2.2.2.2.1 _ (gPair_mem hk) hk2

variable (d₁ d₂ q₁ q₂)

/-- **Proposition 2.6.8 (preprint 2.54)**, compatibility on `[0]`: the transition maps of pulled-back charts are
sc-smooth. -/
theorem transition_isScSmooth (hP : Continuous P) (hB : d₁.c.Compatible d₂.c)
    (hZ : d₁.ψ.Compatible d₂.ψ) :
    IsScSmoothRetractMap (d₁.ψ.model.E.prod d₁.c.F) (d₁.ψ.model.C ×ˢ univ)
      ((d₁.toChart q₁).overlap (d₂.toChart q₂)) (d₂.ψ.model.E.prod d₂.c.F)
      (d₂.ψ.model.C ×ˢ univ) ((d₂.toChart q₂).overlap (d₁.toChart q₁))
      ((d₁.toChart q₁).transition (d₂.toChart q₂)) := by
  have hPf : Continuous (pullbackProj P f) := continuous_pullbackProj P f
  have hO₁ := (d₁.toChart q₁).isScRetract_overlap (d₂.toChart q₂) hPf
  have hfst : IsScSmoothRetractMap (d₁.ψ.model.E.prod d₁.c.F) (d₁.ψ.model.C ×ˢ univ)
      ((d₁.toChart q₁).overlap (d₂.toChart q₂)) d₁.ψ.model.E d₁.ψ.model.C
      (d₁.ψ.overlap d₂.ψ) Prod.fst :=
    (d₁.ψ.model.E.prodFstOp d₁.c.F).isScSmoothRetractMap hO₁ fun k hk => fst_mem_overlap hk
  have hψ := hZ.1.comp hfst (d₁.ψ.isScRetract_overlap d₂.ψ)
  have hfstR : IsScSmoothRetractMap (d₁.ψ.model.E.prod d₁.c.F) (d₁.ψ.model.C ×ˢ univ)
      ((d₁.toChart q₁).overlap (d₂.toChart q₂)) d₁.ψ.model.E d₁.ψ.model.C
      d₁.RZ.retract Prod.fst :=
    (d₁.ψ.model.E.prodFstOp d₁.c.F).isScSmoothRetractMap hO₁ fun k hk => fst_mem_retract hk
  have hg := d₁.g_smooth.comp hfstR ⟨d₁.RZ, rfl⟩
  have hsnd : IsScSmoothRetractMap (d₁.ψ.model.E.prod d₁.c.F) (d₁.ψ.model.C ×ˢ univ)
      ((d₁.toChart q₁).overlap (d₂.toChart q₂)) d₁.c.F univ univ Prod.snd :=
    (d₁.ψ.model.E.prodSndOp d₁.c.F).isScSmoothRetractMap hO₁ (mapsTo_univ _ _)
  have hG : IsScSmoothRetractMap (d₁.ψ.model.E.prod d₁.c.F) (d₁.ψ.model.C ×ˢ univ)
      ((d₁.toChart q₁).overlap (d₂.toChart q₂)) (d₁.c.φ.model.E.prod d₁.c.F)
      (d₁.c.φ.model.C ×ˢ univ) (d₁.c.overlap d₂.c) d₁.gPair :=
    IsScSmoothRetractMap.scPair hg hsnd fun k hk => gPair_mem hk
  have hT := hB.1.comp hG (d₁.c.isScRetract_overlap d₂.c hP)
  have hsnd2 : IsScSmoothRetractMap (d₂.c.φ.model.E.prod d₂.c.F) (d₂.c.φ.model.C ×ˢ univ)
      (d₂.c.overlap d₁.c) d₂.c.F univ univ Prod.snd :=
    (d₂.c.φ.model.E.prodSndOp d₂.c.F).isScSmoothRetractMap (d₂.c.isScRetract_overlap d₁.c hP)
      (mapsTo_univ _ _)
  have hS := hsnd2.comp hT (d₂.c.isScRetract_overlap d₁.c hP)
  have hpair : IsScSmoothRetractMap (d₁.ψ.model.E.prod d₁.c.F) (d₁.ψ.model.C ×ˢ univ)
      ((d₁.toChart q₁).overlap (d₂.toChart q₂)) (d₂.ψ.model.E.prod d₂.c.F)
      (d₂.ψ.model.C ×ˢ univ) ((d₂.toChart q₂).overlap (d₁.toChart q₁)) (transitionFormula d₁ d₂) :=
    IsScSmoothRetractMap.scPair hψ hS fun k hk => by
      have := transition_eqOn d₁ d₂ q₁ q₂ hk
      change transitionFormula d₁ d₂ k ∈ (d₂.toChart q₂).overlap (d₁.toChart q₁)
      rw [this]; exact transition_mem hk
  exact hpair.congr (transition_eqOn d₁ d₂ q₁ q₂)

/-- `G₁[1](w, h) = (g₁(w), h)` on `E_Z ⊕ F¹`. -/
def gPairOne : (d₁.ψ.model.E.prod d₁.c.F.shift) 0 → (d₁.c.φ.model.E.prod d₁.c.F.shift) 0 :=
  scPair (E := d₁.ψ.model.E.prod d₁.c.F.shift) (F := d₁.c.φ.model.E) (G := d₁.c.F.shift)
    (d₁.g ∘ Prod.fst) Prod.snd

/-- The `[1]`-transition through those of `Z` and `Y`. -/
def transitionFormulaOne :
    (d₁.ψ.model.E.prod d₁.c.F.shift) 0 → (d₂.ψ.model.E.prod d₂.c.F.shift) 0 :=
  scPair (E := d₁.ψ.model.E.prod d₁.c.F.shift) (F := d₂.ψ.model.E) (G := d₂.c.F.shift)
    (d₁.ψ.transition d₂.ψ ∘ Prod.fst) (Prod.snd ∘ shiftFiber (d₁.c.transition d₂.c) ∘ d₁.gPairOne)

lemma transitionOne_eqOn :
    EqOn (transitionFormulaOne d₁ d₂) (shiftFiber ((d₁.toChart q₁).transition (d₂.toChart q₂)))
      (strongShiftOne ((d₁.toChart q₁).overlap (d₂.toChart q₂))) := by
  intro p hp
  have h := transition_eqOn d₁ d₂ q₁ q₂ hp
  exact congrArg (fun x : _ × _ => (x.1, Function.invFun (d₂.c.F.toBase 1) x.2)) h

/-- **Proposition 2.6.8 (preprint 2.54)**, compatibility on `[1]`. -/
theorem transitionOne_isScSmooth (hP : Continuous P) (hB : d₁.c.Compatible d₂.c)
    (hZ : d₁.ψ.Compatible d₂.ψ) :
    IsScSmoothRetractMap (d₁.ψ.model.E.prod d₁.c.F.shift) (d₁.ψ.model.C ×ˢ univ)
      (strongShiftOne ((d₁.toChart q₁).overlap (d₂.toChart q₂))) (d₂.ψ.model.E.prod d₂.c.F.shift)
      (d₂.ψ.model.C ×ˢ univ) (strongShiftOne ((d₂.toChart q₂).overlap (d₁.toChart q₁)))
      (shiftFiber ((d₁.toChart q₁).transition (d₂.toChart q₂))) := by
  have hPf : Continuous (pullbackProj P f) := continuous_pullbackProj P f
  have hO₁ := (d₁.toChart q₁).isScRetract_overlap_one (d₂.toChart q₂) hPf
  have hfst : IsScSmoothRetractMap (d₁.ψ.model.E.prod d₁.c.F.shift) (d₁.ψ.model.C ×ˢ univ)
      (strongShiftOne ((d₁.toChart q₁).overlap (d₂.toChart q₂))) d₁.ψ.model.E d₁.ψ.model.C
      (d₁.ψ.overlap d₂.ψ) Prod.fst :=
    (d₁.ψ.model.E.prodFstOp d₁.c.F.shift).isScSmoothRetractMap hO₁ fun p hp =>
      fst_mem_overlap (k := (p.1, d₁.c.F.toBase 1 p.2)) hp
  have hψ := hZ.1.comp hfst (d₁.ψ.isScRetract_overlap d₂.ψ)
  have hfstR : IsScSmoothRetractMap (d₁.ψ.model.E.prod d₁.c.F.shift) (d₁.ψ.model.C ×ˢ univ)
      (strongShiftOne ((d₁.toChart q₁).overlap (d₂.toChart q₂))) d₁.ψ.model.E d₁.ψ.model.C
      d₁.RZ.retract Prod.fst :=
    (d₁.ψ.model.E.prodFstOp d₁.c.F.shift).isScSmoothRetractMap hO₁ fun p hp =>
      fst_mem_retract (k := (p.1, d₁.c.F.toBase 1 p.2)) hp
  have hg := d₁.g_smooth.comp hfstR ⟨d₁.RZ, rfl⟩
  have hsnd : IsScSmoothRetractMap (d₁.ψ.model.E.prod d₁.c.F.shift) (d₁.ψ.model.C ×ˢ univ)
      (strongShiftOne ((d₁.toChart q₁).overlap (d₂.toChart q₂))) d₁.c.F.shift univ univ
      Prod.snd :=
    (d₁.ψ.model.E.prodSndOp d₁.c.F.shift).isScSmoothRetractMap hO₁ (mapsTo_univ _ _)
  have hG : IsScSmoothRetractMap (d₁.ψ.model.E.prod d₁.c.F.shift) (d₁.ψ.model.C ×ˢ univ)
      (strongShiftOne ((d₁.toChart q₁).overlap (d₂.toChart q₂)))
      (d₁.c.φ.model.E.prod d₁.c.F.shift) (d₁.c.φ.model.C ×ˢ univ)
      (strongShiftOne (d₁.c.overlap d₂.c)) d₁.gPairOne :=
    IsScSmoothRetractMap.scPair hg hsnd fun p hp =>
      gPair_mem (k := (p.1, d₁.c.F.toBase 1 p.2)) hp
  have hT := hB.2.2.1.comp hG (d₁.c.isScRetract_overlap_one d₂.c hP)
  have hsnd2 : IsScSmoothRetractMap (d₂.c.φ.model.E.prod d₂.c.F.shift) (d₂.c.φ.model.C ×ˢ univ)
      (strongShiftOne (d₂.c.overlap d₁.c)) d₂.c.F.shift univ univ Prod.snd :=
    (d₂.c.φ.model.E.prodSndOp d₂.c.F.shift).isScSmoothRetractMap
      (d₂.c.isScRetract_overlap_one d₁.c hP) (mapsTo_univ _ _)
  have hS := hsnd2.comp hT (d₂.c.isScRetract_overlap_one d₁.c hP)
  have hpair : IsScSmoothRetractMap (d₁.ψ.model.E.prod d₁.c.F.shift) (d₁.ψ.model.C ×ˢ univ)
      (strongShiftOne ((d₁.toChart q₁).overlap (d₂.toChart q₂)))
      (d₂.ψ.model.E.prod d₂.c.F.shift) (d₂.ψ.model.C ×ˢ univ)
      (strongShiftOne ((d₂.toChart q₂).overlap (d₁.toChart q₁))) (transitionFormulaOne d₁ d₂) :=
    IsScSmoothRetractMap.scPair hψ hS fun p hp => by
      have := transitionOne_eqOn d₁ d₂ q₁ q₂ hp
      change transitionFormulaOne d₁ d₂ p ∈
        strongShiftOne ((d₂.toChart q₂).overlap (d₁.toChart q₁))
      rw [this]
      set k : d₁.ψ.model.E 0 × d₁.c.F 0 := (p.1, d₁.c.F.toBase 1 p.2)
      have hk : k ∈ (d₁.toChart q₁).overlap (d₂.toChart q₂) := hp
      have hr := transition_snd_mem_range hB hk ⟨p.2, rfl⟩
      change ((((d₁.toChart q₁).transition (d₂.toChart q₂) k).1,
        d₂.c.F.toBase 1 (Function.invFun (d₂.c.F.toBase 1)
          ((d₁.toChart q₁).transition (d₂.toChart q₂) k).2)) : _ × _) ∈
          (d₂.toChart q₂).overlap (d₁.toChart q₁)
      rw [Function.invFun_eq hr]
      exact transition_mem hk
  exact hpair.congr (transitionOne_eqOn d₁ d₂ q₁ q₂)

/-- **Proposition 2.6.8 (preprint 2.54)**: two pulled-back charts are compatible. -/
theorem compatible_toChart (hP : Continuous P) (hB : d₁.c.Compatible d₂.c)
    (hZ : d₁.ψ.Compatible d₂.ψ) : (d₁.toChart q₁).Compatible (d₂.toChart q₂) :=
  ⟨transition_isScSmooth d₁ d₂ q₁ q₂ hP hB hZ, transition_isScSmooth d₂ d₁ q₂ q₁ hP hB.symm hZ.symm,
    transitionOne_isScSmooth d₁ d₂ q₁ q₂ hP hB hZ,
    transitionOne_isScSmooth d₂ d₁ q₂ q₁ hP hB.symm hZ.symm,
    fun _ hk hk2 => transition_snd_mem_range hB hk hk2,
    fun _ hk hk2 => transition_snd_mem_range hB.symm hk hk2⟩

end PullbackChartData

/-! ### Proposition 2.6.8 (preprint 2.54) -/

/-- The fibre identification `P_f⁻¹(z) ≅ P⁻¹(f(z))` as a continuous linear equivalence. -/
def pullbackFiberCLE (z : Z) : (pullbackProj P f ⁻¹' {z}) ≃L[ℝ] (P ⁻¹' {f z}) where
  toFun := pullbackFiberEquiv P f z
  invFun := (pullbackFiberEquiv P f z).symm
  map_add' := pullbackFiberEquiv_add P f z
  map_smul' := pullbackFiberEquiv_smul P f z
  left_inv := (pullbackFiberEquiv P f z).left_inv
  right_inv := (pullbackFiberEquiv P f z).right_inv
  continuous_toFun :=
    ((continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _
  continuous_invFun :=
    ((continuous_const.prodMk continuous_subtype_val).subtype_mk _).subtype_mk _

variable [T2Space Y] [ParacompactSpace Y]

/-- `f*Y` is paracompact: it is a subspace of the metrizable space `Z × Y` (Theorem 2.3.10 (preprint 2.16) for `Z`
and for the M-polyfold `Y[0]`). -/
theorem paracompactSpace_pullbackSpace (Q : MPolyfold Z) (B : StrongBundle PX P) :
    ParacompactSpace (pullbackSpace P f) := by
  have := Q.metrizableSpace
  have := B.toMPolyfold0.metrizableSpace
  exact paracompactSpace_of_metrizableSpace _

/-- The pulled-back strong bundle atlas of `f*Y`. -/
def pullbackAtlas (B : StrongBundle PX P) (hf : PZ.IsScSmoothMap PX f) :
    StrongBundleAtlas PZ (pullbackProj P f) where
  charts := {Φ | ∃ (d : PullbackChartData PX P PZ f) (q₀ : pullbackSpace P f),
    d.c ∈ B.atlas.charts ∧ Φ = d.toChart q₀}
  compatible := by
    rintro _ ⟨d₁, q₁, hd₁, rfl⟩ _ ⟨d₂, q₂, hd₂, rfl⟩
    exact PullbackChartData.compatible_toChart d₁ d₂ q₁ q₂ B.continuous
      (B.atlas.compatible _ hd₁ _ hd₂) (d₁.isChart.compatible d₂.isChart (P := PZ))
  cover q := by
    classical
    obtain ⟨c, hc, hy⟩ := B.atlas.cover q.1.2
    have hfz : f q.1.1 ∈ c.φ.source := by
      rw [c.source_eq, mem_preimage, show P q.1.2 = f q.1.1 from q.2] at hy; exact hy
    obtain ⟨ψ₀, hψ₀, hz⟩ := PZ.exists_isChart_mem_source q.1.1
    have hfc : Continuous f := continuousOn_univ.1 hf.continuousOn
    have hV : IsOpen (ψ₀.source ∩ f ⁻¹' c.φ.source) :=
      ψ₀.isOpen_source.inter (c.φ.isOpen_source.preimage hfc)
    set ψ := ψ₀.restrict inter_subset_left hV
    have hψ : PZ.IsChart ψ := MPolyfold.IsChart.restrict PZ hψ₀ inter_subset_left hV
    have hψf : MapsTo f ψ.source c.φ.source := fun z hz => hz.2
    obtain ⟨RZ, hRZ⟩ := ψ.model.isScRetract
    have hsm := hf.smooth ψ c.φ hψ c.isChart ψ.source ψ.isOpen_source
      (fun z hz => ⟨mem_univ _, hz⟩) hψf
    rw [ψ.image_source] at hsm
    let d : PullbackChartData PX P PZ f := ⟨c, ψ, hψ, hψf, RZ, hRZ, hsm⟩
    exact ⟨d.toChart q, ⟨d, q, hc, rfl⟩, show q.1.1 ∈ ψ.source from ⟨hz, hfz⟩⟩

/-- **Proposition 2.6.8 (preprint 2.54)**: the pull-back `P_f : f*Y → Z` of a strong bundle `P : Y → X` along an
sc-smooth map `f : Z → X` carries a natural structure of a strong bundle over `Z`: `f*Y` is
paracompact Hausdorff, `P_f` is a continuous surjection with Banachable fibres
`P_f⁻¹(z) ≅ P⁻¹(f(z))`, and the pulled-back charts `Φ_f(z, y) = (ψ(z), pr_F Φ(y))` with the
strong bundle retractions `R_g(w, h) = (r_Z(w), Γ(g(r_Z(w)), h))`, `g = φ ∘ f ∘ ψ⁻¹`, form a strong
bundle atlas (the preprint: "the easy proof is left to the reader"). -/
theorem proposition_2_6_8 (B : StrongBundle PX P) (hf : PZ.IsScSmoothMap PX f) :
    haveI := paracompactSpace_pullbackSpace (f := f) PZ B
    ∃ B' : StrongBundle PZ (pullbackProj P f), B'.atlas.charts = (pullbackAtlas B hf).charts := by
  have := paracompactSpace_pullbackSpace (f := f) PZ B
  refine ⟨⟨continuous_pullbackProj P f, fun z => ?_, fun z => ?_, pullbackAtlas B hf⟩, rfl⟩
  · obtain ⟨y, hy⟩ := B.surjective (f z)
    exact ⟨⟨(z, y), hy⟩, rfl⟩
  · obtain ⟨Bsp, h1, h2, h3, ⟨e⟩⟩ := B.banachable (f z)
    exact ⟨Bsp, h1, h2, h3, ⟨(pullbackFiberCLE z).trans e⟩⟩

end PullbackChart

end Polyfold
