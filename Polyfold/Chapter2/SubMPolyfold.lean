import Polyfold.Chapter2.TangentBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.2,
Proposition 2.3.19 (preprint 2.21) (1), (2) (sub-M-polyfolds are M-polyfolds), and §2.3, Lemma 2.4.6 (preprint 2.26).

# Sub-M-polyfolds as M-polyfolds

## The text, paraphrased

(Proposition 2.3.19 (preprint 2.21)) A sub-M-polyfold `A` of `X` has a natural M-polyfold structure, for which
(1) the inclusion `i : A → X` is sc-smooth and a homeomorphism onto its image; (2) for every
sc-smooth retraction `r : V → V` with `r(V) = A ∩ V` the map `i⁻¹ ∘ r : V → A` is sc-smooth;
(3) `T_aA` has an sc-complement in `T_aX` at smooth points; (4) for `s : W → W` with
`s(W) = W ∩ A`, `Ts(a) T_aX = T_aA`.  *Proof of the structure.* Given a chart `(φ, V)` around
`a ∈ A` and a retraction `r : U → U` with `r(U) = U ∩ A`, the set `W = r⁻¹(U ∩ V) ∩ (U ∩ V)` is
open with `r(W) ⊆ W` and `r(W) = W ∩ A`; `ρ = φ ∘ r ∘ φ⁻¹` is an sc-smooth retraction of `φ(W)`,
so `O' = ρ(φ(W)) = φ(W ∩ A)` is a retract (Proposition 2.3.1 (preprint 2.10) (2)) and `(φ|_{W ∩ A}, W ∩ A, (O', C, E))`
is a chart on `A`.  Two such charts are compatible: with a retraction `s''` onto
`ψ(W ∩ A ∩ W' ∩ A)`, `(ψ' ∘ ψ⁻¹) ∘ s'' = (φ' ∘ φ⁻¹) ∘ s''` is sc-smooth by the chain rule.
(Lemma 2.4.6 (preprint 2.26)) `d_A(a) ≤ d_X(a)`: the chart of `A` built from a chart of `X` realizing `d_X(a)`
has the same `C` and the same image point.

## What is formalized

* `IsScSmoothRetractMap.mono_source`: an sc-smooth map between retracts restricts to every
  sub-retract `O₁ ⊆ O` (the text's chain-rule argument `(φ' ∘ φ⁻¹) ∘ s''`, once and for all).
* `MPolyfold.SubData P A`: the data `(V, r)` of Definition 2.3.18 (preprint 2.20) at a point; `SubData.shrink`
  (the set `W` and its properties `r(W) ⊆ W`, `r(W) = W ∩ A`); `SubData.rho_isScSmooth`
  (`ρ = φ ∘ r ∘ φ⁻¹` is sc-smooth on `φ(W)`) and `SubData.isScRetract_image`
  (`φ(W ∩ A)` is a retract, Proposition 2.3.1 (preprint 2.10) (2)).
* `MPolyfold.subChart d hφ a₀ : MChart A`, the chart `(φ|_{W ∩ A}, W ∩ A, (φ(W ∩ A), C, E))`;
  `subChart_compatible`; `MPolyfold.subAtlas`, `MPolyfold.subPolyfold P hA : MPolyfold A`
  (**Proposition 2.3.19 (preprint 2.21)**, the structure) with the argument `[ParacompactSpace A]` (supplied by
  `MPolyfold.paracompactSpace_subtype` in `Metrizable.lean`);
  `MPolyfold.paracompactSpace_of_isClosed`: a closed sub-M-polyfold is paracompact.
* `MPolyfold.subPolyfold_inclusion_isScSmooth` (**Proposition 2.3.19 (preprint 2.21) (1)**: `i : A → X` is
  sc-smooth; it is a homeomorphism onto its image by definition of the subspace topology), and
  `MPolyfold.subPolyfold_retraction_isScSmooth` (**Proposition 2.3.19 (preprint 2.21) (2)**).
* `Polyfold.lemma_2_4_6` (**Lemma 2.4.6 (preprint 2.26)**): `d_A(a) ≤ d_X(a)`.

## What the text leaves implicit, and the choices made

* The text does not discuss the topology of `A`; here `A` carries the subspace topology, so that
  `i` is a homeomorphism onto its image by construction, and the chart domains `W ∩ A` are open
  in `A`.
* Paracompactness of `A` is an instance argument `[ParacompactSpace A]` of `subPolyfold`, because
  this file comes before the metrizability proof.  It is not an added hypothesis: as in the text
  (through Theorem 2.3.10 (preprint 2.16), `A` is metrizable as a subspace of the metrizable `X`), it is proved for
  every subset `A` by `MPolyfold.paracompactSpace_subtype` in `Metrizable.lean` (not an instance,
  since it depends on the M-polyfold structure of `X`: it is supplied with
  `haveI := P.paracompactSpace_subtype A`).  For a *closed* sub-M-polyfold it is proved here as
  well (`paracompactSpace_of_isClosed`; a sub-M-polyfold is locally closed, not closed in general).
* Proposition 2.3.19 (preprint 2.21) (3), (4) (the tangent spaces of `A`) are proved in a chart, as the text proves
  them, in `Metrizable.lean` (`Polyfold.proposition_2_3_19_three`, `Polyfold.proposition_2_3_19_four`); their
  transport to `T_aX` is not formalized, since `T_xX` carries no linear or sc-structure here (gap
  G.7 of the report).
* In Proposition 2.3.19 (preprint 2.21) (2) the map `i⁻¹ ∘ r : V → A` is a total function `X → A` with a junk value
  off `r⁻¹(A)`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

variable {E E' : ScBanach}

/-- An sc-smooth map between retracts is sc-smooth on every sub-retract `O₁ ⊆ O`: for a retraction
`S` onto `O₁`, `f ∘ S = (f ∘ R) ∘ S` (the text's "`(ψ' ∘ ψ⁻¹) ∘ s'' = (φ' ∘ φ⁻¹) ∘ s''`"). -/
theorem IsScSmoothRetractMap.mono_source {C : Set (E 0)} {C' : Set (E' 0)} {O O₁ : Set (E 0)}
    {O' : Set (E' 0)} {f : E 0 → E' 0} (hf : IsScSmoothRetractMap E C O E' C' O' f)
    (hO : IsScRetract E C O) (hO₁ : O₁ ⊆ O) : IsScSmoothRetractMap E C O₁ E' C' O' f where
  mapsTo := hf.mapsTo.mono_left hO₁
  comp_isScSmooth S hS := by
    obtain ⟨R, rfl⟩ := hO
    have hmaps : MapsTo S S.U R.U := fun y hy => R.retract_subset (hO₁ (hS ▸ S.apply_mem_retract hy))
    have := IsScSmooth.comp S.isScDomain R.isScDomain (hf.comp_isScSmooth R rfl) S.isScSmooth hmaps
    refine this.congr S.isScDomain fun y hy => ?_
    simp only [Function.comp_apply, R.apply_eq_self_of_mem_retract (hO₁ (hS ▸ S.apply_mem_retract hy))]

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-! ### The local data of a sub-M-polyfold -/

/-- The data `(V, r)` of Definition 2.3.18 (preprint 2.20) at a point `a` of a sub-M-polyfold `A`: an open `V ∋ a` and an
sc-smooth retraction `r : V → V` with `r(V) = A ∩ V`. -/
structure SubData (A : Set X) where
  /-- The open set `V`. -/
  V : Set X
  /-- The retraction `r`. -/
  r : X → X
  isOpen : IsOpen V
  mapsTo : MapsTo r V V
  isScSmoothOn : P.IsScSmoothOn P r V
  idem : ∀ x ∈ V, r (r x) = r x
  image : r '' V = A ∩ V

namespace SubData

variable {P} {A : Set X} (d : P.SubData A)

lemma apply_mem (hx : x ∈ d.V) : d.r x ∈ A := (d.image ▸ ⟨x, hx, rfl⟩ : d.r x ∈ A ∩ d.V).1

lemma apply_eq_self {x : X} (hx : x ∈ A ∩ d.V) : d.r x = x := by
  rw [← d.image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact d.idem y hy

lemma continuousOn : ContinuousOn d.r d.V := d.isScSmoothOn.continuousOn

variable (φ : MChart X)

/-- The set `W = V ∩ dom φ ∩ r⁻¹(V ∩ dom φ)` of the proof of Proposition 2.3.19 (preprint 2.21). -/
def shrink : Set X := (d.V ∩ φ.source) ∩ d.r ⁻¹' (d.V ∩ φ.source)

lemma shrink_subset_V : d.shrink φ ⊆ d.V := fun _ hx => hx.1.1

lemma shrink_subset_source : d.shrink φ ⊆ φ.source := fun _ hx => hx.1.2

lemma isOpen_shrink : IsOpen (d.shrink φ) :=
  (d.continuousOn.mono inter_subset_left).isOpen_inter_preimage (d.isOpen.inter φ.isOpen_source)
    (d.isOpen.inter φ.isOpen_source)

lemma mem_shrink {a : X} (ha : a ∈ A) (haV : a ∈ d.V) (haφ : a ∈ φ.source) : a ∈ d.shrink φ :=
  ⟨⟨haV, haφ⟩, by rw [mem_preimage, d.apply_eq_self ⟨ha, haV⟩]; exact ⟨haV, haφ⟩⟩

/-- `r(W) ⊆ W`. -/
lemma mapsTo_shrink : MapsTo d.r (d.shrink φ) (d.shrink φ) := fun x hx =>
  ⟨hx.2, by rw [mem_preimage, d.idem x hx.1.1]; exact hx.2⟩

/-- `r(W) = W ∩ A`. -/
lemma image_shrink : d.r '' d.shrink φ = d.shrink φ ∩ A := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨d.mapsTo_shrink φ hx, d.apply_mem hx.1.1⟩
  · rintro ⟨hy, hyA⟩
    exact ⟨y, hy, d.apply_eq_self ⟨hyA, hy.1.1⟩⟩

variable (hφ : P.IsChart φ)
include hφ

/-- `ρ = φ ∘ r ∘ φ⁻¹` is sc-smooth `φ(W) → φ(W)`. -/
theorem rho_isScSmooth : IsScSmoothRetractMap φ.model.E φ.model.C (φ '' d.shrink φ) φ.model.E
    φ.model.C (φ '' d.shrink φ) (φ ∘ d.r ∘ φ.symm) := by
  refine (d.isScSmoothOn.smooth φ φ hφ hφ (d.shrink φ) (d.isOpen_shrink φ)
    (fun x hx => ⟨hx.1.1, hx.1.2⟩) fun x hx => (d.mapsTo_shrink φ hx).1.2).mono_target ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [Function.comp_apply, φ.symm_apply_apply hx.1.2]
  exact ⟨d.r x, d.mapsTo_shrink φ hx, rfl⟩

omit hφ in
/-- `ρ ∘ ρ = ρ` on `φ(W)`. -/
lemma rho_idem {z : φ.model.E 0} (hz : z ∈ φ '' d.shrink φ) :
    (φ ∘ d.r ∘ φ.symm) ((φ ∘ d.r ∘ φ.symm) z) = (φ ∘ d.r ∘ φ.symm) z := by
  obtain ⟨x, hx, rfl⟩ := hz
  simp only [Function.comp_apply, φ.symm_apply_apply hx.1.2,
    φ.symm_apply_apply (d.mapsTo_shrink φ hx).1.2, d.idem x hx.1.1]

omit hφ in
/-- `ρ(φ(W)) = φ(W ∩ A)`. -/
lemma rho_image : (φ ∘ d.r ∘ φ.symm) '' (φ '' d.shrink φ) = φ '' (d.shrink φ ∩ A) := by
  rw [← d.image_shrink φ, ← image_comp, ← image_comp]
  refine image_congr fun x hx => ?_
  simp only [Function.comp_apply, φ.symm_apply_apply hx.1.2]

omit hφ in
/-- The model `O' = φ(W ∩ A)` of the chart of `A` is an sc-smooth retract (Proposition 2.3.1 (preprint 2.10) (2)). -/
theorem isScRetract_image (hφ : P.IsChart φ) :
    IsScRetract φ.model.E φ.model.C (φ '' (d.shrink φ ∩ A)) := by
  rw [← d.rho_image φ]
  exact proposition_2_3_1_two (φ.isScRetract_image (d.shrink_subset_source φ) (d.isOpen_shrink φ))
    (d.rho_isScSmooth φ hφ) fun _ hz => d.rho_idem φ hz

end SubData

/-! ### The charts of a sub-M-polyfold (Proposition 2.3.19 (preprint 2.21)) -/

section SubChart

variable {P} {A : Set X} (d : P.SubData A) {φ ψ : MChart X} (hφ : P.IsChart φ) (a₀ : A)

open scoped Classical in
/-- The inverse `φ(W ∩ A) → W ∩ A` of the sub-chart, with the junk value `a₀`. -/
def subChartInv (z : φ.model.E 0) : A :=
  if h : z ∈ φ '' (d.shrink φ ∩ A) then
    ⟨φ.symm z, by
      obtain ⟨x, hx, rfl⟩ := h
      rw [φ.symm_apply_apply (d.shrink_subset_source φ hx.1)]; exact hx.2⟩
  else a₀

lemma subChartInv_val {z : φ.model.E 0} (hz : z ∈ φ '' (d.shrink φ ∩ A)) :
    (subChartInv d a₀ z).1 = φ.symm z := by
  unfold subChartInv; rw [dif_pos hz]

/-- The chart `(φ|_{W ∩ A}, W ∩ A, (φ(W ∩ A), C, E))` of the sub-M-polyfold `A`, with the junk value
`a₀` for the inverse. -/
def subChart : MChart A where
  model := ⟨φ.model.E, φ.model.C, φ '' (d.shrink φ ∩ A), d.isScRetract_image φ hφ⟩
  toPartialEquiv :=
    { toFun := fun x => φ x.1
      invFun := subChartInv d a₀
      source := {x | x.1 ∈ d.shrink φ}
      target := φ '' (d.shrink φ ∩ A)
      map_source' := fun x hx => ⟨x.1, ⟨hx, x.2⟩, rfl⟩
      map_target' := fun z hz => by
        show (subChartInv d a₀ z).1 ∈ d.shrink φ
        rw [subChartInv_val d a₀ hz]
        obtain ⟨x, hx, rfl⟩ := hz
        rw [φ.symm_apply_apply (d.shrink_subset_source φ hx.1)]; exact hx.1
      left_inv' := fun x hx => by
        have h : φ x.1 ∈ φ '' (d.shrink φ ∩ A) := ⟨x.1, ⟨hx, x.2⟩, rfl⟩
        apply Subtype.ext
        rw [subChartInv_val d a₀ h]
        exact φ.symm_apply_apply (d.shrink_subset_source φ hx)
      right_inv' := fun z hz => by
        change φ (subChartInv d a₀ z).1 = z
        rw [subChartInv_val d a₀ hz]
        exact φ.apply_symm_apply (φ.image_subset_model (fun _ hx => d.shrink_subset_source φ hx.1) hz) }
  isOpen_source := (d.isOpen_shrink φ).preimage continuous_subtype_val
  target_eq := rfl
  continuousOn_toFun := φ.continuousOn_toFun.comp continuous_subtype_val.continuousOn
    fun _ hx => d.shrink_subset_source φ hx
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine continuous_induced_rng.2 ?_
    have h1 : Continuous ((φ '' (d.shrink φ ∩ A)).domRestrict φ.symm) :=
      continuousOn_iff_continuous_domRestrict.1
        (φ.continuousOn_invFun.mono (φ.image_subset_model fun _ hx => d.shrink_subset_source φ hx.1))
    refine h1.congr fun z => ?_
    exact (subChartInv_val d a₀ z.2).symm

lemma subChart_source : (subChart d hφ a₀).source = {x | x.1 ∈ d.shrink φ} := rfl

lemma subChart_apply (x : A) : subChart d hφ a₀ x = φ x.1 := rfl

lemma subChart_model_O : (subChart d hφ a₀).model.O = φ '' (d.shrink φ ∩ A) := rfl

lemma subChart_model_E : (subChart d hφ a₀).model.E = φ.model.E := rfl

lemma subChart_model_C : (subChart d hφ a₀).model.C = φ.model.C := rfl

lemma subChart_symm_apply {z : φ.model.E 0} (hz : z ∈ φ '' (d.shrink φ ∩ A)) :
    ((subChart d hφ a₀).symm z : X) = φ.symm z :=
  subChartInv_val d a₀ hz

/-- The overlap of two sub-charts is the image of `W ∩ W' ∩ A`, a subset of `φ(V ∩ V')`. -/
lemma subChart_overlap (d' : P.SubData A) (hψ : P.IsChart ψ) (b₀ : A) :
    (subChart d hφ a₀).overlap (subChart d' hψ b₀) = φ '' ((d.shrink φ ∩ d'.shrink ψ) ∩ A) := by
  ext z
  constructor
  · rintro ⟨x, ⟨hx, hx'⟩, rfl⟩
    exact ⟨x.1, ⟨⟨hx, hx'⟩, x.2⟩, rfl⟩
  · rintro ⟨x, ⟨⟨hx, hx'⟩, hxA⟩, rfl⟩
    exact ⟨⟨x, hxA⟩, ⟨hx, hx'⟩, rfl⟩

/-- Two sub-charts are sc-smoothly compatible: their transition maps are restrictions of the
transition maps of `X` to sub-retracts of the overlaps. -/
theorem subChart_compatible (d' : P.SubData A) (hψ : P.IsChart ψ) (b₀ : A) :
    (subChart d hφ a₀).Compatible (subChart d' hψ b₀) := by
  have key : ∀ (d d' : P.SubData A) (φ ψ : MChart X) (hφ : P.IsChart φ) (hψ : P.IsChart ψ)
      (a₀ b₀ : A), IsScSmoothRetractMap (subChart d hφ a₀).model.E (subChart d hφ a₀).model.C
        ((subChart d hφ a₀).overlap (subChart d' hψ b₀)) (subChart d' hψ b₀).model.E
        (subChart d' hψ b₀).model.C ((subChart d' hψ b₀).overlap (subChart d hφ a₀))
        ((subChart d hφ a₀).transition (subChart d' hψ b₀)) := by
    intro d d' φ ψ hφ hψ a₀ b₀
    rw [subChart_overlap, subChart_overlap]
    have hsub : φ '' ((d.shrink φ ∩ d'.shrink ψ) ∩ A) ⊆ φ.overlap ψ :=
      image_mono fun x hx => ⟨d.shrink_subset_source φ hx.1.1, d'.shrink_subset_source ψ hx.1.2⟩
    refine (((hφ.compatible hψ (P := P)).1.mono_source (φ.isScRetract_overlap ψ) hsub).mono_target
      ?_).congr ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [φ.transition_apply ψ (d.shrink_subset_source φ hx.1.1)]
      exact ⟨x, ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [φ.transition_apply ψ (d.shrink_subset_source φ hx.1.1)]
      change ψ x = ψ ((subChart d hφ a₀).symm (φ x)).1
      rw [subChart_symm_apply d hφ a₀ ⟨x, ⟨hx.1.1, hx.2⟩, rfl⟩,
        φ.symm_apply_apply (d.shrink_subset_source φ hx.1.1)]
  exact ⟨key d d' φ ψ hφ hψ a₀ b₀, key d' d ψ φ hψ hφ b₀ a₀⟩

end SubChart

/-! ### The M-polyfold structure of a sub-M-polyfold -/

section SubPolyfold

variable {P} {A : Set X} (hA : P.IsSubMPolyfold A)

/-- The data of Definition 2.3.18 (preprint 2.20) at a point of a sub-M-polyfold. -/
def IsSubMPolyfold.data {a : X} (ha : a ∈ A) : P.SubData A :=
  let h := hA a ha
  { V := h.choose
    r := h.choose_spec.2.2.choose
    isOpen := h.choose_spec.1
    mapsTo := h.choose_spec.2.2.choose_spec.1
    isScSmoothOn := h.choose_spec.2.2.choose_spec.2.1
    idem := h.choose_spec.2.2.choose_spec.2.2.1
    image := h.choose_spec.2.2.choose_spec.2.2.2 }

lemma IsSubMPolyfold.mem_data_V {a : X} (ha : a ∈ A) : a ∈ (hA.data ha).V := (hA a ha).choose_spec.2.1

/-- The atlas of the sub-M-polyfold `A`: all sub-charts. -/
def subAtlas : MAtlas A where
  charts := {χ | ∃ (d : P.SubData A) (φ : MChart X) (hφ : P.IsChart φ) (a₀ : A),
    χ = subChart d hφ a₀}
  compatible := by
    rintro _ ⟨d, φ, hφ, a₀, rfl⟩ _ ⟨d', ψ, hψ, b₀, rfl⟩
    exact subChart_compatible d hφ a₀ d' hψ b₀
  cover a := by
    obtain ⟨φ, hφ, haφ⟩ := P.exists_isChart_mem_source a.1
    exact ⟨subChart (hA.data a.2) hφ a, ⟨_, _, _, _, rfl⟩,
      (hA.data a.2).mem_shrink φ a.2 (hA.mem_data_V a.2) haφ⟩

omit [T2Space X] in
/-- A closed sub-M-polyfold is paracompact (closed subsets of paracompact spaces are). -/
theorem paracompactSpace_of_isClosed (h : IsClosed A) : ParacompactSpace A :=
  h.isClosedEmbedding_subtypeVal.paracompactSpace

/-- **Proposition 2.3.19 (preprint 2.21)**: a sub-M-polyfold `A` of `X` is an M-polyfold, with the charts
`(φ|_{W ∩ A}, W ∩ A, (φ(W ∩ A), C, E))`.  Paracompactness of `A` is an argument, proved by
`MPolyfold.paracompactSpace_subtype` in `Metrizable.lean` (see the header). -/
def subPolyfold [ParacompactSpace A] : MPolyfold A where
  atlas := subAtlas hA

theorem subPolyfold_isChart [ParacompactSpace A] (d : P.SubData A) {φ : MChart X} (hφ : P.IsChart φ)
    (a₀ : A) : (subPolyfold hA).IsChart (subChart d hφ a₀) :=
  (subPolyfold hA).isChart_of_mem ⟨d, φ, hφ, a₀, rfl⟩

/-- **Proposition 2.3.19 (preprint 2.21) (1)**: the inclusion `i : A → X` is sc-smooth (and a homeomorphism onto
its image, by the choice of the subspace topology). -/
theorem subPolyfold_inclusion_isScSmooth [ParacompactSpace A] :
    (subPolyfold hA).IsScSmoothMap P (Subtype.val : A → X) := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ continuous_subtype_val.continuousOn fun a _ => ?_
  obtain ⟨φ, hφ, haφ⟩ := P.exists_isChart_mem_source a.1
  set d := hA.data a.2
  refine ⟨subChart d hφ a, φ, (subChart d hφ a).source, subPolyfold_isChart hA d hφ a, hφ,
    (subChart d hφ a).isOpen_source, d.mem_shrink φ a.2 (hA.mem_data_V a.2) haφ,
    fun _ hx => ⟨mem_univ _, hx⟩, fun _ hx => d.shrink_subset_source φ hx, ?_⟩
  rw [(subChart d hφ a).image_source]
  refine ((isScSmoothRetractMap_id _).mono_target
    (φ.image_subset_model fun _ hx => d.shrink_subset_source φ hx.1)).congr fun z hz => ?_
  change z = φ ((subChart d hφ a).symm z).1
  rw [subChart_symm_apply d hφ a hz,
    φ.apply_symm_apply (φ.image_subset_model (fun _ hx => d.shrink_subset_source φ hx.1) hz)]

open scoped Classical in
/-- The map `i⁻¹ ∘ r : V → A` of Proposition 2.3.19 (preprint 2.21) (2), as a total function with junk value `a₀`. -/
def SubData.retractInto (d : P.SubData A) (a₀ : A) (x : X) : A :=
  if h : d.r x ∈ A then ⟨d.r x, h⟩ else a₀

lemma SubData.retractInto_val (d : P.SubData A) (a₀ : A) {x : X} (hx : x ∈ d.V) :
    (d.retractInto a₀ x).1 = d.r x := by
  rw [SubData.retractInto, dif_pos (d.apply_mem hx)]

/-- **Proposition 2.3.19 (preprint 2.21) (2)**: for every retraction `r : V → V` with `r(V) = A ∩ V`, the map
`i⁻¹ ∘ r : V → A` is sc-smooth. -/
theorem subPolyfold_retraction_isScSmooth [ParacompactSpace A] (d : P.SubData A) (a₀ : A) :
    P.IsScSmoothOn (subPolyfold hA) (d.retractInto a₀) d.V := by
  have hcont : ContinuousOn (d.retractInto a₀) d.V := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact d.continuousOn.congr fun x hx => d.retractInto_val a₀ hx
  refine IsScSmoothOn.of_exists_charts d.isOpen hcont fun x hx => ?_
  obtain ⟨φ', hφ', hxφ'⟩ := P.exists_isChart_mem_source x
  obtain ⟨φ, hφ, hrxφ⟩ := P.exists_isChart_mem_source (d.r x)
  -- the open set `V₀ = V ∩ dom φ' ∩ r⁻¹(dom φ)`
  set V₀ := (d.V ∩ φ'.source) ∩ d.r ⁻¹' φ.source with hV₀
  have hV₀o : IsOpen V₀ :=
    (d.continuousOn.mono inter_subset_left).isOpen_inter_preimage (d.isOpen.inter φ'.isOpen_source)
      φ.isOpen_source
  have hmaps : ∀ y ∈ V₀, d.r y ∈ d.shrink φ := fun y hy =>
    ⟨⟨d.mapsTo hy.1.1, hy.2⟩, by rw [mem_preimage, d.idem y hy.1.1]; exact ⟨d.mapsTo hy.1.1, hy.2⟩⟩
  refine ⟨φ', subChart d hφ a₀, V₀, hφ', subPolyfold_isChart hA d hφ a₀, hV₀o, ⟨⟨hx, hxφ'⟩, hrxφ⟩,
    fun _ hy => ⟨hy.1.1, hy.1.2⟩, fun y hy => ?_, ?_⟩
  · change (d.retractInto a₀ y).1 ∈ d.shrink φ
    rw [d.retractInto_val a₀ hy.1.1]; exact hmaps y hy
  · have h1 := d.isScSmoothOn.smooth φ' φ hφ' hφ V₀ hV₀o (fun _ hy => ⟨hy.1.1, hy.1.2⟩)
      fun _ hy => hy.2
    refine (h1.mono_target ?_).congr ?_
    · rintro _ ⟨y, hy, rfl⟩
      simp only [Function.comp_apply, φ'.symm_apply_apply hy.1.2]
      exact ⟨d.r y, ⟨hmaps y hy, d.apply_mem hy.1.1⟩, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      change φ (d.r (φ'.symm (φ' y))) = φ (d.retractInto a₀ (φ'.symm (φ' y))).1
      rw [φ'.symm_apply_apply hy.1.2, d.retractInto_val a₀ hy.1.1]

/-- **Lemma 2.4.6 (preprint 2.26)**: `d_A(a) ≤ d_X(a)` for a sub-M-polyfold `A ⊆ X`. -/
theorem _root_.Polyfold.lemma_2_4_6 [ParacompactSpace A] (a : A) :
    (subPolyfold hA).degIndex a ≤ P.degIndex a.1 := by
  obtain ⟨φ, hφ, haφ, hd⟩ := P.exists_isChart_degIndex_eq a.1
  rw [hd]
  exact (subPolyfold hA).degIndex_le (subPolyfold_isChart hA (hA.data a.2) hφ a)
    ((hA.data a.2).mem_shrink φ a.2 (hA.mem_data_V a.2) haφ)

end SubPolyfold

end MPolyfold

end Polyfold
