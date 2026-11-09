import Polyfold.Chapter2.TangentMapLinear
import Polyfold.Chapter2.SubMPolyfold

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §2.3, Proposition 2.3.19
(3), (4), p. 42 (preprint: Proposition 2.21 (3), (4), p. 30): the tangent space of a
sub-M-polyfold inside the tangent space of the ambient M-polyfold.

# `T_aA ⊆ T_aX` for a sub-M-polyfold `A ⊆ X`

## The text, paraphrased

(2021 Proposition 2.3.19, p. 42) A sub-M-polyfold `A` of `X` has a natural M-polyfold structure
with: (1) `i : A → X` sc-smooth, a homeomorphism onto its image; (2) `i⁻¹ ∘ r : V → A` sc-smooth
for every sc-smooth retraction `r : V → V` with `r(V) = A ∩ V`; (3) at a smooth `a ∈ A`, `T_aA`
has an sc-complement in `T_aX`; (4) for `s : W → W` an sc-smooth retraction with `s(W) = W ∩ A`
and `a ∈ W` smooth, the induced map `W → A` is sc-smooth and `Ts(a)T_aX = T_aA`.

## What is formalized (row V2.25 of `Exposition/cmp/ch02.json`, and row V7.30 through
`Chapter7/SubGroupoidTangent.lean`)

(1), (2) are `subPolyfold_inclusion_isScSmooth`, `subPolyfold_retraction_isScSmooth`
(`SubMPolyfold.lean`); (3), (4) in a chart are `proposition_2_3_19_three`, `proposition_2_3_19_four`
(`Metrizable.lean`).  With the linear structure of `T_xX` (`TangentSpaceLinear.lean`, gap G.7)
and the fibrewise linearity of tangent maps (`TangentMapLinear.lean`), (3) and (4) are stated in
`T_aX` itself, for `a ∈ A₁` (smoothness is not needed for the linear statements, as in the chart
form, V2.25):

* `MPolyfold.subInclusionCLM hA hax : T_aA →L[ℝ] T_aX`, the tangent of the inclusion `Ti`, and
  `MPolyfold.subRetractionCLM hA hax d a₀ hxV : T_aX →L[ℝ] T_aA`, the tangent of `i⁻¹ ∘ r`,
  for a retraction datum `(V, r)` with `a ∈ V`.
* **`MPolyfold.subRetractionCLM_subInclusionCLM`**: `T(i⁻¹ ∘ r) ∘ Ti = id` on `T_aA` (chain
  rule on `i⁻¹(V)`, where `i⁻¹ ∘ r ∘ i = id`); hence `Ti` is injective
  (`injective_subInclusionCLM`) and `T(i⁻¹ ∘ r)` is surjective.
* **`MPolyfold.proposition_2_3_19_3_linear`** (the linear content of (3)): `Ti(T_aA)` is a
  closed subspace of `T_aX` with the closed complement `ker T(i⁻¹ ∘ r)`:
  `T_aX = Ti(T_aA) ⊕ ker T(i⁻¹ ∘ r)`.
* **`MPolyfold.proposition_2_3_19_4`**: `T(i⁻¹ ∘ r) : T_aX → T_aA` is onto,
  `Ti ∘ T(i⁻¹ ∘ r) = Tr` on `T_aX` (for `r : V → X`), and the range of `Tr(a)` on `T_aX` is
  `Ti(T_aA)`: this is `Tr(a)T_aX = T_aA` with `T_aA ⊆ T_aX` through `Ti`.

## What the text leaves implicit, and the choices made

* The text identifies `T_aA` with a subspace of `T_aX` without naming the map; here it is `Ti`,
  which is injective by (4).
* The **sc**-complement of (3): the sc-structures of `T_aA`, `T_aX` at a smooth `a` live in the
  chart models (`isScSubspace_tangentFiberModel`); the sc-splitting
  `T_aO = Dt(a)E ⊕ (Dr(a) − Dt(a))E` of the text's proof is `proposition_2_3_19_three`
  (`Metrizable.lean`), in the chart.  Here (3) is proved as a topological direct sum in `T_aX`
  through the projection `Ti ∘ T(i⁻¹ ∘ r)`, which is the text's `Ts(a)`; that the complement
  `ker T(i⁻¹ ∘ r)` is an sc-subspace of `T_aX` (in the chart: the range of the idempotent
  sc-operator `Dr(a) − D(ρ ∘ r)(a)`) is not restated here.
* The text's `r : V → V` is read as the datum `d : P.SubData A` of `SubMPolyfold.lean`, with
  `i⁻¹ ∘ r` the total function `d.retractInto a₀` (junk value `a₀` off `V`).
-/

open Set Function Topology

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {A : Set X} (hA : P.IsSubMPolyfold A) [ParacompactSpace A]
variable {a : (subPolyfold hA).Level 1} {x : P.Level 1}
  (hax : ((subPolyfold hA).levelVal 1 a : A).1 = P.levelVal 1 x)

/-- **`Ti : T_aA →L[ℝ] T_aX`**, the tangent of the inclusion `i : A → X` on the fibre over
`a ∈ A₁` (Proposition 2.3.19 (1), p. 42). -/
def subInclusionCLM : (subPolyfold hA).tangentFiber a →L[ℝ] P.tangentFiber x :=
  tangentMapCLM (subPolyfold_inclusion_isScSmooth hA) hax

theorem subInclusionCLM_apply (β : (subPolyfold hA).tangentFiber a) :
    (subInclusionCLM hA hax β : P.TangentSpace) =
      tangentMap (subPolyfold_inclusion_isScSmooth hA) β.1 :=
  tangentMapCLM_apply _ _ β

include hax in
lemma levelVal_mem_of_sub : P.levelVal 1 x ∈ A := hax ▸ ((subPolyfold hA).levelVal 1 a).2

variable (d : P.SubData A) (a₀ : A) (hxV : P.levelVal 1 x ∈ d.V)

include hax hxV in
lemma retractInto_levelVal :
    d.retractInto a₀ (P.levelVal 1 x) = (subPolyfold hA).levelVal 1 a := by
  apply Subtype.ext
  rw [d.retractInto_val a₀ hxV, d.apply_eq_self ⟨levelVal_mem_of_sub hA hax, hxV⟩, hax]

/-- **`T(i⁻¹ ∘ r) : T_aX →L[ℝ] T_aA`**, the tangent of the sc-smooth map `i⁻¹ ∘ r : V → A` of
Proposition 2.3.19 (2) on the fibre over `a ∈ V`. -/
def subRetractionCLM : P.tangentFiber x →L[ℝ] (subPolyfold hA).tangentFiber a :=
  tangentMapOnCLM (subPolyfold_retraction_isScSmooth hA d a₀) hxV
    (retractInto_levelVal hA hax d a₀ hxV)

theorem subRetractionCLM_apply (α : P.tangentFiber x) :
    (subRetractionCLM hA hax d a₀ hxV α : (subPolyfold hA).TangentSpace) =
      tangentMapOn (subPolyfold_retraction_isScSmooth hA d a₀) α.1 :=
  tangentMapOnCLM_apply _ _ _ α

include hax hxV in
/-- The fibre `T_aA` lies over `i⁻¹(V)`. -/
lemma mem_tangentPreimage_preimage_of_mem_fiber {β : (subPolyfold hA).TangentSpace}
    (hβ : β ∈ (subPolyfold hA).tangentFiber a) :
    β ∈ (subPolyfold hA).tangentPreimage ((Subtype.val : A → X) ⁻¹' d.V) := by
  rw [mem_tangentPreimage, tangentProj_eq_of_mem_fiber hβ]
  change ((subPolyfold hA).levelVal 1 a : A).1 ∈ d.V
  rw [hax]; exact hxV

/-- **`T(i⁻¹ ∘ r) ∘ Ti = id` on `T_aA`** (the chain rule, `i⁻¹ ∘ r ∘ i = id` on `i⁻¹(V)`). -/
theorem subRetractionCLM_subInclusionCLM (β : (subPolyfold hA).tangentFiber a) :
    subRetractionCLM hA hax d a₀ hxV (subInclusionCLM hA hax β) = β := by
  apply Subtype.ext
  rw [subRetractionCLM_apply, subInclusionCLM_apply]
  have hi := subPolyfold_inclusion_isScSmooth hA
  have hr := subPolyfold_retraction_isScSmooth hA d a₀
  have hWo : IsOpen ((Subtype.val : A → X) ⁻¹' d.V) := d.isOpen.preimage continuous_subtype_val
  have hi' : (subPolyfold hA).IsScSmoothOn P Subtype.val ((Subtype.val : A → X) ⁻¹' d.V) :=
    hi.mono hWo (subset_univ _)
  have hmaps : MapsTo (Subtype.val : A → X) ((Subtype.val : A → X) ⁻¹' d.V) d.V := fun _ hz => hz
  have hβ := mem_tangentPreimage_preimage_of_mem_fiber hA hax d hxV β.2
  have h1 := tangentMapOn_comp hr hi' hmaps hβ
  have h2 := tangentMapOn_eqOn_id (hr.comp hi' hmaps) (fun z hz => by
    change d.retractInto a₀ z.1 = z
    apply Subtype.ext
    rw [d.retractInto_val a₀ hz, d.apply_eq_self ⟨z.2, hz⟩]) hβ
  rw [Function.comp_apply, tangentMapOn_eq_tangentMap hi hi' hβ] at h1
  rw [← h1, h2]; rfl

include d a₀ hxV in
/-- `Ti : T_aA → T_aX` is injective. -/
theorem injective_subInclusionCLM : Injective (subInclusionCLM hA hax) := by
  intro β γ h
  rw [← subRetractionCLM_subInclusionCLM hA hax d a₀ hxV β, h,
    subRetractionCLM_subInclusionCLM]

/-- `T(i⁻¹ ∘ r) : T_aX → T_aA` is surjective. -/
theorem surjective_subRetractionCLM : Surjective (subRetractionCLM hA hax d a₀ hxV) := fun β =>
  ⟨subInclusionCLM hA hax β, subRetractionCLM_subInclusionCLM hA hax d a₀ hxV β⟩

/-- The projection `Ti ∘ T(i⁻¹ ∘ r) : T_aX → T_aX` (the text's `Ts(a)`) is idempotent. -/
theorem isIdempotentElem_subInclusionCLM_comp_subRetractionCLM :
    IsIdempotentElem ((subInclusionCLM hA hax).comp (subRetractionCLM hA hax d a₀ hxV)) := by
  change ((subInclusionCLM hA hax).comp (subRetractionCLM hA hax d a₀ hxV)).comp
    ((subInclusionCLM hA hax).comp (subRetractionCLM hA hax d a₀ hxV)) = _
  ext α
  simp only [ContinuousLinearMap.comp_apply, subRetractionCLM_subInclusionCLM]

/-- `range (Ti ∘ T(i⁻¹ ∘ r)) = range Ti`. -/
theorem range_subInclusionCLM_comp_subRetractionCLM :
    LinearMap.range (((subInclusionCLM hA hax).comp (subRetractionCLM hA hax d a₀ hxV) :
        P.tangentFiber x →L[ℝ] P.tangentFiber x) : P.tangentFiber x →ₗ[ℝ] P.tangentFiber x) =
      LinearMap.range (subInclusionCLM hA hax :
        (subPolyfold hA).tangentFiber a →ₗ[ℝ] P.tangentFiber x) := by
  apply le_antisymm
  · rintro _ ⟨α, rfl⟩
    exact ⟨subRetractionCLM hA hax d a₀ hxV α, rfl⟩
  · rintro _ ⟨β, rfl⟩
    refine ⟨subInclusionCLM hA hax β, ?_⟩
    change subInclusionCLM hA hax (subRetractionCLM hA hax d a₀ hxV (subInclusionCLM hA hax β)) = _
    rw [subRetractionCLM_subInclusionCLM]
    rfl

/-- `ker (Ti ∘ T(i⁻¹ ∘ r)) = ker T(i⁻¹ ∘ r)`. -/
theorem ker_subInclusionCLM_comp_subRetractionCLM :
    LinearMap.ker (((subInclusionCLM hA hax).comp (subRetractionCLM hA hax d a₀ hxV) :
        P.tangentFiber x →L[ℝ] P.tangentFiber x) : P.tangentFiber x →ₗ[ℝ] P.tangentFiber x) =
      LinearMap.ker (subRetractionCLM hA hax d a₀ hxV :
        P.tangentFiber x →ₗ[ℝ] (subPolyfold hA).tangentFiber a) := by
  ext α
  change subInclusionCLM hA hax (subRetractionCLM hA hax d a₀ hxV α) = 0 ↔
    subRetractionCLM hA hax d a₀ hxV α = 0
  constructor
  · intro h
    exact injective_subInclusionCLM hA hax d a₀ hxV (h.trans (map_zero _).symm)
  · intro h; rw [h, map_zero]

/-- **Proposition 2.3.19 (3) (2021 p. 42; preprint 2.21 (3)), the linear content, in `T_aX`**:
`Ti(T_aA)` is a closed subspace of `T_aX` and `T_aX = Ti(T_aA) ⊕ ker T(i⁻¹ ∘ r)` is a direct sum
of closed subspaces (`T_aA` has a topological complement in `T_aX`), for `a ∈ A₁ ∩ V`. -/
theorem proposition_2_3_19_3_linear :
    IsClosed (LinearMap.range (subInclusionCLM hA hax :
        (subPolyfold hA).tangentFiber a →ₗ[ℝ] P.tangentFiber x) : Set (P.tangentFiber x)) ∧
      IsClosed (LinearMap.ker (subRetractionCLM hA hax d a₀ hxV :
        P.tangentFiber x →ₗ[ℝ] (subPolyfold hA).tangentFiber a) : Set (P.tangentFiber x)) ∧
      IsCompl
        (LinearMap.range (subInclusionCLM hA hax :
          (subPolyfold hA).tangentFiber a →ₗ[ℝ] P.tangentFiber x))
        (LinearMap.ker (subRetractionCLM hA hax d a₀ hxV :
          P.tangentFiber x →ₗ[ℝ] (subPolyfold hA).tangentFiber a)) := by
  set Pr := (subInclusionCLM hA hax).comp (subRetractionCLM hA hax d a₀ hxV) with hPr
  refine ⟨?_, ?_, ?_⟩
  · rw [← range_subInclusionCLM_comp_subRetractionCLM hA hax d a₀ hxV]
    exact ContinuousLinearMap.IsIdempotentElem.isClosed_range
      (isIdempotentElem_subInclusionCLM_comp_subRetractionCLM hA hax d a₀ hxV)
  · exact ContinuousLinearMap.isClosed_ker _
  · have hmem : ∀ α : P.tangentFiber x, Pr α ∈
        LinearMap.range (subInclusionCLM hA hax :
          (subPolyfold hA).tangentFiber a →ₗ[ℝ] P.tangentFiber x) :=
      fun α => ⟨subRetractionCLM hA hax d a₀ hxV α, rfl⟩
    have h := LinearMap.isCompl_of_proj (f := LinearMap.codRestrict _
      (Pr : P.tangentFiber x →ₗ[ℝ] P.tangentFiber x) hmem) (fun v => by
        obtain ⟨β, hβ⟩ := v.2
        apply Subtype.ext
        change Pr v.1 = v.1
        rw [← hβ]
        change subInclusionCLM hA hax
          (subRetractionCLM hA hax d a₀ hxV (subInclusionCLM hA hax β)) = subInclusionCLM hA hax β
        rw [subRetractionCLM_subInclusionCLM])
    rwa [LinearMap.ker_codRestrict, ker_subInclusionCLM_comp_subRetractionCLM] at h

/-- `Ti ∘ T(i⁻¹ ∘ r) = Tr` on `T_aX`, for `r : V → X` (the text's `Ts(a)` on `T_aX`). -/
theorem subInclusionCLM_subRetractionCLM_apply (α : P.tangentFiber x) :
    (subInclusionCLM hA hax (subRetractionCLM hA hax d a₀ hxV α) : P.TangentSpace) =
      tangentMapOn d.isScSmoothOn α.1 := by
  rw [subInclusionCLM_apply, subRetractionCLM_apply]
  have hi := subPolyfold_inclusion_isScSmooth hA
  have hr := subPolyfold_retraction_isScSmooth hA d a₀
  have hWo : IsOpen ((Subtype.val : A → X) ⁻¹' d.V) := d.isOpen.preimage continuous_subtype_val
  have hi' : (subPolyfold hA).IsScSmoothOn P Subtype.val ((Subtype.val : A → X) ⁻¹' d.V) :=
    hi.mono hWo (subset_univ _)
  have hmaps : MapsTo (d.retractInto a₀) d.V ((Subtype.val : A → X) ⁻¹' d.V) := fun z hz => by
    change (d.retractInto a₀ z).1 ∈ d.V
    rw [d.retractInto_val a₀ hz]; exact d.mapsTo hz
  have hα : α.1 ∈ P.tangentPreimage d.V := by
    rw [mem_tangentPreimage, tangentProj_eq_of_mem_fiber α.2]; exact hxV
  have h1 := tangentMapOn_comp hi' hr hmaps hα
  have h2 := tangentMapOn_congr (hi'.comp hr hmaps) d.isScSmoothOn d.isOpen subset_rfl subset_rfl
    (fun z hz => by
      change (d.retractInto a₀ z).1 = d.r z
      exact d.retractInto_val a₀ hz) hα
  rw [Function.comp_apply, tangentMapOn_eq_tangentMap hi hi'
    (tangentMapOn_mapsTo hr hmaps hα)] at h1
  rw [← h1, h2]

/-- **Proposition 2.3.19 (4) (2021 p. 42; preprint 2.21 (4)), in `T_aX`**: for a retraction
`r : V → V` onto `A ∩ V` and `a ∈ A₁ ∩ V`, the induced map `i⁻¹ ∘ r : V → A` is sc-smooth
(`subPolyfold_retraction_isScSmooth`), its tangent `T(i⁻¹ ∘ r) : T_aX → T_aA` is onto,
`Ti ∘ T(i⁻¹ ∘ r) = Tr(a)` on `T_aX`, and `Tr(a)T_aX = Ti(T_aA)`: this is `Tr(a)T_aX = T_aA`. -/
theorem proposition_2_3_19_4 :
    Surjective (subRetractionCLM hA hax d a₀ hxV) ∧
      (∀ α : P.tangentFiber x,
        (subInclusionCLM hA hax (subRetractionCLM hA hax d a₀ hxV α) : P.TangentSpace) =
          tangentMapOn d.isScSmoothOn α.1) ∧
      LinearMap.range (((subInclusionCLM hA hax).comp (subRetractionCLM hA hax d a₀ hxV) :
          P.tangentFiber x →L[ℝ] P.tangentFiber x) : P.tangentFiber x →ₗ[ℝ] P.tangentFiber x) =
        LinearMap.range (subInclusionCLM hA hax :
          (subPolyfold hA).tangentFiber a →ₗ[ℝ] P.tangentFiber x) :=
  ⟨surjective_subRetractionCLM hA hax d a₀ hxV,
    subInclusionCLM_subRetractionCLM_apply hA hax d a₀ hxV,
    range_subInclusionCLM_comp_subRetractionCLM hA hax d a₀ hxV⟩

end MPolyfold

end Polyfold
