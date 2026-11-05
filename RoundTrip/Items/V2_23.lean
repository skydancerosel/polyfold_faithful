import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_23

/-! Round trip for V2_23 (Definition 2.20: sub-M-polyfolds).

`A` is the type of the only listed theorem, `Polyfold.MPolyfold.isSubMPolyfold_univ` (`X` is a
sub-M-polyfold of itself), instantiated at universe `0` (B lives in `Type`).
`Polyfold.MPolyfold.IsSubMPolyfold` is a definition (vocabulary); B says it is the text's notion.

The two definitions have the same shape (same `V`, same `r`, `r(V) ⊆ V`, `r ∘ r = r` on `V`,
`r(V) = A ∩ V`); they differ only in the reading of "`r` is sc-smooth on `V`" (Definition 2.14):
* the project (`IsScSmoothOn P P r V`): `r` continuous on `V` and, for ALL charts `φ, ψ` of `X`
  and every open `W ⊆ V ∩ dom φ` with `r(W) ⊆ dom ψ`, `ψ ∘ r ∘ φ⁻¹` is sc-smooth on `(φ(W), C, E)`
  (Definition 2.7 for every retraction);
* B (`IsScSmoothOnB`): every `x ∈ V` has SOME charts `φ ∋ x`, `ψ` with domains inside `V`,
  `r(dom φ) ⊆ dom ψ`, and `ψ ∘ r ∘ φ⁻¹` sc-smooth on `(O, C, E)` for SOME retraction; no
  continuity clause.
They agree (`isScSmoothOn_iff`): project ⇒ B by restricting charts (`IsChart.restrict`); B ⇒ project
by the locality of Definition 2.14 (`IsScSmoothOn.of_exists_charts`), continuity of `r` being
recovered from the chart representatives (sc-smooth maps between retracts are continuous). -/

namespace RoundTrip.V2_23
open Polyfold Set

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @Polyfold.MPolyfold.isSubMPolyfold_univ.{0}

theorem A_holds : A := @Polyfold.MPolyfold.isSubMPolyfold_univ.{0}

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- The project's Definition 2.14 on an open `V` with `r(V) ⊆ V` gives B's existential reading. -/
theorem isScSmoothOnB_of {r : X → X} {V : Set X} (hV : IsOpen V) (hrV : MapsTo r V V)
    (h : P.IsScSmoothOn P r V) : IsScSmoothOnB P r V := by
  intro x hx
  obtain ⟨ψ₀, hψ₀, hrxψ₀⟩ := P.exists_isChart_mem_source (r x)
  obtain ⟨φ₀, hφ₀, hxφ₀⟩ := P.exists_isChart_mem_source x
  -- `ψ = ψ₀|(dom ψ₀ ∩ V)`
  have hsψ : ψ₀.source ∩ V ⊆ ψ₀.source := inter_subset_left
  have hsψo : IsOpen (ψ₀.source ∩ V) := ψ₀.isOpen_source.inter hV
  set ψ := ψ₀.restrict hsψ hsψo with hψdef
  have hψ : P.IsChart ψ := hψ₀.restrict (P := P) hsψ hsψo
  -- `φ = φ₀|(dom φ₀ ∩ (V ∩ r⁻¹(dom ψ)))`
  have hpre : IsOpen (V ∩ r ⁻¹' ψ.source) := h.continuousOn.isOpen_inter_preimage hV hsψo
  have hsφ : φ₀.source ∩ (V ∩ r ⁻¹' ψ.source) ⊆ φ₀.source := inter_subset_left
  have hsφo : IsOpen (φ₀.source ∩ (V ∩ r ⁻¹' ψ.source)) := φ₀.isOpen_source.inter hpre
  set φ := φ₀.restrict hsφ hsφo with hφdef
  have hφ : P.IsChart φ := hφ₀.restrict (P := P) hsφ hsφo
  have hφsrc : φ.source = φ₀.source ∩ (V ∩ r ⁻¹' ψ.source) := rfl
  have hψsrc : ψ.source = ψ₀.source ∩ V := rfl
  have hxφ : x ∈ φ.source := by
    rw [hφsrc]; exact ⟨hxφ₀, hx, by rw [mem_preimage, hψsrc]; exact ⟨hrxψ₀, hrV hx⟩⟩
  have hφV : φ.source ⊆ V := fun y hy => by rw [hφsrc] at hy; exact hy.2.1
  have hψV : ψ.source ⊆ V := fun y hy => by rw [hψsrc] at hy; exact hy.2
  have hmaps : MapsTo r φ.source ψ.source := fun y hy => by rw [hφsrc] at hy; exact hy.2.2
  refine ⟨φ, ψ, hφ, hψ, hxφ, hφV, hψV, hmaps, ?_⟩
  have hsm := h.smooth φ ψ hφ hψ φ.source φ.isOpen_source (fun y hy => ⟨hφV hy, hy⟩) hmaps
  rw [φ.image_source] at hsm
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  exact ⟨hsm.mapsTo, R, hR, hsm.comp_isScSmooth R hR⟩

/-- B's existential reading gives the project's Definition 2.14 on an open `V`. -/
theorem isScSmoothOn_of_B {r : X → X} {V : Set X} (hV : IsOpen V) (h : IsScSmoothOnB P r V) :
    P.IsScSmoothOn P r V := by
  -- the chart representatives, in the project's form
  have hrep : ∀ x ∈ V, ∃ φ ψ : MChart X, P.IsChart φ ∧ P.IsChart ψ ∧ x ∈ φ.source ∧
      φ.source ⊆ V ∧ MapsTo r φ.source ψ.source ∧
      IsScSmoothRetractMap φ.model.E φ.model.C (φ '' φ.source) ψ.model.E ψ.model.C ψ.model.O
        (ψ ∘ r ∘ φ.symm) := by
    intro x hx
    obtain ⟨φ, ψ, hφ, hψ, hxφ, hφV, -, hmaps, hmapsO, R, hR, hsm⟩ := h x hx
    refine ⟨φ, ψ, hφ, hψ, hxφ, hφV, hmaps, ?_⟩
    rw [φ.image_source]
    exact (isScSmoothRetractMap_iff_exists φ.model.isScRetract).2 ⟨hmapsO, R, hR, hsm⟩
  -- continuity of `r` on `V`
  have hcont : ContinuousOn r V := by
    intro x hx
    obtain ⟨φ, ψ, hφ, hψ, hxφ, hφV, hmaps, hsm⟩ := hrep x hx
    rw [φ.image_source] at hsm
    have h1 : ContinuousOn (ψ ∘ r ∘ φ.symm) φ.model.O := hsm.continuousOn φ.model.isScRetract
    have h2 : ContinuousOn (ψ.symm ∘ (ψ ∘ r ∘ φ.symm) ∘ φ) φ.source :=
      ψ.continuousOn_invFun.comp (h1.comp φ.continuousOn_toFun fun y hy => φ.mapsTo_model y hy)
        fun y hy => hsm.mapsTo (φ.mapsTo_model y hy)
    have h3 : ContinuousOn r φ.source := h2.congr fun y hy => by
      simp only [Function.comp_apply, φ.symm_apply_apply hy, ψ.symm_apply_apply (hmaps hy)]
    exact (h3.continuousAt (φ.isOpen_source.mem_nhds hxφ)).continuousWithinAt
  refine MPolyfold.IsScSmoothOn.of_exists_charts hV hcont fun x hx => ?_
  obtain ⟨φ, ψ, hφ, hψ, hxφ, hφV, hmaps, hsm⟩ := hrep x hx
  exact ⟨φ, ψ, φ.source, hφ, hψ, φ.isOpen_source, hxφ, fun y hy => ⟨hφV hy, hy⟩, hmaps, hsm⟩

/-- The project's Definition 2.20 is B's. -/
theorem isSubMPolyfold_iff (A : Set X) : P.IsSubMPolyfold A ↔ IsSubMPolyfoldB P A := by
  constructor
  · intro h a ha
    obtain ⟨V, hV, haV, r, hrV, hsm, hidem, himg⟩ := h a ha
    exact ⟨V, hV, haV, r, hrV, isScSmoothOnB_of P hV hrV hsm, hidem, himg⟩
  · intro h a ha
    obtain ⟨V, hV, haV, r, hrV, hsm, hidem, himg⟩ := h a ha
    exact ⟨V, hV, haV, r, hrV, isScSmoothOn_of_B P hV hsm, hidem, himg⟩

/-- In B's reading, `id` is an sc-smooth retraction of `X` (every chart `φ`, `φ ∘ φ⁻¹ = id` on
`O`). -/
theorem isSubMPolyfoldB_univ : IsSubMPolyfoldB P univ := by
  intro a _
  refine ⟨univ, isOpen_univ, mem_univ a, id, mapsTo_id _, ?_, fun _ _ => rfl, by simp⟩
  intro x _
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  refine ⟨φ, φ, hφ, hφ, hxφ, subset_univ _, subset_univ _, mapsTo_id _, ?_, ?_⟩
  · intro z hz
    change φ (φ.symm z) ∈ φ.model.O
    rw [φ.apply_symm_apply hz]; exact hz
  · obtain ⟨R, hR⟩ := φ.model.isScRetract
    refine ⟨R, hR, R.isScSmooth.congr R.isScDomain fun y hy => ?_⟩
    have : R y ∈ φ.model.O := hR ▸ R.apply_mem_retract hy
    change R y = φ (φ.symm (R y))
    rw [φ.apply_symm_apply this]

end Glue

/-- `A → B`: B (the definitions agree) is proved outright; A is not used. -/
theorem A_to_B : A → B := by
  intro _ X _ _ _ P S
  exact isSubMPolyfold_iff P S

/-- `B → A`: B at `A = univ`, with `id` an sc-smooth retraction in B's reading. -/
theorem B_to_A : B → A := by
  intro hB X _ _ _ P
  exact (hB X P univ).2 (isSubMPolyfoldB_univ P)

#rt_check RoundTrip.V2_23.A_to_B [Polyfold.MPolyfold.isSubMPolyfold_univ]
#rt_check RoundTrip.V2_23.B_to_A [Polyfold.MPolyfold.isSubMPolyfold_univ]
#rt_overlap RoundTrip.V2_23.B_to_A [Polyfold.MPolyfold.isSubMPolyfold_univ]

end RoundTrip.V2_23
