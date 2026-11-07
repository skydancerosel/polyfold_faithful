import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_15

/-! Round trip for V7_15 (Proposition 7.4, p. 230: the isotropy groups are finite).

`A` is the conjunction of the types of `EpGroupoid.proposition_7_4` (an instance
`Finite (X.Isotropy x)`, universe at `0`) and `MPolyfold.finite_isotropy_of_isLocalScDiffeo`
(an abstract form for maps `s, t : Y → X` between M-polyfolds, two universes, both at `0`).

* `A → B`: `X.Isotropy x` (a structure: a morphism with `s = x`, `t = x`) maps onto `B`'s set
  `{g | s g = x ∧ t g = x}` by `val`, so the set is finite.
* `B → A`: `proposition_7_4` from `B` (`val` is injective).  `finite_isotropy_of_isLocalScDiffeo`
  speaks of arbitrary `s, t` (with `t` a local sc-diffeomorphism and a properness hypothesis),
  not of an ep-groupoid, so it is not a consequence of `B`; it is re-proved outright (compact
  discrete fibres are finite). -/

namespace RoundTrip.V7_15
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.proposition_7_4.{0}) ∧
  (type_of% @Polyfold.MPolyfold.finite_isotropy_of_isLocalScDiffeo.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.proposition_7_4.{0},
    @Polyfold.MPolyfold.finite_isotropy_of_isLocalScDiffeo.{0, 0}⟩

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X x
  have := hA.1 X x
  exact (Set.finite_range fun g : X.Isotropy x => g.val).subset fun g hg =>
    ⟨⟨g, hg.1, hg.2⟩, rfl⟩

/-- The abstract finiteness lemma, re-proved outright: a fibre of a proper locally injective map
is compact and discrete. -/
theorem finite_setOf_mem' {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y] {s t : M → Y}
    (ht : IsLocallyInjective t) {K : Set Y} (hK : IsProperMap ((s ⁻¹' K).domRestrict t)) (y : Y) :
    {ψ | s ψ ∈ K ∧ t ψ = y}.Finite := by
  have hfin : (((s ⁻¹' K).domRestrict t) ⁻¹' {y}).Finite :=
    (hK.isCompact_preimage isCompact_singleton).finite
      (IsLocallyInjective.isDiscrete_preimage_singleton
        (ht.comp_right continuous_subtype_val Subtype.val_injective) y)
  refine (hfin.image Subtype.val).subset ?_
  rintro ψ ⟨hψK, hψx⟩
  exact ⟨⟨ψ, hψK⟩, hψx, rfl⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X x
    have := (hB Obj Mor X x).to_subtype
    exact Finite.of_injective (β := {g : Mor | X.src g = x ∧ X.tgt g = x})
      (fun g => ⟨g.val, g.src_val, g.tgt_val⟩) fun g h hgh =>
        GroupoidStr.Isotropy.ext (congrArg Subtype.val hgh)
  · -- outright
    intro X _ _ _ P Y _ _ _ Q s t ht x hx
    obtain ⟨V, -, hxV, hV⟩ := hx
    exact (finite_setOf_mem' ht.isLocallyInjective hV x).subset fun φ hφ =>
      ⟨hφ.1 ▸ subset_closure hxV, hφ.2⟩

#rt_check RoundTrip.V7_15.A_to_B [Polyfold.EpGroupoid.proposition_7_4,
  Polyfold.MPolyfold.finite_isotropy_of_isLocalScDiffeo]
#rt_check RoundTrip.V7_15.B_to_A [Polyfold.EpGroupoid.proposition_7_4,
  Polyfold.MPolyfold.finite_isotropy_of_isLocalScDiffeo]
#rt_overlap RoundTrip.V7_15.B_to_A [Polyfold.EpGroupoid.proposition_7_4,
  Polyfold.MPolyfold.finite_isotropy_of_isLocalScDiffeo]

end RoundTrip.V7_15
