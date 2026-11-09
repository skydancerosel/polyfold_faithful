import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_18

/-! Round trip for V3_18 (Lemma 3.16, the extension `s̃ = s ∘ r`).

`A` is the conjunction of the types of `Polyfold.lemma_3_1_19` (no universe parameters) and
`Polyfold.StrongBundle.IsScFredholmGerm.sectionAdd` (universes `u v` of `X`, `Y`, instantiated at
`0`).

Refresh 2026-11-02: `IsScFredholmGerm.sectionAdd` now states the germ reading of Definition 3.11
(`IsFillingGerm`, `IsScPlusGerm`); `lemma_3_1_19` and B are unchanged, and the proof below (which uses
only `lemma_3_1_19`) still checks.

* `A → B` is proved.  `B`'s (1) and (2) are `lemma_3_1_19` (from the hypothesis) applied to the
  principal part `ι ∘ ŝ : E₀ → F₀` of the sc⁺-section (its section condition `(x, ι ŝ(x)) ∈ K` is
  `IsScPlusSection.mem`), plus injectivity of `ι : F₁ → F₀`.  `B`'s regularity clause
  (`s̃` is an sc⁺-section of `U ◁ F → U`) is NOT in the statement of any theorem of `A`: in the
  project it appears only inside the proof of `IsScFredholmGerm.sectionAdd` (`hlift`).  It is
  proved here directly from the project's sc-calculus (Definition 2.7 for one retraction,
  `baseRetraction`, `IsScSmooth.snd`, `scPair`), not from `A`.
* `B → A` is not proved: `A`'s `lemma_3_1_19` is about an ARBITRARY map `s : E₀ → F₀` satisfying
  only the section condition (no regularity, values in `F₀`), while `B` only speaks about
  sc⁺-sections (values in `F₁`, sc-smooth into `K[1]`); and `IsScFredholmGerm.sectionAdd` is the
  germ part of Theorem 3.15 (fillers via Lemma 3.17, sc-Fredholm germs over an M-polyfold), which
  `B` does not mention.
-/

namespace RoundTrip.V3_18
open Polyfold Set

/-- The project's statement (universes of `IsScFredholmGerm.sectionAdd` at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.lemma_3_1_19) ∧
    (type_of% @Polyfold.StrongBundle.IsScFredholmGerm.sectionAdd.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.lemma_3_1_19, @Polyfold.StrongBundle.IsScFredholmGerm.sectionAdd.{0, 0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h16, -⟩ E F C U R hU hR s hs
  intro r st
  -- the principal part `ι ∘ ŝ` is a section of `K → O`
  have hsK : ∀ x ∈ StrongRetr.r R '' U,
      (x, F.toBase 1 (s x).2) ∈ R '' (U ×ˢ (univ : Set (F 0))) := by
    intro x hx
    have := hs.mem hx
    rwa [hs.fst_eq x hx] at this
  obtain ⟨h1, h2⟩ := h16 hR (s := fun x => F.toBase 1 (s x).2) hsK
  refine ⟨?_, ?_, ?_⟩
  · -- regularity of `s̃` (not in `A`; from the sc-calculus)
    have hUd := hU.isScDomain
    have hlift : IsScSmooth (F := F.shift) U fun u => (s (r u)).2 :=
      ((hs.isScSmooth.comp_isScSmooth (hR.baseRetraction hU) rfl).snd hUd).congr hUd
        fun _ _ => rfl
    refine ⟨fun x _ => rfl, ?_⟩
    refine (isScSmoothRetractMap_iff_exists hU.isScRetract).2
      ⟨fun x hx => ⟨hx, mem_univ _⟩, ScRetraction.id hU, image_id U, ?_⟩
    exact ((isScSmooth_id hUd).scPair hUd hlift).congr hUd fun _ _ => rfl
  · -- (1) `s̃ = s` on `O`
    intro u hu
    have hsu := hs.fst_eq u hu
    have h1u : F.toBase 1 (s (r u)).2 = F.toBase 1 (s u).2 := h1 u hu
    refine Prod.ext hsu.symm ?_
    exact F.toBase_injective 1 h1u
  · -- (2) `R(r(u), s̃(u)) = s(r(u))`
    intro u hu
    have hru : r u ∈ r '' U := ⟨u, hu, rfl⟩
    have h2u := (h2 u hu).2
    change R (r u, F.toBase 1 (s (r u)).2) = ((s (r u)).1, F.toBase 1 (s (r u)).2)
    rw [hs.fst_eq (r u) hru]
    exact h2u

#rt_check RoundTrip.V3_18.A_to_B [Polyfold.lemma_3_1_19,
  Polyfold.StrongBundle.IsScFredholmGerm.sectionAdd]
#rt_overlap RoundTrip.V3_18.A_to_B [Polyfold.lemma_3_1_19,
  Polyfold.StrongBundle.IsScFredholmGerm.sectionAdd]

end RoundTrip.V3_18
