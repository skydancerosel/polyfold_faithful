import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_76

set_option maxSynthPendingDepth 3

/-! Round trip for V19_76 (2021 Proposition 19.7.14, p. 914: `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` is a
surjective local homeomorphism).

`A` is the conjunction of the types of `proposition_19_7_14` (main conjunct) and of the two
point-set lemmas `Chapter19.isLocalHomeomorph_fibredFst`, `isLocalHomeomorph_fibredSnd`
(projections of a fibred product along a local homeomorphism), all at universe `0`.

* `A_to_B`: `B`'s topology on `MT` (induced by `toFib`) is by definition the project's
  `topologicalSpaceMHat`; the two clauses are `proposition_19_7_14`'s, swapped.
* `B_to_A`: `proposition_19_7_14` is `B` (swapped).  The two point-set lemmas are general facts
  about fibred products of topological spaces, unrelated to `B`; they are re-proved outright
  (the project's proofs, copied; Mathlib only). -/

namespace RoundTrip.V19_76
open Polyfold GroupoidalCategory

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_14.{0}) ∧
  (type_of% @Polyfold.Chapter19.isLocalHomeomorph_fibredFst.{0, 0, 0}) ∧
  (type_of% @Polyfold.Chapter19.isLocalHomeomorph_fibredSnd.{0, 0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_14.{0},
    @Polyfold.Chapter19.isLocalHomeomorph_fibredFst.{0, 0, 0},
    @Polyfold.Chapter19.isLocalHomeomorph_fibredSnd.{0, 0, 0}⟩

theorem main_A_to_B :
    (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_14.{0}) →
      B := by
  intro h A B P hP Bh x y
  exact ⟨(h Bh hP x y).2, (h Bh hP x y).1⟩

theorem A_to_B : A → B := fun h => main_A_to_B h.1

theorem main_B_to_A : B →
    (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_14.{0}) := by
  intro hB A B P Bh hP x y
  exact ⟨(hB A B P hP Bh x y).2, (hB A B P hP Bh x y).1⟩

/-! ### The point-set lemmas, re-proved outright (the project's proofs, copied) -/

section FibredProduct

open Set Function Topology

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem fibredFst' {s : X → Z} {τ : Y → Z} (hs : Continuous s)
    (hτ : IsLocalHomeomorph τ) :
    IsLocalHomeomorph fun p : {p : X × Y // s p.1 = τ p.2} => p.1.1 := by
  classical
  refine IsLocalHomeomorph.mk _ fun p => ?_
  obtain ⟨e, hpe, he⟩ := hτ p.1.2
  have hτe : ∀ y, τ y = e y := fun y => congrFun he y
  have hmem : ∀ x, s x ∈ e.target → s x = τ (e.symm (s x)) := fun x hx => by
    rw [hτe, e.right_inv hx]
  let inv : X → {p : X × Y // s p.1 = τ p.2} := fun x =>
    if hx : s x ∈ e.target then ⟨(x, e.symm (s x)), hmem x hx⟩ else p
  have hinv : ∀ x (hx : s x ∈ e.target), inv x = ⟨(x, e.symm (s x)), hmem x hx⟩ :=
    fun x hx => dif_pos hx
  have hsrc : ∀ q : {p : X × Y // s p.1 = τ p.2}, q.1.2 ∈ e.source → s q.1.1 ∈ e.target :=
    fun q hq => by rw [q.2, hτe]; exact e.map_source hq
  refine ⟨{ toFun := fun q => q.1.1
            invFun := inv
            source := {q | q.1.2 ∈ e.source}
            target := s ⁻¹' e.target
            map_source' := fun q hq => hsrc q hq
            map_target' := fun x hx => by
              change (inv x).1.2 ∈ e.source
              rw [hinv x hx]
              exact e.map_target hx
            left_inv' := fun q hq => by
              change inv q.1.1 = q
              rw [hinv _ (hsrc q hq)]
              refine Subtype.ext (Prod.ext rfl ?_)
              change e.symm (s q.1.1) = q.1.2
              rw [q.2, hτe, e.left_inv hq]
            right_inv' := fun x hx => by
              rw [hinv x hx]
            open_source := e.open_source.preimage (continuous_snd.comp continuous_subtype_val)
            open_target := e.open_target.preimage hs
            continuousOn_toFun := (continuous_fst.comp continuous_subtype_val).continuousOn
            continuousOn_invFun := by
              rw [continuousOn_iff_continuous_domRestrict]
              exact Continuous.congr (Continuous.subtype_mk (continuous_subtype_val.prodMk
                (e.continuousOn_symm.comp_continuous (hs.comp continuous_subtype_val)
                  fun x => x.2)) fun x => hmem x.1 x.2) fun x => (hinv x.1 x.2).symm },
    hpe, fun _ _ => rfl⟩

theorem fibredSnd' {s : X → Z} {τ : Y → Z} (hs : IsLocalHomeomorph s)
    (hτ : Continuous τ) :
    IsLocalHomeomorph fun p : {p : X × Y // s p.1 = τ p.2} => p.1.2 := by
  let e : {p : X × Y // s p.1 = τ p.2} ≃ₜ {p : Y × X // τ p.1 = s p.2} :=
    { toFun := fun p => ⟨p.1.swap, p.2.symm⟩
      invFun := fun p => ⟨p.1.swap, p.2.symm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _ }
  exact (fibredFst' hτ hs).comp e.isLocalHomeomorph

end FibredProduct

theorem B_to_A : B → A := fun hB =>
  ⟨main_B_to_A hB, @fibredFst', @fibredSnd'⟩

#rt_check RoundTrip.V19_76.A_to_B [Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_14,
  Polyfold.Chapter19.isLocalHomeomorph_fibredFst, Polyfold.Chapter19.isLocalHomeomorph_fibredSnd]
#rt_check RoundTrip.V19_76.B_to_A [Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_14,
  Polyfold.Chapter19.isLocalHomeomorph_fibredFst, Polyfold.Chapter19.isLocalHomeomorph_fibredSnd]
#rt_check RoundTrip.V19_76.main_A_to_B [Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_14,
  Polyfold.Chapter19.isLocalHomeomorph_fibredFst, Polyfold.Chapter19.isLocalHomeomorph_fibredSnd]
#rt_check RoundTrip.V19_76.main_B_to_A [Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_14,
  Polyfold.Chapter19.isLocalHomeomorph_fibredFst, Polyfold.Chapter19.isLocalHomeomorph_fibredSnd]
#rt_overlap RoundTrip.V19_76.B_to_A [Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_14,
  Polyfold.Chapter19.isLocalHomeomorph_fibredFst, Polyfold.Chapter19.isLocalHomeomorph_fibredSnd]

end RoundTrip.V19_76
