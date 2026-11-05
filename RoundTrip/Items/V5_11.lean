import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_11

/-! **Refresh 2026-11-02** (HEAD after the germ reading of Definition 3.11 and the notions built
on it).
theorem_5_6 and B now both use the germ-reading IsScFredholmSection (theorem_5_6 is theorem_3_12
applied to the germ at the zero); the conclusions are unchanged and both repackaging proofs still
check. Result unchanged: equivalent.
-/

namespace RoundTrip.V5_11
open Polyfold

/-- The project's statement (Theorem 5.6), universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.theorem_5_6.{0, 0}

theorem A_holds : A := @Polyfold.theorem_5_6.{0, 0}

/-- `A ⇒ B`: the compact `K ⊆ X_i` of A whose image is the closure is the set of points of `X_i`
lying in the closure (the inclusion `X_i → X` is injective). -/
theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f hf x hx
  obtain ⟨U, h1, h2, h3, h4⟩ := hA hf hx
  refine ⟨U, h1, h2, h3, fun i => ?_⟩
  obtain ⟨K, hK, hKe⟩ := h4 i
  have hsub : closure {y | y ∈ U i ∧ IsZeroAt P f y} ⊆ PX.levelSet i := by
    rw [← hKe]
    rintro _ ⟨k, -, rfl⟩
    exact PX.levelVal_mem k
  refine ⟨hsub, ?_⟩
  have hK' : @IsCompact (PX.levelSet i) (PX.levelTopology i) K := hK
  have heq : {p : PX.levelSet i | p.1 ∈ closure {y | y ∈ U i ∧ IsZeroAt P f y}} = K := by
    ext p
    change p.1 ∈ closure {y | y ∈ U i ∧ IsZeroAt P f y} ↔ p ∈ K
    rw [← hKe]
    constructor
    · rintro ⟨k, hk, hkp⟩
      have : k = p := MPolyfold.level_ext hkp
      exact this ▸ hk
    · intro hp
      exact ⟨p, hp, rfl⟩
  rw [heq]
  exact hK'

/-- `B ⇒ A`: take `K = {p ∈ X_i | p ∈ closure}`; its image is the closure since the closure lies
in `X_i`. -/
theorem B_to_A : B → A := by
  intro hB X _ _ _ PX Y _ _ _ P _ _ Bd f hf x hx
  obtain ⟨U, h1, h2, h3, h4⟩ := hB PX P Bd f hf x hx
  refine ⟨U, h1, h2, h3, fun i => ⟨{p : PX.Level i |
    PX.levelVal i p ∈ closure {y | y ∈ U i ∧ IsZeroAt P f y}}, (h4 i).2, ?_⟩⟩
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hy
    exact ⟨PX.levelMk i y ((h4 i).1 hy), hy, rfl⟩

#rt_check RoundTrip.V5_11.A_to_B [Polyfold.theorem_5_6]
#rt_check RoundTrip.V5_11.B_to_A [Polyfold.theorem_5_6]
#rt_overlap RoundTrip.V5_11.B_to_A [Polyfold.theorem_5_6]

end RoundTrip.V5_11
