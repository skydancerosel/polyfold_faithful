import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_12

/-!
Round trip for V4_12 (Lemma 4.7: the retract of an sc⁺-retraction consists of smooth points, and
`T_oO = Dr(o)E` is finite-dimensional).  `A` is the conjunction of the types of
`Polyfold.lemma_4_7_i`, `Polyfold.lemma_4_7_ii` and `Polyfold.lemma_4_7_ii_tangentSpace` (no
universe parameters).

Glue: `O ⊆ E_∞` is B's pointwise "lifts to every level" (`ScBanach.mem_smooth_iff`); A's
tangent-space clause is stated for SOME lift `o₁` of `o`, B's for every level-1 point `o₁` over
`O` — the same, since `ι₁` is injective; `↑(LinearMap.range L) = Set.range L`
(`LinearMap.coe_range`).  Conversely B's (i) produces the smooth lift `o₁` that A's
`lemma_4_7_ii_tangentSpace` asks for (`smoothLvl 1` is the preimage of `E_∞`).
-/

namespace RoundTrip.V4_12
open Polyfold

def A : Prop :=
  type_of% @Polyfold.lemma_4_7_i ∧ type_of% @Polyfold.lemma_4_7_ii ∧
    type_of% @Polyfold.lemma_4_7_ii_tangentSpace

theorem A_holds : A := ⟨@Polyfold.lemma_4_7_i, @Polyfold.lemma_4_7_ii,
  @Polyfold.lemma_4_7_ii_tangentSpace⟩

theorem A_to_B : A → B := by
  rintro ⟨hA1, hA2, hA3⟩ E C r hr
  refine ⟨fun o ho => E.mem_smooth_iff.1 (hA1 hr ho), fun o₁ ho₁ => ⟨?_, hA2 hr ho₁⟩⟩
  obtain ⟨o₁', h1, -, h3, -⟩ := hA3 hr ho₁
  have : o₁' = o₁ := E.toBase_injective 1 h1
  subst this
  rw [h3, LinearMap.coe_range]
  rfl

theorem B_to_A : B → A := by
  intro hB
  have hi : ∀ {E : ScBanach} {C : Set (E.lvl 0)} {R : ScRetraction E C}, R.IsScPlus →
      R.retract ⊆ ↑E.smooth := fun {E C R} hR o ho =>
    E.mem_smooth_iff.2 ((hB E C R hR).1 o ho)
  refine ⟨@hi, fun {E C R} hR {o} ho => ((hB E C R hR).2 o ho).2, fun {E C R} hR {o} ho => ?_⟩
  obtain ⟨o₁, ho₁⟩ := (hB E C R hR).1 o ho 1
  have ho₁' : E.toBase 1 o₁ ∈ R.retract := ho₁ ▸ ho
  obtain ⟨h1, h2⟩ := (hB E C R hR).2 o₁ ho₁'
  refine ⟨o₁, ho₁, ?_, ?_, h2⟩
  · change E.toBase 1 o₁ ∈ (E.smooth : Set (E.lvl 0))
    exact hi hR ho₁'
  · rw [h1, LinearMap.coe_range]
    rfl

#rt_check RoundTrip.V4_12.A_to_B [Polyfold.lemma_4_7_i, Polyfold.lemma_4_7_ii, Polyfold.lemma_4_7_ii_tangentSpace]
#rt_check RoundTrip.V4_12.B_to_A [Polyfold.lemma_4_7_i, Polyfold.lemma_4_7_ii, Polyfold.lemma_4_7_ii_tangentSpace]
#rt_overlap RoundTrip.V4_12.B_to_A [Polyfold.lemma_4_7_i, Polyfold.lemma_4_7_ii, Polyfold.lemma_4_7_ii_tangentSpace]

end RoundTrip.V4_12
