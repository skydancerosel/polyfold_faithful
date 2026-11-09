import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_8

/-! Round trip for V9_8 (Definition 9.1.8, p. 405; 2017: Definition 9.3, p. 294: manifold- and
orbifold-type).

The listed declarations are two definitions (`EpGroupoid.IsOrbifoldType`,
`EpGroupoid.IsManifoldType`, vocabulary) and one theorem, the witness
`EpGroupoid.isManifoldType_indicator` (the indicator of a point of `ℝⁿ` in the trivial
ep-groupoid of `ℝⁿ` is of manifold type).  `A` is the type of that theorem (it has no universe
parameters).

* `B` says the project's two predicates are the text's notions, for every ep-groupoid in
  universe `0` and every `Θ : Obj → ℚ`.  This is proved outright (`B_holds`): `IsOrbifoldType`
  is literally `B`'s `IsZeroOneB`, and the project's "two morphisms with the same source and
  target in `supp Θ` are equal" is `B`'s "at most one morphism between two objects of
  `supp Θ`", with the quantifiers rearranged.
* So `A → B` holds without its hypothesis, and `B → A` uses `B` to rewrite `IsManifoldType`
  into `B`'s form, then checks the indicator (values `0`, `1`; the morphisms of the trivial
  ep-groupoid are units, `src = tgt` determines them). -/

namespace RoundTrip.V9_8
open Polyfold

/-- The project's statement (the witness; no universe parameters). -/
def A : Prop := type_of% @Polyfold.EpGroupoid.isManifoldType_indicator

theorem A_holds : A := @Polyfold.EpGroupoid.isManifoldType_indicator

/-- The project's definitions are `B`'s (proved outright, from the definitions). -/
theorem B_holds : B := by
  intro Obj Mor _ _ _ _ _ _ X Θ
  refine ⟨⟨fun h => ⟨h.1, fun x hx y hy φ ψ h1 h2 h3 h4 => ?_⟩, fun h => ⟨h.1, ?_⟩⟩,
    Iff.rfl⟩
  · subst h1 h2
    exact h.2 φ ψ hx hy h3.symm h4.symm
  · intro φ ψ hs ht h3 h4
    exact h.2 (X.src φ) hs (X.tgt φ) ht φ ψ rfl rfl h3.symm h4.symm

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := by
  intro hB n p
  rw [((hB _ _ (EpGroupoid.trivial (rnPolyfold n))
    (({p} : Set (Fin n → ℝ)).indicator 1)).1)]
  refine ⟨fun y => ?_, fun x _ y _ φ ψ h1 h2 h3 h4 => ?_⟩
  · by_cases hy : y = p
    · subst hy; simp
    · simp [hy]
  · -- in the trivial ep-groupoid the morphisms are the objects and `src = tgt = id`
    exact h1.trans h3.symm

#rt_check RoundTrip.V9_8.A_to_B [Polyfold.EpGroupoid.isManifoldType_indicator]
#rt_check RoundTrip.V9_8.B_to_A [Polyfold.EpGroupoid.isManifoldType_indicator]
#rt_overlap RoundTrip.V9_8.B_to_A [Polyfold.EpGroupoid.isManifoldType_indicator]

end RoundTrip.V9_8
