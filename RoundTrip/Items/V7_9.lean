import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_9

/-! Round trip for V7_9 (Definition 7.7, p. 228: the category `𝓔𝓟`).

The item lists definitions (`GroupoidFunctor`, `GroupoidFunctor.id`, `.comp`, `.toFunctor`,
`.orbitMap`, `EpFunctor`, `EpFunctor.id`, `.comp`, `EP`) and two theorems,
`GroupoidFunctor.mor_inv` (a functor commutes with the inverse) and `EpFunctor.ext`.  `A` is the
conjunction of the types of these two theorems, universes instantiated at `0` (`B` lives in
`Type`).  The real comparison is between the project's definitions and `B`'s notions; `B` (a)–(d)
states that comparison, and `A_to_B` proves it (using `EpFunctor.ext` from `A` for the category
laws).

* `A → B`: (a), (b): the fields of `EpFunctor` are exactly `IsFunctorB` plus sc-smoothness on
  objects and morphisms; (c): `isScSmoothMap_id`, `IsScSmoothMap.comp`; (d): `rfl` for the maps,
  and the unit and associativity laws by `EpFunctor.ext` (the hypothesis).
* `B → A`: both conjuncts of `A` are re-proved outright (groupoid algebra; structure eta), `B`
  is not used: `B` is about `EpFunctor`s between ep-groupoids and gives no uniqueness of an
  `EpFunctor` with given maps, and `mor_inv` is about functors between arbitrary groupoids. -/

namespace RoundTrip.V7_9
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GroupoidFunctor.mor_inv.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.ext.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidFunctor.mor_inv.{0, 0}, @Polyfold.EpFunctor.ext.{0, 0}⟩

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA Obj Mor Obj' Mor' Obj'' Mor'' Obj''' Mor''' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ X Y Z W
  refine ⟨fun F => ⟨⟨F.src_mor, F.tgt_mor, F.mor_comp, F.mor_unit⟩, F.isScSmoothMap_obj,
      F.isScSmoothMap_mor⟩, ?_, ?_, ?_, ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩,
    fun F => ⟨hA.2 rfl rfl, hA.2 rfl rfl⟩, fun _ _ _ => hA.2 rfl rfl⟩
  · rintro f₀ f₁ ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
    exact ⟨⟨⟨f₀, f₁, h1, h2, h3, h4⟩, h5, h6⟩, rfl, rfl⟩
  · exact ⟨⟨fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩,
      MPolyfold.isScSmoothMap_id, MPolyfold.isScSmoothMap_id⟩
  · rintro f₀ f₁ g₀ g₁ ⟨⟨f1, f2, f3, f4⟩, f5, f6⟩ ⟨⟨g1, g2, g3, g4⟩, g5, g6⟩
    refine ⟨⟨fun φ => ?_, fun φ => ?_, fun φ ψ h => ?_, fun x => ?_⟩, g5.comp f5, g6.comp f6⟩
    · simp only [Function.comp_apply, g1, f1]
    · simp only [Function.comp_apply, g2, f2]
    · simp only [Function.comp_apply, f3 φ ψ h, g3 _ _ (by rw [f1, f2, h])]
    · simp only [Function.comp_apply, f4, g4]

/-! ### `B → A` (outright) -/

theorem mor_inv' {Obj Mor Obj' Mor' : Type} {G : GroupoidStr Obj Mor} {H : GroupoidStr Obj' Mor'}
    (F : GroupoidFunctor G H) (φ : Mor) : F.mor (G.inv φ) = H.inv (F.mor φ) := by
  refine GroupoidStr.eq_inv_of_comp_eq_unit ?_ ?_
  · rw [F.src_mor, F.tgt_mor, G.src_inv]
  · rw [← F.mor_comp _ _ (G.src_inv φ), G.inv_comp, F.mor_unit, F.src_mor]

theorem B_to_A : B → A := by
  intro _
  refine ⟨@mor_inv', ?_⟩
  intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F F' h₁ h₂
  obtain ⟨⟨o, m, a, b, c, d⟩, e, f⟩ := F
  obtain ⟨⟨o', m', a', b', c', d'⟩, e', f'⟩ := F'
  cases h₁
  cases h₂
  rfl

#rt_check RoundTrip.V7_9.A_to_B [Polyfold.GroupoidFunctor.mor_inv, Polyfold.EpFunctor.ext]
#rt_check RoundTrip.V7_9.B_to_A [Polyfold.GroupoidFunctor.mor_inv, Polyfold.EpFunctor.ext]
#rt_overlap RoundTrip.V7_9.B_to_A [Polyfold.GroupoidFunctor.mor_inv, Polyfold.EpFunctor.ext]

end RoundTrip.V7_9
