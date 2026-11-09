import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_15

/-! Round trip for V8_15 (Definition 8.1.13 = 2017 Definition 8.1: natural transformations and
natural equivalence).

The listed declarations `Polyfold.EpNatTrans` (a structure) and
`Polyfold.EpFunctor.NaturallyEquivalent` (`Nonempty (EpNatTrans F G)`) are both definitions, so
`A = True`; the content of the audit is the comparison of the project's definitions with B's
notions, which is B itself, proved outright here (`B_holds`).

* (a) the fields of `EpNatTrans` are B's three conditions; B's naturality, quantified over
  `h, x, x'` with `s h = x`, `t h = x'`, is the project's `naturality h` after substitution.
* (b) a map `τ` with B's conditions is the `app` of the structure built from them.
* (c) `Nonempty (EpNatTrans F G)` iff some `τ` satisfies B's conditions, by (a) and (b).

Universes: B is stated for `Type`; the project's notions are universe-polymorphic (`u = v = 0`
here).
-/

namespace RoundTrip.V8_15
open Polyfold

/-- Only definitions are listed: `A = True`. -/
def A : Prop := True

theorem A_holds : A := trivial

section Glue
variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {F G : EpFunctor X Y}

theorem proj_to_B (τ : EpNatTrans F G) : IsNatTransB F G τ.app := by
  refine ⟨τ.isScSmoothMap_app, fun x => ⟨τ.src_app x, τ.tgt_app x⟩, ?_⟩
  rintro h x x' rfl rfl
  exact τ.naturality h

/-- The project natural transformation with `app = τ`, built from B's conditions. -/
def ofB (τ : Obj → Mor') (hτ : IsNatTransB F G τ) : EpNatTrans F G where
  app := τ
  isScSmoothMap_app := hτ.1
  src_app x := (hτ.2.1 x).1
  tgt_app x := (hτ.2.1 x).2
  naturality h := hτ.2.2 h _ _ rfl rfl

theorem B_to_proj (τ : Obj → Mor') (hτ : IsNatTransB F G τ) :
    ∃ T : EpNatTrans F G, T.app = τ :=
  ⟨ofB τ hτ, rfl⟩

end Glue

theorem B_holds : B := by
  intro Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F G
  refine ⟨fun τ => proj_to_B τ, fun τ hτ => B_to_proj τ hτ, ⟨?_, ?_⟩⟩
  · rintro ⟨τ⟩
    exact ⟨τ.app, proj_to_B τ⟩
  · rintro ⟨τ, hτ⟩
    exact ⟨ofB τ hτ⟩

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V8_15.A_to_B []
#rt_check RoundTrip.V8_15.B_to_A []
#rt_overlap RoundTrip.V8_15.B_to_A []
#rt_check RoundTrip.V8_15.B_holds []

end RoundTrip.V8_15
