import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_17

/-! Round trip for V8_17 (Proposition 8.1.14 = 2017 Proposition 8.1: the tangent of a natural
transformation).

The item lists the definition `EpNatTrans.tangent` (vocabulary) and the theorem
`proposition_8_1`; `A` is its type, universes at `0` (B lives in `Type`): for every project
natural transformation `τ : Φ → Ψ` there is `Tτ : EpNatTrans Φ.tangent Ψ.tangent` with
`Tτ.app = Tτ` (Part I's tangent map of `τ.app`), and `Φ ≃ Ψ → TΦ ≃ TΨ`.

`B`: for every map `τ` that is a natural transformation in B's reading (`IsNatTransB`, V8_15),
there are sc-smooth functors `TΦ, TΨ : T(X, 𝐗) → T(Y, 𝐘)` with the tangent maps of `Φ`, `Ψ` as
object and morphism maps, and the tangent map of `τ` is a natural transformation between them in
B's reading of Definition 8.1.13 (stated on the data).

* `A ⇒ B`: package `τ` with B's conditions as a project `EpNatTrans` (`ofB`, as in V8_15), apply
  `A`; `TΦ := Φ.tangent`, `TΨ := Ψ.tangent` (the project's functors, whose object and morphism maps
  are the tangent maps by definition), and the fields of A's `Tτ` are B's conditions after
  rewriting `Tτ.app` (the tangent maps of `τ` with the two sc-smoothness proofs agree by proof
  irrelevance).
* `B ⇒ A`: apply `B` to `τ.app`; B's `TΦ`, `TΨ` equal `Φ.tangent`, `Ψ.tangent` (`EpFunctor.ext`),
  so B's conditions on the tangent map of `τ` build the project `Tτ`; the second conjunct is the
  same construction applied to a witness of `Φ ≃ Ψ`.
-/

namespace RoundTrip.V8_17
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop := type_of% @Polyfold.proposition_8_1.{0, 0}

theorem A_holds : A := @Polyfold.proposition_8_1.{0, 0}

section Glue
variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- The project natural transformation with `app = τ`, built from B's conditions. -/
def ofB {F G : EpFunctor X Y} (τ : Obj → Mor') (hτ : IsNatTransB F G τ) : EpNatTrans F G where
  app := τ
  isScSmoothMap_app := hτ.1
  src_app x := (hτ.2.1 x).1
  tgt_app x := (hτ.2.1 x).2
  naturality h := hτ.2.2 h _ _ rfl rfl

theorem proj_to_B {F G : EpFunctor X Y} (τ : EpNatTrans F G) : IsNatTransB F G τ.app := by
  refine ⟨τ.isScSmoothMap_app, fun x => ⟨τ.src_app x, τ.tgt_app x⟩, ?_⟩
  rintro h x x' rfl rfl
  exact τ.naturality h

/-- B's conclusion for `τ` gives a project natural transformation `TΦ → TΨ` with `app` the tangent
map of `τ`. -/
theorem tangent_of_B {Φ Ψ : EpFunctor X Y} (τ : EpNatTrans Φ Ψ)
    (h : ∃ TΦ TΨ : EpFunctor X.tangentEpGroupoid Y.tangentEpGroupoid,
      TΦ.obj = MPolyfold.tangentMap Φ.isScSmoothMap_obj ∧
      TΦ.mor = MPolyfold.tangentMap Φ.isScSmoothMap_mor ∧
      TΨ.obj = MPolyfold.tangentMap Ψ.isScSmoothMap_obj ∧
      TΨ.mor = MPolyfold.tangentMap Ψ.isScSmoothMap_mor ∧
      IsNatTransDataB X.tangentEpGroupoid Y.tangentEpGroupoid TΦ.obj TΨ.obj TΦ.mor TΨ.mor
        (MPolyfold.tangentMap (proj_to_B τ).1)) :
    ∃ Tτ : EpNatTrans Φ.tangent Ψ.tangent, Tτ.app = MPolyfold.tangentMap τ.isScSmoothMap_app := by
  obtain ⟨TΦ, TΨ, h1, h2, h3, h4, hn⟩ := h
  have e1 : TΦ = Φ.tangent := EpFunctor.ext h1 h2
  have e2 : TΨ = Ψ.tangent := EpFunctor.ext h3 h4
  subst e1 e2
  exact ⟨⟨_, hn.1, fun a => (hn.2.1 a).1, fun a => (hn.2.1 a).2,
    fun v => hn.2.2 v _ _ rfl rfl⟩, rfl⟩

end Glue

theorem A_to_B : A → B := by
  intro hA Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y Φ Ψ τ hτ
  obtain ⟨Tτ, happ, -⟩ := hA (τ := ofB τ hτ)
  refine ⟨Φ.tangent, Ψ.tangent, rfl, rfl, rfl, rfl, ?_⟩
  have e : MPolyfold.tangentMap hτ.1 = Tτ.app := happ.symm
  rw [e]
  refine ⟨Tτ.isScSmoothMap_app, fun a => ⟨Tτ.src_app a, Tτ.tgt_app a⟩, ?_⟩
  rintro v a a' rfl rfl
  exact Tτ.naturality v

theorem B_to_A : B → A := by
  intro hB Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y Φ Ψ τ
  refine ⟨(tangent_of_B τ (hB Obj Mor Obj' Mor' X Y Φ Ψ τ.app (proj_to_B τ))).choose,
    (tangent_of_B τ (hB Obj Mor Obj' Mor' X Y Φ Ψ τ.app (proj_to_B τ))).choose_spec, ?_⟩
  rintro ⟨σ⟩
  exact ⟨(tangent_of_B σ (hB Obj Mor Obj' Mor' X Y Φ Ψ σ.app (proj_to_B σ))).choose⟩

#rt_check RoundTrip.V8_17.A_to_B [Polyfold.proposition_8_1]
#rt_check RoundTrip.V8_17.B_to_A [Polyfold.proposition_8_1]
#rt_overlap RoundTrip.V8_17.B_to_A [Polyfold.proposition_8_1]

end RoundTrip.V8_17
