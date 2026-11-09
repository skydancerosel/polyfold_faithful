import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_42

/-! Round trip for V8_42 (Proposition 8.6.4 / 2017: Proposition 8.4: `#F⁻¹(x)` is constant on the
components of `|X|`; `x ↦ #F⁻¹(x)` is an sc-smooth functor `X → ℕ`).

The item lists the definitions `fiberCardOrbit`, `fiberCardFunctor`, `EpGroupoid.trivial`,
`discretePolyfold` (vocabulary) and five theorems.  `A` is the conjunction of the types of the
theorems, universes at `0`: `IsProperCovering.one_le_ncard_fiber`,
`IsProperCovering.eventually_ncard_fiber_eq`, `IsProperCovering.isLocallyConstant_ncard_fiber`,
`IsProperCovering.isLocallyConstant_fiberCardOrbit`, `IsProperCovering.proposition_8_6_4`.

* `A ⇒ B`: constancy on components is `proposition_8_6_4`; values `≥ 1` is `one_le_ncard_fiber`.
  For the functor we do **not** use the project's `fiberCardFunctor` (its smoothness field is the
  banned `isLocallyConstant_ncard_fiber`); we build the same functor from A's
  `isLocallyConstant_ncard_fiber` (continuity into discrete `ℕ`, then the non-item
  `isScSmoothMap_discrete_of_continuous`), with the morphism map `φ ↦ #F⁻¹(s φ)` and the non-item
  Lemma 8.6.3 (`ncard_fiber_eq_of_isomorphic`) for `t`.
* `B ⇒ A`: B's sc-smooth functor `E` has a continuous object map into discrete `ℕ`, so
  `x ↦ #F⁻¹(x) = E.obj x` is locally constant: this gives `isLocallyConstant_ncard_fiber`,
  `eventually_ncard_fiber_eq` and (through the quotient topology) `isLocallyConstant_fiberCardOrbit`;
  `proposition_8_6_4` is B's first conjunct, `one_le_ncard_fiber` its third.
-/

namespace RoundTrip.V8_42
open Polyfold Set Function Topology

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.IsProperCovering.one_le_ncard_fiber.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.eventually_ncard_fiber_eq.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.isLocallyConstant_ncard_fiber.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.isLocallyConstant_fiberCardOrbit.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.proposition_8_6_4.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.IsProperCovering.one_le_ncard_fiber.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.eventually_ncard_fiber_eq.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.isLocallyConstant_ncard_fiber.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.isLocallyConstant_fiberCardOrbit.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.proposition_8_6_4.{0, 0}⟩

section
variable {ObjY MorY ObjX MorX : Type}
  [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}

/-- The functor `x ↦ #F⁻¹(x)` built from a proof that this map is locally constant (the
project's `fiberCardFunctor`, with its smoothness proof supplied by the caller). -/
noncomputable def cardFunctor (F : EpFunctor Y X) (hF : F.IsProperCovering)
    (hlc : IsLocallyConstant fun x => (F.obj ⁻¹' {x}).ncard) :
    EpFunctor X (EpGroupoid.trivial (discretePolyfold ℕ)) where
  obj x := (F.obj ⁻¹' {x}).ncard
  mor φ := (F.obj ⁻¹' {X.src φ}).ncard
  src_mor _ := rfl
  tgt_mor φ := hF.ncard_fiber_eq_of_isomorphic ⟨φ, rfl, rfl⟩
  mor_comp φ ψ h := by
    change (F.obj ⁻¹' {X.src (X.comp φ ψ)}).ncard = (F.obj ⁻¹' {X.src φ}).ncard
    rw [X.src_comp _ _ h, h]
    exact hF.ncard_fiber_eq_of_isomorphic ⟨ψ, rfl, rfl⟩
  mor_unit x := by
    change (F.obj ⁻¹' {X.src (X.unit x)}).ncard = (F.obj ⁻¹' {x}).ncard
    rw [X.src_unit]
  isScSmoothMap_obj := isScSmoothMap_discrete_of_continuous hlc.continuous
  isScSmoothMap_mor := isScSmoothMap_discrete_of_continuous (hlc.continuous.comp X.continuous_src)

/-- From B's functor: `x ↦ #F⁻¹(x)` is locally constant. -/
theorem isLocallyConstant_of_functor (F : EpFunctor Y X)
    (E : EpFunctor X (EpGroupoid.trivial (discretePolyfold ℕ)))
    (hE : ∀ x, E.obj x = (F.obj ⁻¹' {x}).ncard) :
    IsLocallyConstant fun x => (F.obj ⁻¹' {x}).ncard := by
  have hc : Continuous E.obj := continuousOn_univ.1 E.isScSmoothMap_obj.continuousOn
  have : (fun x => (F.obj ⁻¹' {x}).ncard) = E.obj := funext fun x => (hE x).symm
  rw [this]
  exact (IsLocallyConstant.iff_continuous _).2 hc

end

theorem A_to_B : A → B := by
  intro hA ObjY MorY ObjX MorX _ _ _ _ _ _ _ _ _ _ _ _ Y X F hF
  obtain ⟨hone, -, hlc, -, h84⟩ := hA
  refine ⟨fun c ⟨p, hp⟩ => ?_, ⟨cardFunctor F hF (hlc hF), fun _ => rfl⟩, hone hF⟩
  obtain ⟨k, hk⟩ := h84 hF c ⟨p, hp.symm⟩
  exact ⟨k, fun x hx => hk _ hx x rfl⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF
    exact (hB ObjY MorY ObjX MorX Y X F hF).2.2
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x
    obtain ⟨E, hE⟩ := (hB ObjY MorY ObjX MorX Y X F hF).2.1
    exact (isLocallyConstant_of_functor F E hE).eventually_eq x
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF
    obtain ⟨E, hE⟩ := (hB ObjY MorY ObjX MorX Y X F hF).2.1
    exact isLocallyConstant_of_functor F E hE
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF
    obtain ⟨E, hE⟩ := (hB ObjY MorY ObjX MorX Y X F hF).2.1
    exact fun s => isOpen_coinduced.2 (isLocallyConstant_of_functor F E hE s)
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF c hc
    obtain ⟨p, rfl⟩ := hc
    obtain ⟨k, hk⟩ := (hB ObjY MorY ObjX MorX Y X F hF).1 _ ⟨p, rfl⟩
    exact ⟨k, fun z hz x hx => hk x (hx ▸ hz)⟩

#rt_check RoundTrip.V8_42.A_to_B [Polyfold.EpFunctor.IsProperCovering.one_le_ncard_fiber,
  Polyfold.EpFunctor.IsProperCovering.eventually_ncard_fiber_eq,
  Polyfold.EpFunctor.IsProperCovering.isLocallyConstant_ncard_fiber,
  Polyfold.EpFunctor.IsProperCovering.isLocallyConstant_fiberCardOrbit,
  Polyfold.EpFunctor.IsProperCovering.proposition_8_6_4]
#rt_check RoundTrip.V8_42.B_to_A [Polyfold.EpFunctor.IsProperCovering.one_le_ncard_fiber,
  Polyfold.EpFunctor.IsProperCovering.eventually_ncard_fiber_eq,
  Polyfold.EpFunctor.IsProperCovering.isLocallyConstant_ncard_fiber,
  Polyfold.EpFunctor.IsProperCovering.isLocallyConstant_fiberCardOrbit,
  Polyfold.EpFunctor.IsProperCovering.proposition_8_6_4]
#rt_overlap RoundTrip.V8_42.B_to_A [Polyfold.EpFunctor.IsProperCovering.one_le_ncard_fiber,
  Polyfold.EpFunctor.IsProperCovering.eventually_ncard_fiber_eq,
  Polyfold.EpFunctor.IsProperCovering.isLocallyConstant_ncard_fiber,
  Polyfold.EpFunctor.IsProperCovering.isLocallyConstant_fiberCardOrbit,
  Polyfold.EpFunctor.IsProperCovering.proposition_8_6_4]

end RoundTrip.V8_42
