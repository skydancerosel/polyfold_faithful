import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_33

/-! Round trip for V8_33 (after Definition 8.9 of the 2017 text, 2021: after Definition 8.5.5:
the maps `τ(y)`, `φ_{yy'}(ψ)`, the two actions and the equivariance of `τ(y)`).

`A` is the conjunction of the types of the ten listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `GeometricLift.isScDiffeoOn_τy`, `isScDiffeoOn_φ`, `φ_comp`, `φ_id`,
`φ_inv_φ`, `smul_def`, `smul_def'`, `isScSmoothMap_smul`, `τy_φ`, `τ_equivariant`.  The listed
`GeometricLift.Ux`, `τy`, `φ` are definitions (vocabulary): `τy y = (L.τ.app y).toFun`,
`φ ψ = (L.LD.map ψ).toFun`, definitionally `B`'s maps.

* `A → B`: glue.  `B`'s two sc-diffeomorphism clauses are `isScDiffeoOn_τy`, `isScDiffeoOn_φ`
  (with the inverses `τyInv`, `φInv`); functoriality is `φ_comp`; the `G_y`-action laws are
  `φ_id`, `φ_comp`; the `G_x`-action laws come from `smul_def` (`g • z = L_C(g)(z)`) and the
  `MulAction` laws of the project's scoped instance; equivariance is `τ_equivariant` with
  `smul_def'`, `smul_def`.
* `B → A`: every conjunct of `A` is stated for an arbitrary functor `f : D ⥤ SingleObj G` and
  geometric lift, with no finiteness hypotheses and no covering hypothesis, while `B` assumes
  `[Fintype D]`, `[Fintype (a ⟶ b)]`, `[Fintype G]` and `IsCoveringFunctor f`.  `B` cannot be
  applied there; the conjuncts are one-line consequences of the definitions (the `isScDiffeoOn`
  field of `ScDiffeo`, `Functor.map_comp`, `Functor.map_id`, the naturality square of `τ`) and are
  re-proved outright.  This direction is vacuous for the audit (it does not use `B`). -/

namespace RoundTrip.V8_33
open Polyfold CategoryTheory Set
open scoped Polyfold.GeometricLift

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GeometricLift.isScDiffeoOn_τy.{0}) ∧
  (type_of% @Polyfold.GeometricLift.isScDiffeoOn_φ.{0}) ∧
  (type_of% @Polyfold.GeometricLift.φ_comp.{0}) ∧
  (type_of% @Polyfold.GeometricLift.φ_id.{0}) ∧
  (type_of% @Polyfold.GeometricLift.φ_inv_φ.{0}) ∧
  (type_of% @Polyfold.GeometricLift.smul_def.{0}) ∧
  (type_of% @Polyfold.GeometricLift.smul_def'.{0}) ∧
  (type_of% @Polyfold.GeometricLift.isScSmoothMap_smul.{0}) ∧
  (type_of% @Polyfold.GeometricLift.τy_φ.{0}) ∧
  (type_of% @Polyfold.GeometricLift.τ_equivariant.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GeometricLift.isScDiffeoOn_τy.{0}, @Polyfold.GeometricLift.isScDiffeoOn_φ.{0},
    @Polyfold.GeometricLift.φ_comp.{0}, @Polyfold.GeometricLift.φ_id.{0},
    @Polyfold.GeometricLift.φ_inv_φ.{0}, @Polyfold.GeometricLift.smul_def.{0},
    @Polyfold.GeometricLift.smul_def'.{0}, @Polyfold.GeometricLift.isScSmoothMap_smul.{0},
    @Polyfold.GeometricLift.τy_φ.{0}, @Polyfold.GeometricLift.τ_equivariant.{0}⟩

theorem A_to_B : A → B := by
  intro hA D _ _ _ G _ _ f _ L
  obtain ⟨hτ, hφ, hcomp, hid, -, hsmul, hsmul', -, -, hequiv⟩ := hA
  refine ⟨fun y => ⟨_, hτ L y⟩, fun y y' ψ => ⟨_, hφ L ψ⟩, fun y y' y'' γ ψ => hcomp L γ ψ,
    fun y z => congrFun (hid L y) z, fun y h k z => congrFun (hcomp L k h) z, fun z => ?_,
    fun g h z => ?_, fun y h z => ?_⟩
  · rw [← hsmul L (1 : G) z]
    exact one_smul G z
  · rw [← hsmul L (g * h) z, ← hsmul L h z, ← hsmul L g]
    exact mul_smul g h z
  · have h1 := hequiv L h z
    rw [hsmul' L h z, hsmul L] at h1
    exact h1

theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro D _ G _ f L y
    exact (L.τ.app y).isScDiffeoOn
  · intro D _ G _ f L y y' ψ
    exact (L.LD.map ψ).isScDiffeoOn
  · intro D _ G _ f L y y' y'' γ ψ
    unfold GeometricLift.φ
    rw [L.LD.map_comp]
    rfl
  · intro D _ G _ f L y
    unfold GeometricLift.φ
    rw [L.LD.map_id]
    rfl
  · intro D _ G _ f L y y' ψ z
    unfold GeometricLift.φ
    change (L.LD.map ψ ≫ L.LD.map (Groupoid.inv ψ)).toFun z = z
    rw [← L.LD.map_comp, Groupoid.comp_inv, L.LD.map_id]
    rfl
  · intro D _ G _ f L g z
    rfl
  · intro D _ G _ f L y h z
    rfl
  · intro D _ G _ f L g
    exact (L.LC.map (g.down : SingleObj.star G ⟶ SingleObj.star G)).isScDiffeoOn.isScSmoothOn
  · intro D _ G _ f L y y' ψ z
    exact congrFun (congrArg ScDiffeo.toFun (L.τ.naturality ψ)) z
  · intro D _ G _ f L y h z
    exact congrFun (congrArg ScDiffeo.toFun (L.τ.naturality h)) z

#rt_check_soft RoundTrip.V8_33.A_to_B [Polyfold.GeometricLift.isScDiffeoOn_τy,
  Polyfold.GeometricLift.isScDiffeoOn_φ, Polyfold.GeometricLift.φ_comp,
  Polyfold.GeometricLift.φ_id, Polyfold.GeometricLift.φ_inv_φ, Polyfold.GeometricLift.smul_def,
  Polyfold.GeometricLift.smul_def', Polyfold.GeometricLift.isScSmoothMap_smul,
  Polyfold.GeometricLift.τy_φ, Polyfold.GeometricLift.τ_equivariant]
#rt_check_soft RoundTrip.V8_33.B_to_A [Polyfold.GeometricLift.isScDiffeoOn_τy,
  Polyfold.GeometricLift.isScDiffeoOn_φ, Polyfold.GeometricLift.φ_comp,
  Polyfold.GeometricLift.φ_id, Polyfold.GeometricLift.φ_inv_φ, Polyfold.GeometricLift.smul_def,
  Polyfold.GeometricLift.smul_def', Polyfold.GeometricLift.isScSmoothMap_smul,
  Polyfold.GeometricLift.τy_φ, Polyfold.GeometricLift.τ_equivariant]
#rt_overlap RoundTrip.V8_33.B_to_A [Polyfold.GeometricLift.isScDiffeoOn_τy,
  Polyfold.GeometricLift.isScDiffeoOn_φ, Polyfold.GeometricLift.φ_comp,
  Polyfold.GeometricLift.φ_id, Polyfold.GeometricLift.φ_inv_φ, Polyfold.GeometricLift.smul_def,
  Polyfold.GeometricLift.smul_def', Polyfold.GeometricLift.isScSmoothMap_smul,
  Polyfold.GeometricLift.τy_φ, Polyfold.GeometricLift.τ_equivariant]

end RoundTrip.V8_33
