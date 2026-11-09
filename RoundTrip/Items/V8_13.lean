import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_13

/-! Round trip for V8_13 (Theorem 8.1.11 (2017: 8.2): the tangent of an sc-smooth functor).

`A` is the type of `EpFunctor.theorem_8_2`, universes instantiated at `0, 0` (`B` lives in
`Type`); the listed `EpFunctor.tangent` is a definition (vocabulary): the `EpFunctor`
`(TΦ, T𝚽) : T(X, 𝐗) → T(Y, 𝐘)` with `obj`, `mor` Part I's tangent maps.  `theorem_8_2` says
`Φ.tangent.obj = TΦ`, `Φ.tangent.mor = T𝚽` (by `rfl`), both sc-smooth, and `T𝚽` compatible with
`s_T`, `t_T`, the composition (8.5) and the units `u_T = Tu`.

`B` asks the same of `TΦ = tangentMap F.isScSmoothMap_obj`, `T𝚽 = tangentMap F.isScSmoothMap_mor`,
with the units characterized by `IsTUnitB` (plus uniqueness) instead of named.  By proof
irrelevance `B`'s `tangentMap hsX`, `tCompB X hsX`, … are the project's `X.tSrc`, `X.tComp`, …;
`IsTUnitB` is matched with `tUnit` by `tBase_tUnit`, `tSrc_tUnit`, `tangent_ext`. -/

namespace RoundTrip.V8_13
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop := type_of% @Polyfold.EpFunctor.theorem_8_2.{0, 0}

theorem A_holds : A := @Polyfold.EpFunctor.theorem_8_2.{0, 0}

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

theorem isTUnitB_tUnit (X : EpGroupoid Obj Mor) (q : X.PObj.TangentSpace) :
    IsTUnitB X X.isScSmoothMap_src q (X.tUnit q) :=
  ⟨X.tBase_tUnit q, X.tSrc_tUnit q⟩

theorem eq_tUnit_of_isTUnitB (X : EpGroupoid Obj Mor) {q : X.PObj.TangentSpace}
    {v : X.PMor.TangentSpace} (hv : IsTUnitB X X.isScSmoothMap_src q v) : X.tUnit q = v :=
  X.tangent_ext ((X.tBase_tUnit q).trans hv.1.symm) ((X.tSrc_tUnit q).trans hv.2.symm)

end

theorem A_to_B : A → B := by
  intro hA Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F
  obtain ⟨-, -, hso, hsm, hs, ht, hc, hu⟩ := hA F
  refine ⟨X.isScSmoothMap_src, X.isScSmoothMap_tgt, Y.isScSmoothMap_src, Y.isScSmoothMap_tgt,
    hso, hsm, hs, ht, hc, fun a v hv => ?_⟩
  have hv' : X.tUnit a = v := eq_tUnit_of_isTUnitB X hv
  subst hv'
  have h1 : MPolyfold.tangentMap F.isScSmoothMap_mor (X.tUnit a) =
      Y.tUnit (MPolyfold.tangentMap F.isScSmoothMap_obj a) := hu a
  rw [h1]
  exact ⟨isTUnitB_tUnit Y _, fun w hw => eq_tUnit_of_isTUnitB Y hw⟩

theorem B_to_A : B → A := by
  intro hB Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y Φ
  obtain ⟨hsX, htX, hsY, htY, hso, hsm, hs, ht, hc, hu⟩ := hB Obj Mor Obj' Mor' X Y Φ
  exact ⟨rfl, rfl, hso, hsm, hs, ht, hc, fun a =>
    (hu a (X.tUnit a) (isTUnitB_tUnit X a)).2 _ (isTUnitB_tUnit Y _)⟩

#rt_check RoundTrip.V8_13.A_to_B [Polyfold.EpFunctor.theorem_8_2]
#rt_check RoundTrip.V8_13.B_to_A [Polyfold.EpFunctor.theorem_8_2]
#rt_overlap RoundTrip.V8_13.B_to_A [Polyfold.EpFunctor.theorem_8_2]

end RoundTrip.V8_13
