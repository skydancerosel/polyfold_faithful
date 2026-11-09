import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_18

/-! Round trip for V8_18 (Theorem 8.1.15 = 2017 Theorem 8.4: the orbit space `|TX|`).

The item lists the definitions `tangentOrbitProj`, `NaturalRep.tangentU`, `NaturalRep.tΦ`,
`NaturalRep.tangentMulAction`, `NaturalRep.tΓ` (vocabulary) and thirteen theorems.  `A` is the
conjunction of their types, universes at `0` (B lives in `Type`; `metrizableSpace_of_pullback`
has two universe parameters, both at `0`):

1. `continuous_tangentOrbitProj` (`|p| : |TX| → |X¹|` continuous),
2. `preimage_tangentOrbitProj_image` (`|p|⁻¹(π₁(U ∩ X₁)) = π_T(p⁻¹ U)`),
3. `NaturalRep.isScDiffeoOn_tΦ` (`TΦ(g)` sc-diffeomorphisms of `TU(x)`),
4. `NaturalRep.tangent_π_eq_iff` (fibres of `π_T` on `TU(x)` are `G_x`-orbits),
5. `NaturalRep.isOpenEmbedding_tangentOrbitQuotientMap` (`G_x\TU(x) ↪ |TX|` open embedding),
6. `NaturalRep.range_tangentOrbitQuotientMap`, 7. `NaturalRep.image_tangentU_eq_preimage`,
8. `NaturalRep.metrizableSpace_image_tangentU` (`|TU(x)|` metrizable),
9. `NaturalRep.metrizableSpace_image_liftU` (`|U(x)₁|` metrizable),
10. `metrizableSpace_tangent_orbitSpace` (`|X|` paracompact ⇒ `|TX|` **metrizable**),
11. `theorem_8_1_15` (`|X|` paracompact ⇒ `|TX|` paracompact),
12. `hasParacompactOrbitSpace_tangent_trivial` (non-vacuity witness),
13. `metrizableSpace_of_pullback` (Part I's Smirnov theorem pulled back along a map).

`B`: for every ep-groupoid `X` in `Type`, `|X|` paracompact (quotient topology written as
`coinduced π`) ⇒ `|TX|` paracompact.

* `OrbitParacompactB G ↔ G.HasParacompactOrbitSpace` is `Iff.rfl`: the project's orbit space is a
  `Quotient` with the quotient topology `coinduced (Quotient.mk _)`, and `π = Quotient.mk _`.
* `A ⇒ B`: conjunct 11, `theorem_8_1_15`.
* `B ⇒ A` is **not proved**.  Conjuncts 11 and 12 follow from `B` (`B_to_A_core`, with the
  Chapter 7 lemma `hasParacompactOrbitSpace_trivial` for 12).  The other eleven conjuncts are not
  consequences of `B`: they are the project's proof of Theorem 8.4 (a different route from the
  text's: Smirnov's theorem pulled back along `|p|` instead of Michael's Proposition 2.7.4), its
  intermediate lemmas about the `G_x`-action on `TU(x)`, a strictly stronger conclusion (10:
  metrizability of `|TX|`, not implied by paracompactness), and a Part I metrization theorem (13).
  Re-proving them would mean re-proving the whole of `Polyfold/Chapter8/TangentOrbit.lean` (and
  Part I's `metrizableSpace_of_pullback`); they are true (`A_holds`), so the failure is effort only.
-/

namespace RoundTrip.V8_18
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.continuous_tangentOrbitProj.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.preimage_tangentOrbitProj_image.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_tΦ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.tangent_π_eq_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_tangentOrbitQuotientMap.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.range_tangentOrbitQuotientMap.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.image_tangentU_eq_preimage.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.metrizableSpace_image_tangentU.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.metrizableSpace_image_liftU.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.metrizableSpace_tangent_orbitSpace.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.theorem_8_1_15.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.hasParacompactOrbitSpace_tangent_trivial.{0}) ∧
  (type_of% @Polyfold.metrizableSpace_of_pullback.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.continuous_tangentOrbitProj.{0},
    @Polyfold.EpGroupoid.preimage_tangentOrbitProj_image.{0},
    @Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_tΦ.{0},
    @Polyfold.EpGroupoid.NaturalRep.tangent_π_eq_iff.{0},
    @Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_tangentOrbitQuotientMap.{0},
    @Polyfold.EpGroupoid.NaturalRep.range_tangentOrbitQuotientMap.{0},
    @Polyfold.EpGroupoid.NaturalRep.image_tangentU_eq_preimage.{0},
    @Polyfold.EpGroupoid.NaturalRep.metrizableSpace_image_tangentU.{0},
    @Polyfold.EpGroupoid.NaturalRep.metrizableSpace_image_liftU.{0},
    @Polyfold.EpGroupoid.metrizableSpace_tangent_orbitSpace.{0},
    @Polyfold.EpGroupoid.theorem_8_1_15.{0},
    @Polyfold.EpGroupoid.hasParacompactOrbitSpace_tangent_trivial.{0},
    @Polyfold.metrizableSpace_of_pullback.{0, 0}⟩

/-- B's paracompactness of `|G|` (quotient topology written out) is the project's. -/
theorem orbitParacompactB_iff {Obj Mor : Type _} [TopologicalSpace Obj] (G : GroupoidStr Obj Mor) :
    OrbitParacompactB G ↔ ParacompactSpace G.OrbitSpace := Iff.rfl

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X hX
  exact (orbitParacompactB_iff _).2 (hA.2.2.2.2.2.2.2.2.2.2.1 X ((orbitParacompactB_iff _).1 hX))

/-- The part of `A` that `B` gives: `theorem_8_1_15` and its non-vacuity witness. -/
theorem B_to_A_core : B →
    (type_of% @Polyfold.EpGroupoid.theorem_8_1_15.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.hasParacompactOrbitSpace_tangent_trivial.{0}) := by
  intro hB
  refine ⟨fun {Obj Mor} _ _ _ _ _ _ X hX => (orbitParacompactB_iff _).1
    (hB Obj Mor X ((orbitParacompactB_iff _).2 hX)), fun {Z} _ _ _ P => ?_⟩
  exact (orbitParacompactB_iff _).1 (hB Z Z (EpGroupoid.trivial P)
    ((orbitParacompactB_iff _).2 (EpGroupoid.hasParacompactOrbitSpace_trivial P)))

/-! ### Checks

**Harness note.**  The banned Part I theorem `metrizableSpace_of_pullback` (Smirnov's theorem
pulled back) is foundational Part I infrastructure, reached by *every* statement that mentions the
tangent ep-groupoid, `B` included: e.g. `B → B._proof_2 → MPolyfold.paracompactSpace_tangentSpace
→ MPolyfold.metrizableSpace_tangentSpace → metrizableSpace_of_pullback` (the instance
`[ParacompactSpace TX]` that `tangentEpGroupoid` needs), and
`tangentEpGroupoid → lemma_8_1_8 → … → MPolyfold.metrizableSpace → metrizableSpace_of_locally →
metrizableSpace_of_pullback` (every M-polyfold is metrizable).  So `#rt_check` and
`#rt_check_soft` fail on every term mentioning `B` (recorded below with `#guard_msgs` on
`B_stmt : B → B := id`).  We therefore run `#rt_check_beyond_stmt T`: the harness traversal
`rtCollect` from the proof of `T`, with everything that the *statement* (type) of `T` already
reaches marked as visited; a banned theorem reached by the proof but not by the statement fails
the check.  Our proofs pass; the banned theorems they reach are reached through the statements
alone. -/

open Lean Elab Command in
/-- `#rt_check_beyond_stmt T [banned]`: the proof of `T` reaches no banned declaration beyond
those that the statement of `T` itself reaches. -/
elab "#rt_check_beyond_stmt " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let stmt := rtCollect env ci.type.getUsedConstants.toList {}
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let used := rtCollect env roots.toList stmt
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let banned := bs.getElems.toList.map (·.getId)
  let bad := banned.filter fun b => used.contains b && !stmt.contains b
  unless bad.isEmpty do throwError "FAIL: {t.getId} uses {bad} beyond its statement"
  let viaStmt := banned.filter stmt.contains
  logInfo m!"OK: {t.getId} reaches no banned declaration beyond its statement; its statement alone reaches {viaStmt}"

/-- `B`'s statement alone, to show that it reaches `metrizableSpace_of_pullback`. -/
theorem B_stmt : B → B := id

/--
error: rt_check FAIL: RoundTrip.V8_18.B_stmt uses [Polyfold.metrizableSpace_of_pullback]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V8_18.B_stmt [Polyfold.EpGroupoid.continuous_tangentOrbitProj,
  Polyfold.EpGroupoid.preimage_tangentOrbitProj_image,
  Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_tΦ, Polyfold.EpGroupoid.NaturalRep.tangent_π_eq_iff,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_tangentOrbitQuotientMap,
  Polyfold.EpGroupoid.NaturalRep.range_tangentOrbitQuotientMap,
  Polyfold.EpGroupoid.NaturalRep.image_tangentU_eq_preimage,
  Polyfold.EpGroupoid.NaturalRep.metrizableSpace_image_tangentU,
  Polyfold.EpGroupoid.NaturalRep.metrizableSpace_image_liftU,
  Polyfold.EpGroupoid.metrizableSpace_tangent_orbitSpace, Polyfold.EpGroupoid.theorem_8_1_15,
  Polyfold.EpGroupoid.hasParacompactOrbitSpace_tangent_trivial, Polyfold.metrizableSpace_of_pullback]

#rt_check_beyond_stmt RoundTrip.V8_18.A_to_B [Polyfold.EpGroupoid.continuous_tangentOrbitProj,
  Polyfold.EpGroupoid.preimage_tangentOrbitProj_image,
  Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_tΦ, Polyfold.EpGroupoid.NaturalRep.tangent_π_eq_iff,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_tangentOrbitQuotientMap,
  Polyfold.EpGroupoid.NaturalRep.range_tangentOrbitQuotientMap,
  Polyfold.EpGroupoid.NaturalRep.image_tangentU_eq_preimage,
  Polyfold.EpGroupoid.NaturalRep.metrizableSpace_image_tangentU,
  Polyfold.EpGroupoid.NaturalRep.metrizableSpace_image_liftU,
  Polyfold.EpGroupoid.metrizableSpace_tangent_orbitSpace, Polyfold.EpGroupoid.theorem_8_1_15,
  Polyfold.EpGroupoid.hasParacompactOrbitSpace_tangent_trivial, Polyfold.metrizableSpace_of_pullback]
#rt_check_beyond_stmt RoundTrip.V8_18.B_to_A_core [Polyfold.EpGroupoid.continuous_tangentOrbitProj,
  Polyfold.EpGroupoid.preimage_tangentOrbitProj_image,
  Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_tΦ, Polyfold.EpGroupoid.NaturalRep.tangent_π_eq_iff,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_tangentOrbitQuotientMap,
  Polyfold.EpGroupoid.NaturalRep.range_tangentOrbitQuotientMap,
  Polyfold.EpGroupoid.NaturalRep.image_tangentU_eq_preimage,
  Polyfold.EpGroupoid.NaturalRep.metrizableSpace_image_tangentU,
  Polyfold.EpGroupoid.NaturalRep.metrizableSpace_image_liftU,
  Polyfold.EpGroupoid.metrizableSpace_tangent_orbitSpace, Polyfold.EpGroupoid.theorem_8_1_15,
  Polyfold.EpGroupoid.hasParacompactOrbitSpace_tangent_trivial, Polyfold.metrizableSpace_of_pullback]
#rt_overlap RoundTrip.V8_18.B_to_A_core [Polyfold.EpGroupoid.continuous_tangentOrbitProj,
  Polyfold.EpGroupoid.preimage_tangentOrbitProj_image,
  Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_tΦ, Polyfold.EpGroupoid.NaturalRep.tangent_π_eq_iff,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_tangentOrbitQuotientMap,
  Polyfold.EpGroupoid.NaturalRep.range_tangentOrbitQuotientMap,
  Polyfold.EpGroupoid.NaturalRep.image_tangentU_eq_preimage,
  Polyfold.EpGroupoid.NaturalRep.metrizableSpace_image_tangentU,
  Polyfold.EpGroupoid.NaturalRep.metrizableSpace_image_liftU,
  Polyfold.EpGroupoid.metrizableSpace_tangent_orbitSpace, Polyfold.EpGroupoid.theorem_8_1_15,
  Polyfold.EpGroupoid.hasParacompactOrbitSpace_tangent_trivial, Polyfold.metrizableSpace_of_pullback]

end RoundTrip.V8_18
