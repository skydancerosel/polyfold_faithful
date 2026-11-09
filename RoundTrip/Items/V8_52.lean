import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_52

/-!
Round trip for V8_52 (2021 Proposition 8.1.17 (2) for every `(TX)ⁱ`: (SLUC) for `X` gives (SLUC)
for `TX`, p. 371).

The item lists the definitions `ScEquiv.toHomeomorph`, `EP.tangentEP`, `EpEquiv`,
`EpEquiv.shift`, `tangentShiftEpEquiv`, `EP.tangentLiftEpEquiv`,
`BundledMPolyfold.tangentLiftEquiv` (vocabulary) and seven theorems: `EpEquiv.nonEffectivePart_eq`,
`EpEquiv.isLUC` ((LUC) is transported by an `EpEquiv`), `EP.isLUC_tangent_lift` (every `T(Xⁱ)`
has (LUC)), **`EP.proposition_8_1_17_two_all`**, the witnesses
`hasConnectedDenseLevelOneReps_of_subsingleton`, `Examples.proposition_8_1_17_two_all_pointEP`,
and `proposition_2_3_17_all` (`T(Xⁱ) ≅ (TX)ⁱ` for bundled M-polyfolds).  `A` is the
conjunction of their types, universes at `0` (the point witness has none).

`B`: for `A : EP.{0}`, (LUC) for every `Xⁱ` implies (LUC) for every `(TX)ⁱ`.

* `B ⇒ A`: the main theorem and the point witness come from `B` (`B` has no further
  hypotheses, so it gives the project's theorem with `hR`, `hp` unused).  The other five conjuncts
  are auxiliary lemmas of the project's proof that `B` does not contain; they are re-proved here
  from the non-item lemmas their proofs use (2021 Proposition 7.2.21,
  `proposition_8_1_17_one`, the Proposition 2.3.17 sub-lemmas of `TangentLiftAll.lean`).
* `A ⇒ B` **fails**: `proposition_8_1_17_two_all` assumes, for every `i`,
  `HasConnectedDenseLevelOneReps (Xⁱ)` (natural representations with `U(x) ∩ X₁` connected and
  dense, the text's `V(x)`) and that `p : T𝐗ⁱ → (𝐗ⁱ)¹` is open (Part I gap G.8), which `B` does
  not have.  With them, `A ⇒ B` is immediate (`A_to_B_of_hyp`).  Both are satisfiable (the point
  witness).
-/

namespace RoundTrip.V8_52
open Polyfold Set Function Topology Filter

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.EpEquiv.nonEffectivePart_eq.{0, 0}) ∧
  (type_of% @Polyfold.EpGroupoid.EpEquiv.isLUC.{0, 0}) ∧
  (type_of% @Polyfold.EP.isLUC_tangent_lift.{0}) ∧
  (type_of% @Polyfold.EP.proposition_8_1_17_two_all.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.hasConnectedDenseLevelOneReps_of_subsingleton.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.Examples.proposition_8_1_17_two_all_pointEP) ∧
  (type_of% @Polyfold.proposition_2_3_17_all.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.EpEquiv.nonEffectivePart_eq.{0, 0},
    @Polyfold.EpGroupoid.EpEquiv.isLUC.{0, 0},
    @Polyfold.EP.isLUC_tangent_lift.{0},
    @Polyfold.EP.proposition_8_1_17_two_all.{0},
    @Polyfold.EpGroupoid.hasConnectedDenseLevelOneReps_of_subsingleton.{0},
    @Polyfold.EpGroupoid.Examples.proposition_8_1_17_two_all_pointEP,
    @Polyfold.proposition_2_3_17_all.{0}⟩

/-- `A ⇒ B` under the project's extra hypotheses (the only difference). -/
theorem A_to_B_of_hyp (hA : A) (X : EP.{0}) (h : ∀ i : ℕ, (X.lift i).X.IsLUC)
    (hR : ∀ i, (X.lift i).X.HasConnectedDenseLevelOneReps)
    (hp : ∀ i, IsOpenMap (X.lift i).X.PMor.tangentProj) (i : ℕ) :
    (X.tangentEP.lift i).X.IsLUC :=
  hA.2.2.2.1 X h hR hp i

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {X' : EpGroupoid Obj' Mor'}

/-- `EpEquiv.nonEffectivePart_eq`, re-proved. -/
theorem nonEffectivePart_eq' (e : EpGroupoid.EpEquiv X X') :
    X'.nonEffectivePart = e.mor.invFun ⁻¹' X.nonEffectivePart := by
  ext k'
  rw [mem_preimage, X'.mem_nonEffectivePart_iff, X.mem_nonEffectivePart_iff]
  have hk : e.mor.toHomeomorph (e.mor.invFun k') = k' := e.mor.right_inv k'
  conv_lhs => rw [← hk, ← e.mor.toHomeomorph.map_nhds_eq, Filter.eventually_map]
  refine Filter.eventually_congr (Filter.Eventually.of_forall fun φ => ?_)
  change X'.src (e.mor φ) = X'.tgt (e.mor φ) ↔ _
  rw [e.src_mor, e.tgt_mor]
  exact e.obj.toEquiv.injective.eq_iff

/-- `EpEquiv.isLUC`, re-proved. -/
theorem isLUC' (e : EpGroupoid.EpEquiv X X') (h : X.IsLUC) : X'.IsLUC := by
  rw [X'.proposition_7_2_21, nonEffectivePart_eq' e]
  exact (X.proposition_7_2_21.1 h).preimage e.mor.toHomeomorph.symm.continuous

/-- `hasConnectedDenseLevelOneReps_of_subsingleton`, re-proved. -/
theorem hasConnectedDense' (X : EpGroupoid Obj Mor) [Subsingleton Obj]
    (hs : X.PObj.smoothSet = univ) : X.HasConnectedDenseLevelOneReps := fun x => by
  obtain ⟨R, -⟩ := X.theorem_7_1_13 (X.PObj.levelVal 1 x) isOpen_univ (mem_univ _)
  refine ⟨R, Set.Subsingleton.isPreconnected fun _ _ _ _ =>
    MPolyfold.level_ext (Subsingleton.elim _ _), ?_⟩
  have h1 : X.PObj.levelSet 1 = univ := eq_univ_of_forall fun y =>
    MPolyfold.smoothSet_subset_levelSet 1 (by rw [hs]; exact mem_univ y)
  rw [h1, inter_univ]
  exact subset_closure

end

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun e => nonEffectivePart_eq' e, fun e h => isLUC' e h, ?_,
    fun X h _ _ => hB X h, fun X _ hs => hasConnectedDense' X hs,
    hB EpGroupoid.Examples.pointEP EpGroupoid.Examples.isSLUC_pointEP, ?_⟩
  · -- `isLUC_tangent_lift`: part (1) for every `Xⁱ` (not part of `B`)
    intro X h hR hp i
    exact (X.lift i).X.proposition_8_1_17_one (h (i + 1)) (hR i) (hp i)
  · -- `proposition_2_3_17_all` (not part of `B`): its sub-lemmas
    intro M i
    exact ⟨(M.tangentLiftEquiv i).isScDiffeoOn, (M.shiftLiftEquiv i).isScDiffeoOn,
      ⟨(M.tangentProjLift i).isScSmoothMap, (M.lift i).P.tangentProj_isScSmooth⟩,
      M.tangentProjLift_tangentLiftEquiv i, M.incl_tangentLiftEquiv i,
      M.levelVal_tangentLiftEquiv_succ i, M.incl_shiftLiftEquiv i, M.tangentLiftEquiv_unique i⟩

#rt_check RoundTrip.V8_52.B_to_A [Polyfold.EpGroupoid.EpEquiv.nonEffectivePart_eq,
  Polyfold.EpGroupoid.EpEquiv.isLUC, Polyfold.EP.isLUC_tangent_lift,
  Polyfold.EP.proposition_8_1_17_two_all,
  Polyfold.EpGroupoid.hasConnectedDenseLevelOneReps_of_subsingleton,
  Polyfold.EpGroupoid.Examples.proposition_8_1_17_two_all_pointEP,
  Polyfold.proposition_2_3_17_all]
#rt_check RoundTrip.V8_52.A_to_B_of_hyp [Polyfold.EpGroupoid.EpEquiv.nonEffectivePart_eq,
  Polyfold.EpGroupoid.EpEquiv.isLUC, Polyfold.EP.isLUC_tangent_lift,
  Polyfold.EP.proposition_8_1_17_two_all,
  Polyfold.EpGroupoid.hasConnectedDenseLevelOneReps_of_subsingleton,
  Polyfold.EpGroupoid.Examples.proposition_8_1_17_two_all_pointEP,
  Polyfold.proposition_2_3_17_all]
#rt_overlap RoundTrip.V8_52.B_to_A [Polyfold.EpGroupoid.EpEquiv.nonEffectivePart_eq,
  Polyfold.EpGroupoid.EpEquiv.isLUC, Polyfold.EP.isLUC_tangent_lift,
  Polyfold.EP.proposition_8_1_17_two_all,
  Polyfold.EpGroupoid.hasConnectedDenseLevelOneReps_of_subsingleton,
  Polyfold.EpGroupoid.Examples.proposition_8_1_17_two_all_pointEP,
  Polyfold.proposition_2_3_17_all]

end RoundTrip.V8_52
