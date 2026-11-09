import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_34

/-! Round trip for V9_34 (Definition 9.3.6, pp. 425–426 of the 2021 book; 2017: Definition 9.10:
tame `Θ`).

The item lists the definitions `EpGroupoid.TameBranchingStructure` and `EpGroupoid.IsTameBranched`
(vocabulary) and three theorems; `A` is the conjunction of their types, universes at `0`:
`isTameBranched_zero`, `isTameBranched_indicator` (the indicator of a point of `ℝⁿ` is tame) and
`MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero` (a submanifold avoiding `∂X` has a tame
induced structure).

`B` says (a) `IsTameBranched Θ ↔ IsTameB X Θ` for branched `Θ` and (b) the "in particular": the
sheets of such data are manifolds with boundary with corners.

* The definitions, "⇒": `isTameB_of_isTameBranched` (proved): a project
  `TameBranchingStructure` (natural representation `NaturalRep` on `U(x)`, properness property,
  tame induced structures) gives `B`'s data, with `Φ(g)⁻¹ = Φ(g⁻¹)` as the inverse.
* "⇐" is not proved: `B`'s natural action (`IsNatAction`) does not ask `U(x)` to be connected,
  and the project's `NaturalRep` does.  From `B`'s data one gets a project structure by passing
  to a connected `U' ⊆ U(x)` (Theorem 7.1, `theorem_7_1`; properness passes to open subsets,
  `HasPropernessProperty.mono`; `LocalBranchingStructure.restrict`).  The sheets `Mᵢ ∩ U'` must
  then have tame induced structures, i.e. a tame induced structure restricts to open pieces,
  which the project does not have as a lemma.  This direction is believed true; it is proof
  effort only.
* (b) is not in `A`: the project lists "a tame finite-dimensional M-polyfold is a manifold with
  boundary with corners" as not formalized.  It is a genuine content gap (substantial
  mathematics: the corner charts from the tame retracts).
* `B_to_A` re-proves `A`'s three theorems outright (they do not use `B`), as copies of the
  project's proofs. -/

namespace RoundTrip.V9_34
open Polyfold Polyfold.EpGroupoid Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.isTameBranched_zero.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isTameBranched_indicator) ∧
  (type_of% @Polyfold.MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.isTameBranched_zero.{0}, @Polyfold.EpGroupoid.isTameBranched_indicator,
    @Polyfold.MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero.{0}⟩

/-! ### The definitions: project ⇒ `B` -/

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- A natural representation is a natural action in `B`'s sense. -/
theorem isNatAction_of_naturalRep {x : Obj} (R : X.NaturalRep x) :
    IsNatAction X x R.U R.Φ R.Γ where
  isOpen := R.isOpen_U
  mem := R.mem_U
  diffeo g := ⟨R.Φ g⁻¹, R.isScDiffeoOn_Φ g⟩
  hom := R.Φ_mul
  smooth := R.isScSmoothOn_Γ
  Γ_x := R.Γ_self
  src_tgt g y hy := ⟨R.src_Γ g y hy, R.tgt_Γ g y hy⟩
  unique := R.existsUnique_Γ

/-- **Definition 9.3.6, project ⇒ `B`**: a tame `Θ` in the project's sense is tame in `B`'s. -/
theorem isTameB_of_isTameBranched {Θ : Obj → ℚ} (h : X.IsTameBranched Θ) : IsTameB X Θ := by
  intro x hx
  obtain ⟨S⟩ := h x hx
  refine ⟨S.rep.U, S.rep.Φ, S.rep.Γ, S.toLocalBranchingStructure,
    isNatAction_of_naturalRep S.rep, ?_, S.U_eq, S.hasTameInducedStructure⟩
  rw [← S.U_eq]
  exact S.hasPropernessProperty

end

/-- `B`'s first half, the direction `IsTameBranched → IsTameB` of (a). -/
def B_def_forward : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    X.IsTameBranched Θ → IsTameB X Θ

theorem B_def_forward_holds : B_def_forward := fun _ _ _ _ _ _ _ _ _ _ _ h =>
  isTameB_of_isTameBranched h

/-! ### `B → A`: re-proved outright (copies of the project's proofs) -/

theorem hasTameInducedStructure_copy {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] {P : MPolyfold X} {A : Set X} (hA : P.IsSmoothSubmanifold A)
    (h0 : ∀ a ∈ A, P.degIndex a = 0) : P.HasTameInducedStructure A := by
  let := P.paracompactSpace_subtype A
  exact ⟨hA.isSubMPolyfold, (MPolyfold.hasCornerStructure_of_degIndex_eq_zero hA h0).isTame⟩

theorem isTameBranched_zero_copy {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) : X.IsTameBranched 0 := fun _ hx =>
  (lt_irrefl (0 : ℚ) hx).elim

theorem isTameBranched_indicator_copy (n : ℕ) (p : Fin n → ℝ) :
    (trivial (rnPolyfold n)).IsTameBranched (({p} : Set (Fin n → ℝ)).indicator 1) := by
  intro y hy
  have hyp : y = p := by
    rw [supp_indicator_singleton] at hy; exact hy
  subst hyp
  obtain ⟨R, -⟩ := theorem_7_1 (trivial (rnPolyfold n)) y isOpen_univ (mem_univ y)
  let B := (localBranchingStructure_indicator n y).restrict R.isOpen_U R.mem_U (subset_univ _)
  exact ⟨{ toLocalBranchingStructure := B
           rep := R
           U_eq := rfl
           hasPropernessProperty := hasPropernessProperty_trivial (rnPolyfold n) R.isOpen_U
           hasTameInducedStructure := fun i =>
             hasTameInducedStructure_copy (B.isSmoothSubmanifold i)
               fun a _ => rnPolyfold_degIndex n a }⟩

/-- `B → A`, by re-proving `A` outright (`A`'s witnesses are not consequences of `B`). -/
theorem B_to_A : B → A := fun _ =>
  ⟨@isTameBranched_zero_copy, @isTameBranched_indicator_copy, @hasTameInducedStructure_copy⟩

#rt_check RoundTrip.V9_34.B_def_forward_holds [Polyfold.EpGroupoid.isTameBranched_zero,
  Polyfold.EpGroupoid.isTameBranched_indicator,
  Polyfold.MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero]
#rt_check RoundTrip.V9_34.B_to_A [Polyfold.EpGroupoid.isTameBranched_zero,
  Polyfold.EpGroupoid.isTameBranched_indicator,
  Polyfold.MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero]
#rt_overlap RoundTrip.V9_34.B_to_A [Polyfold.EpGroupoid.isTameBranched_zero,
  Polyfold.EpGroupoid.isTameBranched_indicator,
  Polyfold.MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero]

end RoundTrip.V9_34
