import Polyfold
/-! Blind formalization of V9_21 (the text's Part II, §9.2, Lemma 9.2.7 (2), p. 412 of the
Springer 2021 book; 2017: Lemma 9.5 (2), p. 301): for an equidimensional `Θ`, a bad point `x`
and a local branching structure `(Mᵢ)_{i ∈ I}`, `(σᵢ)` on `U(x)`, every `Mᵢ` contains a sequence
of good points converging to `x`.

Choices:
- Setting: as in `RoundTrip/Blind/V9_15.lean`: ep-groupoid `X : EpGroupoid Obj Mor`,
  `Obj Mor : Type` (universe 0), a branched ep⁺-subgroupoid `Θ` (project's
  `IsBranchedEpSubgroupoid`), equidimensional read as `∃ n, X.IsNDimensional Θ n` (the
  standing hypothesis of Lemma 9.2.7).
- "bad point `x`": `x ∈ supp Θ` and `x` is not good, i.e. `x ∈ S^b_Θ` (Definition 9.2.6, as in
  `RoundTrip/Blind/V9_19.lean`); "good points": points of `S^g_Θ`, i.e. points of `supp Θ` good
  (my `IsGoodAt`, Definition 9.2.2) for some local branching structure whose domain contains
  them (by Remark 9.2.4 (a) the same as for the given structure, the `yₖ` lying in `U(x)`).
- "a local branching structure on `U(x)`": any structure `B` of `Θ` at `x` (project's
  `LocalBranchingStructure Θ x`), not required to be `n`-dimensional.
- "a sequence ... converging to `x`": `y : ℕ → Obj` with `yₖ ∈ Mᵢ`, `yₖ` good, `yₖ → x` in the
  topology of the object space.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_21
open Polyfold

/-- The text's good point `y` of the local branching structure `B` (Definition 9.2.2). -/
def IsGoodAt {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x) (y : Obj) : Prop :=
  y ∈ ⋃ i, B.M i ∧
    ∃ V : Set Obj, IsOpen V ∧ y ∈ V ∧ V ⊆ B.U ∧
      ∀ i j : B.ι, y ∈ B.M i ∩ B.M j → B.M i ∩ V = B.M j ∩ V

/-- `y` is a good point of `Θ`: good for some local branching structure whose domain contains
`y`. -/
def IsGoodPt {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (Θ : Obj → ℚ) (y : Obj) : Prop :=
  ∃ (x : Obj) (B : X.LocalBranchingStructure Θ x), y ∈ B.U ∧ IsGoodAt B y

/-- **Lemma 9.2.7 (2)**: at a bad point `x`, every sheet `Mᵢ` of every local branching structure
at `x` contains good points `yₖ → x`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    (∃ n : ℕ, X.IsNDimensional Θ n) →
    ∀ x : Obj, x ∈ EpGroupoid.supp Θ → ¬ IsGoodPt X Θ x →
    ∀ (B : X.LocalBranchingStructure Θ x) (i : B.ι),
      ∃ y : ℕ → Obj, (∀ k, y k ∈ B.M i ∧ y k ∈ EpGroupoid.supp Θ ∧ IsGoodPt X Θ (y k)) ∧
        Filter.Tendsto y Filter.atTop (nhds x)

end RoundTrip.V9_21
