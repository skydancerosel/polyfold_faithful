import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_68

/-!
Round trip for V7_68 (Corollary 7.3: ep-groupoids whose object M-polyfold has an sc-Hilbert
atlas).

`A` is the conjunction of the types, universes at `0`, of the listed theorems:
`EpGroupoid.corollary_7_6_6` (paracompact `|X|` and, for every `x`, a chart `φ` of the structure
with `x ∈ dom φ`, `‖v‖² = b(v, v)` on `E₀` for a continuous bilinear `b`, **and
`GodefroyTroyanskiWhitfieldZizlerStatement (φ.model.E 0) ⊤`**, imply `HasScPartitionsOfUnity`),
`MPolyfold.admitsScPartitionsOfUnity_of_hilbert` (the same chart hypothesis on any M-polyfold
gives `AdmitsScPartitionsOfUnity`), and `EpGroupoid.corollary_7_6_6_hypotheses_rn` (satisfiability
on the trivial ep-groupoid on `ℝ¹`).  `GodefroyTroyanskiWhitfieldZizlerStatement` is a definition
(the cited Theorem 5.14 [5.43] for `E₀`, an explicit hypothesis).

`B → A`: the charts of the structure with a Hilbert `E₀` form an atlas (pairwise compatible by
`MPolyfold.IsChart.compatible`) equivalent to the given one (`MAtlas.equiv_iff`); a bilinear `b`
with `‖v‖² = b(v, v)` gives the parallelogram identity; B's partition of unity is repackaged as a
Mathlib `PartitionOfUnity` as in V7_65.  For the M-polyfold statement B is applied to the trivial
ep-groupoid `EpGroupoid.trivial PX` (whose `PObj` is `PX` by `rfl`).  The satisfiability conjunct
is proved from `hasParacompactOrbitSpace_trivial` and `rnPolyfold_one_hilbert_hypothesis` (not
from B).  The GTWZ hypothesis of A is simply dropped.

`A → B` is not proved: A needs `GodefroyTroyanskiWhitfieldZizlerStatement E₀ ⊤`
(WCG + `C^∞` bump ⇒ `C^∞` partitions of unity on `E₀`) for the charts' `E₀`, which B does not
assume and which for a general (non-separable) Hilbert space is a deep theorem not in Mathlib or
the project.
-/

namespace RoundTrip.V7_68
open Polyfold Set

/-- The project's Corollary 7.3, its M-polyfold ingredient and the satisfiability witness,
universes at `0`. -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.corollary_7_6_6.{0}) ∧
  (type_of% @Polyfold.MPolyfold.admitsScPartitionsOfUnity_of_hilbert.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.corollary_7_6_6_hypotheses_rn)

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.corollary_7_6_6.{0},
    @Polyfold.MPolyfold.admitsScPartitionsOfUnity_of_hilbert.{0},
    @Polyfold.EpGroupoid.corollary_7_6_6_hypotheses_rn⟩

/-- A bilinear form with `‖v‖² = b(v, v)` gives the parallelogram identity. -/
theorem isHilbertNormB_of_bilinear {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hb : ∀ v, ‖v‖ ^ 2 = b v v) : IsHilbertNormB E := by
  intro x y
  simp only [← sq, hb, map_add, map_sub, add_apply, sub_apply]
  ring

/-- The chart hypothesis of A gives B's Hilbert atlas. -/
theorem hasHilbertAtlasB_of {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    {P : MPolyfold Z}
    (h : ∀ x, ∃ φ : MChart Z, P.IsChart φ ∧ x ∈ φ.source ∧
      (∃ b : φ.model.E 0 →L[ℝ] φ.model.E 0 →L[ℝ] ℝ, ∀ v, ‖v‖ ^ 2 = b v v) ∧
      GodefroyTroyanskiWhitfieldZizlerStatement (φ.model.E 0) ⊤) :
    HasHilbertAtlasB P := by
  let A : MAtlas Z :=
    { charts := {φ | P.IsChart φ ∧ IsHilbertNormB (φ.model.E.lvl 0)}
      compatible := fun φ hφ ψ hψ => MPolyfold.IsChart.compatible P hφ.1 hψ.1
      cover := fun x => by
        obtain ⟨φ, hφ, hx, ⟨b, hb⟩, -⟩ := h x
        exact ⟨φ, ⟨hφ, isHilbertNormB_of_bilinear b hb⟩, hx⟩ }
  exact ⟨A, (MAtlas.equiv_iff _ _).2 fun φ hφ ψ hψ => hφ.1 ψ hψ, fun φ hφ => hφ.2⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X hpara h ι U hUo hUs hcov
    obtain ⟨-, hpou⟩ := hB Obj Mor X hpara (hasHilbertAtlasB_of h)
    obtain ⟨β, ⟨hsm, h0, h1, hW, hinv⟩, hsub⟩ := hpou ι U hUo hUs hcov
    have hlf : LocallyFinite fun i => Function.support (β i) := by
      intro y
      obtain ⟨W, hWo, -, hyW, hfin⟩ := hW y
      exact ⟨W, hWo.mem_nhds hyW, hfin.subset fun i ⟨z, hz⟩ =>
        ⟨z, hz.2, subset_tsupport _ hz.1⟩⟩
    let ρ : PartitionOfUnity ι Obj :=
      { toFun := fun i => ⟨β i, continuousOn_univ.1 (hsm i).continuousOn⟩
        locallyFinite' := hlf
        nonneg' := fun i y => h0 i y
        sum_eq_one' := fun y _ => h1 y
        sum_le_one' := fun y => (h1 y).le }
    exact ⟨ρ, hsub, hsm, hW, hinv⟩
  · intro Z _ _ _ PX h
    exact (hB Z Z (EpGroupoid.trivial PX) (EpGroupoid.hasParacompactOrbitSpace_trivial PX)
      (hasHilbertAtlasB_of h)).1
  · exact ⟨EpGroupoid.hasParacompactOrbitSpace_trivial _, rnPolyfold_one_hilbert_hypothesis⟩

#rt_check RoundTrip.V7_68.B_to_A [Polyfold.EpGroupoid.corollary_7_6_6,
  Polyfold.MPolyfold.admitsScPartitionsOfUnity_of_hilbert,
  Polyfold.EpGroupoid.corollary_7_6_6_hypotheses_rn]
#rt_overlap RoundTrip.V7_68.B_to_A [Polyfold.EpGroupoid.corollary_7_6_6,
  Polyfold.MPolyfold.admitsScPartitionsOfUnity_of_hilbert,
  Polyfold.EpGroupoid.corollary_7_6_6_hypotheses_rn]

end RoundTrip.V7_68
