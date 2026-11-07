import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_65

/-!
Round trip for V7_65 (Theorem 7.6 = Theorem 7.4: sc-smooth partitions of unity of an ep-groupoid).

`A` is the type of `Polyfold.EpGroupoid.theorem_7_6` at universe `0`: for every ep-groupoid
`X : EpGroupoid Obj Mor` (`Obj Mor : Type`) with `X.HasParacompactOrbitSpace` (by definition
`ParacompactSpace X.OrbitSpace`) and `X.PObj.AdmitsScPartitionsOfUnity`, `X.HasScPartitionsOfUnity`
(Definition 7.16: every saturated open cover indexed by a `Type` has a subordinate Mathlib
`PartitionOfUnity` of sc-smooth functions with saturated neighbourhoods meeting finitely many
supports and `β(s φ) = β(t φ)`).  `B` has the same hypotheses and asks for a family of real
functions `β_λ` that are sc-smooth, `≥ 0`, with `∑ᶠ β_λ = 1`, the same two conditions of
Definition 7.16 and `tsupport β_λ ⊆ U_λ`.  The only glue is packaging the functions as a Mathlib
`PartitionOfUnity`: continuity from sc-smoothness, local finiteness of the supports from the
saturated-neighbourhood condition.
-/

namespace RoundTrip.V7_65
open Polyfold

/-- The project's Theorem 7.6, universes at `0`. -/
def A : Prop := type_of% @Polyfold.EpGroupoid.theorem_7_6.{0}

theorem A_holds : A := @Polyfold.EpGroupoid.theorem_7_6.{0}

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X hpara hpu Λ U hUo hUs hcov
  obtain ⟨β, hsub, hsm, hW, hinv⟩ := hA X hpara hpu Λ U hUo hUs hcov
  exact ⟨fun l y => β l y, ⟨hsm, fun l y => β.nonneg l y,
    fun y => β.sum_eq_one (Set.mem_univ y), hW, hinv⟩, hsub⟩

theorem B_to_A : B → A := by
  intro hB Obj Mor _ _ _ _ _ _ X hpara hpu ι U hUo hUs hcov
  obtain ⟨β, ⟨hsm, h0, h1, hW, hinv⟩, hsub⟩ := hB Obj Mor X hpara hpu ι U hUo hUs hcov
  have hlf : LocallyFinite fun i => Function.support (β i) := by
    intro y
    obtain ⟨W, hWo, -, hyW, hfin⟩ := hW y
    exact ⟨W, hWo.mem_nhds hyW, hfin.subset fun i ⟨z, hz⟩ => ⟨z, hz.2, subset_tsupport _ hz.1⟩⟩
  let ρ : PartitionOfUnity ι Obj :=
    { toFun := fun i => ⟨β i, continuousOn_univ.1 (hsm i).continuousOn⟩
      locallyFinite' := hlf
      nonneg' := fun i y => h0 i y
      sum_eq_one' := fun y _ => h1 y
      sum_le_one' := fun y => (h1 y).le }
  exact ⟨ρ, hsub, hsm, hW, hinv⟩

#rt_check RoundTrip.V7_65.A_to_B [Polyfold.EpGroupoid.theorem_7_6]
#rt_check RoundTrip.V7_65.B_to_A [Polyfold.EpGroupoid.theorem_7_6]
#rt_overlap RoundTrip.V7_65.B_to_A [Polyfold.EpGroupoid.theorem_7_6]
#rt_overlap RoundTrip.V7_65.A_to_B [Polyfold.EpGroupoid.theorem_7_6]

end RoundTrip.V7_65
