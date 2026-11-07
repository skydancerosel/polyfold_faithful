import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_58

/-!
Round trip for V7_58 (Theorem 7.4: sc-smooth partitions of unity of an ep-groupoid).

`A` is the type of `EpGroupoid.theorem_7_4` at universe `0`: paracompact orbit space and
`X.PObj.AdmitsScPartitionsOfUnity` imply `X.HasScPartitionsOfUnity`.  B has the same hypotheses
(the project's `HasParacompactOrbitSpace` and `AdmitsScPartitionsOfUnity`) and B's own reading
`HasScPUB` of Definition 7.16 as conclusion; the two conclusions agree (`hasScPUB_iff`, the
argument of V7_56: invariance `β(s φ) = β(t φ)` versus `IsoB y z → β z = β y`, everything else
literally the same).  Both directions are this rephrasing applied to the hypothesis.
-/

namespace RoundTrip.V7_58
open Polyfold

/-- The listed theorem (universe `0`). -/
def A : Prop := type_of% @Polyfold.EpGroupoid.theorem_7_4.{0}

theorem A_holds : A := @Polyfold.EpGroupoid.theorem_7_4.{0}

theorem hasScPUB_iff {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor) :
    X.HasScPartitionsOfUnity ↔ HasScPUB X := by
  constructor
  · intro h Λ U hUo hUs hcov
    obtain ⟨β, hsub, hsm, hW, hinv⟩ := h Λ U hUo hUs hcov
    exact ⟨β, hsub, hsm, hW, fun l y z ⟨φ, hy, hz⟩ => hy ▸ hz ▸ (hinv l φ).symm⟩
  · intro h ι U hUo hUs hcov
    obtain ⟨β, hsub, hsm, hW, hinv⟩ := h ι U hUo hUs hcov
    exact ⟨β, hsub, hsm, hW, fun i φ => (hinv i _ _ ⟨φ, rfl, rfl⟩).symm⟩

theorem A_to_B : A → B := fun hA _ _ _ _ _ _ _ _ X hp hpu =>
  (hasScPUB_iff X).1 (hA X hp hpu)

theorem B_to_A : B → A := fun hB {Obj Mor} _ _ _ _ _ _ X hp hpu =>
  (hasScPUB_iff X).2 (hB Obj Mor X hp hpu)

#rt_check RoundTrip.V7_58.A_to_B [Polyfold.EpGroupoid.theorem_7_4]
#rt_check RoundTrip.V7_58.B_to_A [Polyfold.EpGroupoid.theorem_7_4]
#rt_overlap RoundTrip.V7_58.B_to_A [Polyfold.EpGroupoid.theorem_7_4]

end RoundTrip.V7_58
