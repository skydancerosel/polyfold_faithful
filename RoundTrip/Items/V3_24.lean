import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_24

/-!
Round trip for V3_24 (Theorem 3.27).  `A` is the conjunction of the types of the listed theorems
`Polyfold.theorem_3_27`, `Polyfold.theorem_3_27_isSubMPolyfold`,
`Polyfold.MPolyfold.theorem_3_27_isChart`, `Polyfold.MPolyfold.theorem_3_27_isTame`,
`Polyfold.MPolyfold.theorem_3_27_isManifoldWithCorners`, `Polyfold.MPolyfold.theorem_3_27_degIndex`
and `Polyfold.isScSmooth_subtype_val`, universes instantiated at `0`.  (`TangentGermChart.IsRegular`,
`TangentGermChart.chart` and `MPolyfold.IsManifoldWithCorners` are vocabulary.)

Neither direction is proved.

* `A → B` fails at the hypothesis: every theorem of A assumes that every point of `M` carries
  tangent-germ data satisfying `TangentGermChart.IsRegular` ((a) `δ` sc-smooth on all of `V` in the
  set sense, (b) the projection `π` along `Y` maps the retract `O` into `C`).  B's hypothesis is
  Definition 3.25 only (`HasTangentGermProperty`: some data at every point, `δ` an sc^∞-germ with
  `k`-dependent neighbourhoods, no condition on `π(O)`), plus tameness of `X`.  B's clause (2) is
  also claimed for *every* datum, A's only for regular data.  `A_to_B_of_allRegular` below shows
  that this is the only gap: under the extra hypothesis "every datum is regular" A gives B's
  conclusion (tameness of `X` is not needed).
* `B → A` fails: B needs `X` tame (A's theorems do not assume it; the data only carry a tame
  retract at the points of `M`), B's chart clause gives a chart of `M` on *some* neighbourhood of
  the centre `x` (A: the specific chart `d.chart` on the whole `U₀`), and A's conjuncts
  `theorem_3_27_degIndex` and `isScSmooth_subtype_val` are not about B's content at all.
-/

namespace RoundTrip.V3_24
open Polyfold

/-- The project's statement: the theorems listed for Theorem 3.27, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_27.{0} ∧ type_of% @Polyfold.theorem_3_27_isSubMPolyfold.{0} ∧
    type_of% @Polyfold.MPolyfold.theorem_3_27_isChart.{0} ∧
    type_of% @Polyfold.MPolyfold.theorem_3_27_isTame.{0} ∧
    type_of% @Polyfold.MPolyfold.theorem_3_27_isManifoldWithCorners.{0} ∧
    type_of% @Polyfold.MPolyfold.theorem_3_27_degIndex.{0} ∧
    type_of% @Polyfold.isScSmooth_subtype_val

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_27.{0}, @Polyfold.theorem_3_27_isSubMPolyfold.{0},
    @Polyfold.MPolyfold.theorem_3_27_isChart.{0}, @Polyfold.MPolyfold.theorem_3_27_isTame.{0},
    @Polyfold.MPolyfold.theorem_3_27_isManifoldWithCorners.{0},
    @Polyfold.MPolyfold.theorem_3_27_degIndex.{0}, @Polyfold.isScSmooth_subtype_val⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- B's conclusion for an empty set: the empty atlas. -/
theorem empty_case {S : Set X} (hS : ¬ S.Nonempty) :
    ∃ (hsub : PX.IsSubMPolyfold S) (_ : ParacompactSpace S),
      (PX.subPolyfold hsub).IsTame ∧ (PX.subPolyfold hsub).HasCornerStructure := by
  have hsub : PX.IsSubMPolyfold S := fun a ha => absurd ⟨a, ha⟩ hS
  have hpc := PX.paracompactSpace_subtype S
  have hcorner : (PX.subPolyfold hsub).HasCornerStructure := by
    refine ⟨⟨∅, fun φ hφ => absurd hφ (Set.notMem_empty φ), fun y => absurd ⟨y.1, y.2⟩ hS⟩,
      (MAtlas.equiv_iff _ _).2 fun φ hφ => absurd hφ (Set.notMem_empty φ),
      fun φ hφ => absurd hφ (Set.notMem_empty φ)⟩
  exact ⟨hsub, hpc, hcorner.isTame, hcorner⟩

end Glue

/-- **Diagnostic** (not a direction of the round trip): B's conclusion follows from A's first
conjunct (`theorem_3_27`; taken alone because the types of A's other conjuncts mention
`theorem_3_27_isSubMPolyfold`, which would trip `#rt_check`) when every
tangent-germ datum at every point of `M` is regular (`IsRegular`); tameness of `X` is not used.
So the whole gap `A → B` is the regularity hypothesis of A (and B's chart claim for non-regular
data). -/
theorem A_to_B_of_allRegular (h327 : type_of% @Polyfold.theorem_3_27.{0}) {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] (PX : MPolyfold X) (M : Set X) (n : ℕ)
    (hT : PX.HasTangentGermProperty M n)
    (hreg : ∀ x ∈ M, ∀ d : PX.TangentGermChart M x n, d.IsRegular) :
    ∃ (hM : PX.IsSubMPolyfold M) (_ : ParacompactSpace M),
      (PX.subPolyfold hM).IsTame ∧ (PX.subPolyfold hM).HasCornerStructure ∧
      ∀ (x : X) (hx : x ∈ M) (d : PX.TangentGermChart M x n),
        letI := d.finiteDimensional
        IsSmoothChartAt (PX.subPolyfold hM) (Subtype.val ⁻¹' d.φ.model.C : Set d.N) ⟨x, hx⟩
          (fun y : M => d.π (d.φ.toPartialEquiv y)) := by
  have hM' : ∀ x ∈ M, ∃ d : PX.TangentGermChart M x n, d.IsRegular := fun x hx => by
    obtain ⟨d⟩ := hT.2 x hx
    exact ⟨d, hreg x hx d⟩
  by_cases hne : M.Nonempty
  · have := PX.paracompactSpace_subtype M
    obtain ⟨hsub, htame, hman, hchart⟩ := h327 PX hne hM'
    refine ⟨hsub, PX.paracompactSpace_subtype M, htame, hman.hasCornerStructure,
      fun x hx d => ?_⟩
    obtain ⟨hc, hxs⟩ := hchart x hx d (hreg x hx d) ⟨x, hx⟩
    let c := d.chart (hreg x hx d) ⟨x, hx⟩
    exact ⟨d.V, d.V_isRelOpenInQuadrant, c.toPartialEquiv, c.isOpen_source, rfl,
      c.continuousOn_toFun, c.continuousOn_invFun, hxs, fun y _ => rfl, hc⟩
  · obtain ⟨hsub, hpc, h1, h2⟩ := empty_case (PX := PX) hne
    exact ⟨hsub, hpc, h1, h2, fun x hx => absurd ⟨x, hx⟩ hne⟩

example (hA : A) : type_of% @Polyfold.theorem_3_27.{0} := hA.1

#rt_check RoundTrip.V3_24.A_to_B_of_allRegular [Polyfold.theorem_3_27,
  Polyfold.theorem_3_27_isSubMPolyfold, Polyfold.MPolyfold.theorem_3_27_isChart,
  Polyfold.MPolyfold.theorem_3_27_isTame, Polyfold.MPolyfold.theorem_3_27_isManifoldWithCorners,
  Polyfold.MPolyfold.theorem_3_27_degIndex, Polyfold.isScSmooth_subtype_val]

end RoundTrip.V3_24
