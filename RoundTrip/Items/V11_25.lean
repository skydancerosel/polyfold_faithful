import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_25

/-! Round trip for V11_25 (2021 Theorem 11.3.9, p. 542: oriented boundaries `∂Θ̂` under
generalized isomorphisms, for a representative).

The item lists the definition `MPolyfold.IsBoundaryTransfer` (vocabulary) and five theorems; `A`
is the conjunction of their types, universes at `0`: `isBoundaryTransfer_id` (the identity
transfers every `bd`), `EpFunctor.pushSection_boundaryLift`, `pullSection_boundaryLift`
(`F_*`, `F^*` commute with `boundaryLift` along an equivalence, for boundary operations that the
fibre maps `Tψ ∘ TF(x)` resp. `TF(x)⁻¹` transfer), `EPLoc.theorem_11_3_9_push`, `_pull`
(on a representative `d = X ←F A →Φ Y` with `Φ` an equivalence, for `Θ` with
`HasIndependentTangentSums` and an orientation `T`, and boundary operations `bd`, `bdA`, `bd'` on
`X`, `d.A`, `Y` satisfying `IsBoundaryTransfer` along `TF(a)⁻¹` and along `Tψ ∘ TΦ(a)` at every
smooth `a`).  `IsBoundaryTransfer x y f bd bd'` says `f_*` preserves "degree `d_M = 1`"
(`HasSubDegree`) both ways *and* `bd'(f_* L) = f_*(bd L)` in degree `1`.

`B`: on every representative of a generalized isomorphism, for boundary operations `bdX`, `bdY`
natural (`IsNaturalBdB`) for all sc-diffeomorphisms between open subsets of `X` and `Y` (in both
directions, in degree `1`), and for tame oriented branched `Θ` (no independence hypothesis):
`∂(d_*Θ) = d_*(∂Θ)`, `boundaryLift bdY (d_*T) = d_*(boundaryLift bdX T)`, and the same for `d^*`.

* `A → B` fails.  `B`'s hypotheses do not give `A`'s: (i) no `HasIndependentTangentSums` (as in
  V11_24: `boundaryTheta` and the tangent sums are read off chosen local branching structures);
  (ii) `B` has no boundary operation on the middle ep-groupoid `d.A`, which `A`'s
  `theorem_11_3_9_*` need (one would have to construct `bdA` by transport along `TF`);
  (iii) `IsNaturalBdB` does not say that sc-diffeomorphisms preserve `HasSubDegree … 1` (a smooth
  submanifold with tame induced structure and `d_M = 1` through the point), which
  `IsBoundaryTransfer` requires; that invariance (tame induced structures and `d_M` under
  sc-diffeomorphisms between different M-polyfolds) is, by the project's own header, not
  formalized.  So deriving `B` would need new mathematics (Theorem 9.2.1's independence, the
  invariance of `HasSubDegree`, and the identification of `Tψ ∘ TΦ ∘ TF⁻¹` with the tangent map of
  a local sc-diffeomorphism `X ⊇ W → W' ⊆ Y` to apply naturality), not glue.
* `B → A` fails: `A`'s theorems hold for *arbitrary* boundary operations satisfying the
  pointwise transfer conditions along the maps of one equivalence or diagram, and for arbitrary
  `GrHat` sections (`pushSection_boundaryLift`); `B` concludes only for operations natural for
  all sc-diffeomorphisms between `X` and `Y`, which the transfer hypotheses do not give.  Only
  `isBoundaryTransfer_id` (definitional) would follow, by re-proving it outright; no `B_to_A` is
  given.
* Both hypotheses are satisfiable: `isNaturalBdB_id` (identity operations are natural in `B`'s
  sense), and `A`'s `isBoundaryTransfer_id`. -/

namespace RoundTrip.V11_25
open Polyfold Polyfold.EPLocalization

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.isBoundaryTransfer_id.{0}) ∧
  (type_of% @Polyfold.EpFunctor.pushSection_boundaryLift.{0}) ∧
  (type_of% @Polyfold.EpFunctor.pullSection_boundaryLift.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_9_push.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_9_pull.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.isBoundaryTransfer_id.{0},
    @Polyfold.EpFunctor.pushSection_boundaryLift.{0},
    @Polyfold.EpFunctor.pullSection_boundaryLift.{0},
    @Polyfold.EPLocalization.EPLoc.theorem_11_3_9_push.{0},
    @Polyfold.EPLocalization.EPLoc.theorem_11_3_9_pull.{0}⟩

/-- `B`'s naturality hypothesis is satisfiable: the identity operations are natural. -/
theorem isNaturalBdB_id {X Y : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : MPolyfold X) (Q : MPolyfold Y) :
    IsNaturalBdB P Q id id := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl

end RoundTrip.V11_25
