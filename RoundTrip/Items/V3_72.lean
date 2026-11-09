import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_72

/-!
Round trip for V3_72 (Theorem 3.27 with locally constant dimension).  `A` is the conjunction of
the types of `Polyfold.theorem_3_2_3_loc_of_isRegular` (universe `u_1` at `0`),
`Polyfold.MPolyfold.theorem_3_2_3_loc_isSubMPolyfold`, `Polyfold.MPolyfold.theorem_3_2_3_loc_isTame`,
`Polyfold.MPolyfold.theorem_3_2_3_loc_isManifoldWithCornersLoc` and
`Polyfold.MPolyfold.theorem_3_2_3_loc_atlas_equiv` (universe `u` at `0`);
`Polyfold.MPolyfold.IsManifoldWithCornersLoc` is vocabulary.

Neither direction is proved.  The gap is the one found in V3_24 for `theorem_3_2_3_of_isRegular`, unchanged by
the passage to locally constant dimension.

* `A → B` fails at A's hypothesis.  Every theorem of A assumes that each point of `M` carries
  project data `TangentGermChart M x n` (some `n`) satisfying `IsRegular`: (a) `δ` sc-smooth on
  all of `V` in the set sense and (b) `π(O) ⊆ C` for the projection `π` along `Y`.  B assumes only
  the blind Definition 3.25 (`HasTangentGermPropertyB`: `δ` an sc-smooth germ on one germ of
  neighbourhoods, no condition on `π(O)`) and tameness of `X`.
  - (a) is not the obstacle: after converting a blind datum into a project `TangentGermChart`
    (the glue of V3_22: the sc-complement is closed, the fixed germ gives the project's
    `IsScInftyGermAt`, `Dδ(0) = 0` by uniqueness), `TangentGermChart.exists_isRegular_of_locally`
    (not an item theorem here) shrinks it to a datum whose `δ` is sc-smooth on the shrunk `V'`;
    its proof of (a) does not use (b).
  - (b) is the genuine gap: it holds for some good complement of `N` (the project's
    `exists_goodComplement_projectsInto`), but not for B's given `Y` (Finding 83:
    `C = [0,∞)³`, `N = ℝ(1,1,1)`, `Y = {x + y − z = 0}`), and replacing `Y` means re-graphing `M`
    over `N` along a new complement (an inverse function theorem on a partial quadrant with a
    germ-smooth `δ`), which is new mathematics.  The hypothesis (b) is satisfiable (it is automatic
    when `C = E`, and the project produces it for solution sets, `theorem_3_6_8_two`), so A is not
    vacuous; but B's hypotheses do not supply it.  Whether B itself holds without (b) is open (the
    text's proof needs `Σ = {z ∈ O | πz ∈ V}` relatively open in `O`, which (b) provides).
  - B's chart clause is claimed for **every** blind datum (`IsProjChartAt`, on some
    neighbourhood of `x`), A's (`theorem_3_2_3_loc_of_isRegular`, last clause) only for regular data; with (b)
    this would again follow by shrinking.  B's `HasCornerStructureOfDim n` (all charts of
    dimension `n`) is stronger than A's `IsManifoldWithCornersLoc` (finite-dimensional charts), but
    is recoverable from A's chart clause by taking the atlas of the charts `π ∘ φ` (glue).
* `B → A` fails: A's theorems need no tameness of `X` (B assumes `PX.IsTame`), allow the dimension
  to vary from point to point (B fixes `n`), and take project data with `k`-dependent germ
  neighbourhoods (`IsScInftyGermAt`), which B's blind data (one fixed germ) need not provide (the
  project ⇒ text direction of V3_22, not proved there); A's `atlas_equiv` is about the specific
  atlas `germAtlasLoc`, which B does not mention.
-/

namespace RoundTrip.V3_72
open Polyfold

/-- The project's statement: the listed theorems, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_2_3_loc_of_isRegular.{0} ∧
    type_of% @Polyfold.MPolyfold.theorem_3_2_3_loc_isSubMPolyfold.{0} ∧
    type_of% @Polyfold.MPolyfold.theorem_3_2_3_loc_isTame.{0} ∧
    type_of% @Polyfold.MPolyfold.theorem_3_2_3_loc_isManifoldWithCornersLoc.{0} ∧
    type_of% @Polyfold.MPolyfold.theorem_3_2_3_loc_atlas_equiv.{0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_2_3_loc_of_isRegular.{0}, @Polyfold.MPolyfold.theorem_3_2_3_loc_isSubMPolyfold.{0},
    @Polyfold.MPolyfold.theorem_3_2_3_loc_isTame.{0},
    @Polyfold.MPolyfold.theorem_3_2_3_loc_isManifoldWithCornersLoc.{0},
    @Polyfold.MPolyfold.theorem_3_2_3_loc_atlas_equiv.{0}⟩

end RoundTrip.V3_72
