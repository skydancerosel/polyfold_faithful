import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_116

set_option maxSynthPendingDepth 3

/-! Round trip for V17_116 (2021 Theorem 17.6.10 and (17.92), p. 824: effective Stokes under
(LUC), `∮_Θ̂ d[ω] = ∮_{∂Θ̂} [ω]`).

The item lists thirteen theorems; `A` is the conjunction of their types, the polyfold theorems at
universe `0` (`B` lives on `GCT.{0}`), the `ℤ/3 ⋉ ℝ` witnesses having no universe parameter.
Conjuncts: **`theorem_17_6_10_all`** (`m ≥ 1`) and **`theorem_17_6_10_dim1_all`** (`n = 1`):
effective Stokes on the model of any covering family on which `Θ̂` is tame oriented (together the
main claim); `_book_all`, `_dim1_book_all` (the same for the integrals `integralEff`,
`boundaryIntegralEff(Dim1)` on `C`, computed on the family chosen by `IsTameOriented`);
`_of_epStokes`, `_dim1_of_epStokes`, `_hyp`, `_book`, `_book_hyp`, `_dim1_book` (the same under the
extra hypotheses `EP.StokesWithoutPartitions` / sc-smooth partitions of unity on a model, which
the `_all` forms remove); the witnesses `z3Model_hasScPartitionsOfUnity`,
`z3Model_stokesWithoutPartitions`, `z3Taut_hypotheses_17_6_10` (these hypotheses are satisfiable
for `ℤ/3 ⋉ ℝ`).

* `A_to_B`: `B` is `theorem_17_6_10_all ∧ theorem_17_6_10_dim1_all` at universe `0`.
* `B_to_A`: the `_all`, `_of_epStokes`, `_hyp` forms on a covering family are `B` (the extra
  hypotheses are dropped); the forms on `C` from `B` with
  `boundaryIntegralEff_eq_boundaryIntegralEffVia`, `boundaryIntegralEffDim1_eq_…` (Theorem 17.6.9;
  not item theorems), after unfolding `integralEff` to the family chosen by `IsTameOriented`.
  The three `ℤ/3` witnesses do not follow from `B` (they are facts about one example); they are
  re-proved outright by the project's proofs (`corollary_7_6_6_unconditional`,
  `rnPolyfold_one_hilbert_hypothesis`, `z3Taut_properties`,
  `EP.stokesWithoutPartitions_of_hasScPartitionsOfUnity`). -/

namespace RoundTrip.V17_116
open Polyfold
open Polyfold.GCT.PolyfoldConstruction Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_all.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_all.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book_all.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_book_all.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_of_epStokes.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_of_epStokes.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_hyp.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book_hyp.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_book.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.z3Model_hasScPartitionsOfUnity) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.z3Model_stokesWithoutPartitions) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.z3Taut_hypotheses_17_6_10)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_all.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_all.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book_all.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_book_all.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_of_epStokes.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_of_epStokes.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_hyp.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book_hyp.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_book.{0},
    @Polyfold.GCT.PolyfoldConstruction.z3Model_hasScPartitionsOfUnity,
    @Polyfold.GCT.PolyfoldConstruction.z3Model_stokesWithoutPartitions,
    @Polyfold.GCT.PolyfoldConstruction.z3Taut_hypotheses_17_6_10⟩

/-- The main claim: `theorem_17_6_10_all` and its `n = 1` case. -/
def AMain : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_all.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_all.{0})

theorem main_A_to_B (h : AMain) : B := by
  intro C S hL A hc
  exact ⟨fun m hm c ht ω => h.1 A hL c hm hc ht ω, fun c ht ω => h.2 A hL c hc ht ω⟩

theorem main_B_to_A (hB : B) : AMain :=
  ⟨fun {C S _m} A hL c hm hc ht ω => (hB C S hL A hc).1 _ hm c ht ω,
    fun {C S} A hL c hc ht ω => (hB C S hL A hc).2 c ht ω⟩

/-- Effective Stokes for the integrals on `C` (`m ≥ 1`), from `B`. -/
theorem book_of_B (hB : B) {C : GCT.{0}} {S : C.PolyfoldConstruction} {m : ℕ}
    (A : S.OrientedSubcategory) (hL : S.IsLUC) (hm : 0 < m) (hc : C.IsCompactBranched A.Θ)
    (h : A.IsTameOriented (m + 1)) (ω : S.catFormsInfty m) :
    A.integralEff hL (Nat.succ_pos m) hc h (S.catFormsInftyD m ω) =
      A.boundaryIntegralEff hL hm hc h ω :=
  ((hB C S hL A hc).1 _ hm h.choose h.choose_spec ω).trans
    (A.boundaryIntegralEff_eq_boundaryIntegralEffVia hL hm hc h h.choose h.choose_spec ω).symm

/-- Effective Stokes for the integrals on `C` (`n = 1`), from `B`. -/
theorem dim1_book_of_B (hB : B) {C : GCT.{0}} {S : C.PolyfoldConstruction}
    (A : S.OrientedSubcategory) (hL : S.IsLUC) (hc : C.IsCompactBranched A.Θ)
    (h : A.IsTameOriented (0 + 1)) (ω : S.catFormsInfty 0) :
    A.integralEff hL (Nat.succ_pos 0) hc h (S.catFormsInftyD 0 ω) =
      A.boundaryIntegralEffDim1 hL hc h ω :=
  ((hB C S hL A hc).2 h.choose h.choose_spec ω).trans
    (A.boundaryIntegralEffDim1_eq_boundaryIntegralEffDim1Via hL hc h h.choose h.choose_spec
      ω).symm

/-- `z3Model_hasScPartitionsOfUnity`, re-proved (the project's proof). -/
theorem z3Model_hasScPartitionsOfUnity' :
    (z3TautConstruction.modelEP z3Family.Ψ).X.HasScPartitionsOfUnity ∧
      Nonempty (z3TautConstruction.modelEP z3Family.Ψ).Obj := by
  refine ⟨EpGroupoid.corollary_7_6_6_unconditional _ ?_ fun x => ?_,
    ⟨⟨PUnit.unit, (0 : Fin 1 → ℝ)⟩⟩⟩
  · have := metrizableSpace_modelOrbitSpace_of_family (S := z3TautConstruction) (Ψ := z3Family.Ψ)
    let _ := TopologicalSpace.metrizableSpaceMetric
      (z3TautConstruction.modelEP z3Family.Ψ).X.OrbitSpace
    exact (inferInstance : ParacompactSpace (z3TautConstruction.modelEP z3Family.Ψ).X.OrbitSpace)
  · obtain ⟨i, y⟩ := x
    obtain ⟨φ, hφ, hy, hb, -⟩ := rnPolyfold_one_hilbert_hypothesis y
    exact ⟨MPolyfold.sigmaChart i φ, MPolyfold.IsChart.sigmaChart hφ, ⟨y, hy, rfl⟩, hb⟩

theorem B_to_A : B → A := fun hB =>
  ⟨(main_B_to_A hB).1, (main_B_to_A hB).2,
    -- `_book_all`
    fun A hL _c₀ hm hc h ω => book_of_B hB A hL hm hc h ω,
    -- `_dim1_book_all`
    fun A hL _c₀ hc h ω => dim1_book_of_B hB A hL hc h ω,
    -- `_dim1_of_epStokes`
    fun {C S} A hL c _hS hc ht ω => (hB C S hL A hc).2 c ht ω,
    -- `_of_epStokes`
    fun {C S _m} A hL c _hS hm hc ht ω => (hB C S hL A hc).1 _ hm c ht ω,
    -- `_hyp`
    fun {C S _m} A hL c _hPU hm hc ht ω => (hB C S hL A hc).1 _ hm c ht ω,
    -- `_book`
    fun A hL _c₀ _hS hm hc h ω => book_of_B hB A hL hm hc h ω,
    -- `_book_hyp`
    fun A hL _c₀ _hPU hm hc h ω => book_of_B hB A hL hm hc h ω,
    -- `_dim1_book`
    fun A hL _c₀ _hS hc h ω => dim1_book_of_B hB A hL hc h ω,
    z3Model_hasScPartitionsOfUnity',
    EP.stokesWithoutPartitions_of_hasScPartitionsOfUnity _ z3Model_hasScPartitionsOfUnity'.1,
    ⟨z3Taut_properties.2.1, z3Model_hasScPartitionsOfUnity'.1,
      EP.stokesWithoutPartitions_of_hasScPartitionsOfUnity _ z3Model_hasScPartitionsOfUnity'.1⟩⟩

theorem A_to_B : A → B := fun h => main_A_to_B ⟨h.1, h.2.1⟩

#rt_check RoundTrip.V17_116.main_A_to_B
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_book_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_of_epStokes,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_of_epStokes,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_hyp,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book_hyp,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_book,
   Polyfold.GCT.PolyfoldConstruction.z3Model_hasScPartitionsOfUnity,
   Polyfold.GCT.PolyfoldConstruction.z3Model_stokesWithoutPartitions,
   Polyfold.GCT.PolyfoldConstruction.z3Taut_hypotheses_17_6_10]
#rt_check RoundTrip.V17_116.main_B_to_A
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_book_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_of_epStokes,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_of_epStokes,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_hyp,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book_hyp,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_book,
   Polyfold.GCT.PolyfoldConstruction.z3Model_hasScPartitionsOfUnity,
   Polyfold.GCT.PolyfoldConstruction.z3Model_stokesWithoutPartitions,
   Polyfold.GCT.PolyfoldConstruction.z3Taut_hypotheses_17_6_10]
#rt_check RoundTrip.V17_116.A_to_B
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_book_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_of_epStokes,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_of_epStokes,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_hyp,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book_hyp,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_book,
   Polyfold.GCT.PolyfoldConstruction.z3Model_hasScPartitionsOfUnity,
   Polyfold.GCT.PolyfoldConstruction.z3Model_stokesWithoutPartitions,
   Polyfold.GCT.PolyfoldConstruction.z3Taut_hypotheses_17_6_10]
#rt_check RoundTrip.V17_116.B_to_A
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_book_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_of_epStokes,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_of_epStokes,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_hyp,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book_hyp,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_book,
   Polyfold.GCT.PolyfoldConstruction.z3Model_hasScPartitionsOfUnity,
   Polyfold.GCT.PolyfoldConstruction.z3Model_stokesWithoutPartitions,
   Polyfold.GCT.PolyfoldConstruction.z3Taut_hypotheses_17_6_10]
#rt_overlap RoundTrip.V17_116.B_to_A
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_book_all,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_of_epStokes,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_of_epStokes,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_hyp,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book_hyp,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_book,
   Polyfold.GCT.PolyfoldConstruction.z3Model_hasScPartitionsOfUnity,
   Polyfold.GCT.PolyfoldConstruction.z3Model_stokesWithoutPartitions,
   Polyfold.GCT.PolyfoldConstruction.z3Taut_hypotheses_17_6_10]

end RoundTrip.V17_116
