import Polyfold.Chapter16.BranchedSuborbifold
import Polyfold.Chapter9.HalfCircleWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.5, Remark 9.5.19 (p. 451) and §16.4, Theorem 16.4.6 (p. 732).
Numbers and pages are the 2021 text's.

# Stokes on polyfolds and the partitions of unity of Remark 9.5.19

Theorem 16.4.6 is printed for every polyfold `(Z, c)` (standing assumptions: `|X|` paracompact
and (ZHOU)), and is justified in the text by the sentence before it: Stokes holds on the
ep-groupoid level.  The ep-groupoid theorems, Theorems 9.5.17 and 9.5.18, assume that `X`
admits sc-smooth partitions of unity, and Remark 9.5.19 says that this assumption is very likely
not needed, sketches how one might remove it (smooth partitions of unity on `supp Θ` only), and
leaves the modification to the reader.  As we read it, Theorem 16.4.6 without partitions of unity
therefore rests on the point that Remark 9.5.19 leaves open; what the text proves is the case
with partitions of unity (`PolyfoldClass.OrientedRep.theorem_16_4_6_hyp` and its three companions).

This file states the open point and derives the printed theorem from it.

* `EP.StokesWithoutPartitions A`: the assertion of Remark 9.5.19 for one ep-groupoid, i.e.
  Theorems 9.5.17, 9.5.18 (`m ≥ 1`) and their `n = 1` forms for `X` without partitions of unity
  (the effective forms with (LUC), as in Theorem 9.5.18).
* `EP.stokesWithoutPartitions_of_hasScPartitionsOfUnity`: it holds when `X` admits sc-smooth
  partitions of unity (Theorems 9.5.17, 9.5.18).
* `EP.stokesWithoutPartitions_witness`: the half-plane, with a compact oriented `Θ` whose
  boundary `supp(∂Θ)` is non-empty.
* `PolyfoldClass.HasEpStokes c`: every model `(X, α) ∈ c` satisfies it.
* `PolyfoldClass.OrientedRep.theorem_16_4_6_of_epStokes`, `theorem_16_4_6_eff_of_epStokes`,
  `theorem_16_4_6_dim1_of_epStokes`, `theorem_16_4_6_eff_dim1_of_epStokes`: **Theorem 16.4.6 as
  printed** (all four identities, every compact tame oriented representative), from the ep-level
  assertion only; no partitions of unity on `c`.
* `PolyfoldClass.hasEpStokes_of_admitsScPartitionsOfUnity` and the witness
  `hasEpStokes_witness` (`[ℤ/3 ⋉ ℝ]`).
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

universe u

namespace Polyfold

namespace EP

open EpGroupoid

/-- **The assertion of Remark 9.5.19, 2021 p. 451 (2017: Remark 9.8)** for the ep-groupoid `A`:
the two Stokes formulas of Theorems 9.5.17 and 9.5.18 (boundary dimension `m ≥ 1`, and the case
`n = 1`) hold for every compact, tame, oriented branched ep⁺-subgroupoid, with no sc-smooth
partitions of unity on `X`; the effective forms with (LUC) as in Theorem 9.5.18. -/
structure StokesWithoutPartitions (A : EP.{u}) : Prop where
  /-- Theorem 9.5.17, `m ≥ 1`. -/
  stokes : ∀ {m : ℕ} (hm : 0 < m) {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty m),
    (A.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt hT hloc
        (A.epFormsInftyD m ω) =
      A.boundaryMeasure hm hΘ hcpt hT hloc ω univ
  /-- Theorem 9.5.18, `m ≥ 1`. -/
  stokesEff : ∀ {m : ℕ} (hm : 0 < m) (hLUC : A.X.IsLUC) {Θ : A.Obj → ℚ}
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty m),
    (A.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) hΘ hcpt hT
        (A.hloc_hasLUC hLUC hloc) (A.epFormsInftyD m ω) =
      A.boundaryMeasureEff hm hLUC hΘ hcpt hT hloc ω univ
  /-- Theorem 9.5.17, `n = 1`. -/
  stokesDim1 : ∀ {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty 0),
    (A.epFormsInftyEval (0 + 1)).tameBranchedIntegral (Nat.succ_pos 0) hΘ hcpt hT hloc
        (A.epFormsInftyD 0 ω) =
      A.boundaryBranchedMeasureDim1 hΘ hcpt hT hloc ω univ
  /-- Theorem 9.5.18, `n = 1`. -/
  stokesEffDim1 : ∀ {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x,
      C.Represents T ∧ C.rep.HasLUC)
    (ω : A.epFormsInfty 0),
    (A.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff (Nat.succ_pos 0) hΘ hcpt hT hloc
        (A.epFormsInftyD 0 ω) =
      A.boundaryBranchedMeasureEffDim1 hΘ hcpt hT hloc ω univ

/-- **With sc-smooth partitions of unity the assertion of Remark 9.5.19 holds**: these are
Theorems 9.5.17 and 9.5.18 (and their `n = 1` forms). -/
theorem stokesWithoutPartitions_of_hasScPartitionsOfUnity (A : EP.{u})
    (hPU : A.X.HasScPartitionsOfUnity) : A.StokesWithoutPartitions where
  stokes hm _ _ hΘ hcpt hT hloc ω := A.theorem_9_5_17 hm hPU hΘ hcpt hT hloc ω
  stokesEff hm hLUC _ _ hΘ hcpt hT hloc ω := A.theorem_9_5_18 hm hPU hLUC hΘ hcpt hT hloc ω
  stokesDim1 hΘ hcpt hT hloc ω := A.theorem_9_5_17_dim1 hPU hΘ hcpt hT hloc ω
  stokesEffDim1 hΘ hcpt hT hloc ω := A.theorem_9_5_18_dim1 hPU hΘ hcpt hT hloc ω

/-- **The assertion of Remark 9.5.19 in a case with boundary**: the half-plane `[0, ∞) × ℝ`
(trivial ep-groupoid) satisfies it, and its compact oriented half-circle `Θ` has
`supp(∂Θ) ≠ ∅`. -/
theorem stokesWithoutPartitions_witness :
    K2Arc.AA.StokesWithoutPartitions ∧
      (supp (K2Arc.AA.X.boundaryTheta K2Arc.thetaA)).Nonempty :=
  ⟨K2Arc.AA.stokesWithoutPartitions_of_hasScPartitionsOfUnity K2Arc.arc_hasScPartitionsOfUnity,
    K2Arc.arc_boundary_nonempty⟩

end EP

namespace PolyfoldClass

open EpGroupoid MPolyfold

variable {Z : Type u} [TopologicalSpace Z]

/-- **Stokes on the ep-groupoid level** for the polyfold `(Z, c)`: every model `(X, α) ∈ c`
satisfies the assertion of Remark 9.5.19 (the sentence before Theorem 16.4.6). -/
def HasEpStokes (c : PolyfoldClass Z) : Prop :=
  ∀ p : PolyfoldStructure Z, (⟦p⟧ : PolyfoldClass Z) = c → p.X.StokesWithoutPartitions

/-- A polyfold admitting sc-smooth partitions of unity (Definition 16.1.5) has Stokes on the
ep-groupoid level. -/
theorem hasEpStokes_of_admitsScPartitionsOfUnity {c : PolyfoldClass Z}
    (hPU : c.AdmitsScPartitionsOfUnity) : c.HasEpStokes := fun p hp =>
  p.X.stokesWithoutPartitions_of_hasScPartitionsOfUnity ((c.definition_16_1_5_two).1 hPU p hp)

/-- **The hypothesis `HasEpStokes` is satisfiable**: `[ℤ/3 ⋉ ℝ]`. -/
theorem hasEpStokes_witness : PolyfoldStructure.z3Polyfold.HasEpStokes :=
  hasEpStokes_of_admitsScPartitionsOfUnity
    OrientedRep.theorem_16_4_6_hyp_witness

namespace OrientedRep

variable {c : PolyfoldClass Z} {m : ℕ}

/-- **2021 Theorem 16.4.6 (Stokes), p. 732 (2017: Theorem 16.5), branched integration,
`n ≥ 2`, as printed**, from Stokes on the ep-groupoid level (`HasEpStokes`, the assertion of
Remark 9.5.19) with no partitions of unity on `c`: `∫_θ̂ dτ = ∫_∂θ̂ τ`. -/
theorem theorem_16_4_6_of_epStokes (h : c.HasEpStokes) (a : OrientedRep c) (hm : 0 < m)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (m + 1))
    (τ : ScForm c m) :
    a.integral (Nat.succ_pos m) hcpt hloc (ScForm.d τ) = a.boundaryIntegral hm hcpt hloc τ := by
  unfold integral boundaryIntegral
  rw [toStructure_d]
  exact (h a.p a.mem).stokes hm a.A.isBranchedEpSubgroupoid hcpt a.A.isOrientation hloc _

/-- **Theorem 16.4.6, effective branched integration, `n ≥ 2`, as printed**, from `HasEpStokes`:
`∮_θ̂ dτ = ∮_∂θ̂ τ`.  (LUC) comes from (ZHOU). -/
theorem theorem_16_4_6_eff_of_epStokes (h : c.HasEpStokes) (a : OrientedRep c) (hm : 0 < m)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (m + 1))
    (τ : ScForm c m) :
    a.integralEff (Nat.succ_pos m) hcpt hloc (ScForm.d τ) =
      a.boundaryIntegralEff hm hcpt hloc τ := by
  unfold integralEff boundaryIntegralEff
  rw [toStructure_d]
  exact (h a.p a.mem).stokesEff hm (a.p.X.X.proposition_7_4_10_of_isZhou a.p.isZhou)
    a.A.isBranchedEpSubgroupoid hcpt a.A.isOrientation hloc _

/-- **Theorem 16.4.6, branched integration, `n = 1`, as printed**, from `HasEpStokes`. -/
theorem theorem_16_4_6_dim1_of_epStokes (h : c.HasEpStokes) (a : OrientedRep c)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (0 + 1))
    (τ : ScForm c 0) :
    a.integral (Nat.succ_pos 0) hcpt hloc (ScForm.d τ) = a.boundaryIntegralDim1 hcpt hloc τ := by
  unfold integral boundaryIntegralDim1
  rw [toStructure_d]
  exact (h a.p a.mem).stokesDim1 a.A.isBranchedEpSubgroupoid hcpt a.A.isOrientation hloc _

/-- **Theorem 16.4.6, effective branched integration, `n = 1`, as printed**, from
`HasEpStokes`. -/
theorem theorem_16_4_6_eff_dim1_of_epStokes (h : c.HasEpStokes) (a : OrientedRep c)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (0 + 1))
    (τ : ScForm c 0) :
    a.integralEff (Nat.succ_pos 0) hcpt hloc (ScForm.d τ) =
      a.boundaryIntegralEffDim1 hcpt hloc τ := by
  unfold integralEff boundaryIntegralEffDim1
  rw [toStructure_d]
  exact (h a.p a.mem).stokesEffDim1 a.A.isBranchedEpSubgroupoid hcpt a.A.isOrientation _ _

end OrientedRep

end PolyfoldClass

end Polyfold
