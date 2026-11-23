import Polyfold.Chapter9.StokesLocalPartitions
import Polyfold.Chapter9.StokesLocalPartitionsDimOne
import Polyfold.Chapter17.TameOrientedTransfer

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.5, Remark 9.5.19 (p. 451), §16.4, Theorem 16.4.6 (p. 732), §17.6, Theorems 17.6.7 (p. 823)
and 17.6.10 (p. 824).  Point G.153.  Numbers and pages are the 2021 text's.

# Stokes with no sc-smooth partitions of unity

Remark 9.5.19 says that the sc-smooth partitions of unity assumed in Theorems 9.5.17 and 9.5.18
are very likely not needed, since partitions of unity on the compact `supp Θ` suffice, and leaves
the modification to the reader.  It is carried out in `Polyfold/Chapter9`:
`EP.hasLocalPartitions` (partitions of unity near `supp Θ`, on every ep-groupoid),
`EP.LocalPartition.nonempty_localFormSystem` (the forms `β_k ω` near `supp Θ`),
`EP.stokes_of_localFormSystems` (the proof on p. 451 with them), and the same for `n = 1`.

* **`EP.stokesWithoutPartitions_all`**: the assertion of Remark 9.5.19 (Theorems 9.5.17, 9.5.18
  and their `n = 1` forms, with no partitions of unity) holds for every ep-groupoid.
* `PolyfoldClass.hasEpStokes_all`: Stokes on the ep-groupoid level for every polyfold.
* `PolyfoldClass.OrientedRep.theorem_16_4_6_all` and its three companions: **Theorem 16.4.6 as
  printed**.
* `GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_all`, `theorem_17_6_10_all` and
  their companions: **Theorems 17.6.7 and 17.6.10**, on a covering family and for the integrals
  on `C`.
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

universe u

namespace Polyfold

namespace EP

/-- **Remark 9.5.19, 2021 p. 451 (2017: Remark 9.8)**: Theorems 9.5.17 and 9.5.18 (pp. 449–450)
and their `n = 1` forms hold for every ep-groupoid, with no sc-smooth partitions of unity on
`X`. -/
theorem stokesWithoutPartitions_all (A : EP.{u}) : A.StokesWithoutPartitions where
  stokes hm _ _ hΘ hcpt hT hloc ω := A.theorem_9_5_17_all hm hΘ hcpt hT hloc ω
  stokesEff hm hLUC _ _ hΘ hcpt hT hloc ω := A.theorem_9_5_18_all hm hLUC hΘ hcpt hT hloc ω
  stokesDim1 hΘ hcpt hT hloc ω := A.theorem_9_5_17_dim1_all hΘ hcpt hT hloc ω
  stokesEffDim1 hΘ hcpt hT hloc ω := A.theorem_9_5_18_dim1_all hΘ hcpt hT hloc ω

end EP

namespace PolyfoldClass

variable {Z : Type u} [TopologicalSpace Z]

/-- **Stokes on the ep-groupoid level for every polyfold** (the sentence before Theorem 16.4.6,
2021 p. 732, with Remark 9.5.19). -/
theorem hasEpStokes_all (c : PolyfoldClass Z) : c.HasEpStokes := fun p _ =>
  p.X.stokesWithoutPartitions_all

namespace OrientedRep

variable {c : PolyfoldClass Z} {m : ℕ}

/-- **Theorem 16.4.6 (Stokes), 2021 p. 732 (2017: Theorem 16.5), branched integration, `n ≥ 2`,
as printed**: `∫_θ̂ dτ = ∫_∂θ̂ τ`, with no partitions of unity on `c`. -/
theorem theorem_16_4_6_all (a : OrientedRep c) (hm : 0 < m)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (m + 1))
    (τ : ScForm c m) :
    a.integral (Nat.succ_pos m) hcpt hloc (ScForm.d τ) = a.boundaryIntegral hm hcpt hloc τ :=
  theorem_16_4_6_of_epStokes c.hasEpStokes_all a hm hcpt hloc τ

/-- **Theorem 16.4.6, 2021 p. 732, effective branched integration, `n ≥ 2`, as printed**:
`∮_θ̂ dτ = ∮_∂θ̂ τ`. -/
theorem theorem_16_4_6_eff_all (a : OrientedRep c) (hm : 0 < m)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (m + 1))
    (τ : ScForm c m) :
    a.integralEff (Nat.succ_pos m) hcpt hloc (ScForm.d τ) =
      a.boundaryIntegralEff hm hcpt hloc τ :=
  theorem_16_4_6_eff_of_epStokes c.hasEpStokes_all a hm hcpt hloc τ

/-- **Theorem 16.4.6, 2021 p. 732, branched integration, `n = 1`, as printed.** -/
theorem theorem_16_4_6_dim1_all (a : OrientedRep c)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (0 + 1))
    (τ : ScForm c 0) :
    a.integral (Nat.succ_pos 0) hcpt hloc (ScForm.d τ) = a.boundaryIntegralDim1 hcpt hloc τ :=
  theorem_16_4_6_dim1_of_epStokes c.hasEpStokes_all a hcpt hloc τ

/-- **Theorem 16.4.6, 2021 p. 732, effective branched integration, `n = 1`, as printed.** -/
theorem theorem_16_4_6_eff_dim1_all (a : OrientedRep c)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (0 + 1))
    (τ : ScForm c 0) :
    a.integralEff (Nat.succ_pos 0) hcpt hloc (ScForm.d τ) =
      a.boundaryIntegralEffDim1 hcpt hloc τ :=
  theorem_16_4_6_eff_dim1_of_epStokes c.hasEpStokes_all a hcpt hloc τ

end OrientedRep

end PolyfoldClass

namespace GCT.PolyfoldConstruction.OrientedSubcategory

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {m : ℕ} (A : S.OrientedSubcategory)

/-- **Theorem 17.6.7 (Stokes), 2021 p. 823**, on a covering family, `[ω]` of degree `m ≥ 1`:
`∫_Θ̂ d[ω] = ∫_{∂Θ̂} [ω]`. -/
theorem theorem_17_6_7_all (c : S.CoveringFamily) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c (m + 1))
    (ω : S.catFormsInfty m) :
    A.integralVia c (Nat.succ_pos m) hcpt hloc (S.catFormsInftyD m ω) =
      A.boundaryIntegralVia c hm hcpt hloc ω :=
  A.theorem_17_6_7_of_epStokes c (S.modelEP c.Ψ).stokesWithoutPartitions_all hm hcpt hloc ω

/-- **Theorem 17.6.7 (Stokes), 2021 p. 823, for `n = 1`**, on a covering family. -/
theorem theorem_17_6_7_dim1_all (c : S.CoveringFamily) (hcpt : C.IsCompactBranched A.Θ)
    (hloc : A.IsTameOrientedVia c (0 + 1)) (ω : S.catFormsInfty 0) :
    A.integralVia c (Nat.succ_pos 0) hcpt hloc (S.catFormsInftyD 0 ω) =
      A.boundaryIntegralDim1Via c hcpt hloc ω :=
  A.theorem_17_6_7_dim1_of_epStokes c (S.modelEP c.Ψ).stokesWithoutPartitions_all hcpt hloc ω

/-- **Theorem 17.6.7 (Stokes), 2021 p. 823**, for the integrals on `C`, `m ≥ 1`:
`∫_Θ̂ d[ω] = ∫_{∂Θ̂} [ω]`. -/
theorem theorem_17_6_7_book_all (c₀ : S.CoveringFamily) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (h : A.IsTameOriented (m + 1)) (ω : S.catFormsInfty m) :
    A.integral (Nat.succ_pos m) hcpt h (S.catFormsInftyD m ω) =
      A.boundaryIntegral hm hcpt h ω :=
  A.theorem_17_6_7_book c₀ (S.modelEP c₀.Ψ).stokesWithoutPartitions_all hm hcpt h ω

/-- **Theorem 17.6.7 (Stokes), 2021 p. 823, for `n = 1`**, for the integrals on `C`. -/
theorem theorem_17_6_7_dim1_book_all (c₀ : S.CoveringFamily) (hcpt : C.IsCompactBranched A.Θ)
    (h : A.IsTameOriented (0 + 1)) (ω : S.catFormsInfty 0) :
    A.integral (Nat.succ_pos 0) hcpt h (S.catFormsInftyD 0 ω) =
      A.boundaryIntegralDim1 hcpt h ω :=
  A.theorem_17_6_7_dim1_book c₀ (S.modelEP c₀.Ψ).stokesWithoutPartitions_all hcpt h ω

/-- **Theorem 17.6.10 (effective Stokes), 2021 p. 824**, on a covering family, for `C` with
(LUC), `m ≥ 1`: `∮_Θ̂ d[ω] = ∮_{∂Θ̂} [ω]`. -/
theorem theorem_17_6_10_all (hL : S.IsLUC) (c : S.CoveringFamily) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c (m + 1))
    (ω : S.catFormsInfty m) :
    A.integralEffVia hL c (Nat.succ_pos m) hcpt hloc (S.catFormsInftyD m ω) =
      A.boundaryIntegralEffVia hL c hm hcpt hloc ω :=
  A.theorem_17_6_10_of_epStokes hL c (S.modelEP c.Ψ).stokesWithoutPartitions_all hm hcpt hloc ω

/-- **Theorem 17.6.10 (effective Stokes), 2021 p. 824, for `n = 1`**, on a covering family. -/
theorem theorem_17_6_10_dim1_all (hL : S.IsLUC) (c : S.CoveringFamily)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c (0 + 1))
    (ω : S.catFormsInfty 0) :
    A.integralEffVia hL c (Nat.succ_pos 0) hcpt hloc (S.catFormsInftyD 0 ω) =
      A.boundaryIntegralEffDim1Via hL c hcpt hloc ω :=
  A.theorem_17_6_10_dim1_of_epStokes hL c (S.modelEP c.Ψ).stokesWithoutPartitions_all hcpt hloc ω

/-- **Theorem 17.6.10 (effective Stokes), 2021 p. 824**, for the integrals on `C` with (LUC),
`m ≥ 1`. -/
theorem theorem_17_6_10_book_all (hL : S.IsLUC) (c₀ : S.CoveringFamily) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (h : A.IsTameOriented (m + 1)) (ω : S.catFormsInfty m) :
    A.integralEff hL (Nat.succ_pos m) hcpt h (S.catFormsInftyD m ω) =
      A.boundaryIntegralEff hL hm hcpt h ω :=
  A.theorem_17_6_10_book hL c₀ (S.modelEP c₀.Ψ).stokesWithoutPartitions_all hm hcpt h ω

/-- **Theorem 17.6.10 (effective Stokes), 2021 p. 824, for `n = 1`**, for the integrals on
`C`. -/
theorem theorem_17_6_10_dim1_book_all (hL : S.IsLUC) (c₀ : S.CoveringFamily)
    (hcpt : C.IsCompactBranched A.Θ) (h : A.IsTameOriented (0 + 1)) (ω : S.catFormsInfty 0) :
    A.integralEff hL (Nat.succ_pos 0) hcpt h (S.catFormsInftyD 0 ω) =
      A.boundaryIntegralEffDim1 hL hcpt h ω :=
  A.theorem_17_6_10_dim1_book hL c₀ (S.modelEP c₀.Ψ).stokesWithoutPartitions_all hcpt h ω

end GCT.PolyfoldConstruction.OrientedSubcategory

end Polyfold
