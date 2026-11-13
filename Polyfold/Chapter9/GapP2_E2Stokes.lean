import Polyfold.Chapter9.GapP1_Stokes2021
import Polyfold.Chapter9.GapP2_E2MeasureGlue

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §9.5,
**Theorems 9.5.17 and 9.5.18** (Stokes' theorem for branched integration, pp. 449–451; 2017:
Theorems 9.7, 9.8, pp. 327–329): the steps of the proof on pp. 450–451 (gap G.110).

# Stokes' theorem for branched integration: the proof from the local formulas

## The text, paraphrased

(pp. 450–451) Cover the compact `S = |supp(Θ)|` by finitely many `|U_k|`, `U_k = U(x_k)` with the
natural `G_{x_k}`-action, the properness property and an oriented branching structure
`(Mᵢ, oᵢ)_{i ∈ I_k}`, `(σᵢ)`.  With the saturations `U_k^*` and a further saturated open `U_0^*`
take an sc-smooth partition of unity `β_0, …, β_ℓ` subordinate to them and put `ω_k = β_k ω`.  By
the standard Stokes theorem `∫_{(Mᵢ,oᵢ)} dω_k = ∫_{∂(Mᵢ,oᵢ)} ω_k` for `i ∈ I_k`.  Summing up,
`μ_{dω}(S) = ∑_k μ_{dω_k}(S) = ∑_k (1/♯G^{eff}_{x_k}) ∑_{i ∈ I_k} σᵢ ∫_{(Mᵢ,oᵢ)} dω_k
= ∑_k (1/♯G^{eff}_{x_k}) ∑_{i ∈ I_k} σᵢ ∫_{∂(Mᵢ,oᵢ)} ω_k = ∑_k μ^∂_{ω_k}(∂S) = μ^∂_ω(∂S)`.

## What is formalized

* `MPolyfold.stokes_formsInftyRestrict_of_isCompact`, `stokes_formsInftyRestrict_of_vanishes`:
  the standard Stokes theorem on a sheet that need not be compact: for a sub-M-polyfold `M ⊆ X`
  with a corner structure of dimension `n + 1`, σ-compact, with a continuous orientation, and
  `ω ∈ Ωⁿ_∞(X)` whose restriction to `M` has compact support (or vanishes off a closed `C` with
  `M ∩ C` compact), `∫_M (dω)|_M = ∫_{∂M} ω|_M`.
* `EpGroupoid.NaturalRep.exists_ultrafilter_le_nhds`: for a natural representation on `U(x)`, an
  ultrafilter on `U(x)` whose image in `|X|` converges to `|u₀|`, `u₀ ∈ U(x)`, converges to a point
  `g * u₀` of the orbit: `U(x) → |U(x)|` is proper.
* `EpGroupoid.TameBranchingStructure.isCompact_inter`: **the supports in the sheets are compact**:
  for `Θ` compact, a tame branching structure on `U(x)` and a closed saturated `C ⊆ U(x)^*` (the
  support of a `β_k` of the partition of unity), every `Mᵢ ∩ C` is compact.  This is what makes
  the standard Stokes theorem applicable to `ω_k` on the non-compact `Mᵢ`.
* `MPolyfold.OrientedSheet`: a σ-compact sheet with a corner structure of dimension `n + 1` and a
  continuous tangent orientation; `OrientedSheet.integral` (`∫_{(M,o)} η|_M`),
  `OrientedSheet.boundaryIntegral` (`∫_{∂(M,o)} ω|_M`, the boundary orientation of
  Definition 9.3.8, outward vector first), `OrientedSheet.stokes`.
* `EpGroupoid.TameBranchingStructure.stokes_sheets`: the third equality of the display, for one
  `k`: `c ∑ᵢ σᵢ ∫_{(Mᵢ,oᵢ)} dω_k = c ∑ᵢ σᵢ ∫_{∂(Mᵢ,oᵢ)} ω_k` for `ω_k` vanishing on the sheets off a
  closed saturated `C ⊆ U_k^*`.
* **`EpGroupoid.theorem_9_5_17_of_localization`**: Stokes' formula `Φ(dω) = Φ^∂(ω)` for linear
  `Φ : Ωⁿ⁺¹_∞(X) → ℝ` (`η ↦ μ_η(S)`) and `Φ^∂ : Ωⁿ_∞(X) → ℝ` (`ω ↦ μ^∂_ω(∂S)`), every
  `ω = ω_0 + ∑_k ω_k` with `ω_k` vanishing on the sheets off a closed saturated `C_k ⊆ U_k^*`, the
  second and fourth equalities of the display for the `ω_k` (the local formulas of Theorems
  9.5.4/9.5.5 and 9.5.15/9.5.16 for forms supported in `U_k^*`) and `Φ(dω_0) = 0 = Φ^∂(ω_0)`.
  The weights `c_k` are arbitrary: `1/♯G_{x_k}` (Theorem 9.5.17) or `1/♯G^{eff}_{x_k}`
  (Theorem 9.5.18).

## What the text leaves implicit, and the choices made

* The sheets `Mᵢ` are not compact; the standard Stokes theorem applies to `ω_k` on `Mᵢ` since
  `Mᵢ ∩ supp β_k` is compact: `supp β_k` is closed and saturated in `U_k^*`, `S` is compact and
  `U_k → |U_k|` is proper (`isCompact_inter`; the properness property of `U_k` is not used).
* Mathlib's partitions of unity on the sheet need it σ-compact (`OrientedSheet.sigmaCompact`); it
  is when `X` is second countable.
* The orientation of a sheet is here a continuous Mathlib tangent orientation of the sheet with
  its corner charts; the passage from the orientations of Definition 9.3.3 is not formalized.
  (2026-11-13) It is `OrientedTameStructure.orientedSheet` (`GapP2_E5_StokesSheet.lean`).

## Not formalized

The measures `μ_ω`, `μ^∂_ω` (gaps G.107, G.109) and with them the second and fourth equalities
(hypotheses here); the forms `β_k ω` (the product of an sc-form with an sc-smooth function, and
that it vanishes on the sheets off `supp β_k`); Remark 9.5.20 (its M-polyfold `X ⊆ ℝ × ℂ` has a
jump of dimension and is not constructed).  (2026-11-13) Formalized since: the measures `μ_ω` for
sc-forms (`GapP2_E3_*`, `GapP2_E4_*`), the forms `β ω` (`EP.epFormsInftySmul`,
`GapP2_E5_FunForm.lean`), the comparison with Part I's integral for classes represented on any
level (`EP.epFormsInftyEval_integ_eq_integral`, `GapP2_E5_LevelRestrict.lean`), `μ^∂_ω` under a
class condition (`GapP2_E7_BoundaryMeasure.lean`) and Stokes' theorem with it
(`GapP2_E8_Stokes.lean`).  Remark 9.5.20 is still not formalized.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Manifold Module

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

/-! ### The standard Stokes theorem on a non-compact sheet -/

namespace MPolyfold

section Sheet

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {S : Set X} [ParacompactSpace S] [SigmaCompactSpace S]
  {hY : PX.IsSubMPolyfold S} {hcs : (subPolyfold hY).HasCornerStructureOfDim (n + 1)}
  [inst : ChartedSpace (EuclideanQuadrant (n + 1)) S]
  (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)
include hch

/-- **Stokes' theorem for sc-forms on a sheet, compact support** (2021 Theorem 4.4.7, p. 199, as
used on p. 451): for a σ-compact `S ⊆ X` with a corner structure of dimension `n + 1`, a
continuous tangent orientation `o` and `ω ∈ Ωⁿ_∞(X)` whose restriction `ω|_S` has compact
support, `∫_S (dω)|_S = ∫_{∂S} ω|_S`. -/
theorem stokes_formsInftyRestrict_of_isCompact
    {o : TangentOrientation (𝓠 (n + 1)) S (n + 1)} (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    (ω : (BundledMPolyfold.of PX).formsInfty n)
    (hc : IsCompact (ManifoldForm.tsupport (formsInftyRestrict n hcs ω))) :
    haveI := isManifold_of_eq hcs hch
    ManifoldForm.integral o
        (formsInftyRestrict (n + 1) hcs ((BundledMPolyfold.of PX).formsInftyD n ω)) =
      ManifoldForm.boundaryIntegral o (formsInftyRestrict n hcs ω) := by
  have := isManifold_of_eq hcs hch
  rw [← extDeriv_formsInftyRestrict hch]
  exact ManifoldForm.integral_extDeriv_eq_boundaryIntegral ho
    ((contMDiffForm_formsInftyRestrict hch ω).of_le (by exact_mod_cast le_top)) hc

/-- **Stokes' theorem on a sheet for a form vanishing off `C`**: if `C ⊆ X` is closed, `S ∩ C` is
compact and `ω|_S` vanishes at the points of `S ∖ C`, then `∫_S (dω)|_S = ∫_{∂S} ω|_S`. -/
theorem stokes_formsInftyRestrict_of_vanishes
    {o : TangentOrientation (𝓠 (n + 1)) S (n + 1)} (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    (ω : (BundledMPolyfold.of PX).formsInfty n) {C : Set X} (hC : IsClosed C)
    (hK : IsCompact (S ∩ C)) (h0 : ∀ y : S, (y : X) ∉ C → formsInftyRestrict n hcs ω y = 0) :
    haveI := isManifold_of_eq hcs hch
    ManifoldForm.integral o
        (formsInftyRestrict (n + 1) hcs ((BundledMPolyfold.of PX).formsInftyD n ω)) =
      ManifoldForm.boundaryIntegral o (formsInftyRestrict n hcs ω) := by
  refine stokes_formsInftyRestrict_of_isCompact hch ho ω ?_
  have hcl : IsClosed ((↑) ⁻¹' C : Set S) := hC.preimage continuous_subtype_val
  have hcp : IsCompact ((↑) ⁻¹' C : Set S) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
    exact hK
  refine hcp.of_isClosed_subset isClosed_closure (closure_minimal (fun y hy => ?_) hcl)
  by_contra hyC
  exact hy (h0 y hyC)

end Sheet

/-! ### Oriented sheets and their integrals -/

section OrientedSheet

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- **An oriented sheet of dimension `n + 1`**: a sub-M-polyfold `M ⊆ X` with a corner structure
of dimension `n + 1` (a tame `(n+1)`-dimensional submanifold, Definition 9.3.6), σ-compact, with a
continuous tangent orientation of the manifold with corners `M`. -/
structure OrientedSheet (PX : MPolyfold X) (n : ℕ) where
  /-- The sheet `M`. -/
  carrier : Set X
  isSub : PX.IsSubMPolyfold carrier
  [paracompact : ParacompactSpace carrier]
  [sigmaCompact : SigmaCompactSpace carrier]
  hcs : (subPolyfold isSub).HasCornerStructureOfDim (n + 1)
  /-- The orientation `o`. -/
  o : letI := (subPolyfold isSub).cornerChartedSpace hcs
    TangentOrientation (𝓠 (n + 1)) carrier (n + 1)
  isContinuous : letI := (subPolyfold isSub).cornerChartedSpace hcs
    TangentOrientation.IsContinuous (𝓠 (n + 1)) ∞ o

attribute [instance] OrientedSheet.paracompact OrientedSheet.sigmaCompact

namespace OrientedSheet

variable {PX : MPolyfold X} {n : ℕ} (N : OrientedSheet PX n)

/-- `∫_{(M,o)} η|_M` for `η ∈ Ωⁿ⁺¹_∞(X)`. -/
def integral (η : (BundledMPolyfold.of PX).formsInfty (n + 1)) : ℝ :=
  letI := (subPolyfold N.isSub).cornerChartedSpace N.hcs
  haveI := (subPolyfold N.isSub).isManifold_cornerChartedSpace N.hcs
  ManifoldForm.integral N.o (formsInftyRestrict (n + 1) N.hcs η)

/-- `∫_{∂(M,o)} ω|_M` for `ω ∈ Ωⁿ_∞(X)`, the boundary with the induced orientation (outward
vector first, Definition 9.3.8). -/
def boundaryIntegral (ω : (BundledMPolyfold.of PX).formsInfty n) : ℝ :=
  letI := (subPolyfold N.isSub).cornerChartedSpace N.hcs
  haveI := (subPolyfold N.isSub).isManifold_cornerChartedSpace N.hcs
  ManifoldForm.boundaryIntegral N.o (formsInftyRestrict n N.hcs ω)

/-- `ω|_M` vanishes at the points of `M ∖ C`. -/
def VanishesOff (C : Set X) (ω : (BundledMPolyfold.of PX).formsInfty n) : Prop :=
  letI := (subPolyfold N.isSub).cornerChartedSpace N.hcs
  ∀ y : N.carrier, (y : X) ∉ C → formsInftyRestrict n N.hcs ω y = 0

/-- **The standard Stokes theorem on an oriented sheet** (p. 451): `∫_{(M,o)} dω = ∫_{∂(M,o)} ω`
for `ω` vanishing on `M` off a closed `C` with `M ∩ C` compact. -/
theorem stokes {C : Set X} (hC : IsClosed C) (hK : IsCompact (N.carrier ∩ C))
    (ω : (BundledMPolyfold.of PX).formsInfty n) (h0 : N.VanishesOff C ω) :
    N.integral ((BundledMPolyfold.of PX).formsInftyD n ω) = N.boundaryIntegral ω :=
  stokes_formsInftyRestrict_of_vanishes (inst := (subPolyfold N.isSub).cornerChartedSpace N.hcs)
    rfl N.isContinuous ω hC hK h0

end OrientedSheet

end OrientedSheet

end MPolyfold

/-! ### Compact supports in the sheets -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {x : Obj}

/-- **`U(x) → |U(x)|` is proper** for a natural representation: an ultrafilter on `U(x)` whose
image under `π` converges to `|u₀|`, `u₀ ∈ U(x)`, converges to `g * u₀` for some `g ∈ G_x`. -/
theorem NaturalRep.exists_ultrafilter_le_nhds (R : X.NaturalRep x) {F : Ultrafilter Obj}
    (hU : R.U ∈ F) {u₀ : Obj} (hu₀ : u₀ ∈ R.U) (hπ : Tendsto X.π F (𝓝 (X.π u₀))) :
    ∃ g : X.Isotropy x, (F : Filter Obj) ≤ 𝓝 (R.Φ g u₀) := by
  by_contra hne
  simp only [not_exists] at hne
  have hex : ∀ g : X.Isotropy x, ∃ O : Set Obj, IsOpen O ∧ R.Φ g u₀ ∈ O ∧ Oᶜ ∈ F := fun g => by
    obtain ⟨s, hs, hsF⟩ := Filter.not_le.1 (hne g)
    obtain ⟨O, hOs, hO, hmem⟩ := mem_nhds_iff.1 hs
    refine ⟨O, hO, hmem, Ultrafilter.compl_mem_iff_notMem.2 fun h => hsF (mem_of_superset h hOs)⟩
  choose O hO hmem hOc using hex
  set N : Set Obj := ⋃ g, O g with hN
  have hNo : IsOpen N := isOpen_iUnion hO
  have hNc : Nᶜ ∈ F := by
    rw [hN, compl_iUnion]
    exact (Filter.iInter_mem (f := (F : Filter Obj))).2 hOc
  set N' : Set Obj := ⋂ g, (R.U ∩ R.Φ g ⁻¹' N) with hN'
  have hN'o : IsOpen N' := isOpen_iInter_of_finite fun g =>
    (R.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn.isOpen_inter_preimage R.isOpen_U hNo
  have hu₀N' : u₀ ∈ N' := mem_iInter.2 fun g => ⟨hu₀, mem_iUnion.2 ⟨g, hmem g⟩⟩
  have hA : X.π ⁻¹' (X.π '' N') ∈ F :=
    hπ ((X.proposition_7_1_8 _ hN'o).mem_nhds ⟨u₀, hu₀N', rfl⟩)
  have hsub : R.U ∩ X.π ⁻¹' (X.π '' N') ⊆ N := by
    rintro y ⟨hyU, z, hz, hzy⟩
    obtain ⟨φ, hsrc, htgt⟩ := X.π_eq_π_iff.1 hzy
    have hzU : z ∈ R.U := (mem_iInter.1 hz 1).1
    obtain ⟨g, hg, -⟩ := R.existsUnique_Γ φ (hsrc ▸ hzU) (htgt ▸ hyU)
    have hy : y = R.Φ g z := by
      rw [← htgt, ← hg, hsrc, R.tgt_Γ g z hzU]
    rw [hy]
    exact (mem_iInter.1 hz g).2
  exact Ultrafilter.compl_mem_iff_notMem.1 hNc (mem_of_superset (inter_mem hU hA) hsub)

variable {Θ : Obj → ℚ}

/-- The sheets of a local branching structure lie in `supp(Θ)`. -/
theorem LocalBranchingStructure.M_subset_supp (B : X.LocalBranchingStructure Θ x) (i : B.ι) :
    B.M i ⊆ supp Θ := fun y hy => by
  classical
  change 0 < Θ y
  rw [B.eq_sum y (B.subset_U i hy)]
  exact Finset.sum_pos' (fun j _ => (B.σ_pos j).le) ⟨i, by simp [hy], B.σ_pos i⟩

/-- **The supports in the sheets are compact** (the proof of Theorem 9.5.18, p. 451: the standard
Stokes theorem for `ω_k = β_k ω` on `Mᵢ`): let `Θ` be compact, `B` a tame branching structure on
`U(x)` and `C` closed and saturated with `C ⊆ U(x)^* = π⁻¹(|U(x)|)`.  Then `Mᵢ ∩ C` is compact for
every sheet `Mᵢ`. -/
theorem TameBranchingStructure.isCompact_inter (B : X.TameBranchingStructure Θ x)
    (hS : X.IsCompactBranched Θ) {C : Set Obj} (hC : IsClosed C) (hsat : X.IsSaturated C)
    (hCU : C ⊆ X.π ⁻¹' (X.π '' B.U)) (i : B.ι) : IsCompact (B.M i ∩ C) := by
  refine isCompact_iff_ultrafilter_le_nhds.2 fun F hF => ?_
  have hFM : B.M i ∩ C ∈ F := le_principal_iff.1 hF
  have hMF : B.M i ∈ F := mem_of_superset hFM inter_subset_left
  have hCF : C ∈ F := mem_of_superset hFM inter_subset_right
  have hUF : B.U ∈ F := mem_of_superset hMF (B.subset_U i)
  -- the image ultrafilter converges in the compact `S`
  have hSG : X.orbitSupp Θ ∈ F.map X.π :=
    Ultrafilter.mem_map.2 (mem_of_superset hMF fun y hy => ⟨y, B.M_subset_supp i hy, rfl⟩)
  obtain ⟨q, -, hq⟩ := hS.ultrafilter_le_nhds (F.map X.π) (le_principal_iff.2 hSG)
  -- `π(C)` is closed, so `q ∈ π(C)`
  have hπC : IsClosed (X.π '' C) := by
    have hcompl : (X.π '' C)ᶜ = X.π '' Cᶜ := by
      ext p
      obtain ⟨y, rfl⟩ := X.surjective_π p
      constructor
      · intro hp
        exact ⟨y, fun hy => hp ⟨y, hy, rfl⟩, rfl⟩
      · rintro ⟨z, hz, hzy⟩ ⟨c, hc, hcy⟩
        exact hz (hsat ▸ (⟨c, hc, hcy.trans hzy.symm⟩ : z ∈ X.π ⁻¹' (X.π '' C)))
    rw [← isOpen_compl_iff, hcompl]
    exact X.proposition_7_1_8 _ hC.isOpen_compl
  have hqC : q ∈ X.π '' C :=
    isClosed_iff_ultrafilter.1 hπC q (F.map X.π) hq
      (Ultrafilter.mem_map.2 (mem_of_superset hCF (subset_preimage_image _ _)))
  obtain ⟨c, hc, rfl⟩ := hqC
  obtain ⟨u₀, hu₀, hu₀c⟩ := hCU hc
  have hu₀C : u₀ ∈ C := hsat ▸ (⟨c, hc, hu₀c.symm⟩ : u₀ ∈ X.π ⁻¹' (X.π '' C))
  have hRU : B.rep.U = B.U := B.U_eq.symm
  have hq' : Tendsto X.π F (𝓝 (X.π u₀)) := by
    rw [hu₀c, Filter.Tendsto, ← Ultrafilter.coe_map]
    exact hq
  obtain ⟨g, hg⟩ := B.rep.exists_ultrafilter_le_nhds (hRU ▸ hUF) (hRU ▸ hu₀) hq'
  have huU : B.rep.Φ g u₀ ∈ B.U := hRU ▸ B.rep.mapsTo_Φ g (hRU ▸ hu₀)
  -- `Mᵢ` is closed in `U`
  obtain ⟨t, ht, hMt⟩ := B.exists_isClosed_eq_inter i
  have htF : t ∈ F := mem_of_superset hMF (hMt ▸ inter_subset_left)
  refine ⟨B.rep.Φ g u₀, ⟨?_, isClosed_iff_ultrafilter.1 hC _ F hg hCF⟩, hg⟩
  rw [hMt]
  exact ⟨isClosed_iff_ultrafilter.1 ht _ F hg htF, huU⟩

/-! ### Stokes' theorem from the local formulas -/

section Stokes

open MPolyfold

variable {n : ℕ}

/-- **The standard Stokes theorem on the sheets of one `U_k`** (the third equality of the display
on p. 451): for `Θ` compact, a tame branching structure `B` on `U(x)` whose sheets are oriented
sheets `Nᵢ` of dimension `n + 1`, and `ω ∈ Ωⁿ_∞(X)` vanishing on the sheets off a closed saturated
`C ⊆ U(x)^*`: `c ∑ᵢ σᵢ ∫_{(Mᵢ,oᵢ)} dω = c ∑ᵢ σᵢ ∫_{∂(Mᵢ,oᵢ)} ω`. -/
theorem TameBranchingStructure.stokes_sheets (B : X.TameBranchingStructure Θ x)
    (hS : X.IsCompactBranched Θ) (N : B.ι → OrientedSheet X.PObj n)
    (hN : ∀ i, (N i).carrier = B.M i) {C : Set Obj} (hC : IsClosed C)
    (hsat : X.IsSaturated C) (hCU : C ⊆ X.π ⁻¹' (X.π '' B.U))
    (ω : (BundledMPolyfold.of X.PObj).formsInfty n) (h0 : ∀ i, (N i).VanishesOff C ω)
    (c : ℝ) :
    c * ∑ i, (B.σ i : ℝ) * (N i).integral ((BundledMPolyfold.of X.PObj).formsInftyD n ω) =
      c * ∑ i, (B.σ i : ℝ) * (N i).boundaryIntegral ω := by
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(N i).stokes hC (by rw [hN i]; exact B.isCompact_inter hS hC hsat hCU i) ω (h0 i)]

/-- **Theorems 9.5.17 and 9.5.18 (Stokes, 2021 pp. 449–451), from the local formulas**: let `Θ`
be compact, `Φ : Ωⁿ⁺¹_∞(X) → ℝ` and `Φ^∂ : Ωⁿ_∞(X) → ℝ` linear (`η ↦ μ_η(S)`, `ω ↦ μ^∂_ω(∂S)`),
and for `k` in a finite set let `B_k` be a tame branching structure on `U_k = U(x_k)` with
oriented sheets `N_{k,i}`, `c_k` a weight (`1/♯G_{x_k}` or `1/♯G^{eff}_{x_k}`), `C_k ⊆ U_k^*`
closed and saturated, and `ω_k ∈ Ωⁿ_∞(X)` vanishing on the sheets of `B_k` off `C_k` (the form
`β_k ω`), such that
`Φ(dω_k) = c_k ∑ᵢ σᵢ ∫_{(Mᵢ,oᵢ)} dω_k` and `Φ^∂(ω_k) = c_k ∑ᵢ σᵢ ∫_{∂(Mᵢ,oᵢ)} ω_k`
(the local formulas of the measures), and `Φ(dω_0) = 0 = Φ^∂(ω_0)`.  Then
`Φ(dω) = Φ^∂(ω)` for `ω = ω_0 + ∑_k ω_k`: `μ_{dω}(S) = μ^∂_ω(∂S)`. -/
theorem theorem_9_5_17_of_localization (hS : X.IsCompactBranched Θ)
    (Φ : (BundledMPolyfold.of X.PObj).formsInfty (n + 1) →ₗ[ℝ] ℝ)
    (Φb : (BundledMPolyfold.of X.PObj).formsInfty n →ₗ[ℝ] ℝ)
    {κ : Type*} (s : Finset κ) (pt : κ → Obj) (B : ∀ k, X.TameBranchingStructure Θ (pt k))
    (N : ∀ k, (B k).ι → OrientedSheet X.PObj n) (hN : ∀ k i, (N k i).carrier = (B k).M i)
    (c : κ → ℝ) (C : κ → Set Obj) (hC : ∀ k, IsClosed (C k)) (hsat : ∀ k, X.IsSaturated (C k))
    (hCU : ∀ k, C k ⊆ X.π ⁻¹' (X.π '' (B k).U))
    (ω₀ : (BundledMPolyfold.of X.PObj).formsInfty n)
    (ωk : κ → (BundledMPolyfold.of X.PObj).formsInfty n)
    (h0 : ∀ k i, (N k i).VanishesOff (C k) (ωk k))
    (hΦ : ∀ k ∈ s, Φ ((BundledMPolyfold.of X.PObj).formsInftyD n (ωk k)) =
      c k * ∑ i, ((B k).σ i : ℝ) *
        (N k i).integral ((BundledMPolyfold.of X.PObj).formsInftyD n (ωk k)))
    (hΦb : ∀ k ∈ s, Φb (ωk k) =
      c k * ∑ i, ((B k).σ i : ℝ) * (N k i).boundaryIntegral (ωk k))
    (hΦ₀ : Φ ((BundledMPolyfold.of X.PObj).formsInftyD n ω₀) = 0) (hΦb₀ : Φb ω₀ = 0) :
    Φ ((BundledMPolyfold.of X.PObj).formsInftyD n (ω₀ + ∑ k ∈ s, ωk k)) =
      Φb (ω₀ + ∑ k ∈ s, ωk k) := by
  rw [map_add, map_add, map_add, map_sum, map_sum, map_sum, hΦ₀, hΦb₀]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [hΦ k hk, hΦb k hk]
  exact (B k).stokes_sheets hS (N k) (hN k) (hC k) (hsat k) (hCU k) (ωk k) (h0 k) (c k)

end Stokes

end EpGroupoid

end Polyfold
