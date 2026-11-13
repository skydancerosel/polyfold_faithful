import Polyfold.Chapter9.Measure
import Polyfold.Chapter7.ReducedCriterion
import Polyfold.Chapter7.Uniformizer

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes": the parts not involving forms or integrals of
**Lemma 9.5.9** (p. 442; 2017: Lemma 9.18, p. 326), **Lemma 9.5.10** (p. 444, new in the 2021
edition), **Lemma 9.5.11** (p. 445; 2017: Lemma 9.19, p. 326) and **Proposition 9.5.13**
(p. 446, new in the 2021 edition).  Numbers and pages are the 2021 text's.

# Restrictions, morphism invariance and the isotropy factors of §9.5

## The text, paraphrased

(Lemma 9.5.9) For `x ∈ supp(Θ)`, `U = U(x)` with the natural `G = G_x`-action carrying a local
branching structure, `y ∈ U` with isotropy `H_y` and a small `V = V(y) ⊆ U` with the natural
`H_y`-action, the measures `μ_ω^U` and `μ_ω^V` agree on `K ∈ L(S)` with `K ⊆ |M_V|`.  *Proof*:
`H = {g | g ∗ y = y} ≅ H_y`, `G = ⋃_{r ∈ R} r H`; choose `V` with `ϕ_g(V) = V` for `g ∈ H` and
`ϕ_g(V) ∩ V = ∅` otherwise; `M̃ᵢ = V ∩ Mᵢ` is a branching structure on `V` with
`M_V = M_U ∩ V`; the preimage of `K` in `Mᵢ` is `[⋃_r ϕ_r(K̃)] ∩ Mᵢ`; by invariance of `ω` each
`r` contributes the same integral, and `♯R = ♯G/♯H` gives the claim.  (Lemma 9.5.10) The same
for the effective measures under LUC; the proof replaces `♯R = ♯G/♯H` by (9.23)
`♯R = ♯G_x^eff/♯H_y^eff`, using `T_x = {g | ĝ = id on a nonempty open W ⊆ U}`, `T_x ⊆ H`, and that
`T_y` is identified with `T_x`.  (Lemma 9.5.11) For `φ : x → x'` whose local sc-diffeomorphism is
`φ̂ : U → U'`, `μ_ω^U(K) = μ_ω^{U'}(K)` on `|M_U| = |M_{U'}|`; likewise for the effective measures
under LUC ("a change of variables").  (Proposition 9.5.13) (1) For effective `X` the two branched
integrals agree; (2) under LUC the effective integral on `X` is the integral on `X_R`.  The
proof: `T_x = {1}`, so `G_x^eff = G_x` and the normalizing factors agree.

## What is formalized

* Lemma 9.5.9: `card_quotient_stabilizer_mul_card_isotropy` (`♯R · ♯G_y = ♯G_x`),
  `exists_slice` (the neighbourhood `V`), `mapsTo_Φ_MU`, `MU_inter_preimage_eq_iUnion`,
  `MU_inter_preimage_eq_iUnion_quotient` (the preimage of `K` is `⋃_r ϕ_r(K̃)`) and
  `pairwise_disjoint_image_Φ_out` (the union is disjoint).
* Lemma 9.5.10: `kerΦ_eq_trivialSubgroup` (`T_x = ker Φ` under `HasLUC`), `kerΦ_le_stabilizer`,
  `stabilizerEquivIsotropy_mem_trivialSubgroup_iff` and `card_trivialSubgroup_eq` (`T_y ≅ T_x`),
  `card_quotient_stabilizer_mul_card_effIsotropy` (**(9.23)**);
  `card_effIsotropy_mul_card_trivialSubgroup` (`♯T_x · ♯G_x^eff = ♯G_x`).
* Lemma 9.5.11: `card_isotropy_eq_of_mor`, `card_effIsotropy_eq_of_mor`, `image_π_MU_eq`
  (`|M_U| = |M_{U'}|`), with `NaturalRep.Φ_hyps` (its hypotheses hold for `ϕ_g`).
* Proposition 9.5.13: `card_effIsotropy_eq_of_isEffective` ((1): `♯G_x^eff = ♯G_x`);
  `isFunctorial_reduced_iff`, `LocalBranchingStructure.toReduced` (the data induced on `X_R`) and
  `card_effIsotropy_eq_reduced` ((2): `♯G_x^eff = ♯G_x^R = ♯(G_x^R)^eff`).

## What the text leaves implicit, and the choices made

* The measure identities themselves need forms and integrals (gaps G.74, G.80) and are not
  stated here; only the isotropy orders and the decompositions the proofs rest on are.  Since
  2026-11-12 they are proved for an abstract integration of forms over oriented sheets
  (`OrientedTameStructure.lemma_9_5_9`, `lemma_9_5_10`, `lemma_9_5_11`,
  `GapP2_E1_LocalMeasure.lean`; `proposition_9_5_13_1`, `GapP2_E1_BranchedIntegral.lean`).
* The text's `R ⊆ G` of representatives of the cosets `r H` is `Quotient.out` on `G_x ⧸ H`, with
  `H` the stabilizer of `y` for the action of `G_x` on `U(x)`.
* The restriction `M̃ⱼ = V ∩ Mⱼ` is `LocalBranchingStructure.restrict` / `restrictAt`
  (`Symmetric.lean`, `GoodPoints.lean`): the repository's local branching structures pass through
  their base point, so at `y` one keeps the sheets through `y` (`restrictAt`).
* In Lemma 9.5.10 LUC enters through `NaturalRep.HasLUC` (Definition 7.2.18) of the given
  `U(x)`; it is satisfiable (`isLUC_trivial`, `isLUC_of_isEffective`).  In Lemma 9.5.11, `φ̂` is
  any map of `U` onto `U'` with `|φ̂(z)| = |z|`.
* In Proposition 9.5.13 (2) the reduced ep-groupoid needs `T_R` Hausdorff and paracompact
  (instances); under LUC it is Hausdorff (`t2Space_reducedMor_of_isLUC`).  The local branching
  structures of `X` and `X_R` coincide, since both have the object M-polyfold of `X`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-! ### Isotropy orders -/

/-- `♯G_x^eff · ♯T_x = ♯G_x` (2021 p. 444, in the proof of Lemma 9.5.10). -/
theorem card_effIsotropy_mul_card_trivialSubgroup (x : Obj) :
    Nat.card (X.EffIsotropy x) * Nat.card (X.trivialSubgroup x) = Nat.card (X.Isotropy x) := by
  rw [Nat.card_congr (X.effIsotropyEquiv x).toEquiv,
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

namespace NaturalRep

variable {x : Obj} (R : X.NaturalRep x)

/-- `|Φ(g)(y)| = |y|` for `y ∈ U(x)`. -/
theorem π_Φ (g : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) : X.π (R.Φ g y) = X.π y :=
  ((X.π_eq_π_iff).2 ⟨R.Γ g y, R.src_Γ g y hy, R.tgt_Γ g y hy⟩).symm

/-- `g ∈ H = {g | g ∗ y = y}` iff `Φ(g)(y) = y`. -/
theorem mem_stabilizer_iff_Φ {a : R.U} {g : X.Isotropy x} :
    g ∈ MulAction.stabilizer (X.Isotropy x) a ↔ R.Φ g a = a :=
  MulAction.mem_stabilizer_iff.trans Subtype.ext_iff

/-! ### Lemma 9.5.9: the group-theoretic and set-theoretic part -/

/-- **`♯R = ♯G/♯H` (2021 p. 444, in the proof of Lemma 9.5.9)**: for `y ∈ U(x)` with the
stabilizer `H = {g ∈ G_x | g ∗ y = y} ≅ G_y` (`stabilizerEquivIsotropy`), the set `R = G/H` of
cosets satisfies `♯R · ♯G_y = ♯G_x`. -/
theorem card_quotient_stabilizer_mul_card_isotropy (a : R.U) :
    Nat.card (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) *
      Nat.card (X.Isotropy (a : Obj)) = Nat.card (X.Isotropy x) := by
  rw [← Nat.card_congr (R.stabilizerEquivIsotropy a).toEquiv,
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

/-- **The neighbourhood `V` of the proof of Lemma 9.5.9 (2021 p. 442)**: every `y ∈ U(x)` has
arbitrarily small open neighbourhoods `V ⊆ U(x)` with `ϕ_g(V) = V` for `g ∈ H` (the stabilizer
of `y`) and `ϕ_g(V) ∩ V = ∅` for `g ∈ G_x \ H`. -/
theorem exists_slice (a : R.U) {W : Set Obj} (hW : IsOpen W) (haW : (a : Obj) ∈ W) :
    ∃ V : Set Obj, IsOpen V ∧ (a : Obj) ∈ V ∧ V ⊆ R.U ∧ V ⊆ W ∧
      (∀ g ∈ MulAction.stabilizer (X.Isotropy x) a, R.Φ g '' V = V) ∧
      ∀ g ∉ MulAction.stabilizer (X.Isotropy x) a, Disjoint (R.Φ g '' V) V := by
  set H := MulAction.stabilizer (X.Isotropy x) a
  -- a small neighbourhood `N` of `a` with `Φ(g)(N) ∩ N = ∅` for `g ∉ H`
  have hev : ∀ g : X.Isotropy x, ∀ᶠ N in (𝓝 (a : Obj)).smallSets,
      g ∉ H → ∀ z ∈ N, ∀ z' ∈ N, R.Φ g z ≠ z' := by
    intro g
    by_cases hg : g ∈ H
    · exact Eventually.of_forall fun _ h => absurd hg h
    have hne : R.Φ g a ≠ a := fun h => hg (R.mem_stabilizer_iff_Φ.2 h)
    obtain ⟨O₁, O₂, hO₁, hO₂, h₁, h₂, hd⟩ := t2_separation hne
    have hN : R.U ∩ R.Φ g ⁻¹' O₁ ∩ O₂ ∈ 𝓝 (a : Obj) :=
      ((R.continuousOn_Φ g).isOpen_inter_preimage R.isOpen_U hO₁ |>.inter hO₂).mem_nhds
        ⟨⟨a.2, h₁⟩, h₂⟩
    refine (eventually_smallSets' fun s t hst ht hg z hz z' hz' =>
      ht hg z (hst hz) z' (hst hz')).2 ⟨_, hN, fun _ z hz z' hz' he => ?_⟩
    exact Set.disjoint_left.1 hd (he ▸ hz.1.2) hz'.2
  obtain ⟨N, hN, hNP⟩ := eventually_smallSets.1 (eventually_all.2 hev)
  set V₀ := interior N ∩ W ∩ R.U
  have hV₀o : IsOpen V₀ := (isOpen_interior.inter hW).inter R.isOpen_U
  set V := ⋂ h : H, R.U ∩ R.Φ h ⁻¹' V₀
  have hVo : IsOpen V := isOpen_iInter_of_finite fun h =>
    (R.continuousOn_Φ h).isOpen_inter_preimage R.isOpen_U hV₀o
  have hVU : V ⊆ R.U := fun z hz => (mem_iInter.1 hz 1).1
  have hVV₀ : V ⊆ V₀ := fun z hz => by
    have h1 := (mem_iInter.1 hz 1).2
    rwa [mem_preimage, Subgroup.coe_one, R.Φ_one z (hVU hz)] at h1
  have hmaps : ∀ g ∈ H, MapsTo (R.Φ g) V V := fun g hg z hz => mem_iInter.2 fun h =>
    ⟨R.mapsTo_Φ g (hVU hz), by
      rw [mem_preimage, ← R.Φ_mul _ g z (hVU hz)]
      exact (mem_iInter.1 hz ⟨h * g, H.mul_mem h.2 hg⟩).2⟩
  refine ⟨V, hVo, mem_iInter.2 fun h => ⟨a.2, ?_⟩, hVU,
    fun z hz => (hVV₀ hz).1.2, fun g hg => ?_, fun g hg => ?_⟩
  · rw [mem_preimage, R.mem_stabilizer_iff_Φ.1 h.2]
    exact ⟨⟨interior_mem_nhds.2 hN |> mem_of_mem_nhds, haW⟩, a.2⟩
  · refine (hmaps g hg).image_subset.antisymm fun z hz => ⟨R.Φ g⁻¹ z,
      hmaps g⁻¹ (H.inv_mem hg) hz, R.Φ_Φ_inv g (hVU hz)⟩
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨z, hz, rfl⟩ hz'
    exact hNP N subset_rfl g hg z (interior_subset (hVV₀ hz).1.1) _
      (interior_subset (hVV₀ hz').1.1) rfl

variable {Θ : Obj → ℚ}

/-- The `G_x`-invariance of `M_U = supp(Θ) ∩ U` for `U = U(x)` (`Θ` a functor). -/
theorem mapsTo_Φ_MU (hΘ : X.IsFunctorial Θ) (B : X.LocalBranchingStructure Θ x)
    (hBU : B.U = R.U) (g : X.Isotropy x) : MapsTo (R.Φ g) B.MU B.MU := fun z hz => by
  rw [B.MU_eq, hBU] at hz ⊢
  refine ⟨?_, R.mapsTo_Φ g hz.2⟩
  change 0 < Θ (R.Φ g z)
  rw [hΘ.apply_Φ R g hz.2]
  exact hz.1

/-- **The preimage of `K ⊆ |M_V|` in `M_U` (2021 p. 443, in the proof of Lemma 9.5.9)**: if `K`
lies in `|M_V| = |M_U ∩ V|` for some `V ⊆ U(x)`, then its preimage in `M_U` is the union of the
translates `ϕ_g(K̃)`, `g ∈ G_x`, of its preimage `K̃ = M_U ∩ V ∩ π⁻¹(K)` in `M_V`. -/
theorem MU_inter_preimage_eq_iUnion (hΘ : X.IsFunctorial Θ) (B : X.LocalBranchingStructure Θ x)
    (hBU : B.U = R.U) {V : Set Obj} {K : Set X.OrbitSpace} (hK : K ⊆ X.π '' (B.MU ∩ V)) :
    B.MU ∩ X.π ⁻¹' K = ⋃ g : X.Isotropy x, R.Φ g '' (B.MU ∩ V ∩ X.π ⁻¹' K) := by
  have hMU : B.MU ⊆ R.U := fun z hz => by
    rw [B.MU_eq, hBU] at hz
    exact hz.2
  refine Subset.antisymm (fun z hz => ?_) (iUnion_subset fun g => ?_)
  · obtain ⟨w, ⟨hwM, hwV⟩, hwz⟩ := hK hz.2
    obtain ⟨g, hg⟩ := (R.π_eq_π_iff_exists_smul (y := ⟨w, hMU hwM⟩)
      (z := ⟨z, hMU hz.1⟩)).1 hwz
    refine mem_iUnion.2 ⟨g, w, ⟨⟨hwM, hwV⟩, ?_⟩, congrArg Subtype.val hg⟩
    rw [mem_preimage, hwz]
    exact hz.2
  · rintro _ ⟨w, ⟨⟨hwM, -⟩, hwK⟩, rfl⟩
    exact ⟨R.mapsTo_Φ_MU hΘ B hBU g hwM, by rwa [mem_preimage, R.π_Φ g (hMU hwM)]⟩

/-- **The decomposition `Kᵢ = [⋃_{r ∈ R} ϕ_r(K̃)] ∩ Mᵢ` of the proof of Lemma 9.5.9 (2021
p. 443)**: with `V` as in `exists_slice` (`ϕ_h(V) = V` for `h ∈ H`), the preimage of `K ⊆ |M_V|`
in `M_U` is the union of the `ϕ_r(K̃)` over a set `R` of coset representatives of `G_x/H`
(`Quotient.out`). -/
theorem MU_inter_preimage_eq_iUnion_quotient (hΘ : X.IsFunctorial Θ)
    (B : X.LocalBranchingStructure Θ x) (hBU : B.U = R.U) (a : R.U) {V : Set Obj}
    (hVH : ∀ g ∈ MulAction.stabilizer (X.Isotropy x) a, R.Φ g '' V = V)
    {K : Set X.OrbitSpace} (hK : K ⊆ X.π '' (B.MU ∩ V)) :
    B.MU ∩ X.π ⁻¹' K = ⋃ q : X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a,
      R.Φ (Quotient.out q) '' (B.MU ∩ V ∩ X.π ⁻¹' K) := by
  have hMU : B.MU ⊆ R.U := fun z hz => by
    rw [B.MU_eq, hBU] at hz
    exact hz.2
  rw [R.MU_inter_preimage_eq_iUnion hΘ B hBU hK]
  refine Subset.antisymm (iUnion_subset fun g => ?_)
    (iUnion_subset fun q => subset_iUnion (fun g => R.Φ g '' _) _)
  rintro _ ⟨w, ⟨⟨hwM, hwV⟩, hwK⟩, rfl⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (MulAction.stabilizer (X.Isotropy x) a) g
  have hg : g = Quotient.out (g : X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) *
      (h : X.Isotropy x)⁻¹ := by
    rw [hh, mul_inv_cancel_right]
  have hw' : R.Φ (h : X.Isotropy x)⁻¹ w ∈ V := by
    rw [← hVH _ (inv_mem h.2)]
    exact mem_image_of_mem _ hwV
  refine mem_iUnion.2 ⟨(g : X.Isotropy x ⧸ _), R.Φ (h : X.Isotropy x)⁻¹ w,
    ⟨⟨R.mapsTo_Φ_MU hΘ B hBU _ hwM, hw'⟩, ?_⟩, ?_⟩
  · rwa [mem_preimage, R.π_Φ _ (hMU hwM)]
  · conv_rhs => rw [hg]
    rw [R.Φ_mul _ _ w (hMU hwM)]

/-- **The translates `ϕ_r(K̃)`, `r ∈ R`, are pairwise disjoint (2021 p. 443, in the proof of
Lemma 9.5.9)**: for `V` as in `exists_slice` (`ϕ_g(V) ∩ V = ∅` for `g ∉ H`) and `A ⊆ V`, the sets
`ϕ_r(A)` over distinct cosets `r H` are disjoint; so the union in
`MU_inter_preimage_eq_iUnion_quotient` is disjoint, and integrating over it gives the factor
`♯R`. -/
theorem pairwise_disjoint_image_Φ_out (a : R.U) {V : Set Obj} (hVU : V ⊆ R.U)
    (hVd : ∀ g ∉ MulAction.stabilizer (X.Isotropy x) a, Disjoint (R.Φ g '' V) V)
    {A : Set Obj} (hAV : A ⊆ V) :
    Pairwise (Disjoint on fun q : X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a =>
      R.Φ (Quotient.out q) '' A) := by
  intro q q' hne
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', he⟩
  set r := Quotient.out q
  set r' := Quotient.out q'
  have hmem : r'⁻¹ * r ∈ MulAction.stabilizer (X.Isotropy x) a := by
    by_contra hn
    refine Set.disjoint_left.1 (hVd _ hn) ⟨w, hAV hw, ?_⟩ (hAV hw')
    rw [R.Φ_mul _ _ w (hVU (hAV hw)), ← he, R.Φ_inv_Φ _ (hVU (hAV hw'))]
  refine hne ?_
  rw [← Quotient.out_eq q, ← Quotient.out_eq q']
  exact (QuotientGroup.eq (s := MulAction.stabilizer (X.Isotropy x) a)).2
    hmem |>.symm

/-! ### Lemma 9.5.10: the effective orders, (9.23) -/

/-- **`T_x = ker Φ` under LUC (2021 p. 444, in the proof of Lemma 9.5.10)**: if `U(x)` has the
property of Definition 7.2.18 (`HasLUC`), then `T_x` is the kernel of `G_x → Diff_sc(U(x))`. -/
theorem kerΦ_eq_trivialSubgroup (hL : R.HasLUC) : R.kerΦ = X.trivialSubgroup x := by
  ext g
  rw [R.mem_kerΦ, X.mem_trivialSubgroup]
  change _ ↔ X.ActsTrivially g
  rw [R.actsTrivially_iff]
  refine ⟨fun h => Filter.mem_of_superset (R.isOpen_U.mem_nhds R.mem_U) h, fun h => ?_⟩
  obtain ⟨N, hN, hNo, hxN⟩ := mem_nhds_iff.1 h
  exact hL g (N ∩ R.U) (hNo.inter R.isOpen_U) ⟨x, hxN, R.mem_U⟩ inter_subset_right
    fun y hy => hN hy.1

/-- `ker Φ ⊆ H` (2021 p. 445, "`T_x ⊂ H`"). -/
theorem kerΦ_le_stabilizer (a : R.U) : R.kerΦ ≤ MulAction.stabilizer (X.Isotropy x) a :=
  fun _ hg => R.mem_stabilizer_iff_Φ.2 (R.mem_kerΦ.1 hg a a.2)

/-- **`T_y` is identified with `T_x` (2021 p. 445, in the proof of Lemma 9.5.10)**: under LUC,
`h ∈ H` corresponds to an element of `T_y` under `H ≅ G_y` iff `ĥ = Φ(h)` is the identity of
`U(x)`. -/
theorem stabilizerEquivIsotropy_mem_trivialSubgroup_iff (hL : R.HasLUC) (a : R.U)
    (h : MulAction.stabilizer (X.Isotropy x) a) :
    R.stabilizerEquivIsotropy a h ∈ X.trivialSubgroup (a : Obj) ↔
      (h : X.Isotropy x) ∈ R.kerΦ := by
  rw [R.mem_kerΦ]
  have hval : (R.stabilizerEquivIsotropy a h).val = R.Γ h a := rfl
  have hfix : R.Φ h a = a := R.mem_stabilizer_iff_Φ.1 h.2
  refine ⟨fun hT => ?_, fun hk => ?_⟩
  · have hev := (X.mem_trivialSet_iff_eventually).1 hT
    rw [hval] at hev
    have hc : ContinuousAt (R.Γ h) a := (R.continuousOn_Γ h).continuousAt
      (R.isOpen_U.mem_nhds a.2)
    have hev' : ∀ᶠ z in 𝓝 (a : Obj), R.Φ h z = z := by
      filter_upwards [hc.eventually hev, R.isOpen_U.mem_nhds a.2] with z hz hzU
      rw [← R.tgt_Γ h z hzU, ← hz, R.src_Γ h z hzU]
    obtain ⟨N, hN, hNo, haN⟩ := mem_nhds_iff.1 hev'
    exact hL h (N ∩ R.U) (hNo.inter R.isOpen_U) ⟨a, haN, a.2⟩ inter_subset_right
      fun y hy => hN hy.1
  · exact X.mem_trivialSet_of_section R.isOpen_U a.2 (R.continuousOn_Γ h)
      (fun z hz => R.src_Γ h z hz) (fun z hz => (R.tgt_Γ h z hz).trans (hk z hz)) hval.symm

/-- Under LUC, `♯T_y = ♯T_x` for `y ∈ U(x)` (2021 p. 445). -/
theorem card_trivialSubgroup_eq (hL : R.HasLUC) (a : R.U) :
    Nat.card (X.trivialSubgroup (a : Obj)) = Nat.card (X.trivialSubgroup x) := by
  have hle : X.trivialSubgroup x ≤ MulAction.stabilizer (X.Isotropy x) a :=
    R.kerΦ_eq_trivialSubgroup hL ▸ R.kerΦ_le_stabilizer a
  set e := R.stabilizerEquivIsotropy a
  refine Nat.card_congr
    { toFun := fun k => ⟨(e.symm k : X.Isotropy x), ?_⟩
      invFun := fun g => ⟨e ⟨g, hle g.2⟩, ?_⟩
      left_inv := fun k => Subtype.ext ?_
      right_inv := fun g => Subtype.ext ?_ }
  · rw [← R.kerΦ_eq_trivialSubgroup hL, ← R.stabilizerEquivIsotropy_mem_trivialSubgroup_iff hL]
    simp [e]
  · rw [R.stabilizerEquivIsotropy_mem_trivialSubgroup_iff hL, R.kerΦ_eq_trivialSubgroup hL]
    exact g.2
  · change e ⟨_, _⟩ = k.1
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
  · change ((e.symm (e ⟨g.1, _⟩) : _) : X.Isotropy x) = g.1
    rw [MulEquiv.symm_apply_apply]

/-- **(9.23), 2021 p. 445 (in the proof of Lemma 9.5.10)**: under LUC, for `y ∈ U(x)` with
stabilizer `H`, `♯R = ♯(G_x/H) = ♯G_x^eff / ♯G_y^eff`, as `♯R · ♯G_y^eff = ♯G_x^eff`. -/
theorem card_quotient_stabilizer_mul_card_effIsotropy (hL : R.HasLUC) (a : R.U) :
    Nat.card (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) *
      Nat.card (X.EffIsotropy (a : Obj)) = Nat.card (X.EffIsotropy x) := by
  have h1 := card_effIsotropy_mul_card_trivialSubgroup (X := X) x
  have h2 := card_effIsotropy_mul_card_trivialSubgroup (X := X) (a : Obj)
  have h3 := R.card_quotient_stabilizer_mul_card_isotropy a
  rw [R.card_trivialSubgroup_eq hL a] at h2
  have ht : 0 < Nat.card (X.trivialSubgroup x) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right ht ?_
  rw [h1, mul_assoc, h2, h3]

end NaturalRep

/-! ### Lemma 9.5.11: morphism invariance -/

/-- **The isotropy orders in Lemma 9.5.11 (2021 p. 445)**: for `φ : x → x'`, `♯G_x = ♯G_{x'}`. -/
theorem card_isotropy_eq_of_mor {x x' : Obj} (φ : Mor) (hx : X.src φ = x) (hx' : X.tgt φ = x') :
    Nat.card (X.Isotropy x) = Nat.card (X.Isotropy x') :=
  Nat.card_congr (X.isotropyConj φ hx hx').toEquiv

/-- **The effective isotropy orders in Lemma 9.5.11 (2021 p. 445)**: for `φ : x → x'`,
`♯G_x^eff = ♯G_{x'}^eff` (`φ T_x φ⁻¹ = T_{x'}`, Lemma 7.2.6). -/
theorem card_effIsotropy_eq_of_mor {x x' : Obj} (φ : Mor) (hx : X.src φ = x)
    (hx' : X.tgt φ = x') : Nat.card (X.EffIsotropy x) = Nat.card (X.EffIsotropy x') := by
  rw [Nat.card_congr (X.effIsotropyEquiv x).toEquiv, Nat.card_congr (X.effIsotropyEquiv x').toEquiv]
  exact Nat.card_congr (QuotientGroup.congr _ _ (X.isotropyConj φ hx hx')
    (X.map_isotropyConj_trivialSubgroup φ hx hx')).toEquiv

/-- A functor `Θ` is constant on the fibres of `π`. -/
theorem IsFunctorial.eq_of_π_eq {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ) {y z : Obj}
    (h : X.π y = X.π z) : Θ y = Θ z := by
  obtain ⟨φ, hs, ht⟩ := (X.π_eq_π_iff).1 h
  rw [← hs, ← ht]
  exact hΘ φ

/-- **`|M_U| = |M_{U'}|` in Lemma 9.5.11 (2021 p. 445)**: if `φ̂ : U → U'` is onto and
`|φ̂(z)| = |z|` (as for the local sc-diffeomorphism `t ∘ s⁻¹` of a morphism), then two local
branching structures on `U` and `U'` have the same image `|M_U| = |M_{U'}|` in `|X|`. -/
theorem image_π_MU_eq {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ) {x x' : Obj}
    (B : X.LocalBranchingStructure Θ x) (B' : X.LocalBranchingStructure Θ x') {f : Obj → Obj}
    (hf : MapsTo f B.U B'.U) (hfs : SurjOn f B.U B'.U) (hπ : ∀ z ∈ B.U, X.π (f z) = X.π z) :
    X.π '' B.MU = X.π '' B'.MU := by
  rw [B.MU_eq, B'.MU_eq]
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨z, ⟨hzs, hzU⟩, rfl⟩
    refine ⟨f z, ⟨?_, hf hzU⟩, hπ z hzU⟩
    change 0 < Θ (f z)
    rw [hΘ.eq_of_π_eq (hπ z hzU)]
    exact hzs
  · rintro _ ⟨z', ⟨hzs, hzU⟩, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hfs hzU
    refine ⟨z, ⟨?_, hz⟩, (hπ z hz).symm⟩
    change 0 < Θ z
    rw [← hΘ.eq_of_π_eq (hπ z hz)]
    exact hzs

/-- **The hypotheses of `image_π_MU_eq` are satisfiable**: for `φ = g ∈ G_x` the natural local
sc-diffeomorphism is `ϕ_g : U(x) → U(x)`, which is onto with `|ϕ_g(z)| = |z|`. -/
theorem NaturalRep.Φ_hyps (R : X.NaturalRep x) (g : X.Isotropy x) :
    MapsTo (R.Φ g) R.U R.U ∧ SurjOn (R.Φ g) R.U R.U ∧ ∀ z ∈ R.U, X.π (R.Φ g z) = X.π z :=
  ⟨R.mapsTo_Φ g, fun z hz => ⟨R.Φ g⁻¹ z, R.mapsTo_Φ g⁻¹ hz, R.Φ_Φ_inv g hz⟩,
    fun _ hz => R.π_Φ g hz⟩

/-! ### Proposition 9.5.13: the normalizing factors -/

/-- **Proposition 9.5.13 (1), the normalizing factors (2021 p. 446, new in the 2021 edition)**:
if `X` is effective then `T_x = {1}`, so `G_x^eff = G_x` and the factors `1/♯G_x^eff` and
`1/♯G_x` of the two local measures agree. -/
theorem card_effIsotropy_eq_of_isEffective (hX : X.IsEffective) (x : Obj) :
    Nat.card (X.EffIsotropy x) = Nat.card (X.Isotropy x) := by
  have h := card_effIsotropy_mul_card_trivialSubgroup (X := X) x
  rwa [X.isEffective_iff_trivialSubgroup_eq_bot.1 hX x, Subgroup.card_bot, mul_one] at h

section Reduced

variable (X)

/-- A function on the objects is a functor on `X_R` iff it is one on `X` (2021 p. 446, the data
induced on the reduced ep-groupoid in Proposition 9.5.13 (2)). -/
theorem isFunctorial_reduced_iff [T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor]
    {Θ : Obj → ℚ} : X.reducedEpGroupoid.IsFunctorial Θ ↔ X.IsFunctorial Θ := by
  refine ⟨fun h φ => h (X.reducedπ φ), fun h q => ?_⟩
  obtain ⟨φ, rfl⟩ := X.surjective_reducedπ q
  exact h φ

/-- A local branching structure of `Θ` on `X` is one on `X_R`: the definition only involves the
object M-polyfold, which `X` and `X_R` share. -/
def LocalBranchingStructure.toReduced [T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor]
    {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x) :
    X.reducedEpGroupoid.LocalBranchingStructure Θ x where
  U := B.U
  isOpen_U := B.isOpen_U
  mem_U := B.mem_U
  ι := B.ι
  M := B.M
  subset_U := B.subset_U
  isSmoothSubmanifold := B.isSmoothSubmanifold
  mem_M := B.mem_M
  isProperMap := B.isProperMap
  σ := B.σ
  σ_pos := B.σ_pos
  eq_sum := B.eq_sum

/-- **Proposition 9.5.13 (2), the normalizing factors (2021 p. 446, new in the 2021 edition)**:
the isotropy group of `x` in `X_R` is `G_x^eff` (`effIsotropyEquivReduced`), so the factor
`1/♯G_x^eff` on `X` equals the factor `1/♯G_x^R = 1/♯(G_x^R)^eff` on the effective `X_R`. -/
theorem card_effIsotropy_eq_reduced [T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor]
    (x : Obj) :
    Nat.card (X.EffIsotropy x) = Nat.card (X.reducedEpGroupoid.Isotropy x) ∧
      Nat.card (X.reducedEpGroupoid.EffIsotropy x) = Nat.card (X.reducedEpGroupoid.Isotropy x) :=
  ⟨Nat.card_congr (X.effIsotropyEquivReduced x).toEquiv,
    card_effIsotropy_eq_of_isEffective X.isEffective_reducedEpGroupoid x⟩

end Reduced

end EpGroupoid

end Polyfold
