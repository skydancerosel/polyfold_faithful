import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_57

/-! Round trip for V6_57 (Theorem 6.37, the functor `Γ_f`).

A is the conjunction of the 12 theorems of the row (universes at `0`).  The project's Theorem 6.37
(`theorem_6_6_13_hyp`) assumes, beyond B's setting (tame `X`, `f` sc-Fredholm): sc-smooth bump functions
(`PX.AdmitsBumpFunctions`), a TAME sc-Fredholm section (`IsScFredholmSectionTame`), sc⁺-sections
through every fibre point (`HasScPlusSectionsThrough`, a consequence of the bump functions) and two
more families of paracompactness instances.  So `A → B` cannot be proved: B gives none of these.

What A gives, under these hypotheses, is proved below (`A_to_BExtra`):
* existence: the family `G(γ) = Γ_f([γ])` on representatives is a functor in B's sense (constant on
  classes, identities, and the composition rule for EVERY admissible `β`, since each `β`-composite
  is homotopic rel end points to `concatPath`) with B's property (∗) (A's (∗) holds on all open sets
  with the local propagation property, B asks it only on the sc-smoothly contractible ones);
* uniqueness, under the extra hypothesis `ContractibleCover`: every smooth point lies in an open,
  sc-smoothly contractible set with the local propagation property in some chart
  (`orFunctorMap_unique_of_cover` for the family of open contractible sets).
Without `ContractibleCover` B's uniqueness is not available: B's (∗) constrains `G` only on paths
inside contractible sets with the local propagation property; the project proves the existence of
open sets with the local propagation property (Theorem 6.35) but never that contractible ones exist
(Proposition 6.28 gives (1′) instead), and a functor twisted by the swap of `Or_x^f` at a smooth point
lying in no such set would satisfy B's (∗) as well.

`B → A` is not proved: A's conjuncts are statements about the project's constructions (`orPush`,
`orLocalTransport`, `orFunctorMap`, (∗) on all open propagation sets, the cover form of the
uniqueness), which B does not mention.
-/

namespace RoundTrip.V6_57
open Polyfold Set Filter Topology CategoryTheory
open scoped ContDiff

/-- The project's statement (the 12 theorems of the row), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.orPush_eq.{0, 0} ∧
  type_of% @Polyfold.orPush_compat.{0, 0} ∧
  type_of% @Polyfold.orPush_trans.{0, 0} ∧
  type_of% @Polyfold.orLocalTransport_transport_eq.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.transport_apply_eq_of_local.{0, 0} ∧
  type_of% @Polyfold.orFunctorMap_mk.{0, 0} ∧
  type_of% @Polyfold.orFunctorMap_id.{0, 0} ∧
  type_of% @Polyfold.orFunctorMap_comp.{0, 0} ∧
  type_of% @Polyfold.orFunctorMap_isStarProperty.{0, 0} ∧
  type_of% @Polyfold.orFunctorMap_unique_of_cover.{0, 0} ∧
  type_of% @Polyfold.orFunctorMap_unique.{0, 0} ∧
  type_of% @Polyfold.theorem_6_6_13_hyp.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.orPush_eq.{0, 0}, @Polyfold.orPush_compat.{0, 0}, @Polyfold.orPush_trans.{0, 0},
    @Polyfold.orLocalTransport_transport_eq.{0, 0},
    @Polyfold.LocalTransport.transport_apply_eq_of_local.{0, 0}, @Polyfold.orFunctorMap_mk.{0, 0},
    @Polyfold.orFunctorMap_id.{0, 0}, @Polyfold.orFunctorMap_comp.{0, 0},
    @Polyfold.orFunctorMap_isStarProperty.{0, 0}, @Polyfold.orFunctorMap_unique_of_cover.{0, 0},
    @Polyfold.orFunctorMap_unique.{0, 0}, @Polyfold.theorem_6_6_13_hyp.{0, 0}⟩

local notation "κ" => Real.smoothTransition

/-! ### Glue: admissible `β`, `β`-composites and `concatPath` (as in V6_52) -/

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- `β(1/2) = 1` from the two image conditions. -/
theorem beta_half {β : ℝ → ℝ} (h₁ : β '' Icc 0 (1 / 2) = Icc 0 1)
    (h₂ : β '' Icc (1 / 2) 1 = Icc 1 2) : β (1 / 2) = 1 := by
  have a : β (1 / 2) ∈ Icc (0 : ℝ) 1 := h₁ ▸ mem_image_of_mem β ⟨by norm_num, le_rfl⟩
  have b : β (1 / 2) ∈ Icc (1 : ℝ) 2 := h₂ ▸ mem_image_of_mem β ⟨le_rfl, by norm_num⟩
  exact le_antisymm a.2 b.1

/-- An `ε`-neighbourhood of `1/2` on which `β = 1`. -/
theorem exists_beta_eq_one {β : ℝ → ℝ} (h₁ : β '' Icc 0 (1 / 2) = Icc 0 1)
    (h₂ : β '' Icc (1 / 2) 1 = Icc 1 2) (h : ∀ᶠ s in 𝓝 (1 / 2 : ℝ), β s = β (1 / 2)) :
    ∃ ε > 0, ∀ s, |s - 1 / 2| < ε → β s = 1 := by
  obtain ⟨ε, hε, hεβ⟩ := Metric.eventually_nhds_iff.1 h
  exact ⟨ε, hε, fun s hs => (hεβ (by rwa [Real.dist_eq])).trans (beta_half h₁ h₂)⟩

/-- **Every `β`-composite is homotopic rel end points to `concatPath`** (straight-line homotopy of
the inner reparametrizations; near `s = 1/2` both pieces are the junction point). -/
theorem scHomotopic_concatPath_of_beta {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    (hβ1 : β 1 = 2) {ε : ℝ} (hε : 0 < ε) (hβc : ∀ s, |s - 1 / 2| < ε → β s = 1)
    {φ ψ γ : (Fin 1 → ℝ) → X} (hφ : (rnPolyfold 1).IsScSmoothMap PX φ)
    (hψ : (rnPolyfold 1).IsScSmoothMap PX ψ) (hj : φ (pt1 1) = ψ (pt1 0))
    (h₁ : ∀ s ∈ Icc (0 : ℝ) (1 / 2), γ (pt1 s) = φ (pt1 (β s)))
    (h₂ : ∀ s ∈ Icc (1 / 2 : ℝ) 1, γ (pt1 s) = ψ (pt1 (β s - 1))) :
    ScHomotopic PX γ (concatPath φ ψ) := by
  have hκ₁ : ContDiff ℝ ∞ fun t : ℝ => κ (3 * t) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)
  have hκ₂ : ContDiff ℝ ∞ fun t : ℝ => κ (3 * t - 2) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  refine ⟨fun q => if q 1 ≤ 1 / 2 then φ (pt1 ((1 - q 0) * β (q 1) + q 0 * κ (3 * q 1)))
    else ψ (pt1 ((1 - q 0) * (β (q 1) - 1) + q 0 * κ (3 * q 1 - 2))), ?_, ?_, ?_, ?_, ?_⟩
  · refine isScSmoothMap_ite (σ := fun q => q 1) (continuous_apply 1)
      (lt_min hε (show (0 : ℝ) < 1 / 6 by norm_num))
      (isScSmoothMap_comp_pt1₂ hφ (contDiff_lerp hβ hκ₁))
      (isScSmoothMap_comp_pt1₂ hψ (contDiff_lerp (hβ.sub contDiff_const) hκ₂)) fun q hq => ?_
    have hq₁ : |q 1 - 1 / 2| < ε := hq.trans_le (min_le_left _ _)
    have hq₂ := abs_sub_lt_iff.1 (hq.trans_le (min_le_right _ _))
    change φ (pt1 ((1 - q 0) * β (q 1) + q 0 * κ (3 * q 1))) =
      ψ (pt1 ((1 - q 0) * (β (q 1) - 1) + q 0 * κ (3 * q 1 - 2)))
    rw [hβc _ hq₁, Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith), sub_self, mul_zero, mul_zero, add_zero,
      mul_one, mul_one, sub_add_cancel, hj]
  · intro t ht
    simp only [pt2_apply_zero, pt2_apply_one, sub_zero, one_mul, zero_mul, add_zero]
    split_ifs with h
    · exact (h₁ t ⟨ht.1, h⟩).symm
    · exact (h₂ t ⟨(not_le.1 h).le, ht.2⟩).symm
  · intro t _
    simp only [pt2_apply_zero, pt2_apply_one, sub_self, zero_mul, zero_add, one_mul]
    simp only [concatPath, pt1_apply]
    by_cases h : t ≤ 1 / 2 <;> simp
  · intro τ _
    simp only [pt2_apply_zero, pt2_apply_one]
    rw [if_pos (by norm_num), h₁ 0 ⟨le_rfl, by norm_num⟩, hβ0]
    simp only [mul_zero, Real.smoothTransition.zero, add_zero]
  · intro τ _
    simp only [pt2_apply_zero, pt2_apply_one]
    rw [if_neg (by norm_num), h₂ 1 ⟨by norm_num, le_rfl⟩, hβ1]
    have e : (1 - τ) * ((2 : ℝ) - 1) + τ * κ (3 * 1 - 2) = 2 - 1 := by
      rw [show (3 : ℝ) * 1 - 2 = 1 by norm_num, Real.smoothTransition.one]
      ring
    rw [e]

/-- `β₀(s) = κ(3s) + κ(3s − 2)`, the reparametrization behind `concatPath`. -/
noncomputable def β₀ (s : ℝ) : ℝ := κ (3 * s) + κ (3 * s - 2)

theorem contDiff_β₀ : ContDiff ℝ ∞ β₀ :=
  (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)).add
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

theorem β₀_of_le {s : ℝ} (hs : s ≤ 2 / 3) : β₀ s = κ (3 * s) := by
  have h : κ (3 * s - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  rw [β₀, h, add_zero]

theorem β₀_of_ge {s : ℝ} (hs : 1 / 3 ≤ s) : β₀ s = 1 + κ (3 * s - 2) := by
  rw [β₀, Real.smoothTransition.one_of_one_le (by linarith)]

theorem β₀_eq_one {s : ℝ} (h₁ : 1 / 3 ≤ s) (h₂ : s ≤ 2 / 3) : β₀ s = 1 := by
  have h : κ (3 * s - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  rw [β₀_of_ge h₁, h, add_zero]

theorem isAdmissibleBetaB_β₀ : IsAdmissibleBetaB β₀ := by
  have hc : Continuous β₀ := contDiff_β₀.continuous
  have h0 : β₀ 0 = 0 := by rw [β₀_of_le (by norm_num), mul_zero, Real.smoothTransition.zero]
  have h1 : β₀ 1 = 2 := by
    rw [β₀_of_ge (by norm_num), show (3 : ℝ) * 1 - 2 = 1 by norm_num, Real.smoothTransition.one]
    norm_num
  refine ⟨contDiff_β₀, h0, h1, Subset.antisymm ?_ ?_, Subset.antisymm ?_ ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [β₀_of_le (by linarith [hs.2])]
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · have h := intermediate_value_Icc (show (0 : ℝ) ≤ 1 / 3 by norm_num) hc.continuousOn
    rw [h0, β₀_eq_one le_rfl (by norm_num)] at h
    exact h.trans (image_mono (Icc_subset_Icc le_rfl (by norm_num)))
  · rintro _ ⟨s, hs, rfl⟩
    rw [β₀_of_ge (by linarith [hs.1])]
    exact ⟨by linarith [Real.smoothTransition.nonneg (3 * s - 2)],
      by linarith [Real.smoothTransition.le_one (3 * s - 2)]⟩
  · have h := intermediate_value_Icc (show (2 / 3 : ℝ) ≤ 1 by norm_num) hc.continuousOn
    rw [h1, β₀_eq_one (by norm_num) le_rfl] at h
    exact h.trans (image_mono (Icc_subset_Icc (by norm_num) le_rfl))
  · filter_upwards [Ioo_mem_nhds (show (1 / 3 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 2 / 3 by norm_num)] with s hs
    rw [β₀_eq_one hs.1.le hs.2.le, β₀_eq_one (by norm_num) (by norm_num)]

/-- `concatPath φ ψ` is a `β₀`-composite of `φ` and `ψ` (B's `IsConcatB`). -/
theorem isConcatB_concatPath {φ ψ : (Fin 1 → ℝ) → X} (hj : φ (pt1 1) = ψ (pt1 0)) :
    IsConcatB β₀ φ ψ (concatPath φ ψ) := by
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [concatPath_of_le_two_thirds hj (by linarith [hs.2]), β₀_of_le (by linarith [hs.2])]
  · rw [concatPath_of_one_third_le hj (by linarith [hs.1]), β₀_of_ge (by linarith [hs.1]),
      add_sub_cancel_left]

end Glue

/-! ### B with the hypotheses of the project's Theorem 6.37, and the covering hypothesis -/

section Cover

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  {Bd : StrongBundle PX P}

/-- **The covering hypothesis** (not proved in the project, not a hypothesis of the text): every
smooth point lies in an open, sc-smoothly contractible set with the local propagation property in a
chart. -/
def ContractibleCover (f : X → Y) (hf : Bd.IsScFredholmSection f) : Prop :=
  ∀ x ∈ PX.smoothSet, ∃ (c : StrongBundleChart PX P) (hc : Bd.IsChart c) (U : Set X),
    IsOpen U ∧ x ∈ U ∧ IsScContractibleB PX U ∧ HasLocalPropagation f hf c hc U

end Cover

/-- **B under the project's hypotheses** (bump functions, a tame sc-Fredholm section, the further
paracompactness instances): existence of a functor with B's property (∗), and its uniqueness under
`ContractibleCover`. -/
def BExtra : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × (Fin n → ℝ) × X)]
    [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
    (Bd : StrongBundle PX P) (f : X → Y) (hfT : Bd.IsScFredholmSectionTame f),
    PX.IsTame → PX.AdmitsBumpFunctions →
      (∃ G : GammaDataB PX f hfT.toIsScFredholmSection,
        IsFunctorB f hfT.toIsScFredholmSection G ∧ IsStarB f hfT.toIsScFredholmSection G) ∧
      (ContractibleCover f hfT.toIsScFredholmSection →
        ∃! G : GammaDataB PX f hfT.toIsScFredholmSection,
          IsFunctorB f hfT.toIsScFredholmSection G ∧ IsStarB f hfT.toIsScFredholmSection G)

theorem A_to_BExtra : A → BExtra := by
  intro hA
  obtain ⟨-, -, -, -, -, -, -, -, -, huc, -, h637⟩ := hA
  intro X _ _ _ PX Y _ _ _ P _ _ _ _ _ _ Bd f hfT hX hbump
  have hsec : Bd.HasScPlusSectionsThrough := hbump.hasScPlusSectionsThrough
  obtain ⟨Gc, ⟨hid, hcomp, hstar⟩, -⟩ := h637 hX hbump hfT hsec
  -- `Γ_f` on representatives
  let G : GammaDataB PX f hfT.toIsScFredholmSection := fun x y hx hy γ hγ =>
    Gc ⟨x, hx⟩ ⟨y, hy⟩ (PathCat.homMk ⟨γ, hγ.1, hγ.2.1, hγ.2.2⟩)
  have hGF : IsFunctorB f hfT.toIsScFredholmSection G := by
    refine ⟨fun x y hx hy γ γ' hγ hγ' h => ?_, fun x hx h => ?_,
      fun β hβ x y z hx hy hz φ ψ γ hφ hψ hγ hc => ?_⟩
    · exact congrArg (Gc ⟨x, hx⟩ ⟨y, hy⟩) (PathCat.mk_eq_mk_iff.2 h)
    · have e : (⟨fun _ => x, h.1, h.2.1, h.2.2⟩ : ScPath PX x x) = ScPath.const x hx :=
        ScPath.ext rfl
      change Gc ⟨x, hx⟩ ⟨x, hx⟩ (PathCat.homMk ⟨fun _ => x, h.1, h.2.1, h.2.2⟩) = Equiv.refl _
      rw [e]
      exact hid ⟨x, hx⟩
    · obtain ⟨hβs, hβ0, hβ1, hβi₁, hβi₂, hβe⟩ := hβ
      obtain ⟨ε, hε, hβc⟩ := exists_beta_eq_one hβi₁ hβi₂ hβe
      have hh : ScHomotopic PX γ (concatPath φ ψ) :=
        scHomotopic_concatPath_of_beta hβs hβ0 hβ1 hε hβc hφ.1 hψ.1 (hφ.2.2.trans hψ.2.1.symm)
          hc.1 hc.2
      have e : (PathCat.homMk ⟨γ, hγ.1, hγ.2.1, hγ.2.2⟩ : (⟨x, hx⟩ : PathCat PX) ⟶ ⟨z, hz⟩) =
          PathCat.homMk (y := ⟨y, hy⟩) ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩ ≫
            PathCat.homMk ⟨ψ, hψ.1, hψ.2.1, hψ.2.2⟩ := by
        rw [PathCat.comp_mk]
        exact PathCat.mk_eq_mk_iff.2 hh
      change Gc ⟨x, hx⟩ ⟨z, hz⟩ (PathCat.homMk ⟨γ, hγ.1, hγ.2.1, hγ.2.2⟩) = _
      rw [e, hcomp]
  have hGS : IsStarB f hfT.toIsScFredholmSection G :=
    fun c hc U hUo _ hLP x y hx hy γ hγ hγU _ hxc hyc e he =>
      hstar c hc U hUo hLP ⟨x, hx⟩ ⟨y, hy⟩ ⟨γ, hγ.1, hγ.2.1, hγ.2.2⟩ hγU hxc hyc e he
  refine ⟨⟨G, hGF, hGS⟩, fun hcov => ⟨G, ⟨hGF, hGS⟩, fun G' ⟨hG'F, hG'S⟩ => ?_⟩⟩
  -- `G'` on classes
  let G'c : ∀ x y : PathCat PX, (x ⟶ y) → (Orx f hfT.toIsScFredholmSection x.pt x.smooth ≃
      Orx f hfT.toIsScFredholmSection y.pt y.smooth) := fun x y a =>
    Quotient.lift (s := ScPath.setoid PX x.pt y.pt)
      (fun φ => G' x.pt y.pt x.smooth y.smooth φ.toFun ⟨φ.isScSmoothMap, φ.source, φ.target⟩)
      (fun φ ψ h => hG'F.1 _ _ _ _ _ _ _ _ h) a
  have hG'c_comp : ∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
      G'c x z (a ≫ b) = (G'c x y a).trans (G'c y z b) := by
    intro x y z a b
    obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
    obtain ⟨ψ, rfl⟩ := PathCat.exists_eq_mk b
    rw [PathCat.comp_mk]
    exact hG'F.2.2 β₀ isAdmissibleBetaB_β₀ x.pt y.pt z.pt x.smooth y.smooth z.smooth φ.toFun
      ψ.toFun _ ⟨φ.isScSmoothMap, φ.source, φ.target⟩ ⟨ψ.isScSmoothMap, ψ.source, ψ.target⟩
      ⟨(φ.concat ψ).isScSmoothMap, (φ.concat ψ).source, (φ.concat ψ).target⟩
      (isConcatB_concatPath (φ.target.trans ψ.source.symm))
  let W : Set X → Prop := fun U => IsOpen U ∧ IsScContractibleB PX U
  have hG'cS : IsStarPropertyOn f hfT.toIsScFredholmSection W G'c :=
    fun c hc U hW hU x y φ hφ hx hy e he =>
      hG'S c hc U hW.1 hW.2 hU x.pt y.pt x.smooth y.smooth φ.toFun
        ⟨φ.isScSmoothMap, φ.source, φ.target⟩ hφ (fun q hq => hU.subset (hφ q hq)) hx hy e he
  have hWc : ∀ x ∈ PX.smoothSet, ∃ U, W U ∧ x ∈ U ∧ ∃ (c : StrongBundleChart PX P)
      (hc : Bd.IsChart c), HasLocalPropagation f hfT.toIsScFredholmSection c hc U :=
    fun x hx =>
      let ⟨c, hc, U, hUo, hxU, hUc, hLP⟩ := hcov x hx
      ⟨U, ⟨hUo, hUc⟩, hxU, c, hc, hLP⟩
  have e' := huc hX hbump hfT hsec W (fun h => h.1) hWc G'c hG'c_comp hG'cS
  have e := huc hX hbump hfT hsec W (fun h => h.1) hWc Gc hcomp
    (fun c hc U hW => hstar c hc U hW.1)
  funext x y hx hy γ hγ
  exact congrFun (congrFun (congrFun (e'.trans e.symm) ⟨x, hx⟩) ⟨y, hy⟩)
    (PathCat.homMk ⟨γ, hγ.1, hγ.2.1, hγ.2.2⟩)

/-! `A → B` is not proved: B's setting gives neither `PX.AdmitsBumpFunctions` nor
`Bd.IsScFredholmSectionTame f` (nor the families of paracompactness instances `∀ k n`), which every
theorem of A assumes (`HasScPlusSectionsThrough` follows from the bump functions); and B's
uniqueness needs `ContractibleCover`, which A does not give.  These hypotheses are satisfiable
(bump functions: `MPolyfold.admitsBumpFunctions_of_hilbert`; sc⁺-sections:
`MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough`), so A is not vacuous; but they are not
consequences of B's hypotheses. -/

open Lean Elab Command in
/-- `#rt_check_except_defs T [d₁, …] [n₁, …]` (as in items V1_32, V2_24, V3_64, V6_19): the harness
traversal `rtCollect` with the bodies of the definitions `dᵢ` not unfolded; fails if the proof of
`T` reaches some `nᵢ` elsewhere. -/
elab "#rt_check_except_defs " t:ident " [" ds:ident,* "]" " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let seen := ds.getElems.foldl (fun s d => s.insert d.getId) NameSet.empty
  let used := rtCollect env roots.toList seen
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do throwError "FAIL: {t.getId} uses {bad} outside the bodies of the definitions"
  logInfo m!"OK: {t.getId} reaches the banned declarations only through the bodies of the definitions {ds.getElems.toList.map (·.getId)}"

#rt_check_soft RoundTrip.V6_57.A_to_BExtra [Polyfold.orPush_eq, Polyfold.orPush_compat,
  Polyfold.orPush_trans, Polyfold.orLocalTransport_transport_eq,
  Polyfold.LocalTransport.transport_apply_eq_of_local, Polyfold.orFunctorMap_mk,
  Polyfold.orFunctorMap_id, Polyfold.orFunctorMap_comp, Polyfold.orFunctorMap_isStarProperty,
  Polyfold.orFunctorMap_unique_of_cover, Polyfold.orFunctorMap_unique, Polyfold.theorem_6_6_13_hyp]
#rt_overlap RoundTrip.V6_57.A_to_BExtra [Polyfold.orPush_eq, Polyfold.orPush_compat,
  Polyfold.orPush_trans, Polyfold.orLocalTransport_transport_eq,
  Polyfold.LocalTransport.transport_apply_eq_of_local, Polyfold.orFunctorMap_mk,
  Polyfold.orFunctorMap_id, Polyfold.orFunctorMap_comp, Polyfold.orFunctorMap_isStarProperty,
  Polyfold.orFunctorMap_unique_of_cover, Polyfold.orFunctorMap_unique, Polyfold.theorem_6_6_13_hyp]

end RoundTrip.V6_57
