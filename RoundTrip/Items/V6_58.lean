import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_58

/-! Round trip for V6_58 (Definition 6.38, orientable sections).

A is the type of `isOrientableSection_iff_exists` (universes at `0`): the project's orientability
(`IsOrientableSection`, `Γ_f([φ])` independent of `[φ] : x ⟶ y`, with `Γ_f = orFunctorMap`) iff some
`y ↦ o_y` is carried along by `Γ_f`.  B is a statement about the DEFINITION: the project's
`IsOrientableSection` (which takes the hypotheses `hX`, `hbump`, a tame `hfT`, `hsec`) is the text's
notion `IsOrientableB`: every family `G` which is a functor `PX → 𝒪_f` (B's `IsFunctorB`) with B's
property (∗) (only on sc-smoothly contractible open sets with the local propagation property)
takes the same value on all paths `x → y`.

Proved here (without A, which says nothing about `IsOrientableB`):
* `isOrientableSection_of_isOrientableB` (B's `←`, unconditionally): `Γ_f` on representatives
  (`Grep`) is such a `G` (`isFunctorB_Grep`, `isStarB_Grep`: (∗) holds on all open propagation sets,
  every admissible `β`-composite is homotopic to `concatPath`).
* `isOrientableB_of_isOrientableSection` (B's `→`) under `ContractibleCover` (every smooth point
  lies in an open sc-smoothly contractible set with the local propagation property), by the
  uniqueness `eq_Grep_of_cover`; hence `B_of_cover`: B with that hypothesis added.
B's `→` without the cover is not proved: B's (∗) then constrains `G` only on the paths inside the
contractible propagation sets that exist, and `G` may differ from `Γ_f` by a homomorphism
`PX → ℤ/2` trivial on those paths (all `Or_x^f` have two elements and the swap commutes with every
bijection), which need not be trivial on loops.  The project never shows that contractible
propagation sets cover `X_∞` (Proposition 6.28 gives (1′)), and B's setting assumes nothing that
would give them.

`A → B` is therefore not proved (it would need the cover).  `B → A` is proved only by proving A
outright (`exists_apply_eq_of_isOrientableSection`, `isOrientableSection_of_apply_eq`): vacuous.
-/

namespace RoundTrip.V6_58
open Polyfold Set Filter Topology CategoryTheory
open scoped ContDiff

/-- The project's statement (`isOrientableSection_iff_exists`), universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.isOrientableSection_iff_exists.{0, 0}

theorem A_holds : A := @Polyfold.isOrientableSection_iff_exists.{0, 0}

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

section Gamma

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × (Fin n → ℝ) × X)]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
  {Bd : StrongBundle PX P} {f : X → Y}

/-- **The covering hypothesis** (not proved in the project, not a hypothesis of the text): every
smooth point lies in an open, sc-smoothly contractible set with the local propagation property in a
chart. -/
def ContractibleCover (f : X → Y) (hf : Bd.IsScFredholmSection f) : Prop :=
  ∀ x ∈ PX.smoothSet, ∃ (c : StrongBundleChart PX P) (hc : Bd.IsChart c) (U : Set X),
    IsOpen U ∧ x ∈ U ∧ IsScContractibleB PX U ∧ HasLocalPropagation f hf c hc U

variable (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hfT : Bd.IsScFredholmSectionTame f)
  (hsec : Bd.HasScPlusSectionsThrough)

/-- `Γ_f` on representatives: `G(γ) = Γ_f([γ])`. -/
noncomputable def Grep : GammaDataB PX f hfT.toIsScFredholmSection := fun x y hx hy γ hγ =>
  orFunctorMap hX hbump hfT hsec (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)
    (PathCat.homMk ⟨γ, hγ.1, hγ.2.1, hγ.2.2⟩)

theorem isFunctorB_Grep : IsFunctorB f hfT.toIsScFredholmSection (Grep hX hbump hfT hsec) := by
  refine ⟨fun x y hx hy γ γ' hγ hγ' h => ?_, fun x hx h => ?_,
    fun β hβ x y z hx hy hz φ ψ γ hφ hψ hγ hc => ?_⟩
  · exact congrArg (orFunctorMap hX hbump hfT hsec) (PathCat.mk_eq_mk_iff.2 h)
  · have e : (⟨fun _ => x, h.1, h.2.1, h.2.2⟩ : ScPath PX x x) = ScPath.const x hx :=
      ScPath.ext rfl
    change orFunctorMap hX hbump hfT hsec (x := ⟨x, hx⟩) (y := ⟨x, hx⟩)
      (PathCat.homMk ⟨fun _ => x, h.1, h.2.1, h.2.2⟩) = Equiv.refl _
    rw [e]
    exact orFunctorMap_id hX hbump hfT hsec ⟨x, hx⟩
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
    change orFunctorMap hX hbump hfT hsec (PathCat.homMk ⟨γ, hγ.1, hγ.2.1, hγ.2.2⟩) = _
    rw [e, orFunctorMap_comp]
    rfl

theorem isStarB_Grep : IsStarB f hfT.toIsScFredholmSection (Grep hX hbump hfT hsec) :=
  fun c hc U hUo _ hLP x y hx hy γ hγ hγU _ hxc hyc e he =>
    orFunctorMap_isStarProperty hX hbump hfT hsec c hc U hUo hLP ⟨x, hx⟩ ⟨y, hy⟩
      ⟨γ, hγ.1, hγ.2.1, hγ.2.2⟩ hγU hxc hyc e he

/-- **Uniqueness under the covering hypothesis**: a functor with B's property (∗) is `Γ_f`
(`orFunctorMap_unique_of_cover` for the open sc-smoothly contractible sets). -/
theorem eq_Grep_of_cover (hcov : ContractibleCover f hfT.toIsScFredholmSection)
    (G : GammaDataB PX f hfT.toIsScFredholmSection) (hGF : IsFunctorB f hfT.toIsScFredholmSection G)
    (hGS : IsStarB f hfT.toIsScFredholmSection G) : G = Grep hX hbump hfT hsec := by
  let Gc : ∀ x y : PathCat PX, (x ⟶ y) → (Orx f hfT.toIsScFredholmSection x.pt x.smooth ≃
      Orx f hfT.toIsScFredholmSection y.pt y.smooth) := fun x y a =>
    Quotient.lift (s := ScPath.setoid PX x.pt y.pt)
      (fun φ => G x.pt y.pt x.smooth y.smooth φ.toFun ⟨φ.isScSmoothMap, φ.source, φ.target⟩)
      (fun φ ψ h => hGF.1 _ _ _ _ _ _ _ _ h) a
  have hGc_comp : ∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
      Gc x z (a ≫ b) = (Gc x y a).trans (Gc y z b) := by
    intro x y z a b
    obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
    obtain ⟨ψ, rfl⟩ := PathCat.exists_eq_mk b
    rw [PathCat.comp_mk]
    exact hGF.2.2 β₀ isAdmissibleBetaB_β₀ x.pt y.pt z.pt x.smooth y.smooth z.smooth φ.toFun
      ψ.toFun _ ⟨φ.isScSmoothMap, φ.source, φ.target⟩ ⟨ψ.isScSmoothMap, ψ.source, ψ.target⟩
      ⟨(φ.concat ψ).isScSmoothMap, (φ.concat ψ).source, (φ.concat ψ).target⟩
      (isConcatB_concatPath (φ.target.trans ψ.source.symm))
  let W : Set X → Prop := fun U => IsOpen U ∧ IsScContractibleB PX U
  have hGcS : IsStarPropertyOn f hfT.toIsScFredholmSection W Gc :=
    fun c hc U hW hU x y φ hφ hx hy e he =>
      hGS c hc U hW.1 hW.2 hU x.pt y.pt x.smooth y.smooth φ.toFun
        ⟨φ.isScSmoothMap, φ.source, φ.target⟩ hφ (fun q hq => hU.subset (hφ q hq)) hx hy e he
  have hWc : ∀ x ∈ PX.smoothSet, ∃ U, W U ∧ x ∈ U ∧ ∃ (c : StrongBundleChart PX P)
      (hc : Bd.IsChart c), HasLocalPropagation f hfT.toIsScFredholmSection c hc U :=
    fun x hx =>
      let ⟨c, hc, U, hUo, hxU, hUc, hLP⟩ := hcov x hx
      ⟨U, ⟨hUo, hUc⟩, hxU, c, hc, hLP⟩
  have e := orFunctorMap_unique_of_cover hX hbump hfT hsec W (fun h => h.1) hWc Gc hGc_comp hGcS
  funext x y hx hy γ hγ
  exact congrFun (congrFun (congrFun e ⟨x, hx⟩) ⟨y, hy⟩) (PathCat.homMk ⟨γ, hγ.1, hγ.2.1, hγ.2.2⟩)

/-- **B's `←`**: the text's orientability (as B reads it) implies the project's. -/
theorem isOrientableSection_of_isOrientableB (h : IsOrientableB f hfT.toIsScFredholmSection) :
    IsOrientableSection hX hbump hfT hsec := by
  intro x y a b
  obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
  obtain ⟨ψ, rfl⟩ := PathCat.exists_eq_mk b
  exact h (Grep hX hbump hfT hsec) (isFunctorB_Grep hX hbump hfT hsec)
    (isStarB_Grep hX hbump hfT hsec) x.pt y.pt x.smooth y.smooth φ.toFun ψ.toFun
    ⟨φ.isScSmoothMap, φ.source, φ.target⟩ ⟨ψ.isScSmoothMap, ψ.source, ψ.target⟩

/-- **B's `→` under the covering hypothesis.** -/
theorem isOrientableB_of_isOrientableSection (hcov : ContractibleCover f hfT.toIsScFredholmSection)
    (h : IsOrientableSection hX hbump hfT hsec) : IsOrientableB f hfT.toIsScFredholmSection := by
  intro G hGF hGS x y hx hy φ ψ hφ hψ
  rw [eq_Grep_of_cover hX hbump hfT hsec hcov G hGF hGS]
  exact h ⟨x, hx⟩ ⟨y, hy⟩ _ _

end Gamma

/-- B's `←` half, in B's quantifier form. -/
def BMpr : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × (Fin n → ℝ) × X)]
    [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
    (Bd : StrongBundle PX P) (f : X → Y)
    (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hfT : Bd.IsScFredholmSectionTame f)
    (hsec : Bd.HasScPlusSectionsThrough),
    IsOrientableB f hfT.toIsScFredholmSection → IsOrientableSection hX hbump hfT hsec

/-- B with the covering hypothesis added. -/
def BCover : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × (Fin n → ℝ) × X)]
    [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
    (Bd : StrongBundle PX P) (f : X → Y)
    (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hfT : Bd.IsScFredholmSectionTame f)
    (hsec : Bd.HasScPlusSectionsThrough),
    ContractibleCover f hfT.toIsScFredholmSection →
      (IsOrientableSection hX hbump hfT hsec ↔ IsOrientableB f hfT.toIsScFredholmSection)

theorem B_mpr : BMpr := by
  intro X _ _ _ PX Y _ _ _ P _ _ _ _ _ _ Bd f hX hbump hfT hsec h
  exact isOrientableSection_of_isOrientableB hX hbump hfT hsec h

theorem B_of_cover : BCover := by
  intro X _ _ _ PX Y _ _ _ P _ _ _ _ _ _ Bd f hX hbump hfT hsec hcov
  exact ⟨isOrientableB_of_isOrientableSection hX hbump hfT hsec hcov,
    isOrientableSection_of_isOrientableB hX hbump hfT hsec⟩

/-- `B → A`, VACUOUS: A is proved outright (from `exists_apply_eq_of_isOrientableSection` and
`isOrientableSection_of_apply_eq`), without using B. -/
theorem B_to_A : B → A := by
  intro _ X _ _ _ PX Y _ _ _ P _ _ Bd f _ _ _ _ hX hbump hf hsec
  exact ⟨exists_apply_eq_of_isOrientableSection hX hbump hf hsec,
    fun ⟨o, ho⟩ => isOrientableSection_of_apply_eq hX hbump hf hsec o ho⟩

/-! `A → B` is not proved: A (the characterization by maps `y ↦ o_y`) says nothing about the text's
notion; B's `←` is proved above without A, B's `→` needs `ContractibleCover`. -/

#rt_check RoundTrip.V6_58.B_to_A [Polyfold.isOrientableSection_iff_exists]
#rt_check RoundTrip.V6_58.B_mpr [Polyfold.isOrientableSection_iff_exists]
#rt_check RoundTrip.V6_58.B_of_cover [Polyfold.isOrientableSection_iff_exists]
#rt_overlap RoundTrip.V6_58.B_to_A [Polyfold.isOrientableSection_iff_exists]

end RoundTrip.V6_58
