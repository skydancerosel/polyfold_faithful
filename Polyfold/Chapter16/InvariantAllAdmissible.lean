import Polyfold.Chapter15.AdmissibleCobordism
import Polyfold.Chapter16.InheritedPerturbationExists
import Polyfold.Chapter16.StokesUnconditional

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739:
**Theorem 16.6.6** (2017: Theorem 16.8), with Definition 16.6.5 (p. 739), Theorem 15.4.3 and
Corollary 15.4.4 (pp. 702–703), and Stokes from Remark 9.5.19 (p. 451).

# Theorem 16.6.6 over all admissible perturbations

## The text, paraphrased

(Theorem 16.6.6) Let `∂Z = ∅`, `f` be an oriented sc-Fredholm section of `p : Y → Z` with compact
solution set and index `k`, and `(n, U)` control compactness.  For an sc⁺-multisection `λ`
controlled by `(n, U)` with `(f, λ)` in general position, the branched integrals `∫_θ̂ τ`,
`∮_θ̂ τ` of a closed `k`-form `τ` over `θ̂ = λ ∘ f` with the orientation inherited from `f` are
well defined, do not depend on `λ`, and depend only on `[τ]`.

## What is formalized (namespace `Polyfold.StrongPolyfoldBundle`)

* `CanonicalBumpInput o k`: the standing hypotheses in the model of the orientation `o`:
  sc-smooth bump functions on the object M-polyfold, tame germ data of the representative `F`,
  index `k` at the smooth points.  `CanonicalInput.canonicalBumpInput`: they follow from
  `CanonicalInput o k` when `Z` admits sc-smooth partitions of unity and `∂Z = ∅`.
* `ModelSolutionSet.toSolution`, `integral_toCompact`, `integralEff_toCompact`: the polyfold
  integrals over the class of a model solution set are the ep-groupoid integrals in the model.
* `ModelSolutionSet.isTransversalPerturbation`: an admissible `λ` gives a transversal
  perturbation `(N, γπ⁻¹(U), Λ)` of the model with `N(Λ) ≤ 1` (Theorem 15.4.3's hypotheses).
* `theorem_16_6_6_solutionSet_of_bump`: every admissible `λ` has a compact tame `θ̂ = λ ∘ f` with
  the canonical orientation of `(f, o)`.
* **`theorem_16_6_6_integral_eq`**: for any two admissible perturbed solution sets with the
  canonical orientation of `(f, o)`, `∫_θ̂ τ` and `∮_θ̂ τ` agree for closed `τ`.  The
  perturbations are all those of the theorem: controlled by `(n, U)` (so `n(λ) ≤ 1`), in general
  position; structurability is not assumed.
* **`theorem_16_6_6_all_admissible`**: `theorem_16_6_6_statement` for the predicate
  "`θ̂` carries the canonical orientation of `(f, o)`" (`IsCanonicalSolutionSet`), with the
  standing hypotheses `CanonicalBumpInput o (m + 1)`.
* **`theorem_16_6_6_all_admissible_wellDefined`**: existence for every admissible `λ` together
  with the independence; `theorem_16_6_6_all_admissible_of_partitions`: the same from
  `CanonicalInput` and partitions of unity on `Z`.

## Reading

The orientation inherited from `f` is the canonical orientation of Definition 15.4.2 in the model
carrying `o` (as in `theorem_16_6_6_canonical`).  No partitions of unity are assumed; sc-smooth
bump functions in the model are used for Theorem 15.4.1 and for the cobordism of Corollary
15.3.10 (3), which is built here for sc⁺-multisections with `N(Λ) ≤ 1` that need not be
structurable (`SBLocalization.corollary_15_3_10_3_transversal`).  Compactness of the solution set
of `f` is not used beyond `(n, U)` controlling compactness.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace PolyfoldClass

open EpGroupoid

variable {Z : Type u} [TopologicalSpace Z] {c : PolyfoldClass Z} {m : ℕ}

/-- `∫_θ̂ dη = 0` and `∮_θ̂ dη = 0` on a representative when `∂Z = ∅`, with Stokes from Remark
9.5.19 (`theorem_16_4_6_all` and its companions). -/
private theorem OrientedRep.integral_d_eq_zero_aux (hbd : c.boundary = ∅) (a : OrientedRep c)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (m + 1))
    (η : ScForm c m) :
    a.integral (Nat.succ_pos m) hcpt hloc (ScForm.d η) = 0 ∧
      a.integralEff (Nat.succ_pos m) hcpt hloc (ScForm.d η) = 0 := by
  have hemp : ∀ x, x ∉ a.p.X.X.PObj.boundary ∩ EpGroupoid.supp a.A.Θ := fun x hx =>
    not_mem_boundary_of_eq_empty hbd a.p a.mem x hx.1
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · constructor
    · rw [OrientedRep.theorem_16_4_6_dim1_all a hcpt hloc η, OrientedRep.boundaryIntegralDim1]
      exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary hemp _
    · rw [OrientedRep.theorem_16_4_6_eff_dim1_all a hcpt hloc η,
        OrientedRep.boundaryIntegralEffDim1]
      exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary hemp _
  · constructor
    · rw [OrientedRep.theorem_16_4_6_all a hm hcpt hloc η, OrientedRep.boundaryIntegral]
      exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary hemp _
    · rw [OrientedRep.theorem_16_4_6_eff_all a hm hcpt hloc η, OrientedRep.boundaryIntegralEff]
      exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary hemp _

/-- **`∫_θ̂ τ` and `∮_θ̂ τ` depend only on `[τ]`** for `∂Z = ∅` (Theorem 16.6.6, 2021 p. 739),
with no partitions of unity on `Z`. -/
theorem CompactOrientedSuborbifold.integral_add_d_of_boundary_eq_empty (hbd : c.boundary = ∅)
    (P : CompactOrientedSuborbifold c m) (τ : ScForm c (m + 1)) (η : ScForm c m) :
    P.integral (τ + ScForm.d η) = P.integral τ ∧
      P.integralEff (τ + ScForm.d η) = P.integralEff τ := by
  constructor
  · change P.θ.integral _ _ _ _ = P.θ.integral _ _ _ _
    rw [OrientedSuborbifold.integral_add]
    have h : P.θ.integral (Nat.succ_pos m) P.isCompact P.isTame (ScForm.d η) = 0 :=
      (OrientedRep.integral_d_eq_zero_aux hbd _ _ _ η).1
    rw [h, add_zero]
  · change P.θ.integralEff _ _ _ _ = P.θ.integralEff _ _ _ _
    rw [OrientedSuborbifold.integralEff_add]
    have h : P.θ.integralEff (Nat.succ_pos m) P.isCompact P.isTame (ScForm.d η) = 0 :=
      (OrientedRep.integral_d_eq_zero_aux hbd _ _ _ η).2
    rw [h, add_zero]

end PolyfoldClass

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass SBLocalization SEP EpGroupoid

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-! ### The standing hypotheses -/

/-- **The standing hypotheses of Theorem 16.6.6 in the model of an orientation `o`**, Fredholm
index `k`, without partitions of unity: sc-smooth bump functions on the object M-polyfold of the
model, tame germ data of the representative `F`, and index `k` at every smooth point. -/
structure CanonicalBumpInput {s : FredholmSection c} (o : OrientationRep s) (k : ℕ) : Prop where
  bump : o.a.S.A.X.PObj.AdmitsBumpFunctions
  tame : o.a.S.A.B.IsScFredholmSectionTame o.a.F
  index : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x (k : ℤ)

/-- The standing hypotheses follow from `CanonicalInput` when `Z` admits sc-smooth partitions of
unity (Theorem 12.3.2 (1) gives the bump functions in the model). -/
theorem CanonicalInput.canonicalBumpInput (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    {s : FredholmSection c} {o : OrientationRep s} {k : ℕ} (H : CanonicalInput o k) :
    CanonicalBumpInput o k := by
  have hPUq := (c.polyfold.definition_16_1_5_two).1 hPU o.a.S.toPolyfoldStructure
    (toPolyfoldStructure_mem o.a.hS)
  exact ⟨o.a.S.A.X.theorem_12_3_2_1.1
    (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hPUq), H.tame, H.index⟩

/-! ### Model solution sets as oriented solution sets -/

namespace ModelSolutionSet

variable {a : SectionRep c} {m : ℕ} (M : ModelSolutionSet a m)

/-- The oriented solution set `(Λ, T̂)` of the model. -/
def toSolution : OrientedSolution a.S.A a.F m where
  Λ := M.Λ
  isScPlusMultisection := M.isScPlusMultisection
  T := M.T
  isBranched := M.isBranched
  isCompact := M.isCompact
  isOrientation := M.isOrientation
  loc := M.loc

/-- **`∫_θ̂ [(ω, (X, γ))] = ∫_{(Λ ∘ F, T̂)} ω`**: the polyfold integral over the class of a model
solution set is the ep-groupoid integral in the model (the cut-off of `T̂` outside `X_∞` does not
change it). -/
theorem integral_toCompact (ω : a.S.A.baseEP.epFormsInfty (m + 1)) :
    M.toCompact.integral (ScForm.mk a.S.toPolyfoldStructure (toPolyfoldStructure_mem a.hS) ω) =
      M.toSolution.integral ω :=
  (M.toCompact.integral_mk_rep M.orientedRep rfl ω).trans
    (a.S.A.baseEP.tameBranchedIntegral_congr_orientation (Nat.succ_pos m) M.isBranched
      M.isCompact M.isOrientation.smoothPart M.isOrientation (fun _ hy => smoothPart_of_mem hy) _
      M.loc ω)

/-- **`∮_θ̂ [(ω, (X, γ))] = ∮_{(Λ ∘ F, T̂)} ω`**; (ZHOU) gives the local unique continuation
property in the model (Proposition 7.4.10). -/
theorem integralEff_toCompact (ω : a.S.A.baseEP.epFormsInfty (m + 1)) :
    M.toCompact.integralEff
        (ScForm.mk a.S.toPolyfoldStructure (toPolyfoldStructure_mem a.hS) ω) =
      M.toSolution.integralEff (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou) ω :=
  (M.toCompact.integralEff_mk_rep M.orientedRep rfl ω).trans
    (a.S.A.baseEP.tameBranchedIntegralEff_congr_orientation (Nat.succ_pos m) M.isBranched
      M.isCompact M.isOrientation.smoothPart M.isOrientation (fun _ hy => smoothPart_of_mem hy) _
      _ ω)

end ModelSolutionSet

/-- **An admissible `λ` is a transversal perturbation of the model with `N(Λ) ≤ 1`** (Theorem
16.6.6's hypotheses on `λ` against Theorem 15.4.3's): if the class of a model solution set is
admissible (controlled by `(n, U)`, `(f, λ)` in general position), then `(N, γπ⁻¹(U), Λ)`, with
`N` the model form of `n`, is a transversal perturbation of `F`. -/
theorem ModelSolutionSet.isTransversalPerturbation {s : FredholmSection c} {n : Y → ℝ}
    (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U) (hcc : s.1.ControlsCompactness n U)
    {m : ℕ} {o : OrientationRep s} (M : ModelSolutionSet o.a m)
    (hadm : (M.toOrientedPerturbation o.ha).IsAdmissible n U) :
    IsTransversalPerturbation o.a.S.A o.a.F (o.a.S.normOf n) (o.a.g ⁻¹' U) M.Λ := by
  have hΛ := M.isScPlusMultisection
  have hcca := (o.a.controlsCompactness_iff hn hU).1 (by rw [o.ha]; exact hcc)
  set b := ofFunctor o.a.S o.a.hS M.Λ hΛ
  have ht : ScPlusMultisection.IsControlledBy (c := c) ⟦b⟧ n U := hadm.1
  have hgp := (ScSection.isInGeneralPositionWith_iff_of_rep s.1 s.2 _ o.a o.ha hΛ
    (toFun_of_mk_ofFunctor_eq rfl)).1 hadm.2
  have hN1 : ∀ x, pointwiseNorm (o.a.S.normOf n) M.Λ x ≤ 1 := by
    intro x
    rw [← normLam_eq o.a.hS n M.Λ b.lam x fun w _ => b.comm w]
    exact ht.1 _
  have hdom : domSupp M.Λ ⊆ o.a.g ⁻¹' U := by
    intro x hx
    apply ht.2
    rw [← remark_16_5_3 b]
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨hcca, hΛ, hdom, hN1, IsInGeneralPosition.isTransversal o.hF hΛ hgp⟩

/-! ### Existence -/

/-- **2021 Theorem 16.6.6, p. 739: every admissible `λ` gives a canonically oriented `θ̂`**, with
bump functions in the model in place of partitions of unity on `Z`: for every sc⁺-multisection
`t` controlled by `(n, U)` with `(f, t)` in general position, `θ̂ = t ∘ f` is a compact tame
oriented branched suborbifold of dimension `m + 1` carrying the canonical orientation of
`(f, o)`. -/
theorem theorem_16_6_6_solutionSet_of_bump (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {m : ℕ} {o : OrientationRep s}
    (H : CanonicalBumpInput o (m + 1)) (t : ScPlusMultisection c)
    (ht : t.IsControlledBy n U) (hgp : s.1.IsInGeneralPositionWith t) :
    ∃ Q : OrientedPerturbation s.1 m, Q.t = t ∧ Q.IsAdmissible n U ∧
      IsCanonicalSolutionSet o Q := by
  obtain ⟨Λ, hΛ, hl⟩ := exists_functor_rep t o.a.hS
  have ht' : (⟦ofFunctor o.a.S o.a.hS Λ hΛ⟧ : ScPlusMultisection c) = t :=
    mk_ofFunctor_eq t o.a.hS hΛ hl
  have hgpΛ := (ScSection.isInGeneralPositionWith_iff_of_rep s.1 s.2 t o.a o.ha hΛ hl).1 hgp
  rw [← ht'] at ht
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hX : o.a.S.A.X.IsTame := o.a.S.A.X.isTame_of_degIndex_eq_zero hd
  have ho := o.isSectionOrientation hX H.bump H.tame
  have hcca := (o.a.controlsCompactness_iff hn hU).1 (by rw [o.ha]; exact hcc)
  set b := ofFunctor o.a.S o.a.hS Λ hΛ
  have hN1 : ∀ x, pointwiseNorm (o.a.S.normOf n) Λ x ≤ 1 := by
    intro x
    rw [← normLam_eq o.a.hS n Λ b.lam x fun w _ => b.comm w]
    exact ht.1 _
  have hdom : domSupp Λ ⊆ o.a.g ⁻¹' U := by
    intro x hx
    apply ht.2
    rw [← remark_16_5_3 b]
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have htr := IsInGeneralPosition.isTransversal o.hF hΛ hgpΛ
  have hgood : ∀ x, 0 < Λ (o.a.F x) → SBLocalization.IsGoodPositionAt o.a.F Λ x :=
    fun x hpos => isGoodPositionAt_of_isInGeneralPosition o.hF H.tame hΛ hgpΛ hpos
  obtain ⟨hbr, hcpt⟩ := theorem_15_4_3_isBranched_hyp o.hF H.tame hcca hΛ hdom hN1 htr
    fun x _ => hgood x
  have hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (o.a.F z) : ℚ)),
      o.a.S.A.B.IsIndexAt o.a.F x (m + 1 : ℕ) := fun x hx =>
    H.index x (mem_smoothSet_of_pos H.tame hΛ (by exact_mod_cast hx))
  have hcan := theorem_15_4_1 hX H.bump o.hF H.tame hΛ o.hsec o.o o.isOrientation.2 ho
    (fun x hx => hgood x (by exact_mod_cast hx)) hidx
  let M : ModelSolutionSet o.a m :=
    ⟨Λ, hΛ, canonicalOrientation Λ o.hF.2 o.hsec o.o, hbr, hcpt, hcan.1, hcan.loc⟩
  exact ⟨M.toOrientedPerturbation o.ha, ht', ⟨ht, o.a, Λ, hΛ, o.ha, rfl, hgpΛ⟩, M, hcan, rfl⟩

/-! ### Independence of the perturbation -/

set_option maxHeartbeats 800000 in
-- the cylinder of the model is unfolded in the hypotheses of the ep-groupoid statement
/-- **2021 Theorem 16.6.6, p. 739 (2017: Theorem 16.8): the integrals do not depend on the
admissible perturbation.**  Let `∂Z = ∅`, `(n, U)` control the compactness of `f`, and `o` be an
orientation of `f` (Definition 16.6.5) whose model has sc-smooth bump functions, tame germ data
and Fredholm index `m + 1`.  Let `θ̂₀ = λ₀ ∘ f` and `θ̂₁ = λ₁ ∘ f` be perturbed solution sets of
admissible `λ₀`, `λ₁` (controlled by `(n, U)`, in general position; neither structurability nor
`n(λ) < 1` is asked), with the canonical orientation of `(f, o)`.  Then `∫_{θ̂₀} τ = ∫_{θ̂₁} τ`
and `∮_{θ̂₀} τ = ∮_{θ̂₁} τ` for every closed `τ`.  No partitions of unity are assumed. -/
theorem theorem_16_6_6_integral_eq (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c}
    {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {m : ℕ} {o : OrientationRep s}
    (H : CanonicalBumpInput o (m + 1)) {Q₀ Q₁ : OrientedPerturbation s.1 m}
    (a₀ : Q₀.IsAdmissible n U) (c₀ : IsCanonicalSolutionSet o Q₀)
    (a₁ : Q₁.IsAdmissible n U) (c₁ : IsCanonicalSolutionSet o Q₁)
    (τ : ScForm c.polyfold (m + 1)) (hτ : ScForm.d τ = 0) :
    Q₀.integral τ = Q₁.integral τ ∧ Q₀.integralEff τ = Q₁.integralEff τ := by
  obtain ⟨M₀, hT₀, rfl⟩ := c₀
  obtain ⟨M₁, hT₁, rfl⟩ := c₁
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hpara := o.a.S.paracompact
  have hX : o.a.S.A.X.IsTame := o.a.S.A.X.isTame_of_degIndex_eq_zero hd
  have hbump : o.a.S.A.X.AdmitsBumpFunctionsPointwise := o.a.S.A.X.theorem_12_3_2_1.2 H.bump
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) o.a.S.A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) o.a.S.A.X.PMor
  have hbumpC : (o.a.S.A.cubeSEP 1).X.PObj.AdmitsBumpFunctions :=
    admitsBumpFunctions_prod_cube H.bump
  have hsec' : (o.a.S.A.cubeSEP 1).B.HasScPlusSectionsThrough :=
    MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbumpC
  have ho := o.isSectionOrientation hX H.bump H.tame
  have hinvC := isOrInvariant_cubeOrientation o.hF H.tame o.hsec hsec' o.o o.isOrientation.2
  have hLUC := o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou
  have hLUCC : (o.a.S.A.cubeSEP 1).X.IsLUC := isLUC_cubeSEP hLUC
  have hr₀ := M₀.isTransversalPerturbation hn hU hcc a₀
  have hr₁ := M₁.isTransversalPerturbation hn hU hcc a₁
  have hq := toPolyfoldStructure_mem o.a.hS
  have hω : o.a.S.A.baseEP.epFormsInftyD (m + 1)
      (ScForm.toStructure o.a.S.toPolyfoldStructure hq τ) = 0 := by
    have h : o.a.S.toPolyfoldStructure.X.epFormsInftyD (m + 1)
        (ScForm.toStructure o.a.S.toPolyfoldStructure hq τ) = 0 := by
      rw [← ScForm.toStructure_dFun, ← ScForm.d_apply, hτ, ScForm.toStructure_zero]
    exact h
  have e := integral_eq_of_isTransversalPerturbation hd o.hF H.tame o.hsec hsec' o.o ho hinvC
    H.index hpara hbump (S₀ := M₀.toSolution) (S₁ := M₁.toSolution) hr₀ hr₁ hT₀ hT₁ _ hω
  have eE := integralEff_eq_of_isTransversalPerturbation hd o.hF H.tame o.hsec hsec' o.o ho
    hinvC H.index hpara hbump hLUC hLUCC (S₀ := M₀.toSolution) (S₁ := M₁.toSolution) hr₀ hr₁
    hT₀ hT₁ _ hω
  have i₀ := M₀.integral_toCompact (ScForm.toStructure o.a.S.toPolyfoldStructure hq τ)
  have i₁ := M₁.integral_toCompact (ScForm.toStructure o.a.S.toPolyfoldStructure hq τ)
  have j₀ := M₀.integralEff_toCompact (ScForm.toStructure o.a.S.toPolyfoldStructure hq τ)
  have j₁ := M₁.integralEff_toCompact (ScForm.toStructure o.a.S.toPolyfoldStructure hq τ)
  rw [ScForm.mk_toStructure] at i₀ i₁ j₀ j₁
  exact ⟨i₀.trans (e.trans i₁.symm), j₀.trans (eE.trans j₁.symm)⟩

/-- **2021 Theorem 16.6.6, p. 739 (2017: Theorem 16.8), over all admissible perturbations.**
For `∂Z = ∅`, `f` with `(n, U)` controlling compactness and every orientation `o` of `f` whose
model has sc-smooth bump functions, tame germ data and Fredholm index `m + 1`: over the admissible
perturbed solution sets `θ̂ = λ ∘ f` (`λ` controlled by `(n, U)`, `(f, λ)` in general position)
with the canonical orientation of `(f, o)` (Definition 15.4.2 in the model of `o`), `∫_θ̂ τ` and
`∮_θ̂ τ` depend only on `[τ]`, and a closed `τ` has the same `∫_θ̂ τ` and `∮_θ̂ τ` for any two of
them.  No partitions of unity are assumed. -/
theorem theorem_16_6_6_all_admissible (s : FredholmSection c) (n : Y → ℝ) (U : Set Z) (m : ℕ) :
    theorem_16_6_6_statement s n U m
      (fun o Q => CanonicalBumpInput o (m + 1) ∧ IsCanonicalSolutionSet o Q) := by
  intro hbd _ hn hU hcc o
  refine ⟨fun P _ _ τ η =>
    P.toCompactOrientedSuborbifold.integral_add_d_of_boundary_eq_empty hbd τ η, ?_⟩
  rintro P₀ P₁ a₀ ⟨H, c₀⟩ a₁ ⟨-, c₁⟩ τ hτ
  exact theorem_16_6_6_integral_eq hbd hn hU hcc H a₀ c₀ a₁ c₁ τ hτ

/-- **2021 Theorem 16.6.6, p. 739, existence and independence over all admissible `λ`.**  Under
the hypotheses of `theorem_16_6_6_all_admissible`: (1) every sc⁺-multisection `λ` controlled by
`(n, U)` with `(f, λ)` in general position has a perturbed solution set `θ̂ = λ ∘ f`, compact,
tame and oriented of dimension `m + 1`, with the canonical orientation of `(f, o)`; (2) for any two
such `θ̂`, of the same or of different `λ`, the integrals `∫_θ̂ τ` and `∮_θ̂ τ` of a closed `τ`
agree; (3) they depend only on `[τ]`. -/
theorem theorem_16_6_6_all_admissible_wellDefined (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {m : ℕ} {o : OrientationRep s}
    (H : CanonicalBumpInput o (m + 1)) :
    (∀ t : ScPlusMultisection c, t.IsControlledBy n U → s.1.IsInGeneralPositionWith t →
      ∃ Q : OrientedPerturbation s.1 m, Q.t = t ∧ Q.IsAdmissible n U ∧
        IsCanonicalSolutionSet o Q) ∧
    (∀ Q₀ Q₁ : OrientedPerturbation s.1 m, Q₀.IsAdmissible n U → IsCanonicalSolutionSet o Q₀ →
      Q₁.IsAdmissible n U → IsCanonicalSolutionSet o Q₁ →
      ∀ τ : ScForm c.polyfold (m + 1), ScForm.d τ = 0 →
        Q₀.integral τ = Q₁.integral τ ∧ Q₀.integralEff τ = Q₁.integralEff τ) ∧
    ∀ Q : OrientedPerturbation s.1 m, ∀ (τ : ScForm c.polyfold (m + 1))
      (η : ScForm c.polyfold m),
      Q.integral (τ + ScForm.d η) = Q.integral τ ∧
        Q.integralEff (τ + ScForm.d η) = Q.integralEff τ :=
  ⟨fun t ht hgp => theorem_16_6_6_solutionSet_of_bump hbd hn hU hcc H t ht hgp,
    fun _ _ a₀ c₀ a₁ c₁ τ hτ => theorem_16_6_6_integral_eq hbd hn hU hcc H a₀ c₀ a₁ c₁ τ hτ,
    fun Q τ η => Q.toCompactOrientedSuborbifold.integral_add_d_of_boundary_eq_empty hbd τ η⟩

/-- **2021 Theorem 16.6.6, p. 739, over all admissible `λ`, from the hypotheses of
`theorem_16_6_6_canonical`**: if `Z` admits sc-smooth partitions of unity and the model of `o` has
the standing hypotheses `CanonicalInput o (m + 1)`, the conclusions of
`theorem_16_6_6_all_admissible_wellDefined` hold. -/
theorem theorem_16_6_6_all_admissible_of_partitions
    (hPU : c.polyfold.AdmitsScPartitionsOfUnity) (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {m : ℕ} {o : OrientationRep s}
    (H : CanonicalInput o (m + 1)) :
    (∀ t : ScPlusMultisection c, t.IsControlledBy n U → s.1.IsInGeneralPositionWith t →
      ∃ Q : OrientedPerturbation s.1 m, Q.t = t ∧ Q.IsAdmissible n U ∧
        IsCanonicalSolutionSet o Q) ∧
    (∀ Q₀ Q₁ : OrientedPerturbation s.1 m, Q₀.IsAdmissible n U → IsCanonicalSolutionSet o Q₀ →
      Q₁.IsAdmissible n U → IsCanonicalSolutionSet o Q₁ →
      ∀ τ : ScForm c.polyfold (m + 1), ScForm.d τ = 0 →
        Q₀.integral τ = Q₁.integral τ ∧ Q₀.integralEff τ = Q₁.integralEff τ) ∧
    ∀ Q : OrientedPerturbation s.1 m, ∀ (τ : ScForm c.polyfold (m + 1))
      (η : ScForm c.polyfold m),
      Q.integral (τ + ScForm.d η) = Q.integral τ ∧
        Q.integralEff (τ + ScForm.d η) = Q.integralEff τ :=
  theorem_16_6_6_all_admissible_wellDefined hbd hn hU hcc (H.canonicalBumpInput hPU)

end StrongPolyfoldBundle

end Polyfold
