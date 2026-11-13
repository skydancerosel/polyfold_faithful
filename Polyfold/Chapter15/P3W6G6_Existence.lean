import Polyfold.Chapter15.P3W6G6_GeneralPosition

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3,
**Theorem 15.3.7** (General Position; 2017: Theorem 15.4), pp. 693–698, and
**Remark 15.3.8**, p. 694.

# Theorem 15.3.7 without a good system

## The text, paraphrased

Theorem 15.3.7 gives an sc⁺-multisection functor `Λ` with (1)–(4); "also" `Λ` can be taken
structurable.  Remark 15.3.8: the theorem does not assume that `|X|` is paracompact (only that
an auxiliary norm exists).

## What is formalized (namespace `Polyfold.SBLocalization`)

"Structurable" (Definition 13.3.6) asks for a good system, which the text obtains for paracompact
`|X|` (Theorem 13.1.8).  GP's assembly (`GPFamily`) keeps structurability along; here the same
assembly is carried out for sc⁺-multisections only, so that no good system is needed:

* `ScPlusGPFamily`: GP's `GPFamily` with "sc⁺-multisection" in place of "structurable";
  `GPFamily.toScPlus`, `.mono`, `.zero`, `.add` (Definition 13.2.9: sums of sc⁺-multisections),
  `.saturate`; `exists_scPlusGPFamily_of_compact` (the finite cover of `|S_f|`).
* `SeedData.scPlusGPFamily`: GA's local family without the good system.
* **`theorem_15_3_7_existence`**: Theorem 15.3.7, (1)–(4), under exactly the hypotheses of the
  text (with the inherited tame germ data of §15.2, as in `theorem_15_3_7_statement`): `X` tame
  with sc-smooth bump functions, `f` an sc-Fredholm section functor with compact `|S_f|`,
  `(N, U)` controlling compactness, `h : X → (0, 1]` a continuous functor.  No good system and
  no paracompactness of `|X|` (Remark 15.3.8).
* **`theorem_15_3_7`**: the theorem with its addendum: (1)–(4) always, and a structurable `Λ`
  with (1)–(4) whenever a good system exists (`theorem_15_3_7_of_goodSystem`), in particular
  for paracompact `|X|`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold

variable {A : SEP.{u}}

variable (A) in
/-- **The local families of the proof of Theorem 15.3.7, without structurability**: GP's
`GPFamily` with "sc⁺-multisection" in place of "structurable". -/
structure ScPlusGPFamily (f : A.Obj → A.W) (N : A.B.One → ℝ) (U : Set A.Obj) (h : A.Obj → ℝ)
    (Q : Set A.Obj) where
  /-- The number of parameters. -/
  ℓ : ℕ
  /-- The family. -/
  Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0
  isScPlus : ∀ t, IsScPlusMultisection A (Λ t)
  isLinear : IsLinearFamily Λ
  norm_le : ∀ t x, pointwiseNorm N (Λ t) x ≤ (∑ j, |t j|) * h x
  domSupp_subset : ∀ t, domSupp (Λ t) ⊆ U
  paramOnto : ∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ Q →
    A.X.PObj.levelVal 1 x ∈ solutionSet A.P f → IsParamOntoAt f Λ x

variable {f : A.Obj → A.W} {N : A.B.One → ℝ} {U : Set A.Obj} {h : A.Obj → ℝ}

namespace ScPlusGPFamily

/-- A family on `Q` is a family on every `Q' ⊆ Q`. -/
def mono {Q Q' : Set A.Obj} (F : ScPlusGPFamily A f N U h Q) (hQ : Q' ⊆ Q) :
    ScPlusGPFamily A f N U h Q' where
  ℓ := F.ℓ
  Λ := F.Λ
  isScPlus := F.isScPlus
  isLinear := F.isLinear
  norm_le := F.norm_le
  domSupp_subset := F.domSupp_subset
  paramOnto x hx := F.paramOnto x (hQ hx)

/-- The empty family on `∅` (the trivial multisection, no parameters). -/
def zero (hN : A.B.IsAuxNorm N) (hU : ∅ ⊆ U) : ScPlusGPFamily A f N U h ∅ where
  ℓ := 0
  Λ _ := zeroMultisection A
  isScPlus _ := isScPlusMultisection_zeroMultisection A
  isLinear x₀ := ⟨univ, 1, fun _ j => j.elim0, fun _ => 1, isOpen_univ, mem_univ _,
    fun _ j => j.elim0, fun t => by
      simp only [paramSec_fin_zero]
      exact isLocalRepOn_zeroMultisection isOpen_univ⟩
  norm_le t x := by rw [pointwiseNorm_zeroMultisection hN]; simp
  domSupp_subset _ := by rw [domSupp_zeroMultisection]; exact hU
  paramOnto _ hx := hx.elim

/-- **The sum of two families** (`Λ_t ⊕ Λ'_{t'}`, Definition 13.2.9) is a family on `Q ∪ Q'`. -/
def add (hN : A.B.IsAuxNorm N) {Q Q' : Set A.Obj} (F : ScPlusGPFamily A f N U h Q)
    (F' : ScPlusGPFamily A f N U h Q') : ScPlusGPFamily A f N U h (Q ∪ Q') where
  ℓ := F.ℓ + F'.ℓ
  Λ := famAdd F.Λ F'.Λ
  isScPlus t := definition_13_2_9 (F.isScPlus _) (F'.isScPlus _)
  isLinear := IsLinearFamily.famAdd F.isLinear F'.isLinear
  norm_le t x := by
    refine (pointwiseNorm_multisectionAdd_le hN (F.isScPlus _) (F'.isScPlus _) x).trans ?_
    refine (add_le_add (F.norm_le _ x) (F'.norm_le _ x)).trans_eq ?_
    rw [← add_mul, Fin.sum_univ_add]
    rfl
  domSupp_subset t := (domSupp_multisectionAdd_subset _ _).trans
    (union_subset (F.domSupp_subset _) (F'.domSupp_subset _))
  paramOnto x hx hS := by
    rcases hx with hx | hx
    · exact (F.paramOnto x hx hS).famAdd_left F'.isLinear
    · exact IsParamOntoAt.famAdd_right F.isLinear (F'.paramOnto x hx hS)

/-- **A family on `V` is a family on the saturation of `V`** (the text's "by equivariance"). -/
def saturate (hf : A.E.IsScFredholmSectionFunctor f) {V : Set A.Obj}
    (F : ScPlusGPFamily A f N U h V) : ScPlusGPFamily A f N U h (A.X.saturation V) where
  ℓ := F.ℓ
  Λ := F.Λ
  isScPlus := F.isScPlus
  isLinear := F.isLinear
  norm_le := F.norm_le
  domSupp_subset := F.domSupp_subset
  paramOnto z hz hzS := by
    obtain ⟨a, haV, ha⟩ := hz
    obtain ⟨φ, hφs, hφt⟩ := A.X.π_eq_π_iff.1 ha
    have h1 := src_mem_levelSet_one (z := z) hφt.symm
    have haS : A.X.src φ ∈ solutionSet A.P f := by
      have := mem_solutionSet_tgt hf (A.X.inv φ) (by rw [A.X.src_inv, hφt]; exact hzS)
      rwa [A.X.tgt_inv] at this
    have H := F.paramOnto (A.X.PObj.levelMk 1 (A.X.src φ) h1)
      (by rw [A.X.PObj.levelVal_levelMk, hφs]; exact haV)
      (by rw [A.X.PObj.levelVal_levelMk]; exact haS)
    exact H.of_mor hf (fun t => (F.isScPlus t).1) φ (A.X.PObj.levelVal_levelMk _ _ _)
      hφt.symm

end ScPlusGPFamily

/-- Finite sums of families. -/
theorem nonempty_scPlusGPFamily_biUnion (hN : A.B.IsAuxNorm N) {ι : Type*} (Q : ι → Set A.Obj)
    (F : ∀ i, Nonempty (ScPlusGPFamily A f N U h (Q i))) (s : Finset ι) :
    Nonempty (ScPlusGPFamily A f N U h (⋃ i ∈ s, Q i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨(ScPlusGPFamily.zero hN (empty_subset U)).mono (by simp)⟩
  | insert a s _ ih =>
    obtain ⟨G⟩ := ih
    obtain ⟨Fa⟩ := F a
    exact ⟨(Fa.add hN G).mono (Finset.set_biUnion_insert a s Q).le⟩

/-- **"From local to global" (p. 696)** for families of sc⁺-multisections: if `|S_f|` is compact
and every `x ∈ S_f` has an open neighbourhood carrying a family, one family covers `S_f`. -/
theorem exists_scPlusGPFamily_of_compact (hf : A.E.IsScFredholmSectionFunctor f)
    (hN : A.B.IsAuxNorm N) (hS : A.E.HasCompactSolutionSetEp f)
    (hloc : ∀ x ∈ solutionSet A.P f, ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧
      Nonempty (ScPlusGPFamily A f N U h V)) :
    ∃ Q : Set A.Obj, solutionSet A.P f ⊆ Q ∧ Nonempty (ScPlusGPFamily A f N U h Q) := by
  classical
  choose Vx hVo hxV hF using hloc
  set Qx : ∀ x ∈ solutionSet A.P f, Set A.Obj := fun x hx => A.X.saturation (Vx x hx)
  have hQo : ∀ x hx, IsOpen (Qx x hx) := fun x hx =>
    EpGroupoid.isOpen_saturation_of_isOpen A.X (hVo x hx)
  have hQs : ∀ x hx, A.X.IsSaturated (Qx x hx) := fun x hx =>
    EpGroupoid.isSaturated_saturation A.X (Vx x hx)
  have hcov : A.X.π '' solutionSet A.P f ⊆ ⋃ i : solutionSet A.P f, A.X.π '' Qx i.1 i.2 := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_iUnion.2 ⟨⟨x, hx⟩, x, A.X.subset_saturation _ (hxV x hx), rfl⟩
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover (fun i : solutionSet A.P f => A.X.π '' Qx i.1 i.2)
    (fun i => A.X.proposition_7_1_8 _ (hQo i.1 i.2)) hcov
  refine ⟨⋃ i ∈ s, Qx i.1 i.2, fun y hy => ?_,
    nonempty_scPlusGPFamily_biUnion hN (fun i : solutionSet A.P f => Qx i.1 i.2)
      (fun i => ⟨(hF i.1 i.2).some.saturate hf⟩) s⟩
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (hs ⟨y, hy, rfl⟩)
  have hy' : y ∈ A.X.π ⁻¹' (A.X.π '' Qx i.1 i.2) := hyi
  rw [hQs i.1 i.2] at hy'
  exact mem_iUnion₂.2 ⟨i, hi, hy'⟩

/-- **GA's local family without the good system** (the family `Λ^x_t` of the seeds on `Q₀`). -/
def SeedData.scPlusGPFamily (S : SeedData A) (hf : A.E.IsScFredholmSectionFunctor f)
    (hN : A.E.IsAuxNorm N) {c : ℝ} (hc : 0 ≤ c) (hsN : ∀ j y, normW N (S.s j y) ≤ c)
    (hch : ∀ y ∈ A.X.saturation S.R.U, c ≤ h y) (hh0 : ∀ y, 0 ≤ h y)
    (hUsat : A.X.saturation S.R.U ⊆ U) {W : Set A.Obj}
    (hW : ∀ y : A.X.PObj.Level 1, A.X.PObj.levelVal 1 y ∈ W →
      A.X.PObj.levelVal 1 y ∈ solutionSet A.P f →
        IsParamOntoVec f y (fun j => ⟨S.s j (A.X.PObj.levelVal 1 y), (S.isScPlusSection j).1 _⟩)) :
    ScPlusGPFamily A f N U h (⋂ g, S.R.U ∩ S.R.Φ g ⁻¹' W) where
  ℓ := S.ℓ
  Λ := S.Λ
  isScPlus := S.isScPlusMultisection_Λ
  isLinear := S.isLinearFamily
  norm_le := S.norm_le hN hc hsN hch hh0
  domSupp_subset t := (S.domSupp_Λ_subset t).trans hUsat
  paramOnto := S.isParamOntoAt hf hW

/-- **The local constructions of the proof, without the good system**: every `x ∈ S_f` has an
open neighbourhood carrying a family of sc⁺-multisections, from GA's seeds. -/
theorem exists_scPlusGPFamily_nhds (hf : A.E.IsScFredholmSectionFunctor f)
    (hcc : ControlsCompactness A f N U) (hhc : Continuous h)
    (hhφ : ∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) (hh : ∀ x, 0 < h x)
    (H : HasLocalParamSeeds A f N) :
    ∀ x ∈ solutionSet A.P f, ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧
      Nonempty (ScPlusGPFamily A f N U h V) := by
  intro x hx
  have hc : 0 < h x / 2 := half_pos (hh x)
  set W₁ : Set A.Obj := U ∩ {y | h x / 2 < h y}
  have hW₁ : IsOpen W₁ := hcc.2.1.inter (isOpen_lt continuous_const hhc)
  have hxW₁ : x ∈ W₁ := ⟨hcc.2.2.2.1 hx, half_lt_self (hh x)⟩
  obtain ⟨R, V, hprop, hRU, hVo, hxV, hVinv, hVcl⟩ := exists_atomicNbhd x hW₁ hxW₁
  obtain ⟨ℓ, s, hs, hsV, hsN, W, hWo, hxW, hW⟩ := H x hx V hVo hxV (h x / 2) hc
  let S : SeedData A := ⟨x, R, hprop, V, hVo, hxV, hVinv, hVcl, ℓ, s, hs, hsV⟩
  have hch : ∀ y ∈ A.X.saturation S.R.U, h x / 2 ≤ h y := by
    rintro y ⟨a, haU, hay⟩
    rw [← EpGroupoid.eq_of_π_eq (X := A.X) hhφ hay]
    exact (hRU haU).2.le
  have hUsat : A.X.saturation S.R.U ⊆ U :=
    EpGroupoid.saturation_subset_of_isSaturated (X := A.X) hcc.2.2.1 (hRU.trans inter_subset_left)
  exact ⟨⋂ g, S.R.U ∩ S.R.Φ g ⁻¹' W, isOpen_iInter_of_finite fun g =>
    (S.R.continuousOn_Φ g).isOpen_inter_preimage S.R.isOpen_U hWo,
    mem_iInter.2 fun g => ⟨S.R.mem_U, by rw [mem_preimage, S.R.Φ_self]; exact hxW⟩,
    ⟨S.scPlusGPFamily hf hcc.1 hc.le hsN hch (fun y => (hh y).le) hUsat hW⟩⟩

variable (A) in
/-- **Theorem 15.3.7, (1)–(4)**, as a proposition: G's `theorem_15_3_7_statement` with
"sc⁺-multisection functor" in place of "structurable sc⁺-multisection functor". -/
def theorem_15_3_7_existence_statement : Prop :=
  A.X.IsTame → A.X.AdmitsBumpFunctionsPointwise →
    ∀ f : A.Obj → A.W, A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
      A.E.HasCompactSolutionSetEp f →
      ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
      ∀ h : A.Obj → ℝ, Continuous h → (∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) →
        (∀ x, 0 < h x ∧ h x ≤ 1) →
        ∃ Λ : A.W → ℚ≥0, IsScPlusMultisection A Λ ∧ (∀ x, pointwiseNorm N Λ x < h x) ∧
          domSupp Λ ⊆ U ∧ IsTransversal f Λ ∧ IsInGeneralPosition A f Λ

/-- **Theorem 15.3.7 (General Position; 2017: Theorem 15.4), pp. 693–698, (1)–(4)**, with the
hypotheses of the text only (and the tame germ data inherited from §15.2, as in
`theorem_15_3_7_statement`): `X` tame with sc-smooth bump functions, `f` an sc-Fredholm section
functor with compact `|S_f|`, `(N, U)` controlling compactness, `h : X → (0, 1]` a continuous
functor.  There is an sc⁺-multisection functor `Λ` with (1) `N(Λ) < h`, (2)
`dom-supp(Λ) ⊆ U`, (3) `(f, Λ)` transversal, (4) `(f, Λ)` in general position.  No good system
and no paracompactness of `|X|` is used (Remark 15.3.8). -/
theorem theorem_15_3_7_existence : theorem_15_3_7_existence_statement A := by
  intro htame hbump f hf hft hS N U hcc h hhc hhφ hh
  have hN : A.B.IsAuxNorm N := hcc.1.isAuxNorm
  have hseed : HasLocalParamSeeds A f N :=
    hasLocalParamSeeds_of hbump hN (fun y hy => mem_smoothSet_of_eq hft isOpen_univ
      (isScPlusSectionOn_fiberZero isOpen_univ) (mem_univ y) hy)
      (hasPointwiseParamOnto hbump hf hft hN) (hasParamOntoOpen htame hf hft)
  obtain ⟨Q, hSQ, ⟨F⟩⟩ := exists_scPlusGPFamily_of_compact hf hN hS
    (exists_scPlusGPFamily_nhds hf hcc hhc hhφ (fun x => (hh x).1) hseed)
  obtain ⟨ε, hε, hae⟩ := hasParametricGeneralPosition htame hf hft hS hcc F.ℓ F.Λ F.isScPlus
    F.isLinear (fun t x => (F.norm_le t x).trans (mul_le_of_le_one_right
      (Finset.sum_nonneg fun j _ => abs_nonneg _) (hh x).2))
    F.domSupp_subset (fun x hx => F.paramOnto x (hSQ hx) hx)
  have hr : (0 : ℝ) < min ε (1 / (F.ℓ + 1)) := lt_min hε (by positivity)
  obtain ⟨t, ht, hgp⟩ := exists_norm_lt_of_ae hr (min_le_left _ _) hae
  have hsum : ∑ j, |t j| < 1 := sum_abs_lt_one (ht.trans_le (min_le_right _ _))
  refine ⟨F.Λ t, F.isScPlus t, fun x => ?_, F.domSupp_subset t,
    isTransversal_of_isInGeneralPosition hf (F.isScPlus t) hgp, hgp⟩
  exact (F.norm_le t x).trans_lt (mul_lt_of_lt_one_left (hh x).1 hsum)

/-- **Theorem 15.3.7 with its addendum**: (1)–(4) under the hypotheses of the text
(`theorem_15_3_7_existence`), and, when a good system exists (Definition 13.3.6 asks for one;
Theorem 13.1.8 gives one for paracompact `|X|`), a structurable `Λ` with (1)–(4)
(`theorem_15_3_7_of_goodSystem`). -/
theorem theorem_15_3_7 :
    theorem_15_3_7_existence_statement A ∧
      (Nonempty A.X.GoodSystem → theorem_15_3_7_statement A) :=
  ⟨theorem_15_3_7_existence, theorem_15_3_7_of_goodSystem⟩

end SBLocalization

end Polyfold
