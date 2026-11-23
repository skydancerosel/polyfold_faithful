import Polyfold.Chapter15.RelativeStepBump

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, the proof of
**Theorem 15.3.9** (Transversal Extension Theorem, p. 698; 2017: Theorem 15.5), steps (c)–(d),
pp. 698–699, for boundary data that are sc⁺ but not assumed structurable, and with `N(Λ₀) ≤ h`.

# The relative step for sc⁺ data with `N(Λ₀) ≤ h`

## The text, paraphrased

Steps (c)–(d): `(f, Λ₀)` is in general position near `supp(Λ₀ ∘ f) ∩ ∂X`; away from `∂X` one
argues as in Theorem 15.3.7 with parameter families supported off `∂X` and takes
`Λ̃ = Λ_t ⊕ Λ₀` for a small regular `t`.

## What is formalized (namespace `Polyfold.SBLocalization`)

The argument uses of `Λ₀` only that it is an sc⁺-multisection, and of the bound `N(Λ₀) < h` only
its strict form off `∂X` (where the families live).

* `exists_relGPFamily_of_seeds_of_le`: the relative local families at the points of
  `supp(Λ₀ ∘ f) ∖ ∂X`, for `N(Λ₀) ≤ h` on `X` and `N(Λ₀) < h` off `∂X`.
* **`theorem_15_3_7_relative_of_le`**: for tame `X` with sc-smooth bump functions and a good
  system, `f` sc-Fredholm with tame germ data, `(N, U)` controlling compactness, a continuous
  functor `h ≤ 1` and an sc⁺-multisection `Λ₀` with dom-supp in `U`, `N(Λ₀) ≤ h`, `N(Λ₀) < h` off
  `∂X`, and `(f, Λ₀)` in general position at the points of `supp(Λ₀ ∘ f) ∩ ∂X`: there is an
  sc⁺-multisection `Λ'` equal to `Λ₀` over `∂X` with dom-supp in `U`, `N(Λ') ≤ h`, `(f, Λ')`
  transversal and in general position.

## Reading

`theorem_15_3_7_relative_of_bump` is the case of a structurable `Λ₀` with `N(Λ₀) < h` everywhere,
whose conclusion is structurable with `N(Λ') < h`.  Here `Λ'` is `Λ₀ ⊕ Λ_t` with `Λ_t`
structurable; `Λ'` is structurable when `Λ₀` is.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}} {f : A.Obj → A.W} {Λ₀ : A.W → ℚ≥0} {N : A.B.One → ℝ} {U : Set A.Obj}

/-- **The relative local families at the points of `supp(Λ₀ ∘ f) ∖ ∂X` for `N(Λ₀) ≤ h`** (steps
(c)–(d) of the proof of Theorem 15.3.9, 2021 pp. 698–699): as `exists_relGPFamily_of_seeds`, with
`N(Λ₀) ≤ h ≤ 1` on `X` and `N(Λ₀) < h` off `∂X`. -/
theorem exists_relGPFamily_of_seeds_of_le (h𝒰 : Nonempty A.X.GoodSystem)
    (hf : A.E.IsScFredholmSectionFunctor f) (hcc : ControlsCompactness A f N U)
    (hΛ₀ : IsScPlusMultisection A Λ₀) (hdom₀ : domSupp Λ₀ ⊆ U) {h : A.Obj → ℝ}
    (hhc : Continuous h) (hhφ : ∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) (hh1 : ∀ x, h x ≤ 1)
    (hN₀ : ∀ x, pointwiseNorm N Λ₀ x ≤ h x)
    (hN₀' : ∀ x ∉ A.X.PObj.boundary, pointwiseNorm N Λ₀ x < h x)
    (H : HasLocalParamSeedsRel A f Λ₀ N) :
    ∀ x ∉ A.X.PObj.boundary, 0 < Λ₀ (f x) → ∃ Q : Set A.Obj, IsOpen Q ∧
      A.X.IsSaturated Q ∧ x ∈ Q ∧ Nonempty (RelGPFamily A f Λ₀ N (U ∩ A.X.PObj.boundaryᶜ)
        (fun y => h y - pointwiseNorm N Λ₀ y) Q) := by
  intro x hxb hx
  have hNB : A.B.IsAuxNorm N := hcc.1.isAuxNorm
  have hxU : x ∈ U := (auxLe_of_pos hf.1.1.1 hΛ₀ hcc.2.2.2.1
    (fun y => (hN₀ y).trans (hh1 y)) hdom₀ hx).1
  set c : ℝ := (h x - pointwiseNorm N Λ₀ x) / 4 with hcdef
  set r : ℝ := (h x + pointwiseNorm N Λ₀ x) / 2 with hrdef
  have hc : 0 < c := by have := hN₀' x hxb; rw [hcdef]; linarith
  set W₁ : Set A.Obj := (U ∩ A.X.PObj.boundaryᶜ) ∩
    ({y | pointwiseNorm N Λ₀ y < r} ∩ {y | r + c < h y}) with hW₁def
  have hW₁ : IsOpen W₁ := (hcc.2.1.inter A.X.PObj.isClosed_boundary.isOpen_compl).inter
    ((isOpen_pointwiseNorm_lt hNB hΛ₀ continuous_const).inter (isOpen_lt continuous_const hhc))
  have hxW₁ : x ∈ W₁ := by
    refine ⟨⟨hxU, hxb⟩, ?_, ?_⟩
    · change pointwiseNorm N Λ₀ x < r
      have := hN₀' x hxb; rw [hrdef]; linarith
    · change r + c < h x
      have := hN₀' x hxb; rw [hrdef, hcdef]; linarith
  obtain ⟨R, V, hprop, hRU, hVo, hxV, hVinv, hVcl⟩ := exists_atomicNbhd x hW₁ hxW₁
  obtain ⟨ℓ, s, hs, hsV, hsN, W, hWo, hxW, hW⟩ := H x hx V hVo hxV c hc
  let S : SeedData A := ⟨x, R, hprop, V, hVo, hxV, hVinv, hVcl, ℓ, s, hs, hsV⟩
  have hch : ∀ y ∈ A.X.saturation S.R.U, c ≤ h y - pointwiseNorm N Λ₀ y := by
    rintro y ⟨a, haU, hay⟩
    obtain ⟨φ, hφs, hφt⟩ := A.X.π_eq_π_iff.1 hay
    have e1 : h y = h a := by rw [← hφt, ← hφs, hhφ φ]
    have e2 : pointwiseNorm N Λ₀ y = pointwiseNorm N Λ₀ a := by
      rw [← hφt, ← hφs]; exact pointwiseNorm_tgt hcc.1 hΛ₀ φ
    rw [e1, e2]
    have h1 : pointwiseNorm N Λ₀ a < r := (hRU haU).2.1
    have h2 : r + c < h a := (hRU haU).2.2
    linarith
  have hUsat : A.X.saturation S.R.U ⊆ U ∩ A.X.PObj.boundaryᶜ :=
    EpGroupoid.saturation_subset_of_isSaturated (X := A.X)
      (isSaturated_inter_boundary_compl hcc.2.2.1) (hRU.trans inter_subset_left)
  have hQo : IsOpen (⋂ k, S.R.U ∩ S.R.Φ k ⁻¹' W) := isOpen_iInter_of_finite fun k =>
    (S.R.continuousOn_Φ k).isOpen_inter_preimage S.R.isOpen_U hWo
  have hxQ : x ∈ ⋂ k, S.R.U ∩ S.R.Φ k ⁻¹' W :=
    mem_iInter.2 fun k => ⟨S.R.mem_U, by rw [mem_preimage, S.R.Φ_self]; exact hxW⟩
  exact ⟨A.X.saturation (⋂ k, S.R.U ∩ S.R.Φ k ⁻¹' W),
    EpGroupoid.isOpen_saturation_of_isOpen A.X hQo, EpGroupoid.isSaturated_saturation A.X _,
    A.X.subset_saturation _ hxQ,
    ⟨(S.relGPFamily h𝒰 hf hΛ₀ hcc.1 hc.le hsN hch (fun y => sub_nonneg.2 (hN₀ y)) hUsat
      hW).saturate hf hΛ₀⟩⟩

/-- **Steps (c)–(d) of the proof of Theorem 15.3.9 (2021 pp. 698–699) for sc⁺ data with
`N(Λ₀) ≤ h`.**  Let `X` be tame with sc-smooth bump functions and a good system, `f` sc-Fredholm
with tame germ data, `(N, U)` controlling compactness, `h ≤ 1` a continuous functor, and `Λ₀` an
sc⁺-multisection with dom-supp in `U`, `N(Λ₀) ≤ h` on `X`, `N(Λ₀) < h` off `∂X`, and `(f, Λ₀)`
in general position at the points of `supp(Λ₀ ∘ f) ∩ ∂X`.  Then there is an sc⁺-multisection
`Λ'` with `Λ' = Λ₀` over `∂X`, dom-supp in `U`, `N(Λ') ≤ h`, and `(f, Λ')` transversal and in
general position. -/
theorem theorem_15_3_7_relative_of_le (hX : A.X.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (h𝒰 : Nonempty A.X.GoodSystem)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hcc : ControlsCompactness A f N U) {h : A.Obj → ℝ}
    (hc : Continuous h) (hfun : ∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) (hh1 : ∀ x, h x ≤ 1)
    (hΛ₀ : IsScPlusMultisection A Λ₀) (hdom₀ : domSupp Λ₀ ⊆ U)
    (hN₀ : ∀ x, pointwiseNorm N Λ₀ x ≤ h x)
    (hN₀' : ∀ x ∉ A.X.PObj.boundary, pointwiseNorm N Λ₀ x < h x)
    (hbd : ∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary →
      0 < Λ₀ (f (A.X.PObj.levelVal 1 x)) → IsReducedOntoAtPt f Λ₀ x) :
    ∃ Λ' : A.W → ℚ≥0, IsScPlusMultisection A Λ' ∧
      (∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ₀ w) ∧ domSupp Λ' ⊆ U ∧
      (∀ x, pointwiseNorm N Λ' x ≤ h x) ∧ IsTransversal f Λ' ∧ IsInGeneralPosition A f Λ' := by
  have hN : A.B.IsAuxNorm N := hcc.1.isAuxNorm
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  have hN1 : ∀ x, pointwiseNorm N Λ₀ x ≤ 1 := fun x => (hN₀ x).trans (hh1 x)
  have hloc : HasLocalGPFamiliesRel A f Λ₀ N (U ∩ A.X.PObj.boundaryᶜ)
      (fun x => h x - pointwiseNorm N Λ₀ x) := by
    refine hasLocalGPFamiliesRel_of_boundary h𝒰 hN (fun x hxb hpos => ?_)
      (exists_relGPFamily_of_seeds_of_le h𝒰 hf hcc hΛ₀ hdom₀ hc hfun hh1 hN₀ hN₀'
        (hasLocalParamSeedsRel hX hbump hf hft hΛ₀ hN))
    have hx1 := mem_levelSet_one_of_pos hf hΛ₀ hpos
    exact exists_isOpen_isReducedOntoAtPt hX hf hft hΛ₀ hx1
      (hbd _ (by rw [A.X.PObj.levelVal_levelMk]; exact hxb)
        (by rw [A.X.PObj.levelVal_levelMk]; exact hpos))
  have hsard := hasParametricGeneralPositionRel hX hf hft hcc hΛ₀ hN1 hdom₀
  have hK := isCompact_image_supp_comp hf hfc hΛ₀ hcc hN1 hdom₀
  obtain ⟨Q, hSQ, ⟨F⟩⟩ := exists_relGPFamily_of_compact h𝒰 hN hK hloc
  have hFU : ∀ t, domSupp (F.Λ t) ⊆ U := fun t => (F.domSupp_subset t).trans inter_subset_left
  obtain ⟨ε, hε, hae⟩ := hsard F.ℓ F.Λ (fun t => (F.isStructurable t).1) F.isLinear
    (fun t x => (F.norm_le t x).trans (mul_le_mul_of_nonneg_left (by linarith [hh1 x])
      (Finset.sum_nonneg fun j _ => abs_nonneg _)))
    hFU (fun x hx => F.paramOnto x (hSQ hx) hx)
  have hr : (0 : ℝ) < min ε (1 / (F.ℓ + 1)) := lt_min hε (by positivity)
  obtain ⟨t, ht, hgp⟩ := exists_norm_lt_of_ae hr (min_le_left _ _) hae
  have hsum : ∑ j, |t j| < 1 := sum_abs_lt_one (ht.trans_le (min_le_right _ _))
  have hΛt := F.isStructurable t
  have hsc : IsScPlusMultisection A (multisectionAdd Λ₀ (F.Λ t)) :=
    definition_13_2_9 hΛ₀ hΛt.1
  refine ⟨multisectionAdd Λ₀ (F.Λ t), hsc, fun w hw => ?_,
    (domSupp_multisectionAdd_subset _ _).trans (union_subset hdom₀ (hFU t)), fun x => ?_,
    isTransversal_of_isInGeneralPosition hf hsc hgp, hgp⟩
  · refine multisectionAdd_eq_left_of_notMem_domSupp hΛ₀ hΛt.1 fun hd => ?_
    exact (F.domSupp_subset t hd).2 hw
  · refine (pointwiseNorm_multisectionAdd_le hN hΛ₀ hΛt.1 x).trans ?_
    have hm : 0 ≤ h x - pointwiseNorm N Λ₀ x := sub_nonneg.2 (hN₀ x)
    have h1 : pointwiseNorm N (F.Λ t) x ≤ h x - pointwiseNorm N Λ₀ x :=
      (F.norm_le t x).trans (mul_le_of_le_one_left hm hsum.le)
    linarith

end SBLocalization

end Polyfold
