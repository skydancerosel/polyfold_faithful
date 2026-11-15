import Polyfold.Chapter15.ProductAuxNorm
import Polyfold.Chapter15.ControllingPairs

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2021), §15.3, the products remark after
**Definition 15.3.3** and **Remark 15.3.4** (pp. 692–693; 2017: after Definition 15.5 and
Remark 15.3).

# The product multisection `Λ × Λ'`

## The text, paraphrased

For two sets of data the product `Λ × Λ'` is `(h, h') ↦ Λ(h) · Λ'(h')`, an sc⁺-multisection
functor of `W × W' → X × X'`; its pointwise norm with respect to `N × N' = max` is the maximum of
the pointwise norms; `t(Λ × Λ') = (tΛ) × (tΛ')`; admissibility is preserved.  (Remark 15.3.4) The
domain support of `Λ × Λ'` lies in `(U × X') ∪ (X × U')` when those of `Λ`, `Λ'` lie in `U`, `U'`.

## What is formalized

* `SEP.prod A A'`: the product of two bundled strong bundles over ep-groupoids.
* `SBLocalization.prodMult Λ Λ'`, `isWFunctor_prodMult`, `IsScPlusSectionOn.prodMap`,
  `IsLocalRepOn.prodMult` (the sections `sᵢ × s'ⱼ` with the weights `σᵢσ'ⱼ`),
  **`IsScPlusMultisection.prodMult`**.
* `suppAt_prodMult`, `normW_prodAuxNorm`, **`pointwiseNorm_prodMult`**
  (`(N × N')(Λ × Λ')(x, x') = max(N(Λ)(x), N'(Λ')(x'))`).
* **`multisectionSmul_prodMult`** (`t(Λ × Λ') = (tΛ) × (tΛ')`).
* **`IsAdmissible.prodMult`** (admissibility with respect to `(N × N', U × U')`).
* **`remark_15_3_4`** (the domain support), `domSupp_prodMult` (the exact domain support
  `(dom-supp Λ × X') ∪ (X × dom-supp Λ')`) and `remark_15_3_4_eq_univ` (it lies in `U × U'`
  only if `U' = X'`, unless `Λ` is the multisection of the zero section).
* **`ControlsCompactness.prod`**: `(N × N', U × U')` controls the compactness of `f × f'`
  (Definition 15.3.1 for the product data), with `auxLe_prodAuxNorm`,
  `solutionSet_prodMap`, `isSaturated_prod`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace SEP

instance instParacompactObjProd (A A' : SEP.{u}) : ParacompactSpace (A.Obj × A'.Obj) :=
  MPolyfold.paracompactSpace_prod A.X.PObj A'.X.PObj

instance instParacompactMorProd (A A' : SEP.{u}) : ParacompactSpace (A.Mor × A'.Mor) :=
  MPolyfold.paracompactSpace_prod A.X.PMor A'.X.PMor

instance instParacompactWProd (A A' : SEP.{u}) : ParacompactSpace (A.W × A'.W) :=
  StrongBundle.paracompactSpace_prod A.B A'.B

/-- **The product of two strong bundles over ep-groupoids** (p. 692): `W × W' → X × X'` with
`μ × μ'`. -/
abbrev prod (A A' : SEP.{u}) : SEP.{u} where
  Obj := A.Obj × A'.Obj
  Mor := A.Mor × A'.Mor
  X := A.X.prod A'.X
  W := A.W × A'.W
  P := Prod.map A.P A'.P
  B := A.B.prod A'.B
  E := A.E.prod A'.E

end SEP

namespace SBLocalization

open StrongBundle

variable {A A' : SEP.{u}}

/-- **The product multisection** `(Λ × Λ')(h, h') = Λ(h) · Λ'(h')` (p. 692). -/
def prodMult (Λ : A.W → ℚ≥0) (Λ' : A'.W → ℚ≥0) : (A.prod A').W → ℚ≥0 :=
  fun w => Λ w.1 * Λ' w.2

@[simp] lemma prodMult_apply (Λ : A.W → ℚ≥0) (Λ' : A'.W → ℚ≥0) (w : (A.prod A').W) :
    prodMult Λ Λ' w = Λ w.1 * Λ' w.2 := rfl

/-- `Λ × Λ'` is a functor on `W × W'`. -/
theorem isWFunctor_prodMult {Λ : A.W → ℚ≥0} {Λ' : A'.W → ℚ≥0} (h : IsWFunctor A Λ)
    (h' : IsWFunctor A' Λ') : IsWFunctor (A.prod A') (prodMult Λ Λ') := fun q => by
  have e := h (prodPullbackSplit A.X A'.X q).1
  have e' := h' (prodPullbackSplit A.X A'.X q).2
  change Λ (A.E.μ (prodPullbackSplit A.X A'.X q).1) * Λ' (A'.E.μ (prodPullbackSplit A.X A'.X q).2)
    = _
  rw [e, e']
  rfl

/-- Products of sc⁺-sections on open sets. -/
theorem IsScPlusSectionOn.prodMap {s : A.Obj → A.W} {s' : A'.Obj → A'.W} {O : Set A.Obj}
    {O' : Set A'.Obj} (h : IsScPlusSectionOn A s O) (h' : IsScPlusSectionOn A' s' O') :
    IsScPlusSectionOn (A.prod A') (Prod.map s s') (O ×ˢ O') := by
  obtain ⟨hs, G, hG, hGs⟩ := h
  obtain ⟨hs', G', hG', hGs'⟩ := h'
  have := A.B.paracompactSpace_prod_one A'.B
  refine ⟨fun y hy => Prod.ext (hs y.1 hy.1) (hs' y.2 hy.2),
    fun y => (A.B.prodOneHomeomorph A'.B).symm (G y.1, G' y.2),
    fun y hy => Prod.ext (hG y.1 hy.1) (hG' y.2 hy.2), ?_⟩
  have h1 : (A.X.PObj.prod A'.X.PObj).IsScSmoothOn (A.B.toMPolyfold1.prod A'.B.toMPolyfold1)
      (Prod.map G G') (O ×ˢ O') := hGs.prodMap hGs'
  exact MPolyfold.IsScSmoothOn.comp (A.B.isScSmoothMap_prodOneHomeomorph_symm A'.B) h1
    fun _ _ => mem_univ _

open scoped Classical in
/-- **Products of local representations**: the sections `sᵢ × s'ⱼ` with the weights `σᵢσ'ⱼ`
represent `Λ × Λ'` over `O × O'`. -/
theorem IsLocalRepOn.prodMult {Λ : A.W → ℚ≥0} {Λ' : A'.W → ℚ≥0} {O : Set A.Obj}
    {O' : Set A'.Obj} {k k' : ℕ} {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0}
    {s' : Fin k' → A'.Obj → A'.W} {σ' : Fin k' → ℚ≥0} (h : IsLocalRepOn A Λ O s σ)
    (h' : IsLocalRepOn A' Λ' O' s' σ') :
    IsLocalRepOn (A.prod A') (prodMult Λ Λ') (O ×ˢ O')
      (fun κ : Fin (k * k') => Prod.map (s (finProdFinEquiv.symm κ).1)
        (s' (finProdFinEquiv.symm κ).2))
      (fun κ => σ (finProdFinEquiv.symm κ).1 * σ' (finProdFinEquiv.symm κ).2) := by
  refine ⟨fun κ => mul_pos (h.1 _) (h'.1 _), fun κ => (h.2.1 _).prodMap (h'.2.1 _), ?_, ?_⟩
  · rw [Equiv.sum_comp finProdFinEquiv.symm (fun p : Fin k × Fin k' => σ p.1 * σ' p.2),
      Fintype.sum_prod_type, ← Finset.sum_mul_sum, h.2.2.1, h'.2.2.1, one_mul]
  · intro w hw
    have e := h.2.2.2 w.1 hw.1
    have e' := h'.2.2.2 w.2 hw.2
    refine Eq.trans ?_ (Equiv.sum_comp finProdFinEquiv.symm (fun p : Fin k × Fin k' =>
      @ite ℚ≥0 (w = Prod.map (s p.1) (s' p.2) ((A.prod A').P w)) (Classical.propDecidable _)
        (σ p.1 * σ' p.2) 0)).symm
    rw [Fintype.sum_prod_type, prodMult_apply, e, e', Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hiff : w = Prod.map (s i) (s' j) ((A.prod A').P w) ↔
        w.1 = s i (A.P w.1) ∧ w.2 = s' j (A'.P w.2) := Prod.ext_iff
    by_cases h1 : w.1 = s i (A.P w.1)
    · by_cases h2 : w.2 = s' j (A'.P w.2)
      · rw [if_pos (hiff.2 ⟨h1, h2⟩), if_pos h1, if_pos h2]
      · rw [if_neg fun e => h2 (hiff.1 e).2, if_neg h2, mul_zero]
    · rw [if_neg fun e => h1 (hiff.1 e).1, if_neg h1, zero_mul]

/-- **`Λ × Λ'` is an sc⁺-multisection** (p. 692). -/
theorem IsScPlusMultisection.prodMult {Λ : A.W → ℚ≥0} {Λ' : A'.W → ℚ≥0}
    (h : IsScPlusMultisection A Λ) (h' : IsScPlusMultisection A' Λ') :
    IsScPlusMultisection (A.prod A') (prodMult Λ Λ') := by
  refine ⟨isWFunctor_prodMult h.1 h'.1, fun x₀ => ?_⟩
  obtain ⟨O, k, s, σ, hO, hx, hr⟩ := h.exists_isLocalRepOn x₀.1
  obtain ⟨O', k', s', σ', hO', hx', hr'⟩ := h'.exists_isLocalRepOn x₀.2
  exact hasLocalSectionStructure_of_isLocalRepOn (A := A.prod A') (hO.prod hO') ⟨hx, hx'⟩
    (hr.prodMult hr')

/-- `supp(Λ × Λ')(x, x') = supp(Λ)(x) × supp(Λ')(x')`. -/
theorem suppAt_prodMult (Λ : A.W → ℚ≥0) (Λ' : A'.W → ℚ≥0) (x : (A.prod A').Obj) :
    suppAt (A := A.prod A') (prodMult Λ Λ') x = suppAt Λ x.1 ×ˢ suppAt Λ' x.2 := by
  ext w
  change (Prod.map A.P A'.P w = x ∧ 0 < Λ w.1 * Λ' w.2) ↔
    (A.P w.1 = x.1 ∧ 0 < Λ w.1) ∧ (A'.P w.2 = x.2 ∧ 0 < Λ' w.2)
  rw [Prod.ext_iff, pos_iff_ne_zero, pos_iff_ne_zero, pos_iff_ne_zero, mul_ne_zero_iff]
  exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c⟩, b, d⟩, fun ⟨⟨a, c⟩, b, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩

/-- On `(W × W')_{0,1}` the norm `N × N'` is the maximum. -/
theorem normW_prodAuxNorm (N : A.B.One → ℝ) (N' : A'.B.One → ℝ) {w : (A.prod A').W}
    (h : w.1 ∈ A.B.oneSet) (h' : w.2 ∈ A'.B.oneSet) :
    normW (A := A.prod A') (A.B.prodAuxNorm A'.B N N') w = max (normW N w.1) (normW N' w.2) := by
  have hw : w ∈ (A.prod A').B.oneSet := (A.B.mem_oneSet_prod A'.B).2 ⟨h, h'⟩
  rw [normW_of_mem N h, normW_of_mem N' h']
  exact (normW_of_mem (A := A.prod A') _ hw).trans rfl

/-- **p. 692**: `(N × N')(Λ × Λ')(x, x') = max{N(Λ)(x), N'(Λ')(x')}`. -/
theorem pointwiseNorm_prodMult {Λ : A.W → ℚ≥0} {Λ' : A'.W → ℚ≥0}
    (h : IsScPlusMultisection A Λ) (h' : IsScPlusMultisection A' Λ') (N : A.B.One → ℝ)
    (N' : A'.B.One → ℝ) (x : (A.prod A').Obj) :
    pointwiseNorm (A := A.prod A') (A.B.prodAuxNorm A'.B N N') (prodMult Λ Λ') x =
      max (pointwiseNorm N Λ x.1) (pointwiseNorm N' Λ' x.2) := by
  have g := (h.prodMult h').isGreatest_pointwiseNorm (A.B.prodAuxNorm A'.B N N') x
  have g₁ := h.isGreatest_pointwiseNorm N x.1
  have g₂ := h'.isGreatest_pointwiseNorm N' x.2
  refine g.unique ⟨?_, ?_⟩
  · obtain ⟨w, hw, e⟩ := g₁.1
    obtain ⟨w', hw', e'⟩ := g₂.1
    refine ⟨(w, w'), ?_, ?_⟩
    · rw [suppAt_prodMult]; exact ⟨hw, hw'⟩
    · rw [normW_prodAuxNorm N N' (h.suppAt_subset_oneSet _ hw) (h'.suppAt_subset_oneSet _ hw'), e,
        e']
  · rintro _ ⟨w, hw, rfl⟩
    rw [suppAt_prodMult] at hw
    rw [normW_prodAuxNorm N N' (h.suppAt_subset_oneSet _ hw.1) (h'.suppAt_subset_oneSet _ hw.2)]
    exact max_le_max (g₁.2 ⟨w.1, hw.1, rfl⟩) (g₂.2 ⟨w.2, hw.2, rfl⟩)

/-- **p. 692**: `t(Λ × Λ') = (tΛ) × (tΛ')`. -/
theorem multisectionSmul_prodMult (t : ℝ) (Λ : A.W → ℚ≥0) (Λ' : A'.W → ℚ≥0) :
    multisectionSmul (A := A.prod A') t (prodMult Λ Λ') =
      prodMult (multisectionSmul t Λ) (multisectionSmul t Λ') := by
  classical
  funext w
  change smulAt (A := A.prod A') t (prodMult Λ Λ') ((A.prod A').P w) (toFib (A := A.prod A') w) =
    smulAt t Λ (A.P w.1) (toFib w.1) * smulAt t Λ' (A'.P w.2) (toFib w.2)
  unfold smulAt
  have hfst : ∀ v : (A.prod A').P ⁻¹' {(A.prod A').P w},
      prodFiberEquiv A.P A'.P _ v = 0 ↔ v = 0 := fun v =>
    (prodFiberCLE A.P A'.P ((A.prod A').P w)).map_eq_zero_iff
  by_cases ht : t = 0
  · rw [if_pos ht, if_pos ht, if_pos ht]
    have hz : toFib (A := A.prod A') w = 0 ↔ toFib w.1 = 0 ∧ toFib w.2 = 0 := by
      rw [← hfst, Prod.ext_iff]
      rfl
    by_cases h1 : toFib w.1 = 0
    · by_cases h2 : toFib w.2 = 0
      · rw [if_pos (hz.2 ⟨h1, h2⟩), if_pos h1, if_pos h2, mul_one]
      · rw [if_neg fun e => h2 (hz.1 e).2, if_neg h2, mul_zero]
    · rw [if_neg fun e => h1 (hz.1 e).1, if_neg h1, zero_mul]
  · rw [if_neg ht, if_neg ht, if_neg ht]
    have e := prodFiberEquiv_smul A.P A'.P ((A.prod A').P w) t⁻¹ (toFib (A := A.prod A') w)
    have e1 : (((t⁻¹ • toFib (A := A.prod A') w : (A.prod A').P ⁻¹' {(A.prod A').P w}) :
        (A.prod A').W)).1 = ((t⁻¹ • toFib w.1 : A.P ⁻¹' {A.P w.1}) : A.W) :=
      congrArg (fun z => (z.1 : A.W)) e
    have e2 : (((t⁻¹ • toFib (A := A.prod A') w : (A.prod A').P ⁻¹' {(A.prod A').P w}) :
        (A.prod A').W)).2 = ((t⁻¹ • toFib w.2 : A'.P ⁻¹' {A'.P w.2}) : A'.W) :=
      congrArg (fun z => (z.2 : A'.W)) e
    rw [prodMult_apply, e1, e2]

/-- **Admissible perturbations behave well under products** (p. 692): if `Λ` is
`(N, U)`-admissible for `f` and `Λ'` is `(N', U')`-admissible for `f'`, then `Λ × Λ'` is
`(N × N', U × U')`-admissible for `f × f'`. -/
theorem IsAdmissible.prodMult {f : A.Obj → A.W} {f' : A'.Obj → A'.W} {N : A.B.One → ℝ}
    {N' : A'.B.One → ℝ} {U : Set A.Obj} {U' : Set A'.Obj} {Λ : A.W → ℚ≥0} {Λ' : A'.W → ℚ≥0}
    (h : IsAdmissible A f N U Λ) (h' : IsAdmissible A' f' N' U' Λ') :
    IsAdmissible (A.prod A') (Prod.map f f') (A.B.prodAuxNorm A'.B N N') (U ×ˢ U')
      (prodMult Λ Λ') := by
  refine ⟨h.1.prodMult h'.1, fun x => ?_, ?_⟩
  · rw [pointwiseNorm_prodMult h.1 h'.1]
    exact max_le (h.2.1 _) (h'.2.1 _)
  · rintro x ⟨t, ht, hpos⟩
    rw [multisectionSmul_prodMult, prodMult_apply] at hpos
    have hne := mul_ne_zero_iff.1 hpos.ne'
    exact ⟨h.2.2 ⟨t, ht, pos_iff_ne_zero.2 hne.1⟩, h'.2.2 ⟨t, ht, pos_iff_ne_zero.2 hne.2⟩⟩

/-- **Remark 15.3.4, p. 693 (2017: Remark 15.3)**: if `Λ` has domain support in `U` and `Λ'` in
`U'` (closed sets, or any sets containing the domain supports), the domain support of `Λ × Λ'`
lies in `(dom-supp Λ × X') ∪ (X × dom-supp Λ')`, hence in `(U × X') ∪ (X × U')`. -/
theorem remark_15_3_4 {Λ : A.W → ℚ≥0} {Λ' : A'.W → ℚ≥0} {U : Set A.Obj} {U' : Set A'.Obj}
    (hU : domSupp Λ ⊆ U) (hU' : domSupp Λ' ⊆ U') :
    domSupp (A := A.prod A') (prodMult Λ Λ') ⊆ (U ×ˢ univ) ∪ (univ ×ˢ U') := by
  have hcl : IsClosed ((domSupp Λ ×ˢ (univ : Set A'.Obj)) ∪
      ((univ : Set A.Obj) ×ˢ domSupp Λ')) :=
    (isClosed_closure.prod isClosed_univ).union (isClosed_univ.prod isClosed_closure)
  have hsub : (domSupp Λ ×ˢ (univ : Set A'.Obj)) ∪ ((univ : Set A.Obj) ×ˢ domSupp Λ') ⊆
      (U ×ˢ univ) ∪ (univ ×ˢ U') :=
    union_subset_union (prod_mono hU subset_rfl) (prod_mono subset_rfl hU')
  refine (closure_minimal ?_ hcl).trans hsub
  rintro x ⟨w, hw, hw0, hpos⟩
  have hne := mul_ne_zero_iff.1 (ne_of_gt hpos)
  have hw1 : A.P w.1 = x.1 := congrArg Prod.fst hw
  have hw2 : A'.P w.2 = x.2 := congrArg Prod.snd hw
  by_cases h1 : w.1 = fiberZero A.P x.1
  · right
    refine ⟨mem_univ _, subset_closure ⟨w.2, hw2, fun h2 => hw0 ?_, pos_iff_ne_zero.2 hne.2⟩⟩
    exact Prod.ext h1 h2
  · left
    exact ⟨subset_closure ⟨w.1, hw1, h1, pos_iff_ne_zero.2 hne.1⟩, mem_univ _⟩

/-- **Remark 15.3.4, the exact domain support**: for sc⁺-multisections,
`dom-supp(Λ × Λ') = (dom-supp Λ × X') ∪ (X × dom-supp Λ')`. -/
theorem domSupp_prodMult {Λ : A.W → ℚ≥0} {Λ' : A'.W → ℚ≥0} (h : IsScPlusMultisection A Λ)
    (h' : IsScPlusMultisection A' Λ') :
    domSupp (A := A.prod A') (prodMult Λ Λ') =
      (domSupp Λ ×ˢ (univ : Set A'.Obj)) ∪ ((univ : Set A.Obj) ×ˢ domSupp Λ') := by
  refine Subset.antisymm (remark_15_3_4 subset_rfl subset_rfl) (union_subset ?_ ?_)
  · have e : domSupp Λ ×ˢ (univ : Set A'.Obj) =
        closure ({x | ∃ w, A.P w = x ∧ w ≠ fiberZero A.P x ∧ 0 < Λ w} ×ˢ (univ : Set A'.Obj)) := by
      rw [closure_prod_eq, closure_univ]; rfl
    rw [e]
    refine closure_mono ?_
    rintro x ⟨⟨w, hw, hw0, hpos⟩, -⟩
    obtain ⟨w', hw', hpos'⟩ := h'.suppAt_nonempty x.2
    exact ⟨(w, w'), Prod.ext hw hw', fun e0 => hw0 (congrArg Prod.fst e0 |>.trans
      (congrArg (fun z => (z.1 : A.W)) (prodFiberCLE A.P A'.P x).map_zero)), mul_pos hpos hpos'⟩
  · have e : (univ : Set A.Obj) ×ˢ domSupp Λ' =
        closure ((univ : Set A.Obj) ×ˢ
          {x | ∃ w, A'.P w = x ∧ w ≠ fiberZero A'.P x ∧ 0 < Λ' w}) := by
      rw [closure_prod_eq, closure_univ]; rfl
    rw [e]
    refine closure_mono ?_
    rintro x ⟨-, ⟨w', hw', hw0', hpos'⟩⟩
    obtain ⟨w, hw, hpos⟩ := h.suppAt_nonempty x.1
    exact ⟨(w, w'), Prod.ext hw hw', fun e0 => hw0' (congrArg Prod.snd e0 |>.trans
      (congrArg (fun z => (z.2 : A'.W)) (prodFiberCLE A.P A'.P x).map_zero)), mul_pos hpos hpos'⟩

/-- **Remark 15.3.4, "not necessarily in `U × U'`"**: if the domain support of `Λ × Λ'` lies in
`U × U'` and `Λ` is not the multisection of the zero section (its domain support is nonempty),
then `U'` is all of `X'`. -/
theorem remark_15_3_4_eq_univ {Λ : A.W → ℚ≥0} {Λ' : A'.W → ℚ≥0} (h : IsScPlusMultisection A Λ)
    (h' : IsScPlusMultisection A' Λ') {U : Set A.Obj} {U' : Set A'.Obj}
    (hsub : domSupp (A := A.prod A') (prodMult Λ Λ') ⊆ U ×ˢ U') (hne : (domSupp Λ).Nonempty) :
    U' = univ := by
  obtain ⟨x, hx⟩ := hne
  refine eq_univ_of_forall fun x' => ?_
  have hmem : ((x, x') : (A.prod A').Obj) ∈ domSupp (A := A.prod A') (prodMult Λ Λ') := by
    rw [domSupp_prodMult h h']
    exact Or.inl ⟨hx, mem_univ _⟩
  exact (hsub hmem).2

/-! ### The product data `(N × N', U × U')` control compactness -/

/-- `(N × N')(h, h') ≤ r` iff `N(h) ≤ r` and `N'(h') ≤ r` (with the value `+∞` off
`W_{0,1}`). -/
theorem auxLe_prodAuxNorm (N : A.B.One → ℝ) (N' : A'.B.One → ℝ) (w : (A.prod A').W) (r : ℝ) :
    (A.prod A').B.AuxLe (A.B.prodAuxNorm A'.B N N') w r ↔
      A.B.AuxLe N w.1 r ∧ A'.B.AuxLe N' w.2 r := by
  constructor
  · rintro ⟨hw, hle⟩
    have hw' := (A.B.mem_oneSet_prod A'.B).1 hw
    exact ⟨⟨hw'.1, (le_max_left _ _).trans hle⟩, ⟨hw'.2, (le_max_right _ _).trans hle⟩⟩
  · rintro ⟨⟨h1, l1⟩, ⟨h2, l2⟩⟩
    exact ⟨(A.B.mem_oneSet_prod A'.B).2 ⟨h1, h2⟩, max_le l1 l2⟩

/-- The solution set of `f × f'` is the product of the solution sets. -/
theorem solutionSet_prodMap (f : A.Obj → A.W) (f' : A'.Obj → A'.W) :
    solutionSet (A.prod A').P (Prod.map f f') = solutionSet A.P f ×ˢ solutionSet A'.P f' := by
  ext x
  change Prod.map f f' x = fiberZero (Prod.map A.P A'.P) x ↔
    f x.1 = fiberZero A.P x.1 ∧ f' x.2 = fiberZero A'.P x.2
  have hz : fiberZero (Prod.map A.P A'.P) x = (fiberZero A.P x.1, fiberZero A'.P x.2) := by
    have e := (prodFiberCLE A.P A'.P x).map_zero
    exact Prod.ext (congrArg (fun z => (z.1 : A.W)) e) (congrArg (fun z => (z.2 : A'.W)) e)
  rw [hz]
  exact Prod.ext_iff

/-- Products of saturated sets are saturated in `X × X'`. -/
theorem isSaturated_prod {U : Set A.Obj} {U' : Set A'.Obj} (hU : A.X.IsSaturated U)
    (hU' : A'.X.IsSaturated U') : (A.prod A').X.IsSaturated (U ×ˢ U') := by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro x ⟨y, hy, hxy⟩
  have h := (EpGroupoid.prod_π_eq_π_iff A.X A'.X y x).1 hxy
  refine ⟨?_, ?_⟩
  · rw [← hU]; exact ⟨y.1, hy.1, h.1⟩
  · rw [← hU']; exact ⟨y.2, hy.2, h.2⟩

/-- **Definition 15.3.1 for the product data** (p. 692, "take the product"): if `(N, U)`
controls the compactness of `f` and `(N', U')` that of `f'`, then `(N × N', U × U')` controls the
compactness of `f × f'`. -/
theorem ControlsCompactness.prod {f : A.Obj → A.W} {f' : A'.Obj → A'.W} {N : A.B.One → ℝ}
    {N' : A'.B.One → ℝ} {U : Set A.Obj} {U' : Set A'.Obj} (h : ControlsCompactness A f N U)
    (h' : ControlsCompactness A' f' N' U') :
    ControlsCompactness (A.prod A') (Prod.map f f') (A.B.prodAuxNorm A'.B N N') (U ×ˢ U') := by
  obtain ⟨hN, hUo, hUs, hSU, hK⟩ := h
  obtain ⟨hN', hUo', hUs', hSU', hK'⟩ := h'
  refine ⟨EpStrongBundle.isAuxNorm_prodAuxNorm hN hN', hUo.prod hUo', isSaturated_prod hUs hUs',
    ?_, ?_⟩
  · rw [solutionSet_prodMap]; exact prod_mono hSU hSU'
  · -- the quotient map `π × π'` and the induced map `|X| × |X'| → |X × X'|`
    have hq : IsQuotientMap (Prod.map A.X.π A'.X.π) :=
      (A.X.proposition_7_1_8.prodMap A'.X.proposition_7_1_8).isQuotientMap
        (A.X.continuous_π.prodMap A'.X.continuous_π)
        (Quotient.mk_surjective.prodMap Quotient.mk_surjective)
    set j : A.X.OrbitSpace × A'.X.OrbitSpace → (A.prod A').X.OrbitSpace := fun z =>
      (A.prod A').X.π (Quotient.out z.1, Quotient.out z.2) with hj
    have hjπ : ∀ x : (A.prod A').Obj, j (A.X.π x.1, A'.X.π x.2) = (A.prod A').X.π x := fun x =>
      (EpGroupoid.prod_π_eq_π_iff A.X A'.X _ _).2 ⟨Quotient.out_eq _, Quotient.out_eq _⟩
    have hjc : Continuous j := by
      rw [hq.continuous_iff]
      exact (A.prod A').X.continuous_π.congr fun x => (hjπ x).symm
    have hcomp := (hK.prod hK').image hjc
    refine hcomp.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcomp.isClosed)
    rintro _ ⟨x, ⟨hxU, hx⟩, rfl⟩
    rw [auxLe_prodAuxNorm] at hx
    exact ⟨(A.X.π x.1, A'.X.π x.2), ⟨subset_closure ⟨x.1, ⟨hxU.1, hx.1⟩, rfl⟩,
      subset_closure ⟨x.2, ⟨hxU.2, hx.2⟩, rfl⟩⟩, hjπ x⟩

end SBLocalization

end Polyfold
