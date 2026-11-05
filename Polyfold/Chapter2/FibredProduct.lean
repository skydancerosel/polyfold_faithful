import Polyfold.Chapter2.TameFaces

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.4,
**Proposition 2.46** (fibred products), with the products of M-polyfolds it needs (exposition
Lemma 4.D).

# Products and fibred products of M-polyfolds

## The text, paraphrased

(Proposition 2.46) Let `f : X → Z` be a local sc-diffeomorphism and `g : Y → Z` sc-smooth.  Then
`X ₓ×_g Y = {(x, y) | f(x) = g(y)}` is a sub-M-polyfold of `X × Y`.  If `Y` is tame, so is
`X ₓ×_g Y`, and `d_{X ₓ×_g Y}(x, y) = d_Y(y)`.  If `X` and `Y` are tame and `f`, `g` are both local
sc-diffeomorphisms, `d_{X ₓ×_g Y}(x, y) = ½ d_{X×Y}(x, y) = ½(d_X(x) + d_Y(y)) = d_X(x) = d_Y(y)`.
The text uses, without stating it, that `X × Y` is an M-polyfold with the product charts and
that `d_{X × Y} = d_X + d_Y` for tame `X`, `Y` (exposition Lemma 4.D).

## What is formalized

* `finAppendL : ℝⁿ × ℝⁿ' ≃L ℝⁿ⁺ⁿ'`, `prodPresentation T T'` (the presentation
  `E ⊕ E' ≅ ℝⁿ⁺ⁿ' ⊕ (W ⊕ W')` of `C × C'`), `prod_eq_prodPresentation`,
  `IsPartialQuadrant.prod`, `IsRelOpenInQuadrant.prod`, `degIndexWith_prodPresentation` and
  `degIndex_prod` (`d_{C × C'} = d_C + d_{C'}`), `minimalSubspaceWith_prodPresentation`
  (`E_{(x, x')} = E_x ⊕ E'_{x'}`).
* `IsScSmooth.prodMap`, `scDeriv_prodMap` (`D(f × f') = Df × Df'`), `ScRetraction.prod`,
  `IsScRetract.prod`, `IsScSmoothRetractMap.prodMap`, `IsScSubspace.prod`, `IsScSplitting.prod`,
  `ScRetraction.IsTameWith.prod` (products of tame retractions are tame).
* `LocalModel.prod`, `MChart.prod`, `MChart.overlap_prod`, `MChart.Compatible.prod`,
  `MPolyfold.paracompactSpace_prod` (from Theorem 2.16), `MPolyfold.prod` (**Lemma 4.D**: `X × Y`
  with the product charts), `MPolyfold.IsChart.prod`, `MPolyfold.degIndex_prod_le`
  (`d_{X × Y} ≤ d_X + d_Y`), `MPolyfold.isTame_prod` (tame factors: `X × Y` is tame and
  `d_{X × Y} = d_X + d_Y`), `MPolyfold.isScSmoothMap_fst`, `MPolyfold.isScSmoothMap_snd`,
  `MPolyfold.IsScSmoothOn.prodMk`.
* `MPolyfold.IsLocalScDiffeo`, `MPolyfold.fibredProduct`, the retractions `fibredSubDataL`
  (`R(x', y') = ((f|_U)⁻¹(g(y')), y')`) and `fibredSubDataR`, `isSubMPolyfold_fibredProduct`,
  `isScDiffeoOn_snd_fibredProduct` / `isScDiffeoOn_fst_fibredProduct` (`π₂`, resp. `π₁`, is an
  sc-diffeomorphism near each point), `degIndex_fibredProduct_eq_snd` / `_fst`,
  `isTame_fibredProduct`, and `MPolyfold.proposition_2_46`,
  `MPolyfold.proposition_2_46_of_isLocalScDiffeo` (**Proposition 2.46**).

## What the text leaves implicit, and the choices made

* "Local sc-diffeomorphism" is read as: every `x` has an open neighbourhood `U` such that `f|_U`
  is an sc-diffeomorphism onto an open subset of `Z` (`IsScDiffeoOn`).
* The fibred product carries the sub-M-polyfold structure of Proposition 2.21; it is paracompact
  as a closed subset of the metrizable `X × Y`.
* The inverse of `π₂` near `(x, y)` is `y' ↦ ((f|_U)⁻¹(g(y')), y')` followed by Proposition
  2.21 (2); the exposition's factorization through `y' ↦ (x, y')` is not sc-smooth unless `x` is
  a smooth point (a constant map is sc⁰ only when its value lies in `X_∞`).
* In the last statement, `d_{X ₓ×_g Y} = d_X = d_Y` holds without tameness (Proposition 2.24 along
  `π₁` and `π₂`); tameness enters only through `d_{X × Y} = d_X + d_Y`, stated as
  `2 d_{X ₓ×_g Y}(x, y) = d_{X × Y}(x, y)`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

/-! ### `ℝⁿ × ℝⁿ' ≅ ℝⁿ⁺ⁿ'` -/

section FinAppend

variable (n n' : ℕ)

/-- `(a, b) ↦ (a₁, …, a_n, b₁, …, b_{n'})`, as a linear equivalence. -/
def finAppendLE : ((Fin n → ℝ) × (Fin n' → ℝ)) ≃ₗ[ℝ] (Fin (n + n') → ℝ) where
  toFun p := Fin.append p.1 p.2
  invFun c := (fun i => c (Fin.castAdd n' i), fun j => c (Fin.natAdd n j))
  map_add' p q := by
    funext l
    refine Fin.addCases (fun i => ?_) (fun j => ?_) l <;> simp
  map_smul' c p := by
    funext l
    refine Fin.addCases (fun i => ?_) (fun j => ?_) l <;> simp
  left_inv p := by simp
  right_inv c := by
    funext l
    refine Fin.addCases (fun i => ?_) (fun j => ?_) l <;> simp

/-- `(a, b) ↦ (a, b)` as a continuous linear equivalence `ℝⁿ × ℝⁿ' ≅ ℝⁿ⁺ⁿ'`. -/
def finAppendL : ((Fin n → ℝ) × (Fin n' → ℝ)) ≃L[ℝ] (Fin (n + n') → ℝ) :=
  (finAppendLE n n').toContinuousLinearEquiv

variable {n n'}

@[simp] lemma finAppendL_castAdd (p : (Fin n → ℝ) × (Fin n' → ℝ)) (i : Fin n) :
    finAppendL n n' p (Fin.castAdd n' i) = p.1 i := by
  simp [finAppendL, finAppendLE]

@[simp] lemma finAppendL_natAdd (p : (Fin n → ℝ) × (Fin n' → ℝ)) (j : Fin n') :
    finAppendL n n' p (Fin.natAdd n j) = p.2 j := by
  simp [finAppendL, finAppendLE]

end FinAppend

/-! ### Products of partial quadrants (exposition Lemma 4.D) -/

section ProdQuadrant

variable {E E' : ScBanach} {n n' : ℕ} {W W' : ScBanach}

/-- The presentation `E ⊕ E' ≅ ℝⁿ⁺ⁿ' ⊕ (W ⊕ W')` of `C × C'` built from presentations
`T : E ≅ ℝⁿ ⊕ W` of `C` and `T' : E' ≅ ℝⁿ' ⊕ W'` of `C'`. -/
def prodPresentation (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W')) :
    ScIso (E.prod E') ((ScBanach.const (Fin (n + n') → ℝ)).prod (W.prod W')) where
  lvl m := ((T m).prodCongr (T' m)).trans
    ((ContinuousLinearEquiv.prodProdProdComm ℝ (Fin n → ℝ) (W m) (Fin n' → ℝ) (W' m)).trans
      ((finAppendL n n').prodCongr (ContinuousLinearEquiv.refl ℝ (W m × W' m))))
  incl_comm m x := by
    have h1 := T.incl_comm m x.1
    have h2 := T'.incl_comm m x.2
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · change finAppendL n n' ((T (m + 1) x.1).1, (T' (m + 1) x.2).1) =
        finAppendL n n' ((T m (E.incl m x.1)).1, (T' m (E'.incl m x.2)).1)
      rw [← h1, ← h2]; rfl
    · change W.incl m (T (m + 1) x.1).2 = (T m (E.incl m x.1)).2
      rw [← h1]; rfl
    · change W'.incl m (T' (m + 1) x.2).2 = (T' m (E'.incl m x.2)).2
      rw [← h2]; rfl

variable (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
  (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W'))

lemma prodPresentation_apply (p : (E.prod E') 0) :
    prodPresentation T T' 0 p =
      (finAppendL n n' ((T 0 p.1).1, (T' 0 p.2).1), ((T 0 p.1).2, (T' 0 p.2).2)) := rfl

lemma prodPresentation_castAdd (p : (E.prod E') 0) (i : Fin n) :
    (prodPresentation T T' 0 p).1 (Fin.castAdd n' i) = (T 0 p.1).1 i :=
  finAppendL_castAdd ((T 0 p.1).1, (T' 0 p.2).1) i

lemma prodPresentation_natAdd (p : (E.prod E') 0) (j : Fin n') :
    (prodPresentation T T' 0 p).1 (Fin.natAdd n j) = (T' 0 p.2).1 j :=
  finAppendL_natAdd ((T 0 p.1).1, (T' 0 p.2).1) j

variable {C : Set (E 0)} {C' : Set (E' 0)}

/-- `C × C'` is the partial quadrant of the product presentation. -/
theorem prod_eq_prodPresentation (hT : C = T 0 ⁻¹' quadrant n W 0)
    (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0) :
    C ×ˢ C' = prodPresentation T T' 0 ⁻¹' quadrant (n + n') (W.prod W') 0 := by
  subst hT hT'
  ext p
  change ((∀ i, 0 ≤ (T 0 p.1).1 i) ∧ ∀ j, 0 ≤ (T' 0 p.2).1 j) ↔
    ∀ l, 0 ≤ (prodPresentation T T' 0 p).1 l
  constructor
  · rintro ⟨h1, h2⟩ l
    refine Fin.addCases (fun i => ?_) (fun j => ?_) l
    · rw [prodPresentation_castAdd]; exact h1 i
    · rw [prodPresentation_natAdd]; exact h2 j
  · intro h
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have := h (Fin.castAdd n' i); rwa [prodPresentation_castAdd] at this
    · have := h (Fin.natAdd n j); rwa [prodPresentation_natAdd] at this

theorem IsPartialQuadrant.prod (hC : IsPartialQuadrant E C) (hC' : IsPartialQuadrant E' C') :
    IsPartialQuadrant (E.prod E') (C ×ˢ C') := by
  obtain ⟨n, W, T, hT⟩ := hC
  obtain ⟨n', W', T', hT'⟩ := hC'
  exact ⟨n + n', W.prod W', prodPresentation T T', prod_eq_prodPresentation T T' hT hT'⟩

/-- The degeneracy index is additive: `d_{C × C'}(x, x') = d_C(x) + d_{C'}(x')`, in the
presentations. -/
theorem degIndexWith_prodPresentation (p : (E.prod E') 0) :
    degIndexWith (prodPresentation T T') p = degIndexWith T p.1 + degIndexWith T' p.2 := by
  classical
  unfold degIndexWith quadrantDeg
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [prodPresentation_castAdd]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [prodPresentation_natAdd]

theorem degIndex_prod (hC : IsPartialQuadrant E C) (hC' : IsPartialQuadrant E' C') {x : E 0}
    {x' : E' 0} (hx : x ∈ C) (hx' : x' ∈ C') :
    degIndex (E.prod E') (C ×ˢ C') (x, x') = degIndex E C x + degIndex E' C' x' := by
  obtain ⟨n, W, T, hT⟩ := hC
  obtain ⟨n', W', T', hT'⟩ := hC'
  rw [degIndex_eq (prodPresentation T T') (prod_eq_prodPresentation T T' hT hT') ⟨hx, hx'⟩,
    degIndex_eq T hT hx, degIndex_eq T' hT' hx', degIndexWith_prodPresentation]

/-- `E_{(x, x')} = E_x ⊕ E'_{x'}` for the product presentation. -/
theorem minimalSubspaceWith_prodPresentation (p : (E.prod E') 0) :
    minimalSubspaceWith (prodPresentation T T') p =
      (minimalSubspaceWith T p.1).prod (minimalSubspaceWith T' p.2) := by
  ext v
  rw [Submodule.mem_prod, mem_minimalSubspaceWith, mem_minimalSubspaceWith,
    mem_minimalSubspaceWith]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · have := h (Fin.castAdd n' i) (by rw [prodPresentation_castAdd]; exact hi)
      rwa [prodPresentation_castAdd] at this
    · have := h (Fin.natAdd n j) (by rw [prodPresentation_natAdd]; exact hj)
      rwa [prodPresentation_natAdd] at this
  · rintro ⟨h1, h2⟩ l
    refine Fin.addCases (fun i hi => ?_) (fun j hj => ?_) l
    · rw [prodPresentation_castAdd] at hi ⊢; exact h1 i hi
    · rw [prodPresentation_natAdd] at hj ⊢; exact h2 j hj

theorem IsRelOpenInQuadrant.prod {U : Set (E 0)} {U' : Set (E' 0)}
    (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U') :
    IsRelOpenInQuadrant (E.prod E') (C ×ˢ C') (U ×ˢ U') := by
  obtain ⟨O, hO, rfl⟩ := hU.relOpen
  obtain ⟨O', hO', rfl⟩ := hU'.relOpen
  exact ⟨hU.isPartialQuadrant.prod hU'.isPartialQuadrant, O ×ˢ O', hO.prod hO',
    (prod_inter_prod).symm⟩

lemma lvlSet_prod (U : Set (E 0)) (U' : Set (E' 0)) (m : ℕ) :
    (E.prod E').lvlSet (U ×ˢ U') m = E.lvlSet U m ×ˢ E'.lvlSet U' m := by
  ext p
  rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase]
  rfl

end ProdQuadrant

/-! ### Products of sc-smooth maps and of retractions -/

section ProdMaps

variable {E E' F F' : ScBanach}

/-- `f × f'` is sc-smooth on `U × U'` (Lemma 3.G (3) of Chapter 1 in the exposition). -/
theorem IsScSmooth.prodMap {U : Set (E 0)} {U' : Set (E' 0)} {f : E 0 → F 0} {f' : E' 0 → F' 0}
    (hU : IsScDomain E U) (hU' : IsScDomain E' U') (hUU' : IsScDomain (E.prod E') (U ×ˢ U'))
    (hf : IsScSmooth U f) (hf' : IsScSmooth U' f') :
    IsScSmooth (E := E.prod E') (F := F.prod F') (U ×ˢ U') (Prod.map f f') := by
  have h1 : IsScSmooth (U ×ˢ U') (f ∘ ScBanach.prodFstOp E E' 0) :=
    IsScSmooth.comp hUU' hU hf ((ScBanach.prodFstOp E E').isScSmooth hUU') fun p hp => hp.1
  have h2 : IsScSmooth (U ×ˢ U') (f' ∘ ScBanach.prodSndOp E E' 0) :=
    IsScSmooth.comp hUU' hU' hf' ((ScBanach.prodSndOp E E').isScSmooth hUU') fun p hp => hp.2
  exact IsScSmooth.scPair hUU' h1 h2

/-- The derivative of `f × f'` at a level-`1` point is `Df(x) × Df'(x')`. -/
theorem scDeriv_prodMap {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)} {U' : Set (E' 0)}
    {f : E 0 → F 0} {f' : E' 0 → F' 0} (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (hf : IsScSmooth U f) (hf' : IsScSmooth U' f')
    {x : (E.prod E') 1} (hx : x ∈ (E.prod E').lvlSet (U ×ˢ U') 1) :
    scDeriv (E := E.prod E') (F := F.prod F') (U ×ˢ U') (Prod.map f f') x =
      (scDeriv U f x.1).prodMap (scDeriv U' f' x.2) := by
  have hUU' := (hU.prod hU').isScDomain
  have hsm := IsScSmooth.prodMap hU.isScDomain hU'.isScDomain hUU' hf hf'
  have h1 := (hsm.isSc1.isSc1With_scDeriv).hasFDerivWithinAt x hx
  rw [lvlSet_prod] at hx
  have hx1 := hf.isSc1.isSc1With_scDeriv.hasFDerivWithinAt x.1 hx.1
  have hx2 := hf'.isSc1.isSc1With_scDeriv.hasFDerivWithinAt x.2 hx.2
  have h2 : HasFDerivWithinAt (Prod.map f f' ∘ (E.prod E').toBase 1)
      (((scDeriv U f x.1).prodMap (scDeriv U' f' x.2)).comp ((E.prod E').toBase 1))
      ((E.prod E').lvlSet (U ×ˢ U') 1) x := by
    have he : Prod.map f f' ∘ (E.prod E').toBase 1 =
        Prod.map (f ∘ E.toBase 1) (f' ∘ E'.toBase 1) := by
      funext q; rw [Function.comp_apply, ScBanach.prod_toBase]; rfl
    have hd : ((scDeriv U f x.1).prodMap (scDeriv U' f' x.2)).comp ((E.prod E').toBase 1) =
        ((scDeriv U f x.1).comp (E.toBase 1)).prodMap ((scDeriv U' f' x.2).comp (E'.toBase 1)) := by
      refine ContinuousLinearMap.ext fun q => ?_
      rw [ContinuousLinearMap.comp_apply, ScBanach.prod_toBase]; rfl
    have h3 : HasFDerivWithinAt (Prod.map (f ∘ E.toBase 1) (f' ∘ E'.toBase 1))
        (((scDeriv U f x.1).comp (E.toBase 1)).prodMap ((scDeriv U' f' x.2).comp (E'.toBase 1)))
        (E.lvlSet U 1 ×ˢ E'.lvlSet U' 1) (x.1, x.2) :=
      HasFDerivWithinAt.prodMap (p := (x.1, x.2)) (hx1.mono (fst_image_prod_subset _ _))
        (hx2.mono (snd_image_prod_subset _ _))
    rw [he, hd, lvlSet_prod]
    exact h3
  have h := (hUU'.uniqueDiffWithinAt_one x (by rw [lvlSet_prod]; exact hx)).eq h1 h2
  have hd : Dense (Submodule.span ℝ (range ((E.prod E').toBase 1)) : Set ((E.prod E') 0)) :=
    Dense.mono Submodule.subset_span ((E.prod E').denseRange_inclK 0 1)
  refine ContinuousLinearMap.ext_on hd ?_
  rintro _ ⟨y, rfl⟩
  exact congrArg (fun L : (E.prod E') 1 →L[ℝ] (F.prod F') 0 => L y) h

variable {C : Set (E 0)} {C' : Set (E' 0)}

/-- The product `r × r' : U × U' → U × U'` of sc-smooth retractions. -/
def ScRetraction.prod (R : ScRetraction E C) (R' : ScRetraction E' C') :
    ScRetraction (E.prod E') (C ×ˢ C') where
  U := R.U ×ˢ R'.U
  toFun := Prod.map R R'
  relOpen := R.relOpen.prod R'.relOpen
  mapsTo _ hp := ⟨R.mapsTo hp.1, R'.mapsTo hp.2⟩
  isScSmooth := IsScSmooth.prodMap R.isScDomain R'.isScDomain (R.relOpen.prod R'.relOpen).isScDomain
    R.isScSmooth R'.isScSmooth
  idem _ hp := Prod.ext (R.idem _ hp.1) (R'.idem _ hp.2)

lemma ScRetraction.prod_apply (R : ScRetraction E C) (R' : ScRetraction E' C') (p : (E.prod E') 0) :
    R.prod R' p = (R p.1, R' p.2) := rfl

lemma ScRetraction.prod_retract (R : ScRetraction E C) (R' : ScRetraction E' C') :
    (R.prod R').retract = R.retract ×ˢ R'.retract := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨⟨q.1, hq.1, rfl⟩, ⟨q.2, hq.2, rfl⟩⟩
  · rintro ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
    exact ⟨(a, b), ⟨ha, hb⟩, Prod.ext h1 h2⟩

theorem IsScRetract.prod {O : Set (E 0)} {O' : Set (E' 0)} (hO : IsScRetract E C O)
    (hO' : IsScRetract E' C' O') : IsScRetract (E.prod E') (C ×ˢ C') (O ×ˢ O') := by
  obtain ⟨R, rfl⟩ := hO
  obtain ⟨R', rfl⟩ := hO'
  exact ⟨R.prod R', R.prod_retract R'⟩

/-- Products of sc-smooth maps between retracts are sc-smooth. -/
theorem IsScSmoothRetractMap.prodMap {D : Set (F 0)} {D' : Set (F' 0)} {O : Set (E 0)}
    {O' : Set (E' 0)} {O₂ : Set (F 0)} {O₂' : Set (F' 0)} {f : E 0 → F 0} {f' : E' 0 → F' 0}
    (hO : IsScRetract E C O) (hO' : IsScRetract E' C' O')
    (h : IsScSmoothRetractMap E C O F D O₂ f) (h' : IsScSmoothRetractMap E' C' O' F' D' O₂' f') :
    IsScSmoothRetractMap (E.prod E') (C ×ˢ C') (O ×ˢ O') (F.prod F') (D ×ˢ D') (O₂ ×ˢ O₂')
      (Prod.map f f') := by
  obtain ⟨R, hR⟩ := id hO
  obtain ⟨R', hR'⟩ := id hO'
  refine (isScSmoothRetractMap_iff_exists (hO.prod hO')).2
    ⟨fun p hp => ⟨h.mapsTo hp.1, h'.mapsTo hp.2⟩, R.prod R', by rw [R.prod_retract, hR, hR'], ?_⟩
  exact IsScSmooth.prodMap R.isScDomain R'.isScDomain (R.relOpen.prod R'.relOpen).isScDomain
    (h.comp_isScSmooth R hR) (h'.comp_isScSmooth R' hR')

end ProdMaps

/-! ### Products of sc-splittings and of tame retractions -/

section ProdTame

variable {E E' : ScBanach}

lemma levelSub_prod (A : Submodule ℝ (E 0)) (A' : Submodule ℝ (E' 0)) (m : ℕ) :
    (E.prod E').levelSub (A.prod A') m = (E.levelSub A m).prod (E'.levelSub A' m) := by
  ext p
  rw [ScBanach.mem_levelSub, ScBanach.prod_toBase, Submodule.mem_prod, Submodule.mem_prod]
  rfl

theorem IsScSubspace.prod {A : Submodule ℝ (E 0)} {A' : Submodule ℝ (E' 0)}
    (h : E.IsScSubspace A) (h' : E'.IsScSubspace A') : (E.prod E').IsScSubspace (A.prod A') := by
  refine ⟨by rw [Submodule.prod_coe]; exact h.1.prod h'.1, fun m => ?_⟩
  rw [levelSub_prod, Submodule.prod_coe, ScBanach.prod_smoothLvl, prod_inter_prod,
    closure_prod_eq]
  exact prod_mono (h.2 m) (h'.2 m)

theorem IsScSplitting.prod {A B : Submodule ℝ (E 0)} {A' B' : Submodule ℝ (E' 0)}
    (h : E.IsScSplitting A B) (h' : E'.IsScSplitting A' B') :
    (E.prod E').IsScSplitting (A.prod A') (B.prod B') := by
  refine ⟨IsScSubspace.prod h.1 h'.1, IsScSubspace.prod h.2.1 h'.2.1, fun m => ?_⟩
  rw [levelSub_prod, levelSub_prod]
  have h1 := h.2.2 m
  have h2 := h'.2.2 m
  refine isCompl_iff.2 ⟨disjoint_iff.2 ?_, codisjoint_iff.2 ?_⟩
  · rw [Submodule.prod_inf_prod, h1.inf_eq_bot, h2.inf_eq_bot, Submodule.prod_bot]
  · rw [Submodule.prod_sup_prod, h1.sup_eq_top, h2.sup_eq_top, Submodule.prod_top]

variable {n n' : ℕ} {W W' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}

/-- **Exposition Lemma 4.D**: the product of tame retractions is tame (for the product
presentation): condition (1) is the additivity of the index, and for (2)
`T_{(x, x')}(O × O') = T_xO ⊕ T_{x'}O'` has the sc-complement `A ⊕ A' ⊆ E_x ⊕ E'_{x'}`. -/
theorem ScRetraction.IsTameWith.prod {R : ScRetraction E C} {R' : ScRetraction E' C'}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)}
    {T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W')} (hT : C = T 0 ⁻¹' quadrant n W 0)
    (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0) (hR : R.IsTameWith T) (hR' : R'.IsTameWith T') :
    (R.prod R').IsTameWith (prodPresentation T T') := by
  have hTT' := prod_eq_prodPresentation T T' hT hT'
  refine ⟨fun p hp => ?_, fun x hx hs => ?_⟩
  · have hpC : p ∈ C ×ˢ C' := (R.prod R').U_subset_C hp
    have hRpC : R.prod R' p ∈ C ×ˢ C' := (R.prod R').U_subset_C ((R.prod R').mapsTo hp)
    rw [degIndex_eq _ hTT' hRpC, degIndex_eq _ hTT' hpC, degIndexWith_prodPresentation,
      degIndexWith_prodPresentation]
    have hRp1 : R p.1 ∈ C := hRpC.1
    have hRp2 : R' p.2 ∈ C' := hRpC.2
    change degIndexWith T (R p.1) + degIndexWith T' (R' p.2) = _
    rw [← degIndex_eq T hT hRp1, ← degIndex_eq T' hT' hRp2, ← degIndex_eq T hT hpC.1,
      ← degIndex_eq T' hT' hpC.2, hR.degIndex_apply _ hp.1, hR'.degIndex_apply _ hp.2]
  · have hx' : E.toBase 1 x.1 ∈ R.retract ∧ E'.toBase 1 x.2 ∈ R'.retract := by
      have : (E.prod E').toBase 1 x ∈ (R.prod R').retract := hx
      rw [R.prod_retract, ScBanach.prod_toBase] at this
      exact this
    have hs' : x.1 ∈ E.smoothLvl 1 ∧ x.2 ∈ E'.smoothLvl 1 := by
      rw [ScBanach.prod_smoothLvl] at hs; exact hs
    obtain ⟨A, hA, hAE⟩ := hR.exists_complement x.1 hx'.1 hs'.1
    obtain ⟨A', hA', hA'E⟩ := hR'.exists_complement x.2 hx'.2 hs'.2
    refine ⟨A.prod A', ?_, ?_⟩
    · have hD := scDeriv_prodMap R.relOpen R'.relOpen R.isScSmooth R'.isScSmooth
        ((R.prod R').lvlSet_retract_subset 1 hx)
      change (E.prod E').IsScSplitting (LinearMap.range
        (scDeriv (E := E.prod E') (F := E.prod E') (R.U ×ˢ R'.U) (Prod.map R R') x :
          (E.prod E') 0 →ₗ[ℝ] (E.prod E') 0)) (A.prod A')
      rw [hD, ContinuousLinearMap.coe_prodMap, LinearMap.range_prodMap]
      exact IsScSplitting.prod hA hA'
    · rw [ScBanach.prod_toBase, minimalSubspaceWith_prodPresentation]
      exact Submodule.prod_mono hAE hA'E

end ProdTame

/-! ### Product charts and product M-polyfolds (exposition Lemma 4.D) -/

/-- The product `(O × O', C × C', E ⊕ E')` of local models. -/
def LocalModel.prod (M M' : LocalModel) : LocalModel :=
  ⟨M.E.prod M'.E, M.C ×ˢ M'.C, M.O ×ˢ M'.O, M.isScRetract.prod M'.isScRetract⟩

namespace MChart

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The product chart `(V × V', φ × φ', (O × O', C × C', E ⊕ E'))`. -/
def prod (φ : MChart X) (ψ : MChart Y) : MChart (X × Y) where
  model := φ.model.prod ψ.model
  toPartialEquiv := φ.toPartialEquiv.prod ψ.toPartialEquiv
  isOpen_source := φ.isOpen_source.prod ψ.isOpen_source
  target_eq := by
    rw [PartialEquiv.prod_target, φ.target_eq, ψ.target_eq]; rfl
  continuousOn_toFun := φ.continuousOn_toFun.prodMap ψ.continuousOn_toFun
  continuousOn_invFun := φ.continuousOn_invFun.prodMap ψ.continuousOn_invFun

variable (φ φ' : MChart X) (ψ ψ' : MChart Y)

lemma prod_apply (p : X × Y) : φ.prod ψ p = (φ p.1, ψ p.2) := rfl

lemma prod_source : (φ.prod ψ).source = φ.source ×ˢ ψ.source := rfl

lemma prod_symm_apply (z : (φ.prod ψ).model.E 0) : (φ.prod ψ).symm z = (φ.symm z.1, ψ.symm z.2) :=
  rfl

lemma prod_model_O : (φ.prod ψ).model.O = φ.model.O ×ˢ ψ.model.O := rfl

lemma overlap_prod : (φ.prod ψ).overlap (φ'.prod ψ') = φ.overlap φ' ×ˢ ψ.overlap ψ' := by
  change (fun p : X × Y => (φ p.1, ψ p.2)) '' ((φ.source ×ˢ ψ.source) ∩ (φ'.source ×ˢ ψ'.source))
    = _
  rw [prod_inter_prod, ← prod_image_image_eq]; rfl

variable {φ φ' ψ ψ'} in
/-- Products of compatible charts are compatible (their transition maps are products). -/
theorem Compatible.prod (h : φ.Compatible φ') (h' : ψ.Compatible ψ') :
    (φ.prod ψ).Compatible (φ'.prod ψ') := by
  constructor
  · rw [overlap_prod, overlap_prod]
    exact IsScSmoothRetractMap.prodMap (φ.isScRetract_overlap φ') (ψ.isScRetract_overlap ψ') h.1
      h'.1
  · rw [overlap_prod, overlap_prod]
    exact IsScSmoothRetractMap.prodMap (φ'.isScRetract_overlap φ) (ψ'.isScRetract_overlap ψ) h.2
      h'.2

end MChart

namespace MPolyfold

universe u v w

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : MPolyfold X) (Q : MPolyfold Y)

include P Q in
/-- `X × Y` is paracompact: it is metrizable (Theorem 2.16 for `X` and `Y`). -/
theorem paracompactSpace_prod : ParacompactSpace (X × Y) := by
  have := P.metrizableSpace
  have := Q.metrizableSpace
  exact paracompactSpace_of_metrizableSpace (X × Y)

/-- **Exposition Lemma 4.D**: the product M-polyfold `X × Y`, with the product charts. -/
def prod [ParacompactSpace (X × Y)] : MPolyfold (X × Y) where
  atlas :=
    { charts := {χ | ∃ φ ∈ P.atlas.charts, ∃ ψ ∈ Q.atlas.charts, χ = φ.prod ψ}
      compatible := by
        rintro _ ⟨φ, hφ, ψ, hψ, rfl⟩ _ ⟨φ', hφ', ψ', hψ', rfl⟩
        exact (P.atlas.compatible φ hφ φ' hφ').prod (Q.atlas.compatible ψ hψ ψ' hψ')
      cover := fun p => by
        obtain ⟨φ, hφ, hx⟩ := P.atlas.cover p.1
        obtain ⟨ψ, hψ, hy⟩ := Q.atlas.cover p.2
        exact ⟨φ.prod ψ, ⟨φ, hφ, ψ, hψ, rfl⟩, hx, hy⟩ }

variable {P Q}

theorem IsChart.prod [ParacompactSpace (X × Y)] {φ : MChart X} {ψ : MChart Y} (hφ : P.IsChart φ)
    (hψ : Q.IsChart ψ) : (P.prod Q).IsChart (φ.prod ψ) := by
  rintro _ ⟨φ', hφ', ψ', hψ', rfl⟩
  exact (hφ φ' hφ').prod (hψ ψ' hψ')

omit [T2Space X] [ParacompactSpace X] [T2Space Y] [ParacompactSpace Y] in
lemma chartDegIndex_prod (φ : MChart X) (ψ : MChart Y) {x : X} {y : Y} (hx : x ∈ φ.source)
    (hy : y ∈ ψ.source) :
    chartDegIndex (φ.prod ψ) (x, y) = chartDegIndex φ x + chartDegIndex ψ y :=
  degIndex_prod φ.model.isPartialQuadrant ψ.model.isPartialQuadrant (φ.apply_mem_C hx)
    (ψ.apply_mem_C hy)

variable (P Q)

/-- **Exposition Lemma 4.D**: `d_{X × Y}(x, y) ≤ d_X(x) + d_Y(y)`. -/
theorem degIndex_prod_le [ParacompactSpace (X × Y)] (x : X) (y : Y) :
    (P.prod Q).degIndex (x, y) ≤ P.degIndex x + Q.degIndex y := by
  obtain ⟨φ, hφ, hx, hdx⟩ := P.exists_isChart_degIndex_eq x
  obtain ⟨ψ, hψ, hy, hdy⟩ := Q.exists_isChart_degIndex_eq y
  rw [hdx, hdy, ← chartDegIndex_prod φ ψ hx hy]
  exact (P.prod Q).degIndex_le (hφ.prod hψ) ⟨hx, hy⟩

/-- **Exposition Lemma 4.D**, the tame case: if `X` and `Y` are tame, so is `X × Y`, and
`d_{X × Y}(x, y) = d_X(x) + d_Y(y)`. -/
theorem isTame_prod [ParacompactSpace (X × Y)] (hP : P.IsTame) (hQ : Q.IsTame) :
    (P.prod Q).IsTame ∧ ∀ x y, (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y := by
  have key : ∀ (x : X) (y : Y), ∃ χ : MChart (X × Y), (P.prod Q).IsChart χ ∧ (x, y) ∈ χ.source ∧
      IsTameRetract χ.model.E χ.model.C χ.model.O ∧
      (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y := by
    intro x y
    obtain ⟨φ, hφ, hx, R, hRO, hRt⟩ := IsTame.exists_chart P hP x
    obtain ⟨ψ, hψ, hy, R', hR'O, hR't⟩ := IsTame.exists_chart Q hQ y
    obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
    obtain ⟨n', W', T', hT'⟩ := ψ.model.isPartialQuadrant
    have hR := hRt n W T hT
    have hR' := hR't n' W' T' hT'
    have hTT' := prod_eq_prodPresentation T T' hT hT'
    have htame := ScRetraction.IsTameWith.prod hT hT' hR hR'
    have hret : (R.prod R').retract = (φ.prod ψ).model.O := by
      rw [R.prod_retract, hRO, hR'O]; rfl
    refine ⟨φ.prod ψ, hφ.prod hψ, ⟨hx, hy⟩, ⟨R.prod R', hret, htame.isTame hTT'⟩, ?_⟩
    rw [(P.prod Q).degIndex_eq_chartDegIndex_of_isTameWith (hφ.prod hψ) (R.prod R') hret hTT'
      htame ⟨hx, hy⟩, chartDegIndex_prod φ ψ hx hy,
      P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR hx,
      Q.degIndex_eq_chartDegIndex_of_isTameWith hψ R' hR'O hT' hR' hy]
  refine ⟨isTame_of_forall_exists_chart _ fun p => ?_, fun x y => (key x y).choose_spec.2.2.2⟩
  obtain ⟨χ, h1, h2, h3, -⟩ := key p.1 p.2
  exact ⟨χ, h1, h2, h3⟩

/-! ### Sc-smooth maps into and out of products -/

/-- The projection `X × Y → X` is sc-smooth. -/
theorem isScSmoothMap_fst [ParacompactSpace (X × Y)] : (P.prod Q).IsScSmoothMap P Prod.fst := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ continuous_fst.continuousOn fun p _ => ?_
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source p.1
  obtain ⟨ψ, hψ, hy⟩ := Q.exists_isChart_mem_source p.2
  refine ⟨φ.prod ψ, φ, (φ.prod ψ).source, hφ.prod hψ, hφ, (φ.prod ψ).isOpen_source, ⟨hx, hy⟩,
    fun q hq => ⟨mem_univ _, hq⟩, fun q hq => hq.1, ?_⟩
  rw [(φ.prod ψ).image_source]
  refine ((ScBanach.prodFstOp φ.model.E ψ.model.E).isScSmoothRetractMap
    (φ.prod ψ).model.isScRetract fun z hz => hz.1).congr fun z hz => ?_
  change z.1 = φ (φ.symm z.1)
  rw [φ.apply_symm_apply hz.1]

/-- The projection `X × Y → Y` is sc-smooth. -/
theorem isScSmoothMap_snd [ParacompactSpace (X × Y)] : (P.prod Q).IsScSmoothMap Q Prod.snd := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ continuous_snd.continuousOn fun p _ => ?_
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source p.1
  obtain ⟨ψ, hψ, hy⟩ := Q.exists_isChart_mem_source p.2
  refine ⟨φ.prod ψ, ψ, (φ.prod ψ).source, hφ.prod hψ, hψ, (φ.prod ψ).isOpen_source, ⟨hx, hy⟩,
    fun q hq => ⟨mem_univ _, hq⟩, fun q hq => hq.2, ?_⟩
  rw [(φ.prod ψ).image_source]
  refine ((ScBanach.prodSndOp φ.model.E ψ.model.E).isScSmoothRetractMap
    (φ.prod ψ).model.isScRetract fun z hz => hz.2).congr fun z hz => ?_
  change z.2 = ψ (ψ.symm z.2)
  rw [ψ.apply_symm_apply hz.2]

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

variable {P Q} in
/-- The pairing `z ↦ (f(z), g(z))` of sc-smooth maps is sc-smooth into `X × Y`. -/
theorem IsScSmoothOn.prodMk [ParacompactSpace (X × Y)] {f : Z → X} {g : Z → Y} {U : Set Z}
    (hf : S.IsScSmoothOn P f U) (hg : S.IsScSmoothOn Q g U) :
    S.IsScSmoothOn (P.prod Q) (fun z => (f z, g z)) U := by
  refine IsScSmoothOn.of_exists_charts hf.isOpen (hf.continuousOn.prodMk hg.continuousOn)
    fun z hz => ?_
  obtain ⟨φ, hφ, hzφ⟩ := S.exists_isChart_mem_source z
  obtain ⟨ψ₁, hψ₁, h1⟩ := P.exists_isChart_mem_source (f z)
  obtain ⟨ψ₂, hψ₂, h2⟩ := Q.exists_isChart_mem_source (g z)
  set V₁ := (U ∩ φ.source) ∩ f ⁻¹' ψ₁.source with hV₁
  have hV₁o : IsOpen V₁ := (hf.continuousOn.mono inter_subset_left).isOpen_inter_preimage
    (hf.isOpen.inter φ.isOpen_source) ψ₁.isOpen_source
  set V := V₁ ∩ g ⁻¹' ψ₂.source with hV
  have hVo : IsOpen V := (hg.continuousOn.mono fun x hx => hx.1.1).isOpen_inter_preimage hV₁o
    ψ₂.isOpen_source
  have hVU : V ⊆ U ∩ φ.source := fun x hx => hx.1.1
  have k1 := hf.smooth φ ψ₁ hφ hψ₁ V hVo hVU fun x hx => hx.1.2
  have k2 := hg.smooth φ ψ₂ hφ hψ₂ V hVo hVU fun x hx => hx.2
  refine ⟨φ, ψ₁.prod ψ₂, V, hφ, hψ₁.prod hψ₂, hVo, ⟨⟨⟨hz, hzφ⟩, h1⟩, h2⟩, hVU,
    fun x hx => ⟨hx.1.2, hx.2⟩, ?_⟩
  exact IsScSmoothRetractMap.scPair k1 k2 fun w hw => ⟨k1.mapsTo hw, k2.mapsTo hw⟩

end MPolyfold

/-! ### Fibred products (Proposition 2.46) -/

namespace MPolyfold

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w} [TopologicalSpace X] [T2Space X]
  [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] [TopologicalSpace Z]
  [T2Space Z] [ParacompactSpace Z] (P : MPolyfold X) (Q : MPolyfold Y) (S : MPolyfold Z)

/-- `f : X → Z` is a **local sc-diffeomorphism**: every `x` has an open neighbourhood `U` such
that `f|_U` is an sc-diffeomorphism onto an open subset of `Z`. -/
def IsLocalScDiffeo (f : X → Z) : Prop :=
  ∀ x, ∃ (U : Set X) (V : Set Z) (h : Z → X), x ∈ U ∧ P.IsScDiffeoOn S f h U V

variable {P Q S}

lemma IsLocalScDiffeo.continuous {f : X → Z} (hf : P.IsLocalScDiffeo S f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => by
    obtain ⟨U, V, h, hx, hd⟩ := hf x
    exact hd.isScSmoothOn.continuousOn.continuousAt (hd.isScSmoothOn.isOpen.mem_nhds hx)

/-- The fibred product `X ₓ×_g Y = {(x, y) | f(x) = g(y)}`. -/
def fibredProduct (f : X → Z) (g : Y → Z) : Set (X × Y) := {p | f p.1 = g p.2}

omit [T2Space X] [ParacompactSpace X] [T2Space Y] [ParacompactSpace Y] [ParacompactSpace Z] in
lemma isClosed_fibredProduct {f : X → Z} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    IsClosed (fibredProduct f g) :=
  isClosed_eq (hf.comp continuous_fst) (hg.comp continuous_snd)

variable [ParacompactSpace (X × Y)] {f : X → Z} {g : Y → Z}

/-- The retraction `R(x', y') = ((f|_U)⁻¹(g(y')), y')` of `U × g⁻¹(V)` onto the fibred product, for
an sc-diffeomorphism `f|_U : U → V` (the proof of Proposition 2.46). -/
def fibredSubDataL {h : Z → X} {U : Set X} {V : Set Z} (hd : P.IsScDiffeoOn S f h U V)
    (hg : Q.IsScSmoothMap S g) : (P.prod Q).SubData (fibredProduct f g) where
  V := U ×ˢ (g ⁻¹' V)
  r p := (h (g p.2), p.2)
  isOpen := hd.isScSmoothOn.isOpen.prod (hd.isScSmoothOn_inv.isOpen.preimage
    (continuousOn_univ.1 hg.continuousOn))
  mapsTo p hp := ⟨hd.mapsTo_inv hp.2, hp.2⟩
  isScSmoothOn := by
    have hVo : IsOpen (U ×ˢ (g ⁻¹' V)) := hd.isScSmoothOn.isOpen.prod
      (hd.isScSmoothOn_inv.isOpen.preimage (continuousOn_univ.1 hg.continuousOn))
    have hsnd : (P.prod Q).IsScSmoothOn Q Prod.snd (U ×ˢ (g ⁻¹' V)) :=
      (isScSmoothMap_snd P Q).mono hVo (subset_univ _)
    have hgs : (P.prod Q).IsScSmoothOn S (g ∘ Prod.snd) (U ×ˢ (g ⁻¹' V)) :=
      IsScSmoothOn.comp hg hsnd (mapsTo_univ _ _)
    have hhgs : (P.prod Q).IsScSmoothOn P (h ∘ (g ∘ Prod.snd)) (U ×ˢ (g ⁻¹' V)) :=
      IsScSmoothOn.comp hd.isScSmoothOn_inv hgs fun p hp => hp.2
    exact IsScSmoothOn.prodMk hhgs hsnd
  idem _ _ := rfl
  image := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(hd.right_inv _ hq.2).trans rfl, hd.mapsTo_inv hq.2, hq.2⟩
    · rintro ⟨hpA, hpV⟩
      refine ⟨p, hpV, Prod.ext ?_ rfl⟩
      change h (g p.2) = p.1
      rw [← show f p.1 = g p.2 from hpA, hd.left_inv _ hpV.1]

/-- The retraction `R(x', y') = (x', (g|_U)⁻¹(f(x')))` of `f⁻¹(V) × U` onto the fibred product, for
an sc-diffeomorphism `g|_U : U → V`. -/
def fibredSubDataR {k : Z → Y} {U : Set Y} {V : Set Z} (hd : Q.IsScDiffeoOn S g k U V)
    (hf : P.IsScSmoothMap S f) : (P.prod Q).SubData (fibredProduct f g) where
  V := (f ⁻¹' V) ×ˢ U
  r p := (p.1, k (f p.1))
  isOpen := (hd.isScSmoothOn_inv.isOpen.preimage
    (continuousOn_univ.1 hf.continuousOn)).prod hd.isScSmoothOn.isOpen
  mapsTo p hp := ⟨hp.1, hd.mapsTo_inv hp.1⟩
  isScSmoothOn := by
    have hVo : IsOpen ((f ⁻¹' V) ×ˢ U) := (hd.isScSmoothOn_inv.isOpen.preimage
      (continuousOn_univ.1 hf.continuousOn)).prod hd.isScSmoothOn.isOpen
    have hfst : (P.prod Q).IsScSmoothOn P Prod.fst ((f ⁻¹' V) ×ˢ U) :=
      (isScSmoothMap_fst P Q).mono hVo (subset_univ _)
    have hfs : (P.prod Q).IsScSmoothOn S (f ∘ Prod.fst) ((f ⁻¹' V) ×ˢ U) :=
      IsScSmoothOn.comp hf hfst (mapsTo_univ _ _)
    have hkfs : (P.prod Q).IsScSmoothOn Q (k ∘ (f ∘ Prod.fst)) ((f ⁻¹' V) ×ˢ U) :=
      IsScSmoothOn.comp hd.isScSmoothOn_inv hfs fun p hp => hp.1
    exact IsScSmoothOn.prodMk hfst hkfs
  idem _ _ := rfl
  image := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(hd.right_inv _ hq.1).symm, hq.1, hd.mapsTo_inv hq.1⟩
    · rintro ⟨hpA, hpV⟩
      refine ⟨p, hpV, Prod.ext rfl ?_⟩
      change k (f p.1) = p.2
      rw [show f p.1 = g p.2 from hpA, hd.left_inv _ hpV.2]

/-- **Proposition 2.46**, first statement: for a local sc-diffeomorphism `f : X → Z` and an
sc-smooth `g : Y → Z`, the fibred product `X ₓ×_g Y` is a sub-M-polyfold of `X × Y`. -/
theorem isSubMPolyfold_fibredProduct (hf : P.IsLocalScDiffeo S f) (hg : Q.IsScSmoothMap S g) :
    (P.prod Q).IsSubMPolyfold (fibredProduct f g) := by
  intro a _
  obtain ⟨U, V, h, hx, hd⟩ := hf a.1
  have ha : a ∈ (fibredSubDataL hd hg).V := ⟨hx, by
    change g a.2 ∈ V
    rw [← show f a.1 = g a.2 from ‹a ∈ fibredProduct f g›]; exact hd.mapsTo hx⟩
  set d := fibredSubDataL hd hg
  exact ⟨d.V, d.isOpen, ha, d.r, d.mapsTo, d.isScSmoothOn, d.idem, d.image⟩

/-- The symmetric statement: for a local sc-diffeomorphism `g`, the fibred product is a
sub-M-polyfold. -/
theorem isSubMPolyfold_fibredProduct' (hf : P.IsScSmoothMap S f) (hg : Q.IsLocalScDiffeo S g) :
    (P.prod Q).IsSubMPolyfold (fibredProduct f g) := by
  intro a haA
  obtain ⟨U, V, k, hy, hd⟩ := hg a.2
  have ha : a ∈ (fibredSubDataR hd hf).V := ⟨by
    change f a.1 ∈ V
    rw [show f a.1 = g a.2 from haA]; exact hd.mapsTo hy, hy⟩
  set d := fibredSubDataR hd hf
  exact ⟨d.V, d.isOpen, ha, d.r, d.mapsTo, d.isScSmoothOn, d.idem, d.image⟩

omit [ParacompactSpace (X × Y)] in
/-- A local sc-diffeomorphism is sc-smooth. -/
theorem IsLocalScDiffeo.isScSmoothMap (hf : P.IsLocalScDiffeo S f) : P.IsScSmoothMap S f := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ hf.continuous.continuousOn fun x _ => ?_
  obtain ⟨U, V, h, hx, hd⟩ := hf x
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  obtain ⟨ψ, hψ, hfx⟩ := S.exists_isChart_mem_source (f x)
  set V₀ := (U ∩ φ.source) ∩ f ⁻¹' ψ.source with hV₀
  have hV₀o : IsOpen V₀ :=
    (hd.isScSmoothOn.continuousOn.mono inter_subset_left).isOpen_inter_preimage
      (hd.isScSmoothOn.isOpen.inter φ.isOpen_source) ψ.isOpen_source
  exact ⟨φ, ψ, V₀, hφ, hψ, hV₀o, ⟨⟨hx, hxφ⟩, hfx⟩, fun y hy => ⟨mem_univ _, hy.1.2⟩,
    fun y hy => hy.2, hd.isScSmoothOn.smooth φ ψ hφ hψ V₀ hV₀o (fun y hy => hy.1) fun y hy => hy.2⟩

section Diffeo

variable [ParacompactSpace (fibredProduct f g)] (hA : (P.prod Q).IsSubMPolyfold (fibredProduct f g))

/-- Near a point of the fibred product, `π₂ : (x, y) ↦ y` is an sc-diffeomorphism onto an open
subset of `Y`, with inverse `y ↦ ((f|_U)⁻¹(g(y)), y)` (the proof of Proposition 2.46). -/
theorem isScDiffeoOn_snd_fibredProduct {h : Z → X} {U : Set X} {V : Set Z}
    (hd : P.IsScDiffeoOn S f h U V) (hg : Q.IsScSmoothMap S g) (a₀ : fibredProduct f g) :
    (subPolyfold hA).IsScDiffeoOn Q (fun a => (a : X × Y).2)
      (fun y => (fibredSubDataL hd hg).retractInto a₀ (h (g y), y))
      (Subtype.val ⁻¹' (U ×ˢ (g ⁻¹' V))) (g ⁻¹' V) := by
  set d := fibredSubDataL hd hg with hddef
  have hVY : IsOpen (g ⁻¹' V) :=
    hd.isScSmoothOn_inv.isOpen.preimage (continuousOn_univ.1 hg.continuousOn)
  have hdV : ∀ y ∈ g ⁻¹' V, (h (g y), y) ∈ d.V := fun y hy => ⟨hd.mapsTo_inv hy, hy⟩
  have hval : ∀ y ∈ g ⁻¹' V, ((d.retractInto a₀ (h (g y), y) : fibredProduct f g) : X × Y) =
      (h (g y), y) := fun y hy => d.retractInto_val a₀ (hdV y hy)
  have hUo : IsOpen (Subtype.val ⁻¹' d.V : Set (fibredProduct f g)) :=
    d.isOpen.preimage continuous_subtype_val
  refine ⟨?_, ?_, fun a ha => ha.2, fun y hy => ?_, fun a ha => ?_, fun y hy => ?_⟩
  · exact IsScSmoothOn.comp (isScSmoothMap_snd P Q)
      ((subPolyfold_inclusion_isScSmooth hA).mono hUo (subset_univ _)) (mapsTo_univ _ _)
  · have hpair : Q.IsScSmoothOn (P.prod Q) (fun y => (h (g y), y)) (g ⁻¹' V) :=
      IsScSmoothOn.prodMk (IsScSmoothOn.comp hd.isScSmoothOn_inv (hg.mono hVY (subset_univ _))
        fun y hy => hy) (isScSmoothMap_id.mono hVY (subset_univ _))
    exact IsScSmoothOn.comp (subPolyfold_retraction_isScSmooth hA d a₀) hpair hdV
  · change ((d.retractInto a₀ (h (g y), y) : fibredProduct f g) : X × Y) ∈ d.V
    rw [hval y hy]; exact hdV y hy
  · apply Subtype.ext
    change ((d.retractInto a₀ (h (g (a : X × Y).2), (a : X × Y).2) : fibredProduct f g) : X × Y) =
      (a : X × Y)
    rw [hval _ ha.2]
    refine Prod.ext ?_ rfl
    change h (g (a : X × Y).2) = (a : X × Y).1
    rw [← show f (a : X × Y).1 = g (a : X × Y).2 from a.2, hd.left_inv _ ha.1]
  · rw [hval y hy]

/-- Near a point of the fibred product, `π₁ : (x, y) ↦ x` is an sc-diffeomorphism onto an open
subset of `X` when `g` is a local sc-diffeomorphism. -/
theorem isScDiffeoOn_fst_fibredProduct {k : Z → Y} {U : Set Y} {V : Set Z}
    (hd : Q.IsScDiffeoOn S g k U V) (hf : P.IsScSmoothMap S f) (a₀ : fibredProduct f g) :
    (subPolyfold hA).IsScDiffeoOn P (fun a => (a : X × Y).1)
      (fun x => (fibredSubDataR hd hf).retractInto a₀ (x, k (f x)))
      (Subtype.val ⁻¹' ((f ⁻¹' V) ×ˢ U)) (f ⁻¹' V) := by
  set d := fibredSubDataR hd hf with hddef
  have hVX : IsOpen (f ⁻¹' V) :=
    hd.isScSmoothOn_inv.isOpen.preimage (continuousOn_univ.1 hf.continuousOn)
  have hdV : ∀ x ∈ f ⁻¹' V, (x, k (f x)) ∈ d.V := fun x hx => ⟨hx, hd.mapsTo_inv hx⟩
  have hval : ∀ x ∈ f ⁻¹' V, ((d.retractInto a₀ (x, k (f x)) : fibredProduct f g) : X × Y) =
      (x, k (f x)) := fun x hx => d.retractInto_val a₀ (hdV x hx)
  have hUo : IsOpen (Subtype.val ⁻¹' d.V : Set (fibredProduct f g)) :=
    d.isOpen.preimage continuous_subtype_val
  refine ⟨?_, ?_, fun a ha => ha.1, fun x hx => ?_, fun a ha => ?_, fun x hx => ?_⟩
  · exact IsScSmoothOn.comp (isScSmoothMap_fst P Q)
      ((subPolyfold_inclusion_isScSmooth hA).mono hUo (subset_univ _)) (mapsTo_univ _ _)
  · have hpair : P.IsScSmoothOn (P.prod Q) (fun x => (x, k (f x))) (f ⁻¹' V) :=
      IsScSmoothOn.prodMk (isScSmoothMap_id.mono hVX (subset_univ _))
        (IsScSmoothOn.comp hd.isScSmoothOn_inv (hf.mono hVX (subset_univ _)) fun x hx => hx)
    exact IsScSmoothOn.comp (subPolyfold_retraction_isScSmooth hA d a₀) hpair hdV
  · change ((d.retractInto a₀ (x, k (f x)) : fibredProduct f g) : X × Y) ∈ d.V
    rw [hval x hx]; exact hdV x hx
  · apply Subtype.ext
    change ((d.retractInto a₀ ((a : X × Y).1, k (f (a : X × Y).1)) : fibredProduct f g) :
      X × Y) = (a : X × Y)
    rw [hval _ ha.1]
    refine Prod.ext rfl ?_
    change k (f (a : X × Y).1) = (a : X × Y).2
    rw [show f (a : X × Y).1 = g (a : X × Y).2 from a.2, hd.left_inv _ ha.2]
  · rw [hval x hx]

/-- `d_{X ₓ×_g Y}(x, y) = d_Y(y)` when `f` is a local sc-diffeomorphism (Proposition 2.24 along
`π₂`). -/
theorem degIndex_fibredProduct_eq_snd (hf : P.IsLocalScDiffeo S f) (hg : Q.IsScSmoothMap S g)
    (a : fibredProduct f g) : (subPolyfold hA).degIndex a = Q.degIndex (a : X × Y).2 := by
  obtain ⟨U, V, h, hx, hd⟩ := hf (a : X × Y).1
  refine proposition_2_24 (isScDiffeoOn_snd_fibredProduct hA hd hg a) ⟨hx, ?_⟩
  change g (a : X × Y).2 ∈ V
  rw [← show f (a : X × Y).1 = g (a : X × Y).2 from a.2]; exact hd.mapsTo hx

/-- `d_{X ₓ×_g Y}(x, y) = d_X(x)` when `g` is a local sc-diffeomorphism. -/
theorem degIndex_fibredProduct_eq_fst (hf : P.IsScSmoothMap S f) (hg : Q.IsLocalScDiffeo S g)
    (a : fibredProduct f g) : (subPolyfold hA).degIndex a = P.degIndex (a : X × Y).1 := by
  obtain ⟨U, V, k, hy, hd⟩ := hg (a : X × Y).2
  refine proposition_2_24 (isScDiffeoOn_fst_fibredProduct hA hd hf a) ⟨?_, hy⟩
  change f (a : X × Y).1 ∈ V
  rw [show f (a : X × Y).1 = g (a : X × Y).2 from a.2]; exact hd.mapsTo hy

/-- If `Y` is tame, so is the fibred product (charts `ψ ∘ π₂` with tame charts `ψ` of `Y`). -/
theorem isTame_fibredProduct (hf : P.IsLocalScDiffeo S f) (hg : Q.IsScSmoothMap S g)
    (hQ : Q.IsTame) : (subPolyfold hA).IsTame := by
  refine isTame_of_forall_exists_chart _ fun a => ?_
  obtain ⟨U, V, h, hx, hd⟩ := hf (a : X × Y).1
  have hD := isScDiffeoOn_snd_fibredProduct hA hd hg a
  have haU : a ∈ (Subtype.val ⁻¹' (U ×ˢ (g ⁻¹' V)) : Set (fibredProduct f g)) := ⟨hx, by
    change g (a : X × Y).2 ∈ V
    rw [← show f (a : X × Y).1 = g (a : X × Y).2 from a.2]; exact hd.mapsTo hx⟩
  obtain ⟨ψ, hψ, hy, Rψ, hRψ, hRt⟩ := IsTame.exists_chart Q hQ (a : X × Y).2
  have hVY : IsOpen (g ⁻¹' V) :=
    hd.isScSmoothOn_inv.isOpen.preimage (continuousOn_univ.1 hg.continuousOn)
  obtain ⟨W', hW', heq⟩ := ψ.exists_isOpen_image_eq (s := g ⁻¹' V ∩ ψ.source) inter_subset_right
    (hVY.inter ψ.isOpen_source)
  refine ⟨transportChart hD ψ, transportChart_isChart hD hψ, ⟨haU, hy⟩, Rψ.restrict hW', ?_,
    fun n W T hT => (hRt n W T hT).restrict hW'⟩
  have h1 : (Rψ.restrict hW').retract = ψ '' (g ⁻¹' V ∩ ψ.source) := by
    rw [Rψ.restrict_retract, hRψ]; exact heq.symm
  exact h1

end Diffeo

/-- **Proposition 2.46**: let `f : X → Z` be a local sc-diffeomorphism and `g : Y → Z`
sc-smooth.  The fibred product `X ₓ×_g Y` is a sub-M-polyfold of `X × Y`;
`d_{X ₓ×_g Y}(x, y) = d_Y(y)`; and if `Y` is tame, so is `X ₓ×_g Y`.  (Paracompactness of the
fibred product: it is closed in the metrizable `X × Y`.) -/
theorem proposition_2_46 (hf : P.IsLocalScDiffeo S f) (hg : Q.IsScSmoothMap S g) :
    haveI : ParacompactSpace (fibredProduct f g) := paracompactSpace_of_isClosed
      (isClosed_fibredProduct hf.continuous (continuousOn_univ.1 hg.continuousOn))
    ∃ hA : (P.prod Q).IsSubMPolyfold (fibredProduct f g),
      (∀ a : fibredProduct f g, (subPolyfold hA).degIndex a = Q.degIndex (a : X × Y).2) ∧
      (Q.IsTame → (subPolyfold hA).IsTame) := by
  have : ParacompactSpace (fibredProduct f g) := paracompactSpace_of_isClosed
    (isClosed_fibredProduct hf.continuous (continuousOn_univ.1 hg.continuousOn))
  have hA := isSubMPolyfold_fibredProduct hf hg
  exact ⟨hA, degIndex_fibredProduct_eq_snd hA hf hg, isTame_fibredProduct hA hf hg⟩

/-- **Proposition 2.46**, last statement: if both `f` and `g` are local sc-diffeomorphisms, then
`d_{X ₓ×_g Y}(x, y) = d_X(x) = d_Y(y)`, and if moreover `X` and `Y` are tame,
`2 d_{X ₓ×_g Y}(x, y) = d_{X × Y}(x, y)` (`= d_X(x) + d_Y(y)`, Lemma 4.D). -/
theorem proposition_2_46_of_isLocalScDiffeo (hf : P.IsLocalScDiffeo S f)
    (hg : Q.IsLocalScDiffeo S g) :
    haveI : ParacompactSpace (fibredProduct f g) := paracompactSpace_of_isClosed
      (isClosed_fibredProduct hf.continuous hg.continuous)
    ∀ a : fibredProduct f g,
      (subPolyfold (isSubMPolyfold_fibredProduct hf hg.isScSmoothMap)).degIndex a =
          P.degIndex (a : X × Y).1 ∧
        (subPolyfold (isSubMPolyfold_fibredProduct hf hg.isScSmoothMap)).degIndex a =
          Q.degIndex (a : X × Y).2 ∧
        (P.IsTame → Q.IsTame →
          2 * (subPolyfold (isSubMPolyfold_fibredProduct hf hg.isScSmoothMap)).degIndex a =
            (P.prod Q).degIndex (a : X × Y)) := by
  have : ParacompactSpace (fibredProduct f g) := paracompactSpace_of_isClosed
    (isClosed_fibredProduct hf.continuous hg.continuous)
  intro a
  have hA := isSubMPolyfold_fibredProduct hf hg.isScSmoothMap
  have h1 := degIndex_fibredProduct_eq_fst hA hf.isScSmoothMap hg a
  have h2 := degIndex_fibredProduct_eq_snd hA hf hg.isScSmoothMap a
  refine ⟨h1, h2, fun hP hQ => ?_⟩
  rw [(isTame_prod P Q hP hQ).2 (a : X × Y).1 (a : X × Y).2]
  change 2 * (subPolyfold hA).degIndex a = _
  omega

end MPolyfold

end Polyfold
