import Polyfold.Chapter4.Families

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §4.3, **Theorem 4.3.1**
(p. 193; preprint: Theorem 4.23, p. 165): **the chart independence of stratified regularity**.
Closes gap G.36 (Findings, Chapter 4, items 102, 108).

# Stratified regular values are intrinsic to `A`

## The text, paraphrased

The proof of Theorem 4.3.1 uses regular values of the maps `p_σ : A ∩ F_σ° → ℝᵐ`, the restrictions
of `P(λ, x) = λ` to the open strata of `A`; this is a notion intrinsic to `A` and its strata.

## What is formalized

* `IsStratRegularPoint` (`Families.lean`) states the condition in *some* product chart
  `(r ↦ r − a) × φ` of `ℝᵐ × X`, with some data of Definition 4.2.1, presentation and lift: the
  projection to `ℝᵐ` maps `T_zA ∩ (ℝᵐ × E_{z₂})` onto `ℝᵐ` (`StratRegCond`).
* `IsStratRegularPoint.stratRegCond`: the condition then holds in **every** such choice;
  `isStratRegularPoint_iff_forall`, `isStratRegularValue_iff_forall`: the chart-free forms.
* The transport argument (as for Definitions 4.2.5 and 4.2.10, row V4.39):
  `StratRegCond.transport` (a germ of sc-diffeomorphisms which is a translation in the
  `ℝᵐ`-factor carries the condition: its derivative maps `T_zQ` to `T_{F(z)}Q'`, `E_z` into
  `E'_{F(z)}` by the sign argument, and preserves the `ℝᵐ`-component, `scDeriv_fst_eq_of_fst_eq`),
  and `stratRegCond_chart_change` (the transition maps of product charts are `τ(w) =
  (w₁ + a − a', φ' ∘ φ⁻¹(w₂))`, `transition_rnChart_prod_fst`).

## What the text leaves implicit, and the choices made

* As `T_zA` and the reduced tangent space have no chart-free linear structure here (gap G.7),
  "intrinsic" is read as "independent of all choices in the product charts".  Only product charts
  `(r ↦ r − a) × φ` are used, as in the definition: they are the charts of `ℝᵐ × X`
  (`MPolyfold.prod`).
-/

open Set Function

noncomputable section

namespace Polyfold

section FstDeriv

variable {m : ℕ} {E E' E'' : ScBanach}

/-- If the first components of two sc¹ maps `f, g : U → ℝᵐ ⊕ E'` differ by a constant on a
relatively open `U`, the first components of their derivatives agree at every level-`1` point. -/
theorem scDeriv_fst_eq_of_fst_eq {C U : Set (((rnSc m).prod E) 0)}
    (hU : IsRelOpenInQuadrant ((rnSc m).prod E) C U)
    {f : ((rnSc m).prod E) 0 → ((rnSc m).prod E') 0}
    {g : ((rnSc m).prod E) 0 → ((rnSc m).prod E'') 0} (hf : IsSc1 U f) (hg : IsSc1 U g)
    (c : Fin m → ℝ) (hfg : ∀ u ∈ U, (f u).1 = (g u).1 + c) {z : ((rnSc m).prod E) 1}
    (hz : z ∈ ((rnSc m).prod E).lvlSet U 1) (v : ((rnSc m).prod E) 0) :
    (scDeriv U f z v).1 = (scDeriv U g z v).1 := by
  set L := ContinuousLinearMap.fst ℝ (Fin m → ℝ) (E' 0)
  have d₁ := L.hasFDerivAt.comp_hasFDerivWithinAt (x := z)
    (hf.isSc1With_scDeriv.hasFDerivWithinAt z hz)
  have d₂ := ((ContinuousLinearMap.fst ℝ (Fin m → ℝ) (E'' 0)).hasFDerivAt.comp_hasFDerivWithinAt
    (x := z) (hg.isSc1With_scDeriv.hasFDerivWithinAt z hz)).add_const c
  have d₂' : HasFDerivWithinAt (L ∘ (f ∘ ((rnSc m).prod E).toBase 1))
      ((ContinuousLinearMap.fst ℝ (Fin m → ℝ) (E'' 0)).comp
        ((scDeriv U g z).comp (((rnSc m).prod E).toBase 1)))
      (((rnSc m).prod E).lvlSet U 1) z :=
    d₂.congr (fun x hx => (hfg _ hx)) (hfg _ hz)
  have key := (hU.isScDomain.uniqueDiffWithinAt 1 z hz).eq d₁ d₂'
  have key' : (L.comp (scDeriv U f z)).comp (((rnSc m).prod E).toBase 1) =
      ((ContinuousLinearMap.fst ℝ (Fin m → ℝ) (E'' 0)).comp (scDeriv U g z)).comp
        (((rnSc m).prod E).toBase 1) := key
  have := ContinuousLinearMap.ext_of_comp_toBase_one (F₀ := rnSc m) key'
  exact congrArg (fun T => T v) this

end FstDeriv

/-! ### The chart condition and its transport -/

section Transport

variable {m : ℕ} {E E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {n n' : ℕ}
  {Wq Wq' : ScBanach}

variable (m) in
/-- **The chart condition of stratified regularity** (the last clause of `IsStratRegularPoint`):
for a retract `Q` in `ℝᵐ ⊕ E` (partial quadrant `ℝᵐ × C`), a presentation `T` of `C` and a
level-`1` point `y`, the projection to `ℝᵐ` maps `T_yQ ∩ (ℝᵐ × E_{y₂})` onto `ℝᵐ`. -/
def StratRegCond (E : ScBanach) (C : Set (E 0)) (Q : Set (((rnSc m).prod E) 0))
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (y : ((rnSc m).prod E) 1) : Prop :=
  ∀ μ : Fin m → ℝ, ∃ v ∈ tangentSpace ((rnSc m).prod E) (univ ×ˢ C) Q y,
    v.2 ∈ minimalSubspaceWith T (E.toBase 1 y.2) ∧ v.1 = μ

/-- The condition depends only on the tangent space `T_yQ`. -/
theorem StratRegCond.congr {Q Q₂ : Set (((rnSc m).prod E) 0)}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)} {y : ((rnSc m).prod E) 1}
    (hQ : tangentSpace ((rnSc m).prod E) (univ ×ˢ C) Q y =
      tangentSpace ((rnSc m).prod E) (univ ×ˢ C) Q₂ y)
    (h : StratRegCond m E C Q T y) : StratRegCond m E C Q₂ T y := by
  intro μ
  obtain ⟨v, hv, h2, h1⟩ := h μ
  exact ⟨v, hQ ▸ hv, h2, h1⟩

/-- `E_{(r, e)} = ℝᵐ × E_e` for the presentation `ℝᵐ ⊕ E ≅ ℝⁿ ⊕ (ℝᵐ ⊕ W)` of `ℝᵐ × C`. -/
lemma mem_minimalSubspaceWith_rnPres_prod (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (p v : ((rnSc m).prod E) 0) :
    v ∈ minimalSubspaceWith (prodPresentation (rnPres m) T) p ↔
      v.2 ∈ minimalSubspaceWith T p.2 := by
  rw [minimalSubspaceWith_prodPresentation, Submodule.mem_prod]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [mem_minimalSubspaceWith]
  intro i
  exact i.elim0

/-- `ℝᵐ × C` is the partial quadrant of the product presentation. -/
lemma univ_prod_eq_rnPres_prod (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : C = T 0 ⁻¹' quadrant n Wq 0) :
    (univ : Set ((rnSc m) 0)) ×ˢ C =
      prodPresentation (rnPres m) T 0 ⁻¹'
        quadrant (0 + n) ((ScBanach.const (Fin m → ℝ)).prod Wq) 0 :=
  prod_eq_prodPresentation (rnPres m) T rnPres_eq hT

/-- **Stratified regularity is carried by a germ of sc-diffeomorphisms which is a translation in
the `ℝᵐ`-factor**: let `F : O → O'` be a germ of sc-diffeomorphisms between retracts in `ℝᵐ ⊕ E`
and `ℝᵐ ⊕ E'` (partial quadrants `ℝᵐ × C`, `ℝᵐ × C'`) with `(F w)₁ = w₁ + c` on `O`, and
`Q ⊆ O`, `Q'` retracts with `F(Q) ⊆ Q'`.  If the projection maps `T_zQ ∩ (ℝᵐ × E_{z₂})` onto
`ℝᵐ`, so does it `T_{F(z)}Q' ∩ (ℝᵐ × E'_{F(z)₂})`.  *Proof*: `A = D(F ∘ r)(z)` maps `T_zQ` into
`T_{F(z)}Q'` (`scDeriv_mem_tangentSpace_of_subset`), `E_z` into `E'_{F(z)}` (the sign argument,
`IsDiffeoGerm.deriv_mapsTo_minimalSubspace`, for the product presentations), and preserves the
first component on `T_zO = Dr(z)E` (`scDeriv_fst_eq_of_fst_eq`). -/
theorem StratRegCond.transport {R : ScRetraction ((rnSc m).prod E) (univ ×ˢ C)}
    {R' : ScRetraction ((rnSc m).prod E') (univ ×ˢ C')}
    {F : ((rnSc m).prod E) 0 → ((rnSc m).prod E') 0}
    {G : ((rnSc m).prod E') 0 → ((rnSc m).prod E) 0}
    (h : R.IsDiffeoGerm R' F G) (hFs : IsScSmooth R.U (F ∘ R)) (c : Fin m → ℝ)
    (hF1 : ∀ w ∈ R.retract, (F w).1 = w.1 + c)
    {Q : Set (((rnSc m).prod E) 0)} {Q' : Set (((rnSc m).prod E') 0)}
    (hQ : IsScRetract ((rnSc m).prod E) (univ ×ˢ C) Q)
    (hQ' : IsScRetract ((rnSc m).prod E') (univ ×ˢ C') Q') (hQR : Q ⊆ R.retract)
    (hFQ : MapsTo F Q Q') {z : ((rnSc m).prod E) 1} (hz : z ∈ ((rnSc m).prod E).lvlSet Q 1)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (hT : C = T 0 ⁻¹' quadrant n Wq 0)
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod Wq'))
    (hT' : C' = T' 0 ⁻¹' quadrant n' Wq' 0) (hs : StratRegCond m E C Q T z) :
    StratRegCond m E' C' Q' T' (levelMap (F ∘ R) 1 z) := by
  intro μ
  obtain ⟨v, hvQ, hv2, hv1⟩ := hs μ
  have hx : z ∈ ((rnSc m).prod E).lvlSet R.retract 1 := hQR hz
  refine ⟨scDeriv R.U (F ∘ R) z v,
    scDeriv_mem_tangentSpace_of_subset R hFs hQ hQ' hQR hFQ hz hvQ, ?_, ?_⟩
  · have hmap := h.deriv_mapsTo_minimalSubspace hx (prodPresentation (rnPres m) T)
      (univ_prod_eq_rnPres_prod T hT) (prodPresentation (rnPres m) T')
      (univ_prod_eq_rnPres_prod T' hT')
    have hv : v ∈ minimalSubspaceWith (prodPresentation (rnPres m) T)
        (((rnSc m).prod E).toBase 1 z) := by
      rw [mem_minimalSubspaceWith_rnPres_prod, ScBanach.prod_toBase]; exact hv2
    have h' := hmap hv
    rw [SetLike.mem_coe, mem_minimalSubspaceWith_rnPres_prod, ← h.toBase_image hx,
      ScBanach.prod_toBase] at h'
    exact h'
  · have hfg : ∀ u ∈ R.U, ((F ∘ R) u).1 = (R u).1 + c := fun u hu =>
      hF1 _ (R.apply_mem_retract hu)
    have e1 := scDeriv_fst_eq_of_fst_eq R.relOpen hFs.isSc1 R.isSc1 c hfg
      (R.lvlSet_retract_subset 1 hx) v
    rw [e1]
    have hvO := tangentSpace_subset_of_subset R hQ hQR hz hvQ
    rw [tangentSpace_eq_range R hx] at hvO
    obtain ⟨w, rfl⟩ := hvO
    have e2 := congrArg (fun L : ((rnSc m).prod E) 0 →L[ℝ] ((rnSc m).prod E) 0 => L w)
      (R.scDeriv_comp_self hx)
    simp only [ContinuousLinearMap.comp_apply] at e2
    rw [e2]
    exact hv1

end Transport

/-! ### The chart change for product charts -/

section ChartChange

universe u

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} [ParacompactSpace ((Fin m → ℝ) × X)]

omit [T2Space X] [ParacompactSpace X] [ParacompactSpace ((Fin m → ℝ) × X)] in
/-- The transition map of two product charts `(r ↦ r − a) × φ`, `(r ↦ r − a') × φ'` is a
translation in the `ℝᵐ`-factor. -/
lemma transition_rnChart_prod_fst (a a' : Fin m → ℝ) (φ φ' : MChart X)
    (w : ((rnSc m).prod φ.model.E) 0) :
    (((rnChart m a).prod φ).transition ((rnChart m a').prod φ') w).1 = w.1 + (a - a') := by
  change w.1 + a - a' = w.1 + (a - a')
  abel

/-- **The chart change for stratified regularity** (`chart_change_of_transport` with the product
structure kept): let `χ = (r ↦ r − a) × φ` and `χ' = (r ↦ r − a') × φ'` be product charts of
`ℝᵐ × X`, `G ⊆ dom χ`, `G' ⊆ dom χ'` open with `χ(G ∩ A)`, `χ'(G' ∩ A)` retracts, and
`z ∈ A ∩ G ∩ G'` with level-`1` points `y`, `y'` over `χ(z)`, `χ'(z)`.  If the projection maps
`T_y(χ(G ∩ A)) ∩ (ℝᵐ × E_{y₂})` onto `ℝᵐ`, the same holds in `χ'` at `y'`, for any presentations
`T`, `T'` of the partial quadrants of `φ`, `φ'`.  *Proof*: the transition `τ = χ' ∘ χ⁻¹` is a germ
of sc-diffeomorphisms between the overlap retracts with `τ(w)₁ = w₁ + a − a'`
(`transition_rnChart_prod_fst`), so `StratRegCond.transport` applies on the common open piece
`G ∩ G'`. -/
theorem stratRegCond_chart_change {a a' : Fin m → ℝ} {φ φ' : MChart X} (hφ : PX.IsChart φ)
    (hφ' : PX.IsChart φ') {A G G' : Set ((Fin m → ℝ) × X)} (hG : IsOpen G) (hG' : IsOpen G')
    (hGφ : G ⊆ ((rnChart m a).prod φ).source) (hGφ' : G' ⊆ ((rnChart m a').prod φ').source)
    (hQ : IsScRetract ((rnChart m a).prod φ).model.E ((rnChart m a).prod φ).model.C
      (((rnChart m a).prod φ) '' (G ∩ A)))
    (hQ' : IsScRetract ((rnChart m a').prod φ').model.E ((rnChart m a').prod φ').model.C
      (((rnChart m a').prod φ') '' (G' ∩ A)))
    {z : (Fin m → ℝ) × X} (hzA : z ∈ A) (hzG : z ∈ G) (hzG' : z ∈ G')
    {y : ((rnSc m).prod φ.model.E) 1} {y' : ((rnSc m).prod φ'.model.E) 1}
    (hy : ((rnSc m).prod φ.model.E).toBase 1 y = ((rnChart m a).prod φ) z)
    (hy' : ((rnSc m).prod φ'.model.E).toBase 1 y' = ((rnChart m a').prod φ') z)
    {n n' : ℕ} {Wq Wq' : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (T' : ScIso φ'.model.E ((ScBanach.const (Fin n' → ℝ)).prod Wq'))
    (hT' : φ'.model.C = T' 0 ⁻¹' quadrant n' Wq' 0)
    (h : StratRegCond m φ.model.E φ.model.C (((rnChart m a).prod φ) '' (G ∩ A)) T y) :
    StratRegCond m φ'.model.E φ'.model.C (((rnChart m a').prod φ') '' (G' ∩ A)) T' y' := by
  classical
  set χ := (rnChart m a).prod φ with hχdef
  set χ' := (rnChart m a').prod φ' with hχ'def
  have hχ : ((rnPolyfold m).prod PX).IsChart χ := MPolyfold.IsChart.prod (isChart_rnChart a) hφ
  have hχ' : ((rnPolyfold m).prod PX).IsChart χ' :=
    MPolyfold.IsChart.prod (isChart_rnChart a') hφ'
  have hbase : χ.Compatible χ' := MPolyfold.IsChart.compatible _ hχ hχ'
  obtain ⟨W, hWo, hW⟩ := χ.exists_isOpen_image_eq (s := χ.source ∩ χ'.source)
    inter_subset_left (χ.isOpen_source.inter χ'.isOpen_source)
  obtain ⟨W', hWo', hW'⟩ := χ'.exists_isOpen_image_eq (s := χ'.source ∩ χ.source)
    inter_subset_left (χ'.isOpen_source.inter χ.isOpen_source)
  obtain ⟨R, hR⟩ := χ.model.isScRetract
  obtain ⟨R', hR'⟩ := χ'.model.isScRetract
  set Rw := R.restrict hWo with hRwdef
  set Rw' := R'.restrict hWo' with hRw'def
  have hRw : Rw.retract = χ.overlap χ' := by rw [R.restrict_retract, hR]; exact hW.symm
  have hRw' : Rw'.retract = χ'.overlap χ := by rw [R'.restrict_retract, hR']; exact hW'.symm
  set τ := χ.transition χ' with hτdef
  set τ' := χ'.transition χ with hτ'def
  have hdiff : Rw.IsDiffeoGerm Rw' τ τ' :=
    { isSc1 := (hbase.1.comp_isScSmooth Rw hRw).isSc1
      isSc1_inv := (hbase.2.comp_isScSmooth Rw' hRw').isSc1
      mapsTo := by rw [hRw, hRw']; exact χ.transition_mapsTo χ'
      mapsTo_inv := by rw [hRw, hRw']; exact χ'.transition_mapsTo χ
      left_inv := by
        rw [hRw]; rintro _ ⟨y₁, hy₁, rfl⟩
        rw [hτdef, hτ'def, χ.transition_apply χ' hy₁.1, χ'.transition_apply χ hy₁.2]
      right_inv := by
        rw [hRw']; rintro _ ⟨y₁, hy₁, rfl⟩
        rw [hτdef, hτ'def, χ'.transition_apply χ hy₁.1, χ.transition_apply χ' hy₁.2] }
  have hτs : IsScSmooth Rw.U (τ ∘ Rw) := hbase.1.comp_isScSmooth Rw hRw
  -- the common open piece `H = G ∩ G'`
  have hH : IsOpen (G ∩ G') := hG.inter hG'
  have hHχ : G ∩ G' ⊆ χ.source := fun x hx => hGφ hx.1
  have hHχ' : G ∩ G' ⊆ χ'.source := fun x hx => hGφ' hx.2
  obtain ⟨K, hK, hKeq⟩ := χ.exists_isOpen_image_eq hHχ hH
  obtain ⟨K', hK', hK'eq⟩ := χ'.exists_isOpen_image_eq hHχ' hH
  have hQH : χ '' ((G ∩ G') ∩ A) = χ '' (G ∩ A) ∩ K :=
    χ.image_inter_eq_inter hGφ inter_subset_left hKeq
  have hQ'H : χ' '' ((G ∩ G') ∩ A) = χ' '' (G' ∩ A) ∩ K' :=
    χ'.image_inter_eq_inter hGφ' inter_subset_right hK'eq
  have hQHr : IsScRetract χ.model.E χ.model.C (χ '' ((G ∩ G') ∩ A)) := by
    rw [hQH]; exact proposition_2_3_1_one hQ hK
  have hQ'Hr : IsScRetract χ'.model.E χ'.model.C (χ' '' ((G ∩ G') ∩ A)) := by
    rw [hQ'H]; exact proposition_2_3_1_one hQ' hK'
  have hQHsub : χ '' ((G ∩ G') ∩ A) ⊆ Rw.retract := by
    rw [hRw]; exact image_mono fun x hx => ⟨hHχ hx.1, hHχ' hx.1⟩
  have hτQ : MapsTo τ (χ '' ((G ∩ G') ∩ A)) (χ' '' ((G ∩ G') ∩ A)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hτdef, χ.transition_apply χ' (hHχ hx.1)]
    exact ⟨x, hx, rfl⟩
  have hzH : z ∈ (G ∩ G') ∩ A := ⟨⟨hzG, hzG'⟩, hzA⟩
  have hy1 : y ∈ χ.model.E.lvlSet (χ '' ((G ∩ G') ∩ A)) 1 := by
    change ((rnSc m).prod φ.model.E).toBase 1 y ∈ χ '' ((G ∩ G') ∩ A)
    rw [hy]; exact ⟨z, hzH, rfl⟩
  have hy'1 : χ'.model.E.toBase 1 y' ∈ χ' '' ((G ∩ G') ∩ A) := by
    change ((rnSc m).prod φ'.model.E).toBase 1 y' ∈ _
    rw [hy']; exact ⟨z, hzH, rfl⟩
  have hyQ : χ.model.E.toBase 1 y ∈ χ '' (G ∩ A) ∩ K := by rw [← hQH]; exact hy1
  have hy'Q : χ'.model.E.toBase 1 y' ∈ χ' '' (G' ∩ A) ∩ K' := by rw [← hQ'H]; exact hy'1
  have e1 : tangentSpace χ.model.E χ.model.C (χ '' ((G ∩ G') ∩ A)) y =
      tangentSpace χ.model.E χ.model.C (χ '' (G ∩ A)) y := by
    rw [hQH]; exact tangentSpace_inter_isOpen hQ hK hyQ
  have h1 : StratRegCond m φ.model.E φ.model.C (χ '' ((G ∩ G') ∩ A)) T y :=
    StratRegCond.congr e1.symm h
  have h2 := StratRegCond.transport (C' := φ'.model.C) hdiff hτs (a - a')
    (fun w _ => transition_rnChart_prod_fst a a' φ φ' w) hQHr hQ'Hr hQHsub hτQ hy1 T hT T' hT' h1
  have hlev : levelMap (τ ∘ Rw) 1 y = y' := by
    apply levelMap_eq_of_toBase_eq
    have hχz : χ z ∈ R.retract := hR ▸ χ.mapsTo_model z (hGφ hzG)
    change χ'.model.E.toBase 1 y' = τ (R (χ.model.E.toBase 1 y))
    rw [show χ.model.E.toBase 1 y = χ z from hy, R.apply_eq_self_of_mem_retract hχz, hτdef,
      χ.transition_apply χ' (hGφ hzG)]
    exact hy'
  subst hlev
  have e2 : tangentSpace χ'.model.E χ'.model.C (χ' '' ((G ∩ G') ∩ A)) (levelMap (τ ∘ Rw) 1 y) =
      tangentSpace χ'.model.E χ'.model.C (χ' '' (G' ∩ A)) (levelMap (τ ∘ Rw) 1 y) := by
    rw [hQ'H]; exact tangentSpace_inter_isOpen hQ' hK' hy'Q
  exact StratRegCond.congr e2 h2

/-- **Theorem 4.3.1 (2021, p. 193; preprint 4.23): stratified regularity does not depend on the
chart.**  If `z` is a stratified regular point of `p = P|_A` (`IsStratRegularPoint`: the condition
holds for *some* data of Definition 4.2.1, product chart `(r ↦ r − a) × φ`, presentation and
lift), then the projection maps `T_zA ∩ (ℝᵐ × E_{z₂})` onto `ℝᵐ` for *every* data `d'`, every
product chart `(r ↦ r − a') × φ'` at `z`, every presentation `T'` of the partial quadrant of `φ'`
and the level-`1` point `y'` over the image of `z` (`stratRegCond_chart_change`). -/
theorem IsStratRegularPoint.stratRegCond {A : Set ((Fin m → ℝ) × X)} {z : (Fin m → ℝ) × X}
    (h : IsStratRegularPoint PX A z) (d' : ((rnPolyfold m).prod PX).SubmanifoldData A)
    (a' : Fin m → ℝ) {φ' : MChart X} (hφ' : PX.IsChart φ') {n' : ℕ} {Wq' : ScBanach}
    (T' : ScIso φ'.model.E ((ScBanach.const (Fin n' → ℝ)).prod Wq'))
    (hT' : φ'.model.C = T' 0 ⁻¹' quadrant n' Wq' 0) {y' : ((rnSc m).prod φ'.model.E) 1}
    (hz' : z ∈ d'.V) (hzφ' : z.2 ∈ φ'.source)
    (hy' : ((rnSc m).prod φ'.model.E).toBase 1 y' = ((rnChart m a').prod φ') z) :
    StratRegCond m φ'.model.E φ'.model.C
      (((rnChart m a').prod φ') '' (d'.toSubData.shrink ((rnChart m a').prod φ') ∩ A)) T' y' := by
  obtain ⟨hzA, d, a, φ, n, Wq, T, y, hzd, hφ, hzφ, hT, hy, hs⟩ := h
  have hχ : ((rnPolyfold m).prod PX).IsChart ((rnChart m a).prod φ) :=
    MPolyfold.IsChart.prod (isChart_rnChart a) hφ
  have hχ' : ((rnPolyfold m).prod PX).IsChart ((rnChart m a').prod φ') :=
    MPolyfold.IsChart.prod (isChart_rnChart a') hφ'
  exact stratRegCond_chart_change hφ hφ' (d.toSubData.isOpen_shrink _)
    (d'.toSubData.isOpen_shrink _) (d.toSubData.shrink_subset_source _)
    (d'.toSubData.shrink_subset_source _) (d.toSubData.isScRetract_image _ hχ)
    (d'.toSubData.isScRetract_image _ hχ') hzA
    (d.toSubData.mem_shrink _ hzA hzd ⟨mem_univ _, hzφ⟩)
    (d'.toSubData.mem_shrink _ hzA hz' ⟨mem_univ _, hzφ'⟩) hy hy' T hT T' hT' hs

/-- **Theorem 4.3.1 (2021, p. 193; preprint 4.23), stratified regularity intrinsic to `A`**: for a
smooth finite-dimensional submanifold `A ⊆ ℝᵐ × X` and `z ∈ A`, `z` is a stratified regular point
of `p = P|_A` iff the chart condition holds for all data of Definition 4.2.1, all product charts
`(r ↦ r − a) × φ` at `z`, all presentations and all lifts (equivalently, by
`IsStratRegularPoint.stratRegCond`, for one of them). -/
theorem isStratRegularPoint_iff_forall {A : Set ((Fin m → ℝ) × X)}
    (hA : ((rnPolyfold m).prod PX).IsSmoothSubmanifold A) {z : (Fin m → ℝ) × X} (hzA : z ∈ A) :
    IsStratRegularPoint PX A z ↔
      ∀ (d : ((rnPolyfold m).prod PX).SubmanifoldData A) (a : Fin m → ℝ) (φ : MChart X),
        PX.IsChart φ → ∀ (n : ℕ) (Wq : ScBanach)
        (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
        φ.model.C = T 0 ⁻¹' quadrant n Wq 0 → ∀ y : ((rnSc m).prod φ.model.E) 1, z ∈ d.V →
          z.2 ∈ φ.source → ((rnSc m).prod φ.model.E).toBase 1 y = ((rnChart m a).prod φ) z →
          StratRegCond m φ.model.E φ.model.C
            (((rnChart m a).prod φ) '' (d.toSubData.shrink ((rnChart m a).prod φ) ∩ A)) T y := by
  refine ⟨fun h d a φ hφ n Wq T hT y hzd hzφ hy => h.stratRegCond d a hφ T hT hzd hzφ hy,
    fun h => ?_⟩
  obtain ⟨φ, hφ, hzφ⟩ := PX.exists_isChart_mem_source z.2
  obtain ⟨n, Wq, T, hT⟩ := φ.model.isPartialQuadrant
  have hχ : ((rnPolyfold m).prod PX).IsChart ((rnChart m 0).prod φ) :=
    MPolyfold.IsChart.prod (isChart_rnChart 0) hφ
  have hzχ : z ∈ ((rnChart m 0).prod φ).source := ⟨mem_univ _, hzφ⟩
  have hs : ((rnChart m 0).prod φ) z ∈ ((rnChart m 0).prod φ).model.E.smooth :=
    (MPolyfold.mem_smoothSet_iff hχ hzχ).1 (hA.subset_smoothSet hzA)
  obtain ⟨y, hy, -⟩ := exists_smoothLvl_one_of_mem_smooth hs
  exact ⟨hzA, hA.data hzA, 0, φ, n, Wq, T, y, hA.mem_data_V hzA, hφ, hzφ, hT, hy,
    h _ 0 φ hφ n Wq T hT y (hA.mem_data_V hzA) hzφ hy⟩

/-- **Theorem 4.3.1 (2021, p. 193; preprint 4.23), stratified regular values intrinsic to `A`**:
`λ` is a stratified regular value of `p = P|_A` iff at every point of `A` over `λ` the chart
condition holds in all data, product charts, presentations and lifts. -/
theorem isStratRegularValue_iff_forall {A : Set ((Fin m → ℝ) × X)}
    (hA : ((rnPolyfold m).prod PX).IsSmoothSubmanifold A) (lam : Fin m → ℝ) :
    IsStratRegularValue PX A lam ↔
      ∀ z ∈ A, z.1 = lam →
        ∀ (d : ((rnPolyfold m).prod PX).SubmanifoldData A) (a : Fin m → ℝ) (φ : MChart X),
        PX.IsChart φ → ∀ (n : ℕ) (Wq : ScBanach)
        (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
        φ.model.C = T 0 ⁻¹' quadrant n Wq 0 → ∀ y : ((rnSc m).prod φ.model.E) 1, z ∈ d.V →
          z.2 ∈ φ.source → ((rnSc m).prod φ.model.E).toBase 1 y = ((rnChart m a).prod φ) z →
          StratRegCond m φ.model.E φ.model.C
            (((rnChart m a).prod φ) '' (d.toSubData.shrink ((rnChart m a).prod φ) ∩ A)) T y :=
  forall₂_congr fun _z hzA => imp_congr_right fun _ => isStratRegularPoint_iff_forall hA hzA

end ChartChange

end Polyfold
