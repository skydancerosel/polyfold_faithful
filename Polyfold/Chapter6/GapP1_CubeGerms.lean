import Polyfold.Chapter6.GapP1_CubeCharts

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §3.1, Theorem 3.1.21
(p. 89; preprint Theorem 3.18), "readily verified", **with a parameter factor that has
boundary**: the germ calculus of the product germ `O_Λ × G` for a relatively open `O_Λ` of a
partial quadrant `C_Λ` of a finite-dimensional `Λ`.  This is the input of the pull-back of an
sc-Fredholm section to `[0, 1]ⁿ × X` (gap G.65 (a), step 2; the families of Lemmas 6.6.4–6.6.5).

# The germ calculus with a quadrant parameter

## What is formalized

The project's `ℝⁿ`-forms (`GermCalculusParam.lean`, `ParamPerturbation.lean`) have the factor
`(Λ, univ)`.  Here `(Λ, C_Λ)` with `O_Λ ∋ 0` relatively open in `C_Λ`:

* `ScNbhdGerm.quadProd`: the germ `O_Λ × G` in `Λ ⊕ E` with quadrant `C_Λ × C`;
  `IsQuadrantLike.quadProd`; `IsSckGerm.quadProd`, `IsScSmoothGerm.quadProd`,
  `IsSc1GermWith.quadProd` (`(a, u) ↦ g(u)` with derivative family `Dg(u) ∘ pr₂`).
* `IsStrongBundleMap.mono`, `IsStrongBundleIso.mono`: strong bundle maps restrict to smaller
  relatively open domains (in any partial quadrants).
* `IsPartialQuadrant.const_prod`: `C̃ × C_Λ` is a partial quadrant of `Pn × Λ`.
* `ScNbhdGerm.paramExtendQ`, `IsBasicGerm.paramExtendQ` (the `(Λ, C_Λ)`-extension
  `h'((a, λ), w) = h(a, w)` of a basic germ is a basic germ on the parameter quadrant
  `(C̃ × C_Λ) ⊕ W`) and **`IsConjugateToBasicGerm.quadExtend`** (if `k` is conjugated to a basic
  germ on `U`, then `(λ, u) ↦ k(u)` is conjugated to a basic germ on `O_Λ × U`).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

/-! ### The product germ `O_Λ × G` -/

section QuadProd

variable {E F : ScBanach} {C : Set (E 0)} {Λ : Type} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
  [FiniteDimensional ℝ Λ] {CΛ OΛ : Set Λ}

lemma ScBanach.lvlSet_quadProd (C : Set (E 0)) (CΛ : Set Λ) (m : ℕ) :
    ((ScBanach.const Λ).prod E).lvlSet (CΛ ×ˢ C) m = CΛ ×ˢ E.lvlSet C m := by
  ext p
  rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase, mem_prod, mem_prod, ScBanach.const_toBase,
    ScBanach.mem_lvlSet]

/-- `C_Λ × C` is quadrant-like when `C_Λ` and `C` are. -/
lemma IsQuadrantLike.quadProd (hCΛ : IsQuadrantLike (ScBanach.const Λ) CΛ)
    (hC : IsQuadrantLike E C) : IsQuadrantLike ((ScBanach.const Λ).prod E) (CΛ ×ˢ C) where
  zero_mem := ⟨hCΛ.zero_mem, hC.zero_mem⟩
  convex m := by
    rw [ScBanach.lvlSet_quadProd]
    have := hCΛ.convex m
    rw [ScBanach.const_lvlSet] at this
    exact this.prod (hC.convex m)
  interior_nonempty m := by
    rw [ScBanach.lvlSet_quadProd, interior_prod_eq]
    have := hCΛ.interior_nonempty m
    rw [ScBanach.const_lvlSet] at this
    exact this.prod (hC.interior_nonempty m)

variable (hOΛ : IsRelOpenInQuadrant (ScBanach.const Λ) CΛ OΛ) (h0Λ : (0 : Λ) ∈ OΛ)

/-- **The product germ `O_Λ × G`** in `Λ ⊕ E` with quadrant `C_Λ × C`, levels `O_Λ × U_m`. -/
def ScNbhdGerm.quadProd (G₁ : ScNbhdGerm E C) :
    ScNbhdGerm ((ScBanach.const Λ).prod E) (CΛ ×ˢ C) where
  U m := OΛ ×ˢ G₁.U m
  nested m x hx := ⟨hx.1, G₁.nested m x.2 hx.2⟩
  zero_mem m := ⟨h0Λ, G₁.zero_mem m⟩
  relOpen m := by
    obtain ⟨O', hO', hOΛeq⟩ := hOΛ.relOpen
    obtain ⟨O, hO, h⟩ := G₁.relOpen m
    refine ⟨O' ×ˢ O, hO'.prod hO, ?_⟩
    rw [ScBanach.lvlSet_quadProd, hOΛeq, h, prod_inter_prod]

@[simp] lemma ScNbhdGerm.quadProd_U (G₁ : ScNbhdGerm E C) (m : ℕ) :
    (G₁.quadProd hOΛ h0Λ).U m = OΛ ×ˢ G₁.U m := rfl

lemma ScNbhdGerm.quadProd_mapsToGerm_snd (G₁ : ScNbhdGerm E C) :
    (G₁.quadProd hOΛ h0Λ).MapsToGerm G₁ (ScBanach.prodSndOp (ScBanach.const Λ) E 0) := by
  intro m x hx
  rw [ScOperator.levelMap_eq]
  exact hx.2

/-- `(a, u) ↦ g(u)` is an sc^k-germ on `O_Λ × G` when `g` is one on `G`. -/
theorem IsSckGerm.quadProd {k : ℕ} (hCΛ : IsQuadrantLike (ScBanach.const Λ) CΛ)
    (hC : IsQuadrantLike E C) {G₁ : ScNbhdGerm E C} {g : E 0 → F 0} (hg : IsSckGerm k G₁ g) :
    IsSckGerm k (G₁.quadProd hOΛ h0Λ) fun w : ((ScBanach.const Λ).prod E) 0 => g w.2 :=
  IsSckGerm.comp (hCΛ.quadProd hC) hC hg
    ((ScBanach.prodSndOp (ScBanach.const Λ) E).isSckGerm k _ (hCΛ.quadProd hC))
    (G₁.quadProd_mapsToGerm_snd hOΛ h0Λ)

/-- `(a, u) ↦ g(u)` is an sc-smooth germ on `O_Λ × G` when `g` is one on `G`. -/
theorem IsScSmoothGerm.quadProd (hCΛ : IsQuadrantLike (ScBanach.const Λ) CΛ)
    (hC : IsQuadrantLike E C) {G₁ : ScNbhdGerm E C} {g : E 0 → F 0}
    (hg : IsScSmoothGerm G₁ g) :
    IsScSmoothGerm (G₁.quadProd hOΛ h0Λ) fun w : ((ScBanach.const Λ).prod E) 0 => g w.2 :=
  fun k => (hg k).quadProd hOΛ h0Λ hCΛ hC

/-- `(a, u) ↦ g(u)` is an sc¹-germ on `O_Λ × G` with the derivative family `Dg(u) ∘ pr₂`. -/
theorem IsSc1GermWith.quadProd (hC : IsQuadrantLike E C) {G₁ : ScNbhdGerm E C}
    {g : E 0 → F 0} {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G₁ g Dg) :
    IsSc1GermWith (G₁.quadProd hOΛ h0Λ) (fun w : ((ScBanach.const Λ).prod E) 0 => g w.2)
      fun x => (Dg x.2).comp (ContinuousLinearMap.snd ℝ Λ (E 0)) := by
  have := hg.comp (G₁.relOpenConvex hC 1)
    ((ScBanach.prodSndOp (ScBanach.const Λ) E).isSc1GermWith (G₁.quadProd hOΛ h0Λ))
    (G₁.quadProd_mapsToGerm_snd hOΛ h0Λ)
  refine (this.congr fun _ _ => rfl).congr_deriv fun x _ => ?_
  rw [ScOperator.levelMap_eq]
  rfl

end QuadProd

/-! ### Restricting strong bundle maps -/

section Restrict

variable {E F E' F' : ScBanach} {C V : Set (E 0)} {C' V' : Set (E' 0)} {U : Set (E 0)}
  {U' : Set (E' 0)}

/-- **A strong bundle map restricts to smaller relatively open domains**: the conditions of
Definition 2.6.1 are pointwise or sc-smoothness on `U ⊕ F`, which restricts to `V ⊕ F`. -/
theorem IsStrongBundleMap.mono {Φ : E 0 × F 0 → E' 0 × F' 0} (hΦ : IsStrongBundleMap U U' Φ)
    (hV : IsRelOpenInQuadrant E C V) (hVU : V ⊆ U) (hmaps : MapsTo Φ (V ×ˢ univ) (V' ×ˢ univ)) :
    IsStrongBundleMap V V' Φ where
  mapsTo := hmaps
  fst_independent u hu := hΦ.fst_independent u (hVU hu)
  fiber_linear u hu := hΦ.fiber_linear u (hVU hu)
  preserves_filtration m k hk u hu := hΦ.preserves_filtration m k hk u (hVU hu)
  isScSmooth_zero := hΦ.isScSmooth_zero.of_subset (hV.prod_univ F).isScDomain
    (prod_mono hVU subset_rfl)
  isScSmooth_one := hΦ.isScSmooth_one.of_subset (hV.prod_univ F.shift).isScDomain
    (prod_mono hVU subset_rfl)

/-- **A strong bundle isomorphism restricts** to `V ◁ F → V' ◁ F'` when it maps `V` into `V'`
and its inverse maps `V'` into `V`. -/
theorem IsStrongBundleIso.mono {Φ : E 0 × F 0 → E' 0 × F' 0} {Φ' : E' 0 × F' 0 → E 0 × F 0}
    (hΦ : IsStrongBundleIso U U' Φ Φ') (hV : IsRelOpenInQuadrant E C V)
    (hV' : IsRelOpenInQuadrant E' C' V') (hVU : V ⊆ U) (hVU' : V' ⊆ U')
    (hmaps : MapsTo Φ (V ×ˢ univ) (V' ×ˢ univ)) (hmaps' : MapsTo Φ' (V' ×ˢ univ) (V ×ˢ univ)) :
    IsStrongBundleIso V V' Φ Φ' where
  toFun := hΦ.toFun.mono hV hVU hmaps
  invFun := hΦ.invFun.mono hV' hVU' hmaps'
  left_inv p hp := hΦ.left_inv p ⟨hVU hp.1, hp.2⟩
  right_inv p hp := hΦ.right_inv p ⟨hVU' hp.1, hp.2⟩

end Restrict

/-! ### Basic germs on the parameter quadrant `(C̃ × C_Λ) ⊕ W` -/

section BasicExtension

variable {Pn Q : Type} [NormedAddCommGroup Pn] [NormedSpace ℝ Pn] [FiniteDimensional ℝ Pn]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  {Λ : Type} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
  {W : ScBanach} {Ct : Set Pn} {CΛ OΛ : Set Λ}

/-- `C̃ × C_Λ` is a partial quadrant of `Pn × Λ` (constant structures). -/
lemma IsPartialQuadrant.const_prod (hC : IsPartialQuadrant (ScBanach.const Pn) Ct)
    (hCΛ : IsPartialQuadrant (ScBanach.const Λ) CΛ) :
    IsPartialQuadrant (ScBanach.const (Pn × Λ)) (Ct ×ˢ CΛ) := by
  obtain ⟨n, W', T, hT⟩ := hC.prod hCΛ
  let I : ScIso (ScBanach.const (Pn × Λ)) ((ScBanach.const Pn).prod (ScBanach.const Λ)) :=
    { lvl := fun _ => ContinuousLinearEquiv.refl ℝ (Pn × Λ)
      incl_comm := fun _ _ => rfl }
  exact ⟨n, W', I.trans T, hT⟩

/-- A radius below which the points of `C_Λ` lie in `O_Λ`. -/
lemma IsRelOpenInQuadrant.exists_ball_const (hOΛ : IsRelOpenInQuadrant (ScBanach.const Λ) CΛ OΛ)
    (h0Λ : (0 : Λ) ∈ OΛ) : ∃ r > 0, ∀ l ∈ CΛ, ‖l‖ < r → l ∈ OΛ := by
  obtain ⟨O', hO', hOΛeq⟩ := hOΛ.relOpen
  have h0 : (0 : Λ) ∈ O' := by
    have := h0Λ
    rw [hOΛeq] at this
    exact this.1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO' 0 h0
  refine ⟨r, hr, fun l hl hlr => ?_⟩
  rw [hOΛeq]
  exact ⟨hball (mem_ball_zero_iff.2 hlr), hl⟩

variable (hOΛ : IsRelOpenInQuadrant (ScBanach.const Λ) CΛ OΛ) (h0Λ : (0 : Λ) ∈ OΛ)

/-- **The `(Λ, C_Λ)`-extension of a germ of neighbourhoods**:
`U''_m = {((a, λ), w) | (a, w) ∈ U_m, λ ∈ O_Λ}` in the partial quadrant `(C̃ × C_Λ) ⊕ W`. -/
def ScNbhdGerm.paramExtendQ (G : ScNbhdGerm (ScBanach.paramProd Pn W) (Ct ×ˢ univ)) :
    ScNbhdGerm (ScBanach.paramProd (Pn × Λ) W) ((Ct ×ˢ CΛ) ×ˢ univ) where
  U m := {p | ((p.1.1, p.2) : Pn × W m) ∈ G.U m ∧ p.1.2 ∈ OΛ}
  nested m p hp := ⟨G.nested m (p.1.1, p.2) hp.1, hp.2⟩
  zero_mem m := ⟨G.zero_mem m, h0Λ⟩
  relOpen m := by
    obtain ⟨O, hO, hGO⟩ := G.relOpen m
    obtain ⟨O', hO', hOΛeq⟩ := hOΛ.relOpen
    refine ⟨(paramForgetOp Pn Λ W m) ⁻¹' O ∩ {p | p.1.2 ∈ O'},
      (hO.preimage (paramForgetOp Pn Λ W m).continuous).inter
        (hO'.preimage (continuous_snd.comp continuous_fst)), ?_⟩
    ext p
    have h1 := ScBanach.paramProd_lvlSet (P := Pn) W Ct m
    have h2 := ScBanach.paramProd_lvlSet (P := Pn × Λ) W (Ct ×ˢ CΛ) m
    rw [h1] at hGO
    rw [h2, Set.mem_ofPred_eq, hGO, hOΛeq]
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true, mem_ofPred_eq]
    tauto

variable {hOΛ h0Λ} in
lemma ScNbhdGerm.paramExtendQ_U (G : ScNbhdGerm (ScBanach.paramProd Pn W) (Ct ×ˢ univ)) (m : ℕ)
    (p : (ScBanach.paramProd (Pn × Λ) W) m) :
    p ∈ (G.paramExtendQ hOΛ h0Λ).U m ↔ ((p.1.1, p.2) : Pn × W m) ∈ G.U m ∧ p.1.2 ∈ OΛ :=
  Iff.rfl

/-- **The `(Λ, C_Λ)`-extension of a basic germ is a basic germ**: if `h` is basic on `C̃ ⊕ W`,
then `h'((a, λ), w) = h(a, w)` is basic on `(C̃ × C_Λ) ⊕ W` with `B'((a, λ), w) = B(a, w)`; the
contraction radius is shrunk so that `λ ∈ O_Λ`. -/
theorem IsBasicGerm.paramExtendQ (hCt : IsQuadrantLike (ScBanach.const Pn) Ct)
    (hCtΛ : IsQuadrantLike (ScBanach.const (Pn × Λ)) (Ct ×ˢ CΛ))
    {G : ScNbhdGerm (ScBanach.paramProd Pn W) (Ct ×ˢ univ)} {h : Pn × W 0 → Q × W 0}
    {Bc : Pn × W 0 → W 0} (hh : IsBasicGerm Ct G h Bc) :
    IsBasicGerm (Ct ×ˢ CΛ) (G.paramExtendQ hOΛ h0Λ) (fun p => h (p.1.1, p.2))
      (fun p => Bc (p.1.1, p.2)) where
  isScSmooth := by
    have hC := hCt.paramProd W
    have hC' := hCtΛ.paramProd W
    exact IsScSmoothGerm.comp hC' hC hh.isScSmooth
      ((paramForgetOp Pn Λ W).isScSmoothGerm (G.paramExtendQ hOΛ h0Λ) hC') fun m p hp => by
        change levelMap (⇑(paramForgetOp Pn Λ W 0)) m p ∈ G.U m
        rw [ScOperator.levelMap_eq]; exact hp.1
  f_zero := hh.f_zero
  snd_eq x hx := hh.snd_eq _ hx.1
  contraction :=
    { isSc0 := IsSc0Germ.comp hh.contraction.isSc0 ((paramForgetOp Pn Λ W).isSc0Germ _)
        fun m p hp => by
          change levelMap (⇑(paramForgetOp Pn Λ W 0)) m p ∈ G.U m
          rw [ScOperator.levelMap_eq]; exact hp.1
      B_zero := hh.contraction.B_zero
      contraction := fun ε hε m => by
        obtain ⟨r, hr, H⟩ := hh.contraction.contraction ε hε m
        obtain ⟨rΛ, hrΛ, hball⟩ := hOΛ.exists_ball_const h0Λ
        refine ⟨min r rΛ, lt_min hr hrΛ, fun a ha har w w' hw hw' => ?_⟩
        have ha1 : ‖a.1‖ < r := lt_of_le_of_lt (norm_fst_le a) (har.trans_le (min_le_left _ _))
        have ha2 : ‖a.2‖ < rΛ :=
          lt_of_le_of_lt (norm_snd_le a) (har.trans_le (min_le_right _ _))
        obtain ⟨hmem, hest⟩ := H a.1 ha.1 ha1 w w' (hw.trans_le (min_le_left _ _))
          (hw'.trans_le (min_le_left _ _))
        refine ⟨⟨hmem, hball a.2 ha.2 ha2⟩, ?_⟩
        have e1 := levelMap_comp_scOperator Bc (paramForgetOp Pn Λ W) m (a, w)
        have e2 := levelMap_comp_scOperator Bc (paramForgetOp Pn Λ W) m (a, w')
        change ‖levelMap (Bc ∘ paramForgetOp Pn Λ W 0) m (a, w) -
          levelMap (Bc ∘ paramForgetOp Pn Λ W 0) m (a, w')‖ ≤ ε * ‖w - w'‖
        rw [e1, e2]
        exact hest }

include hOΛ h0Λ in
/-- **The `(Λ, C_Λ)`-extension of a conjugation to a basic germ**: if `k : U → F` is conjugated
to a basic germ `h` by `Ψ : U ◁ F → U' ◁ (ℝᴺ ⊕ W)`, then `(λ, u) ↦ k(u)` on `O_Λ × U` is
conjugated to `h'((a, λ), w) = h(a, w)` on `(C̃ × C_Λ) ⊕ W` by the restriction of `1_Λ × Ψ`
(`IsStrongBundleIso.paramMap`, `IsStrongBundleIso.mono`) followed by the linear reassociation of
the factors. -/
theorem IsConjugateToBasicGerm.quadExtend {E F : ScBanach} {C U : Set (E 0)}
    (hU : IsRelOpenInQuadrant E C U) {k : E 0 → F 0} (hk : IsConjugateToBasicGerm U k) :
    IsConjugateToBasicGerm (E := (ScBanach.const Λ).prod E) (F := F) (OΛ ×ˢ U)
      fun v => k v.2 := by
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, h0, hG, hh,
    hev⟩ := hk
  have hCtΛ : IsPartialQuadrant (ScBanach.const (Pn × Λ)) (Ct ×ˢ CΛ) :=
    hCt.const_prod hOΛ.isPartialQuadrant
  -- the domain `U''' = {((a, λ), w) | (a, w) ∈ U', λ ∈ O_Λ}`
  set U''' : Set ((ScBanach.paramProd (Pn × Λ) W) 0) :=
    {p | (paramForgetOp Pn Λ W 0) p ∈ U' ∧ p.1.2 ∈ OΛ} with hU'''
  have hrel''' : IsRelOpenInQuadrant (ScBanach.paramProd (Pn × Λ) W) ((Ct ×ˢ CΛ) ×ˢ univ)
      U''' := by
    refine ⟨hCtΛ.prod_univ W, ?_⟩
    obtain ⟨O, hO, hUO⟩ := hU'.relOpen
    obtain ⟨O', hO', hOΛeq⟩ := hOΛ.relOpen
    refine ⟨(paramForgetOp Pn Λ W 0) ⁻¹' O ∩ {p | p.1.2 ∈ O'},
      (hO.preimage (paramForgetOp Pn Λ W 0).continuous).inter
        (hO'.preimage (continuous_snd.comp continuous_fst)), ?_⟩
    ext p
    rw [hU''', mem_ofPred_eq, hUO, hOΛeq]
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true, mem_ofPred_eq]
    tauto
  have hrelΛU := hOΛ.prod hU
  have hrel₁ : IsRelOpenInQuadrant ((ScBanach.const Λ).prod (ScBanach.paramProd Pn W))
      (CΛ ×ˢ (Ct ×ˢ univ)) (OΛ ×ˢ U') := hOΛ.prod hU'
  -- `1_Λ × Ψ`, restricted to `O_Λ × U`
  have hpm := (hΨ.paramMap (Λ := Λ) hU hU').mono hrelΛU hrel₁ (prod_mono (subset_univ _)
    subset_rfl) (prod_mono (subset_univ _) subset_rfl)
    (fun p hp => ⟨⟨hp.1.1, (hΨ.toFun.mapsTo ⟨hp.1.2, mem_univ _⟩).1⟩, mem_univ _⟩)
    (fun p hp => ⟨⟨hp.1.1, (hΨ.invFun.mapsTo ⟨hp.1.2, mem_univ _⟩).1⟩, mem_univ _⟩)
  -- the linear reassociation as a strong bundle isomorphism
  have hswap := ScOperator.isStrongBundleIso_prodMap hrel₁ hrel''' (paramSwapOp Pn Λ W)
    (paramSwapInvOp Pn Λ W) (ScOperator.id (ScBanach.paramProd Q W))
    (ScOperator.id (ScBanach.paramProd Q W)) (fun p hp => ⟨hp.2, hp.1⟩)
    (fun p hp => ⟨hp.2, hp.1⟩) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have hiso := hpm.comp hrelΛU hrel₁ hrel''' hswap
  refine ⟨Pn × Λ, Q, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, W, Ct ×ˢ CΛ, U''', _, _, G.paramExtendQ hOΛ h0Λ, fun p => h (p.1.1, p.2),
    fun p => Bc (p.1.1, p.2), hCtΛ, hrel''', hiso, ?_, ?_,
    hh.paramExtendQ hOΛ h0Λ hCt.isQuadrantLike hCtΛ.isQuadrantLike, ?_⟩
  · change paramSwapOp Pn Λ W 0 ((0 : Λ), IsStrongBundleMap.base Ψ 0) = 0
    rw [h0]
    exact map_zero _
  · intro p hp
    exact ⟨hG hp.1, hp.2⟩
  · have ht : Tendsto (fun v : ((ScBanach.const Λ).prod E) 0 => v.2) (𝓝 0) (𝓝 0) :=
      continuous_snd.tendsto' _ _ rfl
    filter_upwards [ht.eventually hev] with v hv hvU
    exact hv hvU.2

end BasicExtension

end Polyfold
