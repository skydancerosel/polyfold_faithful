import Polyfold.Chapter15.ProductGerms
import Polyfold.Chapter6.CubeGerms

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2021), §15.3, the products remark after
**Definition 15.3.3** (p. 692): "`f × f'` is an sc-Fredholm section of `W × W' → X × X'`".
The basic germs (Definition 3.1.7) and the conjugation of Definition 3.1.11.

# Products of basic germs

## What is formalized

* `prodParamOp`, `prodParamInvOp`: the linear reassociation
  `(P ⊕ W) ⊕ (P' ⊕ W') ≅ (P × P') ⊕ (W ⊕ W')` as sc-operators.
* `ScNbhdGerm.prodParam`: the germ `{((a, a'), (w, w')) | (a, w) ∈ G, (a', w') ∈ G'}`.
* **`IsBasicGerm.prod`**: the product of two basic germs, with the coordinates reordered, is a
  basic germ: `h''((a, a'), (w, w')) = ((h₁(a, w), h'₁(a', w')), (w − B(a, w), w' − B'(a', w')))`
  and `B''((a, a'), (w, w')) = (B(a, w), B'(a', w'))` is an sc⁰-contraction germ.
* `IsStrongBundleIso.prod`: products of strong bundle isomorphisms (after the swap).
* **`IsConjugateToBasicGerm.prod`**: if `k` and `k'` are conjugated to basic germs, so is
  `k × k'` on `U × U'`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

section Reassociation

variable (Pn Pn' : Type) [NormedAddCommGroup Pn] [NormedSpace ℝ Pn] [FiniteDimensional ℝ Pn]
  [NormedAddCommGroup Pn'] [NormedSpace ℝ Pn'] [FiniteDimensional ℝ Pn'] (W W' : ScBanach)

/-- The reassociation `((a, w), (a', w')) ↦ ((a, a'), (w, w'))`, an sc-operator
`(P ⊕ W) ⊕ (P' ⊕ W') → (P × P') ⊕ (W ⊕ W')`. -/
def prodParamOp : ScOperator ((ScBanach.paramProd Pn W).prod (ScBanach.paramProd Pn' W'))
    (ScBanach.paramProd (Pn × Pn') (W.prod W')) where
  lvl m := (ContinuousLinearEquiv.prodProdProdComm ℝ Pn (W m) Pn' (W' m) : _ →L[ℝ] _)
  incl_comm _ _ := rfl

/-- The inverse reassociation `((a, a'), (w, w')) ↦ ((a, w), (a', w'))`. -/
def prodParamInvOp : ScOperator (ScBanach.paramProd (Pn × Pn') (W.prod W'))
    ((ScBanach.paramProd Pn W).prod (ScBanach.paramProd Pn' W')) where
  lvl m := (ContinuousLinearEquiv.prodProdProdComm ℝ Pn Pn' (W m) (W' m) : _ →L[ℝ] _)
  incl_comm _ _ := rfl

@[simp] lemma prodParamOp_apply (m : ℕ)
    (p : ((ScBanach.paramProd Pn W).prod (ScBanach.paramProd Pn' W')) m) :
    prodParamOp Pn Pn' W W' m p = ((p.1.1, p.2.1), (p.1.2, p.2.2)) := rfl

@[simp] lemma prodParamInvOp_apply (m : ℕ) (p : (ScBanach.paramProd (Pn × Pn') (W.prod W')) m) :
    prodParamInvOp Pn Pn' W W' m p = ((p.1.1, p.2.1), (p.1.2, p.2.2)) := rfl

end Reassociation

section BasicProduct

variable {Pn Pn' Q Q' : Type} [NormedAddCommGroup Pn] [NormedSpace ℝ Pn] [FiniteDimensional ℝ Pn]
  [NormedAddCommGroup Pn'] [NormedSpace ℝ Pn'] [FiniteDimensional ℝ Pn']
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [NormedAddCommGroup Q'] [NormedSpace ℝ Q'] [FiniteDimensional ℝ Q']
  {W W' : ScBanach} {Ct : Set Pn} {Ct' : Set Pn'}

/-- `C̃ × C̃'` is quadrant-like in `P × P'`. -/
lemma IsQuadrantLike.const_prod_const (hC : IsQuadrantLike (ScBanach.const Pn) Ct)
    (hC' : IsQuadrantLike (ScBanach.const Pn') Ct') :
    IsQuadrantLike (ScBanach.const (Pn × Pn')) (Ct ×ˢ Ct') := by
  obtain ⟨h0, hc, hi⟩ := isQuadrantLike_const_iff.1 hC
  obtain ⟨h0', hc', hi'⟩ := isQuadrantLike_const_iff.1 hC'
  refine isQuadrantLike_const_iff.2 ⟨⟨h0, h0'⟩, hc.prod hc', ?_⟩
  rw [interior_prod_eq]
  exact hi.prod hi'

/-- **The product of two germs of neighbourhoods in parameter products**, with the coordinates
reordered: `U''_m = {((a, a'), (w, w')) | (a, w) ∈ U_m, (a', w') ∈ U'_m}`. -/
def ScNbhdGerm.prodParam (G : ScNbhdGerm (ScBanach.paramProd Pn W) (Ct ×ˢ univ))
    (G' : ScNbhdGerm (ScBanach.paramProd Pn' W') (Ct' ×ˢ univ)) :
    ScNbhdGerm (ScBanach.paramProd (Pn × Pn') (W.prod W')) ((Ct ×ˢ Ct') ×ˢ univ) where
  U m := {p | ((p.1.1, p.2.1) : Pn × W m) ∈ G.U m ∧ ((p.1.2, p.2.2) : Pn' × W' m) ∈ G'.U m}
  nested m p hp := ⟨G.nested m (p.1.1, p.2.1) hp.1, G'.nested m (p.1.2, p.2.2) hp.2⟩
  zero_mem m := ⟨G.zero_mem m, G'.zero_mem m⟩
  relOpen m := by
    obtain ⟨O, hO, hGO⟩ := G.relOpen m
    obtain ⟨O', hO', hGO'⟩ := G'.relOpen m
    refine ⟨(prodParamInvOp Pn Pn' W W' m) ⁻¹' (O ×ˢ O'),
      (hO.prod hO').preimage (prodParamInvOp Pn Pn' W W' m).continuous, ?_⟩
    ext p
    have h1 := ScBanach.paramProd_lvlSet (P := Pn) W Ct m
    have h2 := ScBanach.paramProd_lvlSet (P := Pn') W' Ct' m
    have h3 := ScBanach.paramProd_lvlSet (P := Pn × Pn') (W.prod W') (Ct ×ˢ Ct') m
    rw [h1] at hGO
    rw [h2] at hGO'
    rw [h3, Set.mem_ofPred_eq, hGO, hGO']
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
    tauto

lemma ScNbhdGerm.prodParam_mapsToGerm (G : ScNbhdGerm (ScBanach.paramProd Pn W) (Ct ×ˢ univ))
    (G' : ScNbhdGerm (ScBanach.paramProd Pn' W') (Ct' ×ˢ univ)) :
    (G.prodParam G').MapsToGerm (G.prod G') (prodParamInvOp Pn Pn' W W' 0) := by
  intro m p hp
  rw [ScOperator.levelMap_eq]
  exact hp

/-- **The product of two basic germs is a basic germ** (Definition 3.1.7), after reordering the
coordinates to `(P × P') ⊕ (W ⊕ W') → (Q × Q') ⊕ (W ⊕ W')`. -/
theorem IsBasicGerm.prod (hCt : IsQuadrantLike (ScBanach.const Pn) Ct)
    (hCt' : IsQuadrantLike (ScBanach.const Pn') Ct')
    {G : ScNbhdGerm (ScBanach.paramProd Pn W) (Ct ×ˢ univ)}
    {G' : ScNbhdGerm (ScBanach.paramProd Pn' W') (Ct' ×ˢ univ)} {h : Pn × W 0 → Q × W 0}
    {h' : Pn' × W' 0 → Q' × W' 0} {Bc : Pn × W 0 → W 0} {Bc' : Pn' × W' 0 → W' 0}
    (hh : IsBasicGerm Ct G h Bc) (hh' : IsBasicGerm Ct' G' h' Bc') :
    IsBasicGerm (W := W.prod W') (Q := Q × Q') (Ct ×ˢ Ct') (G.prodParam G')
      (fun p => prodParamOp Q Q' W W' 0 (Prod.map h h' (prodParamInvOp Pn Pn' W W' 0 p)))
      (fun p => Prod.map Bc Bc' (prodParamInvOp Pn Pn' W W' 0 p)) where
  isScSmooth := by
    have hC'' : IsQuadrantLike (ScBanach.paramProd (Pn × Pn') (W.prod W'))
        ((Ct ×ˢ Ct') ×ˢ univ) := (hCt.const_prod_const hCt').paramProd _
    have hCC := (hCt.paramProd W).prod (hCt'.paramProd W')
    have h1 := IsScSmoothGerm.prodMap (hCt.paramProd W) (hCt'.paramProd W') hh.isScSmooth
      hh'.isScSmooth
    have h2 := IsScSmoothGerm.comp hC'' hCC h1
      ((prodParamInvOp Pn Pn' W W').isScSmoothGerm (G.prodParam G') hC'')
      (G.prodParam_mapsToGerm G')
    exact fun k => IsSckGerm.operator_comp hC'' (prodParamOp Q Q' W W') (h2 k)
  f_zero := by
    change prodParamOp Q Q' W W' 0 (h 0, h' 0) = 0
    rw [hh.f_zero, hh'.f_zero]
    rfl
  snd_eq x hx := Prod.ext (hh.snd_eq _ hx.1) (hh'.snd_eq _ hx.2)
  contraction := by
    have hB : IsSc0Germ (F := W.prod W') (G.prod G') (Prod.map Bc Bc') :=
      IsSc0Germ.pair
        (hh.contraction.isSc0.comp ((ScBanach.fstOp _ _).isSc0Germ _) (G.prod_mapsToGerm_fst G'))
        (hh'.contraction.isSc0.comp ((ScBanach.sndOp _ _).isSc0Germ _)
          (G.prod_mapsToGerm_snd G'))
    have hlev : ∀ (m : ℕ) (y : ((ScBanach.paramProd Pn W).prod (ScBanach.paramProd Pn' W')) m),
        y ∈ (G.prod G').U m →
        levelMap (E := (ScBanach.paramProd Pn W).prod (ScBanach.paramProd Pn' W'))
          (F := W.prod W') (Prod.map Bc Bc') m y =
          ((levelB Bc m y.1, levelB Bc' m y.2) : (W.prod W') m) := by
      intro m y hy
      have e := IsSc0Germ.levelMap_pair
        (hh.contraction.isSc0.comp ((ScBanach.fstOp _ _).isSc0Germ _) (G.prod_mapsToGerm_fst G'))
        (hh'.contraction.isSc0.comp ((ScBanach.sndOp _ _).isSc0Germ _)
          (G.prod_mapsToGerm_snd G')) hy
      refine e.trans (Prod.ext ?_ ?_)
      · exact levelMap_comp_scOperator Bc (ScBanach.fstOp _ _) m y
      · exact levelMap_comp_scOperator Bc' (ScBanach.sndOp _ _) m y
    refine ⟨hB.comp ((prodParamInvOp Pn Pn' W W').isSc0Germ _) (G.prodParam_mapsToGerm G'),
      Prod.ext hh.contraction.B_zero hh'.contraction.B_zero, fun ε hε m => ?_⟩
    obtain ⟨r, hr, H⟩ := hh.contraction.contraction ε hε m
    obtain ⟨r', hr', H'⟩ := hh'.contraction.contraction ε hε m
    refine ⟨min r r', lt_min hr hr', fun a ha har w w' hw hw' => ?_⟩
    have ha1 : ‖a.1‖ < r := lt_of_le_of_lt (norm_fst_le a) (har.trans_le (min_le_left _ _))
    have ha2 : ‖a.2‖ < r' := lt_of_le_of_lt (norm_snd_le a) (har.trans_le (min_le_right _ _))
    have hw1 : ‖w.1‖ < r := lt_of_le_of_lt (norm_fst_le w) (hw.trans_le (min_le_left _ _))
    have hw2 : ‖w.2‖ < r' := lt_of_le_of_lt (norm_snd_le w) (hw.trans_le (min_le_right _ _))
    have hw1' : ‖w'.1‖ < r := lt_of_le_of_lt (norm_fst_le w') (hw'.trans_le (min_le_left _ _))
    have hw2' : ‖w'.2‖ < r' := lt_of_le_of_lt (norm_snd_le w') (hw'.trans_le (min_le_right _ _))
    obtain ⟨hm, hest⟩ := H a.1 ha.1 ha1 w.1 w'.1 hw1 hw1'
    obtain ⟨hm', hest'⟩ := H' a.2 ha.2 ha2 w.2 w'.2 hw2 hw2'
    have hmw' := (H a.1 ha.1 ha1 w'.1 w.1 hw1' hw1).1
    have hmw'' := (H' a.2 ha.2 ha2 w'.2 w.2 hw2' hw2).1
    refine ⟨⟨hm, hm'⟩, ?_⟩
    have e1 : levelB (W := W.prod W')
        (fun p => Prod.map Bc Bc' (prodParamInvOp Pn Pn' W W' 0 p)) m (a, w) =
        levelMap (E := (ScBanach.paramProd Pn W).prod (ScBanach.paramProd Pn' W'))
          (F := W.prod W') (Prod.map Bc Bc') m (prodParamInvOp Pn Pn' W W' m (a, w)) :=
      @levelMap_comp_scOperator (ScBanach.paramProd (Pn × Pn') (W.prod W'))
        ((ScBanach.paramProd Pn W).prod (ScBanach.paramProd Pn' W')) (W.prod W')
        (Prod.map Bc Bc') (prodParamInvOp Pn Pn' W W') m
        (a, w)
    have e2 : levelB (W := W.prod W')
        (fun p => Prod.map Bc Bc' (prodParamInvOp Pn Pn' W W' 0 p)) m (a, w') =
        levelMap (E := (ScBanach.paramProd Pn W).prod (ScBanach.paramProd Pn' W'))
          (F := W.prod W') (Prod.map Bc Bc') m (prodParamInvOp Pn Pn' W W' m (a, w')) :=
      @levelMap_comp_scOperator (ScBanach.paramProd (Pn × Pn') (W.prod W'))
        ((ScBanach.paramProd Pn W).prod (ScBanach.paramProd Pn' W')) (W.prod W')
        (Prod.map Bc Bc') (prodParamInvOp Pn Pn' W W') m
        (a, w')
    rw [e1, e2, hlev m _ ⟨hm, hm'⟩, hlev m _ ⟨hmw', hmw''⟩]
    refine (norm_prod_le_iff (x := (_ - _ : (W.prod W') m))).2 ⟨?_, ?_⟩
    · exact hest.trans (mul_le_mul_of_nonneg_left (norm_fst_le (w - w')) hε.le)
    · exact hest'.trans (mul_le_mul_of_nonneg_left (norm_snd_le (w - w')) hε.le)

end BasicProduct

section IsoProduct

variable {E E' F F' E₁ E₁' F₁ F₁' : ScBanach} {C U : Set (E 0)} {C' U' : Set (E' 0)}
  {C₁ V : Set (E₁ 0)} {C₁' V' : Set (E₁' 0)}

/-- **Products of strong bundle isomorphisms** (after the swap). -/
theorem IsStrongBundleIso.prod {Ψ : E 0 × F 0 → E₁ 0 × F₁ 0} {Ψi : E₁ 0 × F₁ 0 → E 0 × F 0}
    {Ψ' : E' 0 × F' 0 → E₁' 0 × F₁' 0} {Ψi' : E₁' 0 × F₁' 0 → E' 0 × F' 0}
    (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    (hV : IsRelOpenInQuadrant E₁ C₁ V) (hV' : IsRelOpenInQuadrant E₁' C₁' V')
    (h : IsStrongBundleIso U V Ψ Ψi) (h' : IsStrongBundleIso U' V' Ψ' Ψi') :
    IsStrongBundleIso (E := E.prod E') (F := F.prod F') (E' := E₁.prod E₁') (F' := F₁.prod F₁')
      (U ×ˢ U') (V ×ˢ V') (prodBundleMap Ψ Ψ') (prodBundleMap Ψi Ψi') where
  toFun := h.toFun.prod hU hU' h'.toFun
  invFun := h.invFun.prod hV hV' h'.invFun
  left_inv p hp := by
    have e1 := h.left_inv (p.1.1, p.2.1) ⟨hp.1.1, mem_univ _⟩
    have e2 := h'.left_inv (p.1.2, p.2.2) ⟨hp.1.2, mem_univ _⟩
    change bundleSwap (Ψi (Ψ (p.1.1, p.2.1)), Ψi' (Ψ' (p.1.2, p.2.2))) = p
    rw [e1, e2]
    rfl
  right_inv p hp := by
    have e1 := h.right_inv (p.1.1, p.2.1) ⟨hp.1.1, mem_univ _⟩
    have e2 := h'.right_inv (p.1.2, p.2.2) ⟨hp.1.2, mem_univ _⟩
    change bundleSwap (Ψ (Ψi (p.1.1, p.2.1)), Ψ' (Ψi' (p.1.2, p.2.2))) = p
    rw [e1, e2]
    rfl

end IsoProduct

section ConjugationProduct

variable {E E' F F' : ScBanach} {C U : Set (E 0)} {C' U' : Set (E' 0)}

/-- **Products of conjugations to basic germs** (Definition 3.1.11, second paragraph): if
`k : U → F` and `k' : U' → F'` are conjugated to basic germs, then `k × k' : U × U' → F ⊕ F'`
is conjugated to the product basic germ (`IsBasicGerm.prod`) by the product of the two strong
bundle isomorphisms followed by the linear reassociation of the factors. -/
theorem IsConjugateToBasicGerm.prod (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') {k : E 0 → F 0} {k' : E' 0 → F' 0}
    (hk : IsConjugateToBasicGerm U k) (hk' : IsConjugateToBasicGerm U' k') :
    IsConjugateToBasicGerm (E := E.prod E') (F := F.prod F') (U ×ˢ U') (Prod.map k k') := by
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U₁, Ψ, Ψi, G, h, Bc, hCt, hU₁, hΨ, h0, hG, hh,
    hev⟩ := hk
  obtain ⟨Pn', Q', j1, j2, j3, j4, j5, j6, W', Ct', U₁', Ψ', Ψi', G', h', Bc', hCt', hU₁', hΨ',
    h0', hG', hh', hev'⟩ := hk'
  have hCt'' : IsPartialQuadrant (ScBanach.const (Pn × Pn')) (Ct ×ˢ Ct') := hCt.const_prod hCt'
  have hrelV := hU₁.prod hU₁'
  -- the domain `U'' = {((a, a'), (w, w')) | (a, w) ∈ U₁, (a', w') ∈ U₁'}`
  set U'' : Set ((ScBanach.paramProd (Pn × Pn') (W.prod W')) 0) :=
    (prodParamInvOp Pn Pn' W W' 0) ⁻¹' (U₁ ×ˢ U₁') with hU''
  have hrel'' : IsRelOpenInQuadrant (ScBanach.paramProd (Pn × Pn') (W.prod W'))
      ((Ct ×ˢ Ct') ×ˢ univ) U'' := by
    refine ⟨hCt''.prod_univ _, ?_⟩
    obtain ⟨O, hO, hUO⟩ := hU₁.relOpen
    obtain ⟨O', hO', hUO'⟩ := hU₁'.relOpen
    refine ⟨(prodParamInvOp Pn Pn' W W' 0) ⁻¹' (O ×ˢ O'),
      (hO.prod hO').preimage (prodParamInvOp Pn Pn' W W' 0).continuous, ?_⟩
    ext p
    rw [hU'', mem_preimage, hUO, hUO']
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
    tauto
  have hprod := IsStrongBundleIso.prod hU hU' hU₁ hU₁' hΨ hΨ'
  have hswap := ScOperator.isStrongBundleIso_prodMap hrelV hrel'' (prodParamOp Pn Pn' W W')
    (prodParamInvOp Pn Pn' W W') (prodParamOp Q Q' W W') (prodParamInvOp Q Q' W W')
    (fun p hp => hp) (fun p hp => hp) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl)
  have hiso := hprod.comp (hU.prod hU') hrelV hrel'' hswap
  refine ⟨Pn × Pn', Q × Q', inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, W.prod W', Ct ×ˢ Ct', U'', _, _, G.prodParam G',
    fun p => prodParamOp Q Q' W W' 0 (Prod.map h h' (prodParamInvOp Pn Pn' W W' 0 p)),
    fun p => Prod.map Bc Bc' (prodParamInvOp Pn Pn' W W' 0 p), hCt'', hrel'', hiso, ?_, ?_,
    hh.prod hCt.isQuadrantLike hCt'.isQuadrantLike hh', ?_⟩
  · change prodParamOp Pn Pn' W W' 0 (IsStrongBundleMap.base Ψ 0, IsStrongBundleMap.base Ψ' 0) = 0
    rw [h0, h0']
    rfl
  · intro p hp
    exact ⟨hG hp.1, hG' hp.2⟩
  · have ht1 : Tendsto (fun v : (E.prod E') 0 => v.1) (𝓝 0) (𝓝 0) :=
      continuous_fst.tendsto' _ _ rfl
    have ht2 : Tendsto (fun v : (E.prod E') 0 => v.2) (𝓝 0) (𝓝 0) :=
      continuous_snd.tendsto' _ _ rfl
    filter_upwards [ht1.eventually hev, ht2.eventually hev'] with v hv hv' hvU
    have e1 := hv hvU.1
    have e2 := hv' hvU.2
    change prodParamOp Q Q' W W' 0 ((Ψ (v.1, k v.1)).2, (Ψ' (v.2, k' v.2)).2) =
      prodParamOp Q Q' W W' 0 (h (IsStrongBundleMap.base Ψ v.1), h' (IsStrongBundleMap.base Ψ' v.2))
    rw [e1, e2]

end ConjugationProduct

end Polyfold
