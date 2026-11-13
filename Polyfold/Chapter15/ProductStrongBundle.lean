import Polyfold.Chapter2.FibredProduct
import Polyfold.Chapter2.StrongBundleOne
import Polyfold.Chapter2.StrongBundleRestrict

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2021), §15.3, the products remark after
**Definition 15.3.3** and **Remark 15.3.4** (pp. 692–693; 2017: after Definition 15.3), first step:
the Part I product of strong bundles (gap G.160 (a)).

# Products of strong bundles over M-polyfolds

## The text, paraphrased

For strong bundles `P : W → X` and `P' : W' → X'` the text uses the product strong bundle
`W × W' → X × X'`, with the product of the sections `f × f'`, without stating its construction.

## What is formalized

* `bundleSwap` (`((a, a'), (b, b')) ↦ ((a, b), (a', b'))`) and the sc-operator
  `ScBanach.bundleSwapOp`: `(E ⊕ E') ⊕ (F ⊕ F') ≅ (E ⊕ F) ⊕ (E' ⊕ F')`.
* `prodBundleMap Φ Φ'` (the product of local strong bundle maps after the swap),
  `IsStrongBundleMap.prod`, `IsStrongBundleRetraction.prod`, `baseRetraction_prod`
  (the base retraction of `R × R'` is `r × r'`), `image_prodBundleMap`
  (`(R × R')(U × U' ◁ F ⊕ F')` is `K × K'` after the swap), `IsStrongBundleRetract.prod`.
* `IsScSmoothRetractMap.prodBundleMap` (products of sc-smooth maps between local strong bundle
  retracts, on `[0]`) and `shiftFiber_prodBundleMap` (the `[1]` version is the product of the
  `[1]` versions).
-/

open Set Function

noncomputable section

namespace Polyfold

/-! ### The swap `(E ⊕ E') ⊕ (F ⊕ F') ≅ (E ⊕ F) ⊕ (E' ⊕ F')` -/

section Swap

/-- The swap `((a, a'), (b, b')) ↦ ((a, b), (a', b'))`; it is its own inverse. -/
def bundleSwap {α β γ δ : Type*} (p : (α × β) × (γ × δ)) : (α × γ) × (β × δ) :=
  ((p.1.1, p.2.1), (p.1.2, p.2.2))

@[simp] lemma bundleSwap_bundleSwap {α β γ δ : Type*} (p : (α × β) × (γ × δ)) :
    bundleSwap (bundleSwap p) = p := rfl

lemma continuous_bundleSwap {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] [TopologicalSpace δ] :
    Continuous (bundleSwap : (α × β) × (γ × δ) → (α × γ) × (β × δ)) :=
  ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd)).prodMk
    ((continuous_snd.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))

/-- The sc-operator `(E ⊕ E') ⊕ (F ⊕ F') → (E ⊕ F) ⊕ (E' ⊕ F')`, `bundleSwap` on every level. -/
def ScBanach.bundleSwapOp (E E' F F' : ScBanach) :
    ScOperator ((E.prod E').prod (F.prod F')) ((E.prod F).prod (E'.prod F')) where
  lvl m := (ContinuousLinearEquiv.prodProdProdComm ℝ (E m) (E' m) (F m) (F' m) : _ →L[ℝ] _)
  incl_comm _ _ := rfl

lemma ScBanach.bundleSwapOp_apply (E E' F F' : ScBanach) (p : (E.prod E').prod (F.prod F') 0) :
    ScBanach.bundleSwapOp E E' F F' 0 p = bundleSwap p := rfl

/-- `p ∈ (E ⊕ F)_m` iff both components are in level `m`. -/
lemma ScBanach.mem_range_prod_toBase {E F : ScBanach} {m : ℕ} {p : (E.prod F) 0} :
    p ∈ range ((E.prod F).toBase m) ↔ p.1 ∈ range (E.toBase m) ∧ p.2 ∈ range (F.toBase m) := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [ScBanach.prod_toBase]
    exact ⟨⟨x.1, rfl⟩, ⟨x.2, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨((a, b) : (E.prod F) m), ?_⟩
    rw [ScBanach.prod_toBase, ha, hb]

/-- The lift to level `1` of a pair of level-`1` points is the pair of the lifts. -/
lemma ScBanach.invFun_prod_toBase_one {E F : ScBanach} {a : E 0} {b : F 0}
    (ha : a ∈ range (E.toBase 1)) (hb : b ∈ range (F.toBase 1)) :
    invFun ((E.prod F).toBase 1) ((a, b) : (E.prod F) 0) =
      ((invFun (E.toBase 1) a, invFun (F.toBase 1) b) : (E.prod F) 1) := by
  apply (E.prod F).toBase_injective 1
  rw [invFun_eq (ScBanach.mem_range_prod_toBase.2 ⟨ha, hb⟩), ScBanach.prod_toBase]
  exact Prod.ext (invFun_eq ha).symm (invFun_eq hb).symm

end Swap

/-! ### Products of local strong bundle maps and retractions -/

section ProdBundleMap

/-- The product `Φ × Φ'` of local strong bundle maps, read on `(E ⊕ E') ⊕ (F ⊕ F')`:
`((u, u'), (h, h')) ↦ ((Φ(u, h)₁, Φ'(u', h')₁), (Φ(u, h)₂, Φ'(u', h')₂))`. -/
def prodBundleMap {α β γ δ α' β' γ' δ' : Type*} (Φ : α × β → γ × δ) (Φ' : α' × β' → γ' × δ') :
    (α × α') × (β × β') → (γ × γ') × (δ × δ') :=
  fun p => bundleSwap (Prod.map Φ Φ' (bundleSwap p))

lemma prodBundleMap_apply {α β γ δ α' β' γ' δ' : Type*} (Φ : α × β → γ × δ)
    (Φ' : α' × β' → γ' × δ') (p : (α × α') × (β × β')) :
    prodBundleMap Φ Φ' p =
      (((Φ (p.1.1, p.2.1)).1, (Φ' (p.1.2, p.2.2)).1),
        ((Φ (p.1.1, p.2.1)).2, (Φ' (p.1.2, p.2.2)).2)) :=
  rfl

variable {E F E₁ F₁ E' F' E₁' F₁' : ScBanach}

/-- `Φ × Φ'` factors as `swap ∘ (Φ × Φ') ∘ swap` through sc-operators. -/
lemma prodBundleMap_eq (Φ : E 0 × F 0 → E₁ 0 × F₁ 0) (Φ' : E' 0 × F' 0 → E₁' 0 × F₁' 0) :
    (prodBundleMap Φ Φ' : ((E.prod E').prod (F.prod F')) 0 → ((E₁.prod E₁').prod (F₁.prod F₁')) 0) =
      ScBanach.bundleSwapOp E₁ F₁ E₁' F₁' 0 ∘ Prod.map Φ Φ' ∘ ScBanach.bundleSwapOp E E' F F' 0 :=
  rfl

lemma bundleSwap_mem_prod_univ {U : Set (E 0)} {U' : Set (E' 0)}
    {p : ((E.prod E').prod (F.prod F')) 0} (hp : p ∈ (U ×ˢ U') ×ˢ (univ : Set ((F.prod F') 0))) :
    bundleSwap p ∈ (U ×ˢ (univ : Set (F 0))) ×ˢ (U' ×ˢ (univ : Set (F' 0))) :=
  ⟨⟨hp.1.1, mem_univ _⟩, ⟨hp.1.2, mem_univ _⟩⟩

/-- Sc-smoothness of `Φ × Φ'` on `(U × U') ◁ (F ⊕ F')` from that of `Φ` and `Φ'`. -/
theorem isScSmooth_prodBundleMap {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)}
    {U' : Set (E' 0)} {Φ : E 0 × F 0 → E₁ 0 × F₁ 0} {Φ' : E' 0 × F' 0 → E₁' 0 × F₁' 0}
    (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    (h : IsScSmooth (E := E.prod F) (F := E₁.prod F₁) (U ×ˢ univ) Φ)
    (h' : IsScSmooth (E := E'.prod F') (F := E₁'.prod F₁') (U' ×ˢ univ) Φ') :
    IsScSmooth (E := (E.prod E').prod (F.prod F')) (F := (E₁.prod E₁').prod (F₁.prod F₁'))
      ((U ×ˢ U') ×ˢ univ) (prodBundleMap Φ Φ') := by
  have hD := ((hU.prod hU').prod_univ (F.prod F')).isScDomain
  have hUF := hU.prod_univ F
  have hUF' := hU'.prod_univ F'
  have hD' := (hUF.prod hUF').isScDomain
  have h1 := IsScSmooth.prodMap hUF.isScDomain hUF'.isScDomain hD' h h'
  have h2 := IsScSmooth.comp hD hD' h1 ((ScBanach.bundleSwapOp E E' F F').isScSmooth hD)
    fun p hp => bundleSwap_mem_prod_univ hp
  rw [prodBundleMap_eq]
  exact IsScSmooth.comp hD (isScDomain_univ _)
    ((ScBanach.bundleSwapOp E₁ F₁ E₁' F₁').isScSmooth (isScDomain_univ _)) h2 (mapsTo_univ _ _)

/-- The `[1]`-map of `Φ × Φ'` is the product of the `[1]`-maps at a point whose two fibre
images are in level `1`. -/
lemma shiftFiber_prodBundleMap {Φ : E 0 × F 0 → E₁ 0 × F₁ 0} {Φ' : E' 0 × F' 0 → E₁' 0 × F₁' 0}
    {p : ((E.prod E').prod (F.prod F').shift) 0}
    (h : (Φ (p.1.1, F.toBase 1 p.2.1)).2 ∈ range (F₁.toBase 1))
    (h' : (Φ' (p.1.2, F'.toBase 1 p.2.2)).2 ∈ range (F₁'.toBase 1)) :
    shiftFiber (E := E.prod E') (F := F.prod F') (E' := E₁.prod E₁') (F' := F₁.prod F₁')
      (prodBundleMap Φ Φ') p = prodBundleMap (shiftFiber Φ) (shiftFiber Φ') p := by
  change (_, invFun ((F₁.prod F₁').toBase 1)
    ((Φ (p.1.1, F.toBase 1 p.2.1)).2, (Φ' (p.1.2, F'.toBase 1 p.2.2)).2)) = _
  rw [ScBanach.invFun_prod_toBase_one h h']
  rfl

/-- **Products of strong bundle maps** (Definition 2.6.1 (preprint 2.47)): `Φ × Φ'` is a strong
bundle map `(U × U') ◁ (F ⊕ F') → (V × V') ◁ (F₁ ⊕ F₁')`. -/
theorem IsStrongBundleMap.prod {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)}
    {U' : Set (E' 0)} {V : Set (E₁ 0)} {V' : Set (E₁' 0)}
    {Φ : E 0 × F 0 → E₁ 0 × F₁ 0} {Φ' : E' 0 × F' 0 → E₁' 0 × F₁' 0}
    (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    (h : IsStrongBundleMap U V Φ) (h' : IsStrongBundleMap U' V' Φ') :
    IsStrongBundleMap (E := E.prod E') (F := F.prod F') (E' := E₁.prod E₁') (F' := F₁.prod F₁')
      (U ×ˢ U') (V ×ˢ V') (prodBundleMap Φ Φ') where
  mapsTo p hp := by
    have h1 := h.mapsTo (show (p.1.1, p.2.1) ∈ U ×ˢ univ from ⟨hp.1.1, mem_univ _⟩)
    have h2 := h'.mapsTo (show (p.1.2, p.2.2) ∈ U' ×ˢ univ from ⟨hp.1.2, mem_univ _⟩)
    exact ⟨⟨h1.1, h2.1⟩, mem_univ _⟩
  fst_independent u hu k k' := by
    change ((Φ (u.1, k.1)).1, (Φ' (u.2, k.2)).1) = ((Φ (u.1, k'.1)).1, (Φ' (u.2, k'.2)).1)
    rw [h.fst_independent u.1 hu.1 k.1 k'.1, h'.fst_independent u.2 hu.2 k.2 k'.2]
  fiber_linear u hu := by
    have l1 := h.fiber_linear u.1 hu.1
    have l2 := h'.fiber_linear u.2 hu.2
    constructor
    · intro k k'
      change ((Φ (u.1, k.1 + k'.1)).2, (Φ' (u.2, k.2 + k'.2)).2) =
        ((Φ (u.1, k.1)).2, (Φ' (u.2, k.2)).2) + ((Φ (u.1, k'.1)).2, (Φ' (u.2, k'.2)).2)
      rw [l1.map_add, l2.map_add]; rfl
    · intro a k
      change ((Φ (u.1, a • k.1)).2, (Φ' (u.2, a • k.2)).2) =
        a • ((Φ (u.1, k.1)).2, (Φ' (u.2, k.2)).2)
      rw [l1.map_smul, l2.map_smul]; rfl
  preserves_filtration m k hk u hu hum v hv := by
    rw [ScBanach.mem_range_prod_toBase] at hum hv
    have h1 := h.preserves_filtration m k hk u.1 hu.1 hum.1 v.1 hv.1
    have h2 := h'.preserves_filtration m k hk u.2 hu.2 hum.2 v.2 hv.2
    exact ⟨ScBanach.mem_range_prod_toBase.2 ⟨h1.1, h2.1⟩,
      ScBanach.mem_range_prod_toBase.2 ⟨h1.2, h2.2⟩⟩
  isScSmooth_zero := isScSmooth_prodBundleMap hU hU' h.isScSmooth_zero h'.isScSmooth_zero
  isScSmooth_one := by
    have hs := isScSmooth_prodBundleMap (F := F.shift) (F' := F'.shift) (F₁ := F₁.shift)
      (F₁' := F₁'.shift) hU hU' h.isScSmooth_one h'.isScSmooth_one
    have hD := ((hU.prod hU').prod_univ (F.prod F').shift).isScDomain
    refine hs.congr hD fun p hp => ?_
    exact (shiftFiber_prodBundleMap
      (h.preserves_filtration 0 1 le_add_self _ hp.1.1 ⟨_, rfl⟩ _ ⟨p.2.1, rfl⟩).2
      (h'.preserves_filtration 0 1 le_add_self _ hp.1.2 ⟨_, rfl⟩ _ ⟨p.2.2, rfl⟩).2).symm

end ProdBundleMap

/-! ### Products of strong bundle retractions and retracts -/

section ProdRetraction

variable {E F E' F' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)}
  {U' : Set (E' 0)} {R : E 0 × F 0 → E 0 × F 0} {R' : E' 0 × F' 0 → E' 0 × F' 0}

/-- **Products of strong bundle retractions** (Definition 2.6.1 (preprint 2.47)). -/
theorem IsStrongBundleRetraction.prod (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (hR : IsStrongBundleRetraction U R)
    (hR' : IsStrongBundleRetraction U' R') :
    IsStrongBundleRetraction (E := E.prod E') (F := F.prod F') (U ×ˢ U') (prodBundleMap R R') where
  toIsStrongBundleMap := hR.toIsStrongBundleMap.prod hU hU' hR'.toIsStrongBundleMap
  idem p hp := by
    have h1 := hR.idem (p.1.1, p.2.1) ⟨hp.1.1, mem_univ _⟩
    have h2 := hR'.idem (p.1.2, p.2.2) ⟨hp.1.2, mem_univ _⟩
    change bundleSwap (R (R (p.1.1, p.2.1)), R' (R' (p.1.2, p.2.2))) =
      bundleSwap (R (p.1.1, p.2.1), R' (p.1.2, p.2.2))
    rw [h1, h2]

/-- The base retraction of `R × R'` is the product `r × r'` of the base retractions. -/
theorem baseRetraction_prod (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    (hR : IsStrongBundleRetraction U R) (hR' : IsStrongBundleRetraction U' R') :
    (hR.prod hU hU' hR').baseRetraction (hU.prod hU') =
      (hR.baseRetraction hU).prod (hR'.baseRetraction hU') := rfl

theorem retract_baseRetraction_prod (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (hR : IsStrongBundleRetraction U R)
    (hR' : IsStrongBundleRetraction U' R') :
    ((hR.prod hU hU' hR').baseRetraction (hU.prod hU')).retract =
      (hR.baseRetraction hU).retract ×ˢ (hR'.baseRetraction hU').retract := by
  rw [baseRetraction_prod, ScRetraction.prod_retract]

/-- `(R × R')((U × U') ◁ (F ⊕ F')) = swap⁻¹(K × K')`. -/
theorem image_prodBundleMap :
    prodBundleMap R R' '' ((U ×ˢ U') ×ˢ (univ : Set ((F.prod F') 0))) =
      bundleSwap ⁻¹' ((R '' (U ×ˢ univ)) ×ˢ (R' '' (U' ×ˢ univ))) := by
  ext k
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨(p.1.1, p.2.1), ⟨hp.1.1, mem_univ _⟩, rfl⟩, ⟨(p.1.2, p.2.2), ⟨hp.1.2, mem_univ _⟩, rfl⟩⟩
  · rintro ⟨⟨q, hq, hqk⟩, ⟨q', hq', hqk'⟩⟩
    refine ⟨((q.1, q'.1), (q.2, q'.2)), ⟨⟨hq.1, hq'.1⟩, mem_univ _⟩, ?_⟩
    change bundleSwap (R q, R' q') = k
    rw [hqk, hqk']
    rfl

/-- **Products of local strong bundle retracts** (Definition 2.6.2 (preprint 2.48)): `K × K'`,
read in `(E ⊕ E') ◁ (F ⊕ F')` through the swap, is a local strong bundle retract of
`(C × C') ◁ (F ⊕ F')`. -/
theorem IsStrongBundleRetract.prod {K : Set (E 0 × F 0)} {K' : Set (E' 0 × F' 0)}
    (hK : IsStrongBundleRetract C K) (hK' : IsStrongBundleRetract C' K') :
    IsStrongBundleRetract (E := E.prod E') (F := F.prod F') (C ×ˢ C')
      (bundleSwap ⁻¹' (K ×ˢ K')) := by
  obtain ⟨U, R, hU, hR, rfl⟩ := hK
  obtain ⟨U', R', hU', hR', rfl⟩ := hK'
  exact ⟨U ×ˢ U', prodBundleMap R R', hU.prod hU', hR.prod hU hU' hR', image_prodBundleMap.symm⟩

end ProdRetraction

/-! ### Sc-smooth maps between products of local strong bundle retracts -/

section ProdRetractMaps

variable {E F E₁ F₁ E' F' E₁' F₁' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}
  {C₁ : Set (E₁ 0)} {C₁' : Set (E₁' 0)}

/-- **Products of sc-smooth maps between retracts of `E ◁ F`**: if `T : O → O₁` and
`T' : O' → O₁'` are sc-smooth, so is `T × T' : swap⁻¹(O × O') → swap⁻¹(O₁ × O₁')`. -/
theorem IsScSmoothRetractMap.prodBundleMap {O : Set (E 0 × F 0)} {O' : Set (E' 0 × F' 0)}
    {O₁ : Set (E₁ 0 × F₁ 0)} {O₁' : Set (E₁' 0 × F₁' 0)} {T : E 0 × F 0 → E₁ 0 × F₁ 0}
    {T' : E' 0 × F' 0 → E₁' 0 × F₁' 0}
    (hO : IsScRetract (E.prod F) (C ×ˢ univ) O) (hO' : IsScRetract (E'.prod F') (C' ×ˢ univ) O')
    (hO₁ : IsScRetract (E₁.prod F₁) (C₁ ×ˢ univ) O₁)
    (hO₁' : IsScRetract (E₁'.prod F₁') (C₁' ×ˢ univ) O₁')
    (hS : IsScRetract ((E.prod E').prod (F.prod F')) ((C ×ˢ C') ×ˢ univ) (bundleSwap ⁻¹' (O ×ˢ O')))
    (hT : IsScSmoothRetractMap (E.prod F) (C ×ˢ univ) O (E₁.prod F₁) (C₁ ×ˢ univ) O₁ T)
    (hT' : IsScSmoothRetractMap (E'.prod F') (C' ×ˢ univ) O' (E₁'.prod F₁') (C₁' ×ˢ univ) O₁' T') :
    IsScSmoothRetractMap ((E.prod E').prod (F.prod F')) ((C ×ˢ C') ×ˢ univ)
      (bundleSwap ⁻¹' (O ×ˢ O')) ((E₁.prod E₁').prod (F₁.prod F₁')) ((C₁ ×ˢ C₁') ×ˢ univ)
      (bundleSwap ⁻¹' (O₁ ×ˢ O₁')) (Polyfold.prodBundleMap T T') := by
  have hσ : IsScSmoothRetractMap ((E.prod E').prod (F.prod F')) ((C ×ˢ C') ×ˢ univ)
      (bundleSwap ⁻¹' (O ×ˢ O')) ((E.prod F).prod (E'.prod F'))
      ((C ×ˢ univ) ×ˢ (C' ×ˢ univ)) (O ×ˢ O') (ScBanach.bundleSwapOp E E' F F' 0) :=
    (ScBanach.bundleSwapOp E E' F F').isScSmoothRetractMap hS fun _ hp => hp
  have hTT := IsScSmoothRetractMap.prodMap hO hO' hT hT'
  have h1 := hTT.comp hσ (hO.prod hO')
  have hσ₁ : IsScSmoothRetractMap ((E₁.prod F₁).prod (E₁'.prod F₁'))
      ((C₁ ×ˢ univ) ×ˢ (C₁' ×ˢ univ)) (O₁ ×ˢ O₁') ((E₁.prod E₁').prod (F₁.prod F₁'))
      ((C₁ ×ˢ C₁') ×ˢ univ) (bundleSwap ⁻¹' (O₁ ×ˢ O₁')) (ScBanach.bundleSwapOp E₁ F₁ E₁' F₁' 0) :=
    (ScBanach.bundleSwapOp E₁ F₁ E₁' F₁').isScSmoothRetractMap (hO₁.prod hO₁') fun _ hp => hp
  exact hσ₁.comp h1 (hO₁.prod hO₁')

/-- `K[1]` of `swap⁻¹(K × K')` is `swap⁻¹(K[1] × K'[1])`. -/
lemma strongShiftOne_bundleSwap_preimage (O : Set (E 0 × F 0)) (O' : Set (E' 0 × F' 0)) :
    strongShiftOne (E := E.prod E') (F := F.prod F') (bundleSwap ⁻¹' (O ×ˢ O')) =
      bundleSwap ⁻¹' (strongShiftOne O ×ˢ strongShiftOne O') := rfl

end ProdRetractMaps

end Polyfold
