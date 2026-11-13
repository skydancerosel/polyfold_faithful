import Polyfold.Chapter7.EpGroupoid
import Polyfold.Chapter7.Discrete

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III: the product of
two ep-groupoids, used without definition in the text after Definition 15.3.3 (p. 692, `X × X'`
for the product of two Fredholm problems), in Remark 15.3.4 (p. 693) and in Corollary 15.3.10
(p. 699, the tame ep-groupoid `[0, 1] × X`).  Part III plan, missing prerequisite (e).

# The product ep-groupoid `X × X'`

## Reading

The text takes products of ep-groupoids for granted.  We read `X × X'` as the groupoid with
object set `X × X'` and morphism set `𝐗 × 𝐗'`, every structure map taken componentwise, and the
product M-polyfold structures (`MPolyfold.prod`, Exposition Lemma 4.D) on objects and morphisms.

## What is formalized

* `GroupoidStr.prod`: the componentwise groupoid.
* `MPolyfold.IsScSmoothOn.prodMap`, `MPolyfold.IsScDiffeoOn.prodMap`,
  `MPolyfold.IsLocalScDiffeo.prodMap`: products of sc-smooth maps, of sc-diffeomorphisms
  between open sets, and of local sc-diffeomorphisms.
* `isProperMap_domRestrict_prod`: products of restricted proper maps are proper.
* **`EpGroupoid.prod`**: `X × X'` is an ep-groupoid (Definition 7.1.3 (1)–(4)).  Condition (4)
  is checked in the sheet form (`isScSmoothComp_iff_sheet`): near a morphism, the first component
  of a sheet inverse of `s × s'` is a sheet inverse of `s` composed with `t`.
* `EpGroupoid.prodFst`, `EpGroupoid.prodSnd`: the projections, sc-smooth functors.
* `EpGroupoid.isTame_prod`, `EpGroupoid.degIndex_prod`: `X × X'` is tame for tame `X`, `X'`,
  with `d_{X × X'}(x, x') = d_X(x) + d_{X'}(x')`.
* `EpGroupoid.prod_π_eq_π_iff`: two objects of `X × X'` are isomorphic iff their components are.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v

/-! ### The componentwise groupoid -/

namespace GroupoidStr

variable {Obj Mor : Type u} {Obj' Mor' : Type v}

/-- **The product groupoid** `G × G'`: objects `Obj × Obj'`, morphisms `Mor × Mor'`, all
structure maps componentwise. -/
def prod (G : GroupoidStr Obj Mor) (G' : GroupoidStr Obj' Mor') :
    GroupoidStr (Obj × Obj') (Mor × Mor') where
  src φ := (G.src φ.1, G'.src φ.2)
  tgt φ := (G.tgt φ.1, G'.tgt φ.2)
  comp φ ψ := (G.comp φ.1 ψ.1, G'.comp φ.2 ψ.2)
  unit x := (G.unit x.1, G'.unit x.2)
  inv φ := (G.inv φ.1, G'.inv φ.2)
  src_comp _ _ h := Prod.ext (G.src_comp _ _ (congrArg Prod.fst h))
    (G'.src_comp _ _ (congrArg Prod.snd h))
  tgt_comp _ _ h := Prod.ext (G.tgt_comp _ _ (congrArg Prod.fst h))
    (G'.tgt_comp _ _ (congrArg Prod.snd h))
  comp_assoc _ _ _ h₁ h₂ := Prod.ext
    (G.comp_assoc _ _ _ (congrArg Prod.fst h₁) (congrArg Prod.fst h₂))
    (G'.comp_assoc _ _ _ (congrArg Prod.snd h₁) (congrArg Prod.snd h₂))
  src_unit _ := Prod.ext (G.src_unit _) (G'.src_unit _)
  tgt_unit _ := Prod.ext (G.tgt_unit _) (G'.tgt_unit _)
  comp_unit _ := Prod.ext (G.comp_unit _) (G'.comp_unit _)
  unit_comp _ := Prod.ext (G.unit_comp _) (G'.unit_comp _)
  src_inv _ := Prod.ext (G.src_inv _) (G'.src_inv _)
  tgt_inv _ := Prod.ext (G.tgt_inv _) (G'.tgt_inv _)
  comp_inv _ := Prod.ext (G.comp_inv _) (G'.comp_inv _)
  inv_comp _ := Prod.ext (G.inv_comp _) (G'.inv_comp _)

variable (G : GroupoidStr Obj Mor) (G' : GroupoidStr Obj' Mor')

@[simp] theorem prod_src (φ : Mor × Mor') : (G.prod G').src φ = (G.src φ.1, G'.src φ.2) := rfl
@[simp] theorem prod_tgt (φ : Mor × Mor') : (G.prod G').tgt φ = (G.tgt φ.1, G'.tgt φ.2) := rfl
@[simp] theorem prod_comp (φ ψ : Mor × Mor') :
    (G.prod G').comp φ ψ = (G.comp φ.1 ψ.1, G'.comp φ.2 ψ.2) := rfl
@[simp] theorem prod_unit (x : Obj × Obj') : (G.prod G').unit x = (G.unit x.1, G'.unit x.2) := rfl
@[simp] theorem prod_inv (φ : Mor × Mor') : (G.prod G').inv φ = (G.inv φ.1, G'.inv φ.2) := rfl

end GroupoidStr

/-! ### Products of sc-smooth maps and of local sc-diffeomorphisms -/

namespace MPolyfold

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {P' : MPolyfold X'}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {Q' : MPolyfold Y'}
  [ParacompactSpace (X × X')] [ParacompactSpace (Y × Y')]

/-- The product `f × g` of sc-smooth maps is sc-smooth on `U × U'`. -/
theorem IsScSmoothOn.prodMap {f : X → Y} {g : X' → Y'} {U : Set X} {U' : Set X'}
    (hf : P.IsScSmoothOn Q f U) (hg : P'.IsScSmoothOn Q' g U') :
    (P.prod P').IsScSmoothOn (Q.prod Q') (Prod.map f g) (U ×ˢ U') := by
  have hUU' : IsOpen (U ×ˢ U') := hf.isOpen.prod hg.isOpen
  have h1 : (P.prod P').IsScSmoothOn Q (f ∘ Prod.fst) (U ×ˢ U') :=
    hf.comp ((isScSmoothMap_fst P P').mono hUU' (subset_univ _)) fun p hp => hp.1
  have h2 : (P.prod P').IsScSmoothOn Q' (g ∘ Prod.snd) (U ×ˢ U') :=
    hg.comp ((isScSmoothMap_snd P P').mono hUU' (subset_univ _)) fun p hp => hp.2
  exact h1.prodMk h2

/-- The product of sc-diffeomorphisms between open sets is one. -/
theorem IsScDiffeoOn.prodMap {f : X → Y} {h : Y → X} {g : X' → Y'} {h' : Y' → X'} {U : Set X}
    {V : Set Y} {U' : Set X'} {V' : Set Y'} (hf : P.IsScDiffeoOn Q f h U V)
    (hg : P'.IsScDiffeoOn Q' g h' U' V') :
    (P.prod P').IsScDiffeoOn (Q.prod Q') (Prod.map f g) (Prod.map h h') (U ×ˢ U') (V ×ˢ V') where
  isScSmoothOn := hf.isScSmoothOn.prodMap hg.isScSmoothOn
  isScSmoothOn_inv := hf.isScSmoothOn_inv.prodMap hg.isScSmoothOn_inv
  mapsTo := hf.mapsTo.prodMap hg.mapsTo
  mapsTo_inv := hf.mapsTo_inv.prodMap hg.mapsTo_inv
  left_inv _ hp := Prod.ext (hf.left_inv _ hp.1) (hg.left_inv _ hp.2)
  right_inv _ hp := Prod.ext (hf.right_inv _ hp.1) (hg.right_inv _ hp.2)

/-- The product of local sc-diffeomorphisms is a local sc-diffeomorphism. -/
theorem IsLocalScDiffeo.prodMap {f : X → Y} {g : X' → Y'} (hf : P.IsLocalScDiffeo Q f)
    (hg : P'.IsLocalScDiffeo Q' g) : (P.prod P').IsLocalScDiffeo (Q.prod Q') (Prod.map f g) :=
  fun p => by
    obtain ⟨U, V, h, hx, hd⟩ := hf p.1
    obtain ⟨U', V', h', hx', hd'⟩ := hg p.2
    exact ⟨U ×ˢ U', V ×ˢ V', Prod.map h h', ⟨hx, hx'⟩, hd.prodMap hd'⟩

end MPolyfold

/-! ### Proper maps on products of subsets -/

/-- The restriction of `f × g` to `s × t` is proper if the restrictions of `f` to `s` and of `g`
to `t` are. -/
theorem isProperMap_domRestrict_prod {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] [TopologicalSpace δ] {f : α → β} {g : γ → δ} {s : Set α} {t : Set γ}
    (hf : IsProperMap (s.domRestrict f)) (hg : IsProperMap (t.domRestrict g)) :
    IsProperMap ((s ×ˢ t).domRestrict (Prod.map f g)) :=
  (hf.prodMap hg).comp (Homeomorph.Set.prod s t).isProperMap

/-! ### The product ep-groupoid -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] (X' : EpGroupoid Obj' Mor')
  [ParacompactSpace (Obj × Obj')] [ParacompactSpace (Mor × Mor')]

/-- `s × s'`, as a map, is the source map of the product. -/
theorem prod_src_eq : (X.toGroupoidStr.prod X'.toGroupoidStr).src = Prod.map X.src X'.src := rfl

theorem prod_tgt_eq : (X.toGroupoidStr.prod X'.toGroupoidStr).tgt = Prod.map X.tgt X'.tgt := rfl

/-- Condition (3) of Definition 7.1.3 for the product: with `V × V'`. -/
theorem prod_exists_isProperMap (x : Obj × Obj') : ∃ V : Set (Obj × Obj'), IsOpen V ∧ x ∈ V ∧
    IsProperMap (((X.toGroupoidStr.prod X'.toGroupoidStr).src ⁻¹' closure V).domRestrict
      (X.toGroupoidStr.prod X'.toGroupoidStr).tgt) := by
  obtain ⟨V, hV, hxV, hp⟩ := X.exists_isProperMap x.1
  obtain ⟨V', hV', hxV', hp'⟩ := X'.exists_isProperMap x.2
  refine ⟨V ×ˢ V', hV.prod hV', ⟨hxV, hxV'⟩, ?_⟩
  have hset : (X.toGroupoidStr.prod X'.toGroupoidStr).src ⁻¹' closure (V ×ˢ V') =
      (X.src ⁻¹' closure V) ×ˢ (X'.src ⁻¹' closure V') := by
    rw [closure_prod_eq]; rfl
  rw [hset]
  exact isProperMap_domRestrict_prod hp hp'

/-- Condition (4) of Definition 7.1.3 for the product, in the sheet form. -/
theorem prod_isScSmoothCompSheet :
    IsScSmoothCompSheet (X.PObj.prod X'.PObj) (X.PMor.prod X'.PMor)
      (X.toGroupoidStr.prod X'.toGroupoidStr).src (X.toGroupoidStr.prod X'.toGroupoidStr).tgt
      (X.toGroupoidStr.prod X'.toGroupoidStr).comp := by
  intro σ W V hd
  set G := X.toGroupoidStr.prod X'.toGroupoidStr
  have htc : Continuous G.tgt := X.continuous_tgt.prodMap X'.continuous_tgt
  have hVo : IsOpen (G.tgt ⁻¹' V) := hd.isScSmoothOn_inv.isOpen.preimage htc
  refine MPolyfold.IsScSmoothOn.of_locally hVo fun ψ₀ hψ₀ => ?_
  -- sheets of `s` and `s'` at the components of `σ(t ψ₀)`
  set a₀ := σ (G.tgt ψ₀)
  obtain ⟨U₁, V₁, h₁, ha₁, hd₁⟩ := X.isLocalScDiffeo_src a₀.1
  obtain ⟨U₂, V₂, h₂, ha₂, hd₂⟩ := X'.isLocalScDiffeo_src a₀.2
  have hσc : ContinuousOn (fun ψ => σ (G.tgt ψ)) (G.tgt ⁻¹' V) :=
    hd.isScSmoothOn_inv.continuousOn.comp htc.continuousOn fun _ h => h
  set O := G.tgt ⁻¹' V ∩ (fun ψ => σ (G.tgt ψ)) ⁻¹' (U₁ ×ˢ U₂) with hOdef
  have hOo : IsOpen O :=
    hσc.isOpen_inter_preimage hVo (hd₁.isScSmoothOn.isOpen.prod hd₂.isScSmoothOn.isOpen)
  have hψO : ψ₀ ∈ O := ⟨hψ₀, ha₁, ha₂⟩
  -- on `O`, `σ(t ψ) = (h₁(t ψ.1), h₂(t' ψ.2))`
  have hsrc : ∀ ψ ∈ O, G.src (σ (G.tgt ψ)) = G.tgt ψ := fun ψ hψ => hd.right_inv _ hψ.1
  have hσ₁ : ∀ ψ ∈ O, (σ (G.tgt ψ)).1 = h₁ (X.tgt ψ.1) := fun ψ hψ => by
    have := congrArg Prod.fst (hsrc ψ hψ)
    change X.src (σ (G.tgt ψ)).1 = X.tgt ψ.1 at this
    rw [← this, hd₁.left_inv _ hψ.2.1]
  have hσ₂ : ∀ ψ ∈ O, (σ (G.tgt ψ)).2 = h₂ (X'.tgt ψ.2) := fun ψ hψ => by
    have := congrArg Prod.snd (hsrc ψ hψ)
    change X'.src (σ (G.tgt ψ)).2 = X'.tgt ψ.2 at this
    rw [← this, hd₂.left_inv _ hψ.2.2]
  have ht₁ : ∀ ψ ∈ O, X.tgt ψ.1 ∈ V₁ := fun ψ hψ => by
    have := congrArg Prod.fst (hsrc ψ hψ)
    change X.src (σ (G.tgt ψ)).1 = X.tgt ψ.1 at this
    rw [← this]; exact hd₁.mapsTo hψ.2.1
  have ht₂ : ∀ ψ ∈ O, X'.tgt ψ.2 ∈ V₂ := fun ψ hψ => by
    have := congrArg Prod.snd (hsrc ψ hψ)
    change X'.src (σ (G.tgt ψ)).2 = X'.tgt ψ.2 at this
    rw [← this]; exact hd₂.mapsTo hψ.2.2
  have k₁ := X.isScSmoothCompSheet h₁ U₁ V₁ hd₁
  have k₂ := X'.isScSmoothCompSheet h₂ U₂ V₂ hd₂
  have c₁ : (X.PMor.prod X'.PMor).IsScSmoothOn X.PMor
      ((fun φ => X.comp (h₁ (X.tgt φ)) φ) ∘ Prod.fst) O :=
    k₁.comp ((MPolyfold.isScSmoothMap_fst X.PMor X'.PMor).mono hOo (subset_univ _))
      fun ψ hψ => ht₁ ψ hψ
  have c₂ : (X.PMor.prod X'.PMor).IsScSmoothOn X'.PMor
      ((fun φ => X'.comp (h₂ (X'.tgt φ)) φ) ∘ Prod.snd) O :=
    k₂.comp ((MPolyfold.isScSmoothMap_snd X.PMor X'.PMor).mono hOo (subset_univ _))
      fun ψ hψ => ht₂ ψ hψ
  refine ⟨O, hOo, hψO, fun ψ hψ => hψ.1, (c₁.prodMk c₂).congr fun ψ hψ => ?_⟩
  change (X.comp (h₁ (X.tgt ψ.1)) ψ.1, X'.comp (h₂ (X'.tgt ψ.2)) ψ.2) =
    (X.comp (σ (G.tgt ψ)).1 ψ.1, X'.comp (σ (G.tgt ψ)).2 ψ.2)
  rw [hσ₁ ψ hψ, hσ₂ ψ hψ]

/-- **The product ep-groupoid `X × X'`** (used in the text after Definition 15.3.3, p. 692, and in
Corollary 15.3.10, p. 699): objects `X × X'`, morphisms `𝐗 × 𝐗'`, structure maps componentwise,
the product M-polyfold structures. -/
def prod : EpGroupoid (Obj × Obj') (Mor × Mor') where
  toGroupoidStr := X.toGroupoidStr.prod X'.toGroupoidStr
  PObj := X.PObj.prod X'.PObj
  PMor := X.PMor.prod X'.PMor
  isLocalScDiffeo_src := X.isLocalScDiffeo_src.prodMap X'.isLocalScDiffeo_src
  isLocalScDiffeo_tgt := X.isLocalScDiffeo_tgt.prodMap X'.isLocalScDiffeo_tgt
  isScSmoothMap_unit := by
    have h := X.isScSmoothMap_unit.prodMap X'.isScSmoothMap_unit
    rw [univ_prod_univ] at h
    exact h
  isScSmoothMap_inv := by
    have h := X.isScSmoothMap_inv.prodMap X'.isScSmoothMap_inv
    rw [univ_prod_univ] at h
    exact h
  exists_isProperMap := prod_exists_isProperMap X X'
  isScSmoothComp := (isScSmoothComp_iff_sheet _ _).2 (prod_isScSmoothCompSheet X X')

variable {X X'}

@[simp] theorem prod_PObj : (X.prod X').PObj = X.PObj.prod X'.PObj := rfl
@[simp] theorem prod_PMor : (X.prod X').PMor = X.PMor.prod X'.PMor := rfl
@[simp] theorem prod_src' (φ : Mor × Mor') : (X.prod X').src φ = (X.src φ.1, X'.src φ.2) := rfl
@[simp] theorem prod_tgt' (φ : Mor × Mor') : (X.prod X').tgt φ = (X.tgt φ.1, X'.tgt φ.2) := rfl
@[simp] theorem prod_comp' (φ ψ : Mor × Mor') :
    (X.prod X').comp φ ψ = (X.comp φ.1 ψ.1, X'.comp φ.2 ψ.2) := rfl
@[simp] theorem prod_unit' (x : Obj × Obj') : (X.prod X').unit x = (X.unit x.1, X'.unit x.2) :=
  rfl
@[simp] theorem prod_inv' (φ : Mor × Mor') : (X.prod X').inv φ = (X.inv φ.1, X'.inv φ.2) := rfl

variable (X X')

/-- The first projection `X × X' → X`, an sc-smooth functor. -/
def prodFst : EpFunctor (X.prod X') X where
  obj := Prod.fst
  mor := Prod.fst
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_fst X.PObj X'.PObj
  isScSmoothMap_mor := MPolyfold.isScSmoothMap_fst X.PMor X'.PMor

/-- The second projection `X × X' → X'`, an sc-smooth functor. -/
def prodSnd : EpFunctor (X.prod X') X' where
  obj := Prod.snd
  mor := Prod.snd
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_snd X.PObj X'.PObj
  isScSmoothMap_mor := MPolyfold.isScSmoothMap_snd X.PMor X'.PMor

@[simp] theorem prodFst_obj : (prodFst X X').obj = Prod.fst := rfl
@[simp] theorem prodSnd_obj : (prodSnd X X').obj = Prod.snd := rfl

/-- **The product of tame ep-groupoids is tame**, with `d_{X × X'}(x, x') = d_X(x) + d_{X'}(x')`
(Exposition Lemma 4.D, `MPolyfold.isTame_prod`). -/
theorem isTame_prod (hX : X.IsTame) (hX' : X'.IsTame) : (X.prod X').IsTame :=
  (MPolyfold.isTame_prod X.PObj X'.PObj hX hX').1

theorem degIndex_prod (hX : X.IsTame) (hX' : X'.IsTame) (x : Obj) (x' : Obj') :
    (X.prod X').PObj.degIndex (x, x') = X.PObj.degIndex x + X'.PObj.degIndex x' :=
  (MPolyfold.isTame_prod X.PObj X'.PObj hX hX').2 x x'

/-- Two objects of `X × X'` are isomorphic iff their components are. -/
theorem prod_π_eq_π_iff (p q : Obj × Obj') :
    (X.prod X').π p = (X.prod X').π q ↔ X.π p.1 = X.π q.1 ∧ X'.π p.2 = X'.π q.2 := by
  simp only [GroupoidStr.π_eq_π_iff]
  constructor
  · rintro ⟨φ, hs, ht⟩
    exact ⟨⟨φ.1, congrArg Prod.fst hs, congrArg Prod.fst ht⟩,
      ⟨φ.2, congrArg Prod.snd hs, congrArg Prod.snd ht⟩⟩
  · rintro ⟨⟨φ, hs, ht⟩, ⟨φ', hs', ht'⟩⟩
    exact ⟨(φ, φ'), Prod.ext hs hs', Prod.ext ht ht'⟩

end EpGroupoid

end Polyfold
