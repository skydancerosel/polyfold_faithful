import Polyfold.Chapter15.ProductBundleMap
import Polyfold.Chapter15.ProductEp
import Polyfold.Chapter8.EpStrongBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2021), §15.3, products remark after
**Definition 15.3.3** (pp. 692–693; 2017: after Definition 15.3): the product of strong bundles
over ep-groupoids, `(W × W', μ × μ') → X × X'` (gap G.160 (b)).

# The product strong bundle over the product ep-groupoid

## What is formalized

* `prodPullbackSplit`, `prodPullbackJoin`: the identification
  `(𝐗 × 𝐗') ₛ×_{P × P'} (W × W') ≅ (𝐗 ₛ×_P W) × (𝐗' ₛ×_{P'} W')`.
* `isStrongBundleMap_prodPullbackSplit` (it is a strong bundle map covering the identity of
  `𝐗 × 𝐗'`, on `[0]` and `[1]`), `isLocalScDiffeo_prodPullbackSplit`.
* `EpStrongBundle.prod`: **the product strong bundle `(W × W', μ × μ')` over `X × X'`**
  (Definition 8.3.1 (2017: 8.4)), with `μ × μ'((φ, φ'), (w, w')) = (μ(φ, w), μ'(φ', w'))`.
* `EpStrongBundle.IsScSmoothSectionFunctor.prod`, `IsScPlusSectionFunctor.prod`: products of
  sc-smooth (sc⁺) section functors are sc-smooth (sc⁺) section functors of the product
  (Definition 8.3.4 (2017: 8.7) (1), (2)).
-/

open Set Function

noncomputable section

namespace Polyfold

universe u u' v v'

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Obj' Mor' : Type u'} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  [ParacompactSpace (Obj × Obj')] [ParacompactSpace (Mor × Mor')]
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {W' : Type v'} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  [ParacompactSpace (W × W')]

/-! ### `(𝐗 × 𝐗') ₛ×_{P × P'} (W × W') ≅ (𝐗 ₛ×_P W) × (𝐗' ₛ×_{P'} W')` -/

/-- The splitting `((φ, φ'), (w, w')) ↦ ((φ, w), (φ', w'))`. -/
def prodPullbackSplit (X : EpGroupoid Obj Mor) (X' : EpGroupoid Obj' Mor')
    (q : pullbackSpace (Prod.map P P') (X.prod X').src) :
    pullbackSpace P X.src × pullbackSpace P' X'.src :=
  (⟨(q.1.1.1, q.1.2.1), show P q.1.2.1 = X.src q.1.1.1 from congrArg Prod.fst q.2⟩,
    ⟨(q.1.1.2, q.1.2.2), show P' q.1.2.2 = X'.src q.1.1.2 from congrArg Prod.snd q.2⟩)

/-- The inverse `((φ, w), (φ', w')) ↦ ((φ, φ'), (w, w'))`. -/
def prodPullbackJoin (X : EpGroupoid Obj Mor) (X' : EpGroupoid Obj' Mor')
    (z : pullbackSpace P X.src × pullbackSpace P' X'.src) :
    pullbackSpace (Prod.map P P') (X.prod X').src :=
  ⟨((z.1.1.1, z.2.1.1), (z.1.1.2, z.2.1.2)),
    show (P z.1.1.2, P' z.2.1.2) = (X.src z.1.1.1, X'.src z.2.1.1) from Prod.ext z.1.2 z.2.2⟩

omit [TopologicalSpace W] [T2Space W] [ParacompactSpace W] [∀ x, AddCommGroup (P ⁻¹' {x})]
  [∀ x, Module ℝ (P ⁻¹' {x})] [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W']
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] [ParacompactSpace (W × W')] in
@[simp] lemma prodPullbackJoin_split (q : pullbackSpace (Prod.map P P') (X.prod X').src) :
    prodPullbackJoin X X' (prodPullbackSplit X X' q) = q := rfl

omit [TopologicalSpace W] [T2Space W] [ParacompactSpace W] [∀ x, AddCommGroup (P ⁻¹' {x})]
  [∀ x, Module ℝ (P ⁻¹' {x})] [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W']
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] [ParacompactSpace (W × W')] in
@[simp] lemma prodPullbackSplit_join (z : pullbackSpace P X.src × pullbackSpace P' X'.src) :
    prodPullbackSplit X X' (prodPullbackJoin X X' z) = z := rfl

variable {B : StrongBundle X.PObj P} {B' : StrongBundle X'.PObj P'}

section Split

variable [ParacompactSpace (pullbackSpace P X.src)] [ParacompactSpace (pullbackSpace P' X'.src)]
  [ParacompactSpace (pullbackSpace (Prod.map P P') (X.prod X').src)]
  [ParacompactSpace (pullbackSpace P X.src × pullbackSpace P' X'.src)]

variable (B B') in
/-- The splitting on the `[1]`-levels, first factor. -/
def prodPullbackSplitOne₁ (y : ((B.prod B').pullback (X.prod X').isScSmoothMap_src).One) :
    (B.pullback X.isScSmoothMap_src).One :=
  (B.pullback X.isScSmoothMap_src).oneMk (prodPullbackSplit X X'
      (((B.prod B').pullback (X.prod X').isScSmoothMap_src).oneVal y)).1 <| by
    have h := ((B.prod B').mem_oneSet_pullback_iff (X.prod X').isScSmoothMap_src _).1
      (((B.prod B').pullback (X.prod X').isScSmoothMap_src).oneVal_mem y)
    exact (B.mem_oneSet_pullback_iff X.isScSmoothMap_src _).2 ((B.mem_oneSet_prod B').1 h).1

variable (B B') in
/-- The splitting on the `[1]`-levels, second factor. -/
def prodPullbackSplitOne₂ (y : ((B.prod B').pullback (X.prod X').isScSmoothMap_src).One) :
    (B'.pullback X'.isScSmoothMap_src).One :=
  (B'.pullback X'.isScSmoothMap_src).oneMk (prodPullbackSplit X X'
      (((B.prod B').pullback (X.prod X').isScSmoothMap_src).oneVal y)).2 <| by
    have h := ((B.prod B').mem_oneSet_pullback_iff (X.prod X').isScSmoothMap_src _).1
      (((B.prod B').pullback (X.prod X').isScSmoothMap_src).oneVal_mem y)
    exact (B'.mem_oneSet_pullback_iff X'.isScSmoothMap_src _).2 ((B.mem_oneSet_prod B').1 h).2

/-- **The splitting is a strong bundle map** `(𝐗 × 𝐗') ₛ×_{P × P'} (W × W') →
(𝐗 ₛ×_P W) × (𝐗' ₛ×_{P'} W')` covering the identity of `𝐗 × 𝐗'` (on `[0]` and `[1]`, by the
universal property of the pull-backs). -/
theorem isStrongBundleMap_prodPullbackSplit :
    ((B.prod B').pullback (X.prod X').isScSmoothMap_src).IsStrongBundleMap
      ((B.pullback X.isScSmoothMap_src).prod (B'.pullback X'.isScSmoothMap_src)) id
      (prodPullbackSplit X X') where
  covers _ := rfl
  fiber_linear m := by
    constructor
    · intro v w; rfl
    · intro a v; rfl
  isScSmoothMap := by
    have h₁ : ((B.prod B').pullback (X.prod X').isScSmoothMap_src).toMPolyfold0.IsScSmoothMap
        (B.pullback X.isScSmoothMap_src).toMPolyfold0 (fun q => (prodPullbackSplit X X' q).1) :=
      B.isScSmoothMap_to_pullback X.isScSmoothMap_src
        ((MPolyfold.isScSmoothMap_fst X.PMor X'.PMor).comp
          ((B.prod B').isScSmoothMap_pullbackProj (X.prod X').isScSmoothMap_src))
        ((MPolyfold.isScSmoothMap_fst B.toMPolyfold0 B'.toMPolyfold0).comp
          ((B.isScSmoothMap_id_prod_zero B').comp
            ((B.prod B').isScSmoothMap_pullbackProj' (X.prod X').isScSmoothMap_src)))
    have h₂ : ((B.prod B').pullback (X.prod X').isScSmoothMap_src).toMPolyfold0.IsScSmoothMap
        (B'.pullback X'.isScSmoothMap_src).toMPolyfold0 (fun q => (prodPullbackSplit X X' q).2) :=
      B'.isScSmoothMap_to_pullback X'.isScSmoothMap_src
        ((MPolyfold.isScSmoothMap_snd X.PMor X'.PMor).comp
          ((B.prod B').isScSmoothMap_pullbackProj (X.prod X').isScSmoothMap_src))
        ((MPolyfold.isScSmoothMap_snd B.toMPolyfold0 B'.toMPolyfold0).comp
          ((B.isScSmoothMap_id_prod_zero B').comp
            ((B.prod B').isScSmoothMap_pullbackProj' (X.prod X').isScSmoothMap_src)))
    exact ((B.pullback X.isScSmoothMap_src).isScSmoothMap_id_prod_zero_symm
      (B'.pullback X'.isScSmoothMap_src)).comp (MPolyfold.IsScSmoothOn.prodMk h₁ h₂)
  mapsTo_oneSet q hq := by
    have h := ((B.prod B').mem_oneSet_pullback_iff (X.prod X').isScSmoothMap_src q).1 hq
    have h' := (B.mem_oneSet_prod B').1 h
    exact ((B.pullback X.isScSmoothMap_src).mem_oneSet_prod (B'.pullback X'.isScSmoothMap_src)).2
      ⟨(B.mem_oneSet_pullback_iff X.isScSmoothMap_src _).2 h'.1,
        (B'.mem_oneSet_pullback_iff X'.isScSmoothMap_src _).2 h'.2⟩
  isScSmoothMap_one := by
    have := B.paracompactSpace_prod_one B'
    have := (B.pullback X.isScSmoothMap_src).paracompactSpace_prod_one
      (B'.pullback X'.isScSmoothMap_src)
    have h₁ : ((B.prod B').pullback (X.prod X').isScSmoothMap_src).toMPolyfold1.IsScSmoothMap
        (B.pullback X.isScSmoothMap_src).toMPolyfold1 (prodPullbackSplitOne₁ B B') :=
      B.isScSmoothMap_to_pullback_one X.isScSmoothMap_src
        ((MPolyfold.isScSmoothMap_fst X.PMor X'.PMor).comp
          (((B.prod B').isScSmoothMap_pullbackProj (X.prod X').isScSmoothMap_src).comp
            ((B.prod B').pullback (X.prod X').isScSmoothMap_src).isScSmoothMap_oneVal))
        ((MPolyfold.isScSmoothMap_fst B.toMPolyfold1 B'.toMPolyfold1).comp
          ((B.isScSmoothMap_prodOneHomeomorph B').comp
            ((B.prod B').isScSmoothMap_one_pullbackProj' (X.prod X').isScSmoothMap_src)))
    have h₂ : ((B.prod B').pullback (X.prod X').isScSmoothMap_src).toMPolyfold1.IsScSmoothMap
        (B'.pullback X'.isScSmoothMap_src).toMPolyfold1 (prodPullbackSplitOne₂ B B') :=
      B'.isScSmoothMap_to_pullback_one X'.isScSmoothMap_src
        ((MPolyfold.isScSmoothMap_snd X.PMor X'.PMor).comp
          (((B.prod B').isScSmoothMap_pullbackProj (X.prod X').isScSmoothMap_src).comp
            ((B.prod B').pullback (X.prod X').isScSmoothMap_src).isScSmoothMap_oneVal))
        ((MPolyfold.isScSmoothMap_snd B.toMPolyfold1 B'.toMPolyfold1).comp
          ((B.isScSmoothMap_prodOneHomeomorph B').comp
            ((B.prod B').isScSmoothMap_one_pullbackProj' (X.prod X').isScSmoothMap_src)))
    exact ((B.pullback X.isScSmoothMap_src).isScSmoothMap_prodOneHomeomorph_symm
      (B'.pullback X'.isScSmoothMap_src)).comp (MPolyfold.IsScSmoothOn.prodMk h₁ h₂)

/-- The splitting is an sc-diffeomorphism on `[0]` (its inverse is `prodPullbackJoin`), in
particular a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_prodPullbackSplit :
    ((B.prod B').pullback (X.prod X').isScSmoothMap_src).toMPolyfold0.IsLocalScDiffeo
      ((B.pullback X.isScSmoothMap_src).prod (B'.pullback X'.isScSmoothMap_src)).toMPolyfold0
      (prodPullbackSplit X X') := by
  have hj : ((B.pullback X.isScSmoothMap_src).prod
      (B'.pullback X'.isScSmoothMap_src)).toMPolyfold0.IsScSmoothMap
      ((B.prod B').pullback (X.prod X').isScSmoothMap_src).toMPolyfold0
      (prodPullbackJoin X X') :=
    (B.prod B').isScSmoothMap_to_pullback (X.prod X').isScSmoothMap_src
      ((B.pullback X.isScSmoothMap_src).prod (B'.pullback X'.isScSmoothMap_src)).isScSmoothMap_proj
      (StrongBundle.isScSmoothMap_prodMap_zero
        (B.isScSmoothMap_pullbackProj' X.isScSmoothMap_src)
        (B'.isScSmoothMap_pullbackProj' X'.isScSmoothMap_src))
  exact fun _ => ⟨univ, univ, prodPullbackJoin X X', mem_univ _,
    ⟨isStrongBundleMap_prodPullbackSplit.isScSmoothMap, hj, mapsTo_univ _ _, mapsTo_univ _ _,
      fun _ _ => rfl, fun _ _ => rfl⟩⟩

end Split

namespace EpStrongBundle

variable (E : EpStrongBundle X B) (E' : EpStrongBundle X' B')

/-- The structure map `μ × μ'((φ, φ'), (w, w')) = (μ(φ, w), μ'(φ', w'))`. -/
def prodμ (q : pullbackSpace (Prod.map P P') (X.prod X').src) : W × W' :=
  Prod.map E.μ E'.μ (prodPullbackSplit X X' q)

/-- **The product strong bundle over the product ep-groupoid** (Definition 8.3.1 (2017: 8.4);
used in the products remark after Definition 15.3.3, p. 692): the product strong bundle
`W × W' → X × X'` with the structure map `μ × μ'`. -/
def prod : EpStrongBundle (X.prod X') (B.prod B') where
  μ := E.prodμ E'
  isStrongBundleMap := by
    have := B.paracompactSpace_pullback X.PMor X.src
    have := B'.paracompactSpace_pullback X'.PMor X'.src
    have := (B.prod B').paracompactSpace_pullback (X.prod X').PMor (X.prod X').src
    have := (B.pullback X.isScSmoothMap_src).paracompactSpace_prod
      (B'.pullback X'.isScSmoothMap_src)
    exact (StrongBundle.IsStrongBundleMap.prod E.isStrongBundleMap E'.isStrongBundleMap).comp
      isStrongBundleMap_prodPullbackSplit
  surjective w := by
    obtain ⟨q, hq⟩ := E.surjective w.1
    obtain ⟨q', hq'⟩ := E'.surjective w.2
    exact ⟨prodPullbackJoin X X' (q, q'), Prod.ext hq hq'⟩
  isLocalScDiffeo := by
    have := B.paracompactSpace_pullback X.PMor X.src
    have := B'.paracompactSpace_pullback X'.PMor X'.src
    have := (B.prod B').paracompactSpace_pullback (X.prod X').PMor (X.prod X').src
    have := (B.pullback X.isScSmoothMap_src).paracompactSpace_prod
      (B'.pullback X'.isScSmoothMap_src)
    have hid₀ : ((B.pullback X.isScSmoothMap_src).prod
        (B'.pullback X'.isScSmoothMap_src)).toMPolyfold0.IsLocalScDiffeo
        ((B.pullback X.isScSmoothMap_src).toMPolyfold0.prod
          (B'.pullback X'.isScSmoothMap_src).toMPolyfold0) id := fun _ =>
      ⟨univ, univ, id, mem_univ _, ⟨(B.pullback X.isScSmoothMap_src).isScSmoothMap_id_prod_zero
        (B'.pullback X'.isScSmoothMap_src),
        (B.pullback X.isScSmoothMap_src).isScSmoothMap_id_prod_zero_symm
        (B'.pullback X'.isScSmoothMap_src), mapsTo_univ _ _, mapsTo_univ _ _, fun _ _ => rfl,
        fun _ _ => rfl⟩⟩
    have hid₁ : (B.toMPolyfold0.prod B'.toMPolyfold0).IsLocalScDiffeo (B.prod B').toMPolyfold0 id :=
      fun _ => ⟨univ, univ, id, mem_univ _, ⟨B.isScSmoothMap_id_prod_zero_symm B',
        B.isScSmoothMap_id_prod_zero B', mapsTo_univ _ _, mapsTo_univ _ _, fun _ _ => rfl,
        fun _ _ => rfl⟩⟩
    have hμ := MPolyfold.IsLocalScDiffeo.prodMap E.isLocalScDiffeo E'.isLocalScDiffeo
    exact (hid₁.comp (hμ.comp hid₀)).comp isLocalScDiffeo_prodPullbackSplit
  μ_unit w := Prod.ext (E.μ_unit w.1) (E'.μ_unit w.2)
  μ_comp ψ γ w h₁ h₂ := Prod.ext
    (E.μ_comp ψ.1 γ.1 w.1 (congrArg Prod.fst h₁) (congrArg Prod.fst h₂))
    (E'.μ_comp ψ.2 γ.2 w.2 (congrArg Prod.snd h₁) (congrArg Prod.snd h₂))

lemma prod_μ (q : pullbackSpace (Prod.map P P') (X.prod X').src) :
    (E.prod E').μ q = (E.μ (prodPullbackSplit X X' q).1, E'.μ (prodPullbackSplit X X' q).2) :=
  rfl

variable {E E'}

/-- The functoriality condition of Definition 8.3.4 (2017: 8.7) holds for `f × f'` if it holds for
`f` and `f'`. -/
theorem IsFunctorialSection.prod {f : Obj → W} {f' : Obj' → W'} {hf : IsSection P f}
    {hf' : IsSection P' f'} (h : E.IsFunctorialSection hf) (h' : E'.IsFunctorialSection hf') :
    (E.prod E').IsFunctorialSection (hf.prodMap hf') :=
  fun φ => Prod.ext (h φ.1) (h' φ.2)

/-- **Products of sc-smooth section functors** (Definition 8.3.4 (2017: 8.7) (1)): `f × f'` is an
sc-smooth section functor of `(W × W', μ × μ')`. -/
theorem IsScSmoothSectionFunctor.prod {f : Obj → W} {f' : Obj' → W'}
    (h : E.IsScSmoothSectionFunctor f) (h' : E'.IsScSmoothSectionFunctor f') :
    (E.prod E').IsScSmoothSectionFunctor (Prod.map f f') := by
  obtain ⟨hf, hfun⟩ := h
  obtain ⟨hf', hfun'⟩ := h'
  exact ⟨hf.prod hf', hfun.prod hfun'⟩

/-- **Products of sc⁺-section functors** (Definition 8.3.4 (2017: 8.7) (2)). -/
theorem IsScPlusSectionFunctor.prod {f : Obj → W} {f' : Obj' → W'}
    (h : E.IsScPlusSectionFunctor f) (h' : E'.IsScPlusSectionFunctor f') :
    (E.prod E').IsScPlusSectionFunctor (Prod.map f f') :=
  ⟨h.1.prod h'.1, h.2.prod h'.2⟩

end EpStrongBundle

end Polyfold
