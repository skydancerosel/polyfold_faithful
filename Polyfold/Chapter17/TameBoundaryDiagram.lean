import Polyfold.Chapter17.TameBoundaryPolyfold
import Polyfold.Chapter17.ModelComparison
import Polyfold.Chapter7.TameBoundaryEpStructure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.4 (pp. 811–812, unnumbered): **the diagram `bX → bC` over `X → C`**.

## The text, paraphrased

(p. 811) Choosing a covering family `Ψ` (with `V(ō)` in place of `O` at boundary points) one
builds the ep-groupoid `X = X_Ψ` with the equivalence `Γ : X → C` of Lemma 17.1.15; taking only
the uniformizers over the boundary one builds an ep-groupoid `bX`.  (p. 812) This gives the
commutative diagram
```
        bΓ
   bX ────→ bC
   │F        │B
   ↓         ↓
   X  ────→  C
        Γ
```
whose horizontal arrows are equivalences of categories and whose vertical arrows are the tame
boundary constructions, in the ep-groupoid context and in the polyfold context.  Two covering
families give two such diagrams; both embed into the diagram of their union.

## What is formalized

* In namespace `Polyfold.TameBoundary`: `IsLiftOf.symm_of_isScDiffeoOn` (a lift along `f` is a
  lift back along the inverse of an sc-diffeomorphism `f : U → V`),
  `exists_isLiftOf_of_isScDiffeoOn`
  (every face germ over `V` comes from one over `U`), `IsLiftOf.inj_of_isScDiffeoOn`.
* In namespace `Polyfold.GCT.PolyfoldConstruction`, for a tame polyfold structure with
  `F(α) ≠ ∅` and a family `Ψ : ι → S.Unif`:
  - `IsComponentGerm` (a face germ `p` of `X = ⊔ O_λ` is the image of a face germ `q` of `O_λ`),
    `exists_isComponentGerm`, `IsComponentGerm.sigma_eq` (`(λ, q)` is unique), `componentGerm`;
  - `bdryModelObj` (`bΓ` on objects: `p ↦ ptObj q`, the object of `bC` given by `q`),
    `germLift_of_isComponentGerm` (a face germ of the morphism M-polyfold `𝐗` over `(x, φ, x')`
    carries the germs of its source and target as in Definition 17.4.3 (2)),
    `bLift_bdryModelObj`;
  - **`bdryModelFunctor`** (`bΓ : bX → bC` as a functor), **`bdryModelFunctor_square`**
    (`B ∘ bΓ = Γ ∘ F`), `bdryModelFunctor_faithful`, `bdryModelFunctor_full`,
    `bdryModelFunctor_essSurj` (for a covering family), **`bdryModelFunctor_isEquivalence`**,
    `bijective_orbitMap_bdryModelFunctor`;
  - **`bdryModelObj_modelMap`**: for `Ψ = Φ ∘ σ` the lift `b(X_Ψ) → b(X_Φ)` of the reindexing
    functor `X_Ψ → X_Φ` commutes with `bΓ` (the embedding into the diagram of the union);
  - **`diagram_bX_bC`**: the whole statement of p. 812; witness `swap_diagram_bX_bC`
    (`ℤ/2 ⋉ ([0,∞)² ⊕ W)`, `bX` non-empty).

## Readings

* `bX` is read as the tame boundary ep-groupoid of the ep-groupoid `X = X_Ψ` (Theorem 7.6.9,
  `EpGroupoid.boundaryEpGroupoid`; `X_Ψ` is tame by Theorem 17.1.14), and `F : bX → X` as its
  forgetful ep-functor `B` (`boundaryEpFunctor`): "the vertical arrows are the tame boundary
  constructions, one in the ep-groupoid context and the other in the polyfold context".
  An object of `bX` over `(λ, x)` is a face germ of `⊔ O_λ` at `(λ, x)`; it is the image of a
  unique face germ `q` of `O_λ` at `x` (`IsComponentGerm`), and `bΓ` sends it to the object of
  `bC` given by `q` (`ptObj`, the class `[Ψ_λ(x), Ψ_λ, U(x), θ]` of (17.57)).  A morphism of `bX`
  over `(x, φ, x')` goes to `φ` with these source and target objects.
* "The horizontal arrows are equivalences of categories": `bΓ` is full, faithful and essentially
  surjective (the functor `Γ` of Lemma 17.1.15 is one as well); the replacement of `O` by `V(ō)`
  is not needed for this, the family being any covering family.
* "The two initial constructions embed into the diagram associated to the union": the reindexing
  functors `X_{Φ ∘ σ} → X_Φ` (in particular the two inclusions into `X_{Ψ ⊔ Ψ'}`, Theorem
  17.1.18) are local sc-diffeomorphisms on objects, so they lift to the face germs
  (`TameBoundary.bLift`), and the lift commutes with `bΓ` (`bdryModelObj_modelMap`).
* The polyfold structure `(F_bC, M)` of Theorem 17.4.26 enters only through the GCT `bC`; the
  diagram is one of categories, which is what the text asserts of it.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

universe u v

namespace Polyfold

namespace TameBoundary

section Inverse

variable {A : Type u} [TopologicalSpace A] [T2Space A] [ParacompactSpace A] {P : MPolyfold A}
  {B : Type v} [TopologicalSpace B] [T2Space B] [ParacompactSpace B] {Q : MPolyfold B}
  {f : A → B} {g : B → A} {U : Set A} {V : Set B}

variable {hP : IsCornerIndex P.degIndex} {hQ : IsCornerIndex Q.degIndex}

/-- **A lift along an sc-diffeomorphism `f : U → V` is a lift back along its inverse.** -/
theorem IsLiftOf.symm_of_isScDiffeoOn (hd : P.IsScDiffeoOn Q f g U V) {p : BSpace hP}
    {q : BSpace hQ} (h : IsLiftOf hP hQ f p q) (hp : bMap hP p ∈ U) : IsLiftOf hQ hP g q p := by
  obtain ⟨r, hr⟩ := exists_isLiftOf hQ hP hd.symm.isDHomeoOn (p := q)
    (by rw [h.bMap_eq]; exact hd.mapsTo hp)
  have he : r = p := (h.comp hr).unique (isLiftOf_id hP p)
    (eventuallyEq_of_mem (hd.isOpen_source.mem_nhds hp) fun x hx => hd.left_inv x hx)
  rwa [he] at hr

variable (hP) in
/-- **Every face germ over `V` is the image of a face germ over `U`** under an
sc-diffeomorphism `f : U → V`. -/
theorem exists_isLiftOf_of_isScDiffeoOn (hd : P.IsScDiffeoOn Q f g U V) {q : BSpace hQ}
    (hq : bMap hQ q ∈ V) : ∃ p : BSpace hP, bMap hP p = g (bMap hQ q) ∧ IsLiftOf hP hQ f p q := by
  obtain ⟨p, hp⟩ := exists_isLiftOf hQ hP hd.symm.isDHomeoOn hq
  exact ⟨p, hp.bMap_eq, hp.symm_of_isScDiffeoOn hd.symm hq⟩

/-- **The lift along an sc-diffeomorphism `f : U → V` is injective** on germs over `U`. -/
theorem IsLiftOf.inj_of_isScDiffeoOn (hd : P.IsScDiffeoOn Q f g U V) {p p' : BSpace hP}
    {q : BSpace hQ} (h : IsLiftOf hP hQ f p q) (h' : IsLiftOf hP hQ f p' q) (hp : bMap hP p ∈ U)
    (hp' : bMap hP p' ∈ U) : p = p' :=
  (h.symm_of_isScDiffeoOn hd hp).unique (h'.symm_of_isScDiffeoOn hd hp') EventuallyEq.rfl

end Inverse

end TameBoundary

namespace GCT.PolyfoldConstruction

open TameBoundary MPolyfold

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} (hT : S.IsTame) (hS : S.HasUniformizers)
  {ι : Type u} (Ψ : ι → S.Unif)

section Objects

/-- **`p ∈ bX` comes from the face germ `q` of `O_λ`**: `p` is the image of `q` under the
inclusion `O_λ → X = ⊔ O_λ`. -/
def IsComponentGerm (p : (S.modelEpGroupoid Ψ).bObj (S.isTame_modelEpGroupoid Ψ hT)) (i : ι)
    (q : S.bO hT (Ψ i)) : Prop :=
  IsLiftOf (S.hdU hT (Ψ i)) ((S.modelEpGroupoid Ψ).cornerObj (S.isTame_modelEpGroupoid Ψ hT))
    (S.objMk Ψ i) q p

variable {hT hS Ψ}

theorem IsComponentGerm.bMap_eq {p : (S.modelEpGroupoid Ψ).bObj (S.isTame_modelEpGroupoid Ψ hT)}
    {i : ι} {q : S.bO hT (Ψ i)} (h : IsComponentGerm hT Ψ p i q) :
    bMap _ p = ⟨i, bMap (S.hdU hT (Ψ i)) q⟩ :=
  IsLiftOf.bMap_eq h

variable (hT) in
/-- **Every face germ of `X` over `(λ, x)` comes from a face germ of `O_λ` at `x`.** -/
theorem exists_isComponentGerm (p : (S.modelEpGroupoid Ψ).bObj (S.isTame_modelEpGroupoid Ψ hT))
    {i : ι} {x : (Ψ i).1.O} (hp : bMap _ p = ⟨i, x⟩) :
    ∃ q : S.bO hT (Ψ i), bMap _ q = x ∧ IsComponentGerm hT Ψ p i q := by
  obtain ⟨q, hq, hl⟩ := exists_isLiftOf_of_isScDiffeoOn (S.hdU hT (Ψ i))
    (hQ := (S.modelEpGroupoid Ψ).cornerObj (S.isTame_modelEpGroupoid Ψ hT))
    (isScDiffeoOn_sigmaMk (fun k => (Ψ k).1.P) i x) (q := p) (by rw [hp]; exact mem_range_self x)
  refine ⟨q, ?_, hl⟩
  rw [hq, hp]
  exact sigmaProj_mk (X := fun k => (Ψ k).1.O) i x x

/-- **The face germ of `O_λ` is unique**, and so is `λ`. -/
theorem IsComponentGerm.sigma_eq {p : (S.modelEpGroupoid Ψ).bObj (S.isTame_modelEpGroupoid Ψ hT)}
    {i j : ι} {q : S.bO hT (Ψ i)} {q' : S.bO hT (Ψ j)} (h : IsComponentGerm hT Ψ p i q)
    (h' : IsComponentGerm hT Ψ p j q') : (⟨i, q⟩ : Σ k, S.bO hT (Ψ k)) = ⟨j, q'⟩ := by
  have e : (⟨i, bMap _ q⟩ : S.ModelObj Ψ) = ⟨j, bMap _ q'⟩ := h.bMap_eq.symm.trans h'.bMap_eq
  obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.1 e
  have : q = q' := IsLiftOf.inj_of_isScDiffeoOn
    (isScDiffeoOn_sigmaMk (fun k => (Ψ k).1.P) i (bMap _ q)) h h' (mem_univ _) (mem_univ _)
  rw [this]

theorem IsComponentGerm.eq {p : (S.modelEpGroupoid Ψ).bObj (S.isTame_modelEpGroupoid Ψ hT)}
    {i : ι} {q q' : S.bO hT (Ψ i)} (h : IsComponentGerm hT Ψ p i q)
    (h' : IsComponentGerm hT Ψ p i q') : q = q' :=
  eq_of_heq (Sigma.mk.inj_iff.1 (h.sigma_eq h')).2

/-- Face germs of `O_λ` with the same image in `bX` are equal. -/
theorem IsComponentGerm.eq_of_eq {p p' : (S.modelEpGroupoid Ψ).bObj (S.isTame_modelEpGroupoid Ψ hT)}
    {i : ι} {q : S.bO hT (Ψ i)} (h : IsComponentGerm hT Ψ p i q)
    (h' : IsComponentGerm hT Ψ p' i q) : p = p' :=
  h.unique h' EventuallyEq.rfl

variable (hT Ψ) in
theorem exists_componentGerm (p : (S.modelEpGroupoid Ψ).bObj (S.isTame_modelEpGroupoid Ψ hT)) :
    ∃ s : Σ k, S.bO hT (Ψ k), IsComponentGerm hT Ψ p s.1 s.2 := by
  obtain ⟨q, -, hq⟩ := exists_isComponentGerm hT p (i := (bMap _ p).1) (x := (bMap _ p).2) rfl
  exact ⟨⟨_, q⟩, hq⟩

variable (hT Ψ) in
/-- The index `λ` and the face germ `q` of `O_λ` of `p ∈ bX`. -/
def componentGerm (p : (S.modelEpGroupoid Ψ).bObj (S.isTame_modelEpGroupoid Ψ hT)) :
    Σ k, S.bO hT (Ψ k) :=
  (exists_componentGerm hT Ψ p).choose

theorem isComponentGerm_componentGerm
    (p : (S.modelEpGroupoid Ψ).bObj (S.isTame_modelEpGroupoid Ψ hT)) :
    IsComponentGerm hT Ψ p (componentGerm hT Ψ p).1 (componentGerm hT Ψ p).2 :=
  (exists_componentGerm hT Ψ p).choose_spec

theorem componentGerm_eq {p : (S.modelEpGroupoid Ψ).bObj (S.isTame_modelEpGroupoid Ψ hT)}
    {i : ι} {q : S.bO hT (Ψ i)} (h : IsComponentGerm hT Ψ p i q) : componentGerm hT Ψ p = ⟨i, q⟩ :=
  (isComponentGerm_componentGerm p).sigma_eq h

variable (hT hS Ψ) in
/-- **`bΓ` on objects**: a face germ `p` of `X = ⊔ O_λ` over `(λ, x)` goes to the object of `bC`
given by the face germ `q` of `O_λ` at `x` with image `p` (`ptObj`, the class
`[Ψ_λ(x), Ψ_λ, U(x), θ]` of (17.57)). -/
def bdryModelObj (p : (S.modelEpGroupoid Ψ).bObj (S.isTame_modelEpGroupoid Ψ hT)) :
    S.BObj hT hS :=
  S.ptObj hT hS (componentGerm hT Ψ p).2

theorem bdryModelObj_eq {p : (S.modelEpGroupoid Ψ).bObj (S.isTame_modelEpGroupoid Ψ hT)}
    {i : ι} {q : S.bO hT (Ψ i)} (h : IsComponentGerm hT Ψ p i q) :
    bdryModelObj hT hS Ψ p = S.ptObj hT hS q := by
  unfold bdryModelObj
  rw [componentGerm_eq h]

/-- `B(bΓ(p)) = Γ(F(p))` on objects. -/
theorem bdryModelObj_α (p : (S.modelEpGroupoid Ψ).bObj (S.isTame_modelEpGroupoid Ψ hT)) :
    (bdryModelObj hT hS Ψ p).α = S.modelObjMap Ψ (bMap _ p) := by
  obtain ⟨q, hqx, hq⟩ := exists_isComponentGerm hT p (i := (bMap _ p).1) (x := (bMap _ p).2) rfl
  rw [bdryModelObj_eq hq, ptObj_α, hqx]
  rfl

end Objects

section Morphisms

variable {hT hS Ψ}

/-- **A face germ `Φ` of the morphism M-polyfold `𝐗 = ⊔ M(Ψ_λ, Ψ_λ')` over `(x, φ, x')` carries the
face germ of its source to that of its target** (2021 Definition 17.4.3 (2), `θ' = f_*θ` for the
local sc-diffeomorphism `f = t ∘ (s|W(h))⁻¹` of `h = (x, φ, x')`): if `s(Φ)` and `t(Φ)` come from
the face germs `q` of `O_λ` and `q'` of `O_λ'`, then `h` carries `q` to `q'`. -/
theorem germLift_of_isComponentGerm
    (Φ : (S.modelEpGroupoid Ψ).bMor (S.isTame_modelEpGroupoid Ψ hT)) {i j : ι}
    {h : S.Tr (Ψ i) (Ψ j)} (hΦ : bMap _ Φ = ⟨(i, j), h⟩) {q : S.bO hT (Ψ i)}
    {q' : S.bO hT (Ψ j)}
    (hq : IsComponentGerm hT Ψ ((S.modelEpGroupoid Ψ).bSrc (S.isTame_modelEpGroupoid Ψ hT) Φ) i q)
    (hq' : IsComponentGerm hT Ψ ((S.modelEpGroupoid Ψ).bTgt (S.isTame_modelEpGroupoid Ψ hT) Φ) j
      q') :
    S.GermLift hT h q q' := by
  have hX := S.isTame_modelEpGroupoid Ψ hT
  have hsrc : bMap _ ((S.modelEpGroupoid Ψ).bSrc hX Φ) = (⟨i, h.src⟩ : S.ModelObj Ψ) := by
    rw [EpGroupoid.bMap_bSrc, hΦ]; rfl
  have hb : bMap (S.hdU hT (Ψ i)) q = h.src :=
    eq_of_heq (Sigma.mk.inj_iff.1 (hq.bMap_eq.symm.trans hsrc)).2
  let T := (S.exists_admissibleTriple h).some
  obtain ⟨r, hr⟩ := exists_isLiftOf (S.hdU hT (Ψ i)) (S.hdU hT (Ψ j)) T.isDHomeoOn_germMap
    (p := q) (by rw [hb]; exact T.src_mem)
  obtain ⟨r', hr'⟩ := exists_isLiftOf (S.hdU hT (Ψ j)) ((S.modelEpGroupoid Ψ).cornerObj hX)
    (isScDiffeoOn_sigmaMk (fun k => (Ψ k).1.P) j (bMap _ r)).isDHomeoOn (p := r) (mem_univ _)
  obtain ⟨W, V, σ, hW, hd⟩ := (S.modelEpGroupoid Ψ).isLocalScDiffeo_src (bMap _ Φ)
  have h1 := EpGroupoid.isLiftOf_sheet hX hd hW
  have hchain := (hq.comp h1).comp (EpGroupoid.isLiftOf_bTgt hX Φ)
  -- the two local sections `σ ∘ (O_λ → X)` and `(O_λ → X) ∘ (s|W(h))⁻¹` of `s` agree near `h.src`
  have hV : S.objMk Ψ i h.src ∈ V := by
    have := hd.mapsTo hW
    rw [hΦ] at this
    exact this
  have hs₁ : ContinuousAt (σ ∘ S.objMk Ψ i) h.src :=
    (hd.isScSmoothOn_inv.continuousOn.continuousAt (hd.isOpen_target.mem_nhds hV)).comp
      continuous_sigmaMk.continuousAt
  have hs₁x : (σ ∘ S.objMk Ψ i) h.src = bMap _ Φ := by
    have := hd.left_inv _ hW
    rw [hΦ] at this ⊢
    exact this
  have hs₂ : ContinuousAt (S.morMk Ψ (i, j) ∘ T.srcInv) h.src :=
    continuous_sigmaMk.continuousAt.comp
      (T.continuousOn_srcInv.continuousAt (T.isOpen_srcSet.mem_nhds T.src_mem))
  have hs₂x : (S.morMk Ψ (i, j) ∘ T.srcInv) h.src = bMap _ Φ := by
    rw [hΦ]
    exact congrArg (S.morMk Ψ (i, j)) (T.srcInv_eq T.mem_carrier)
  have hWn : W ∈ 𝓝 (bMap _ Φ) := hd.isOpen_source.mem_nhds hW
  have e₁ : ∀ᶠ x in 𝓝 h.src, (σ ∘ S.objMk Ψ i) x ∈ W := hs₁.preimage_mem_nhds (hs₁x ▸ hWn)
  have e₂ : ∀ᶠ x in 𝓝 h.src, (S.morMk Ψ (i, j) ∘ T.srcInv) x ∈ W :=
    hs₂.preimage_mem_nhds (hs₂x ▸ hWn)
  have e₃ : ∀ᶠ x in 𝓝 h.src, S.objMk Ψ i x ∈ V :=
    continuous_sigmaMk.continuousAt.preimage_mem_nhds (hd.isOpen_target.mem_nhds hV)
  have e₄ : ∀ᶠ x in 𝓝 h.src, x ∈ T.srcSet := T.isOpen_srcSet.mem_nhds T.src_mem
  have hagree : ∀ᶠ x in 𝓝 h.src,
      (σ ∘ S.objMk Ψ i) x = (S.morMk Ψ (i, j) ∘ T.srcInv) x := by
    filter_upwards [e₁, e₂, e₃, e₄] with x h₁ h₂ h₃ h₄
    refine hd.injOn h₁ h₂ ?_
    change (S.modelEpGroupoid Ψ).src (σ (S.objMk Ψ i x)) =
      (⟨i, (T.srcInv x).src⟩ : S.ModelObj Ψ)
    rw [hd.right_inv _ h₃, T.src_srcInv h₄]
  have hgerm : (S.objMk Ψ j ∘ T.germMap) =ᶠ[𝓝 (bMap _ q)]
      ((S.modelEpGroupoid Ψ).tgt ∘ (σ ∘ S.objMk Ψ i)) := by
    rw [hb]
    filter_upwards [hagree] with x hx
    change (⟨j, (T.srcInv x).tgt⟩ : S.ModelObj Ψ) =
      (S.modelEpGroupoid Ψ).tgt ((σ ∘ S.objMk Ψ i) x)
    rw [hx]
    rfl
  have he : r' = (S.modelEpGroupoid Ψ).bTgt hX Φ := (hr.comp hr').unique hchain hgerm
  have hrq : r = q' := IsComponentGerm.eq (p := (S.modelEpGroupoid Ψ).bTgt hX Φ)
    (show IsComponentGerm hT Ψ _ j r from he ▸ hr') hq'
  exact ⟨hb, T, hrq ▸ hr⟩

/-- **The morphism of `bC` over `φ`** given by a morphism of `bX` over `(x, φ, x')`. -/
theorem bLift_bdryModelObj (Φ : (S.modelEpGroupoid Ψ).bMor (S.isTame_modelEpGroupoid Ψ hT)) :
    S.BLift (bdryModelObj hT hS Ψ ((S.modelEpGroupoid Ψ).bSrc _ Φ)) (bMap _ Φ).2.mor
      (bdryModelObj hT hS Ψ ((S.modelEpGroupoid Ψ).bTgt _ Φ)) := by
  have hX := S.isTame_modelEpGroupoid Ψ hT
  generalize hm : bMap _ Φ = m
  obtain ⟨⟨i, j⟩, h⟩ := m
  have hsrc : bMap _ ((S.modelEpGroupoid Ψ).bSrc hX Φ) = (⟨i, h.src⟩ : S.ModelObj Ψ) := by
    rw [EpGroupoid.bMap_bSrc, hm]; rfl
  have htgt : bMap _ ((S.modelEpGroupoid Ψ).bTgt hX Φ) = (⟨j, h.tgt⟩ : S.ModelObj Ψ) := by
    rw [EpGroupoid.bMap_bTgt, hm]; rfl
  obtain ⟨q, hqx, hq⟩ := exists_isComponentGerm hT _ hsrc
  obtain ⟨q', hqx', hq'⟩ := exists_isComponentGerm hT _ htgt
  rw [bdryModelObj_eq hq, bdryModelObj_eq hq']
  exact (bLift_ptObj_iff h hqx hqx').2 (germLift_of_isComponentGerm Φ hm hq hq')

variable (hT hS Ψ) in
/-- **The functor `bΓ : bX → bC`** (2021 p. 812): a face germ of `X = ⊔ O_λ` goes to the object
of `bC` it defines (`bdryModelObj`), a face germ of `𝐗` over `(x, φ, x')` to the morphism
`φ` between the objects of its source and target. -/
def bdryModelFunctor :
    GroupoidFunctor ((S.modelEpGroupoid Ψ).boundaryGroupoid (S.isTame_modelEpGroupoid Ψ hT))
      (S.bdryGroupoid hT hS) where
  obj := bdryModelObj hT hS Ψ
  mor Φ := ⟨_, (bMap _ Φ).2.mor, _, bLift_bdryModelObj Φ⟩
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp Φ Φ' hc := by
    have hX := S.isTame_modelEpGroupoid Ψ hT
    let A : S.BMor hT hS := ⟨_, (bMap _ Φ).2.mor, _, bLift_bdryModelObj Φ⟩
    let A' : S.BMor hT hS := ⟨_, (bMap _ Φ').2.mor, _, bLift_bdryModelObj Φ'⟩
    have hc' : A.src = A'.tgt := congrArg (bdryModelObj hT hS Ψ) hc
    obtain ⟨hcm, hcs⟩ := EpGroupoid.bComp_spec hX (a := Φ) (b := Φ') hc
    refine BMor.ext_of_src ?_ ?_
    · change bdryModelObj hT hS Ψ ((S.modelEpGroupoid Ψ).bSrc hX
          ((S.modelEpGroupoid Ψ).bComp hX Φ Φ')) = ((S.bdryGroupoid hT hS).comp A A').src
      rw [hcs]
      exact ((S.bdryGroupoid hT hS).src_comp A A' hc').symm
    · change ((bMap _ ((S.modelEpGroupoid Ψ).bComp hX Φ Φ')).2.mor : C.Mor) =
        ((S.bdryGroupoid hT hS).comp A A').mor
      rw [hcm, bdryGroupoid_comp_mor hc']
      exact modelGroupoid_comp_mor (EpGroupoid.src_eq_tgt_of_bSrc_eq hX hc)
  mor_unit p := by
    have hX := S.isTame_modelEpGroupoid Ψ hT
    refine BMor.ext_of_src ?_ ?_
    · change bdryModelObj hT hS Ψ ((S.modelEpGroupoid Ψ).bSrc hX
          ((S.modelEpGroupoid Ψ).bUnit hX p)) = _
      rw [EpGroupoid.bSrc_bUnit]
      rfl
    · change ((bMap _ ((S.modelEpGroupoid Ψ).bUnit hX p)).2.mor : C.Mor) = _
      rw [EpGroupoid.bMap_bUnit, bdryGroupoid_unit, bdryModelObj_α]
      rfl

@[simp] theorem bdryModelFunctor_obj
    (p : (S.modelEpGroupoid Ψ).bObj (S.isTame_modelEpGroupoid Ψ hT)) :
    (bdryModelFunctor hT hS Ψ).obj p = bdryModelObj hT hS Ψ p := rfl

@[simp] theorem bdryModelFunctor_mor
    (Φ : (S.modelEpGroupoid Ψ).bMor (S.isTame_modelEpGroupoid Ψ hT)) :
    ((bdryModelFunctor hT hS Ψ).mor Φ).mor = (bMap _ Φ).2.mor := rfl

variable (hT hS Ψ) in
/-- **The square of p. 812 commutes**: `B ∘ bΓ = Γ ∘ F`, with `B : bC → C` the forgetful functor
(17.81), `Γ = Γ_Ψ : X → C` (17.10) and `F : bX → X` the forgetful functor of the tame boundary
ep-groupoid (Theorem 7.6.9). -/
theorem bdryModelFunctor_square :
    (S.bdryFunctorC hT hS).comp (bdryModelFunctor hT hS Ψ) =
      (S.modelFunctor Ψ).comp
        ((S.modelEpGroupoid Ψ).boundaryEpFunctor
          (S.isTame_modelEpGroupoid Ψ hT)).toGroupoidFunctor :=
  GroupoidFunctor.ext (funext fun p => bdryModelObj_α (hS := hS) p) rfl

variable (hT hS Ψ) in
/-- **`bΓ` is faithful.** -/
theorem bdryModelFunctor_faithful : (bdryModelFunctor hT hS Ψ).toFunctor.Faithful := by
  have hX := S.isTame_modelEpGroupoid Ψ hT
  refine (GroupoidFunctor.faithful_iff _).2 fun Φ Φ' hs ht he => ?_
  have hm : (bMap _ Φ).2.mor = (bMap _ Φ').2.mor := congrArg BMor.mor he
  have hB : bMap _ Φ = bMap _ Φ' :=
    (GroupoidFunctor.faithful_iff _).1 (S.modelFunctor_faithful Ψ) _ _
      ((EpGroupoid.bMap_bSrc hX Φ).symm.trans ((congrArg _ hs).trans (EpGroupoid.bMap_bSrc hX Φ')))
      ((EpGroupoid.bMap_bTgt hX Φ).symm.trans ((congrArg _ ht).trans (EpGroupoid.bMap_bTgt hX Φ')))
      hm
  exact EpGroupoid.eq_of_bMap_eq_of_bSrc_eq hX hB hs

end Morphisms

section Equivalence

variable {hT hS Ψ}

variable (hT hS Ψ) in
/-- **`bΓ` is full**: a morphism `ξ : bΓ(p) → bΓ(p')` of `bC` over `φ : Ψ_λ(x) → Ψ_λ'(x')`
is the image of the face germ of `𝐗` over `(x, φ, x')` whose source is `p`. -/
theorem bdryModelFunctor_full : (bdryModelFunctor hT hS Ψ).toFunctor.Full := by
  have hX := S.isTame_modelEpGroupoid Ψ hT
  refine (GroupoidFunctor.full_iff _).2 fun p p' Ξ hs ht => ?_
  obtain ⟨q, hqx, hq⟩ := exists_isComponentGerm hT p (i := (bMap _ p).1) (x := (bMap _ p).2) rfl
  obtain ⟨q', hqx', hq'⟩ :=
    exists_isComponentGerm hT p' (i := (bMap _ p').1) (x := (bMap _ p').2) rfl
  have hs' : Ξ.src = S.ptObj hT hS q := hs.trans (bdryModelObj_eq hq)
  have ht' : Ξ.tgt = S.ptObj hT hS q' := ht.trans (bdryModelObj_eq hq')
  have hlifts : S.BLift (S.ptObj hT hS q) Ξ.mor (S.ptObj hT hS q') := hs' ▸ ht' ▸ Ξ.lifts
  have hsm : C.toGroupoidStr.src Ξ.mor = (Ψ (bMap _ p).1).1.obj (bMap _ p).2 := by
    rw [Ξ.src_mor, hs', ptObj_α, hqx]
  have htm : C.toGroupoidStr.tgt Ξ.mor = (Ψ (bMap _ p').1).1.obj (bMap _ p').2 := by
    rw [Ξ.tgt_mor, ht', ptObj_α, hqx']
  let h : S.Tr (Ψ (bMap _ p).1) (Ψ (bMap _ p').1) := ⟨(bMap _ p).2, Ξ.mor, (bMap _ p').2, hsm, htm⟩
  have hl : S.GermLift hT h q q' := (bLift_ptObj_iff h hqx hqx').1 hlifts
  let m : S.ModelMor Ψ := ⟨((bMap _ p).1, (bMap _ p').1), h⟩
  obtain ⟨W, V, σ, hW, hd⟩ := (S.modelEpGroupoid Ψ).isLocalScDiffeo_src m
  have hpV : bMap _ p ∈ V := hd.mapsTo hW
  obtain ⟨Φ, hΦ⟩ := exists_isLiftOf ((S.modelEpGroupoid Ψ).cornerObj hX)
    ((S.modelEpGroupoid Ψ).cornerMor hX) hd.symm.isDHomeoOn (p := p) hpV
  have hbΦ : bMap _ Φ = m := hΦ.bMap_eq.trans (hd.left_inv m hW)
  have hsΦ : (S.modelEpGroupoid Ψ).bSrc hX Φ = p :=
    (hΦ.comp (EpGroupoid.isLiftOf_bSrc hX Φ)).unique (isLiftOf_id _ p)
      (eventuallyEq_of_mem (hd.isOpen_target.mem_nhds hpV) fun y hy => hd.right_inv y hy)
  have htgt : bMap _ ((S.modelEpGroupoid Ψ).bTgt hX Φ) =
      (⟨(bMap _ p').1, (bMap _ p').2⟩ : S.ModelObj Ψ) := by
    rw [EpGroupoid.bMap_bTgt, hbΦ]; rfl
  obtain ⟨r, -, hr⟩ := exists_isComponentGerm hT _ htgt
  have hrq : r = q' := germLift_unique
    (germLift_of_isComponentGerm (q := q) Φ hbΦ (hsΦ ▸ hq) hr) hl
  refine ⟨Φ, hsΦ, (hrq ▸ hr).eq_of_eq hq', BMor.ext_of_src ?_ ?_⟩
  · change bdryModelObj hT hS Ψ ((S.modelEpGroupoid Ψ).bSrc hX Φ) = Ξ.src
    rw [hsΦ]; exact hs.symm
  · change (bMap _ Φ).2.mor = Ξ.mor
    rw [hbΦ]

variable (hT hS) in
/-- **`bΓ` is essentially surjective** for a family whose footprints cover `|C|`: every object
`ᾱ` of `bC` over `α ≅ Ψ_λ(x)` is isomorphic to the object given by a face germ of `O_λ` at `x`. -/
theorem bdryModelFunctor_essSurj (hc : S.IsCoveringFamily Ψ) :
    (bdryModelFunctor hT hS Ψ).toFunctor.EssSurj := by
  have hX := S.isTame_modelEpGroupoid Ψ hT
  refine (GroupoidFunctor.essSurj_iff _).2 fun a => ?_
  obtain ⟨z, φ, hs, ht⟩ := (GroupoidFunctor.essSurj_iff _).1 (modelFunctor_essSurj hc) a.α
  obtain ⟨qa, hqa, hqa'⟩ := exists_ptObj_eq (Ψ := S.bdryRefUnif hS a.α) a
    (y := S.refPt hS a.α) (obj_refPt hS a.α).symm
  let h' : S.Tr (S.bdryRefUnif hS a.α) (Ψ z.1) :=
    ⟨S.refPt hS a.α, C.toGroupoidStr.inv φ, z.2,
      (C.toGroupoidStr.src_inv φ).trans (ht.trans (obj_refPt hS a.α).symm),
      (C.toGroupoidStr.tgt_inv φ).trans hs⟩
  have hl := germLift_germPush h' qa hqa
  obtain ⟨p, hp⟩ := exists_isLiftOf (S.hdU hT (Ψ z.1)) ((S.modelEpGroupoid Ψ).cornerObj hX)
    (isScDiffeoOn_sigmaMk (fun k => (Ψ k).1.P) z.1 (bMap _ (germPush h' qa hqa))).isDHomeoOn
    (p := germPush h' qa hqa) (mem_univ _)
  refine ⟨p, (S.bdryGroupoid hT hS).inv (S.ptMor (hS := hS) h' hl), ?_, hqa'⟩
  exact (bdryModelObj_eq (p := p) (i := z.1) hp).symm

variable (hT hS) in
/-- **`bΓ : bX → bC` is an equivalence of categories** for a covering family (2021 p. 812,
"the horizontal arrows are equivalences of categories"). -/
theorem bdryModelFunctor_isEquivalence (hc : S.IsCoveringFamily Ψ) :
    (bdryModelFunctor hT hS Ψ).toFunctor.IsEquivalence :=
  { faithful := bdryModelFunctor_faithful hT hS Ψ, full := bdryModelFunctor_full hT hS Ψ,
    essSurj := bdryModelFunctor_essSurj hT hS hc }

variable (hT hS) in
/-- `|bΓ| : |bX| → |bC|` is a bijection of orbit spaces. -/
theorem bijective_orbitMap_bdryModelFunctor (hc : S.IsCoveringFamily Ψ) :
    Bijective (bdryModelFunctor hT hS Ψ).orbitMap :=
  (bdryModelFunctor hT hS Ψ).bijective_orbitMap_of_isEquivalence
    (bdryModelFunctor_isEquivalence hT hS hc)

end Equivalence

section Reindex

variable {hT hS} {κ : Type u}

/-- The reindexing functor `X_{Φ ∘ σ} → X_Φ` is a local sc-diffeomorphism on objects, hence an
index-preserving local homeomorphism. -/
theorem isDLocalHomeo_modelMap_obj (Φ : ι → S.Unif) (σ : κ → ι) :
    IsDLocalHomeo (S.modelEpGroupoid (Φ ∘ σ)).PObj.degIndex (S.modelEpGroupoid Φ).PObj.degIndex
      (S.modelMap Φ σ).obj :=
  MPolyfold.IsLocalScDiffeo.isDLocalHomeo (by
    change (MPolyfold.sigma fun k => ((Φ ∘ σ) k).1.P).IsLocalScDiffeo
      (MPolyfold.sigma fun i => (Φ i).1.P) (Sigma.map σ fun _ q => q)
    exact MPolyfold.isLocalScDiffeo_sigmaMap _ fun _ => MPolyfold.isLocalScDiffeo_id)

variable (hT) in
/-- **The lift `b(X_{Φ ∘ σ}) → b(X_Φ)` of the reindexing functor** on face germs
(`TameBoundary.bLift`). -/
def bdryModelMap (Φ : ι → S.Unif) (σ : κ → ι)
    (p : (S.modelEpGroupoid (Φ ∘ σ)).bObj (S.isTame_modelEpGroupoid (Φ ∘ σ) hT)) :
    (S.modelEpGroupoid Φ).bObj (S.isTame_modelEpGroupoid Φ hT) :=
  bLift ((S.modelEpGroupoid (Φ ∘ σ)).cornerObj (S.isTame_modelEpGroupoid (Φ ∘ σ) hT))
    ((S.modelEpGroupoid Φ).cornerObj (S.isTame_modelEpGroupoid Φ hT))
    (isDLocalHomeo_modelMap_obj Φ σ) p

/-- **The diagram of `Φ ∘ σ` embeds into the diagram of `Φ`** (2021 p. 812, "the two initial
constructions in the ep-groupoid context embed into the diagram associated to the union"):
`bΓ_Φ ∘ b(X_{Φ ∘ σ} → X_Φ) = bΓ_{Φ ∘ σ}` on objects, and `b(X_{Φ ∘ σ} → X_Φ)` lies over the
reindexing functor.  With `σ` the two inclusions into `Ψ ⊔ Ψ'` (`inclLeft`, `inclRight` of
Theorem 17.1.18) this is the union of two covering families. -/
theorem bdryModelObj_modelMap (Φ : ι → S.Unif) (σ : κ → ι)
    (p : (S.modelEpGroupoid (Φ ∘ σ)).bObj (S.isTame_modelEpGroupoid (Φ ∘ σ) hT)) :
    bdryModelObj hT hS Φ (bdryModelMap hT Φ σ p) = bdryModelObj hT hS (Φ ∘ σ) p ∧
      bMap _ (bdryModelMap hT Φ σ p) = (S.modelMap Φ σ).obj (bMap _ p) := by
  obtain ⟨q, -, hq⟩ := exists_isComponentGerm hT p (i := (bMap _ p).1) (x := (bMap _ p).2) rfl
  have h2 := isLiftOf_bLift ((S.modelEpGroupoid (Φ ∘ σ)).cornerObj
    (S.isTame_modelEpGroupoid (Φ ∘ σ) hT))
    ((S.modelEpGroupoid Φ).cornerObj (S.isTame_modelEpGroupoid Φ hT))
    (isDLocalHomeo_modelMap_obj Φ σ) p
  have hq' : IsComponentGerm hT Φ (bdryModelMap hT Φ σ p) (σ (bMap _ p).1) q := hq.comp h2
  exact ⟨by rw [bdryModelObj_eq hq, bdryModelObj_eq hq'], bMap_bLift _ _ _ p⟩

end Reindex

section Diagram

/-- **2021 p. 812, the diagram `bX → bC` over `X → C`**: for a tame polyfold structure with
`F(α) ≠ ∅` and a covering family `Ψ`, with `X = X_Ψ` and `bX` its tame boundary ep-groupoid
(Theorem 7.6.9, tame), the square
`B ∘ bΓ = Γ ∘ F` commutes (`B : bC → C` of (17.81), `F : bX → X` the forgetful ep-functor of
`bX`), both horizontal arrows `bΓ`, `Γ` are equivalences of categories, and `|bΓ|`, `|Γ|` are
bijections of orbit spaces (`|Γ|` a homeomorphism, Lemma 17.1.15). -/
theorem diagram_bX_bC (c : S.CoveringFamily) :
    ((S.modelEpGroupoid c.Ψ).boundaryEpGroupoid (S.isTame_modelEpGroupoid c.Ψ hT)).IsTame ∧
    (S.bdryFunctorC hT hS).comp (bdryModelFunctor hT hS c.Ψ) =
      (S.modelFunctor c.Ψ).comp ((S.modelEpGroupoid c.Ψ).boundaryEpFunctor
        (S.isTame_modelEpGroupoid c.Ψ hT)).toGroupoidFunctor ∧
    (bdryModelFunctor hT hS c.Ψ).toFunctor.IsEquivalence ∧
    (S.modelFunctor c.Ψ).toFunctor.IsEquivalence ∧
    Bijective (bdryModelFunctor hT hS c.Ψ).orbitMap ∧
    IsHomeomorph (S.modelFunctor c.Ψ).orbitMap :=
  ⟨EpGroupoid.isTame_boundaryEpGroupoid _, bdryModelFunctor_square hT hS c.Ψ,
    bdryModelFunctor_isEquivalence hT hS c.cover, (S.lemma_17_1_15 c).1,
    bijective_orbitMap_bdryModelFunctor hT hS c.cover, (S.lemma_17_1_15 c).2⟩

end Diagram

section SwapWitness

open TameBoundaryExample

variable (W : ScBanach)

/-- **The hypotheses of `diagram_bX_bC` in a non-degenerate case**: the swap polyfold
`ℤ/2 ⋉ ([0,∞)² ⊕ W)` (non-trivial group, `−1` exchanging the two faces at the corner,
`swap_tameBoundary_witness`) is tame, has uniformizers at every object and a covering family,
and the tame boundary ep-groupoid `bX` of its model is non-empty (it contains an object whose
image under `bΓ` is a face germ at the corner). -/
theorem swap_diagram_bX_bC :
    ∃ hT : (swapConstruction W).IsTame, (swapConstruction W).HasUniformizers ∧
      ∃ c : (swapConstruction W).CoveringFamily,
      Nonempty (((swapConstruction W).modelEpGroupoid c.Ψ).bObj
        ((swapConstruction W).isTame_modelEpGroupoid c.Ψ hT)) := by
  have hT := swapConstruction_isTame W
  have hS := swapConstruction_hasUniformizers W
  have hd : (swapUnif₀ W).1.P.degIndex (swapCorner W) = 2 := by
    rw [degIndex_swapUnif₀]; exact quadrantPolyfold_degIndex_zero 2 W
  have hb : swapCorner W ∈ (swapUnif₀ W).1.P.boundary := by
    change 1 ≤ _
    rw [hd]; decide
  obtain ⟨V, -⟩ := (swapConstruction W).exists_goodNbhd (Ψ := swapUnif₀ W)
    (isTame_unif _ hT _) hb isOpen_univ (mem_univ _)
  have hV2 : V.faces.encard = 2 := by rw [V.encard_faces, hd]; rfl
  obtain ⟨θ, hθ⟩ : V.faces.Nonempty := by
    rw [← Set.encard_pos, hV2]; norm_num
  obtain ⟨c⟩ := (swapConstruction W).exists_coveringFamily_iff.2
    ((swapConstruction W).hasCoveringUniformizers_of_hasUniformizers hS)
  refine ⟨hT, hS, c, ?_⟩
  obtain ⟨p, -⟩ := (GroupoidFunctor.essSurj_iff _).1 (bdryModelFunctor_essSurj hT hS c.cover)
    ((swapConstruction W).ptObj hT hS (V.faceGerm hT hθ (swapCorner W) (V.mem_of_mem_faces hθ)))
  exact ⟨p⟩

end SwapWitness

end GCT.PolyfoldConstruction

end Polyfold
