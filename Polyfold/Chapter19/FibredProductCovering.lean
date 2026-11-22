import Polyfold.Chapter19.CoveringSquareTopology

/-!
# Maps between fibred products and proper strong bundle covering squares (HWZ 2021, §19.8)

General results for 2021 Theorem 19.8.22 (pp. 956–957), where the multiplication
`M(Γ̂', Γ̂'') ₛ×ₜ M(Γ̂, Γ̂') → M(Γ̂, Γ̂'')` is a strong bundle map between proper strong bundle
covering squares (Definition 19.8.19, p. 954): the square formed by the fibred products over
`p ₛ×ₜ p` has to be a proper strong bundle covering square.

## Setting

Fibred products `X₁ ₛ×ₜ X₂ = {(x₁, x₂) | s(x₁) = t(x₂)}` and `X₁' ₛ'×ₜ' X₂'` with `s`, `s'`
local sc-diffeomorphisms and `t`, `t'` sc-smooth carry Part I's sub-M-polyfold structure
(Proposition 2.5.20).  A map `Θ` between them of the form `(x₁, x₂) ↦ (f₁(x₁), f₂(x₂))`.

## What is formalized

* `MPolyfold.continuous_fibredProductMap`; **`MPolyfold.isLocalScDiffeo_fibredProductMap`**: if
  `f₂` is a local sc-diffeomorphism (and `f₁` continuous), `Θ` is a local sc-diffeomorphism
  (`pr₂' ∘ Θ = f₂ ∘ pr₂` with both second projections local sc-diffeomorphisms, `s`, `s'` being
  ones).
* Under the *fibrewise bijectivity* of `s` over `f₁` (`hlift`: for `s'(k₁) = t'(f₂(a₂))` there is
  `a₁` over `k₁` with `s(a₁) = t(a₂)`; `hinj`: `s` is injective on the fibres of `f₁`; in §19.7
  this is Lemma 19.7.9 for `ŝ` over `p`): `MPolyfold.fibredProductMap_eq_of_snd_eq`,
  `MPolyfold.surjective_fibredProductMap`, `MPolyfold.finite_fibredProductMap_fiber`,
  **`MPolyfold.exists_sheets_fibredProductMap`**: the fibre of `Θ` over `k` is the fibre of `f₂`
  over `k₂`, and the sheets of `f₂` over an open `V ∋ k₂` give sheets of `Θ` over `pr₂'⁻¹(V)`.
* `MPolyfold.fibredProductSnd` (`pr₂`), `StrongBundle.isScSmoothMap_fibredProductSnd`,
  `StrongBundle.fibredProductLift`, `StrongBundle.isStrongBundleMap_fibredProductLift`,
  `StrongBundle.isLocalStrongBundleIso_fibredProductLift`: for strong bundles `E₂ → X₂`,
  `E₂' → X₂'` and `Φ : E₂ → E₂'` over `f₂`, the pull-backs by the second projections and
  `Θ̃ = (Θ ∘ π, Φ ∘ π')`, a strong bundle map over `Θ`, near every point a strong bundle
  isomorphism when `Φ` is.
* **`isProperStrongBundleCoveringSquare_fibredProduct`**: if `Φ` over `f₂` is a proper strong
  bundle covering square, so is `Θ̃` over `Θ`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

namespace Polyfold

noncomputable section

open Set Function Topology

namespace MPolyfold

section FibredProductMap

variable {X₁ : Type*} [TopologicalSpace X₁] [T2Space X₁] [ParacompactSpace X₁] {P₁ : MPolyfold X₁}
  {X₂ : Type*} [TopologicalSpace X₂] [T2Space X₂] [ParacompactSpace X₂] {P₂ : MPolyfold X₂}
  {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {X₁' : Type*} [TopologicalSpace X₁'] [T2Space X₁'] [ParacompactSpace X₁'] {P₁' : MPolyfold X₁'}
  {X₂' : Type*} [TopologicalSpace X₂'] [T2Space X₂'] [ParacompactSpace X₂'] {P₂' : MPolyfold X₂'}
  {Z' : Type*} [TopologicalSpace Z'] [T2Space Z'] [ParacompactSpace Z'] {PZ' : MPolyfold Z'}
  {s : X₁ → Z} {t : X₂ → Z} {s' : X₁' → Z'} {t' : X₂' → Z'} {f₁ : X₁ → X₁'} {f₂ : X₂ → X₂'}
  {Θ : fibredProduct s t → fibredProduct s' t'}

/-- The second projection `pr₂ : X₁ ₛ×ₜ X₂ → X₂`. -/
abbrev fibredProductSnd (s : X₁ → Z) (t : X₂ → Z) (a : fibredProduct s t) : X₂ :=
  (a : X₁ × X₂).2

/-- A map `(x₁, x₂) ↦ (f₁(x₁), f₂(x₂))` between fibred products is continuous. -/
theorem continuous_fibredProductMap (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hΘ₁ : ∀ a, (Θ a : X₁' × X₂').1 = f₁ (a : X₁ × X₂).1)
    (hΘ₂ : ∀ a, (Θ a : X₁' × X₂').2 = f₂ (a : X₁ × X₂).2) : Continuous Θ := by
  refine continuous_induced_rng.2 ?_
  have e : (Subtype.val ∘ Θ) =
      fun a : fibredProduct s t => (f₁ (a : X₁ × X₂).1, f₂ (a : X₁ × X₂).2) :=
    funext fun a => Prod.ext (hΘ₁ a) (hΘ₂ a)
  rw [e]
  exact ((hf₁.comp continuous_fst).comp continuous_subtype_val).prodMk
    ((hf₂.comp continuous_snd).comp continuous_subtype_val)

/-- **A map between fibred products whose second component is a local sc-diffeomorphism is a
local sc-diffeomorphism** of the sub-M-polyfolds (Proposition 2.5.20): `pr₂' ∘ Θ = f₂ ∘ pr₂`,
and `pr₂`, `pr₂'` are local sc-diffeomorphisms because `s`, `s'` are. -/
theorem isLocalScDiffeo_fibredProductMap [ParacompactSpace (X₁ × X₂)]
    [ParacompactSpace (fibredProduct s t)] [ParacompactSpace (X₁' × X₂')]
    [ParacompactSpace (fibredProduct s' t')] (hs : P₁.IsLocalScDiffeo PZ s)
    (ht : P₂.IsScSmoothMap PZ t) (hs' : P₁'.IsLocalScDiffeo PZ' s')
    (ht' : P₂'.IsScSmoothMap PZ' t') (hf₂ : P₂.IsLocalScDiffeo P₂' f₂) (hΘ : Continuous Θ)
    (hΘ₂ : ∀ a, (Θ a : X₁' × X₂').2 = f₂ (a : X₁ × X₂).2) :
    (subPolyfold (isSubMPolyfold_fibredProduct hs ht)).IsLocalScDiffeo
      (subPolyfold (isSubMPolyfold_fibredProduct hs' ht')) Θ :=
  isLocalScDiffeo_of_comp_eq (hf₂.comp (isLocalScDiffeo_sndOfFibredProduct hs ht))
    (isLocalScDiffeo_sndOfFibredProduct hs' ht') hΘ fun a => hΘ₂ a

/-- Two points of `X₁ ₛ×ₜ X₂` with the same second component and first components in the same
fibre of `f₁` agree, when `s` is injective on the fibres of `f₁`. -/
theorem fibredProductMap_eq_of_snd_eq (hinj : ∀ a₁ b₁, f₁ a₁ = f₁ b₁ → s a₁ = s b₁ → a₁ = b₁)
    (hΘ₁ : ∀ a, (Θ a : X₁' × X₂').1 = f₁ (a : X₁ × X₂).1) {a b : fibredProduct s t}
    (h : Θ a = Θ b) (h₂ : (a : X₁ × X₂).2 = (b : X₁ × X₂).2) : a = b := by
  have ha : s (a : X₁ × X₂).1 = t (a : X₁ × X₂).2 := a.2
  have hb : s (b : X₁ × X₂).1 = t (b : X₁ × X₂).2 := b.2
  refine Subtype.ext (Prod.ext (hinj _ _ ?_ ?_) h₂)
  · rw [← hΘ₁, ← hΘ₁, h]
  · rw [ha, hb, h₂]

/-- **`Θ` is surjective** if `f₂` is, under the lifting property of `s` over `f₁`. -/
theorem surjective_fibredProductMap (hf₂ : Surjective f₂)
    (hlift : ∀ a₂ k₁, s' k₁ = t' (f₂ a₂) → ∃ a₁, f₁ a₁ = k₁ ∧ s a₁ = t a₂)
    (hΘ₁ : ∀ a, (Θ a : X₁' × X₂').1 = f₁ (a : X₁ × X₂).1)
    (hΘ₂ : ∀ a, (Θ a : X₁' × X₂').2 = f₂ (a : X₁ × X₂).2) : Surjective Θ := fun k => by
  obtain ⟨a₂, ha₂⟩ := hf₂ (k : X₁' × X₂').2
  have hk : s' (k : X₁' × X₂').1 = t' (k : X₁' × X₂').2 := k.2
  obtain ⟨a₁, ha₁, hs⟩ := hlift a₂ _ (hk.trans (congrArg t' ha₂.symm))
  exact ⟨⟨(a₁, a₂), hs⟩, Subtype.ext (Prod.ext ((hΘ₁ _).trans ha₁) ((hΘ₂ _).trans ha₂))⟩

/-- **The fibres of `Θ` are finite** if those of `f₂` are: `a ↦ a₂` injects `Θ⁻¹(k)` into
`f₂⁻¹(k₂)`. -/
theorem finite_fibredProductMap_fiber (hinj : ∀ a₁ b₁, f₁ a₁ = f₁ b₁ → s a₁ = s b₁ → a₁ = b₁)
    (hΘ₁ : ∀ a, (Θ a : X₁' × X₂').1 = f₁ (a : X₁ × X₂).1)
    (hΘ₂ : ∀ a, (Θ a : X₁' × X₂').2 = f₂ (a : X₁ × X₂).2) (k : fibredProduct s' t')
    (hfin : (f₂ ⁻¹' {(k : X₁' × X₂').2}).Finite) : (Θ ⁻¹' {k}).Finite := by
  refine Set.Finite.of_finite_image (f := fibredProductSnd s t) (hfin.subset ?_) ?_
  · rintro _ ⟨a, ha, rfl⟩
    change f₂ (a : X₁ × X₂).2 = (k : X₁' × X₂').2
    rw [← hΘ₂, show Θ a = k from ha]
  · intro a ha b hb hab
    exact fibredProductMap_eq_of_snd_eq hinj hΘ₁ ((show Θ a = k from ha).trans hb.symm) hab

/-- **Sheets of `Θ`**: if `f₂⁻¹(V)` (`V ∋ k₂` open) is the disjoint union of open sheets
`U₂(a₂) ∋ a₂`, `a₂ ∈ f₂⁻¹(k₂)`, on which `f₂` is injective, then `Θ⁻¹(pr₂'⁻¹(V))` is the disjoint
union of the open sheets `pr₂⁻¹(U₂(a₂))`, `a ∈ Θ⁻¹(k)`, on which `Θ` is injective. -/
theorem exists_sheets_fibredProductMap
    (hlift : ∀ a₂ k₁, s' k₁ = t' (f₂ a₂) → ∃ a₁, f₁ a₁ = k₁ ∧ s a₁ = t a₂)
    (hinj : ∀ a₁ b₁, f₁ a₁ = f₁ b₁ → s a₁ = s b₁ → a₁ = b₁)
    (hΘ₁ : ∀ a, (Θ a : X₁' × X₂').1 = f₁ (a : X₁ × X₂).1)
    (hΘ₂ : ∀ a, (Θ a : X₁' × X₂').2 = f₂ (a : X₁ × X₂).2) (k : fibredProduct s' t')
    {V : Set X₂'} {U₂ : X₂ → Set X₂} (hV : IsOpen V) (hkV : (k : X₁' × X₂').2 ∈ V)
    (hd : (f₂ ⁻¹' {(k : X₁' × X₂').2}).PairwiseDisjoint U₂)
    (hU₂ : ∀ a₂ ∈ f₂ ⁻¹' {(k : X₁' × X₂').2}, a₂ ∈ U₂ a₂ ∧ IsOpen (U₂ a₂) ∧ InjOn f₂ (U₂ a₂))
    (hpre : f₂ ⁻¹' V = ⋃ a₂ ∈ f₂ ⁻¹' {(k : X₁' × X₂').2}, U₂ a₂) :
    ∃ (U : Set (fibredProduct s' t')) (U' : fibredProduct s t → Set (fibredProduct s t)),
      IsOpen U ∧ k ∈ U ∧ (Θ ⁻¹' {k}).PairwiseDisjoint U' ∧
      (∀ a ∈ Θ ⁻¹' {k}, a ∈ U' a ∧ IsOpen (U' a) ∧ InjOn Θ (U' a)) ∧
      Θ ⁻¹' U = ⋃ a ∈ Θ ⁻¹' {k}, U' a := by
  have hc : Continuous (fibredProductSnd s t) := continuous_snd.comp continuous_subtype_val
  have hc' : Continuous (fibredProductSnd s' t') := continuous_snd.comp continuous_subtype_val
  have hfib : ∀ a ∈ Θ ⁻¹' {k}, (a : X₁ × X₂).2 ∈ f₂ ⁻¹' {(k : X₁' × X₂').2} := fun a ha => by
    change f₂ (a : X₁ × X₂).2 = (k : X₁' × X₂').2
    rw [← hΘ₂, show Θ a = k from ha]
  refine ⟨fibredProductSnd s' t' ⁻¹' V, fun a => fibredProductSnd s t ⁻¹' U₂ (a : X₁ × X₂).2,
    hV.preimage hc', hkV, ?_, fun a ha => ⟨(hU₂ _ (hfib a ha)).1,
      (hU₂ _ (hfib a ha)).2.1.preimage hc, ?_⟩, ?_⟩
  · intro a ha b hb hab
    have hne : (a : X₁ × X₂).2 ≠ (b : X₁ × X₂).2 := fun h2 =>
      hab (fibredProductMap_eq_of_snd_eq hinj hΘ₁ ((show Θ a = k from ha).trans hb.symm) h2)
    exact (hd (hfib a ha) (hfib b hb) hne).preimage _
  · intro b hb c hc' hbc
    have h2 : (b : X₁ × X₂).2 = (c : X₁ × X₂).2 :=
      (hU₂ _ (hfib a ha)).2.2 hb hc' (by rw [← hΘ₂, ← hΘ₂, hbc])
    exact fibredProductMap_eq_of_snd_eq hinj hΘ₁ hbc h2
  · ext b
    simp only [mem_preimage, mem_iUnion, exists_prop]
    constructor
    · intro hb
      have hb' : (b : X₁ × X₂).2 ∈ f₂ ⁻¹' V := by
        change f₂ (b : X₁ × X₂).2 ∈ V
        rw [← hΘ₂]; exact hb
      rw [hpre] at hb'
      obtain ⟨a₂, ha₂, hba⟩ := mem_iUnion₂.1 hb'
      have hk : s' (k : X₁' × X₂').1 = t' (k : X₁' × X₂').2 := k.2
      obtain ⟨a₁, ha₁, hs⟩ := hlift a₂ _ (hk.trans (congrArg t' (show f₂ a₂ = _ from ha₂).symm))
      exact ⟨⟨(a₁, a₂), hs⟩, Subtype.ext (Prod.ext ((hΘ₁ _).trans ha₁) ((hΘ₂ _).trans ha₂)), hba⟩
    · rintro ⟨a, ha, hba⟩
      have hb' : (b : X₁ × X₂).2 ∈ f₂ ⁻¹' V := by
        rw [hpre]; exact mem_iUnion₂.2 ⟨_, hfib a ha, hba⟩
      change (Θ b : X₁' × X₂').2 ∈ V
      rw [hΘ₂]; exact hb'

end FibredProductMap

end MPolyfold

/-! ### The pulled-back strong bundles over fibred products -/

section FibredProductBundle

open MPolyfold

variable {X₁ : Type*} [TopologicalSpace X₁] [T2Space X₁] [ParacompactSpace X₁] {P₁ : MPolyfold X₁}
  {X₂ : Type*} [TopologicalSpace X₂] [T2Space X₂] [ParacompactSpace X₂] {P₂ : MPolyfold X₂}
  {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {X₁' : Type*} [TopologicalSpace X₁'] [T2Space X₁'] [ParacompactSpace X₁'] {P₁' : MPolyfold X₁'}
  {X₂' : Type*} [TopologicalSpace X₂'] [T2Space X₂'] [ParacompactSpace X₂'] {P₂' : MPolyfold X₂'}
  {Z' : Type*} [TopologicalSpace Z'] [T2Space Z'] [ParacompactSpace Z'] {PZ' : MPolyfold Z'}
  {s : X₁ → Z} {t : X₂ → Z} {s' : X₁' → Z'} {t' : X₂' → Z'} {f₁ : X₁ → X₁'} {f₂ : X₂ → X₂'}
  {Θ : fibredProduct s t → fibredProduct s' t'}
  [ParacompactSpace (X₁ × X₂)] [ParacompactSpace (fibredProduct s t)]
  [ParacompactSpace (X₁' × X₂')] [ParacompactSpace (fibredProduct s' t')]
  (hs : P₁.IsLocalScDiffeo PZ s) (ht : P₂.IsScSmoothMap PZ t)
  (hs' : P₁'.IsLocalScDiffeo PZ' s') (ht' : P₂'.IsScSmoothMap PZ' t')
  {E₂ : Type*} [TopologicalSpace E₂] [T2Space E₂] [ParacompactSpace E₂] {q₂ : E₂ → X₂}
  [∀ x, AddCommGroup (q₂ ⁻¹' {x})] [∀ x, Module ℝ (q₂ ⁻¹' {x})]
  {E₂' : Type*} [TopologicalSpace E₂'] [T2Space E₂'] [ParacompactSpace E₂'] {q₂' : E₂' → X₂'}
  [∀ x, AddCommGroup (q₂' ⁻¹' {x})] [∀ x, Module ℝ (q₂' ⁻¹' {x})]
  [ParacompactSpace (pullbackSpace q₂ (fibredProductSnd s t))]
  [ParacompactSpace (pullbackSpace q₂' (fibredProductSnd s' t'))]
  {B₂ : StrongBundle P₂ q₂} {B₂' : StrongBundle P₂' q₂'} {Φ : E₂ → E₂'}

namespace StrongBundle

/-- `pr₂ : X₁ ₛ×ₜ X₂ → X₂` is sc-smooth on the sub-M-polyfold. -/
theorem isScSmoothMap_fibredProductSnd :
    (subPolyfold (isSubMPolyfold_fibredProduct hs ht)).IsScSmoothMap P₂ (fibredProductSnd s t) :=
  (isLocalScDiffeo_sndOfFibredProduct hs ht).isScSmoothMap

variable (q₂ q₂' Θ Φ) in
/-- **`Θ̃ = (Θ ∘ π, Φ ∘ π') : pr₂*E₂ → pr₂'*E₂'`**, `((x₁, x₂), e) ↦ (Θ(x₁, x₂), Φ(e))`. -/
def fibredProductLift (hΘ₂ : ∀ a, (Θ a : X₁' × X₂').2 = f₂ (a : X₁ × X₂).2)
    (hΦ : ∀ e, q₂' (Φ e) = f₂ (q₂ e)) :
    pullbackSpace q₂ (fibredProductSnd s t) → pullbackSpace q₂' (fibredProductSnd s' t') :=
  pullbackPair q₂' (fibredProductSnd s' t') (Θ ∘ pullbackProj q₂ (fibredProductSnd s t))
    (Φ ∘ pullbackProj' q₂ (fibredProductSnd s t)) fun z =>
      (hΦ _).trans ((congrArg f₂ z.2).trans (hΘ₂ _).symm)

/-- **`Θ̃` is a strong bundle map covering `Θ`** between the pull-backs of `E₂`, `E₂'` by the
second projections. -/
theorem isStrongBundleMap_fibredProductLift (hΦ : B₂.IsStrongBundleMap B₂' f₂ Φ)
    (hΘ : (subPolyfold (isSubMPolyfold_fibredProduct hs ht)).IsScSmoothMap
      (subPolyfold (isSubMPolyfold_fibredProduct hs' ht')) Θ)
    (hΘ₂ : ∀ a, (Θ a : X₁' × X₂').2 = f₂ (a : X₁ × X₂).2) :
    (B₂.pullback (isScSmoothMap_fibredProductSnd hs ht)).IsStrongBundleMap
      (B₂'.pullback (isScSmoothMap_fibredProductSnd hs' ht')) Θ
      (fibredProductLift Θ q₂ q₂' Φ hΘ₂ hΦ.covers) :=
  isStrongBundleMap_pullbackPair B₂' (isScSmoothMap_fibredProductSnd hs' ht') hΘ
    ((hΦ.comp (B₂.isStrongBundleMap_pullbackProj'
      (isScSmoothMap_fibredProductSnd hs ht))).congr_base
      (funext fun a => (hΘ₂ a).symm))

/-- **`Θ̃` is near every point a strong bundle isomorphism** if `Φ` is: `π' ∘ Θ̃ = Φ ∘ π` with the
projections `π`, `π'` of the pull-backs local strong bundle isomorphisms (the second projections
being local sc-diffeomorphisms). -/
theorem isLocalStrongBundleIso_fibredProductLift (hΦ : B₂.IsStrongBundleMap B₂' f₂ Φ)
    (hΦloc : ∀ x, ∃ (U : Set X₂) (U' : Set X₂'), x ∈ U ∧ B₂.IsStrongBundleIsoOn B₂' hΦ U U')
    (hΘ : (subPolyfold (isSubMPolyfold_fibredProduct hs ht)).IsScSmoothMap
      (subPolyfold (isSubMPolyfold_fibredProduct hs' ht')) Θ)
    (hΘ₂ : ∀ a, (Θ a : X₁' × X₂').2 = f₂ (a : X₁ × X₂).2) (y : fibredProduct s t) :
    ∃ (U : Set (fibredProduct s t)) (U' : Set (fibredProduct s' t')), y ∈ U ∧
      (B₂.pullback (isScSmoothMap_fibredProductSnd hs ht)).IsStrongBundleIsoOn
        (B₂'.pullback (isScSmoothMap_fibredProductSnd hs' ht'))
        (isStrongBundleMap_fibredProductLift hs ht hs' ht' hΦ hΘ hΘ₂) U U' := by
  obtain ⟨U₁, V₁, σ₁, hy, hd₁⟩ := isLocalScDiffeo_sndOfFibredProduct hs ht y
  have hπ₁ := B₂.isStrongBundleIsoOn_pullbackProj' (isScSmoothMap_fibredProductSnd hs ht) hd₁ y
  obtain ⟨U₂, U₂', hm, hp⟩ := hΦloc (y : X₁ × X₂).2
  obtain ⟨U₀, U₀'', hy₀, hc₀⟩ := hp.exists_comp hπ₁ hy hm
  obtain ⟨V, V', σ, hV, hd⟩ := isLocalScDiffeo_sndOfFibredProduct hs' ht' (Θ y)
  have hπ := B₂'.isStrongBundleIsoOn_pullbackProj' (isScSmoothMap_fibredProductSnd hs' ht') hd
    (Θ y)
  obtain ⟨g, hg⟩ := hc₀.isScDiffeoOn_base
  have hΘc : Continuous Θ := continuousOn_univ.1 hΘ.continuousOn
  have hW : IsOpen (U₀ ∩ Θ ⁻¹' V) := hg.isOpen_source.inter (hd.isOpen_source.preimage hΘc)
  have hc := (hc₀.restrict hg hW inter_subset_left).of_eq
    (f' := fibredProductSnd s' t' ∘ Θ) (funext fun a => (hΘ₂ a).symm)
  have hc' : (B₂.pullback (isScSmoothMap_fibredProductSnd hs ht)).IsStrongBundleIsoOn B₂'
      ((B₂'.isStrongBundleMap_pullbackProj' (isScSmoothMap_fibredProductSnd hs' ht')).comp
        (isStrongBundleMap_fibredProductLift hs ht hs' ht' hΦ hΘ hΘ₂))
      (U₀ ∩ Θ ⁻¹' V) (U₀'' ∩ g ⁻¹' (U₀ ∩ Θ ⁻¹' V)) := hc
  exact ⟨U₀ ∩ Θ ⁻¹' V, _, ⟨hy₀, hV⟩,
    hc'.of_comp (h := isStrongBundleMap_fibredProductLift hs ht hs' ht' hΦ hΘ hΘ₂) hπ
      fun _ hx => hx.2⟩

end StrongBundle

/-- **The fibred-product square of a proper strong bundle covering square is one** (Definition
19.8.19, read form): if `Φ : E₂ → E₂'` over `f₂` is a proper strong bundle covering square, `f₁`
is continuous and `s` is fibrewise bijective over `f₁` (`hlift`, `hinj`), then
`Θ̃ : pr₂*E₂ → pr₂'*E₂'` over `Θ = f₁ ₛ×ₜ f₂ : X₁ ₛ×ₜ X₂ → X₁' ₛ'×ₜ' X₂'` is a proper strong
bundle covering square. -/
theorem isProperStrongBundleCoveringSquare_fibredProduct
    (hsq : IsProperStrongBundleCoveringSquare B₂ B₂' f₂ Φ) (hf₁ : Continuous f₁)
    (hΘ₁ : ∀ a, (Θ a : X₁' × X₂').1 = f₁ (a : X₁ × X₂).1)
    (hΘ₂ : ∀ a, (Θ a : X₁' × X₂').2 = f₂ (a : X₁ × X₂).2)
    (hlift : ∀ a₂ k₁, s' k₁ = t' (f₂ a₂) → ∃ a₁, f₁ a₁ = k₁ ∧ s a₁ = t a₂)
    (hinj : ∀ a₁ b₁, f₁ a₁ = f₁ b₁ → s a₁ = s b₁ → a₁ = b₁) :
    IsProperStrongBundleCoveringSquare
      (B₂.pullback (StrongBundle.isScSmoothMap_fibredProductSnd hs ht))
      (B₂'.pullback (StrongBundle.isScSmoothMap_fibredProductSnd hs' ht')) Θ
      (StrongBundle.fibredProductLift Θ q₂ q₂' Φ hΘ₂ hsq.isStrongBundleMap.covers) := by
  have hΘc : Continuous Θ :=
    continuous_fibredProductMap hf₁ hsq.isLocalScDiffeo.continuous hΘ₁ hΘ₂
  have hΘd := isLocalScDiffeo_fibredProductMap hs ht hs' ht' hsq.isLocalScDiffeo hΘc hΘ₂
  have hΦloc : ∀ x, ∃ (U : Set X₂) (U' : Set X₂'), x ∈ U ∧
      B₂.IsStrongBundleIsoOn B₂' hsq.isStrongBundleMap U U' := fun x => by
    obtain ⟨U, U', -, -, -, hsh, -⟩ := hsq.evenlyCovered (f₂ x)
    exact ⟨U' x, U, (hsh x rfl).1, (hsh x rfl).2⟩
  refine isProperStrongBundleCoveringSquare_of_sheets
    (StrongBundle.isStrongBundleMap_fibredProductLift hs ht hs' ht' hsq.isStrongBundleMap
      hΘd.isScSmoothMap hΘ₂)
    (surjective_fibredProductMap hsq.surjective hlift hΘ₁ hΘ₂) hΘd
    (fun k => finite_fibredProductMap_fiber hinj hΘ₁ hΘ₂ k (hsq.finite_fiber _))
    (StrongBundle.isLocalStrongBundleIso_fibredProductLift hs ht hs' ht' hsq.isStrongBundleMap hΦloc
      hΘd.isScSmoothMap hΘ₂) fun k => ?_
  obtain ⟨V, U₂, hV, hkV, hd, hsh, hpre⟩ := hsq.evenlyCovered (k : X₁' × X₂').2
  refine exists_sheets_fibredProductMap hlift hinj hΘ₁ hΘ₂ k hV hkV hd (fun a₂ ha₂ => ?_) hpre
  obtain ⟨g, hg⟩ := (hsh a₂ ha₂).2.isScDiffeoOn_base
  exact ⟨(hsh a₂ ha₂).1, hg.isOpen_source, fun b hb c hc hbc => by
    rw [← hg.left_inv b hb, ← hg.left_inv c hc, hbc]⟩

end FibredProductBundle

end

end Polyfold
