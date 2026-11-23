import Polyfold.Chapter15.CanonicalOrientationLocal
import Polyfold.Chapter14.LocalScPlus

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702 (**Theorem 15.4.1**), and Part I, §6.6 (Definition 6.6.2, Theorem 6.6.18).

# The orientation of a kernel under a conjugation between two strong bundles

## The text, paraphrased

(pp. 701–702) For an oriented sc-Fredholm section `f` and a local sc⁺-section `s` with
`f(y) = s(y)` and `(f − s)'(y)` onto, the orientation `o_y` of `DET(f, y)` gives an orientation
of `ker (f − s)'(y)`.  The construction is local at `y`.

## What is formalized

* `exists_ray_wedge_map_iff`: for an isomorphism `κ : N ≅ N'` of subspaces given by a map `D` of
  the ambient spaces, a ray `r` of `λ(N)` is spanned by `w₁ ∧ … ∧ wₙ` iff `λ(κ) r` is spanned by
  `D w₁ ∧ … ∧ D wₙ`.
* **`ChartPoint.orKer_conj`**, **`ChartPoint.exists_ray_orKer_conj_iff`**: for chart points
  `a`, `a'` of two strong bundles and a conjugation `S' A = Γ S` of onto members of the two sets
  `Lin`, the orientation of `ker S'` for the conjugated orientation is `λ(A|ker)` of the
  orientation of `ker S`; a tuple spans the one iff its image spans the other.
* `ChartPoint.tangentOr_orSectionAdd_eq_orKer`: Part I's tangent orientation of `f + s` for the
  inherited orientation is the orientation of the kernel of §15.4.
* **`StrongBundle.LocalIso.orTransfer_mpullPt_orxViaAt`**: the orientation map `orxViaAt` of a
  local strong bundle isomorphism `L`, read in the chart point carried from `p`, is `morPull`
  of the orientation read in `p`.
* `isZeroAt_sectionAdd_neg_iff`: `f + (−1) s` vanishes exactly where `f = s`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Module

noncomputable section

namespace Polyfold

open StrongRetr

universe u v u' v'

/-! ### Rays through wedges and isomorphisms of subspaces -/

/-- **A ray through a wedge and its image**: for subspaces `N ⊆ V`, `N' ⊆ V'`, an isomorphism
`κ : N ≅ N'` which is the restriction of an injective map `D : V → V'`, and a ray `r` of `λ(N)`:
`λ(κ) r` is the ray of `D w₁ ∧ … ∧ D wₙ` iff `r` is the ray of `w₁ ∧ … ∧ wₙ`. -/
theorem exists_ray_wedge_map_iff {V V' : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V']
    [Module ℝ V'] {N : Submodule ℝ V} {N' : Submodule ℝ V'} (κ : N ≃ₗ[ℝ] N') (D : V → V')
    (hD : Injective D) (hκ : ∀ v : N, ((κ v : N') : V') = D v) {n : ℕ} (hn : n = finrank ℝ N)
    (hn' : n = finrank ℝ N') (w : Fin n → V) (w' : Fin n → V') (hw : ∀ i, w' i = D (w i))
    (r : Module.Ray ℝ (maxPow N)) :
    (∃ (hmem : ∀ i, w' i ∈ N') (hne : wedge (fun i => (⟨w' i, hmem i⟩ : N')) hn' ≠ 0),
        Module.Ray.map (maxPowEquiv κ) r = rayOfNeZero ℝ _ hne) ↔
      ∃ (hmem : ∀ i, w i ∈ N) (hne : wedge (fun i => (⟨w i, hmem i⟩ : N)) hn ≠ 0),
        r = rayOfNeZero ℝ _ hne := by
  obtain rfl : w' = fun i => D (w i) := funext hw
  have key : ∀ (hmem : ∀ i, w i ∈ N) (hmem' : ∀ i, D (w i) ∈ N'),
      maxPowEquiv κ (wedge (fun i => (⟨w i, hmem i⟩ : N)) hn) =
        wedge (fun i => (⟨D (w i), hmem' i⟩ : N')) hn' := fun hmem hmem' => by
    rw [maxPowEquiv_wedge]
    congr 1
    exact funext fun i => Subtype.ext (hκ ⟨w i, hmem i⟩)
  constructor
  · rintro ⟨hmem', hne', he⟩
    have hmem : ∀ i, w i ∈ N := fun i => by
      have h1 := hκ (κ.symm ⟨D (w i), hmem' i⟩)
      rw [κ.apply_symm_apply] at h1
      rw [hD h1]
      exact (κ.symm ⟨D (w i), hmem' i⟩).2
    have hk := key hmem hmem'
    have hne : wedge (fun i => (⟨w i, hmem i⟩ : N)) hn ≠ 0 := fun h0 => hne' (by
      rw [← hk, h0, map_zero])
    refine ⟨hmem, hne, (Module.Ray.map (maxPowEquiv κ)).injective ?_⟩
    rw [he, Module.Ray.map_apply]
    exact rayOfNeZero_congr hk.symm _ _
  · rintro ⟨hmem, hne, rfl⟩
    have hmem' : ∀ i, D (w i) ∈ N' := fun i => by
      rw [← hκ ⟨w i, hmem i⟩]
      exact (κ ⟨w i, hmem i⟩).2
    have hk := key hmem hmem'
    have hne' : wedge (fun i => (⟨D (w i), hmem' i⟩ : N')) hn' ≠ 0 := by
      rw [← hk]
      exact (maxPowEquiv κ).map_ne_zero_iff.2 hne
    refine ⟨hmem', hne', ?_⟩
    rw [Module.Ray.map_apply]
    exact rayOfNeZero_congr hk _ _

/-! ### The zeros of `f − s` -/

/-- **`f + (−1) s` vanishes exactly where `f = s`.** -/
theorem isZeroAt_sectionAdd_neg_iff {X : Type u} {Y : Type v} {P : Y → X}
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {f s : X → Y}
    (hf : IsSection P f) (hs : IsSection P s) (y : X) :
    IsZeroAt P (sectionAdd P f (sectionSmul P (fun _ => (-1 : ℝ)) s)) y ↔ f y = s y := by
  have hval : sectionAdd P f (sectionSmul P (fun _ => (-1 : ℝ)) s) y =
      (((⟨f y, hf y⟩ : P ⁻¹' {y}) + ((-1 : ℝ) • (⟨s y, hs y⟩ : P ⁻¹' {y})) : P ⁻¹' {y}) : Y) := by
    rw [sectionAdd_apply hf hs.sectionSmul]
    congr 2
    exact Subtype.ext (sectionSmul_apply (f := fun _ => (-1 : ℝ)) hs y)
  unfold IsZeroAt
  rw [hval, neg_one_smul, ← sub_eq_add_neg]
  constructor
  · intro h
    have h' : ((⟨f y, hf y⟩ : P ⁻¹' {y}) - ⟨s y, hs y⟩ : P ⁻¹' {y}) = 0 := Subtype.ext h
    exact congrArg Subtype.val (sub_eq_zero.1 h')
  · intro h
    have h' : (⟨f y, hf y⟩ : P ⁻¹' {y}) = ⟨s y, hs y⟩ := Subtype.ext h
    rw [h', sub_self]
    rfl

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {f : X → Y} {f' : X' → Y'}

/-! ### The orientation of the kernel under a conjugation -/

namespace ChartPoint

variable {y : X} {y' : X'} (a : ChartPoint B y) (a' : ChartPoint B' y')

/-- **The orientation of the kernel is carried by a conjugation between two bundles**: for chart
points `a`, `a'`, isomorphisms `AT : T_zO ≅ T_{z'}O'`, `AK : K_z ≅ K_{z'}` conjugating
`Lin(f', y')` into `Lin(f, y)` and onto members `S`, `S'` with `S' AT = AK S`, the orientation
of `ker S'` for the conjugated orientation is `λ(AT|ker S)` of the orientation of `ker S`. -/
theorem orKer_conj (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (AT : ↥a.T ≃L[ℝ] ↥a'.T) (AK : ↥a.K ≃L[ℝ] ↥a'.K)
    (hmem : ∀ S' ∈ a'.linSet f', ((AK.symm : ↥a'.K →L[ℝ] ↥a.K) ∘L S' ∘L
      (AT : ↥a.T →L[ℝ] ↥a'.T)) ∈ a.linSet f)
    (o : a.Or f hf) {S : ↥a.T →L[ℝ] ↥a.K} (hS : S ∈ a.linSet f) {S' : ↥a'.T →L[ℝ] ↥a'.K}
    (hS' : S' ∈ a'.linSet f') (hconj : ∀ v, S' (AT v) = AK (S v)) (h : Surjective S)
    (h' : Surjective S') {N : Submodule ℝ (a.c.φ.model.E 0)}
    (hN : (LinearMap.ker (S : ↥a.T →ₗ[ℝ] ↥a.K)).map
      (a.T.subtypeL : ↥a.T →ₗ[ℝ] a.c.φ.model.E 0) = N)
    {N' : Submodule ℝ (a'.c.φ.model.E 0)}
    (hN' : (LinearMap.ker (S' : ↥a'.T →ₗ[ℝ] ↥a'.K)).map
      (a'.T.subtypeL : ↥a'.T →ₗ[ℝ] a'.c.φ.model.E 0) = N') :
    a'.orKer (hf := hf') (o.conj (hC' := a'.isFredholm_of_mem_linSet hf') AT AK hmem) hS' h' hN' =
      Module.Ray.map (maxPowEquiv (conjKerEquivOfMap AT AK hconj a.T.subtypeL
        Subtype.val_injective hN a'.T.subtypeL Subtype.val_injective hN'))
        (a.orKer o hS h hN) :=
  (congrArg (surjRay h' a'.T.subtypeL Subtype.val_injective hN')
    (LineOrientation.conj_apply (hC' := a'.isFredholm_of_mem_linSet hf') AT AK hmem o hS hS'
      hconj)).trans (surjRay_conjDet _ _ h h' hconj _ _ hN _ _ hN' _)

/-- **A tuple spans the orientation of `ker S'` iff its preimage spans that of `ker S`**, in
the situation of `orKer_conj`, when `AT` is the restriction of an injective map `D` of the
model spaces. -/
theorem exists_ray_orKer_conj_iff (hf : B.IsScFredholmSection f)
    (hf' : B'.IsScFredholmSection f') (AT : ↥a.T ≃L[ℝ] ↥a'.T) (AK : ↥a.K ≃L[ℝ] ↥a'.K)
    (D : a.c.φ.model.E 0 → a'.c.φ.model.E 0) (hD : Injective D)
    (hAT : ∀ v : ↥a.T, ((AT v : ↥a'.T) : a'.c.φ.model.E 0) = D (v : a.c.φ.model.E 0))
    (hmem : ∀ S' ∈ a'.linSet f', ((AK.symm : ↥a'.K →L[ℝ] ↥a.K) ∘L S' ∘L
      (AT : ↥a.T →L[ℝ] ↥a'.T)) ∈ a.linSet f)
    (o : a.Or f hf) {S : ↥a.T →L[ℝ] ↥a.K} (hS : S ∈ a.linSet f) {S' : ↥a'.T →L[ℝ] ↥a'.K}
    (hS' : S' ∈ a'.linSet f') (hconj : ∀ v, S' (AT v) = AK (S v)) (h : Surjective S)
    (h' : Surjective S') {N : Submodule ℝ (a.c.φ.model.E 0)}
    (hN : (LinearMap.ker (S : ↥a.T →ₗ[ℝ] ↥a.K)).map
      (a.T.subtypeL : ↥a.T →ₗ[ℝ] a.c.φ.model.E 0) = N)
    {N' : Submodule ℝ (a'.c.φ.model.E 0)}
    (hN' : (LinearMap.ker (S' : ↥a'.T →ₗ[ℝ] ↥a'.K)).map
      (a'.T.subtypeL : ↥a'.T →ₗ[ℝ] a'.c.φ.model.E 0) = N') {n : ℕ} (hn : n = finrank ℝ N)
    (hn' : n = finrank ℝ N') (w : Fin n → a.c.φ.model.E 0) (w' : Fin n → a'.c.φ.model.E 0)
    (hw : ∀ i, w' i = D (w i)) :
    (∃ (hm : ∀ i, w' i ∈ N') (hne : wedge (fun i => (⟨w' i, hm i⟩ : N')) hn' ≠ 0),
        a'.orKer (hf := hf') (o.conj (hC' := a'.isFredholm_of_mem_linSet hf') AT AK hmem) hS' h'
          hN' = rayOfNeZero ℝ _ hne) ↔
      ∃ (hm : ∀ i, w i ∈ N) (hne : wedge (fun i => (⟨w i, hm i⟩ : N)) hn ≠ 0),
        a.orKer o hS h hN = rayOfNeZero ℝ _ hne := by
  rw [a.orKer_conj a' hf hf' AT AK hmem o hS hS' hconj h h' hN hN']
  refine exists_ray_wedge_map_iff _ D hD (fun v => ?_) hn hn' w w' hw _
  obtain ⟨u, rfl⟩ := (kerEquivOfMap S a.T.subtypeL Subtype.val_injective hN).surjective v
  exact (coe_conjKerEquivOfMap _ _ hconj _ _ hN _ _ hN' u).trans (hAT u.1)

/-- The isomorphism `ker S ≅ ker S'` of `orKer_conj`, read in the model spaces, is the
restriction of `D`. -/
theorem coe_conjKerEquivOfMap_eq (AT : ↥a.T ≃L[ℝ] ↥a'.T) (AK : ↥a.K ≃L[ℝ] ↥a'.K)
    (D : a.c.φ.model.E 0 → a'.c.φ.model.E 0)
    (hAT : ∀ v : ↥a.T, ((AT v : ↥a'.T) : a'.c.φ.model.E 0) = D (v : a.c.φ.model.E 0))
    {S : ↥a.T →L[ℝ] ↥a.K} {S' : ↥a'.T →L[ℝ] ↥a'.K} (hconj : ∀ v, S' (AT v) = AK (S v))
    {N : Submodule ℝ (a.c.φ.model.E 0)}
    (hN : (LinearMap.ker (S : ↥a.T →ₗ[ℝ] ↥a.K)).map
      (a.T.subtypeL : ↥a.T →ₗ[ℝ] a.c.φ.model.E 0) = N)
    {N' : Submodule ℝ (a'.c.φ.model.E 0)}
    (hN' : (LinearMap.ker (S' : ↥a'.T →ₗ[ℝ] ↥a'.K)).map
      (a'.T.subtypeL : ↥a'.T →ₗ[ℝ] a'.c.φ.model.E 0) = N') (v : N) :
    ((conjKerEquivOfMap AT AK hconj a.T.subtypeL Subtype.val_injective hN a'.T.subtypeL
      Subtype.val_injective hN' v : N') : a'.c.φ.model.E 0) = D v := by
  obtain ⟨u, rfl⟩ := (kerEquivOfMap S a.T.subtypeL Subtype.val_injective hN).surjective v
  exact (coe_conjKerEquivOfMap _ _ hconj _ _ hN _ _ hN' u).trans (hAT u.1)

/-- **The tangent orientation of `f + s` for the inherited orientation is the orientation of
`ker (f + s)'(x)` induced by `o`** (`tangentOr_orSectionAdd`, with the kernel orientation
`orKer` of §15.4). -/
theorem tangentOr_orSectionAdd_eq_orKer (hf : B.IsScFredholmSection f) {s : X → Y}
    (hs : B.IsScPlusSection s) (hx : IsZeroAt P (sectionAdd P f s) y)
    (hL : B.IsLinSurjAt (sectionAdd P f s) y) (o : a.Or f hf) :
    a.tangentOr (theorem_3_1_18_preprint hf hs) hx hL (a.orSectionAdd hf hs o) =
      a.orKer o (a.linZero_mem_linSet_of_sectionAdd hf hs hx)
        (a.linZero_surjective (theorem_3_1_18_preprint hf hs) hx hL)
        (a.map_ker_linZero (theorem_3_1_18_preprint hf hs) hx) :=
  a.tangentOr_orSectionAdd hf hs hx hL o

end ChartPoint

/-! ### The orientation map of a local isomorphism in a carried chart point -/

namespace StrongBundle.LocalIso

variable {U : Set X} {U' : Set X'} (L : StrongBundle.LocalIso B B' U U') {x : X'} {a : X}

/-- **The orientation map of `L` read in a carried chart point**: for `o ∈ Or_x^{f'}`, the image
`orxViaAt o ∈ Or_a^f` read in the chart point carried from `p` is `morPull` of the orientation
`o` read in `p`. -/
theorem orTransfer_mpullPt_orxViaAt (hf : B.IsScFredholmSection f)
    (hf' : B'.IsScFredholmSection f') (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U)
    (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough) (ha : a ∈ U)
    (has : a ∈ PX.smoothSet) (hϕ : L.ϕ a = x) (p : ChartPoint B' x) (hp : p.c.φ.source ⊆ U')
    (o : Orx f' hf' x (L.mem_smoothSet_of_ϕ_eq ha has hϕ)) :
    (orxPt B a has).orTransfer (L.mpullPt p hp ha hϕ) hf has
        (L.orxViaAt hf hf' hfL hsec hsec' ha has hϕ o) =
      L.morPull hf hf' p hp ha hϕ (linSet_mpullPt hf hf' hfL hsec hsec' has
          (L.mem_smoothSet_of_ϕ_eq ha has hϕ))
        ((orxPt B' x (L.mem_smoothSet_of_ϕ_eq ha has hϕ)).orTransfer p hf'
          (L.mem_smoothSet_of_ϕ_eq ha has hϕ) o) := by
  rw [L.orxViaAt_eq_morVia hf hf' hfL hsec hsec' ha has hϕ p hp]
  unfold morVia
  simp only [Equiv.trans_apply]
  have h := DFunLike.congr_fun (((L.mpullPt p hp ha hϕ).orTransfer_trans (orxPt B a has)
    (L.mpullPt p hp ha hϕ) hf has).trans ((L.mpullPt p hp ha hϕ).orTransfer_self hf has))
    (L.morPull hf hf' p hp ha hϕ (linSet_mpullPt hf hf' hfL hsec hsec' has
      (L.mem_smoothSet_of_ϕ_eq ha has hϕ))
      ((orxPt B' x (L.mem_smoothSet_of_ϕ_eq ha has hϕ)).orTransfer p hf'
        (L.mem_smoothSet_of_ϕ_eq ha has hϕ) o))
  simpa only [Equiv.trans_apply, Equiv.refl_apply] using h

end StrongBundle.LocalIso

end Polyfold
