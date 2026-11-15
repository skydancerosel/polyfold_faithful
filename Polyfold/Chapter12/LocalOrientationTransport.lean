import Polyfold.Chapter12.LocalOrientationDomains
import Polyfold.Chapter6.TransportOrientationSpace

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6,
Theorem 6.6.11 (p. 272) and the proof of Theorem 6.6.13 (pp. 273–274), with Definition 6.2.1
(p. 239) for the linearizations.

# Propagation of the local orientation sets along sc-smooth paths

## The text, paraphrased

For an sc-Fredholm section `f` of a strong bundle over a tame M-polyfold, Theorem 6.6.11 gives
around every smooth point an open neighbourhood with the local propagation property: an
orientation of `DET(f, x)` is carried along sc-smooth paths in the neighbourhood, by
continuation in the determinant bundle of a family of linearizations over the path.  The proof
of Theorem 6.6.13 cuts an arbitrary sc-smooth path into pieces lying in such neighbourhoods and
composes the maps of the pieces; the result `Or_{φ(0)}^f → Or_{φ(1)}^f` does not depend on the
choices.  The linearizations are those of `f − s` for locally defined sc⁺-sections `s`, for
instance written in a strong bundle chart (Definition 6.2.1 and Proposition 6.6.3).

## What is formalized

The propagation for the local orientation sets `OrxLoc hf x hs`, with the hypotheses "`X` is
tame" and "`f` has tame germ data" only.  The propagation along a path is made in the
restriction of the bundle to an open subset `W` of a chart domain containing the path (a
*domain*, `StrongBundle.Dom`), where the sc⁺-sections of Proposition 6.6.3 are written in the
chart, and it does not depend on the subset.

* `Dom.liftPath`: an sc-smooth path in `X` with all values in a domain `W`, as an sc-smooth path
  in `W` (`Dom.isScSmoothMap_liftPath`); conversely `Dom.isScSmoothMap_val_comp`.
* `Dom.transportLoc`: the map `Or_{x₀}^f ≃ Or_{x₁}^f` along an sc-smooth path from `x₀` to `x₁`
  with all values in `W`: the transport of `f|W` along the path, read through the
  identifications `Dom.toLoc`.
* `Dom.transportLoc_of_subset`, `Dom.transportLoc_eq`: **the map does not depend on the
  domain** containing the path.
* `Dom.transportLoc_halves`, `Dom.transportLoc_reparam`, `Dom.transportLoc_smoothTransPath`,
  `Dom.transportLoc_trans_of_good`: composition over the two halves of a path, invariance under
  reparametrization, composition in a good set of `W`.
* `orLocalTransportLoc hX hf`: **the local transport data of the sets `Or_x^f`**.  A good set is
  an open set `U` inside a domain `W` which, as a subset of `W`, has the local propagation
  property for `f|W` in a chart of `P|W`.
* `orLocalTransportLoc_transport_eq`: **the transport along an sc-smooth path with all values in
  a domain `W` is `Dom.transportLoc`**, the transport of `f|W` (Theorem 6.6.13, property (∗),
  for all paths in a domain).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- Conjugates of a composite: if `T = T₁ ∘ T₂` then the conjugate of `T` is the composite of
the conjugates of `T₁` and `T₂`. -/
private theorem conj_trans_of_eq {α β γ α' β' γ' : Sort*} (a : α ≃ α') (b : β ≃ β')
    (c : γ ≃ γ') {T : α' ≃ γ'} {T₁ : α' ≃ β'} {T₂ : β' ≃ γ'} (h : T = T₁.trans T₂) :
    a.trans (T.trans c.symm) =
      (a.trans (T₁.trans b.symm)).trans (b.trans (T₂.trans c.symm)) := by
  subst h
  ext x
  simp

namespace StrongBundle.Dom

variable (D D' : B.Dom)

/-! ### Paths in a domain -/

/-- **A path in `X` with all values in a domain `W`, as a path in `W`.** -/
def liftPath (γ : (Fin 1 → ℝ) → X) (hγD : ∀ q, γ q ∈ D.carrier) : (Fin 1 → ℝ) → D.carrier :=
  fun q => ⟨γ q, hγD q⟩

@[simp] theorem liftPath_val (γ : (Fin 1 → ℝ) → X) (hγD : ∀ q, γ q ∈ D.carrier)
    (q : Fin 1 → ℝ) : (D.liftPath γ hγD q).1 = γ q := rfl

/-- An sc-smooth path in `X` with all values in a domain `W` is an sc-smooth path in `W`. -/
theorem isScSmoothMap_liftPath {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγD : ∀ q, γ q ∈ D.carrier) :
    (rnPolyfold 1).IsScSmoothMap (PX.restrictOpen D.isOpen) (D.liftPath γ hγD) :=
  MPolyfold.IsScSmoothMap.codRestrict_restrictOpen D.isOpen hγ hγD

/-- An sc-smooth path in a domain is an sc-smooth path in `X`. -/
theorem isScSmoothMap_val_comp {γ : (Fin 1 → ℝ) → D.carrier}
    (hγ : (rnPolyfold 1).IsScSmoothMap (PX.restrictOpen D.isOpen) γ) :
    (rnPolyfold 1).IsScSmoothMap PX fun q => (γ q).1 :=
  (MPolyfold.isScSmoothMap_subtypeVal D.isOpen).comp hγ

/-! ### The transport read in a domain -/

/-- **The propagation of `Or^f` along a path in a domain `W`**: for an sc-smooth path `γ` from
`x₀` to `x₁` with all values in `W`, the transport `Or_{x₀}^{f|W} ≃ Or_{x₁}^{f|W}` of `f|W`
along `γ`, read as a map `Or_{x₀}^f ≃ Or_{x₁}^f`. -/
def transportLoc (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f) (γ : (Fin 1 → ℝ) → X)
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγD : ∀ q, γ q ∈ D.carrier) {x₀ x₁ : X}
    (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) : OrxLoc hf x₀ hs₀ ≃ OrxLoc hf x₁ hs₁ :=
  (D.toLoc hf x₀ (h₀ ▸ hγD _) hs₀).trans
    (((D.transport hX hf).transport (D.liftPath γ hγD) (D.isScSmoothMap_liftPath hγ hγD)
      (x₀ := ⟨x₀, h₀ ▸ hγD _⟩) (x₁ := ⟨x₁, h₁ ▸ hγD _⟩) (Subtype.ext h₀) (Subtype.ext h₁)
      (mem_smoothSet _ hs₀) (mem_smoothSet _ hs₁)).trans
      (D.toLoc hf x₁ (h₁ ▸ hγD _) hs₁).symm)

theorem transportLoc_apply (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγD : ∀ q, γ q ∈ D.carrier) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) (o : OrxLoc hf x₀ hs₀) :
    D.transportLoc hX hf γ hγ hγD h₀ h₁ hs₀ hs₁ o =
      (D.toLoc hf x₁ (h₁ ▸ hγD _) hs₁).symm
        ((D.transport hX hf).transport (D.liftPath γ hγD) (D.isScSmoothMap_liftPath hγ hγD)
          (x₀ := ⟨x₀, h₀ ▸ hγD _⟩) (x₁ := ⟨x₁, h₁ ▸ hγD _⟩) (Subtype.ext h₀) (Subtype.ext h₁)
          (mem_smoothSet _ hs₀) (mem_smoothSet _ hs₁) (D.toLoc hf x₀ (h₀ ▸ hγD _) hs₀ o)) :=
  rfl

/-- The identification with `Or^{f|W}` at the end point intertwines the propagation and the
transport of `f|W`. -/
theorem toLoc_transportLoc (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγD : ∀ q, γ q ∈ D.carrier) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) (o : OrxLoc hf x₀ hs₀) :
    D.toLoc hf x₁ (h₁ ▸ hγD _) hs₁ (D.transportLoc hX hf γ hγ hγD h₀ h₁ hs₀ hs₁ o) =
      (D.transport hX hf).transport (D.liftPath γ hγD) (D.isScSmoothMap_liftPath hγ hγD)
        (x₀ := ⟨x₀, h₀ ▸ hγD _⟩) (x₁ := ⟨x₁, h₁ ▸ hγD _⟩) (Subtype.ext h₀) (Subtype.ext h₁)
        (mem_smoothSet _ hs₀) (mem_smoothSet _ hs₁) (D.toLoc hf x₀ (h₀ ▸ hγD _) hs₀ o) := by
  rw [transportLoc_apply, Equiv.apply_symm_apply]

variable {D D'} in
/-- **The propagation along a path in a domain `W ⊆ W'` is the propagation in `W'`.** -/
theorem transportLoc_of_subset (h : D.carrier ⊆ D'.carrier) (hX : PX.IsTame)
    (hf : B.IsScFredholmSectionTame f) {γ : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγD : ∀ q, γ q ∈ D.carrier) {x₀ x₁ : X}
    (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) :
    D.transportLoc hX hf γ hγ hγD h₀ h₁ hs₀ hs₁ =
      D'.transportLoc hX hf γ hγ (fun q => h (hγD q)) h₀ h₁ hs₀ hs₁ := by
  have hx₀ : x₀ ∈ D.carrier := h₀ ▸ hγD _
  have hx₁ : x₁ ∈ D.carrier := h₁ ▸ hγD _
  refine Equiv.ext fun o => ?_
  have hc := DFunLike.congr_fun (compare_transport h hX hf (D.isScSmoothMap_liftPath hγ hγD)
    hx₀ hx₁ (Subtype.ext h₀) (Subtype.ext h₁) hs₀ hs₁) (D'.toLoc hf x₀ (h hx₀) hs₀ o)
  have e₀ := DFunLike.congr_fun (D.toLoc_compare D' hf x₀ hx₀ (h hx₀) hs₀) o
  have e₁ := DFunLike.congr_fun (D.toLoc_compare D' hf x₁ hx₁ (h hx₁) hs₁)
    (D'.transportLoc hX hf γ hγ (fun q => h (hγD q)) h₀ h₁ hs₀ hs₁ o)
  rw [Equiv.trans_apply] at hc e₀ e₁
  rw [D'.toLoc_transportLoc] at e₁
  rw [transportLoc_apply, Equiv.symm_apply_eq, ← e₁, ← e₀, hc]
  rfl

/-- **The propagation along a path does not depend on the domain**: for two domains `W`, `W'`
and an sc-smooth path with all values in `W ∩ W'`, the maps made in `W` and in `W'` agree. -/
theorem transportLoc_eq (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγD : ∀ q, γ q ∈ D.carrier) (hγD' : ∀ q, γ q ∈ D'.carrier) {x₀ x₁ : X}
    (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) :
    D.transportLoc hX hf γ hγ hγD h₀ h₁ hs₀ hs₁ =
      D'.transportLoc hX hf γ hγ hγD' h₀ h₁ hs₀ hs₁ :=
  (transportLoc_of_subset (D := D.inter D' ⟨γ (pt1 0), hγD _, hγD' _⟩) (D' := D)
    inter_subset_left hX hf hγ (fun q => ⟨hγD q, hγD' q⟩) h₀ h₁ hs₀ hs₁).symm.trans
    (transportLoc_of_subset (D := D.inter D' ⟨γ (pt1 0), hγD _, hγD' _⟩) (D' := D')
      inter_subset_right hX hf hγ (fun q => ⟨hγD q, hγD' q⟩) h₀ h₁ hs₀ hs₁)

/-- **The propagation along a path in a domain is the composite of the propagations along its
two halves.** -/
theorem transportLoc_halves (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγD : ∀ q, γ q ∈ D.carrier) {x₀ x₁ xm : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁)
    (hm : γ (pt1 (1 / 2)) = xm) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet)
    (hsm : xm ∈ PX.smoothSet) :
    D.transportLoc hX hf γ hγ hγD h₀ h₁ hs₀ hs₁ =
      (D.transportLoc hX hf (leftHalf γ) (isScSmoothMap_leftHalf hγ) (fun _ => hγD _)
        (leftHalf_zero.trans h₀) (leftHalf_one.trans hm) hs₀ hsm).trans
      (D.transportLoc hX hf (rightHalf γ) (isScSmoothMap_rightHalf hγ) (fun _ => hγD _)
        (rightHalf_zero.trans hm) (rightHalf_one.trans h₁) hsm hs₁) := by
  have hxm : xm ∈ D.carrier := hm ▸ hγD _
  exact conj_trans_of_eq (D.toLoc hf x₀ (h₀ ▸ hγD _) hs₀) (D.toLoc hf xm hxm hsm)
    (D.toLoc hf x₁ (h₁ ▸ hγD _) hs₁) ((D.transport hX hf).transport_halves
      (D.isScSmoothMap_liftPath hγ hγD) (x₀ := ⟨x₀, h₀ ▸ hγD _⟩) (x₁ := ⟨x₁, h₁ ▸ hγD _⟩)
      (xm := ⟨xm, hxm⟩) (Subtype.ext h₀) (Subtype.ext h₁) (Subtype.ext hm)
      (mem_smoothSet _ hs₀) (mem_smoothSet _ hs₁) (mem_smoothSet hxm hsm))

/-- **The propagation along a path in a domain is invariant under reparametrization** by a
`C^∞` map `θ : ℝ → ℝ` with `θ(0) = 0` and `θ(1) = 1`. -/
theorem transportLoc_reparam (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγD : ∀ q, γ q ∈ D.carrier) {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (h0 : θ 0 = 0)
    (h1 : θ 1 = 1) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    D.transportLoc hX hf (fun s => γ (pt1 (θ (s 0)))) (isScSmoothMap_reparam hγ hθ)
        (fun _ => hγD _) ((congrArg (fun t => γ (pt1 t)) h0).trans h₀)
        ((congrArg (fun t => γ (pt1 t)) h1).trans h₁) hs₀ hs₁ =
      D.transportLoc hX hf γ hγ hγD h₀ h₁ hs₀ hs₁ := by
  exact congrArg (fun T => (D.toLoc hf x₀ (h₀ ▸ hγD _) hs₀).trans
      (T.trans (D.toLoc hf x₁ (h₁ ▸ hγD _) hs₁).symm))
    ((D.transport hX hf).transport_reparam (D.isScSmoothMap_liftPath hγ hγD) hθ h0 h1
      (x₀ := ⟨x₀, h₀ ▸ hγD _⟩) (x₁ := ⟨x₁, h₁ ▸ hγD _⟩) (Subtype.ext h₀) (Subtype.ext h₁)
      (mem_smoothSet _ hs₀) (mem_smoothSet _ hs₁))

/-- The propagation along the reparametrization of a path by the smooth transition function is
the propagation along the path. -/
theorem transportLoc_smoothTransPath (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγD : ∀ q, γ q ∈ D.carrier) (hγD' : ∀ q, smoothTransPath_or γ q ∈ D.carrier) {x₀ x₁ : X}
    (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (h₀' : smoothTransPath_or γ (pt1 0) = x₀)
    (h₁' : smoothTransPath_or γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) :
    D.transportLoc hX hf (smoothTransPath_or γ) (isScSmoothMap_smoothTransPath_or hγ) hγD'
        h₀' h₁' hs₀ hs₁ =
      D.transportLoc hX hf γ hγ hγD h₀ h₁ hs₀ hs₁ :=
  D.transportLoc_reparam hX hf hγ hγD Real.smoothTransition.contDiff
    Real.smoothTransition.zero Real.smoothTransition.one h₀ h₁ hs₀ hs₁

/-- **In a good set of a domain the propagations compose**: for sc-smooth paths `γ` from `x₀`
to `x₂`, `γ₁` from `x₀` to `x₁` and `γ₂` from `x₁` to `x₂` with all values in `W` and with
`[0, 1]` carried into a good set `G` of `W`, the propagation along `γ` is the composite of
those along `γ₁` and `γ₂`. -/
theorem transportLoc_trans_of_good (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    {G : Set D.carrier} (hG : (D.transport hX hf).Good G) {γ γ₁ γ₂ : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγ₁ : (rnPolyfold 1).IsScSmoothMap PX γ₁)
    (hγ₂ : (rnPolyfold 1).IsScSmoothMap PX γ₂) (hγD : ∀ q, γ q ∈ D.carrier)
    (hγ₁D : ∀ q, γ₁ q ∈ D.carrier) (hγ₂D : ∀ q, γ₂ q ∈ D.carrier)
    (hγG : ∀ t ∈ Icc (0 : ℝ) 1, D.liftPath γ hγD (pt1 t) ∈ G)
    (hγ₁G : ∀ t ∈ Icc (0 : ℝ) 1, D.liftPath γ₁ hγ₁D (pt1 t) ∈ G)
    (hγ₂G : ∀ t ∈ Icc (0 : ℝ) 1, D.liftPath γ₂ hγ₂D (pt1 t) ∈ G)
    {x₀ x₁ x₂ : X} (h₀ : γ (pt1 0) = x₀) (h₂ : γ (pt1 1) = x₂) (h₁₀ : γ₁ (pt1 0) = x₀)
    (h₁₁ : γ₁ (pt1 1) = x₁) (h₂₀ : γ₂ (pt1 0) = x₁) (h₂₁ : γ₂ (pt1 1) = x₂)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) (hs₂ : x₂ ∈ PX.smoothSet) :
    D.transportLoc hX hf γ hγ hγD h₀ h₂ hs₀ hs₂ =
      (D.transportLoc hX hf γ₁ hγ₁ hγ₁D h₁₀ h₁₁ hs₀ hs₁).trans
        (D.transportLoc hX hf γ₂ hγ₂ hγ₂D h₂₀ h₂₁ hs₁ hs₂) := by
  have hx₀ : x₀ ∈ D.carrier := h₀ ▸ hγD _
  have hx₁ : x₁ ∈ D.carrier := h₁₁ ▸ hγ₁D _
  have hx₂ : x₂ ∈ D.carrier := h₂ ▸ hγD _
  have e₀ : (⟨γ (pt1 0), hγD _⟩ : D.carrier) = ⟨x₀, hx₀⟩ := Subtype.ext h₀
  have e₂ : (⟨γ (pt1 1), hγD _⟩ : D.carrier) = ⟨x₂, hx₂⟩ := Subtype.ext h₂
  have e₁₀ : (⟨γ₁ (pt1 0), hγ₁D _⟩ : D.carrier) = ⟨x₀, hx₀⟩ := Subtype.ext h₁₀
  have e₁₁ : (⟨γ₁ (pt1 1), hγ₁D _⟩ : D.carrier) = ⟨x₁, hx₁⟩ := Subtype.ext h₁₁
  have e₂₀ : (⟨γ₂ (pt1 0), hγ₂D _⟩ : D.carrier) = ⟨x₁, hx₁⟩ := Subtype.ext h₂₀
  have e₂₁ : (⟨γ₂ (pt1 1), hγ₂D _⟩ : D.carrier) = ⟨x₂, hx₂⟩ := Subtype.ext h₂₁
  have hw₀ := mem_smoothSet hx₀ hs₀
  have hw₁ := mem_smoothSet hx₁ hs₁
  have hw₂ := mem_smoothSet hx₂ hs₂
  have e : (D.transport hX hf).transport (D.liftPath γ hγD) (D.isScSmoothMap_liftPath hγ hγD)
      e₀ e₂ hw₀ hw₂ =
      ((D.transport hX hf).transport (D.liftPath γ₁ hγ₁D) (D.isScSmoothMap_liftPath hγ₁ hγ₁D)
        e₁₀ e₁₁ hw₀ hw₁).trans
      ((D.transport hX hf).transport (D.liftPath γ₂ hγ₂D) (D.isScSmoothMap_liftPath hγ₂ hγ₂D)
        e₂₀ e₂₁ hw₁ hw₂) := by
    exact (((D.transport hX hf).transport_eq_push hG (D.isScSmoothMap_liftPath hγ hγD) hγG
      e₀ e₂ hw₀ hw₂).trans ((D.transport hX hf).push_trans hG _ _ _ hγG hγ₁G hγ₂G e₀ e₂ e₁₀
        e₁₁ e₂₀ e₂₁ hw₀ hw₁ hw₂)).trans (congrArg₂ Equiv.trans
      ((D.transport hX hf).transport_eq_push hG (D.isScSmoothMap_liftPath hγ₁ hγ₁D) hγ₁G
        e₁₀ e₁₁ hw₀ hw₁).symm
      ((D.transport hX hf).transport_eq_push hG (D.isScSmoothMap_liftPath hγ₂ hγ₂D) hγ₂G
        e₂₀ e₂₁ hw₁ hw₂).symm)
  exact conj_trans_of_eq (D.toLoc hf x₀ hx₀ hs₀) (D.toLoc hf x₁ hx₁ hs₁)
    (D.toLoc hf x₂ hx₂ hs₂) e

end StrongBundle.Dom

/-! ### The local transport data -/

/-- **The local transport data of the local orientation sets `Or_x^f`** (Theorem 6.6.11 and the
proof of Theorem 6.6.13).  A *good* set is an open set `U` inside a domain `W` which, as a
subset of `W`, is a good set for `f|W`: it has the local propagation property in a chart of
`P|W`.  The push-forward along a path in `U` is the propagation `Dom.transportLoc` in `W`; it
does not depend on `W` (`Dom.transportLoc_eq`). -/
def orLocalTransportLoc (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f) :
    LocalTransport PX (fun x hs => OrxLoc hf x hs) where
  Good U := IsOpen U ∧
    ∃ D : B.Dom, U ⊆ D.carrier ∧ (D.transport hX hf).Good (Subtype.val ⁻¹' U)
  isOpen hU := hU.1
  exists_good x hx := by
    obtain ⟨G, hG, hxG⟩ := ((B.domAt x).transport hX hf).exists_good ⟨x, B.mem_domAt x⟩
      (StrongBundle.Dom.mem_smoothSet (B.mem_domAt x) hx)
    refine ⟨Subtype.val '' G, ⟨(B.domAt x).isOpen.isOpenMap_subtype_val G
      (((B.domAt x).transport hX hf).isOpen hG), B.domAt x, ?_, ?_⟩, ⟨x, B.mem_domAt x⟩, hxG,
      rfl⟩
    · rintro _ ⟨w, _, rfl⟩
      exact w.2
    · rw [preimage_image_eq _ Subtype.val_injective]
      exact hG
  nonempty _ hs₀ _ hs₁ :=
    let ⟨_, _, ha, ha'⟩ := exists_two_orxLoc hf hs₀
    let ⟨_, _, hb, hb'⟩ := exists_two_orxLoc hf hs₁
    nonempty_equiv_of_two ha ha' hb hb'
  push hU γ hγ hγU _ _ h₀ h₁ hs₀ hs₁ :=
    hU.2.choose.transportLoc hX hf (smoothTransPath_or γ) (isScSmoothMap_smoothTransPath_or hγ)
      (fun q => hU.2.choose_spec.1 (smoothTransPath_or_mem hγU q))
      ((congrArg (fun t => γ (pt1 t)) Real.smoothTransition.zero).trans h₀)
      ((congrArg (fun t => γ (pt1 t)) Real.smoothTransition.one).trans h₁) hs₀ hs₁
  push_trans hU _ _ _ hγ hγ₁ hγ₂ hγU hγ₁U hγ₂U _ _ _ h₀ h₂ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂ :=
    hU.2.choose.transportLoc_trans_of_good hX hf hU.2.choose_spec.2
      (isScSmoothMap_smoothTransPath_or hγ) (isScSmoothMap_smoothTransPath_or hγ₁)
      (isScSmoothMap_smoothTransPath_or hγ₂) _ _ _
      (fun _ _ => smoothTransPath_or_mem hγU _) (fun _ _ => smoothTransPath_or_mem hγ₁U _)
      (fun _ _ => smoothTransPath_or_mem hγ₂U _) _ _ _ _ _ _ hs₀ hs₁ hs₂
  push_compat hU hU' _ hγ hγU hγU' _ _ h₀ h₁ hs₀ hs₁ :=
    hU.2.choose.transportLoc_eq hU'.2.choose hX hf (isScSmoothMap_smoothTransPath_or hγ) _ _ _ _
      hs₀ hs₁

/-- **A good set and the propagation in its domain**: on an sc-smooth path with `[0, 1]` in a
good set `U`, the push-forward is the propagation of the reparametrized path in every domain
containing `U`. -/
theorem orLocalTransportLoc_push_eq (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    {U : Set X} (hU : (orLocalTransportLoc hX hf).Good U) (D : B.Dom)
    {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U)
    (hγD : ∀ q, smoothTransPath_or γ q ∈ D.carrier) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    (orLocalTransportLoc hX hf).push hU γ hγ hγU h₀ h₁ hs₀ hs₁ =
      D.transportLoc hX hf (smoothTransPath_or γ) (isScSmoothMap_smoothTransPath_or hγ) hγD
        ((congrArg (fun t => γ (pt1 t)) Real.smoothTransition.zero).trans h₀)
        ((congrArg (fun t => γ (pt1 t)) Real.smoothTransition.one).trans h₁) hs₀ hs₁ :=
  hU.2.choose.transportLoc_eq D hX hf (isScSmoothMap_smoothTransPath_or hγ) _ hγD _ _ hs₀ hs₁

/-- **The transport along a path in a domain is the transport of the restriction to the
domain** (property (∗) of Theorem 6.6.13 for all paths in a domain): for a domain `W` and an
sc-smooth path `γ` with all values in `W`, the transport of the sets `Or^f` along `γ` is the
propagation `Dom.transportLoc`, the transport of `f|W` along `γ` read through `Dom.toLoc`. -/
theorem orLocalTransportLoc_transport_eq (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    (D : B.Dom) {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγD : ∀ q, γ q ∈ D.carrier) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    (orLocalTransportLoc hX hf).transport γ hγ h₀ h₁ hs₀ hs₁ =
      D.transportLoc hX hf γ hγ hγD h₀ h₁ hs₀ hs₁ := by
  refine LocalTransport.scPath_induction (PX := PX) (fun γ => ∀ q, γ q ∈ D.carrier)
    (fun γ => ∀ (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγD : ∀ q, γ q ∈ D.carrier)
      {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
      (hs₁ : x₁ ∈ PX.smoothSet), (orLocalTransportLoc hX hf).transport γ hγ h₀ h₁ hs₀ hs₁ =
        D.transportLoc hX hf γ hγ hγD h₀ h₁ hs₀ hs₁)
    (fun γ _ hQ q => hQ _) (fun γ _ hQ q => hQ _) ?_ ?_ hγ hγD hγ hγD h₀ h₁ hs₀ hs₁
  · intro γ _ _ hl hr hγ hγD x₀ x₁ h₀ h₁ hs₀ hs₁
    have hsm := mem_smoothSet_of_isScSmoothMap hγ (pt1 (1 / 2))
    rw [(orLocalTransportLoc hX hf).transport_halves hγ h₀ h₁ rfl hs₀ hs₁ hsm,
      D.transportLoc_halves hX hf hγ hγD h₀ h₁ rfl hs₀ hs₁ hsm,
      hl (isScSmoothMap_leftHalf hγ) (fun _ => hγD _) (leftHalf_zero.trans h₀)
        (leftHalf_one.trans rfl) hs₀ hsm,
      hr (isScSmoothMap_rightHalf hγ) (fun _ => hγD _) (rightHalf_zero.trans rfl)
        (rightHalf_one.trans h₁) hsm hs₁]
  · intro γ hγ _ t _
    obtain ⟨U, hU, hxU⟩ := (orLocalTransportLoc hX hf).exists_good _
      (mem_smoothSet_of_isScSmoothMap hγ (pt1 t))
    refine ⟨U, hU.1, hxU, fun γ' _ _ hγ'U hγ' hγ'D x₀ x₁ h₀ h₁ hs₀ hs₁ => ?_⟩
    rw [(orLocalTransportLoc hX hf).transport_eq_push hU hγ' hγ'U h₀ h₁ hs₀ hs₁,
      orLocalTransportLoc_push_eq hX hf hU D hγ' hγ'U (fun _ => hγ'D _) h₀ h₁ hs₀ hs₁]
    exact D.transportLoc_smoothTransPath hX hf hγ' hγ'D _ h₀ h₁ _ _ hs₀ hs₁

end Polyfold
