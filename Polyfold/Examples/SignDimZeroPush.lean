import Polyfold.Examples.SignDimZeroLinear
import Polyfold.Chapter6.OrientationSpace
import Polyfold.Chapter15.OrientedLinearizations
import Polyfold.Chapter6.SolutionOrientation

/-!
# Positive orientations at an isomorphism, and their propagation

For an sc-Fredholm section `f` and a smooth point `x`, an orientation `o ∈ Or_x^f` and a member
`L` of `Lin(f, x)` which is an isomorphism, `det L = λ(0) ⊗ λ*(0)` is canonically `ℝ`, and
`o(L)` is one of its two rays.  We call `o` *positive at `L`* when it is the ray of the empty
wedge (Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory*, Springer 2021, §6.6,
pp. 268–275; §15.4, pp. 701–702).

## What is formalized (namespace `Polyfold`)

* `ChartPoint.IsPos p o L`: `o` is positive at the isomorphism `L`, read in the chart point `p`;
  `ChartPoint.IsPos.orTransfer`: the notion does not depend on the chart point.
* `IsPosOr hf hxs o S hS hx`: `o ∈ Or_x^f` is positive at `(f + S)'(x)`, for an sc⁺-section `S`
  with `(f + S)(x) = 0`; `isPosOr_iff_chart` (it can be read in every chart).
* **`IsStabKernels.orRay_eq_emptyRayAt_iff`**: for stabilized kernels with no stabilizing
  sections and rank `0`, the orientation read in `λ(Λ_q)` is the ray of the empty wedge iff the
  orientation is positive at `(f + S_q)'(y_q)`.
* **`IsStabKernels.isPos_push_iff`**: the push-forward along such a family preserves
  positivity.
* `SubspaceFamily.botFamily`, `isStabKernels_botFamily`: along an sc-smooth path `γ` and an
  sc⁺-section `S` of the pull-back bundle with `(f + S_t)(γ t) = 0` and `(f + S_t)'(γ t)` an
  isomorphism, the zero subspaces are stabilized kernels.
* **`isPosOr_iff_of_path_local`**: for a continuous orientation and a path in an open set with
  the local propagation property, positivity at `γ(0)` and at `γ(1)` are equivalent.
* **`isPosOr_iff_of_path`**: the same for every sc-smooth path (the path is cut into pieces
  inside sets with the local propagation property, Theorem 6.6.11).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Module Topology Function

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

namespace ChartPoint

variable {x : X} (p p' : ChartPoint B x) {hf : B.IsScFredholmSection f}

/-- The image in `E₀` of the kernel of an injective operator is zero. -/
theorem map_ker_eq_bot {L : ↥p.T →L[ℝ] ↥p.K} (hinj : Injective L) :
    (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = ⊥ := by
  have h : LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K) = ⊥ := LinearMap.ker_eq_bot.2 hinj
  rw [h, Submodule.map_bot]

/-- An operator whose kernel has zero image in `E₀` is injective. -/
theorem injective_of_map_ker_eq_bot {L : ↥p.T →L[ℝ] ↥p.K}
    (h : (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = ⊥) : Injective L := by
  refine (injective_iff_map_eq_zero L).2 fun v hv => ?_
  have hm : (v : p.c.φ.model.E 0) ∈ (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) := ⟨v, hv, rfl⟩
  rw [h] at hm
  exact Subtype.ext hm

/-- **`o ∈ Or_x^f` is positive at the isomorphism `L ∈ Lin(f, x)`**, read in the chart point
`p`: the orientation of `ker L = 0` induced by `o` (`orKer`) is the ray of the empty wedge. -/
def IsPos (o : p.Or f hf) (L : ↥p.T →L[ℝ] ↥p.K) : Prop :=
  ∃ (hL : L ∈ p.linSet f) (hLs : Surjective L)
    (hN : (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = ⊥),
    p.orKer o hL hLs hN = emptyRay (⊥ : Submodule ℝ (p.c.φ.model.E 0)) (finrank_bot ℝ _)

variable {p}

theorem IsPos.bijective {o : p.Or f hf} {L : ↥p.T →L[ℝ] ↥p.K} (h : p.IsPos o L) :
    Bijective L :=
  let ⟨_, hLs, hN, _⟩ := h
  ⟨p.injective_of_map_ker_eq_bot hN, hLs⟩

theorem isPos_iff {o : p.Or f hf} {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f)
    (hLs : Surjective L)
    (hN : (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = ⊥) :
    p.IsPos o L ↔
      p.orKer o hL hLs hN = emptyRay (⊥ : Submodule ℝ (p.c.φ.model.E 0)) (finrank_bot ℝ _) :=
  ⟨fun ⟨_, _, _, h⟩ => h, fun h => ⟨hL, hLs, hN, h⟩⟩

/-- **For an isomorphism `L ∈ Lin(f, x)`, exactly one of two different orientations is
positive.** -/
theorem isPos_or_isPos {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) (hLb : Bijective L)
    {o₁ o₂ : p.Or f hf} (hall : ∀ o : p.Or f hf, o = o₁ ∨ o = o₂) :
    p.IsPos o₁ L ∨ p.IsPos o₂ L := by
  obtain ⟨o, ho⟩ := (p.orKerEquiv hf hL hLb.2 (p.map_ker_eq_bot hLb.1)).surjective
    (emptyRay (⊥ : Submodule ℝ (p.c.φ.model.E 0)) (finrank_bot ℝ _))
  rw [orKerEquiv_apply] at ho
  rcases hall o with rfl | rfl
  · exact Or.inl ⟨hL, hLb.2, _, ho⟩
  · exact Or.inr ⟨hL, hLb.2, _, ho⟩

/-- **Positivity does not depend on the chart point**: if `L'` in `p'` is conjugate to `L` in
`p` by the identifications of the tangent spaces and of the fibres, `o` is positive at `L` iff
the transferred orientation is positive at `L'` (`ChartPoint.orTransfer_surjRay`). -/
theorem IsPos.orTransfer (hxs : x ∈ PX.smoothSet) {o : p.Or f hf} {L : ↥p.T →L[ℝ] ↥p.K}
    (h : p.IsPos o L) {L' : ↥p'.T →L[ℝ] ↥p'.K} (hL' : L' ∈ p'.linSet f)
    (hconj : ∀ v, L' (p.transferT p' v) = p.transferK p' (L v)) :
    p'.IsPos (p.orTransfer p' hf hxs o) L' := by
  obtain ⟨hL, hLs, hN, he⟩ := h
  have hinj : Injective L := p.injective_of_map_ker_eq_bot hN
  have hL's : Surjective L' := fun y => by
    obtain ⟨v, hv⟩ := hLs ((p.transferK p').symm y)
    exact ⟨p.transferT p' v, by rw [hconj, hv, ContinuousLinearEquiv.apply_symm_apply]⟩
  have hL'i : Injective L' := by
    refine (injective_iff_map_eq_zero L').2 fun w hw => ?_
    obtain ⟨v, rfl⟩ := (p.transferT p').surjective w
    rw [hconj] at hw
    have h1 : L v = 0 := (p.transferK p').map_eq_zero_iff.1 hw
    rw [(injective_iff_map_eq_zero L).1 hinj v h1, map_zero]
  have hN' := p'.map_ker_eq_bot hL'i
  refine ⟨hL', hL's, hN', ?_⟩
  have key : p'.orKer (p.orTransfer p' hf hxs o) hL' hL's hN' =
      Module.Ray.map (maxPowEquiv (conjKerEquivOfMap (p.transferT p') (p.transferK p') hconj
          p.T.subtypeL Subtype.val_injective hN p'.T.subtypeL Subtype.val_injective hN'))
        (p.orKer o hL hLs hN) :=
    p.orTransfer_surjRay p' hf hxs o hL hLs hL' hL's hconj hN hN'
  rw [key, he]
  exact ray_map_maxPowEquiv_emptyRay _ _ _

/-- **The linearizations `(f + S)'(x)` in two chart points are conjugate.** -/
theorem stabT_transferT (hf : B.IsScFredholmSection f) {S : X → Y} (hS : B.IsScPlusSection S)
    (hx : IsZeroAt P (sectionAdd P f S) x) (v : ↥p.T) :
    p'.stabT hf hS hx (p.transferT p' v) = p.transferK p' (p.stabT hf hS hx v) :=
  Subtype.ext (p.scDeriv_principal_baseDeriv p' (hf.isScSmooth.sectionAdd hS) hx v)

/-- **Bijectivity of `(f + S)'(x)` does not depend on the chart point.** -/
theorem bijective_stabT_of_bijective (hf : B.IsScFredholmSection f) {S : X → Y}
    (hS : B.IsScPlusSection S) (hx : IsZeroAt P (sectionAdd P f S) x)
    (h : Bijective (p.stabT hf hS hx)) : Bijective (p'.stabT hf hS hx) := by
  have e : ⇑(p'.stabT hf hS hx) =
      ⇑(p.transferK p') ∘ ⇑(p.stabT hf hS hx) ∘ ⇑(p.transferT p').symm := by
    funext w
    have := stabT_transferT p' hf hS hx ((p.transferT p').symm w)
    rw [ContinuousLinearEquiv.apply_symm_apply] at this
    exact this
  rw [e]
  exact (p.transferK p').bijective.comp (h.comp (p.transferT p').symm.bijective)

end ChartPoint

/-! ### The chart-free notion -/

/-- **`o ∈ Or_x^f` is positive at the isomorphism `(f + S)'(x)`**, for an sc⁺-section `S` with
`(f + S)(x) = 0`: read in the chosen chart at `x`. -/
def IsPosOr (hf : B.IsScFredholmSection f) {x : X} (hxs : x ∈ PX.smoothSet)
    (o : Orx f hf x hxs) (S : X → Y) (hS : B.IsScPlusSection S)
    (hx : IsZeroAt P (sectionAdd P f S) x) : Prop :=
  (chartPtOf (orChart B x) (isChart_orChart x) (mem_orChart x) hxs).IsPos o
    ((chartPtOf (orChart B x) (isChart_orChart x) (mem_orChart x) hxs).stabT hf hS hx)

/-- **Positivity can be read in every chart.** -/
theorem isPosOr_iff_chart (hf : B.IsScFredholmSection f) {x : X} (hxs : x ∈ PX.smoothSet)
    (o : Orx f hf x hxs) {S : X → Y} (hS : B.IsScPlusSection S)
    (hx : IsZeroAt P (sectionAdd P f S) x) (c : StrongBundleChart PX P) (hc : B.IsChart c)
    (hxc : x ∈ c.φ.source) :
    IsPosOr hf hxs o S hS hx ↔
      (chartPtOf c hc hxc hxs).IsPos (toChartOr hf hxs c hc hxc o)
        ((chartPtOf c hc hxc hxs).stabT hf hS hx) := by
  set p₀ := chartPtOf (orChart B x) (isChart_orChart x) (mem_orChart x) hxs
  set p := chartPtOf c hc hxc hxs
  constructor
  · intro h
    exact ChartPoint.IsPos.orTransfer p hxs h (p.stabT_mem_linSet hf hS hx hxs)
      (ChartPoint.stabT_transferT p hf hS hx)
  · intro h
    have h' := ChartPoint.IsPos.orTransfer p₀ hxs h (p₀.stabT_mem_linSet hf hS hx hxs)
      (ChartPoint.stabT_transferT p₀ hf hS hx)
    have e : p.orTransfer p₀ hf hxs (toChartOr hf hxs c hc hxc o) = o :=
      (p₀.orTransfer p hf hxs).symm_apply_apply o
    rw [e] at h'
    exact h'

/-- Positivity depends only on the section `S`. -/
theorem isPosOr_congr (hf : B.IsScFredholmSection f) {x : X} (hxs : x ∈ PX.smoothSet)
    (o : Orx f hf x hxs) {S S' : X → Y} (h : S = S') (hS : B.IsScPlusSection S)
    (hS' : B.IsScPlusSection S') (hx : IsZeroAt P (sectionAdd P f S) x)
    (hx' : IsZeroAt P (sectionAdd P f S') x) :
    IsPosOr hf hxs o S hS hx ↔ IsPosOr hf hxs o S' hS' hx' := by
  subst h
  rfl

/-- Positivity at equal points: the point may be replaced along an equality. -/
theorem isPosOr_congr_pt (hf : B.IsScFredholmSection f)
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy) {x x' : X} (h : x = x')
    (hxs : x ∈ PX.smoothSet) (hxs' : x' ∈ PX.smoothSet) {S S' : X → Y} (hSS : S = S')
    (hS : B.IsScPlusSection S) (hS' : B.IsScPlusSection S')
    (hx : IsZeroAt P (sectionAdd P f S) x) (hx' : IsZeroAt P (sectionAdd P f S') x') :
    IsPosOr hf hxs (o x hxs) S hS hx ↔ IsPosOr hf hxs' (o x' hxs') S' hS' hx' := by
  subst h
  subst hSS
  rfl

/-! ### Stabilized kernels of rank `0` -/

namespace IsStabKernels

variable {Q : Type*} [TopologicalSpace Q] [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q]
  {c : StrongBundleChart PX P} {hc : B.IsChart c} {y : Q → X} {hy : ∀ q, y q ∈ c.φ.source}
  {S : Q → X → Y} {s : Fin 0 → Q → X → Y}
  {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin 0 → ℝ))}

/-- **The orientation read in `λ(Λ_q)` is the ray of the empty wedge iff it is positive**: for
stabilized kernels with no stabilizing sections and of rank `0`, `(f + S_q)'(y_q)` is an
isomorphism, and `orRay_q o` is the ray of the empty wedge of `Λ_q = 0` iff `o` is positive at
`(f + S_q)'(y_q)` (`stabRayEquiv_eq_surjRay`; the sign `α(T) = 1` for `T` onto). -/
theorem orRay_eq_emptyRayAt_iff (hΛ : IsStabKernels f c hc y hy S s Λ) (hn : Λ.n = 0)
    (hf : B.IsScFredholmSection f) (q : Q) {x : X} (hq : y q = x) (hx : x ∈ PX.smoothSet)
    (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ x)
    (o : (chartPt c hc (hq ▸ hy q) z hz).Or f hf) :
    hΛ.orRay hf q hq hx z hz o = Λ.emptyRayAt hn q ↔
      (chartPt c hc (hq ▸ hy q) z hz).IsPos o
        ((chartPt c hc (hq ▸ hy q) z hz).stabT hf (hΛ.isScPlusSection q)
          (hq ▸ hΛ.zero q)) := by
  have h0' : IsZeroAt P (sectionAdd P f (S q)) x := hq ▸ hΛ.zero q
  have hTm := (chartPt c hc (hq ▸ hy q) z hz).stabT_mem_linSet hf (hΛ.isScPlusSection q) h0' hx
  have hsq := hΛ.spec q hq (hq ▸ hy q) z hz
    ((chartPt c hc (hq ▸ hy q) z hz).stabT hf (hΛ.isScPlusSection q) h0') (fun _ => rfl)
    ((chartPt c hc (hq ▸ hy q) z hz).stabPhi (fun i => s i q) (fun i => hΛ.isSection i q))
    (fun μ => ChartPoint.coe_stabPhi _ _ _ μ)
  have hTs : Surjective ((chartPt c hc (hq ▸ hy q) z hz).stabT hf (hΛ.isScPlusSection q) h0') :=
    fun w => by
      obtain ⟨⟨v, μ⟩, h⟩ := hsq.1 w
      refine ⟨v, ?_⟩
      rw [ContinuousLinearMap.coprod_apply, Subsingleton.elim μ 0, map_zero, add_zero] at h
      exact h
  have hLq : Λ.L q = ⊥ := Submodule.finrank_eq_zero.1 ((Λ.finrank_eq q).trans hn)
  have hTi : Injective ((chartPt c hc (hq ▸ hy q) z hz).stabT hf (hΛ.isScPlusSection q) h0') := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    have hm : (((v : c.φ.model.E 0), (0 : Fin 0 → ℝ)) : c.φ.model.E 0 × (Fin 0 → ℝ)) ∈ Λ.L q := by
      rw [hsq.2]
      refine ⟨(v, 0), ?_, rfl⟩
      change (chartPt c hc (hq ▸ hy q) z hz).stabT hf (hΛ.isScPlusSection q) h0' v +
        (chartPt c hc (hq ▸ hy q) z hz).stabPhi (fun i => s i q) (fun i => hΛ.isSection i q) 0 = 0
      rw [hv, map_zero, add_zero]
    rw [hLq, Submodule.mem_bot] at hm
    exact Subtype.ext (congrArg Prod.fst hm)
  have hN := (chartPt c hc (hq ▸ hy q) z hz).map_ker_eq_bot hTi
  have : Subsingleton ↥(Λ.L q) := by rw [hLq]; infer_instance
  let e : (⊥ : Submodule ℝ (c.φ.model.E 0)) ≃ₗ[ℝ] Λ.L q := 0
  have he : ∀ v, (e v : c.φ.model.E 0 × (Fin 0 → ℝ)) = ((v : c.φ.model.E 0), 0) := fun v => by
    have h1 : (v : c.φ.model.E 0) = 0 := (Submodule.mem_bot ℝ).1 v.2
    have h2 : (e v : c.φ.model.E 0 × (Fin 0 → ℝ)) = 0 := by
      have h3 : (e v : c.φ.model.E 0 × (Fin 0 → ℝ)) ∈
          (⊥ : Submodule ℝ (c.φ.model.E 0 × (Fin 0 → ℝ))) := hLq ▸ (e v).2
      exact (Submodule.mem_bot ℝ).1 h3
    rw [h1, h2]
    rfl
  have h1 : hΛ.orRay hf q hq hx z hz =
      ((ChartPoint.orEquivRay _ hf hTm).trans (MulAction.toPerm (stabSign
        ((chartPt c hc (hq ▸ hy q) z hz).stabT hf (hΛ.isScPlusSection q) h0')))).trans
      (stabRayEquiv (ChartPoint.isFredholm_of_mem_linSet _ hf _ hTm) hsq.1
        (kerEquivMap (chartPt c hc (hq ▸ hy q) z hz).T.subtypeL Subtype.val_injective
          hsq.2)) := rfl
  have h2 := stabRayEquiv_eq_surjRay (ChartPoint.isFredholm_of_mem_linSet _ hf _ hTm) hTs hsq.1
    (chartPt c hc (hq ▸ hy q) z hz).T.subtypeL Subtype.val_injective hsq.2 hN e he
    ((chartPt c hc (hq ▸ hy q) z hz).orEquivRay hf hTm o)
  have h3 : hΛ.orRay hf q hq hx z hz o = Module.Ray.map (maxPowEquiv e)
      ((chartPt c hc (hq ▸ hy q) z hz).orKer o hTm hTs hN) := by
    refine (DFunLike.congr_fun h1 o).trans ?_
    refine (Equiv.trans_apply _ _ o).trans ?_
    refine (congrArg _ (Equiv.trans_apply _ _ o)).trans ?_
    refine (congrArg _ (MulAction.toPerm_apply _ _)).trans ?_
    exact h2
  have h4 : Λ.emptyRayAt hn q = Module.Ray.map (maxPowEquiv e)
      (emptyRay (⊥ : Submodule ℝ (c.φ.model.E 0)) (finrank_bot ℝ _)) :=
    (ray_map_maxPowEquiv_emptyRay e _ _).symm
  rw [ChartPoint.isPos_iff hTm hTs hN, h3, h4]
  exact (Module.Ray.map (maxPowEquiv e)).apply_eq_iff_eq

/-- **The push-forward along stabilized kernels of rank `0` preserves positivity**
(`push_eq_orRay`, `SubspaceFamily.cont_emptyRay`). -/
theorem isPos_push_iff (hΛ : IsStabKernels f c hc y hy S s Λ) (hn : Λ.n = 0)
    (hf : B.IsScFredholmSection f) (a b : Q) {x₀ x₁ : X} (ha : y a = x₀) (hb : y b = x₁)
    (hx₀ : x₀ ∈ PX.smoothSet) (hx₁ : x₁ ∈ PX.smoothSet) (z₀ : c.φ.model.E 1)
    (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x₀) (z₁ : c.φ.model.E 1)
    (hz₁ : c.φ.model.E.toBase 1 z₁ = c.φ x₁) (o : (chartPt c hc (ha ▸ hy a) z₀ hz₀).Or f hf) :
    (chartPt c hc (hb ▸ hy b) z₁ hz₁).IsPos (hΛ.push hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁ o)
        ((chartPt c hc (hb ▸ hy b) z₁ hz₁).stabT hf (hΛ.isScPlusSection b) (hb ▸ hΛ.zero b)) ↔
      (chartPt c hc (ha ▸ hy a) z₀ hz₀).IsPos o
        ((chartPt c hc (ha ▸ hy a) z₀ hz₀).stabT hf (hΛ.isScPlusSection a)
          (ha ▸ hΛ.zero a)) := by
  rw [← hΛ.orRay_eq_emptyRayAt_iff hn hf b hb hx₁ z₁ hz₁,
    ← hΛ.orRay_eq_emptyRayAt_iff hn hf a ha hx₀ z₀ hz₀, hΛ.push_eq_orRay]
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply, SubspaceFamily.contEquiv_apply]
  rw [← Λ.cont_emptyRay hn a b]
  exact (Λ.contEquiv a b).apply_eq_iff_eq

end IsStabKernels

/-! ### The zero subspaces along a path of isomorphisms -/

/-- The family of the zero subspaces, of rank `0`. -/
def SubspaceFamily.botFamily (Q : Type*) [TopologicalSpace Q] (W : Type*) [NormedAddCommGroup W]
    [NormedSpace ℝ W] : SubspaceFamily Q W where
  L _ := ⊥
  n := 0
  finiteDimensional _ := inferInstance
  finrank_eq _ := finrank_bot ℝ W
  exists_frame _ := ⟨univ, isOpen_univ, mem_univ _, Fin.elim0, fun i => i.elim0,
    fun _ _ => ⟨fun i => i.elim0, linearIndependent_empty_type⟩⟩

section Push

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **The zero subspaces are stabilized kernels along a path of isomorphisms**: for an
sc-smooth path `γ` in the domain of `c` and an sc⁺-section `S` of the pull-back bundle over
`ℝ × X` with `(f + S_q)(γ_q) = 0` and `(f + S_q)'(γ_q)` an isomorphism for `q ∈ [0, 1]`, the
slices `S_q` with no stabilizing sections have the stabilized kernels `Λ_q = 0`. -/
theorem isStabKernels_botFamily (hf : B.IsScFredholmSection f) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγc : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    (hz : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, IsZeroAt P (sectionAdd P f (pullbackSlice S q)) (γ q))
    (hbij : ∀ (q : Fin 1 → ℝ) (hq : q ∈ Icc (0 : Fin 1 → ℝ) 1) (z : c.φ.model.E 1)
      (hzq : c.φ.model.E.toBase 1 z = c.φ (γ q)),
      Bijective ((chartPt c hc (hγc q hq) z hzq).stabT hf (hS.pullbackSlice q) (hz q hq))) :
    IsStabKernels f c hc (fun q : Icc (0 : Fin 1 → ℝ) 1 => γ q) (fun q => hγc q q.2)
      (fun q => pullbackSlice S q)
      (fun (i : Fin 0) q =>
        pullbackSlice (Fin.elim0 i : (Fin 1 → ℝ) × X → pullbackSpace P Prod.snd) q)
      (SubspaceFamily.botFamily _ _) where
  isScPlusSection q := hS.pullbackSlice q
  zero q := hz q q.2
  isSection i _ := i.elim0
  exists_lift q := exists_lift_of_smooth c (hγc q q.2) (mem_smoothSet_of_isScSmoothMap hγs q)
  spec q x hq hxc z' hz' T hT φ hφ := by
    subst hq
    have hTe : T = (chartPt c hc hxc z' hz').stabT hf (hS.pullbackSlice q) (hz q q.2) :=
      ContinuousLinearMap.ext fun v => Subtype.ext (hT v)
    have hb := hbij q q.2 z' hz'
    rw [← hTe] at hb
    refine ⟨fun w => ?_, ?_⟩
    · obtain ⟨v, hv⟩ := hb.2 w
      exact ⟨(v, 0), by rw [ContinuousLinearMap.coprod_apply, map_zero, add_zero, hv]⟩
    · change (⊥ : Submodule ℝ (c.φ.model.E 0 × (Fin 0 → ℝ))) = _
      refine (eq_bot_iff.2 ?_).symm
      rintro _ ⟨⟨u, μ⟩, hker, rfl⟩
      have h1 : T u + φ μ = 0 := hker
      rw [Subsingleton.elim μ 0, map_zero, add_zero] at h1
      have hu : u = 0 := hb.1 (h1.trans (map_zero T).symm)
      subst hu
      rw [Submodule.mem_bot]
      exact Prod.ext rfl (Subsingleton.elim _ _)

variable [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

/-- **Positivity is carried along a path of isomorphisms, locally**: let `o` be a continuous
orientation over `U'`, `γ` an sc-smooth path with `γ([0, 1])` in `U'` and in an open set `U`
with the local propagation property in a chart (Theorem 6.6.11), and `S` an sc⁺-section of the
pull-back bundle over `ℝ × X` with `(f + S_q)(γ_q) = 0` near `[0, 1]` and `(f + S_q)'(γ_q)` an
isomorphism for `q ∈ [0, 1]`.  Then `o` is positive at `(f + S_0)'(γ_0)` iff it is positive at
`(f + S_1)'(γ_1)`. -/
theorem isPosOr_iff_of_path_local (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hft : B.IsScFredholmSectionTame f) (hsec : B.HasScPlusSectionsThrough)
    {c : StrongBundleChart PX P} {hc : B.IsChart c} {U : Set X}
    (hU : HasLocalPropagation f hft.toIsScFredholmSection c hc U) (hUo : IsOpen U)
    {U' : Set X} {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hft.toIsScFredholmSection y hy}
    (ho : IsContOrOn (orLocalTransport hX hbump hft hsec) U' o)
    {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγU : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U)
    (hγU' : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U')
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    (hz : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin 1 → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hft.isScSmooth.1) S) (q, γ q))
    (hbij : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, ∀ (p : ChartPoint B (γ q))
      (h0 : IsZeroAt P (sectionAdd P f (pullbackSlice S q)) (γ q)),
      Bijective (p.stabT hft.toIsScFredholmSection (hS.pullbackSlice q) h0))
    (hs₀ : γ (pt1 0) ∈ PX.smoothSet) (hs₁ : γ (pt1 1) ∈ PX.smoothSet)
    (h0₀ : IsZeroAt P (sectionAdd P f (pullbackSlice S (pt1 0))) (γ (pt1 0)))
    (h0₁ : IsZeroAt P (sectionAdd P f (pullbackSlice S (pt1 1))) (γ (pt1 1))) :
    IsPosOr hft.toIsScFredholmSection hs₀ (o _ hs₀) (pullbackSlice S (pt1 0))
        (hS.pullbackSlice _) h0₀ ↔
      IsPosOr hft.toIsScFredholmSection hs₁ (o _ hs₁) (pullbackSlice S (pt1 1))
        (hS.pullbackSlice _) h0₁ := by
  have hf := hft.toIsScFredholmSection
  have hzq : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1,
      IsZeroAt P (sectionAdd P f (pullbackSlice S q)) (γ q) := fun q hq => by
    have h := (isZeroAt_pullback_iff_pullbackSlice
      ((isSection_pullbackLift _).sectionAdd hS.1) q (γ q)).1 (hz.self_of_nhdsSet q hq)
    rwa [pullbackSlice_sectionAdd_paramLift hft.isScSmooth.1 hS.1] at h
  have hγc : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source := fun q hq => hU.subset (hγU q hq)
  have hΛ := isStabKernels_botFamily hft.toIsScFredholmSection hc hγs hγc hS hzq
    (fun q hq z hzq' => hbij q hq _ _)
  have hx₀ : γ (pt1 0) ∈ c.φ.source := hγc _ (pt1_mem_Icc (left_mem_Icc.2 zero_le_one))
  have hx₁ : γ (pt1 1) ∈ c.φ.source := hγc _ (pt1_mem_Icc (right_mem_Icc.2 zero_le_one))
  have hpush : IsPush f hft.toIsScFredholmSection c hc γ hγc rfl rfl hx₀ hx₁ hs₀ hs₁
      (hΛ.push hft.toIsScFredholmSection iccZero iccOne rfl rfl hs₀ hs₁
        (exists_lift_of_smooth c hx₀ hs₀).choose (exists_lift_of_smooth c hx₀ hs₀).choose_spec
        (exists_lift_of_smooth c hx₁ hs₁).choose (exists_lift_of_smooth c hx₁ hs₁).choose_spec) :=
    ⟨S, hS, hz, 0, Fin.elim0, fun i => i.elim0, _, hΛ, rfl⟩
  have htr := orLocalTransport_transport_eq hX hbump hft hsec hU hUo hγs hγU rfl rfl hs₀ hs₁
    hx₀ hx₁ hpush
  have hoe := ho.2 γ hγs hγU' rfl rfl hs₀ hs₁
  rw [htr] at hoe
  have h2 := equiv_trans_trans_symm_apply hoe
  rw [isPosOr_iff_chart hft.toIsScFredholmSection hs₀ _ _ h0₀ c hc hx₀,
    isPosOr_iff_chart hft.toIsScFredholmSection hs₁ _ _ h0₁ c hc hx₁, ← h2]
  exact (hΛ.isPos_push_iff rfl hft.toIsScFredholmSection iccZero iccOne rfl rfl hs₀ hs₁
    _ _ _ _ _).symm

open scoped ContDiff in
/-- **Positivity is carried along a path of isomorphisms** (2021 §6.6, Theorems 6.6.11 and
6.6.13): let `o` be a continuous orientation over `U'`, `γ` an sc-smooth path with
`γ([0, 1]) ⊆ U'`, and `S` an sc⁺-section of the pull-back bundle over `ℝ × X` with
`(f + S_q)(γ_q) = 0` near `[0, 1]` and `(f + S_q)'(γ_q)` an isomorphism for `q ∈ [0, 1]`.  Then
`o` is positive at `(f + S_0)'(γ_0)` iff it is positive at `(f + S_1)'(γ_1)`.  *Proof*:
positivity at `(f + S_t)'(γ_t)` is locally constant in `t ∈ [0, 1]`, by
`isPosOr_iff_of_path_local` applied to the reparametrized pieces of `γ` inside open sets with
the local propagation property. -/
theorem isPosOr_iff_of_path (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hft : B.IsScFredholmSectionTame f) (hsec : B.HasScPlusSectionsThrough)
    {U' : Set X} {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hft.toIsScFredholmSection y hy}
    (ho : IsContOrOn (orLocalTransport hX hbump hft hsec) U' o)
    {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγU' : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U')
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    (hz : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin 1 → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hft.isScSmooth.1) S) (q, γ q))
    (hbij : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, ∀ (p : ChartPoint B (γ q))
      (h0 : IsZeroAt P (sectionAdd P f (pullbackSlice S q)) (γ q)),
      Bijective (p.stabT hft.toIsScFredholmSection (hS.pullbackSlice q) h0))
    (hs₀ : γ (pt1 0) ∈ PX.smoothSet) (hs₁ : γ (pt1 1) ∈ PX.smoothSet)
    (h0₀ : IsZeroAt P (sectionAdd P f (pullbackSlice S (pt1 0))) (γ (pt1 0)))
    (h0₁ : IsZeroAt P (sectionAdd P f (pullbackSlice S (pt1 1))) (γ (pt1 1))) :
    IsPosOr hft.toIsScFredholmSection hs₀ (o _ hs₀) (pullbackSlice S (pt1 0))
        (hS.pullbackSlice _) h0₀ ↔
      IsPosOr hft.toIsScFredholmSection hs₁ (o _ hs₁) (pullbackSlice S (pt1 1))
        (hS.pullbackSlice _) h0₁ := by
  have hsm : ∀ q, γ q ∈ PX.smoothSet := fun q => mem_smoothSet_of_isScSmoothMap hγs q
  have hzq : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1,
      IsZeroAt P (sectionAdd P f (pullbackSlice S q)) (γ q) := fun q hq => by
    have h := (isZeroAt_pullback_iff_pullbackSlice
      ((isSection_pullbackLift _).sectionAdd hS.1) q (γ q)).1 (hz.self_of_nhdsSet q hq)
    rwa [pullbackSlice_sectionAdd_paramLift hft.isScSmooth.1 hS.1] at h
  -- positivity at the parameter `t`
  let Pt : ℝ → Prop := fun t => ∀ (hs : γ (pt1 t) ∈ PX.smoothSet)
    (h0 : IsZeroAt P (sectionAdd P f (pullbackSlice S (pt1 t))) (γ (pt1 t))),
    IsPosOr hft.toIsScFredholmSection hs (o _ hs) (pullbackSlice S (pt1 t))
      (hS.pullbackSlice _) h0
  have hP : ∀ t (ht : t ∈ Icc (0 : ℝ) 1), Pt t ↔
      IsPosOr hft.toIsScFredholmSection (hsm (pt1 t)) (o _ (hsm (pt1 t)))
        (pullbackSlice S (pt1 t)) (hS.pullbackSlice _) (hzq _ (pt1_mem_Icc ht)) :=
    fun t ht => ⟨fun h => h _ _, fun h _ _ => h⟩
  have hpt : Continuous pt1 := continuous_pi fun _ => continuous_id
  have hγc : Continuous γ := continuousOn_univ.1 hγs.continuousOn
  have key : ∀ t₀ ∈ Icc (0 : ℝ) 1, ∃ ε > 0, ∀ t ∈ Icc (0 : ℝ) 1, |t - t₀| < ε →
      (Pt t₀ ↔ Pt t) := by
    intro t₀ ht₀
    obtain ⟨c, hc, U, hUo, hxU, hU⟩ := theorem_6_6_11 hX hbump hft (hsm (pt1 t₀))
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hUo.preimage (hγc.comp hpt)) t₀ hxU
    refine ⟨ε, hε, fun t ht hd => ?_⟩
    set A : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ) := (t - t₀) • ContinuousLinearMap.id ℝ _ with hA
    have hgpt : ∀ q : Fin 1 → ℝ, A q + pt1 t₀ = pt1 (t₀ + q 0 * (t - t₀)) := fun q =>
      funext fun i => by
        rw [Subsingleton.elim i 0]
        simp [hA, pt1]
        ring
    have hrange : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1,
        t₀ + q 0 * (t - t₀) ∈ Icc (0 : ℝ) 1 ∧ |t₀ + q 0 * (t - t₀) - t₀| < ε := by
      intro q hq
      have h0 : (0 : ℝ) ≤ q 0 := hq.1 0
      have h1 : q 0 ≤ 1 := hq.2 0
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · nlinarith [mul_nonneg (sub_nonneg.2 h1) ht₀.1, mul_nonneg h0 ht.1]
      · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 ht₀.2),
          mul_nonneg h0 (sub_nonneg.2 ht.2)]
      · have e : t₀ + q 0 * (t - t₀) - t₀ = q 0 * (t - t₀) := by ring
        rw [e, abs_mul, abs_of_nonneg h0]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg _) h1) hd
    have hg : MapsTo (fun q : Fin 1 → ℝ => A q + pt1 t₀) (Icc 0 1) (Icc 0 1) := fun q hq => by
      change A q + pt1 t₀ ∈ Icc (0 : Fin 1 → ℝ) 1
      rw [hgpt]
      exact pt1_mem_Icc (hrange q hq).1
    have hgc : Continuous fun q : Fin 1 → ℝ => A q + pt1 t₀ :=
      A.continuous.add continuous_const
    have hgs : (rnPolyfold 1).IsScSmoothMap (rnPolyfold 1) fun q : Fin 1 → ℝ => A q + pt1 t₀ :=
      isScSmoothMap_rn_of_contDiff (A.contDiff.add contDiff_const)
    have hδs : (rnPolyfold 1).IsScSmoothMap PX fun q : Fin 1 → ℝ => γ (A q + pt1 t₀) :=
      hγs.comp hgs
    have hδU : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ (A q + pt1 t₀) ∈ U := fun q hq => by
      rw [hgpt]
      exact hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        exact (hrange q hq).2)
    have hδU' : ∀ s ∈ Icc (0 : ℝ) 1, γ (A (pt1 s) + pt1 t₀) ∈ U' := fun s hs => by
      rw [hgpt]
      exact hγU' _ (hrange _ (pt1_mem_Icc hs)).1
    have hS' := hS.reparam A (pt1 t₀)
    have hz' : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin 1 → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hft.isScSmooth.1)
          (reparamSection (fun q : Fin 1 → ℝ => A q + pt1 t₀) S hS.1))
        (q, γ (A q + pt1 t₀)) :=
      ((hgc.tendsto_nhdsSet hg).eventually hz).mono fun q hq =>
        (isZeroAt_sectionAdd_reparamSection _ (fun q : Fin 1 → ℝ => A q + pt1 t₀) hS.1 q _).2 hq
    have e0 : A (pt1 0) + pt1 t₀ = pt1 t₀ := by
      rw [hgpt]
      congr 1
      simp [pt1]
    have e1 : A (pt1 1) + pt1 t₀ = pt1 t := by
      rw [hgpt]
      congr 1
      simp [pt1]
    have hloc := isPosOr_iff_of_path_local hX hbump hft hsec hU hUo ho hδs hδU hδU' hS' hz'
      (fun q hq p h0 => hbij _ (hg hq) p h0) (hsm _) (hsm _)
      (hzq _ (hg (pt1_mem_Icc (left_mem_Icc.2 zero_le_one))))
      (hzq _ (hg (pt1_mem_Icc (right_mem_Icc.2 zero_le_one))))
    have c0 := isPosOr_congr_pt hft.toIsScFredholmSection o (congrArg γ e0) (hsm _) (hsm _)
      (congrArg (pullbackSlice S) e0) (hS.pullbackSlice _) (hS.pullbackSlice _)
      (hzq _ (hg (pt1_mem_Icc (left_mem_Icc.2 zero_le_one)))) (hzq _ (pt1_mem_Icc ht₀))
    have c1 := isPosOr_congr_pt hft.toIsScFredholmSection o (congrArg γ e1) (hsm _) (hsm _)
      (congrArg (pullbackSlice S) e1) (hS.pullbackSlice _) (hS.pullbackSlice _)
      (hzq _ (hg (pt1_mem_Icc (right_mem_Icc.2 zero_le_one)))) (hzq _ (pt1_mem_Icc ht))
    exact (hP t₀ ht₀).trans (c0.symm.trans (hloc.trans (c1.trans (hP t ht).symm)))
  -- `[0, 1]` is connected
  have hlc : IsLocallyConstant fun t : unitInterval => Pt (t : ℝ) :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun x => by
      obtain ⟨ε, hε, h⟩ := key x x.2
      filter_upwards [Metric.ball_mem_nhds x hε] with y hy
      exact propext (h y y.2 (by rwa [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at hy)).symm
  have h01 : Pt 0 = Pt 1 := hlc.apply_eq_of_preconnectedSpace 0 1
  have ha := hP 0 (left_mem_Icc.2 zero_le_one)
  have hb := hP 1 (right_mem_Icc.2 zero_le_one)
  exact ha.symm.trans ((h01 ▸ Iff.rfl : Pt 0 ↔ Pt 1).trans hb)

end Push

end Polyfold
