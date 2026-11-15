import Polyfold.Chapter15.CanonicalLiftNaturality
import Polyfold.Chapter15.GeneralPositionEquivalence
import Polyfold.Chapter11.BranchedEquivalenceTangentOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702, **Theorem 15.4.1** and **Definition 15.4.2** (2017: Theorem 15.6, Definition 15.7),
read along a strong bundle equivalence (Definition 10.4.1), with Chapter 11's pull-back of
oriented branched ep⁺-subgroupoids (Theorem 11.3.5, Definition 11.3.6) and the identification of
orientations of Theorem 12.5.7.

# The canonical orientation is natural under strong bundle equivalences

## The text, paraphrased

(p. 702) For an oriented sc-Fredholm section functor `(f, o)` and an sc⁺-multisection `Λ` in
good position, `Θ = Λ ∘ f` carries the orientation `T̂_((f, o), Λ)`,
`T̂(y) = ∑ σᵢ · (ker (f − sᵢ)'(y), o_{i,y})`.  (§16.6, p. 739) The orientation of `θ = λ ∘ f`
on the polyfold is read in a model of `o`; two models differ by generalized strong bundle
isomorphisms, represented by diagrams of strong bundle equivalences `Φ : W → W'`, along which
`f = Φ^* f'`, `Λ = Λ' ∘ Φ`, and the orientations correspond (proof of Theorem 12.5.7).  The text
uses without comment that `T̂` is carried along: `T̂_((f, o), Λ) = ϕ^* T̂_((f', o'), Λ')`.

## What is formalized (namespace `Polyfold.SBLocalization`)

For two strong bundles over ep-groupoids `A`, `A'`, a strong bundle equivalence
`Φ : W → W'` covering `ϕ : X → X'` (`h : A.E.IsStrongBundleEquivalence A'.E ϕ Φ`), sc-Fredholm
section functors `f = Φ^* f'`, `f'`, an sc⁺-multisection `Λ'` of `W'`, `Λ = Λ' ∘ Φ`, and a family
`o'_y ∈ Or_y^{f'}`, carried to `o = h^* o'` (`pullOr`, through `orEqv`):

* `linOrTangent_mconj`: the oriented kernel `(ker L, o(L))` under a conjugation of operators
  between chart points of two different bundles (two-bundle form of `linOrTangent_conj`).
* `chartVec_tangent_obj_transportChart`: `Tϕ` is the identity of the chart vectors of `c'` and of
  the carried chart `c' ∘ Φ`.
* `subOp_mpullPt`: `(f − Ψ ∘ s' ∘ ϕ)'(y)` read in the carried chart point is `(f' − s')'(ϕ y)`.
* `mapDomain_linW_mpullPt`: the formal sum of oriented kernels of the carried local sc⁺-section
  structure at `y` is the image under `(Tϕ)⁻¹` of the one at `ϕ(y)`.
* `orTransfer_mpullPt_pullOr`: `o_y` read in the carried chart point is `o'_{ϕ y}` read in the
  original chart point.
* **`KernelBranching.canonSum_pullOr`**: for local branching structures described by kernels `K`
  of `(f, Λ)` and `K'` of `(f', Λ')`, `T̂(y) = (Tϕ)⁻¹ T̂'(ϕ y)` at every common smooth point.
* **`IsCanonicalFor.eq_pullSection`**: a canonical orientation of `Λ ∘ f` for `(f, h^* o')` is the
  pull-back `ϕ^* T̂'` (Chapter 11's `pullSection`, the orientation part of Definition 11.3.6) of
  a canonical orientation of `Λ' ∘ f'` for `(f', o')`, at every smooth point.
* `pullbackTheta_eq`, **`IsCanonicalPerturbation.eq_pullback`**: for oriented regular
  perturbations of `f` and `f'` with `Λ = Λ' ∘ Φ`, both with the canonical orientation, the
  oriented branched ep⁺-subgroupoid `(Λ ∘ f, T̂)` is `ϕ^*(Λ' ∘ f', T̂')`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

/-! ### The oriented kernel under a conjugation between two bundles -/

section Conj

variable {A A' : SEP.{u}} {f : A.Obj → A.W} {f' : A'.Obj → A'.W}

theorem orTangent_mk_ext' {n : ℕ} {C C' : Set A.X.PObj.TangentSpace}
    {F F' : Set (Fin n → A.X.PObj.TangentSpace)} (hC : C = C') (hF : F = F') :
    (⟨n, C, F⟩ : A.X.PObj.OrTangent) = ⟨n, C', F'⟩ := by
  subst hC; subst hF; rfl

set_option maxHeartbeats 800000 in
-- One long proof with the two kernels, their frames and the orientation of each.
open Classical in
/-- **The oriented kernel is carried by a conjugation between two bundles**: let `a`, `a'` be
chart points of `A` at `y` and of `A'` at `y'`, `AT : T_zO ≅ T_{z'}O'`, `AK : K_z ≅ K_{z'}` and
`D : E₀ ≅ E₀'` with `AT = D` on `T_zO`, and let `τ : TX → TX'` map `T_yX` onto `T_{y'}X'` with `D`
as its expression in the chart vectors.  For `L ∈ Lin(f, y)`, `L' ∈ Lin(f', y')` with
`L' AT = AK L`, the oriented tangent set `(ker L', o'(L'))` for the conjugated orientation `o'` is
the image under `τ` of `(ker L, o(L))`. -/
theorem linOrTangent_mconj {y : A.Obj} {y' : A'.Obj} (hf : A.B.IsScFredholmSection f)
    (hf' : A'.B.IsScFredholmSection f') (a : ChartPoint A.B y) (a' : ChartPoint A'.B y')
    (τ : A.X.PObj.TangentSpace → A'.X.PObj.TangentSpace) (AT : ↥a.T ≃L[ℝ] ↥a'.T)
    (AK : ↥a.K ≃L[ℝ] ↥a'.K) (D : a.c.φ.model.E 0 ≃L[ℝ] a'.c.φ.model.E 0)
    (hD : ∀ v : ↥a.T, ((AT v : ↥a'.T) : a'.c.φ.model.E 0) = D (v : a.c.φ.model.E 0))
    (hτ : ∀ α, A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = y →
      A'.X.PObj.levelVal 1 (A'.X.PObj.tangentProj (τ α)) = y' ∧
        chartVec a'.c.isChart (τ α) = D (chartVec a.c.isChart α))
    (hτs : ∀ α', A'.X.PObj.levelVal 1 (A'.X.PObj.tangentProj α') = y' →
      ∃ α, A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = y ∧ τ α = α')
    (hmem : ∀ S' ∈ a'.linSet f', ((AK.symm : ↥a'.K →L[ℝ] ↥a.K) ∘L S' ∘L
      (AT : ↥a.T →L[ℝ] ↥a'.T)) ∈ a.linSet f)
    (o : a.Or f hf) {S : ↥a.T →L[ℝ] ↥a.K} (hS : S ∈ a.linSet f) {S' : ↥a'.T →L[ℝ] ↥a'.K}
    (hS' : S' ∈ a'.linSet f') (hconj : ∀ v, S' (AT v) = AK (S v)) :
    linOrTangent hf' a' (o.conj (hC' := a'.isFredholm_of_mem_linSet hf') AT AK hmem) ⟨S', hS'⟩ =
      (linOrTangent hf a o ⟨S, hS⟩).map τ := by
  have hsurj_iff : Surjective S' ↔ Surjective S := by
    constructor
    · intro h k
      obtain ⟨w, hw⟩ := h (AK k)
      refine ⟨AT.symm w, AK.injective ?_⟩
      rw [← hconj, AT.apply_symm_apply, hw]
    · intro h k'
      obtain ⟨v, hv⟩ := h (AK.symm k')
      exact ⟨AT v, by rw [hconj, hv, AK.apply_symm_apply]⟩
  by_cases h : Surjective S
  · have h' := hsurj_iff.2 h
    have hfin := a.finiteDimensional_of_mem_linSet hf hS rfl
    have hfin' := a'.finiteDimensional_of_mem_linSet hf' hS' rfl
    set κ := conjKerEquivOfMap AT AK hconj a.T.subtypeL Subtype.val_injective rfl a'.T.subtypeL
      Subtype.val_injective rfl with hκdef
    have hκ : ∀ v, ((κ v : _) : a'.c.φ.model.E 0) = D (v : a.c.φ.model.E 0) := fun v => by
      obtain ⟨w, rfl⟩ := (kerEquivOfMap S a.T.subtypeL Subtype.val_injective rfl).surjective v
      exact (coe_conjKerEquivOfMap _ _ hconj _ _ rfl _ _ rfl w).trans (hD w.1)
    obtain ⟨n, hn⟩ : ∃ n, finrank ℝ ↥((LinearMap.ker (S : ↥a.T →ₗ[ℝ] ↥a.K)).map
      (a.T.subtypeL : ↥a.T →ₗ[ℝ] a.c.φ.model.E 0)) = n := ⟨_, rfl⟩
    have hn' : finrank ℝ ↥((LinearMap.ker (S' : ↥a'.T →ₗ[ℝ] ↥a'.K)).map
        (a'.T.subtypeL : ↥a'.T →ₗ[ℝ] a'.c.φ.model.E 0)) = n := κ.finrank_eq.symm.trans hn
    have hray : a'.orKer (hf := hf') (o.conj (hC' := a'.isFredholm_of_mem_linSet hf') AT AK hmem)
        hS' h' rfl = Module.Ray.map (maxPowEquiv κ) (a.orKer o hS h rfl) :=
      (congrArg (surjRay h' a'.T.subtypeL Subtype.val_injective rfl)
        (LineOrientation.conj_apply (hC' := a'.isFredholm_of_mem_linSet hf') AT AK hmem o hS hS'
          hconj)).trans (surjRay_conjDet _ _ h h' hconj _ _ rfl _ _ rfl _)
    have e1 : linOrTangent hf a o ⟨S, hS⟩ = _ :=
      (dif_pos h).trans (orTangent_mk_congr hf a o hS h hn rfl).symm
    have e2 : linOrTangent hf' a' (o.conj (hC' := a'.isFredholm_of_mem_linSet hf') AT AK hmem)
        ⟨S', hS'⟩ = _ := (dif_pos h').trans (orTangent_mk_congr hf' a' _ hS' h' hn' rfl).symm
    rw [e1, e2]
    refine orTangent_mk_ext' ?_ ?_
    · ext α'
      constructor
      · rintro ⟨hov, hN⟩
        obtain ⟨α, hα, rfl⟩ := hτs α' hov
        refine ⟨α, ⟨hα, ?_⟩, rfl⟩
        have h1 : D (κ.symm ⟨_, hN⟩ : a.c.φ.model.E 0) = D (chartVec a.c.isChart α) := by
          rw [← hκ, LinearEquiv.apply_symm_apply]
          exact (hτ α hα).2
        change chartVec a.c.isChart α ∈ _
        rw [← D.injective h1]
        exact (κ.symm ⟨_, hN⟩).2
      · rintro ⟨α, ⟨hα, hN⟩, rfl⟩
        refine ⟨(hτ α hα).1, ?_⟩
        change chartVec a'.c.isChart (τ α) ∈ _
        rw [(hτ α hα).2, ← hκ ⟨_, hN⟩]
        exact (κ ⟨_, hN⟩).2
    · ext v
      change v ∈ chartFrames a'.c.isChart _ _ (pullOr hn' (LinearEquiv.refl ℝ _)
          (a'.orKer (hf := hf') (o.conj (hC' := a'.isFredholm_of_mem_linSet hf') AT AK hmem) hS'
            h' rfl)) ↔
        v ∈ (fun u => τ ∘ u) '' chartFrames a.c.isChart _ _ (pullOr hn (LinearEquiv.refl ℝ _)
          (a.orKer o hS h rfl))
      rw [hray]
      constructor
      · rintro ⟨hv, b', hb', hbo'⟩
        have hex : ∀ i, ∃ α : A.X.PObj.TangentSpace,
            A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = y ∧ τ α = v i :=
          fun i => hτs _ (hv i).1
        choose u hu using hex
        have hbb : (b'.map κ.symm).map κ = b' := Basis.eq_of_apply_eq fun i => by
          rw [Basis.map_apply, Basis.map_apply, LinearEquiv.apply_symm_apply]
        have hcv : ∀ i, chartVec a.c.isChart (u i) = ((b'.map κ.symm) i : a.c.φ.model.E 0) :=
          fun i => by
            apply D.injective
            rw [← (hτ _ (hu i).1).2, (hu i).2, ← hκ, Basis.map_apply,
              LinearEquiv.apply_symm_apply]
            exact (hb' i).symm
        refine ⟨u, ⟨fun i => ⟨(hu i).1, ?_⟩, b'.map κ.symm, fun i => (hcv i).symm, ?_⟩,
          funext fun i => (hu i).2⟩
        · change chartVec a.c.isChart (u i) ∈ _
          rw [hcv i]
          exact ((b'.map κ.symm) i).2
        · exact (orientation_map_pullOr_iff hn hn' κ _ (b'.map κ.symm)).1
            ((congrArg Basis.orientation hbb).trans hbo')
      · rintro ⟨u, ⟨hu, b, hb, hbo⟩, rfl⟩
        have hcv : ∀ i, chartVec a'.c.isChart (τ (u i)) = ((b.map κ) i : a'.c.φ.model.E 0) :=
          fun i => by rw [(hτ _ (hu i).1).2, Basis.map_apply, hκ, hb i]
        refine ⟨fun i => ⟨(hτ _ (hu i).1).1, ?_⟩, b.map κ, fun i => (hcv i).symm,
          (orientation_map_pullOr_iff hn hn' κ _ _).2 hbo⟩
        change chartVec a'.c.isChart (τ (u i)) ∈ _
        rw [hcv i]
        exact ((b.map κ) i).2
  · have e1 : linOrTangent hf a o ⟨S, hS⟩ = ⟨0, ∅, ∅⟩ := dif_neg h
    have e2 : linOrTangent hf' a' (o.conj (hC' := a'.isFredholm_of_mem_linSet hf') AT AK hmem)
        ⟨S', hS'⟩ = ⟨0, ∅, ∅⟩ := dif_neg (mt hsurj_iff.1 h)
    rw [e1, e2]
    exact orTangent_mk_ext' (image_empty _).symm (image_empty _).symm

end Conj

/-! ### Along a strong bundle equivalence -/

section Equiv

variable {A A' : SEP.{u}} {ϕ : EpFunctor A.X A'.X}
  {Φ : EpFunctor A.E.toEpGroupoid A'.E.toEpGroupoid}
  (h : A.E.IsStrongBundleEquivalence A'.E ϕ Φ)

/-- **`Tϕ` is the identity of the chart vectors** of a chart `c'` of `W'` with domain in `U'(y)`
and of the carried chart `c' ∘ Φ` of `W`, over `U(y) ∩ ϕ⁻¹(dom c')`. -/
theorem chartVec_tangent_obj_transportChart (y : A.Obj) {c' : StrongBundleChart A'.X.PObj A'.P}
    (hsub : c'.φ.source ⊆ h.locSet' y) {α : A.X.PObj.TangentSpace}
    (hα : A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) ∈ h.locSet y ∩ ϕ.obj ⁻¹' c'.φ.source) :
    chartVec c'.isChart (ϕ.tangent.obj α) =
      chartVec ((h.locIso y).transportChart c' hsub).isChart α := by
  have hαU : α ∈ A.X.PObj.tangentPreimage (h.locSet y) := hα.1
  rw [EpFunctor.tangent_obj_eq_tangentMapOn (F := ϕ) (h.locIso y).base hαU]
  exact chartVec_tangentMapOn_of_isScDiffeoOn (h.locIso y).base c'.isChart hα

/-- The inverse `(Tϕ)⁻¹` on `T_{ϕ y}X'` lands in `T_yX` and is the identity of the chart vectors
of `c'` and `c' ∘ Φ`. -/
theorem fibreInv_tangent_obj_chartVec (y : A.Obj) {c' : StrongBundleChart A'.X.PObj A'.P}
    (hsub : c'.φ.source ⊆ h.locSet' y) (hyc' : ϕ.obj y ∈ c'.φ.source)
    {α' : A'.X.PObj.TangentSpace}
    (hα' : A'.X.PObj.levelVal 1 (A'.X.PObj.tangentProj α') = ϕ.obj y) :
    A.X.PObj.levelVal 1 (A.X.PObj.tangentProj (fibreInv ϕ.tangent.obj y α')) = y ∧
      chartVec ((h.locIso y).transportChart c' hsub).isChart (fibreInv ϕ.tangent.obj y α') =
        chartVec c'.isChart α' := by
  obtain ⟨h1, h2⟩ := EpFunctor.fibreInv_spec_tangent h.isEquivalence_base.isLocalScDiffeo_obj hα'
  refine ⟨h1, ?_⟩
  rw [← chartVec_tangent_obj_transportChart h y hsub (by rw [h1]; exact ⟨h.mem_locSet y, hyc'⟩),
    h2]

include h in
/-- `(Tϕ)⁻¹` maps `T_{ϕ y}X'` onto `T_yX`. -/
theorem exists_fibreInv_tangent_obj_eq (y : A.Obj) {α : A.X.PObj.TangentSpace}
    (hα : A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = y) :
    ∃ α', A'.X.PObj.levelVal 1 (A'.X.PObj.tangentProj α') = ϕ.obj y ∧
      fibreInv ϕ.tangent.obj y α' = α :=
  ⟨ϕ.tangent.obj α, by rw [EpFunctor.levelVal_tangentProj_tangent_obj, hα],
    fibreInv_apply (EpFunctor.injOn_tangent_obj h.isEquivalence_base.isLocalScDiffeo_obj y) hα⟩

variable {f : A.Obj → A.W} {f' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor f)
  (hF' : A'.E.IsScFredholmSectionFunctor f') (hpb : f = h.pullback f')
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)

/-! ### The operators `(f − sᵢ)'` in the carried chart point -/

include hpb in
/-- **`(f − Ψ ∘ s' ∘ ϕ)'(y)` read in the carried chart point is `(f' − s')'(ϕ y)`** read in the
original chart point. -/
theorem subOp_mpullPt {y : A.Obj} {s' : A'.Obj → A'.W} {O' : Set A'.Obj} (hO' : IsOpen O')
    (hO's : O' ⊆ h.locSet' y) (hs' : IsScPlusSectionOn A' s' O')
    (p : ChartPoint A'.B (ϕ.obj y)) (hp : p.c.φ.source ⊆ h.locSet' y)
    (hsub' : p.c.φ.source ⊆ O')
    (hsub : ((h.locIso y).mpullPt p hp (h.mem_locSet y) rfl).c.φ.source ⊆
      isoSet (h.locIso y) O')
    (hfs : f y = isoSec (h.locIso y) s' y) (hfs' : f' (ϕ.obj y) = s' (ϕ.obj y)) (v : ↥p.T) :
    ((subOp hF.2.isScSmooth (isScPlusSectionOn_isoSec (h.locIso y) hO' hO's hs')
        ((h.locIso y).mpullPt p hp (h.mem_locSet y) rfl) hsub hfs v).1 : p.c.F 0) =
      (subOp hF'.2.isScSmooth hs' p hsub' hfs' v).1 :=
  congrArg (fun M : p.c.φ.model.E 0 →L[ℝ] p.c.F 0 => M v.1)
    (subDeriv_transportChart (h.locIso y) (hsub := hp) hF'.2.isScSmooth
      (h.eqOn_loc hpb hF'.2.isScSmooth.1 y) hs' p.isChart hsub' p.mem_U)

open Classical in
include hpb in
/-- **The formal sum of oriented kernels is carried by `(Tϕ)⁻¹`**: for a local sc⁺-section
structure `(sᵢ, σᵢ)` of `Λ'` on `O' ⊆ U'(y)` and the carried structure `(Ψ ∘ sᵢ ∘ ϕ, σᵢ)` of
`Λ = Λ' ∘ Φ`, the image of `∑ σᵢ · (f − Ψ ∘ sᵢ ∘ ϕ)'(y)` under `L ↦ (ker L, o(L))` in the carried
chart point, for the carried orientation, is the image under `(Tϕ)⁻¹` of the sum at `ϕ(y)`. -/
theorem mapDomain_linW_mpullPt {y : A.Obj} {Λ' : A'.W → ℚ≥0} {O' : Set A'.Obj} (hO' : IsOpen O')
    (hO's : O' ⊆ h.locSet' y) {k : ℕ} {sb : Fin k → A'.Obj → A'.W} {σ : Fin k → ℚ≥0}
    (hrep' : IsLocalRepOn A' Λ' O' sb σ)
    (hrep : IsLocalRepOn A (fun w => Λ' (Φ.obj w)) (isoSet (h.locIso y) O')
      (fun i => isoSec (h.locIso y) (sb i)) σ)
    (p : ChartPoint A'.B (ϕ.obj y)) (hp : p.c.φ.source ⊆ h.locSet' y)
    (hsub' : p.c.φ.source ⊆ O')
    (hsub : ((h.locIso y).mpullPt p hp (h.mem_locSet y) rfl).c.φ.source ⊆
      isoSet (h.locIso y) O')
    (hys : y ∈ A.X.PObj.smoothSet) (hys' : ϕ.obj y ∈ A'.X.PObj.smoothSet)
    (hlin : ((h.locIso y).mpullPt p hp (h.mem_locSet y) rfl).linSet f = p.linSet f')
    (o₀ : p.Or f' hF'.2) :
    (linW hF.2 (isOpen_isoSet (h.locIso y) hO') hrep
        ((h.locIso y).mpullPt p hp (h.mem_locSet y) rfl) hsub hys hsec).mapDomain
        (linOrTangent hF.2 ((h.locIso y).mpullPt p hp (h.mem_locSet y) rfl)
          ((h.locIso y).morPull hF.2 hF'.2 p hp (h.mem_locSet y) rfl hlin o₀)) =
      (linW hF'.2 hO' hrep' p hsub' hys' hsec').mapDomain
        (fun L => (linOrTangent hF'.2 p o₀ L).map (fibreInv ϕ.tangent.obj y)) := by
  set L := h.locIso y with hL
  have hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) (h.locSet y) := h.eqOn_loc hpb hF'.2.isScSmooth.1 y
  have hyU : y ∈ h.locSet y := h.mem_locSet y
  have hxO : ϕ.obj y ∈ O' := hsub' p.mem_source
  have hcond : ∀ i, isoSec L (sb i) y = f y ↔ sb i (ϕ.obj y) = f' (ϕ.obj y) := fun i => by
    have e2 : f y = L.Ψ (f' (ϕ.obj y)) := hfL hyU
    change L.Ψ (sb i (ϕ.obj y)) = f y ↔ _
    rw [e2]
    constructor
    · intro h0
      have h1 := congrArg L.Φ h0
      rwa [L.zero.right_inv _ (show A'.P (sb i (ϕ.obj y)) ∈ h.locSet' y by
          rw [(hrep'.2.1 i).1 _ hxO]; exact hO's hxO),
        L.zero.right_inv _ (show A'.P (f' (ϕ.obj y)) ∈ h.locSet' y by
          rw [hF'.1.1.1 (ϕ.obj y)]; exact hO's hxO)] at h1
    · intro h0
      rw [h0]
  unfold linW
  rw [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : sb i (ϕ.obj y) = f' (ϕ.obj y)
  · rw [dif_pos ((hcond i).2 hi), dif_pos hi, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    refine congrArg (fun g => Finsupp.single g (σ i)) ?_
    have hτ := fun (α' : A'.X.PObj.TangentSpace)
        (hα' : A'.X.PObj.levelVal 1 (A'.X.PObj.tangentProj α') = ϕ.obj y) =>
      fibreInv_tangent_obj_chartVec h y hp p.mem_source hα'
    exact linOrTangent_mconj hF'.2 hF.2 p (L.mpullPt p hp hyU rfl) (fibreInv ϕ.tangent.obj y)
      (L.mcastT p hp hyU rfl) (L.mcastK p hp hyU rfl)
      (ContinuousLinearEquiv.refl ℝ (p.c.φ.model.E 0)) (fun _ => rfl)
      (fun α' hα' => ⟨(hτ α' hα').1, (hτ α' hα').2⟩)
      (fun α hα => exists_fibreInv_tangent_obj_eq h y hα)
      (StrongBundle.LocalIso.mcastT_mem hlin) o₀ _ _
      (fun v => Subtype.ext (subOp_mpullPt h hF hF' hpb hO' hO's (hrep'.2.1 i) p hp hsub' hsub
        ((hcond i).2 hi).symm hi.symm v))
  · rw [dif_neg (mt (hcond i).1 hi), dif_neg hi, Finsupp.mapDomain_zero, Finsupp.mapDomain_zero]

/-! ### The carried orientation in the carried chart point -/

/-- **`o_y = orEqv (o'_{ϕ y})` read in the carried chart point** is `o'_{ϕ y}` read in the
original chart point, carried by `morPull` (the identity of the two `Lin` sets). -/
theorem orTransfer_mpullPt_orEqv {y : A.Obj} (hys : y ∈ A.X.PObj.smoothSet)
    (p : ChartPoint A'.B (ϕ.obj y)) (hp : p.c.φ.source ⊆ h.locSet' y)
    (hlin : ((h.locIso y).mpullPt p hp (h.mem_locSet y) rfl).linSet f = p.linSet f')
    (o₀ : Orx f' hF'.2 (ϕ.obj y) (h.smooth_obj hys)) :
    (orPt A.B y hys).orTransfer ((h.locIso y).mpullPt p hp (h.mem_locSet y) rfl) hF.2 hys
        (h.orEqv hF hF' hpb hsec hsec' y hys o₀) =
      (h.locIso y).morPull hF.2 hF'.2 p hp (h.mem_locSet y) rfl hlin
        ((orPt A'.B (ϕ.obj y) (h.smooth_obj hys)).orTransfer p hF'.2 (h.smooth_obj hys) o₀) := by
  set L := h.locIso y with hL
  have e : h.orEqv hF hF' hpb hsec hsec' y hys =
      L.morVia hF.2 hF'.2 (orPt A'.B _ (h.smooth_obj hys)) (orPt A.B y hys) p hp
        (h.mem_locSet y) rfl hlin (h.smooth_obj hys) hys :=
    L.morVia_eq hF.2 hF'.2 _ _ _ hp (h.mem_locSet y) rfl _ hlin (h.smooth_obj hys) hys
  rw [e]
  exact DFunLike.congr_fun ((ChartPoint.orTransfer_trans (L.mpullPt p hp (h.mem_locSet y) rfl)
    (orPt A.B y hys) (L.mpullPt p hp (h.mem_locSet y) rfl) hF.2 hys).trans
      (ChartPoint.orTransfer_self _ hF.2 hys)) _

/-- The chart point of Part I in the carried chart is the carried chart point. -/
theorem chartPtOf_transportChart_eq_mpullPt {y : A.Obj} {c' : StrongBundleChart A'.X.PObj A'.P}
    (hc' : A'.B.IsChart c') (hsub : c'.φ.source ⊆ h.locSet' y) (hyc' : ϕ.obj y ∈ c'.φ.source)
    (hys : y ∈ A.X.PObj.smoothSet) (hys' : ϕ.obj y ∈ A'.X.PObj.smoothSet)
    (hc : A.B.IsChart ((h.locIso y).transportChart c' hsub))
    (hyc : y ∈ ((h.locIso y).transportChart c' hsub).φ.source) :
    chartPtOf ((h.locIso y).transportChart c' hsub) hc hyc hys =
      (h.locIso y).mpullPt (chartPtOf c' hc' hyc' hys') hsub (h.mem_locSet y) rfl := by
  have hz : (exists_lift_of_smooth ((h.locIso y).transportChart c' hsub) hyc hys).choose =
      (exists_lift_of_smooth c' hyc' hys').choose := by
    refine c'.φ.model.E.toBase_injective 1
      ((exists_lift_of_smooth ((h.locIso y).transportChart c' hsub) hyc hys).choose_spec.trans
        (Eq.trans ?_ (exists_lift_of_smooth c' hyc' hys').choose_spec.symm))
    rfl
  unfold StrongBundle.LocalIso.mpullPt chartPtOf chartPt
  congr 1

open Classical in
include hpb in
/-- The sum of oriented kernels at `y` for the carried orientation, in a chart point equal to the
carried chart point, is the image under `(Tϕ)⁻¹` of the sum at `ϕ(y)`. -/
theorem mapDomain_linW_of_eq_mpullPt {y : A.Obj} {Λ' : A'.W → ℚ≥0}
    (o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx f' hF'.2 x hs) {O' : Set A'.Obj}
    (hO' : IsOpen O') (hO's : O' ⊆ h.locSet' y) {k : ℕ} {sb : Fin k → A'.Obj → A'.W}
    {σ : Fin k → ℚ≥0} (hrep' : IsLocalRepOn A' Λ' O' sb σ)
    (hrep : IsLocalRepOn A (fun w => Λ' (Φ.obj w)) (isoSet (h.locIso y) O')
      (fun i => isoSec (h.locIso y) (sb i)) σ)
    (p : ChartPoint A'.B (ϕ.obj y)) (hp : p.c.φ.source ⊆ h.locSet' y)
    (hsub' : p.c.φ.source ⊆ O') (hys : y ∈ A.X.PObj.smoothSet)
    (hys' : ϕ.obj y ∈ A'.X.PObj.smoothSet) (q : ChartPoint A.B y)
    (hq : q = (h.locIso y).mpullPt p hp (h.mem_locSet y) rfl)
    (hsubq : q.c.φ.source ⊆ isoSet (h.locIso y) O') :
    (linW hF.2 (isOpen_isoSet (h.locIso y) hO') hrep q hsubq hys hsec).mapDomain
        (linOrTangent hF.2 q ((orPt A.B y hys).orTransfer q hF.2 hys
          (h.pullOr hF hF' hpb hsec hsec' o' y hys))) =
      (linW hF'.2 hO' hrep' p hsub' hys' hsec').mapDomain
        (fun L => (linOrTangent hF'.2 p ((orPt A'.B _ hys').orTransfer p hF'.2 hys'
          (o' _ hys')) L).map (fibreInv ϕ.tangent.obj y)) := by
  subst hq
  have hlin : ((h.locIso y).mpullPt p hp (h.mem_locSet y) rfl).linSet f = p.linSet f' :=
    StrongBundle.LocalIso.linSet_mpullPt hF.2 hF'.2 (h.eqOn_loc hpb hF'.2.isScSmooth.1 y) hsec
      hsec' hys hys'
  change (linW hF.2 (isOpen_isoSet (h.locIso y) hO') hrep _ hsubq hys hsec).mapDomain
      (linOrTangent hF.2 _ ((orPt A.B y hys).orTransfer _ hF.2 hys
        (h.orEqv hF hF' hpb hsec hsec' y hys (o' (ϕ.obj y) (h.smooth_obj hys))))) = _
  rw [orTransfer_mpullPt_orEqv h hF hF' hpb hsec hsec' hys p hp hlin]
  exact mapDomain_linW_mpullPt h hF hF' hpb hsec hsec' hO' hO's hrep' hrep p hp hsub' hsubq hys
    hys' hlin _

/-! ### The canonical orientation along the equivalence -/

/-- **2021 Theorem 15.4.1 / Definition 15.4.2 along a strong bundle equivalence** (pp. 701–702,
with the identification of orientations of Theorem 12.5.7): for `f = Φ^* f'`, `Λ = Λ' ∘ Φ` and
the carried family `o = h^* o'`, the formula `∑ σᵢ · (T_yMᵢ, o_{i,y})` of a local branching
structure `K` of `Λ ∘ f` described by kernels is, at every smooth `y ∈ U(K)` with `ϕ(y) ∈ U(K')`,
the image under `(Tϕ)⁻¹` of the formula of a structure `K'` of `Λ' ∘ f'`. -/
theorem KernelBranching.canonSum_pullOr {Λ' : A'.W → ℚ≥0}
    (o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx f' hF'.2 x hs) {x : A.Obj} {x' : A'.Obj}
    (K : KernelBranching A f (fun w => Λ' (Φ.obj w)) x) (K' : KernelBranching A' f' Λ' x')
    {y : A.Obj} (hyU : y ∈ K.U) (hyU' : ϕ.obj y ∈ K'.U) (hys : y ∈ A.X.PObj.smoothSet) :
    K.canonSum hF.2 hsec (h.pullOr hF hF' hpb hsec hsec' o') y =
      (K'.canonSum hF'.2 hsec' o' (ϕ.obj y)).mapDomain
        (OrTangent.map (fibreInv ϕ.tangent.obj y)) := by
  classical
  set L := h.locIso y with hLdef
  have hys' : ϕ.obj y ∈ A'.X.PObj.smoothSet := h.smooth_obj hys
  have hgy : L.g (ϕ.obj y) = y := L.base.left_inv y (h.mem_locSet y)
  have hG : IsOpen (h.locSet' y ∩ L.g ⁻¹' K.O) :=
    L.base.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage L.isOpen_U' K.isOpen_O
  have hV : IsOpen (K'.O ∩ (h.locSet' y ∩ L.g ⁻¹' K.O)) := K'.isOpen_O.inter hG
  have hyV : ϕ.obj y ∈ K'.O ∩ (h.locSet' y ∩ L.g ⁻¹' K.O) :=
    ⟨K'.U_subset hyU', h.obj_mem_locSet' y, by rw [mem_preimage, hgy]; exact K.U_subset hyU⟩
  set c' := (orChart A'.B (ϕ.obj y)).restrictInter hV with hc'def
  have hc' : A'.B.IsChart c' :=
    StrongBundle.IsChart.restrictInter hV (isChart_orChart (B := A'.B) _)
  have hyc' : ϕ.obj y ∈ c'.φ.source :=
    StrongBundleChart.mem_restrictInter_source _ hV (mem_orChart _) hyV
  have hcV : c'.φ.source ⊆ K'.O ∩ (h.locSet' y ∩ L.g ⁻¹' K.O) :=
    StrongBundleChart.restrictInter_source_subset (orChart A'.B (ϕ.obj y)) hV
  have hsubK' : c'.φ.source ⊆ K'.O := fun z hz => (hcV hz).1
  have hsubU' : c'.φ.source ⊆ h.locSet' y := fun z hz => (hcV hz).2.1
  have hO₁ : IsOpen (K'.O ∩ h.locSet' y) := K'.isOpen_O.inter L.isOpen_U'
  have hrep₁ : IsLocalRepOn A' Λ' (K'.O ∩ h.locSet' y) K'.sAll K'.σAll :=
    K'.isLocalRep.mono hO₁ inter_subset_left
  have hrepI := isLocalRepOn_isoSec L (Λ := fun w => Λ' (Φ.obj w)) (fun _ _ => rfl) hO₁
    inter_subset_right hrep₁
  have hsub₁ : c'.φ.source ⊆ K'.O ∩ h.locSet' y := fun z hz => ⟨hsubK' hz, hsubU' hz⟩
  have hc : A.B.IsChart (L.transportChart c' hsubU') := L.isChart_transportChart c' hsubU' hc'
  have hyc : y ∈ (L.transportChart c' hsubU').φ.source := ⟨h.mem_locSet y, hyc'⟩
  have hsubI : (L.transportChart c' hsubU').φ.source ⊆ isoSet L (K'.O ∩ h.locSet' y) :=
    fun z hz => ⟨hz.1, hsub₁ hz.2⟩
  have hsubK : (L.transportChart c' hsubU').φ.source ⊆ K.O := fun z hz => by
    have h1 : L.g (L.ϕ z) ∈ K.O := (hcV hz.2).2.2
    rwa [L.base.left_inv z hz.1] at h1
  have e1 : K'.canonSum hF'.2 hsec' o' (ϕ.obj y) =
      Finsupp.mapRange ((↑) : ℚ≥0 → ℚ) NNRat.cast_zero
        ((linW hF'.2 hO₁ hrep₁ (chartPtOf c' hc' hyc' hys') hsub₁ hys' hsec').mapDomain
          (linOrTangent hF'.2 (chartPtOf c' hc' hyc' hys')
            (toChartOr hF'.2 hys' c' hc' hyc' (o' _ hys')))) := Finsupp.ext fun g => by
    rw [Finsupp.mapRange_apply, K'.canonSum_apply_eq hF'.2 hsec' o' hyU' hys' hc' hyc' hsubK' g,
      linW_chartPtOf_eq hF'.2 K'.isOpen_O hO₁ K'.isLocalRep hrep₁ hys' hsec' hc' hyc' hsubK'
        hsub₁]
  have e2 : K.canonSum hF.2 hsec (h.pullOr hF hF' hpb hsec hsec' o') y =
      Finsupp.mapRange ((↑) : ℚ≥0 → ℚ) NNRat.cast_zero
        ((linW hF.2 (isOpen_isoSet L hO₁) hrepI
            (chartPtOf (L.transportChart c' hsubU') hc hyc hys) hsubI hys hsec).mapDomain
          (linOrTangent hF.2 (chartPtOf (L.transportChart c' hsubU') hc hyc hys)
            (toChartOr hF.2 hys (L.transportChart c' hsubU') hc hyc
              (h.pullOr hF hF' hpb hsec hsec' o' y hys)))) :=
    Finsupp.ext fun g => by
      rw [Finsupp.mapRange_apply, K.canonSum_apply_eq hF.2 hsec _ hyU hys hc hyc hsubK g,
        linW_chartPtOf_eq hF.2 K.isOpen_O (isOpen_isoSet L hO₁) K.isLocalRep hrepI hys hsec
          hc hyc hsubK hsubI]
  rw [e1, e2, Finsupp.mapDomain_mapRange _ _ _ _ (fun x y => NNRat.cast_add x y),
    ← Finsupp.mapDomain_comp]
  congr 1
  exact mapDomain_linW_of_eq_mpullPt h hF hF' hpb hsec hsec' o' hO₁ inter_subset_right hrep₁
    hrepI (chartPtOf c' hc' hyc' hys') hsubU' hsub₁ hys hys' _
    (chartPtOf_transportChart_eq_mpullPt h hc' hsubU' hyc' hys hys' hc hyc) hsubI

include hF' hpb in
/-- `Λ ∘ f = (Λ' ∘ f') ∘ ϕ` for `f = Φ^* f'` and `Λ = Λ' ∘ Φ`. -/
theorem multisection_pullback_apply {Λ' : A'.W → ℚ≥0} (y : A.Obj) :
    Λ' (Φ.obj (f y)) = Λ' (f' (ϕ.obj y)) := by
  rw [hpb, h.obj_pullback hF'.1.1.1 y]

include hpb in
/-- **The canonical orientation is natural under strong bundle equivalences** (2021 Theorem
15.4.1, Definition 15.4.2, with Definition 11.3.6's pull-back): if `T̂` is canonical for
`(Λ' ∘ Φ) ∘ f` and the carried family `h^* o'`, and `T̂'` is canonical for `Λ' ∘ f'` and `o'`,
then `T̂ = ϕ^* T̂'` (Chapter 11's `pullSection`) at every smooth point. -/
theorem IsCanonicalFor.eq_pullSection {Λ' : A'.W → ℚ≥0}
    {o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx f' hF'.2 x hs} {n n' : ℕ}
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} {T' : A'.Obj → A'.X.PObj.OrTangent →₀ ℚ}
    (hT : IsCanonicalFor (fun w => Λ' (Φ.obj w)) hF.2 hsec (h.pullOr hF hF' hpb hsec hsec' o') n T)
    (hT' : IsCanonicalFor Λ' hF'.2 hsec' o' n' T') {y : A.Obj}
    (hys : y ∈ A.X.PObj.smoothSet) : T y = ϕ.pullSection T' y := by
  rw [EpFunctor.pullSection_of_mem hys]
  have hys' := h.smooth_obj hys
  have hsupp : y ∈ EpGroupoid.supp (fun z => ((Λ' (Φ.obj (f z)) : ℚ≥0) : ℚ)) ↔
      ϕ.obj y ∈ EpGroupoid.supp (fun z => ((Λ' (f' z) : ℚ≥0) : ℚ)) := by
    change (0 : ℚ) < (Λ' (Φ.obj (f y)) : ℚ) ↔ (0 : ℚ) < (Λ' (f' (ϕ.obj y)) : ℚ)
    rw [multisection_pullback_apply h hF' hpb (Λ' := Λ') y]
  by_cases hy : y ∈ EpGroupoid.supp (fun z => ((Λ' (Φ.obj (f z)) : ℚ≥0) : ℚ))
  · obtain ⟨K, hc, hn, hR⟩ := hT.2 y hy
    obtain ⟨K', hc', hn', hR'⟩ := hT'.2 _ (hsupp.1 hy)
    rw [hR y K.mem_U hys, hR' _ K'.mem_U hys', K.orientedSum_toOrientedTame,
      K'.orientedSum_toOrientedTame]
    exact K.canonSum_pullOr h hF hF' hpb hsec hsec' o' K' K.mem_U K'.mem_U hys
  · rw [hT.1.eq_zero_of_not_mem hys hy, hT'.1.eq_zero_of_not_mem hys' (mt hsupp.2 hy),
      Finsupp.mapDomain_zero]

/-! ### Oriented regular perturbations -/

include hpb in
/-- **The canonical orientations of two perturbations related by the equivalence**: for oriented
regular perturbations `P` of `f = Φ^* f'` and `P'` of `f'` with `Λ = Λ' ∘ Φ`, both carrying the
canonical orientation (for `h^* o'` and `o'`), `T̂ = ϕ^* T̂'` at every smooth point. -/
theorem IsCanonicalPerturbation.eq_pullSection
    {o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx f' hF'.2 x hs} {m m' : ℕ}
    {P : OrientedRegularPerturbation A f m} {P' : OrientedRegularPerturbation A' f' m'}
    (hΛ : P.Λ = fun w => P'.Λ (Φ.obj w))
    (hP : IsCanonicalPerturbation hF.2 hsec (h.pullOr hF hF' hpb hsec hsec' o') P)
    (hP' : IsCanonicalPerturbation hF'.2 hsec' o' P') {y : A.Obj}
    (hys : y ∈ A.X.PObj.smoothSet) : P.T y = ϕ.pullSection P'.T y := by
  have hP₁ : IsCanonicalFor (fun w => P'.Λ (Φ.obj w)) hF.2 hsec
      (h.pullOr hF hF' hpb hsec hsec' o') (m + 1) P.T := hΛ ▸ hP
  exact IsCanonicalFor.eq_pullSection h hF hF' hpb hsec hsec' hP₁ hP' hys

include hF' hpb in
/-- For `Λ = Λ' ∘ Φ`, the branched ep⁺-subgroupoid `Λ ∘ f` is the pull-back `ϕ^*(Λ' ∘ f')`
(Definition 11.2.1). -/
theorem pullbackTheta_eq {Λ : A.W → ℚ≥0} {Λ' : A'.W → ℚ≥0} (hΛ : Λ = fun w => Λ' (Φ.obj w)) :
    (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) = ϕ.pullbackTheta (fun z => ((Λ' (f' z) : ℚ≥0) : ℚ)) := by
  subst hΛ
  funext z
  rw [EpFunctor.pullbackTheta_apply]
  exact congrArg (fun q : ℚ≥0 => (q : ℚ)) (multisection_pullback_apply h hF' hpb (Λ' := Λ') z)

include hpb in
/-- **2021 Theorem 15.4.1, Definition 15.4.2 and Definition 11.3.6 along a strong bundle
equivalence**: for oriented regular perturbations `P` of `f = Φ^* f'` and `P'` of `f'` with
`Λ = Λ' ∘ Φ` and the canonical orientations of `(f, h^* o')` and `(f', o')`, the oriented
branched ep⁺-subgroupoid `(Λ ∘ f, T̂)` is `ϕ^*(Λ' ∘ f', T̂')` (on `X_∞` for `T̂`). -/
theorem IsCanonicalPerturbation.eq_pullback
    {o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx f' hF'.2 x hs} {m m' : ℕ}
    {P : OrientedRegularPerturbation A f m} {P' : OrientedRegularPerturbation A' f' m'}
    (hΛ : P.Λ = fun w => P'.Λ (Φ.obj w))
    (hP : IsCanonicalPerturbation hF.2 hsec (h.pullOr hF hF' hpb hsec hsec' o') P)
    (hP' : IsCanonicalPerturbation hF'.2 hsec' o' P') :
    (fun z => ((P.Λ (f z) : ℚ≥0) : ℚ)) = ϕ.pullbackTheta (fun z => ((P'.Λ (f' z) : ℚ≥0) : ℚ)) ∧
      ∀ y ∈ A.X.PObj.smoothSet, P.T y = ϕ.pullSection P'.T y :=
  ⟨pullbackTheta_eq h hF' hpb hΛ, fun _ hys =>
    IsCanonicalPerturbation.eq_pullSection h hF hF' hpb hsec hsec' hΛ hP hP' hys⟩

end Equiv

/-! ### Two strong bundle equivalences out of one bundle -/

section Diagram

variable {A₁ A₂ A'' : SEP.{u}} {ϕ₁ : EpFunctor A''.X A₁.X}
  {Φ₁ : EpFunctor A''.E.toEpGroupoid A₁.E.toEpGroupoid} {ϕ₂ : EpFunctor A''.X A₂.X}
  {Φ₂ : EpFunctor A''.E.toEpGroupoid A₂.E.toEpGroupoid}
  (h₁ : A''.E.IsStrongBundleEquivalence A₁.E ϕ₁ Φ₁)
  (h₂ : A''.E.IsStrongBundleEquivalence A₂.E ϕ₂ Φ₂)
  {f₁ : A₁.Obj → A₁.W} {f₂ : A₂.Obj → A₂.W} {f'' : A''.Obj → A''.W}
  (hF₁ : A₁.E.IsScFredholmSectionFunctor f₁) (hF₂ : A₂.E.IsScFredholmSectionFunctor f₂)
  (hF'' : A''.E.IsScFredholmSectionFunctor f'') (hpb₁ : f'' = h₁.pullback f₁)
  (hpb₂ : f'' = h₂.pullback f₂) (hsec₁ : A₁.B.HasScPlusSectionsThrough)
  (hsec₂ : A₂.B.HasScPlusSectionsThrough) (hsec'' : A''.B.HasScPlusSectionsThrough)

include hpb₁ hpb₂ in
/-- **The canonical orientations of two models agree over a diagram of strong bundle
equivalences** `W₁ ←Φ₁ W'' →Φ₂ W₂` (proof of Theorem 12.5.7 and §16.6, p. 739): let
`Λ₁ ∘ Φ₁ = Λ₂ ∘ Φ₂`, let the orientations `o₁`, `o₂` correspond over `W''`
(`h₁^* o₁ = h₂^* o₂`), and let `T̂₁`, `T̂₂` be the canonical orientations of `Λ₁ ∘ f₁` and
`Λ₂ ∘ f₂`.  If `Λ₁ ∘ Φ₁ ∘ f''` has a canonical orientation `T̂''` for the common family, then
`ϕ₁^* T̂₁ = ϕ₂^* T̂₂` at every smooth point of `X''`. -/
theorem IsCanonicalFor.pullSection_eq_pullSection {Λ₁ : A₁.W → ℚ≥0} {Λ₂ : A₂.W → ℚ≥0}
    (hΛ : ∀ w, Λ₁ (Φ₁.obj w) = Λ₂ (Φ₂.obj w))
    {o₁ : ∀ x (hs : x ∈ A₁.X.PObj.smoothSet), Orx f₁ hF₁.2 x hs}
    {o₂ : ∀ x (hs : x ∈ A₂.X.PObj.smoothSet), Orx f₂ hF₂.2 x hs}
    (ho : h₁.pullOr hF'' hF₁ hpb₁ hsec'' hsec₁ o₁ = h₂.pullOr hF'' hF₂ hpb₂ hsec'' hsec₂ o₂)
    {n₁ n₂ n'' : ℕ} {T₁ : A₁.Obj → A₁.X.PObj.OrTangent →₀ ℚ}
    {T₂ : A₂.Obj → A₂.X.PObj.OrTangent →₀ ℚ} {T'' : A''.Obj → A''.X.PObj.OrTangent →₀ ℚ}
    (hT₁ : IsCanonicalFor Λ₁ hF₁.2 hsec₁ o₁ n₁ T₁) (hT₂ : IsCanonicalFor Λ₂ hF₂.2 hsec₂ o₂ n₂ T₂)
    (hT'' : IsCanonicalFor (fun w => Λ₁ (Φ₁.obj w)) hF''.2 hsec''
      (h₁.pullOr hF'' hF₁ hpb₁ hsec'' hsec₁ o₁) n'' T'') {y : A''.Obj}
    (hys : y ∈ A''.X.PObj.smoothSet) : ϕ₁.pullSection T₁ y = ϕ₂.pullSection T₂ y := by
  have e₂ : (fun w => Λ₁ (Φ₁.obj w)) = fun w => Λ₂ (Φ₂.obj w) := funext hΛ
  have hT₂'' : IsCanonicalFor (fun w => Λ₂ (Φ₂.obj w)) hF''.2 hsec''
      (h₂.pullOr hF'' hF₂ hpb₂ hsec'' hsec₂ o₂) n'' T'' := e₂ ▸ ho ▸ hT''
  rw [← IsCanonicalFor.eq_pullSection h₁ hF'' hF₁ hpb₁ hsec'' hsec₁ hT'' hT₁ hys,
    IsCanonicalFor.eq_pullSection h₂ hF'' hF₂ hpb₂ hsec'' hsec₂ hT₂'' hT₂ hys]

end Diagram

end SBLocalization

end Polyfold
