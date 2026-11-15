import Polyfold.Chapter15.KernelBranchingIndex
import Polyfold.Chapter15.LinearizationLocalIso
import Polyfold.Chapter12.OrientationNaturality

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702, **Theorem 15.4.1** (2017: Theorem 15.6): the canonical lift is a section functor of
`Ĝr(X)`.

# The formula of Theorem 15.4.1 is carried by morphisms

## The text, paraphrased

(p. 702) `T̂_((f, o), Λ)` is a section functor of `Ĝr(X) → X_∞`: for a morphism `φ : y → y'`,
`Tφ` maps `∑ σᵢ · (ker (f − sᵢ)'(y), o_{i,y})` to the corresponding sum at `y'`.  The text gives
no separate argument; it rests on the functor property of `T(f, Λ)` (Theorem 15.1.1) and the
invariance `φ_* o_y = o_{y'}` of the orientation (Definition 12.5.4).

## What is formalized (namespace `Polyfold.SBLocalization`)

* `carriedPt`: the chart point at `t(φ)` carried from a chart point at `s(φ)` by the local strong
  bundle isomorphism of `φ`; `subOp_carriedPt`: `(f − s)'` read in a chart point at `s(φ)` is
  `(f − φ_*s)'` read in the carried chart point, for a section functor `f`.
* `chartVec_tangentMor`, `exists_tangentMor_eq`: `Tφ` is the identity of the chart vectors in
  the two chart points, and maps `T_{s(φ)}X` onto `T_{t(φ)}X`.
* `linOrTangent_carriedPt`: the oriented kernel `(ker L, o(L))` read in the carried chart point
  for the carried orientation is the image under `Tφ` of the one read in the chart point.
* `orPull_toChartOr`: for an invariant family `o` (Definition 12.5.4), `o_{t(φ)}` read in the
  carried chart point is the orientation carried from `o_{s(φ)}`.
* **`canonNatural`**: `CanonNatural`, the naturality of the formula of Theorem 15.4.1, for an
  sc-Fredholm section functor `f`, an sc⁺-multisection `Λ` and an invariant family `o`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}} {f : A.Obj → A.W} {φ : A.Mor}

/-! ### The carried chart point -/

/-- **The chart point at `t(φ)` carried from a chart point at `s(φ)`** with domain in the source
set of the sheet of `φ`, by the local strong bundle isomorphism of `φ`. -/
abbrev carriedPt (a : ChartPoint A.B (A.X.src φ))
    (ha : a.c.φ.source ⊆ (A.X.sheetAt φ).srcSet) : ChartPoint A.B (A.X.tgt φ) :=
  (A.E.morIso φ).pullPt a ha (EpStrongBundle.mem_tgtSet rfl) (A.E.morIso_ϕ_eq rfl rfl)

/-- **`(f − s)'(s φ)` and `(f − φ_*s)'(t φ)` are the same operator** in a chart point and its
carried chart point, for a section functor `f` and a local sc⁺-section `s`. -/
theorem subOp_carriedPt (hF : A.E.IsScFredholmSectionFunctor f) {s : A.Obj → A.W}
    {O : Set A.Obj} (hs : IsScPlusSectionOn A s O) {s' : A.Obj → A.W} {O' : Set A.Obj}
    (hs' : IsScPlusSectionOn A s' O') (hss' : s' = transSec φ s)
    (a : ChartPoint A.B (A.X.src φ))
    (ha : a.c.φ.source ⊆ (A.X.sheetAt φ).srcSet) (hsub : a.c.φ.source ⊆ O)
    (hsub' : (carriedPt a ha).c.φ.source ⊆ O') (hfs : f (A.X.src φ) = s (A.X.src φ))
    (hfs' : f (A.X.tgt φ) = s' (A.X.tgt φ)) (v : ↥a.T) :
    ((subOp hF.2.isScSmooth hs' (carriedPt a ha) hsub' hfs' v).1 : a.c.F 0) =
      (subOp hF.2.isScSmooth hs a hsub hfs v).1 := by
  subst hss'
  have hfL : EqOn f ((A.E.morIso φ).Ψ ∘ f ∘ (A.E.morIso φ).ϕ) (A.X.sheetAt φ).tgtSet :=
    A.E.eqOn_morIso φ hF.1.1.1 hF.1.2
  exact congrArg (fun M : a.c.φ.model.E 0 →L[ℝ] a.c.F 0 => M v.1)
    (subDeriv_transportChart (A.E.morIso φ) (hsub := ha) hF.1.1 hfL hs a.isChart hsub a.mem_U)

/-! ### `Tφ` in the chart point and the carried chart point -/

/-- **`Tφ` is the identity of the chart vectors** of a chart `c` at `s(φ)` and the carried chart
at `t(φ)`, and maps `T_{s(φ)}X` into `T_{t(φ)}X`. -/
theorem chartVec_tangentMor {c : StrongBundleChart A.X.PObj A.P}
    (hsub : c.φ.source ⊆ (A.X.sheetAt φ).srcSet) (hxc : A.X.src φ ∈ c.φ.source)
    (hys' : A.X.tgt φ ∈ A.X.PObj.levelSet 1) {α : A.X.PObj.TangentSpace}
    (hα : A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = A.X.src φ) :
    A.X.PObj.levelVal 1 (A.X.PObj.tangentProj (A.X.tangentMor φ α)) = A.X.tgt φ ∧
      chartVec ((A.E.morIso φ).transportChart c hsub).isChart (A.X.tangentMor φ α) =
        chartVec c.isChart α := by
  set x₁ : A.X.PObj.Level 1 := A.X.PObj.tangentProj α with hx₁
  set y₁ : A.X.PObj.Level 1 := ⟨A.X.tgt φ, hys'⟩ with hy₁
  have hy : A.X.PObj.levelVal 1 y₁ = A.X.tgt φ := rfl
  have hφ1 := mem_levelSet_one_of_src (A := A) (φ := φ) (x := x₁) hα
  have hx' : A.X.PObj.levelVal 1 x₁ ∈ c.φ.source := hα ▸ hxc
  have hy' : A.X.PObj.levelVal 1 y₁ ∈ ((A.E.morIso φ).transportChart c hsub).φ.source := by
    refine ⟨A.X.tgt_mem_sheetAt φ, ?_⟩
    change (A.E.morIso φ).ϕ (A.X.tgt φ) ∈ c.φ.source
    rw [EpStrongBundle.morIso_ϕ_tgt]; exact hxc
  set β : A.X.PObj.tangentFiber x₁ := ⟨α, rfl⟩ with hβ
  have h1 := chartVec_transport hφ1 hα hy hsub hx' hy' β
  have h2 : (A.X.tangentMorCLE hφ1 hα hy β : A.X.PObj.TangentSpace) = A.X.tangentMor φ α :=
    A.X.tangentMorCLE_apply hφ1 hα hy β
  refine ⟨?_, ?_⟩
  · rw [← h2]
    exact congrArg (A.X.PObj.levelVal 1) (A.X.tangentMorCLE hφ1 hα hy β).2
  · rw [← h2]
    exact h1

/-- **`Tφ` maps `T_{s(φ)}X` onto `T_{t(φ)}X`** (Chapter 7: `Tφ` is a linear isomorphism of the
fibres). -/
theorem exists_tangentMor_eq (hxs : A.X.src φ ∈ A.X.PObj.levelSet 1)
    {α' : A.X.PObj.TangentSpace}
    (hα' : A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α') = A.X.tgt φ) :
    ∃ α : A.X.PObj.TangentSpace, A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = A.X.src φ ∧
      A.X.tangentMor φ α = α' := by
  set x₁ : A.X.PObj.Level 1 := ⟨A.X.src φ, hxs⟩ with hx₁
  set y₁ : A.X.PObj.Level 1 := A.X.PObj.tangentProj α' with hy₁
  have hx : A.X.PObj.levelVal 1 x₁ = A.X.src φ := rfl
  have hφ1 := mem_levelSet_one_of_src (A := A) (φ := φ) (x := x₁) hx
  set β' : A.X.PObj.tangentFiber y₁ := ⟨α', rfl⟩ with hβ'
  refine ⟨((A.X.tangentMorCLE hφ1 hx hα').symm β' : A.X.PObj.TangentSpace), ?_, ?_⟩
  · exact congrArg (A.X.PObj.levelVal 1) ((A.X.tangentMorCLE hφ1 hx hα').symm β').2
  · have h := A.X.tangentMorCLE_apply hφ1 hx hα' ((A.X.tangentMorCLE hφ1 hx hα').symm β')
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    exact h.symm

/-! ### The oriented kernel under a conjugation -/

theorem orTangent_mk_ext {n : ℕ} {C C' : Set A.X.PObj.TangentSpace}
    {F F' : Set (Fin n → A.X.PObj.TangentSpace)} (hC : C = C') (hF : F = F') :
    (⟨n, C, F⟩ : A.X.PObj.OrTangent) = ⟨n, C', F'⟩ := by
  subst hC; subst hF; rfl

set_option maxHeartbeats 800000 in
-- One long proof with the two kernels, their frames and the orientation of each.
open Classical in
/-- **The oriented kernel is carried by a conjugation**: let `a`, `a'` be chart points at `y`,
`y'`, `A : T_zO ≅ T_{z'}O'`, `Γ : K_z ≅ K_{z'}` and `D : E₀ ≅ E₀'` with `A = D` on `T_zO`, and
let `τ` map `T_yX` onto `T_{y'}X` with `D` as its expression in the chart vectors.  For
`L ∈ Lin(f, y)`, `L' ∈ Lin(f, y')` with `L' A = Γ L`, the oriented tangent set `(ker L', o'(L'))`
for the conjugated orientation `o'` is the image under `τ` of `(ker L, o(L))`. -/
theorem linOrTangent_conj {y y' : A.Obj} (hf : A.B.IsScFredholmSection f)
    (a : ChartPoint A.B y) (a' : ChartPoint A.B y')
    (τ : A.X.PObj.TangentSpace → A.X.PObj.TangentSpace) (AT : ↥a.T ≃L[ℝ] ↥a'.T)
    (AK : ↥a.K ≃L[ℝ] ↥a'.K) (D : a.c.φ.model.E 0 ≃L[ℝ] a'.c.φ.model.E 0)
    (hD : ∀ v : ↥a.T, ((AT v : ↥a'.T) : a'.c.φ.model.E 0) = D (v : a.c.φ.model.E 0))
    (hτ : ∀ α, A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = y →
      A.X.PObj.levelVal 1 (A.X.PObj.tangentProj (τ α)) = y' ∧
        chartVec a'.c.isChart (τ α) = D (chartVec a.c.isChart α))
    (hτs : ∀ α', A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α') = y' →
      ∃ α, A.X.PObj.levelVal 1 (A.X.PObj.tangentProj α) = y ∧ τ α = α')
    (hmem : ∀ S' ∈ a'.linSet f, ((AK.symm : ↥a'.K →L[ℝ] ↥a.K) ∘L S' ∘L
      (AT : ↥a.T →L[ℝ] ↥a'.T)) ∈ a.linSet f)
    (o : a.Or f hf) {S : ↥a.T →L[ℝ] ↥a.K} (hS : S ∈ a.linSet f) {S' : ↥a'.T →L[ℝ] ↥a'.K}
    (hS' : S' ∈ a'.linSet f) (hconj : ∀ v, S' (AT v) = AK (S v)) :
    linOrTangent hf a' (o.conj (hC' := a'.isFredholm_of_mem_linSet hf) AT AK hmem) ⟨S', hS'⟩ =
      (linOrTangent hf a o ⟨S, hS⟩).push τ := by
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
    have hfin' := a'.finiteDimensional_of_mem_linSet hf hS' rfl
    set κ := conjKerEquivOfMap AT AK hconj a.T.subtypeL Subtype.val_injective rfl a'.T.subtypeL
      Subtype.val_injective rfl with hκdef
    have hκ : ∀ v, ((κ v : _) : a'.c.φ.model.E 0) = D (v : a.c.φ.model.E 0) := fun v => by
      obtain ⟨w, rfl⟩ := (kerEquivOfMap S a.T.subtypeL Subtype.val_injective rfl).surjective v
      exact (coe_conjKerEquivOfMap _ _ hconj _ _ rfl _ _ rfl w).trans (hD w.1)
    obtain ⟨n, hn⟩ : ∃ n, finrank ℝ ↥((LinearMap.ker (S : ↥a.T →ₗ[ℝ] ↥a.K)).map
      (a.T.subtypeL : ↥a.T →ₗ[ℝ] a.c.φ.model.E 0)) = n := ⟨_, rfl⟩
    have hn' : finrank ℝ ↥((LinearMap.ker (S' : ↥a'.T →ₗ[ℝ] ↥a'.K)).map
        (a'.T.subtypeL : ↥a'.T →ₗ[ℝ] a'.c.φ.model.E 0)) = n := κ.finrank_eq.symm.trans hn
    have hray : a'.orKer (hf := hf) (o.conj (hC' := a'.isFredholm_of_mem_linSet hf) AT AK hmem)
        hS' h' rfl = Module.Ray.map (maxPowEquiv κ) (a.orKer o hS h rfl) :=
      (congrArg (surjRay h' a'.T.subtypeL Subtype.val_injective rfl)
        (LineOrientation.conj_apply (hC' := a'.isFredholm_of_mem_linSet hf) AT AK hmem o hS hS'
          hconj)).trans (surjRay_conjDet _ _ h h' hconj _ _ rfl _ _ rfl _)
    have e1 : linOrTangent hf a o ⟨S, hS⟩ = _ :=
      (dif_pos h).trans (orTangent_mk_congr hf a o hS h hn rfl).symm
    have e2 : linOrTangent hf a' (o.conj (hC' := a'.isFredholm_of_mem_linSet hf) AT AK hmem)
        ⟨S', hS'⟩ = _ := (dif_pos h').trans (orTangent_mk_congr hf a' _ hS' h' hn' rfl).symm
    rw [e1, e2]
    refine orTangent_mk_ext ?_ ?_
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
          (a'.orKer (hf := hf) (o.conj (hC' := a'.isFredholm_of_mem_linSet hf) AT AK hmem) hS'
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
    have e2 : linOrTangent hf a' (o.conj (hC' := a'.isFredholm_of_mem_linSet hf) AT AK hmem)
        ⟨S', hS'⟩ = ⟨0, ∅, ∅⟩ := dif_neg (mt hsurj_iff.1 h)
    rw [e1, e2]
    exact orTangent_mk_ext (image_empty _).symm (image_empty _).symm

/-! ### The carried chart point -/

set_option maxHeartbeats 1000000 in
-- The types of the carried chart point unfold to those of the chart point.
/-- **The oriented kernel is carried by `Tφ`**: for `L ∈ Lin(f, s φ)`, the oriented tangent set
`(ker L, o(L))` read in the carried chart point at `t(φ)`, for the carried orientation, is the
image under `Tφ` of the one read in the chart point at `s(φ)`. -/
theorem linOrTangent_carriedPt (hf : A.B.IsScFredholmSection f)
    (a : ChartPoint A.B (A.X.src φ)) (ha : a.c.φ.source ⊆ (A.X.sheetAt φ).srcSet)
    (hlin : (carriedPt a ha).linSet f = a.linSet f) (hys : A.X.src φ ∈ A.X.PObj.levelSet 1)
    (hys' : A.X.tgt φ ∈ A.X.PObj.levelSet 1) (o : a.Or f hf) {S : ↥a.T →L[ℝ] ↥a.K}
    (hS : S ∈ a.linSet f) {S' : ↥(carriedPt a ha).T →L[ℝ] ↥(carriedPt a ha).K}
    (hS' : S' ∈ (carriedPt a ha).linSet f)
    (hSS : ∀ v : ↥a.T, ((S' v).1 : a.c.F 0) = (S v).1) :
    linOrTangent hf (carriedPt a ha)
        ((A.E.morIso φ).orPull hf a ha (EpStrongBundle.mem_tgtSet rfl)
          (A.E.morIso_ϕ_eq rfl rfl) hlin o) ⟨S', hS'⟩ =
      (linOrTangent hf a o ⟨S, hS⟩).push (A.X.tangentMor φ) :=
  linOrTangent_conj hf a (carriedPt a ha) (A.X.tangentMor φ)
    ((A.E.morIso φ).castT a ha (EpStrongBundle.mem_tgtSet rfl) (A.E.morIso_ϕ_eq rfl rfl))
    ((A.E.morIso φ).castK a ha (EpStrongBundle.mem_tgtSet rfl) (A.E.morIso_ϕ_eq rfl rfl))
    (ContinuousLinearEquiv.refl ℝ (a.c.φ.model.E 0)) (fun _ => rfl)
    (fun _ hα => chartVec_tangentMor ha a.mem_source hys' hα)
    (fun _ hα' => exists_tangentMor_eq hys hα') (StrongBundle.LocalIso.castT_mem hlin) o hS hS'
    (fun v => Subtype.ext (hSS v))

open Classical in
/-- **The formal sum of oriented kernels is carried by `Tφ`**: for a section functor `f`, a
local sc⁺-section structure `(sᵢ, σᵢ)` of `Λ` on `O` in the source set of the sheet of `φ` and
the carried structure `(φ_*sᵢ, σᵢ)`, the image of `∑ σᵢ · (f − φ_*sᵢ)'(t φ)` under
`L ↦ (ker L, o'(L))` in the carried chart point is the image under `Tφ` of the corresponding
sum at `s(φ)`. -/
theorem mapDomain_linW_carriedPt (hF : A.E.IsScFredholmSectionFunctor f)
    (hsec : A.B.HasScPlusSectionsThrough) {Λ : A.W → ℚ≥0} {O : Set A.Obj} (hO : IsOpen O)
    {k : ℕ} {sb : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0}
    (hrep : IsLocalRepOn A Λ O sb σ)
    (hrep' : IsLocalRepOn A Λ (transSet φ O) (fun i => transSec φ (sb i)) σ)
    (a : ChartPoint A.B (A.X.src φ)) (ha : a.c.φ.source ⊆ (A.X.sheetAt φ).srcSet)
    (hsub : a.c.φ.source ⊆ O) (hsub' : (carriedPt a ha).c.φ.source ⊆ transSet φ O)
    (hys : A.X.src φ ∈ A.X.PObj.smoothSet) (hys' : A.X.tgt φ ∈ A.X.PObj.smoothSet)
    (hlin : (carriedPt a ha).linSet f = a.linSet f) (o : a.Or f hF.2) :
    (linW hF.2 (isOpen_transSet φ hO) hrep' (carriedPt a ha) hsub' hys' hsec).mapDomain
        (linOrTangent hF.2 (carriedPt a ha)
          ((A.E.morIso φ).orPull hF.2 a ha (EpStrongBundle.mem_tgtSet rfl)
            (A.E.morIso_ϕ_eq rfl rfl) hlin o)) =
      (linW hF.2 hO hrep a hsub hys hsec).mapDomain
        (fun L => (linOrTangent hF.2 a o L).push (A.X.tangentMor φ)) := by
  set L := A.E.morIso φ with hL
  have hfL : EqOn f (L.Ψ ∘ f ∘ L.ϕ) (A.X.sheetAt φ).tgtSet :=
    A.E.eqOn_morIso φ hF.1.1.1 hF.1.2
  have hϕ : L.ϕ (A.X.tgt φ) = A.X.src φ := A.E.morIso_ϕ_tgt φ
  have hxO : A.X.src φ ∈ O := hsub a.mem_source
  have hcond : ∀ i, transSec φ (sb i) (A.X.tgt φ) = f (A.X.tgt φ) ↔
      sb i (A.X.src φ) = f (A.X.src φ) := fun i => by
    have e1 : transSec φ (sb i) (A.X.tgt φ) = L.Ψ (sb i (A.X.src φ)) := by
      change L.Ψ (sb i (L.ϕ (A.X.tgt φ))) = _
      rw [hϕ]
    have e2 : f (A.X.tgt φ) = L.Ψ (f (A.X.src φ)) := by
      have := hfL (A.X.tgt_mem_sheetAt φ)
      simp only [Function.comp_apply] at this
      rw [this, hϕ]
    rw [e1, e2]
    constructor
    · intro h
      have h1 := congrArg L.Φ h
      rwa [L.zero.right_inv _ (show A.P (sb i (A.X.src φ)) ∈ _ by
          rw [(hrep.2.1 i).1 _ hxO]; exact A.X.src_mem_sheetAt φ),
        L.zero.right_inv _ (show A.P (f (A.X.src φ)) ∈ _ by
          rw [hF.1.1.1 (A.X.src φ)]; exact A.X.src_mem_sheetAt φ)] at h1
    · intro h
      rw [h]
  unfold linW
  rw [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : sb i (A.X.src φ) = f (A.X.src φ)
  · rw [dif_pos h, dif_pos ((hcond i).2 h), Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    exact congrArg (fun g => Finsupp.single g (σ i))
      (linOrTangent_carriedPt hF.2 a ha hlin (smoothSet_subset_levelSet 1 hys)
        (smoothSet_subset_levelSet 1 hys') o _ _
        (subOp_carriedPt hF (hrep.2.1 i) (hrep'.2.1 i) rfl a ha hsub hsub' h.symm
          ((hcond i).2 h).symm))
  · rw [dif_neg h, dif_neg (mt (hcond i).1 h), Finsupp.mapDomain_zero, Finsupp.mapDomain_zero]

/-! ### An invariant orientation in the carried chart point -/

/-- **`o_{t(φ)}` read in the carried chart point is the orientation carried from `o_{s(φ)}`**, for
a family `o` invariant under the morphisms (Definition 12.5.4). -/
theorem orTransfer_carriedPt (hF : A.E.IsScFredholmSectionFunctor f)
    (hsec : A.B.HasScPlusSectionsThrough)
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy} (hinv : A.E.IsOrInvariant hF hsec o)
    (a : ChartPoint A.B (A.X.src φ)) (ha : a.c.φ.source ⊆ (A.X.sheetAt φ).srcSet)
    (hys : A.X.src φ ∈ A.X.PObj.smoothSet) (hys' : A.X.tgt φ ∈ A.X.PObj.smoothSet)
    (hlin : (carriedPt a ha).linSet f = a.linSet f) :
    (orPt A.B (A.X.tgt φ) hys').orTransfer (carriedPt a ha) hF.2 hys' (o _ hys') =
      (A.E.morIso φ).orPull hF.2 a ha (EpStrongBundle.mem_tgtSet rfl) (A.E.morIso_ϕ_eq rfl rfl)
        hlin ((orPt A.B (A.X.src φ) hys).orTransfer a hF.2 hys (o _ hys)) := by
  rw [← hinv φ rfl rfl hys hys']
  have h2 : A.E.orMor hF hsec φ rfl rfl hys hys' =
      (A.E.morIso φ).orVia hF.2 (orPt A.B _ hys) (orPt A.B _ hys') a ha
        (EpStrongBundle.mem_tgtSet rfl) (A.E.morIso_ϕ_eq rfl rfl) hlin hys hys' :=
    (A.E.morIso φ).orVia_eq hF.2 _ _ _ ha _ _ _ hlin hys hys'
  rw [h2]
  exact DFunLike.congr_fun ((ChartPoint.orTransfer_trans (carriedPt a ha)
    (orPt A.B _ hys') (carriedPt a ha) hF.2 hys').trans
      (ChartPoint.orTransfer_self _ hF.2 hys')) _

/-- The chart point of Part I in the carried chart is the carried chart point. -/
theorem chartPtOf_transportChart_eq {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hsub : c.φ.source ⊆ (A.X.sheetAt φ).srcSet) (hyc : A.X.src φ ∈ c.φ.source)
    (hys : A.X.src φ ∈ A.X.PObj.smoothSet) (hys' : A.X.tgt φ ∈ A.X.PObj.smoothSet)
    (hc' : A.B.IsChart ((A.E.morIso φ).transportChart c hsub))
    (hyc' : A.X.tgt φ ∈ ((A.E.morIso φ).transportChart c hsub).φ.source) :
    chartPtOf ((A.E.morIso φ).transportChart c hsub) hc' hyc' hys' =
      carriedPt (chartPtOf c hc hyc hys) hsub := by
  have hz : (exists_lift_of_smooth ((A.E.morIso φ).transportChart c hsub) hyc' hys').choose =
      (exists_lift_of_smooth c hyc hys).choose := by
    refine c.φ.model.E.toBase_injective 1
      ((exists_lift_of_smooth ((A.E.morIso φ).transportChart c hsub) hyc' hys').choose_spec.trans
        (Eq.trans ?_ (exists_lift_of_smooth c hyc hys).choose_spec.symm))
    change c.φ ((A.E.morIso φ).ϕ (A.X.tgt φ)) = c.φ (A.X.src φ)
    rw [EpStrongBundle.morIso_ϕ_tgt]
  unfold carriedPt chartPtOf chartPt StrongBundle.LocalIso.pullPt
  congr 1

open Classical in
/-- **The formal sum of oriented kernels at `t(φ)` for an invariant orientation**, in a chart
point equal to the carried chart point: it is the image under `Tφ` of the sum at `s(φ)`. -/
theorem mapDomain_linW_of_eq_carriedPt (hF : A.E.IsScFredholmSectionFunctor f)
    (hsec : A.B.HasScPlusSectionsThrough)
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy} (hinv : A.E.IsOrInvariant hF hsec o)
    {Λ : A.W → ℚ≥0} {O : Set A.Obj} (hO : IsOpen O) {k : ℕ} {sb : Fin k → A.Obj → A.W}
    {σ : Fin k → ℚ≥0} (hrep : IsLocalRepOn A Λ O sb σ)
    (hrep' : IsLocalRepOn A Λ (transSet φ O) (fun i => transSec φ (sb i)) σ)
    (a : ChartPoint A.B (A.X.src φ)) (ha : a.c.φ.source ⊆ (A.X.sheetAt φ).srcSet)
    (hsub : a.c.φ.source ⊆ O) (hys : A.X.src φ ∈ A.X.PObj.smoothSet)
    (hys' : A.X.tgt φ ∈ A.X.PObj.smoothSet) (q : ChartPoint A.B (A.X.tgt φ))
    (hq : q = carriedPt a ha) (hsubq : q.c.φ.source ⊆ transSet φ O) :
    (linW hF.2 (isOpen_transSet φ hO) hrep' q hsubq hys' hsec).mapDomain
        (linOrTangent hF.2 q ((orPt A.B _ hys').orTransfer q hF.2 hys' (o _ hys'))) =
      (linW hF.2 hO hrep a hsub hys hsec).mapDomain
        (fun L => (linOrTangent hF.2 a ((orPt A.B _ hys).orTransfer a hF.2 hys (o _ hys))
          L).push (A.X.tangentMor φ)) := by
  subst hq
  have hlin : (carriedPt a ha).linSet f = a.linSet f :=
    A.E.linSet_pullPt_mor hF hsec φ rfl rfl a ha hys hys'
  rw [orTransfer_carriedPt hF hsec hinv a ha hys hys' hlin]
  exact mapDomain_linW_carriedPt hF hsec hO hrep hrep' a ha hsub hsubq hys hys' hlin _

/-! ### Naturality -/

/-- **Theorem 15.4.1 (2021 p. 702; 2017: Theorem 15.6), the functor property in `Ĝr(X)`**: for
an sc-Fredholm section functor `f`, an sc⁺-multisection `Λ` and a family `o_y ∈ Or_y^f`
invariant under the morphisms (Definition 12.5.4), the formula
`∑ σᵢ · (T_yMᵢ, o_{i,y})` is carried by morphisms: `Tφ` maps the sum at `s(φ)` to the sum at
`t(φ)`, for all local branching structures described by kernels around the two points. -/
theorem canonNatural (Λ : A.W → ℚ≥0) (hF : A.E.IsScFredholmSectionFunctor f)
    (hΛ : IsScPlusMultisection A Λ) (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hinv : A.E.IsOrInvariant hF hsec o) : CanonNatural Λ hF.2 hsec o := by
  classical
  intro φ hys x x' K K' hyU hyU'
  have hys' : A.X.tgt φ ∈ A.X.PObj.smoothSet :=
    (A.X.mem_smoothSet_tgt_iff φ).2 ((A.X.mem_smoothSet_src_iff φ).1 hys)
  set L := A.E.morIso φ with hLdef
  have hG : IsOpen ((A.X.sheetAt φ).srcSet ∩ L.g ⁻¹' K'.O) :=
    L.base.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage L.isOpen_U' K'.isOpen_O
  have hV : IsOpen (K.O ∩ ((A.X.sheetAt φ).srcSet ∩ L.g ⁻¹' K'.O)) := K.isOpen_O.inter hG
  have hgy : L.g (A.X.src φ) = A.X.tgt φ := by
    rw [← A.E.morIso_ϕ_tgt φ]; exact L.base.left_inv _ (A.X.tgt_mem_sheetAt φ)
  have hyV : A.X.src φ ∈ K.O ∩ ((A.X.sheetAt φ).srcSet ∩ L.g ⁻¹' K'.O) :=
    ⟨K.U_subset hyU, A.X.src_mem_sheetAt φ, by rw [mem_preimage, hgy]; exact K'.U_subset hyU'⟩
  set c := (orChart A.B (A.X.src φ)).restrictInter hV with hcdef
  have hc : A.B.IsChart c := StrongBundle.IsChart.restrictInter hV (isChart_orChart (B := A.B) _)
  have hyc : A.X.src φ ∈ c.φ.source :=
    StrongBundleChart.mem_restrictInter_source _ hV (mem_orChart _) hyV
  have hcV : c.φ.source ⊆ K.O ∩ ((A.X.sheetAt φ).srcSet ∩ L.g ⁻¹' K'.O) :=
    StrongBundleChart.restrictInter_source_subset (orChart A.B (A.X.src φ)) hV
  have hsubK : c.φ.source ⊆ K.O := fun z hz => (hcV hz).1
  have hsubS : c.φ.source ⊆ (A.X.sheetAt φ).srcSet := fun z hz => (hcV hz).2.1
  have hO₁ : IsOpen (K.O ∩ (A.X.sheetAt φ).srcSet) := K.isOpen_O.inter L.isOpen_U'
  have hrep₁ : IsLocalRepOn A Λ (K.O ∩ (A.X.sheetAt φ).srcSet) K.sAll K.σAll :=
    K.isLocalRep.mono hO₁ inter_subset_left
  have hrep' := isLocalRepOn_transSec hΛ.1 hO₁ inter_subset_right hrep₁
  have hsub₁ : c.φ.source ⊆ K.O ∩ (A.X.sheetAt φ).srcSet := fun z hz => ⟨hsubK hz, hsubS hz⟩
  have hc' : A.B.IsChart (L.transportChart c hsubS) := L.isChart_transportChart c hsubS hc
  have hyc' : A.X.tgt φ ∈ (L.transportChart c hsubS).φ.source := by
    refine ⟨A.X.tgt_mem_sheetAt φ, ?_⟩
    change L.ϕ (A.X.tgt φ) ∈ c.φ.source
    rw [EpStrongBundle.morIso_ϕ_tgt]; exact hyc
  have hsub' : (L.transportChart c hsubS).φ.source ⊆
      transSet φ (K.O ∩ (A.X.sheetAt φ).srcSet) := fun z hz => ⟨hz.1, hsub₁ hz.2⟩
  have hsubK' : (L.transportChart c hsubS).φ.source ⊆ K'.O := fun z hz => by
    have h1 : L.g (L.ϕ z) ∈ K'.O := (hcV hz.2).2.2
    rwa [L.base.left_inv z hz.1] at h1
  have e1 : K.canonSum hF.2 hsec o (A.X.src φ) =
      Finsupp.mapRange ((↑) : ℚ≥0 → ℚ) NNRat.cast_zero
        ((linW hF.2 hO₁ hrep₁ (chartPtOf c hc hyc hys) hsub₁ hys hsec).mapDomain
          (linOrTangent hF.2 (chartPtOf c hc hyc hys)
            (toChartOr hF.2 hys c hc hyc (o _ hys)))) := Finsupp.ext fun g => by
    rw [Finsupp.mapRange_apply, K.canonSum_apply_eq hF.2 hsec o hyU hys hc hyc hsubK g,
      linW_chartPtOf_eq hF.2 K.isOpen_O hO₁ K.isLocalRep hrep₁ hys hsec hc hyc hsubK hsub₁]
  have e2 : K'.canonSum hF.2 hsec o (A.X.tgt φ) =
      Finsupp.mapRange ((↑) : ℚ≥0 → ℚ) NNRat.cast_zero
        ((linW hF.2 (isOpen_transSet φ hO₁) hrep'
            (chartPtOf (L.transportChart c hsubS) hc' hyc' hys') hsub' hys' hsec).mapDomain
          (linOrTangent hF.2 (chartPtOf (L.transportChart c hsubS) hc' hyc' hys')
            (toChartOr hF.2 hys' (L.transportChart c hsubS) hc' hyc' (o _ hys')))) :=
    Finsupp.ext fun g => by
      rw [Finsupp.mapRange_apply, K'.canonSum_apply_eq hF.2 hsec o hyU' hys' hc' hyc' hsubK' g,
        linW_chartPtOf_eq hF.2 K'.isOpen_O (isOpen_transSet φ hO₁) K'.isLocalRep hrep' hys' hsec
          hc' hyc' hsubK' hsub']
  rw [e1, e2, grHatPush, Finsupp.mapDomain_mapRange _ _ _ _ (fun x y => NNRat.cast_add x y),
    ← Finsupp.mapDomain_comp]
  congr 1
  exact (mapDomain_linW_of_eq_carriedPt hF hsec hinv hO₁ hrep₁ hrep' (chartPtOf c hc hyc hys)
    hsubS hsub₁ hys hys' _ (chartPtOf_transportChart_eq hc hsubS hyc hys hys' hc' hyc')
    hsub').symm

end SBLocalization

end Polyfold
