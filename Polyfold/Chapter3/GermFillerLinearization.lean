import Polyfold.Chapter3.GermCalculus
import Polyfold.Chapter3.FillerLinearization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
Definition 3.4 (3) and Proposition 3.5, **for fillings in the germ sense**.

# The linearization of a germ filling at `0`

## What is formalized

The chart-form identities at `0` for the fill defect `k = [1 − ρ(r(·))]g` of a filling germ
(`IsFillingGerm`): `Dk(0) = (1 − ρ(0))Dg(0)` (`fillDefectDeriv_zero_eq`,
`fillDefect_deriv_zero_eq_rho`), the kernel equivalence of condition (3)
(`IsFillingGerm.exists_kerEquiv`), `Dg(0) ∘ Dr(0)`-identities (`IsFillingGerm.deriv_comp_r_eq_zero`,
`IsFillingGerm.ρ_deriv_comp_r`) and Proposition 3.5 for germs (`IsFillingGerm.proposition_3_5`),
the germ analogues of the whole-chart lemmas of `FillerLinearization.lean`.  Written in
`GermCalculusParam.lean` (Findings, Chapter 3, items 270–274) and placed here, just above
`FillerLinearization.lean`, so that §3.1–§3.6 can use them.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

/-! ### The derivative of the fill defect at `0`, chart form -/

section FillDefectZero

open StrongRetr

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0} {G₁ : ScNbhdGerm E C}

/-- **`Dk(0) = (1 − ρ(0))Dg(0)`** for the explicit derivative family of the fill defect, when
`g(0) = 0` and `0 ∈ O` (`fillDefectDeriv_zero` and `StrongRetr.scDeriv_fiber_zero`). -/
theorem fillDefectDeriv_zero_eq (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {g : E 0 → F 0} (hg0 : g 0 = 0) (Dg : E 1 → E 0 →L[ℝ] F 0) :
    fillDefectDeriv U R g Dg 0 = Dg 0 - (ρCLM hR h0).comp (Dg 0) := by
  rw [fillDefectDeriv_zero hR h0O hg0]
  ext h
  simp only [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
  rw [scDeriv_fiber_zero hU hR h0]

/-- **The germ analogue of `IsFillerOf.scDeriv_sub_eq`**: every derivative family `Dk` of the
sc¹-germ `[1 − ρ(r(·))]g` on `G` has `Dk(0) = (1 − ρ(0))Dg(0)`, for any derivative family `Dg`
of `g` on `G`, when `g(0) = 0` and `0 ∈ O`. -/
theorem fillDefect_deriv_zero_eq_rho (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    (hG : G₁.U 0 ⊆ U) {g : E 0 → F 0} {Dg Dk : E 1 → E 0 →L[ℝ] F 0}
    (hg : IsSc1GermWith G₁ g Dg) (hg0 : g 0 = 0) (hk : IsSc1GermWith G₁ (fillDefect R g) Dk) :
    Dk 0 = Dg 0 - (ρCLM hR h0).comp (Dg 0) := by
  rw [fillDefect_deriv_zero_eq hU hR h0 hG hg hk, fillDefectDeriv_zero_eq hU hR h0 h0O hg0]

/-- **Condition (3) of a filling germ in terms of `Dg(0)`** (the germ analogue of
`IsFillerOf.exists_kerEquiv`): for a filling germ `g` of `f̂` with `g(0) = 0`, `0 ∈ O`, and any
derivative family `Dg` of `g` on a germ `G₁` (no inclusion `G₁ ⊆ U` is needed: the value `Dg(0)`
is computed on `G ∩ G₁`), `(1 − ρ(0))Dg(0)` restricts to a topological isomorphism
`ker Dr(0) → ker ρ(0)`. -/
theorem IsFillingGerm.exists_kerEquiv (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) {fb g : E 0 → F 0}
    (hfg : IsFillingGerm hU hR h0 fb g) (hg0 : g 0 = 0) (h0O : (0 : E 0) ∈ r R '' U)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G₁ g Dg) :
    ∃ Φ : ↥(LinearMap.ker ((scDeriv U (r R) 0 : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0)) ≃L[ℝ]
        ↥(LinearMap.ker ((ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0)),
      ∀ v, ((Φ v : ↥(LinearMap.ker ((ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0))) : F 0) =
        Dg 0 v - ρCLM hR h0 (Dg 0 v) := by
  obtain ⟨G, hGU, -, Dk, hDk, Φ, hΦ⟩ := hfg.germ
  have hG' : (G.inter G₁).U 0 ⊆ U := fun _ hy => hGU hy.1
  have heq := fillDefect_deriv_zero_eq_rho hU hR h0 h0O hG'
    (hg.mono (G.inter_subset_right G₁)) hg0 (hDk.mono (G.inter_subset_left G₁))
  refine ⟨Φ, fun v => ?_⟩
  rw [hΦ v, heq]
  rfl

/-- **`(1 − ρ(0))Dg(0)Dr(0) = 0` for a filling germ** (the germ analogue of
`IsFillerOf.deriv_comp_r_eq_zero`): the identity `[1 − ρ(r(y))]g(r(y)) = 0` near `0` (from
`g = f̂` on `O` and `ρ(x)f̂(x) = f̂(x)` on `O`), linearized at `0` along the germ `r⁻¹(G₁)`. -/
theorem IsFillingGerm.deriv_comp_r_eq_zero (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) {fb g : E 0 → F 0}
    (hfg : IsFillingGerm hU hR h0 fb g) (hg0 : g 0 = 0) (h0O : (0 : E 0) ∈ r R '' U)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) (hG : G₁.U 0 ⊆ U)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G₁ g Dg) (h : E 0) :
    Dg 0 (scDeriv U (r R) 0 h) - ρCLM hR h0 (Dg 0 (scDeriv U (r R) 0 h)) = 0 := by
  have hQ := hU.isPartialQuadrant.isQuadrantLike
  have hr : IsSc1 U (r R) := (hR.baseRetraction hU).isScSmooth.isSc1
  have hr0 : r R 0 = 0 := r_eq_self hR h0O
  have hrC : MapsTo (r R) ((ScNbhdGerm.ofSet hU.relOpen h0).U 0) C := fun u hu =>
    hU.subset_quadrant (r_mem hR hu)
  set k := fillDefect R g with hkdef
  have hDk : IsSc1GermWith G₁ k (fillDefectDeriv U R g Dg) :=
    fillDefect_isSc1GermWith hU hR h0 hG hg
  -- `k ∘ r` on the germ `r⁻¹(G₁)` and its derivative at `0`
  set G' := (ScNbhdGerm.ofSet hU.relOpen h0).preimage G₁ (hr.isSc0.isSc0Germ hU.relOpen h0) hr0 hrC
    with hG'
  have hkr := hDk.comp_preimage hQ hU.relOpen h0 hr hr0 hrC
  have hG'U : ∀ x ∈ G'.U 1, E.toBase 1 x ∈ U := fun x hx => (G'.toBase_mem hx).1
  have h1 := hkr.hasFDerivWithinAt 0 (G'.zero_mem 1)
  rw [levelMap_one_zero_of_zero hr0, fillDefectDeriv_zero_eq hU hR h0 h0O hg0] at h1
  -- `k ∘ r = 0` near `0` in `U`
  have hev : ∀ᶠ y in 𝓝[U] (0 : E 0), (k ∘ r R) y = 0 := by
    have hrc : Tendsto (r R) (𝓝[U] 0) (𝓝 0) := by
      have := hr.isSc0.continuousOn_base 0 h0
      rwa [ContinuousWithinAt, hr0] at this
    have h1 : ∀ᶠ y in 𝓝[U] (0 : E 0), r R y ∈ r R '' U → fb (r R y) = g (r R y) :=
      hrc.eventually hfg.eq_on
    filter_upwards [h1, self_mem_nhdsWithin] with y hy hyU
    have hryO : r R y ∈ r R '' U := ⟨y, hyU, rfl⟩
    have hK := hfK _ hryO
    simp only [Function.comp_apply, hkdef, fillDefect]
    rw [r_r hR hyU, ← hy hryO, ρ_eq_self_of_mem_K hR (r_mem hR hyU) hK, sub_self]
  have hev' : ((k ∘ r R) ∘ E.toBase 1) =ᶠ[𝓝[G'.U 1] (0 : E 1)] fun _ => (0 : F 0) := by
    have ht : Tendsto (E.toBase 1) (𝓝[G'.U 1] (0 : E 1)) (𝓝[U] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h1 : Tendsto (E.toBase 1) (𝓝[G'.U 1] (0 : E 1)) (𝓝 (E.toBase 1 0)) :=
          ((E.toBase 1).continuous.tendsto 0).mono_left nhdsWithin_le_nhds
        rwa [map_zero] at h1
      · exact eventually_nhdsWithin_of_forall hG'U
    exact ht.eventually hev
  have hzero : HasFDerivWithinAt ((k ∘ r R) ∘ E.toBase 1) (0 : E 1 →L[ℝ] F 0) (G'.U 1) 0 := by
    refine (hasFDerivWithinAt_const (0 : F 0) 0 (G'.U 1)).congr_of_eventuallyEq hev' ?_
    simp only [Function.comp_apply, map_zero, hkdef, fillDefect]
    rw [hr0, hg0, hr0, (ρ_isLinear hR h0).map_zero, sub_self]
  have huniq := (G'.uniqueDiffWithinAt hQ 1 (G'.zero_mem 1)).eq h1 hzero
  have hD : (Dg 0 - (ρCLM hR h0).comp (Dg 0)).comp (scDeriv U (r R) 0) = 0 :=
    ContinuousLinearMap.ext_of_toBase_one fun y => by
      have := congrArg (fun T : E 1 →L[ℝ] F 0 => T y) huniq
      simpa using this
  have := congrArg (fun T : E 0 →L[ℝ] F 0 => T h) hD
  simpa using this

/-- `ρ(0)Dg(0)Dr(0) = Dg(0)Dr(0)` for a filling germ (`Tf(0)` takes values in `ρ(0)F`). -/
theorem IsFillingGerm.ρ_deriv_comp_r (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) {fb g : E 0 → F 0}
    (hfg : IsFillingGerm hU hR h0 fb g) (hg0 : g 0 = 0) (h0O : (0 : E 0) ∈ r R '' U)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) (hG : G₁.U 0 ⊆ U)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G₁ g Dg) (h : E 0) :
    ρCLM hR h0 (Dg 0 (scDeriv U (r R) 0 h)) = Dg 0 (scDeriv U (r R) 0 h) :=
  (sub_eq_zero.1 (hfg.deriv_comp_r_eq_zero hU hR h0 hg0 h0O hfK hG hg h)).symm

/-- **Proposition 3.5 (Filler) for a filling germ**: for a filling germ `g` of `f̂` with `g(0) = 0`
(`f̂` a section of `K → O`) and any derivative family `Dg` of `g` on a germ `G₁ ⊆ U`, the
restriction `Tf(0) = Dg(0)|_{Dr(0)E} : Dr(0)E → ρ(0)F` (`fillerRestrict`) is surjective iff
`Dg(0)` is, and Fredholm iff `Dg(0)` is, with the same index (the germ analogue of
`IsFillerOf.proposition_3_5`). -/
theorem IsFillingGerm.proposition_3_5 (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) {fb g : E 0 → F 0}
    (hfg : IsFillingGerm hU hR h0 fb g) (hg0 : g 0 = 0) (h0O : (0 : E 0) ∈ r R '' U)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) (hG : G₁.U 0 ⊆ U)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G₁ g Dg) :
    ∃ h1 : ∀ x, ρCLM hR h0 (Dg 0 (scDeriv U (r R) 0 x)) = Dg 0 (scDeriv U (r R) 0 x),
      (Surjective (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1) ↔
          Surjective (Dg 0)) ∧
        (IsFredholm (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1) ↔
          IsFredholm (Dg 0)) ∧
        fredholmIndex (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1) =
          fredholmIndex (Dg 0) := by
  obtain ⟨Φ, hΦ⟩ := hfg.exists_kerEquiv hU hR h0 hg0 h0O hg
  exact ⟨hfg.ρ_deriv_comp_r hU hR h0 hg0 h0O hfK hG hg, Polyfold.proposition_3_5
    (scDeriv_r_idem hU hR h0O) (ρCLM_idem hR h0 h0O) _ Φ hΦ⟩

end FillDefectZero

end Polyfold
