import Polyfold.Chapter5.Theorem5315_Morse

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.3, the local data of
**Theorem 5.3.15** (p. 223; preprint: Theorem 5.22) from the implicit function theorem
(Theorem 3.6.8, p. 136), first step.  Gap G.48.

# A smooth parametrization from the data of Definition 3.2.1

## The text, paraphrased

(Definition 3.2.1, Theorem 3.6.8) Near a zero in good position the solution set is, in a chart,
the graph `{v + δ(v) | v ∈ V}` of an sc-smooth germ `δ` over a relatively open subset `V` of a
partial quadrant of the finite-dimensional kernel `N`.

## What is formalized

* `MPolyfold.TangentGermChart.exists_isSmoothParam`: for regular data `D` of Definition 3.2.1 at
  `x ∈ M` (`TangentGermChart`, `IsRegular`) and sc-smooth bump functions, the map
  `v ↦ D.φ⁻¹(v + δ(v))` is a smooth parametrization (`MPolyfold.IsSmoothParam`) of `M` around `x`
  on `Ω = V ∩ OE`, `OE` open in `N`, `0 ∈ Ω`, with left inverse `q = β · (π ∘ D.φ)` (`β` a bump
  function, `π` the projection onto `N`).

## Done elsewhere (2026-11-12)

* The identification of the tangent vectors of a parametrization with the kernel of the
  linearization is `StrongBundle.exists_fderivWithin_eq_scDeriv_of_mem_linKer`
  (`Theorem5315_LocalTangent.lean`), and (A1)–(A3) of `StrongBundle.HasMorseLocalData` are
  `StrongBundle.hasMorseLocalData` (`Theorem5315_LocalData.lean`).
-/

open Set Function Module Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {M : Set X} {x : X} {n : ℕ}

open scoped Classical in
/-- **The parametrization of Definition 3.2.1 is a smooth parametrization**: for regular data
`D` at `x` (the solution set as a graph over `V ⊆ N`) the map `v ↦ D.φ⁻¹(v + δ(v))` is a smooth
parametrization of `M` around `x` on `Ω = V ∩ OE` (`OE` open in `N`), with `0 ∈ Ω` and
`p(0) = x`. -/
theorem MPolyfold.TangentGermChart.exists_isSmoothParam (hbump : PX.AdmitsBumpFunctions)
    (D : PX.TangentGermChart M x n) (hreg : D.IsRegular) :
    ∃ (Ω : Set D.N) (q : X → D.N) (G : Set X) (OE : Set D.N),
      PX.IsSmoothParam M Ω (fun v => D.φ.symm (D.Γ v)) q G ∧ IsOpen OE ∧ Ω = D.V ∩ OE ∧
        (0 : D.N) ∈ Ω ∧ D.φ.symm (D.Γ 0) = x := by
  obtain ⟨β, hβ, -, -, hβs, hβ1⟩ := proposition_5_5_3 hbump D.φ.isOpen_source D.mem_source
  obtain ⟨W, hWsub, hWo, hxW⟩ := eventually_nhds_iff.1 hβ1
  set p : D.N → X := fun v => D.φ.symm (D.Γ v) with hp
  set q : X → D.N := fun y => if y ∈ D.φ.source then β y • D.π (D.φ y) else 0 with hq
  have hΓc : ContinuousOn D.Γ D.V := continuous_subtype_val.continuousOn.add D.continuousOn
  have hpc : ContinuousOn p D.V :=
    D.φ.continuousOn_invFun.comp hΓc fun v hv => D.Γ_mem_O hv
  obtain ⟨OE, hOE, hOEeq⟩ := (continuousOn_iff'.1 hpc) W hWo
  have hΓ0 : D.Γ 0 = 0 := by rw [D.Γ_apply, D.δ_zero]; simp
  have hp0 : p 0 = x := by
    change D.φ.symm (D.Γ 0) = x
    rw [hΓ0, ← D.φ_zero, D.φ.symm_apply_apply D.mem_source]
  have hmem : ∀ v, v ∈ D.V ∩ OE ↔ v ∈ D.V ∧ p v ∈ W := fun v => by
    have := Set.ext_iff.1 hOEeq v
    exact ⟨fun hv => ⟨hv.1, (this.2 ⟨hv.2, hv.1⟩).1⟩, fun hv => ⟨hv.1, (this.1 ⟨hv.2, hv.1⟩).1⟩⟩
  refine ⟨D.V ∩ OE, q, D.φ.source ∩ W, OE, ?_, hOE, rfl,
    (hmem 0).2 ⟨D.zero_mem_V, by rw [hp0]; exact hxW⟩, hp0⟩
  refine ⟨D.φ.isOpen_source.inter hWo, hpc.mono inter_subset_left, ?_, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨hvV, hvW⟩ := (hmem v).1 hv
      exact ⟨(D.symm_Γ_mem hvV).1, (D.symm_Γ_mem hvV).2, hvW⟩
    · rintro ⟨hyM, hys, hyW⟩
      obtain ⟨hπV, hφy⟩ := D.exists_eq_Γ ⟨hyM, hys⟩
      have hpy : p (D.π (D.φ y)) = y := by
        change D.φ.symm (D.Γ (D.π (D.φ y))) = y
        rw [← hφy, D.φ.symm_apply_apply hys]
      exact ⟨D.π (D.φ y), (hmem _).2 ⟨hπV, by rw [hpy]; exact hyW⟩, hpy⟩
  · intro v hv
    obtain ⟨hvV, hvW⟩ := (hmem v).1 hv
    have hsrc : p v ∈ D.φ.source := (D.symm_Γ_mem hvV).2
    change (if p v ∈ D.φ.source then β (p v) • D.π (D.φ (p v)) else 0) = v
    rw [if_pos hsrc, hWsub _ hvW, one_smul]
    change D.π (D.φ (D.φ.symm (D.Γ v))) = v
    rw [D.φ.apply_symm_apply (D.Γ_mem_O hvV), D.π_Γ]
  · intro ℓ
    have heq : (fun y => ℓ (q y)) = chartLinCutoff D.φ β (ℓ.comp (D.π : D.φ.model.E 0 →L[ℝ] D.N))
        x := by
      funext y
      by_cases hy : y ∈ D.φ.source
      · simp only [hq, if_pos hy, chartLinCutoff_of_mem hy, D.φ_zero, sub_zero, map_smul,
          smul_eq_mul, ContinuousLinearMap.comp_apply]
      · simp only [hq, if_neg hy, chartLinCutoff, map_zero]
    rw [heq]
    exact isScSmoothMap_chartLinCutoff D.isChart hβ hβs _ x
  · intro h hh
    obtain ⟨R, hR⟩ := D.φ.model.isScRetract
    have hdom := D.V_isRelOpenInQuadrant.isScDomain
    have h1 : IsScSmooth (F := ScBanach.const ℝ) R.U ((h ∘ D.φ.symm) ∘ R) :=
      (hh.real_chart D.isChart).comp_isScSmooth R hR
    have hmaps : MapsTo D.Γ D.V R.U := fun v hv => R.retract_subset (hR ▸ D.Γ_mem_O hv)
    have h2 : IsScSmooth (E := ScBanach.const D.N) (F := ScBanach.const ℝ) D.V
        (((h ∘ D.φ.symm) ∘ R) ∘ D.Γ) :=
      IsScSmooth.comp hdom R.isScDomain h1 (D.Γ_isScSmooth hreg) hmaps
    have h3 : ContDiffOn ℝ ∞ (((h ∘ D.φ.symm) ∘ R) ∘ D.Γ) D.V :=
      (isScSmooth_iff_contDiffOn_const (W := ℝ) hdom _).1 h2
    refine (h3.congr fun v hv => ?_).mono inter_subset_left
    simp only [Function.comp_apply, hp, R.apply_eq_self_of_mem_retract (hR ▸ D.Γ_mem_O hv)]

end Polyfold
