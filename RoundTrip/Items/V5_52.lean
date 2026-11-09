import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_52

/-!
Round trip for V5_52 (Theorem 5.34).  `A` is the type of `Polyfold.theorem_5_5_7`, universe
instantiated at `0`.

The two sides read "`f ≠ 0`" differently:

* A (the project): `PX.AdmitsBumpFunctions` (`f(x) ≠ 0` at the given point) and
  `LocalModel.HasBumpProperty` (`f(x) ≠ 0`);
* B (the blind file): `PX.AdmitsBumpFunctionsWeak` (`f` not identically zero, Definition 5.29 as
  written) and `HasBumpPropertyWeak` (`f` not identically zero on `O`).

Apart from that, "an atlas" is written as a covering set of charts of the structure (A) or as an
`MAtlas` equivalent to `PX.atlas` (B); these agree (`exists_atlas_iff`).

* With the strong reading on both sides the statements are equivalent: `A_to_BStrong`,
  `BStrong_to_A` (the blind file's `BStrong`).
* B itself is a true theorem: `B_holds` re-proves it, by the project's argument with `f(x) ≠ 0`
  replaced by `f ≠ 0` (no use of `theorem_5_5_7`).  So `A_to_B` is proved, but **vacuously** (it
  does not use `A`).
* `B → A` is not proved.  A is about the strong notions, and B says nothing about them; deriving A
  from B would need "weak bumps ⟹ strong bumps" (on `X`, or on local models), which is not glue:
  on a retract there is no translation that moves a bump that is merely not identically zero to a
  given point (the project's own reason for the strong reading).
-/

namespace RoundTrip.V5_52
open Polyfold Set Function

/-- The project's statement, universe `0`. -/
def A : Prop := type_of% @Polyfold.theorem_5_5_7.{0}

theorem A_holds : A := @Polyfold.theorem_5_5_7.{0}

/-- A covering set of charts of the structure is the same as an atlas equivalent to `PX.atlas`. -/
theorem exists_atlas_iff {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (Q : MChart X → Prop) :
    (∃ S : Set (MChart X), (∀ φ ∈ S, PX.IsChart φ) ∧ (∀ x, ∃ φ ∈ S, x ∈ φ.source) ∧
      ∀ φ ∈ S, Q φ) ↔
    ∃ A : MAtlas X, A.Equiv PX.atlas ∧ ∀ φ ∈ A.charts, Q φ := by
  constructor
  · rintro ⟨S, hS, hcov, hQ⟩
    refine ⟨⟨S, fun φ hφ ψ hψ => MPolyfold.IsChart.compatible PX (hS φ hφ) (hS ψ hψ), hcov⟩,
      (MAtlas.equiv_iff _ _).2 fun φ hφ ψ hψ => hS φ hφ ψ hψ, hQ⟩
  · rintro ⟨A, hA, hQ⟩
    exact ⟨A.charts, fun φ hφ ψ hψ => (MAtlas.equiv_iff _ _).1 hA φ hφ ψ hψ, A.cover, hQ⟩

/-! ### The strong reading: A ⟺ BStrong -/

theorem A_to_BStrong : A → BStrong := by
  intro hA X _ _ _ PX
  rw [← exists_atlas_iff]
  exact @hA X _ _ _ PX

theorem BStrong_to_A : BStrong → A := by
  intro hB X _ _ _ PX
  rw [exists_atlas_iff]
  exact hB X PX

/-! ### The weak reading: B holds (re-proved, not derived from A) -/

section Weak

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- "⇒" for the weak reading: every chart of the structure has the weak bump property. -/
theorem hasBumpPropertyWeak_of_isChart (h : PX.AdmitsBumpFunctionsWeak) {φ : MChart X}
    (hφ : PX.IsChart φ) : HasBumpPropertyWeak φ.model := by
  intro z hz W hW hzW _
  set U := φ.source ∩ φ ⁻¹' W with hUdef
  have hUo : IsOpen U := φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source hW
  have hxU : φ.symm z ∈ U := ⟨φ.symm_mapsTo hz, by
    rw [mem_preimage, φ.apply_symm_apply hz]; exact hzW⟩
  obtain ⟨f, hf, hfne, hsupp⟩ := h (φ.symm z) U hUo hxU
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := Function.ne_iff.1 hfne
  have hyV : y ∈ φ.source := (hsupp (subset_tsupport f hy)).1
  refine ⟨f ∘ φ.symm, hf.real_chart hφ, ⟨φ y, φ.mapsTo_model y hyV, ?_⟩, fun p hp => ?_⟩
  · simp only [Function.comp_apply, φ.symm_apply_apply hyV]; exact hy
  have hcw : ContinuousWithinAt φ.symm (φ.model.O ∩ support (f ∘ φ.symm)) p :=
    (φ.continuousOn_invFun p hp.2).mono inter_subset_left
  have h1 := hcw.mem_closure_image hp.1
  have h2 : φ.symm '' (φ.model.O ∩ support (f ∘ φ.symm)) ⊆ support f := by
    rintro _ ⟨z', hz', rfl⟩; exact hz'.2
  have h3 : φ.symm p ∈ U := hsupp (closure_mono h2 h1)
  have := h3.2
  rwa [mem_preimage, φ.apply_symm_apply hp.2] at this

/-- "⇐" for the weak reading: the project's argument (bump of a chart supported in a small ball,
extended by `0`) with "`f₀(φ(x)) ≠ 0`" replaced by "`f₀ ≢ 0` on `O`". -/
theorem admitsBumpFunctionsWeak_of_atlas {S : Set (MChart X)} (hS : ∀ φ ∈ S, PX.IsChart φ)
    (hcov : ∀ x, ∃ φ ∈ S, x ∈ φ.source) (hbump : ∀ φ ∈ S, HasBumpPropertyWeak φ.model) :
    PX.AdmitsBumpFunctionsWeak := by
  intro x U hU hx
  obtain ⟨φ, hφS, hxφ⟩ := hcov x
  have hφ := hS φ hφS
  obtain ⟨t, ht, htc, htsub⟩ :=
    exists_mem_nhds_isClosed_subset ((hU.inter φ.isOpen_source).mem_nhds ⟨hx, hxφ⟩)
  set U₁ := interior t with hU₁
  have hxU₁ : x ∈ U₁ := mem_interior_iff_mem_nhds.2 ht
  have hU₁cl : closure U₁ ⊆ U ∩ φ.source :=
    (closure_minimal interior_subset htc).trans htsub
  have hU₁V : U₁ ⊆ φ.source := subset_closure.trans (hU₁cl.trans inter_subset_right)
  obtain ⟨W₁, hW₁o, hW₁⟩ := φ.exists_isOpen_image_eq hU₁V isOpen_interior
  set z := φ x with hz
  have hzW₁ : z ∈ W₁ := by
    have : z ∈ φ '' U₁ := ⟨x, hxU₁, rfl⟩
    rw [hW₁] at this; exact this.2
  have hzO : z ∈ φ.model.O := φ.mapsTo_model x hxφ
  obtain ⟨R₀, hR₀⟩ := φ.model.isScRetract
  obtain ⟨W', hW'o, hW'eq⟩ := R₀.relOpen.relOpen
  have hzW' : z ∈ W' := by
    have : z ∈ R₀.U := R₀.retract_subset (hR₀ ▸ hzO)
    rw [hW'eq] at this; exact this.1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hW₁o.inter hW'o) z ⟨hzW₁, hzW'⟩
  have hclos := closure_inter_ball_subset R₀ hR₀ hW'eq (hball.trans inter_subset_right)
  obtain ⟨f₀, hf₀, ⟨y₀, hy₀O, hf₀y₀⟩, hf₀supp⟩ := hbump φ hφS z hzO (Metric.ball z (r / 2))
    Metric.isOpen_ball (Metric.mem_ball_self (by positivity)) hclos
  set f : X → ℝ := φ.source.indicator (f₀ ∘ φ) with hfdef
  have hsuppf : support f ⊆ U₁ := by
    intro y hy
    have hyV : y ∈ φ.source := by
      by_contra hyV; exact hy (indicator_of_notMem hyV _)
    have hfy : f₀ (φ y) ≠ 0 := by
      have := mem_support.1 hy; rwa [hfdef, indicator_of_mem hyV] at this
    have h1 : φ y ∈ Metric.ball z (r / 2) :=
      hf₀supp ⟨subset_closure ⟨φ.mapsTo_model y hyV, hfy⟩, φ.mapsTo_model y hyV⟩
    have h2 : φ y ∈ W₁ :=
      (hball (Metric.ball_subset_ball (by linarith) h1)).1
    have h3 : φ y ∈ φ '' U₁ := by rw [hW₁]; exact ⟨φ.mapsTo_model y hyV, h2⟩
    obtain ⟨y', hy', hyy'⟩ := h3
    rwa [φ.toPartialEquiv.injOn (hU₁V hy') hyV hyy'] at hy'
  have htsupp : tsupport f ⊆ U ∩ φ.source := (closure_mono hsuppf).trans hU₁cl
  refine ⟨f, ?_, ?_, htsupp.trans inter_subset_left⟩
  · refine isScSmoothMap_real_of_local fun y => ?_
    by_cases hy : y ∈ φ.source
    · refine ⟨φ, φ.source, hφ, φ.isOpen_source, hy, subset_rfl, ?_⟩
      rw [φ.image_source]
      refine hf₀.congr fun z' hz' => ?_
      simp only [Function.comp_apply, hfdef, indicator_of_mem (φ.symm_mapsTo hz'),
        φ.apply_symm_apply hz']
    · obtain ⟨ψ, hψ, hyψ⟩ := PX.exists_isChart_mem_source y
      have hyt : y ∉ tsupport f := fun h => hy (htsupp h).2
      refine ⟨ψ, ψ.source ∩ (tsupport f)ᶜ, hψ,
        ψ.isOpen_source.inter (isClosed_tsupport f).isOpen_compl, ⟨hyψ, hyt⟩,
        inter_subset_left, ⟨mapsTo_univ _ _, fun R hR => ?_⟩⟩
      refine IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) R.isScDomain
        (contDiffOn_const (c := (0 : ℝ)).congr fun u hu => ?_)
      obtain ⟨y', hy', hy'eq⟩ : R u ∈ ψ '' (ψ.source ∩ (tsupport f)ᶜ) :=
        hR ▸ R.apply_mem_retract hu
      simp only [Function.comp_apply, ← hy'eq, ψ.symm_apply_apply hy'.1]
      exact image_eq_zero_of_notMem_tsupport hy'.2
  · intro h0
    have h1 := congrFun h0 (φ.symm y₀)
    have hV : φ.symm y₀ ∈ φ.source := φ.symm_mapsTo hy₀O
    simp only [hfdef, indicator_of_mem hV, Function.comp_apply, φ.apply_symm_apply hy₀O,
      Pi.zero_apply] at h1
    exact hf₀y₀ h1

end Weak

/-- B (the weak reading) holds outright. -/
theorem B_holds : B := by
  intro X _ _ _ PX
  constructor
  · intro h
    exact ⟨PX.atlas, MAtlas.Equiv.refl _,
      fun φ hφ => hasBumpPropertyWeak_of_isChart h (PX.isChart_of_mem hφ)⟩
  · intro h
    obtain ⟨S, hS, hcov, hbump⟩ := (exists_atlas_iff PX _).2 h
    exact admitsBumpFunctionsWeak_of_atlas hS hcov hbump

/-- Vacuous: `B` is proved outright (`B_holds`), without using `A`. -/
theorem A_to_B : A → B := fun _ => B_holds

#rt_check RoundTrip.V5_52.A_to_B [Polyfold.theorem_5_5_7]
#rt_check RoundTrip.V5_52.A_to_BStrong [Polyfold.theorem_5_5_7]
#rt_check RoundTrip.V5_52.BStrong_to_A [Polyfold.theorem_5_5_7]
#rt_overlap RoundTrip.V5_52.BStrong_to_A [Polyfold.theorem_5_5_7]
#rt_overlap RoundTrip.V5_52.A_to_B [Polyfold.theorem_5_5_7]

end RoundTrip.V5_52
