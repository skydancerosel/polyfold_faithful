import Mathlib

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §2.1, Proposition 2.1.2
(p. 22; proof in Appendix 2.7.1, pp. 69–71) (preprint Proposition 2.2).

# Classical smooth retractions have submanifold images

## The text, paraphrased

For a `C^∞` retraction `r : U → U` of an open subset `U` of a Banach space `E`, the image
`O = r(U)` is a `C^∞` submanifold: near each `x ∈ O` there are open `V ∋ x`, `W ∋ 0`, a splitting
`E = R ⊕ N` and a diffeomorphism `ψ` between `V` and `W` with `ψ(O ∩ V) = R ∩ W`.  The text prints
`ψ : V → W` together with `ψ(0) = x`; we read the normalization as `ψ(x) = 0`.

## What is formalized

* `proposition_2_1_2`: the statement, with the splitting `R = range Dr(x)`, `N = ker Dr(x)` (closed
  complementary subspaces) and `ψ` an `OpenPartialHomeomorph` with source `V`, target `W`, `C^∞` in
  both directions, `ψ x = 0`, `ψ '' (O ∩ V) = R ∩ W`.

The proof is not the text's (the `o(h)` estimates of Appendix 2.7.1) but the conjugation argument:
with `P = Dr(x)` (a projection by the chain rule, `isIdempotentElem_fderiv`),
`φ(y) = P(r(y) − x) + (1 − P)(y − r(y))` has derivative `1` at `x` and satisfies
`φ ∘ r = P ∘ φ` on `U` (`retractChart_comp`); so `φ` conjugates `r` to the linear projection `P`
near `x`, and the fixed points of `r` go to `range P`.
-/

open Set Filter Topology
open scoped ContDiff

namespace Polyfold

namespace GapP1Prop212

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The chart `φ(y) = P(r(y) − x) + (1 − P)(y − r(y))` of the proof. -/
noncomputable def retractChart (r : E → E) (P : E →L[ℝ] E) (x : E) (y : E) : E :=
  P (r y - x) + (y - r y - P (y - r y))

/-- At a fixed point `x` of a retraction `r` (`r ∘ r = r` near `x`), `Dr(x)` is a projection. -/
lemma isIdempotentElem_fderiv {U : Set E} (hU : IsOpen U) {r : E → E}
    (hr : ContDiffOn ℝ ∞ r U) (hretr : ∀ y ∈ U, r (r y) = r y) {x : E} (hxU : x ∈ U)
    (hfix : r x = x) : IsIdempotentElem (fderiv ℝ r x) := by
  have hd : DifferentiableAt ℝ r x :=
    (hr.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have hd' : DifferentiableAt ℝ r (r x) := by rw [hfix]; exact hd
  have heq : (r ∘ r) =ᶠ[𝓝 x] r :=
    Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => hretr y hy
  have h1 : fderiv ℝ (r ∘ r) x = fderiv ℝ r (r x) ∘L fderiv ℝ r x := fderiv_comp x hd' hd
  have h2 : fderiv ℝ (r ∘ r) x = fderiv ℝ r x := heq.fderiv_eq
  rw [hfix] at h1
  change fderiv ℝ r x * fderiv ℝ r x = fderiv ℝ r x
  rw [ContinuousLinearMap.mul_def, ← h1, h2]

/-- `φ ∘ r = P ∘ φ` on `U`, for a projection `P`. -/
lemma retractChart_comp {U : Set E} {r : E → E} (hretr : ∀ y ∈ U, r (r y) = r y)
    {P : E →L[ℝ] E} (hP : IsIdempotentElem P) (x : E) {y : E} (hy : y ∈ U) :
    retractChart r P x (r y) = P (retractChart r P x y) := by
  have hPP : ∀ v, P (P v) = P v := fun v => by
    simpa using congrArg (fun T : E →L[ℝ] E => T v) hP.eq
  simp only [retractChart, hretr y hy, sub_self, map_zero, map_add, map_sub, hPP]

/-- The derivative of `φ` at `x` is the identity. -/
lemma hasFDerivAt_retractChart {r : E → E} {P : E →L[ℝ] E} (hP : IsIdempotentElem P) {x : E}
    (hr : HasFDerivAt r P x) :
    HasFDerivAt (retractChart r P x)
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) x := by
  have h1 : HasFDerivAt (fun y => P (r y - x)) (P ∘L P) x :=
    P.hasFDerivAt.comp x (hr.sub_const x)
  have h2 : HasFDerivAt (fun y => y - r y) (ContinuousLinearMap.id ℝ E - P) x :=
    (hasFDerivAt_id x).sub hr
  have h3 : HasFDerivAt (fun y => P (y - r y)) (P ∘L (ContinuousLinearMap.id ℝ E - P)) x :=
    P.hasFDerivAt.comp x h2
  have hPP : ∀ v, P (P v) = P v := fun v => by
    simpa using congrArg (fun T : E →L[ℝ] E => T v) hP.eq
  refine (h1.add (h2.sub h3)).congr_fderiv ?_
  ext v
  simp [hPP]

/-- `φ` is `C^∞` on `U`. -/
lemma contDiffOn_retractChart {U : Set E} {r : E → E} (hr : ContDiffOn ℝ ∞ r U)
    (P : E →L[ℝ] E) (x : E) : ContDiffOn ℝ ∞ (retractChart r P x) U := by
  unfold retractChart
  have hsub : ContDiffOn ℝ ∞ (fun y => y - r y) U := contDiffOn_id.sub hr
  exact (P.contDiff.comp_contDiffOn (hr.sub contDiffOn_const)).add
    (hsub.sub (P.contDiff.comp_contDiffOn hsub))

/-- **Proposition 2.1.2** (2021, p. 22; preprint Proposition 2.2), as printed, with `ψ(x) = 0` for
the printed `ψ(0) = x`: the image `O = r(U)` of a `C^∞` retraction of an open subset of a Banach
space is a `C^∞` submanifold.  Near each `x ∈ O` there are open `V ∋ x`, `W ∋ 0`, closed
complementary subspaces `R`, `N`, and a `C^∞` diffeomorphism `ψ : V → W` (with `C^∞` inverse)
such that `ψ x = 0` and `ψ(O ∩ V) = R ∩ W`.  Moreover `V ⊆ U`. -/
theorem proposition_2_1_2 [CompleteSpace E] {U : Set E} (hU : IsOpen U) {r : E → E}
    (hr : ContDiffOn ℝ ∞ r U) (hmaps : MapsTo r U U) (hretr : ∀ y ∈ U, r (r y) = r y)
    {x : E} (hx : x ∈ r '' U) :
    ∃ (V W : Set E) (R N : Submodule ℝ E) (ψ : OpenPartialHomeomorph E E),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ IsOpen W ∧ (0 : E) ∈ W ∧
      IsCompl R N ∧ IsClosed (R : Set E) ∧ IsClosed (N : Set E) ∧
      ψ.source = V ∧ ψ.target = W ∧ ContDiffOn ℝ ∞ ψ V ∧ ContDiffOn ℝ ∞ ψ.symm W ∧
      ψ x = 0 ∧ ψ '' (r '' U ∩ V) = (R : Set E) ∩ W := by
  obtain ⟨z, hzU, rfl⟩ := hx
  set x := r z with hxdef
  have hxU : x ∈ U := hmaps hzU
  have hfix : r x = x := hretr z hzU
  set P := fderiv ℝ r x with hPdef
  have hP : IsIdempotentElem P := isIdempotentElem_fderiv hU hr hretr hxU hfix
  have hPP : ∀ v, P (P v) = P v := fun v => by
    simpa using congrArg (fun T : E →L[ℝ] E => T v) hP.eq
  set φ := retractChart r P x with hφdef
  have hφU : ContDiffOn ℝ ∞ φ U := contDiffOn_retractChart hr P x
  have hrx : HasFDerivAt r P x :=
    ((hr.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)).hasFDerivAt
  have hφx := hasFDerivAt_retractChart hP hrx
  have hφc : ContDiffAt ℝ ∞ φ x := hφU.contDiffAt (hU.mem_nhds hxU)
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set h := hφc.toOpenPartialHomeomorph φ hφx hn with hhdef
  have hxS : x ∈ h.source := hφc.mem_toOpenPartialHomeomorph_source hφx hn
  have hhcoe : (h : E → E) = φ := rfl
  -- points where `Dφ` is invertible
  set G : Set E := U ∩ fderiv ℝ φ ⁻¹' range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E) with hGdef
  have hG : IsOpen G :=
    (hφU.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage hU
      ContinuousLinearEquiv.isOpen
  have hxG : x ∈ G := ⟨hxU, ⟨ContinuousLinearEquiv.refl ℝ E, hφx.fderiv.symm⟩⟩
  have hrc : ContinuousOn r U := hr.continuousOn
  set V : Set E := h.source ∩ G ∩ (U ∩ r ⁻¹' h.source) with hVdef
  have hV : IsOpen V :=
    (h.open_source.inter hG).inter (hrc.isOpen_inter_preimage hU h.open_source)
  have hxV : x ∈ V := ⟨⟨hxS, hxG⟩, hxU, by rw [Set.mem_preimage, hfix]; exact hxS⟩
  have hVU : V ⊆ U := fun y hy => hy.1.2.1
  set ψ := h.restrOpen V hV with hψdef
  have hψsrc : ψ.source = V := by
    rw [hψdef, OpenPartialHomeomorph.restrOpen_source]
    exact Set.inter_eq_right.2 fun y hy => hy.1.1
  have hψcoe : (ψ : E → E) = φ := rfl
  have hψ0 : ψ x = 0 := by
    rw [hψcoe, hφdef, retractChart, hfix]; simp
  refine ⟨V, ψ.target, LinearMap.range (P : E →ₗ[ℝ] E), LinearMap.ker (P : E →ₗ[ℝ] E), ψ, hV,
    hxV, hVU, ψ.open_target, ?_, ?_, ?_, ?_, hψsrc, rfl, ?_, ?_, hψ0, ?_⟩
  · rw [← hψ0]; exact ψ.map_source (hψsrc ▸ hxV)
  · exact LinearMap.IsIdempotentElem.isCompl (f := (P : E →ₗ[ℝ] E))
      (by ext v; simp [hPP])
  · have : (LinearMap.range (P : E →ₗ[ℝ] E) : Set E) =
        (ContinuousLinearMap.id ℝ E - P) ⁻¹' {0} := by
      ext v
      simp only [SetLike.mem_coe, LinearMap.mem_range, ContinuousLinearMap.coe_coe,
        Set.mem_preimage, Set.mem_singleton_iff, FunLike.coe_sub,
        ContinuousLinearMap.coe_id', Pi.sub_apply, id_eq, sub_eq_zero]
      constructor
      · rintro ⟨w, rfl⟩; exact (hPP w).symm
      · intro hv; exact ⟨v, hv.symm⟩
    rw [this]; exact isClosed_singleton.preimage (ContinuousLinearMap.continuous _)
  · exact P.isClosed_ker
  · rw [hψcoe]; exact hφU.mono hVU
  · intro w hw
    have hwV : ψ.symm w ∈ V := hψsrc ▸ ψ.map_target hw
    have hfd : HasFDerivAt (ψ : E → E) (fderiv ℝ φ (ψ.symm w)) (ψ.symm w) := by
      rw [hψcoe]
      exact ((hφU.contDiffAt (hU.mem_nhds (hVU hwV))).differentiableAt (by simp)).hasFDerivAt
    obtain ⟨e, he⟩ := hwV.1.2.2
    rw [← he] at hfd
    refine (ψ.contDiffAt_symm hw hfd ?_).contDiffWithinAt
    rw [hψcoe]; exact hφU.contDiffAt (hU.mem_nhds (hVU hwV))
  · ext w
    constructor
    · rintro ⟨y, ⟨⟨u, huU, rfl⟩, hyV⟩, rfl⟩
      refine ⟨?_, ψ.map_source (hψsrc ▸ hyV)⟩
      have hry : r (r u) = r u := hretr u huU
      have hc := retractChart_comp hretr hP x (hVU hyV)
      rw [hry] at hc
      rw [hψcoe]
      exact ⟨_, hc.symm⟩
    · rintro ⟨hwR, hwW⟩
      obtain ⟨v, hv⟩ := hwR
      have hPw : P w = w := by rw [← hv]; exact hPP v
      set y := ψ.symm w with hydef
      have hyV : y ∈ V := hψsrc ▸ ψ.map_target hwW
      have hψy : ψ y = w := ψ.right_inv hwW
      have hc : φ (r y) = P (φ y) := retractChart_comp hretr hP x (hVU hyV)
      have hφy : φ y = w := hψy
      have hφry : φ (r y) = φ y := by rw [hc, hφy, hPw]
      have hryy : r y = y := h.injOn hyV.2.2 hyV.1.1 hφry
      exact ⟨y, ⟨⟨y, hVU hyV, hryy⟩, hyV⟩, hψy⟩

end GapP1Prop212

end Polyfold
