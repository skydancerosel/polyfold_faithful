import Polyfold.Chapter13.LocallyFiniteStructurable

/-!
# Locally finite domain supports (2021 Proposition 13.3.19, p. 620)

2021 Proposition 13.3.19 (p. 620) asks for a family of structurable sc⁺-multisections whose
domain supports are locally finite. Wave 3 (C) proved it with M's `IsLocallyFiniteFamily`
(Definition 13.2.12: open saturated neighbourhoods over which only finitely many members are
non-trivial). This file gives the bridge from Mathlib's `LocallyFinite (fun l => domSupp (Λ l))`
to `IsLocallyFiniteFamily Λ` for families of functors on `W`, and the proposition in the
`LocallyFinite` form.

The proof: given `x`, take an open `U ∋ x` meeting finitely many `domSupp (Λ l)` and its
saturation `O = π⁻¹(π(U))` (open, Proposition 7.1.8). If `Λ_l(w) > 0` for some `w ≠ 0` over
`y ∈ O`, pick `φ : y → u` with `u ∈ U`; then `μ(φ, w) ≠ 0` lies over `u` and
`Λ_l(μ(φ, w)) = Λ_l(w) > 0`, so `u ∈ domSupp (Λ l) ∩ U`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}} {L : Type u} {Λ : L → A.W → ℚ≥0}

/-- Transport along a morphism keeps a vector off the zero section: if `w ≠ 0_{s(φ)}` then
`μ(φ, w) ≠ 0_{t(φ)}`. -/
theorem μ_ne_fiberZero_lf (q : pullbackSpace A.P A.X.src)
    (hw : (q : A.Mor × A.W).2 ≠ fiberZero A.P (A.P (q : A.Mor × A.W).2)) :
    A.E.μ q ≠ fiberZero A.P (A.P (A.E.μ q)) := by
  obtain ⟨⟨φ, w⟩, hq⟩ := q
  have hq' : A.P w = A.X.src φ := hq
  intro h0
  have hPμ : A.P (A.E.μ ⟨(φ, w), hq⟩) = A.X.tgt φ := A.E.P_μ _
  have hh : A.P (A.E.μ ⟨(φ, w), hq⟩) = A.X.src (A.X.inv φ) := hPμ.trans (A.X.src_inv φ).symm
  have h1 := A.E.μ_inv_μ ⟨(φ, w), hq⟩ hh
  have hz : A.P (fiberZero A.P (A.X.src (A.X.inv φ))) = A.X.src (A.X.inv φ) :=
    (0 : A.P ⁻¹' {A.X.src (A.X.inv φ)}).2
  have h2 := μ_fiberZero A (A.X.inv φ) hz
  have heq : A.E.μ ⟨(φ, w), hq⟩ = fiberZero A.P (A.X.src (A.X.inv φ)) := by
    rw [← hh]; exact h0
  have h3 : A.E.μ ⟨(A.X.inv φ, A.E.μ ⟨(φ, w), hq⟩), hh⟩ =
      A.E.μ ⟨(A.X.inv φ, fiberZero A.P (A.X.src (A.X.inv φ))), hz⟩ :=
    A.E.μ_congr (congrArg (Prod.mk (A.X.inv φ)) heq)
  have hw' : w = fiberZero A.P (A.X.src φ) := by
    rw [← A.X.tgt_inv φ]; exact h1.symm.trans (h3.trans h2)
  exact hw (hw'.trans (by rw [hq']))

/-- **The bridge for Proposition 13.3.19 (2021, p. 620)**: for a family of functors on `W`, locally
finite domain supports (Mathlib's `LocallyFinite`) give a locally finite family in the sense of
Definition 13.2.12 (p. 612). -/
theorem isLocallyFiniteFamily_of_locallyFinite (hΛ : ∀ l, IsWFunctor A (Λ l))
    (h : LocallyFinite fun l => domSupp (Λ l)) : IsLocallyFiniteFamily Λ := by
  intro x
  obtain ⟨U, hUx, hfin⟩ := h x
  obtain ⟨V, hVU, hVo, hxV⟩ := mem_nhds_iff.1 hUx
  refine ⟨A.X.saturation V, (A.X.proposition_7_1_8 V hVo).preimage A.X.continuous_π, ?_,
    A.X.subset_saturation V hxV, hfin.subset ?_⟩
  · change A.X.π ⁻¹' (A.X.π '' (A.X.π ⁻¹' (A.X.π '' V))) = A.X.π ⁻¹' (A.X.π '' V)
    rw [image_preimage_eq _ A.X.surjective_π]
  · rintro l ⟨w, hwO, hw0, hpos⟩
    obtain ⟨v, hvV, hvw⟩ := hwO
    obtain ⟨φ, hφs, hφt⟩ := A.X.π_eq_π_iff.1 hvw.symm
    have hq : A.P w = A.X.src φ := hφs.symm
    let q : pullbackSpace A.P A.X.src := ⟨(φ, w), hq⟩
    have hPq : A.P (A.E.μ q) = v := (A.E.P_μ q).trans hφt
    refine ⟨v, subset_closure ⟨A.E.μ q, hPq, ?_, ?_⟩, hVU hvV⟩
    · have := μ_ne_fiberZero_lf q hw0
      rwa [hPq] at this
    · rw [hΛ l q]; exact hpos

/-- **2021 Proposition 13.3.19, p. 620 (2017: Proposition 13.5), `LocallyFinite` form**: the sum
`⊕_{l ∈ L} Λ_l` of structurable sc⁺-multisections with locally finite domain supports is
structurable. -/
theorem proposition_13_3_19_locallyFinite [Nonempty L] (h : ∀ l, IsStructurable A (Λ l))
    (hlf : LocallyFinite fun l => domSupp (Λ l)) : IsStructurable A (lfSum Λ) :=
  proposition_13_3_19 h (isLocallyFiniteFamily_of_locallyFinite (fun l => (h l).1.1) hlf)

/-- **Proposition 13.3.19, `LocallyFinite` form, for paracompact `|X|`** (any family). -/
theorem proposition_13_3_19_locallyFinite_of_paracompact (hX : A.X.HasParacompactOrbitSpace)
    (h : ∀ l, IsStructurable A (Λ l)) (hlf : LocallyFinite fun l => domSupp (Λ l)) :
    IsStructurable A (lfSum Λ) :=
  proposition_13_3_19_of_paracompact hX h
    (isLocallyFiniteFamily_of_locallyFinite (fun l => (h l).1.1) hlf)

end SBLocalization

end Polyfold
