import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_56

/-! Round trip for V2_56 (Definition 2.49: sections, sc-smooth sections and sc⁺-sections of a local
strong bundle retract `p : K → O`, and the principal part).

`A` is the conjunction of the types of the theorems `IsScPlusSection.mem` and
`IsScPlusSection.isScSmoothSection` (no universe parameters).  `IsScSmoothSection`,
`IsScPlusSection` are definitions (vocabulary; B compares them with its own notions).

`A → B` (proved): the project's `IsScSmoothSection` (`(f x).1 = x` on `O` and Definition 2.7 in
the "every retraction" form) is B's `IsScSmoothSectionB` (`f(O) ⊆ K`, `(f x).1 = x`, and Definition
2.7 in the "one retraction" form) because `O = r(U)` is a retract (the project's
`baseRetraction`, after converting B's strong bundle retraction with `B_to_retr`); for
sc⁺-sections, B's lift `f₁` is the project's map `E₀ → E₀ × F₁`, and the condition `f(O) ⊆ K`
of B's section is `IsScPlusSection.mem` (from `A`); the principal part is immediate.

`B → A` fails: `A` contains two facts that B (a comparison of definitions) does not state:
`IsScPlusSection.mem` holds for arbitrary `C, O, K` (B only speaks about `O = r(U)`,
`K = R(U ◁ F)`), and `IsScPlusSection.isScSmoothSection` (an sc⁺-section is sc-smooth, through
the sc-smooth inclusion `K[1] → K[0]`) is not in B at all.  Both are true (the second is
Lemma 5.B of the exposition), but B cannot yield them. -/

namespace RoundTrip.V2_56
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsScPlusSection.mem) ∧ (type_of% @Polyfold.IsScPlusSection.isScSmoothSection)

theorem A_holds : A := ⟨@Polyfold.IsScPlusSection.mem, @Polyfold.IsScPlusSection.isScSmoothSection⟩

section Glue

variable {E F : ScBanach} {C U : Set (E.lvl 0)} {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0}

/-- B's strong bundle retractions (on a relatively open `U`) are the project's. -/
theorem B_to_retr (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetractionB U R) :
    IsStrongBundleRetraction U R := by
  obtain ⟨⟨⟨φ, hφ⟩, hlin, hfilt, h0, ⟨Φ₁, hΦ₁, h1⟩⟩, hidem⟩ := hR
  refine ⟨⟨?_, ?_, hlin, ?_, h0, ?_⟩, ?_⟩
  · rintro ⟨u, h⟩ ⟨hu, -⟩
    refine ⟨?_, mem_univ _⟩
    rw [(hφ u hu).2 h]; exact (hφ u hu).1
  · intro u hu h h'
    rw [(hφ u hu).2 h, (hφ u hu).2 h']
  · rintro m k hk u hu ⟨a, rfl⟩ h ⟨b, rfl⟩
    obtain ⟨q', hq'⟩ := hfilt m k hk (a, b) hu
    exact ⟨⟨q'.1, by rw [hq']⟩, ⟨q'.2, by rw [hq']⟩⟩
  · refine IsScSmooth.congr (hU.prod_univ F.shift).isScDomain ?_ h1
    rintro ⟨u, h⟩ ⟨hu, -⟩
    obtain ⟨e1, e2⟩ := hΦ₁ u hu h
    have hr : (R (u, F.toBase 1 h)).2 ∈ range (F.toBase 1) := ⟨_, e2⟩
    refine Prod.ext e1 ?_
    change (Φ₁ (u, h)).2 = Function.invFun (F.toBase 1) (R (u, F.toBase 1 h)).2
    apply F.toBase_injective 1
    rw [Function.invFun_eq hr, e2]
  · rintro ⟨u, h⟩ ⟨hu, -⟩
    exact hidem u hu h

/-- `O = r(U)` is a retract: B's base is the project's `baseRetraction` retract. -/
theorem base_isScRetract (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetractionB U R) :
    ∃ ρ : ScRetraction E C, ρ.retract = baseB U R :=
  ⟨(B_to_retr hU hR).baseRetraction hU, rfl⟩

end Glue

theorem A_to_B : A → B := by
  rintro ⟨hmem, -⟩ E F C U R hU hRB
  obtain ⟨ρ, hρ⟩ := base_isScRetract hU hRB
  refine ⟨fun f => ⟨?_, ?_⟩, fun f => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨hfst, hs⟩
    exact ⟨fun x hx => ⟨hs.mapsTo hx, hfst x hx⟩, hs.mapsTo, ρ, hρ, hs.comp_isScSmooth ρ hρ⟩
  · rintro ⟨hsec, hm, ρ', hρ', hs⟩
    exact ⟨fun x hx => (hsec x hx).2, (isScSmoothRetractMap_iff_exists ⟨ρ', hρ'⟩).2 ⟨hm, ρ', hρ', hs⟩⟩
  · rintro ⟨hsec, f₁, hlift, hm, ρ', hρ', hs⟩
    refine ⟨f₁, ⟨fun x hx => (hlift x hx).1.trans (hsec x hx).2,
      (isScSmoothRetractMap_iff_exists ⟨ρ', hρ'⟩).2 ⟨hm, ρ', hρ', hs⟩⟩, fun x hx => ?_⟩
    exact Prod.ext (hlift x hx).1.symm (hlift x hx).2.symm
  · rintro ⟨f₁, hplus, heq⟩
    refine ⟨fun x hx => ⟨?_, ?_⟩, f₁, fun x hx => ?_, hplus.isScSmooth.mapsTo, ρ, hρ,
      hplus.isScSmooth.comp_isScSmooth ρ hρ⟩
    · rw [heq x hx]; exact hmem hplus hx
    · rw [heq x hx]; exact hplus.fst_eq x hx
    · rw [heq x hx]; exact ⟨rfl, rfl⟩
  · intro f hsec x hx
    exact Prod.ext (hsec x hx).2 rfl

#rt_check RoundTrip.V2_56.A_to_B [Polyfold.IsScPlusSection.mem,
  Polyfold.IsScPlusSection.isScSmoothSection]

end RoundTrip.V2_56
