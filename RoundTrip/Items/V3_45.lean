import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_45

/-! Round trip for V3_45 (Definitions 3.50 and 3.51: sc-Fredholm germs and sections of a tame
strong bundle).  Refreshed 2026-11-02 (HEAD, germ reading).

The item lists only definitions (`StrongBundle.IsScFredholmGerm`, `IsScFredholmSection`,
`IsScFredholmGermTame`, `IsScFredholmSectionTame` — all now the text's germ reading — and the
audit's whole-chart `IsScFredholmGermTameWholeChart`), so `A = True`; the comparison is between the
project's definitions and the blind notions `IsFredGermB`, `IsFredSectionB` (B: they agree for
sc-smooth sections of tame bundles).

* The filling agrees (`fillingGerm_iff_B`, field for field) and the chart is the same (a tame chart
  compatible with the atlas).  The two notions now differ only in the sc⁺-section and in where the
  strong bundle isomorphism lives:
  - B reads the "local sc⁺-section" `s` as sc-smooth on a relatively open `U₀ ∋ 0` (all levels
    `U₀ ∩ E_m`) and the conjugation on that `U₀`; the project's `IsScPlusGerm` is an sc⁺-GERM (its
    levels may shrink with `m`) and its conjugation is on the chart's whole `U`.
  - project ⇒ B (`chart_proj_to_blind`, proved): when the project's `s` is sc-smooth on some
    relatively open `U₀ ∋ 0` in `U`, B holds (with the conjugation restricted to `U₀`, which is
    the project's `IsConjugateToBasicGerm.of_subset`, outside the `import Polyfold` closure).  In general not: an sc⁺-germ smooth on shrinking levels
    only need not be sc-smooth on any `U₀` (the `exists_isScSmoothGerm_not_isScSmooth` phenomenon);
    believed false, not formalized (B's `s` is existential).  In particular the audit's whole-chart
    notion implies B (`wholeChart_to_blind`, the audit's `germTame_to_blind`).
  - B ⇒ project (`blind_to_proj_parts`, proved up to one field): the tame chart, the filling, the
    sc⁺-germ (on `ofSet U₀`) and `s(0) = g(0)` transfer; the conjugation is on `U₀ ⊆ U` only.
    Believed to be glue (shrink the chart's `U` to `U₀ ∩ r⁻¹(W)` with `O ∩ W ⊆ U₀`, a new chart
    construction), not attempted.
  Clause (b) (Definition 3.51) follows from clause (a) both ways (`section_of_germ`).
* `B → A` is trivial (`A = True`); flagged as vacuous.
Net: the project's notion is the broader one now (germ `s`); at the audit it was the stricter one
(whole-chart filled version). -/

open Set Filter Topology Function

noncomputable section

namespace RoundTrip.V3_45
open Polyfold

/-- The item lists only definitions: `A = True`. -/
def A : Prop := True

theorem A_holds : A := trivial

section Glue
variable {E F : ScBanach} {C U : Set (E.lvl 0)} {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0}

/-- **The canonical germ filling is B's text filling**, field for field. -/
theorem fillingGerm_iff_B (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E.lvl 0) ∈ U) (f g : E.lvl 0 → F.lvl 0) :
    IsFillingGerm hU hR h0 f g ↔ IsFillingB hU hR h0 f g := by
  constructor
  · intro h
    obtain ⟨G, hGU, hg, Dk, hDk, Φ, hΦ⟩ := h.germ
    exact ⟨G, hGU, hg, h.eq_on, h.mem_of_fixed, Dk, hDk, Φ, hΦ⟩
  · rintro ⟨G, hGU, hg, h1, h2, Dk, hDk, e, he⟩
    exact ⟨h1, h2, G, hGU, hg, Dk, hDk, e, he⟩

end Glue

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- **project ⇒ B, chart by chart, when the project's `s` is sc-smooth on a relatively open
`U₀ ∋ 0` inside `U`** and the conjugation is taken on `U₀`.  (That the conjugation on `U` restricts
to `U₀` is the project's `IsConjugateToBasicGerm.of_subset`, in `Chapter3/RestrictOpenGerms.lean`,
a module outside the `import Polyfold` closure, so it is a hypothesis here.) -/
theorem chart_proj_to_blind (Bd : StrongBundle PX P) (f : X → Y) (x : X)
    (hxs : x ∈ PX.smoothSet) (c : StrongBundleChart PX P) (hct : Bd.IsTameChart c)
    (hxV : x ∈ c.φ.source) (hφ0 : c.φ x = 0) (h0 : (0 : c.φ.model.E 0) ∈ c.U)
    (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1)
    (hfill : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
    (hs0 : c.F.toBase 1 (s 0) = g 0)
    (U₀ : Set (c.φ.model.E 0)) (hU₀ : IsRelOpenInQuadrant c.φ.model.E c.φ.model.C U₀)
    (h0₀ : (0 : c.φ.model.E 0) ∈ U₀) (hsub : U₀ ⊆ c.U)
    (hsm : IsScSmooth (F := c.F.shift) U₀ s)
    (hconj₀ : IsConjugateToBasicGerm U₀ (fun u => g u - c.F.toBase 1 (s u))) :
    IsFredGermB Bd f x :=
  ⟨hxs, c, hct.1, hct.2, hxV, hφ0, h0, g, s, U₀,
    (fillingGerm_iff_B c.relOpen c.isRetraction h0 _ g).1 hfill, hU₀, h0₀, hsub, hsm, hs0, hconj₀⟩

/-- **The audit's whole-chart Definition 3.50 implies the blind one** (`U₀ = U`). -/
theorem wholeChart_to_blind (Bd : StrongBundle PX P) (f : X → Y) (x : X)
    (h : Bd.IsScFredholmGermTameWholeChart f x) : IsFredGermB Bd f x := by
  obtain ⟨hxs, c, hct, hxV, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ := h
  exact chart_proj_to_blind Bd f x hxs c hct hxV hφ0 h0 g s
    (hfill.isFillingGerm c.relOpen c.isRetraction h0) hs0 c.U c.relOpen h0 subset_rfl hs hconj

/-- **Partial B ⇒ project**: from the blind Definition 3.50, everything of the project's
`IsScFredholmGermTame` in the same tame chart, except that the conjugation is on `U₀ ⊆ U` only. -/
theorem blind_to_proj_parts (Bd : StrongBundle PX P) (f : X → Y) (x : X)
    (h : IsFredGermB Bd f x) :
    x ∈ PX.smoothSet ∧ ∃ c : StrongBundleChart PX P, Bd.IsTameChart c ∧ x ∈ c.φ.source ∧
      c.φ x = 0 ∧ ∃ (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
        (s : c.φ.model.E 0 → c.F 1) (U₀ : Set (c.φ.model.E 0)),
        IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g ∧
        IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
        IsRelOpenInQuadrant c.φ.model.E c.φ.model.C U₀ ∧ (0 : c.φ.model.E 0) ∈ U₀ ∧ U₀ ⊆ c.U ∧
        IsConjugateToBasicGerm U₀ (fun u => g u - c.F.toBase 1 (s u)) := by
  obtain ⟨hxs, c, hc, htame, hxV, hφ0, h0, g, s, U₀, hfill, hU₀, h0₀, hsub, hsm, hs0, hconj⟩ := h
  exact ⟨hxs, c, ⟨hc, htame⟩, hxV, hφ0, h0, g, s, U₀,
    (fillingGerm_iff_B c.relOpen c.isRetraction h0 _ g).2 hfill,
    ⟨ScNbhdGerm.ofSet hU₀.relOpen h0₀, fun _ hu => hsub hu,
      hsm.isScSmoothGerm c.isQuadrantLike hU₀.relOpen h0₀⟩, hs0, hU₀, h0₀, hsub, hconj⟩

/-- **Clause (b) from clause (a)**: if the germ notions agree at every smooth point, so do the
section notions (Definition 3.51), for an sc-smooth `f`. -/
theorem section_of_germ (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScSmoothSection f)
    (hgerm : ∀ x ∈ PX.smoothSet, (Bd.IsScFredholmGermTame f x ↔ IsFredGermB Bd f x)) :
    Bd.IsScFredholmSectionTame f ↔ IsFredSectionB Bd f := by
  constructor
  · intro h
    exact ⟨h.regularizing, fun x hx => (hgerm x hx).1 (h.germTame x hx)⟩
  · rintro ⟨hreg, hg⟩
    exact { isScSmooth := hf, regularizing := hreg,
            germ := fun x hx => ((hgerm x hx).2 (hg x hx)).isScFredholmGerm,
            germTame := fun x hx => (hgerm x hx).2 (hg x hx) }

end

/-- `B → A` is vacuous (`A = True`). -/
theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V3_45.B_to_A []
#rt_overlap RoundTrip.V3_45.B_to_A []
#rt_check RoundTrip.V3_45.chart_proj_to_blind []
#rt_check RoundTrip.V3_45.wholeChart_to_blind []
#rt_check RoundTrip.V3_45.blind_to_proj_parts []
#rt_check RoundTrip.V3_45.section_of_germ []

end RoundTrip.V3_45

end
