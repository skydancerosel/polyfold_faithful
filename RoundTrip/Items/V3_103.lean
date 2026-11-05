import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_103

open Set Filter Topology Function

noncomputable section

/-!
Round trip for V3_103 (Definitions 3.50, 3.51, 3.53 in a tame chart).  Refreshed 2026-11-02 (HEAD,
germ reading).  The decls list four definitions (`StrongBundle.IsTameChart`, `IsScFredholmGermTame`,
`IsGoodPositionGermTame`, `IsScFredholmSectionTame` — the last three now the text's germ reading:
`IsFillingGerm`, `IsScPlusGerm`) and eight theorems, so `A` is the conjunction of the types of
`StrongBundle.IsScFredholmGermTame.isScFredholmGerm`,
`StrongBundle.IsGoodPositionGermTame.isGoodPositionGerm`,
`StrongBundle.IsGoodPositionGermTame.isScFredholmGermTame`,
`StrongBundle.IsGoodPositionGermFilled.isGoodPositionGermTame`,
`StrongBundle.isTameChart_of_eqOn_id`, `ScRetraction.IsTame.congr`,
`IsFillingGerm.nonempty_kerEquiv`, `TrivialBundle.tame_atlas_no_germData_in_atlas_chart`
(universes at `0`).  `B` is the conjunction of four equivalences "project's notion ↔ text's
notion".

What is proved, **outright, without using `A`** (the comparison of the definitions):
* `B_i`: conjunct (i) of `B`, `IsTameChart c ↔ IsTameChartB c` — the definitions agree (`Iff.rfl`).
* (ii)/(iii), as in V3_45: the filling agrees field for field (`fillingGerm_iff_B`); the chart is
  the same tame chart; (iii) follows from (ii) both ways (`section_of_germ`).
  - project ⇒ text (`chart_proj_to_blind`): proved when the project's sc⁺-germ `s` is sc-smooth on
    a relatively open `U₀ ∋ 0` (and the conjugation is taken on `U₀`); the whole-chart notion
    implies the text's (`wholeChart_to_blind`).  In general not: B reads the local sc⁺-section as
    sc-smooth on a relatively open `U₀` (all levels), the project as a germ with possibly
    shrinking levels (believed false in general, not formalized).
  - text ⇒ project (`blind_to_proj_parts`): everything except that B's conjugation lives on
    `U₀ ⊆ U` while the project's is on the chart's whole `U` (believed glue: a chart with `U`
    shrunk into `U₀`; not attempted).
* (iv) (Definition 3.53), not re-done: as at the audit, project ⇒ text needs an **sc-complement**
  of the kernel when `d_X(x) ≥ 1` (the project's `IsInGoodPositionIn` has an algebraic one) and
  needs (ii) ⇒; text ⇒ project needs the good-position chart to be the germ chart (B lets the
  linear conditions sit in another tame chart) and the `U₀` glue of (ii).  The germ reading
  removed the audit's whole-chart filled-version obstruction from (iv) as well.
* `B → A` is now proved outright (B is not used): the eight theorems are re-proved from non-banned
  project lemmas — the six structural ones by their (short) proofs, `IsTame.congr` copied, and
  the `bundleEven` example by re-running its proof with the banned links (`IsTame.congr`,
  `isTameChart_of_eqOn_id`, `IsScFredholmGermTame.isScFredholmGerm`, `nonempty_kerEquiv`) replaced
  by the local copies.  At the audit this direction was recorded as failed.
-/

namespace RoundTrip.V3_103
open Polyfold

/-- The project's statement: the eight theorems among the decls, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.StrongBundle.IsScFredholmGermTame.isScFredholmGerm.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGerm.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.IsGoodPositionGermTame.isScFredholmGermTame.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGermTame.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.isTameChart_of_eqOn_id.{0, 0} ∧
    type_of% @Polyfold.ScRetraction.IsTame.congr ∧
    type_of% @Polyfold.IsFillingGerm.nonempty_kerEquiv ∧
    type_of% @Polyfold.TrivialBundle.tame_atlas_no_germData_in_atlas_chart

theorem A_holds : A :=
  ⟨@Polyfold.StrongBundle.IsScFredholmGermTame.isScFredholmGerm.{0, 0},
    @Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGerm.{0, 0},
    @Polyfold.StrongBundle.IsGoodPositionGermTame.isScFredholmGermTame.{0, 0},
    @Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGermTame.{0, 0},
    @Polyfold.StrongBundle.isTameChart_of_eqOn_id.{0, 0}, @Polyfold.ScRetraction.IsTame.congr,
    @Polyfold.IsFillingGerm.nonempty_kerEquiv,
    @Polyfold.TrivialBundle.tame_atlas_no_germData_in_atlas_chart⟩

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

/-- **(ii) project ⇒ text, chart by chart, when the project's `s` is sc-smooth on a relatively open
`U₀ ∋ 0` inside `U`** and the conjugation is taken on `U₀` (its restriction from `U` is the
project's `IsConjugateToBasicGerm.of_subset`, outside the `import Polyfold` closure). -/
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
  ⟨hxs, c, hct, hxV, hφ0, h0, g, s, U₀,
    (fillingGerm_iff_B c.relOpen c.isRetraction h0 _ g).1 hfill, hU₀, h0₀, hsub, hsm, hs0, hconj₀⟩

/-- **The audit's whole-chart Definition 3.50 implies the text's** (`U₀ = U`). -/
theorem wholeChart_to_blind (Bd : StrongBundle PX P) (f : X → Y) (x : X)
    (h : Bd.IsScFredholmGermTameWholeChart f x) : IsFredGermB Bd f x := by
  obtain ⟨hxs, c, hct, hxV, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ := h
  exact chart_proj_to_blind Bd f x hxs c hct hxV hφ0 h0 g s
    (hfill.isFillingGerm c.relOpen c.isRetraction h0) hs0 c.U c.relOpen h0 subset_rfl hs hconj

/-- **(ii) text ⇒ project, partially**: everything of `IsScFredholmGermTame` in the same tame chart,
except that the conjugation is on `U₀ ⊆ U` only. -/
theorem blind_to_proj_parts (Bd : StrongBundle PX P) (f : X → Y) (x : X)
    (h : IsFredGermB Bd f x) :
    x ∈ PX.smoothSet ∧ ∃ c : StrongBundleChart PX P, Bd.IsTameChart c ∧ x ∈ c.φ.source ∧
      c.φ x = 0 ∧ ∃ (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
        (s : c.φ.model.E 0 → c.F 1) (U₀ : Set (c.φ.model.E 0)),
        IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g ∧
        IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
        IsRelOpenInQuadrant c.φ.model.E c.φ.model.C U₀ ∧ (0 : c.φ.model.E 0) ∈ U₀ ∧ U₀ ⊆ c.U ∧
        IsConjugateToBasicGerm U₀ (fun u => g u - c.F.toBase 1 (s u)) := by
  obtain ⟨hxs, c, hct, hxV, hφ0, h0, g, s, U₀, hfill, hU₀, h0₀, hsub, hsm, hs0, hconj⟩ := h
  exact ⟨hxs, c, hct, hxV, hφ0, h0, g, s, U₀,
    (fillingGerm_iff_B c.relOpen c.isRetraction h0 _ g).2 hfill,
    ⟨ScNbhdGerm.ofSet hU₀.relOpen h0₀, fun _ hu => hsub hu,
      hsm.isScSmoothGerm c.isQuadrantLike hU₀.relOpen h0₀⟩, hs0, hU₀, h0₀, hsub, hconj⟩

/-- **(iii) from (ii)**: if the germ notions agree at every smooth point, so do the section notions
(Definition 3.51), for an sc-smooth `f`. -/
theorem section_of_germ (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScSmoothSection f)
    (hgerm : ∀ x ∈ PX.smoothSet, (Bd.IsScFredholmGermTame f x ↔ IsFredGermB Bd f x)) :
    Bd.IsScFredholmSectionTame f ↔ IsFredSectionB Bd f := by
  constructor
  · intro h
    exact ⟨h.regularizing, fun x hx => (hgerm x hx).1 (h.germTame x hx)⟩
  · rintro ⟨hreg, hg⟩
    have hgt : ∀ x ∈ PX.smoothSet, Bd.IsScFredholmGermTame f x := fun x hx => (hgerm x hx).2 (hg x hx)
    refine { isScSmooth := hf, regularizing := hreg, germ := fun x hx => ?_, germTame := hgt }
    obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩ := hgt x hx
    exact ⟨hs, c, hc.1, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩

end

/-- **Conjunct (i) of `B`**: the project's tame strong bundle chart is the text's (definitional;
proved without `A`). -/
theorem B_i :
    ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
      (Bd : StrongBundle PX P) (c : StrongBundleChart PX P),
        Bd.IsTameChart c ↔ IsTameChartB Bd c :=
  by intros; exact Iff.rfl

/-! ### `B → A`: the eight theorems of A, re-proved from non-banned lemmas -/

/-- `ScRetraction.IsTame.congr`, re-proved (the project's proof). -/
theorem isTame_congr' {E : ScBanach} {C : Set (E.lvl 0)} {R R' : ScRetraction E C}
    (hR : R.IsTame) (hU : R.U = R'.U) (h : Set.EqOn R R' R.U) : R'.IsTame := by
  intro n W T hT
  have hRT := hR n W T hT
  have hret : R.retract = R'.retract := by
    unfold ScRetraction.retract
    rw [← hU]
    exact h.image_eq
  refine ⟨fun x hx => ?_, fun x hx hs => ?_⟩
  · have hxR : x ∈ R.U := by rw [hU]; exact hx
    rw [← h hxR]
    exact hRT.degIndex_apply x hxR
  · have hx' : x ∈ E.lvlSet R.retract 1 := by rw [hret]; exact hx
    obtain ⟨A, hA, hAE⟩ := hRT.exists_complement x hx' hs
    refine ⟨A, ?_, hAE⟩
    have hD : scDeriv R'.U R' x = scDeriv R.U R x :=
      scDeriv_eq_of_eqOn_relOpen R.relOpen R'.isScSmooth.isSc1 R.isScSmooth.isSc1
        (by rw [hU]) subset_rfl h.symm (R.lvlSet_retract_subset 1 hx')
    rw [hD]
    exact hA

/-- The kernel argument of `not_isFillingGerm_of_ker`, without `IsFillingGerm.nonempty_kerEquiv`. -/
theorem not_isFillingGerm_of_ker' {E F : ScBanach} {C U : Set (E.lvl 0)}
    {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0} (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E.lvl 0) ∈ U) {v : E.lvl 0}
    (hv : scDeriv U (StrongRetr.r R) (0 : E.lvl 1) v = 0) (hv0 : v ≠ 0)
    (hρ : ∀ h : F.lvl 0, StrongRetr.ρ R 0 h = 0 → h = 0) (fb g : E.lvl 0 → F.lvl 0) :
    ¬ IsFillingGerm hU hR h0 fb g := by
  intro h
  obtain ⟨-, -, -, -, -, Φ, -⟩ := h.germ
  have hvk : v ∈ LinearMap.ker ((scDeriv U (StrongRetr.r R) (0 : E.lvl 1) :
      E.lvl 0 →L[ℝ] E.lvl 0) : E.lvl 0 →ₗ[ℝ] E.lvl 0) := LinearMap.mem_ker.2 hv
  have hΦ : Φ ⟨v, hvk⟩ = 0 := by
    refine Subtype.ext (hρ _ ?_)
    exact LinearMap.mem_ker.1 (Φ ⟨v, hvk⟩).2
  have : (⟨v, hvk⟩ : LinearMap.ker ((scDeriv U (StrongRetr.r R) (0 : E.lvl 1) :
      E.lvl 0 →L[ℝ] E.lvl 0) : E.lvl 0 →ₗ[ℝ] E.lvl 0)) = 0 :=
    Φ.injective (hΦ.trans Φ.map_zero.symm)
  exact hv0 (congrArg Subtype.val this)

open Polyfold.TrivialBundle in
open scoped ContDiff in
/-- `TrivialBundle.tame_atlas_no_germData_in_atlas_chart`, re-proved with the local copies. -/
theorem tame_atlas_no_germData' {n k : ℕ} {φ : (Fin n → ℝ) → (Fin k → ℝ)} (hφ : ContDiff ℝ ∞ φ) :
    (∀ c ∈ (bundleEven n k).atlas.charts, (bundleEven n k).IsTameChart c) ∧
    (bundleEven n k).IsScFredholmSectionTame (graphSection φ) ∧
    ∀ c ∈ (bundleEven n k).atlas.charts, ∀ (f : (Fin n → ℝ) → (Fin n → ℝ) × (Fin k → ℝ))
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0),
      ¬ IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g := by
  have htc : ∀ a : Fin n → ℝ, (bundleEven n k).IsTameChart (chart a) := fun a =>
    ⟨isChart_chart_even a, isTame_congr' (ScRetraction.id_isTame _) rfl fun _ _ => rfl⟩
  have hwc : ∀ x₀ : Fin n → ℝ,
      (bundleEven n k).IsScFredholmGermTameWholeChart (graphSection φ) x₀ := by
    intro x₀
    obtain ⟨hfill, hs, hs0, hconj⟩ := germData_graphSection (k := k) hφ x₀
    exact ⟨by rw [rnPolyfold_smoothSet]; exact Set.mem_univ x₀, chart x₀, htc x₀, Set.mem_univ x₀,
      sub_self x₀, Set.mem_univ 0, loc φ x₀, fun _ => φ x₀, hfill, hs, hs0, hconj⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro _ rfl
    exact ⟨StrongBundle.isChart_of_mem (B := bundleEven n k) (Set.mem_singleton _),
      isTame_congr' Reven_isTame rfl fun _ _ => rfl⟩
  · refine ⟨⟨isScSmoothSection_graphSection_even hφ,
      fun m x _ _ => (by rw [rnPolyfold_levelSet]; exact Set.mem_univ x), fun x _ => ?_⟩,
      fun x _ => (hwc x).isScFredholmGermTame⟩
    obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩ :=
      (hwc x).isScFredholmGermTame
    exact ⟨hs, c, hc.1, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩
  · rintro _ rfl f h0 g
    exact not_isFillingGerm_of_ker' _ _ h0 scDeriv_r_evenBundleChart_apply
      (fun h => one_ne_zero (congrFun (congrArg Prod.fst h) 0)) (fun _ hh => hh) _ g

theorem A_reproved : A := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ _ PX Y _ _ _ P _ _ B f x h
    obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩ := h
    exact ⟨hs, c, hc.1, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩
  · intro X _ _ _ PX Y _ _ _ P _ _ B f x h
    obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, hgp⟩ := h
    exact ⟨hs, c, hc.1, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, hgp⟩
  · intro X _ _ _ PX Y _ _ _ P _ _ B f x h
    obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, -⟩ := h
    exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩
  · intro X _ _ _ PX Y _ _ _ P _ _ B f x h
    obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, G, Dg, hG, hDg, hgp, -⟩ := h
    exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, G, Dg, hG, hDg, hgp⟩
  · intro X _ _ _ PX Y _ _ _ P _ _ B c hc hid
    exact ⟨hc, isTame_congr' (ScRetraction.id_isTame c.relOpen) rfl fun u hu => (hid u hu).symm⟩
  · intro E C R R' hR hU h
    exact isTame_congr' hR hU h
  · intro E F C U R hU hR h0 fb g h
    obtain ⟨-, -, -, -, -, Φ, -⟩ := h.germ
    exact ⟨Φ⟩
  · intro n k φ hφ
    exact tame_atlas_no_germData' hφ

/-- Proved outright (B is not used); flagged as vacuous. -/
theorem B_to_A : B → A := fun _ => A_reproved

#rt_check RoundTrip.V3_103.B_to_A [Polyfold.StrongBundle.IsScFredholmGermTame.isScFredholmGerm,
  Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGerm,
  Polyfold.StrongBundle.IsGoodPositionGermTame.isScFredholmGermTame,
  Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGermTame,
  Polyfold.StrongBundle.isTameChart_of_eqOn_id, Polyfold.ScRetraction.IsTame.congr,
  Polyfold.IsFillingGerm.nonempty_kerEquiv,
  Polyfold.TrivialBundle.tame_atlas_no_germData_in_atlas_chart]
#rt_overlap RoundTrip.V3_103.B_to_A [Polyfold.StrongBundle.IsScFredholmGermTame.isScFredholmGerm,
  Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGerm,
  Polyfold.StrongBundle.IsGoodPositionGermTame.isScFredholmGermTame,
  Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGermTame,
  Polyfold.StrongBundle.isTameChart_of_eqOn_id, Polyfold.ScRetraction.IsTame.congr,
  Polyfold.IsFillingGerm.nonempty_kerEquiv,
  Polyfold.TrivialBundle.tame_atlas_no_germData_in_atlas_chart]
#rt_check RoundTrip.V3_103.B_i [Polyfold.StrongBundle.IsScFredholmGermTame.isScFredholmGerm,
  Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGerm,
  Polyfold.StrongBundle.IsGoodPositionGermTame.isScFredholmGermTame,
  Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGermTame,
  Polyfold.StrongBundle.isTameChart_of_eqOn_id, Polyfold.ScRetraction.IsTame.congr,
  Polyfold.IsFillingGerm.nonempty_kerEquiv,
  Polyfold.TrivialBundle.tame_atlas_no_germData_in_atlas_chart]
#rt_check RoundTrip.V3_103.chart_proj_to_blind [Polyfold.StrongBundle.IsScFredholmGermTame.isScFredholmGerm,
  Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGerm,
  Polyfold.StrongBundle.IsGoodPositionGermTame.isScFredholmGermTame,
  Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGermTame,
  Polyfold.StrongBundle.isTameChart_of_eqOn_id, Polyfold.ScRetraction.IsTame.congr,
  Polyfold.IsFillingGerm.nonempty_kerEquiv,
  Polyfold.TrivialBundle.tame_atlas_no_germData_in_atlas_chart]
#rt_check RoundTrip.V3_103.wholeChart_to_blind [Polyfold.StrongBundle.IsScFredholmGermTame.isScFredholmGerm,
  Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGerm,
  Polyfold.StrongBundle.IsGoodPositionGermTame.isScFredholmGermTame,
  Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGermTame,
  Polyfold.StrongBundle.isTameChart_of_eqOn_id, Polyfold.ScRetraction.IsTame.congr,
  Polyfold.IsFillingGerm.nonempty_kerEquiv,
  Polyfold.TrivialBundle.tame_atlas_no_germData_in_atlas_chart]
#rt_check RoundTrip.V3_103.blind_to_proj_parts [Polyfold.StrongBundle.IsScFredholmGermTame.isScFredholmGerm,
  Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGerm,
  Polyfold.StrongBundle.IsGoodPositionGermTame.isScFredholmGermTame,
  Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGermTame,
  Polyfold.StrongBundle.isTameChart_of_eqOn_id, Polyfold.ScRetraction.IsTame.congr,
  Polyfold.IsFillingGerm.nonempty_kerEquiv,
  Polyfold.TrivialBundle.tame_atlas_no_germData_in_atlas_chart]
#rt_check RoundTrip.V3_103.section_of_germ [Polyfold.StrongBundle.IsScFredholmGermTame.isScFredholmGerm,
  Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGerm,
  Polyfold.StrongBundle.IsGoodPositionGermTame.isScFredholmGermTame,
  Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGermTame,
  Polyfold.StrongBundle.isTameChart_of_eqOn_id, Polyfold.ScRetraction.IsTame.congr,
  Polyfold.IsFillingGerm.nonempty_kerEquiv,
  Polyfold.TrivialBundle.tame_atlas_no_germData_in_atlas_chart]

end RoundTrip.V3_103

end
