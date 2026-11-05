import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_13

/-! Round trip for V3_13 (Definition 3.11: sc-Fredholm germs).  Refreshed 2026-11-02 (HEAD, germ
reading).

`A` is the conjunction of the types of the listed theorems (universes at `0`):
`StrongBundle.IsScFredholmGermWholeChart.isScFredholmGerm` (the old whole-chart notion implies the
germ notion), `StrongBundle.isScFredholmGerm_iff_germG_wholeChart` (the whole-chart notion is the
germ notion with `g`, `s` sc-smooth on the whole `U`), `IsFillingGerm.nonempty_kerEquiv` (a filling
forces `ker Dr(0) ≅ ker ρ(0)`) and `TrivialBundle.not_isFillingGerm_evenBundleChart` (a compatible
tame chart of a trivial bundle carries no filling).  `StrongBundle.IsScFredholmGerm` (now the germ
reading), `IsFillingGerm`, `IsScPlusGerm`, `IsConjugateToBasicGerm`, `IsStrongBundleIso`,
`StrongBundle.IsScFredholmGermWholeChart` are definitions (vocabulary).

B claims the project's `IsScFredholmGerm` equals the text's `IsScFredholmGermB` for sections of a
tame strong bundle.  With the germ reading the old main obstruction (text germs vs. whole-chart
`g`, `s`) is gone; what is proved and what remains:

* **filling and sc⁺-section agree** (`germ_iff_filling`, proved): `IsFillingGerm` is B's
  `IsFillingB` (B's `Dr` is the chosen `scDeriv U r` by uniqueness at `0 ∈ U₁`; the bijection and
  bound of B are the project's `Φ`); `IsScPlusGerm` is literally B's `IsScPlusGermB`.
* project ⇒ text (`proj_to_parts`, proved up to two fields): everything of `IsScFredholmGermB`
  except (i) **tameness of the chart's base retraction** — the project allows any compatible
  chart; whether germ data in a compatible chart can be moved to a compatible tame chart when the
  bundle is tame is open (the project's own `TameGermData.lean`, and A's
  `not_isFillingGerm_evenBundleChart` shows that some tame charts carry no filling at all, so the
  chart cannot be chosen freely) — a genuine difference in the definitions (the project's tame
  reading is `IsScFredholmGermTame`, Definition 3.50); and (ii) B's form `ConjBasicB` of the
  conjugation (`ℝⁿ`, `ℝᴺ`, the standard quadrant `[0,∞)ᵏ ⊕ ℝⁿ⁻ᵏ`, the literal push-forward a basic
  germ) versus the project's abstract `Pn`, `Q`, partial quadrant `Ct` and `h` agreeing with the
  push-forward near `0` — transport glue, not attempted.
* text ⇒ project (`text_to_parts`, proved up to one field): the chart (tame, compatible), the
  filling and the sc⁺-germ transfer; what remains is the conjugation: B's strong bundle
  isomorphism `Ψ` lives on a relatively open `U₀ ⊆ U`, the project's on the chart's whole `U`.
  Believed to be glue (shrink the chart's `U` to `U₀ ∩ r⁻¹(W)` with `O ∩ W ⊆ U₀` and restrict the
  data as the project's `RestrictOpenGerms.lean` does — `IsFillingGerm.of_subset`,
  `IsConjugateToBasicGerm.of_subset`, a module outside the `import Polyfold` closure; the
  `ℝⁿ`-to-`Pn` direction is direct) but it needs a new chart construction — not attempted.
* `B → A` is proved outright (B is not used): the four theorems are re-proved from non-banned
  project lemmas (for `not_isFillingGerm_evenBundleChart` the kernel argument is redone without
  `nonempty_kerEquiv`).
Net: the project's notion is broader than B's (it admits non-tame charts); the germ/whole-chart
difference of the audit is gone. -/

namespace RoundTrip.V3_13
open Polyfold Set Filter Topology StrongRetr

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.StrongBundle.IsScFredholmGermWholeChart.isScFredholmGerm.{0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.isScFredholmGerm_iff_germG_wholeChart.{0, 0}) ∧
  (type_of% @Polyfold.IsFillingGerm.nonempty_kerEquiv) ∧
  (type_of% @Polyfold.TrivialBundle.not_isFillingGerm_evenBundleChart)

theorem A_holds : A :=
  ⟨@Polyfold.StrongBundle.IsScFredholmGermWholeChart.isScFredholmGerm.{0, 0},
    @Polyfold.StrongBundle.isScFredholmGerm_iff_germG_wholeChart.{0, 0},
    @Polyfold.IsFillingGerm.nonempty_kerEquiv,
    @Polyfold.TrivialBundle.not_isFillingGerm_evenBundleChart⟩

section Glue
variable {E F : ScBanach} {C U : Set (E.lvl 0)} {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0}

/-- Two derivative families of an sc¹ map on `U ∋ 0` agree at `0`. -/
theorem sc1With_zero_unique (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E.lvl 0) ∈ U)
    {F' : ScBanach} {k : E.lvl 0 → F'.lvl 0} {D₁ D₂ : E.lvl 1 → E.lvl 0 →L[ℝ] F'.lvl 0}
    (h₁ : IsSc1With U k D₁) (h₂ : IsSc1With U k D₂) : D₁ 0 = D₂ 0 := by
  have h01 : (0 : E.lvl 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have h1 := (hU.isScDomain.uniqueDiffWithinAt 1 0 h01).eq (h₁.hasFDerivWithinAt 0 h01)
    (h₂.hasFDerivWithinAt 0 h01)
  have hd : Dense (Submodule.span ℝ (range (E.toBase 1)) : Set (E.lvl 0)) :=
    Dense.mono Submodule.subset_span (E.denseRange_inclK 0 1)
  refine ContinuousLinearMap.ext_on hd ?_
  rintro _ ⟨y, rfl⟩
  exact congrArg (fun L : E.lvl 1 →L[ℝ] F'.lvl 0 => L y) h1

/-- A topological isomorphism of the kernels given by `L` yields B's bijection and bound. -/
theorem bij_of_equiv {Lr : E.lvl 0 →L[ℝ] E.lvl 0} {q : F.lvl 0 →L[ℝ] F.lvl 0}
    {L : E.lvl 0 →L[ℝ] F.lvl 0}
    (Φ : LinearMap.ker (Lr : E.lvl 0 →ₗ[ℝ] E.lvl 0) ≃L[ℝ] LinearMap.ker (q : F.lvl 0 →ₗ[ℝ] F.lvl 0))
    (hΦ : ∀ v, (Φ v : F.lvl 0) = L v) :
    Set.BijOn L {v | Lr v = 0} {w | q w = 0} ∧ ∃ c : ℝ, ∀ v, Lr v = 0 → ‖v‖ ≤ c * ‖L v‖ := by
  refine ⟨⟨?_, ?_, ?_⟩, ‖Φ.symm.toContinuousLinearMap‖, fun v hv => ?_⟩
  · intro v hv
    have := (Φ ⟨v, hv⟩).2
    rw [hΦ ⟨v, hv⟩] at this
    exact this
  · intro v₁ hv₁ v₂ hv₂ heq
    have : Φ ⟨v₁, hv₁⟩ = Φ ⟨v₂, hv₂⟩ := by
      apply Subtype.ext
      rw [hΦ, hΦ]
      exact heq
    exact congrArg Subtype.val (Φ.injective this)
  · intro w hw
    refine ⟨(Φ.symm ⟨w, hw⟩ : E.lvl 0), (Φ.symm ⟨w, hw⟩).2, ?_⟩
    have := hΦ (Φ.symm ⟨w, hw⟩)
    rw [ContinuousLinearEquiv.apply_symm_apply] at this
    exact this.symm
  · have h1 : (⟨v, hv⟩ : LinearMap.ker (Lr : E.lvl 0 →ₗ[ℝ] E.lvl 0)) = Φ.symm (Φ ⟨v, hv⟩) :=
      (Φ.symm_apply_apply _).symm
    have h2 : ‖v‖ = ‖(⟨v, hv⟩ : LinearMap.ker (Lr : E.lvl 0 →ₗ[ℝ] E.lvl 0))‖ := rfl
    have h3 : ‖Φ ⟨v, hv⟩‖ = ‖L v‖ := by rw [← hΦ ⟨v, hv⟩]; rfl
    rw [h2, h1, ← h3]
    exact Φ.symm.toContinuousLinearMap.le_opNorm _

/-- B's bijection and bound yield a topological isomorphism of the kernels given by `L`. -/
theorem equiv_of_bij {Lr : E.lvl 0 →L[ℝ] E.lvl 0} {q : F.lvl 0 →L[ℝ] F.lvl 0}
    {L : E.lvl 0 →L[ℝ] F.lvl 0} (hbij : Set.BijOn L {v | Lr v = 0} {w | q w = 0}) (c : ℝ)
    (hc : ∀ v, Lr v = 0 → ‖v‖ ≤ c * ‖L v‖) :
    ∃ Φ : LinearMap.ker (Lr : E.lvl 0 →ₗ[ℝ] E.lvl 0) ≃L[ℝ]
        LinearMap.ker (q : F.lvl 0 →ₗ[ℝ] F.lvl 0), ∀ v, (Φ v : F.lvl 0) = L v := by
  have hmaps : ∀ v : LinearMap.ker (Lr : E.lvl 0 →ₗ[ℝ] E.lvl 0),
      L v ∈ LinearMap.ker (q : F.lvl 0 →ₗ[ℝ] F.lvl 0) := fun v => hbij.1 v.2
  let φ : LinearMap.ker (Lr : E.lvl 0 →ₗ[ℝ] E.lvl 0) →ₗ[ℝ]
      LinearMap.ker (q : F.lvl 0 →ₗ[ℝ] F.lvl 0) :=
    ((L : E.lvl 0 →ₗ[ℝ] F.lvl 0).domRestrict _).codRestrict _ hmaps
  have hφ : ∀ v, (φ v : F.lvl 0) = L v := fun v => rfl
  have hinj : Function.Injective φ := by
    intro v₁ v₂ heq
    have : L v₁ = L v₂ := by rw [← hφ, ← hφ, heq]
    exact Subtype.ext (hbij.2.1 v₁.2 v₂.2 this)
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨v, hv, hvw⟩ := hbij.2.2 w.2
    exact ⟨⟨v, hv⟩, Subtype.ext hvw⟩
  let e := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ v, (e v : F.lvl 0) = L v := fun v => rfl
  refine ⟨e.toContinuousLinearEquivOfBounds ‖L‖ c (fun v => ?_) (fun w => ?_), fun v => he v⟩
  · rw [show ‖e v‖ = ‖L v‖ from congrArg norm (he v)]
    exact L.le_opNorm _
  · have h3 := hc (e.symm w) (e.symm w).2
    have h4 : L (e.symm w) = w := by rw [← he, e.apply_symm_apply]
    rw [h4] at h3
    exact h3

/-- **The canonical germ filling is B's text filling** (no hypothesis on `g`). -/
theorem germ_iff_filling (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E.lvl 0) ∈ U) (fb g : E.lvl 0 → F.lvl 0) :
    IsFillingGerm hU hR h0 fb g ↔ IsFillingB C U R fb g := by
  have hr1 : IsSc1With U (r R) (scDeriv U (r R)) := (r_isScSmooth hU hR).isSc1.isSc1With_scDeriv
  constructor
  · intro h
    obtain ⟨G, hGU, hg, Dk, hDk, Φ, hΦ⟩ := h.germ
    obtain ⟨hb, c, hc⟩ := bij_of_equiv Φ hΦ
    exact ⟨⟨G, hGU, hg, Dk, hDk, scDeriv U (r R), hr1, hb, c, hc⟩, h.eq_on, h.mem_of_fixed⟩
  · rintro ⟨⟨G, hGU, hg, Dk, hDk, Dr, hDr, hbij, c, hc⟩, h1, h2⟩
    have eDr : Dr 0 = scDeriv U (r R) 0 := sc1With_zero_unique hU h0 hDr hr1
    rw [eDr] at hbij hc
    obtain ⟨Φ, hΦ⟩ := equiv_of_bij (q := ρCLM hR h0) hbij c hc
    exact ⟨h1, h2, G, hGU, hg, Dk, hDk, Φ, hΦ⟩

end Glue

section Bundle
set_option linter.unusedSectionVars false
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- **Partial `project ⇒ text`**: from the project's (germ-reading) sc-Fredholm germ, everything of
B's `IsScFredholmGermB` except (i) tameness of the chart's base retraction and (ii) B's form
`ConjBasicB` of the conjugation (the project's `IsConjugateToBasicGerm` is kept). -/
theorem proj_to_parts (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X)
    (h : Bd.IsScFredholmGerm f x₀) :
    x₀ ∈ PX.smoothSet ∧ ∃ c : StrongBundleChart PX P, Bd.IsChart c ∧
      x₀ ∈ c.φ.source ∧ c.φ.toPartialEquiv x₀ = 0 ∧
      ∃ (g : c.φ.model.E.lvl 0 → c.F.lvl 0) (s : c.φ.model.E.lvl 0 → c.F.lvl 1),
        IsFillingB c.φ.model.C c.U c.R (c.principal f) g ∧
        IsScPlusGermB c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
        IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)) := by
  obtain ⟨hx₀, c, hc, hx, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ := h
  exact ⟨hx₀, c, hc, hx, hφ0, g, s,
    (germ_iff_filling c.relOpen c.isRetraction h0 _ g).1 hfill, hs, hs0, hconj⟩

/-- **Partial `text ⇒ project`**: from B's sc-Fredholm germ, everything of the project's
`IsScFredholmGerm` (in the same chart, which is compatible and tame) except the conjugation, which
stays in B's form `ConjBasicB` (strong bundle isomorphism on some `U₀ ⊆ U` only). -/
theorem text_to_parts (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X)
    (h : IsScFredholmGermB Bd f x₀) :
    x₀ ∈ PX.smoothSet ∧ ∃ c : StrongBundleChart PX P, Bd.IsChart c ∧
      (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame ∧
      x₀ ∈ c.φ.source ∧ c.φ x₀ = 0 ∧
      ∃ (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
        IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g ∧
        IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
        ConjBasicB c.φ.model.C c.U (fun u => g u - c.F.toBase 1 (s u)) := by
  obtain ⟨hx₀, c, hc, htame, hx, hφ0, g, s, hfill, hs, hs0, hconj⟩ := h
  have h0 : (0 : c.φ.model.E 0) ∈ c.U := by
    obtain ⟨⟨G, hGU, -⟩, -, -⟩ := hfill
    exact hGU _ (G.zero_mem 0)
  exact ⟨hx₀, c, hc, htame, hx, hφ0, h0, g, s,
    (germ_iff_filling c.relOpen c.isRetraction h0 _ g).2 hfill, hs, hs0, hconj⟩

end Bundle

/-! ### `B → A`: the four theorems of A, re-proved from non-banned lemmas -/

/-- The kernel argument of `not_isFillingGerm_of_ker`, without `IsFillingGerm.nonempty_kerEquiv`. -/
theorem not_isFillingGerm_of_ker' {E F : ScBanach} {C U : Set (E.lvl 0)}
    {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0} (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E.lvl 0) ∈ U) {v : E.lvl 0}
    (hv : scDeriv U (r R) (0 : E.lvl 1) v = 0) (hv0 : v ≠ 0)
    (hρ : ∀ h : F.lvl 0, ρ R 0 h = 0 → h = 0) (fb g : E.lvl 0 → F.lvl 0) :
    ¬ IsFillingGerm hU hR h0 fb g := by
  intro h
  obtain ⟨-, -, -, -, -, Φ, -⟩ := h.germ
  have hvk : v ∈ LinearMap.ker ((scDeriv U (r R) (0 : E.lvl 1) : E.lvl 0 →L[ℝ] E.lvl 0) :
      E.lvl 0 →ₗ[ℝ] E.lvl 0) := LinearMap.mem_ker.2 hv
  have hΦ : Φ ⟨v, hvk⟩ = 0 := by
    refine Subtype.ext (hρ _ ?_)
    exact LinearMap.mem_ker.1 (Φ ⟨v, hvk⟩).2
  have : (⟨v, hvk⟩ : LinearMap.ker ((scDeriv U (r R) (0 : E.lvl 1) : E.lvl 0 →L[ℝ] E.lvl 0) :
      E.lvl 0 →ₗ[ℝ] E.lvl 0)) = 0 :=
    Φ.injective (hΦ.trans Φ.map_zero.symm)
  exact hv0 (congrArg Subtype.val this)

theorem A_reproved : A := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X _ _ _ PX Y _ _ _ P _ _ B f x₀ h
    obtain ⟨hx₀, c, hc, hx, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ := h
    exact ⟨hx₀, c, hc, hx, hφ0, h0, g, s, hfill.isFillingGerm c.relOpen c.isRetraction h0,
      ⟨ScNbhdGerm.ofSet c.relOpen.relOpen h0, fun _ hu => hu,
        hs.isScSmoothGerm c.isQuadrantLike c.relOpen.relOpen h0⟩, hs0, hconj⟩
  · intro X _ _ _ PX Y _ _ _ P _ _ B f x₀
    constructor
    · rintro ⟨hx₀, c, hc, hx, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩
      exact ⟨hx₀, c, hc, hx, hφ0, h0, g, s,
        ⟨hfill.isFillingGerm c.relOpen c.isRetraction h0, hfill.isScSmooth⟩,
        ⟨⟨ScNbhdGerm.ofSet c.relOpen.relOpen h0, fun _ hu => hu,
          hs.isScSmoothGerm c.isQuadrantLike c.relOpen.relOpen h0⟩, hs⟩, hs0, hconj⟩
    · rintro ⟨hx₀, c, hc, hx, hφ0, h0, g, s, ⟨hfill, hg⟩, ⟨-, hs⟩, hs0, hconj⟩
      exact ⟨hx₀, c, hc, hx, hφ0, h0, g, s, hfill.isFilledVersion c.relOpen c.isRetraction h0 hg,
        hs, hs0, hconj⟩
  · intro E F C U R hU hR h0 fb g h
    obtain ⟨-, -, -, -, -, Φ, -⟩ := h.germ
    exact ⟨Φ⟩
  · intro n k h0 fb g
    exact not_isFillingGerm_of_ker' _ _ h0 TrivialBundle.scDeriv_r_evenBundleChart_apply
      (fun h => one_ne_zero (congrFun (congrArg Prod.fst h) 0)) (fun _ hh => hh) fb g

/-- Proved outright (B is not used); flagged as vacuous. -/
theorem B_to_A : B → A := fun _ => A_reproved

#rt_check RoundTrip.V3_13.B_to_A [Polyfold.StrongBundle.IsScFredholmGermWholeChart.isScFredholmGerm,
  Polyfold.StrongBundle.isScFredholmGerm_iff_germG_wholeChart,
  Polyfold.IsFillingGerm.nonempty_kerEquiv, Polyfold.TrivialBundle.not_isFillingGerm_evenBundleChart]
#rt_overlap RoundTrip.V3_13.B_to_A [Polyfold.StrongBundle.IsScFredholmGermWholeChart.isScFredholmGerm,
  Polyfold.StrongBundle.isScFredholmGerm_iff_germG_wholeChart,
  Polyfold.IsFillingGerm.nonempty_kerEquiv, Polyfold.TrivialBundle.not_isFillingGerm_evenBundleChart]
#rt_check RoundTrip.V3_13.proj_to_parts [Polyfold.StrongBundle.IsScFredholmGermWholeChart.isScFredholmGerm,
  Polyfold.StrongBundle.isScFredholmGerm_iff_germG_wholeChart,
  Polyfold.IsFillingGerm.nonempty_kerEquiv, Polyfold.TrivialBundle.not_isFillingGerm_evenBundleChart]
#rt_check RoundTrip.V3_13.text_to_parts [Polyfold.StrongBundle.IsScFredholmGermWholeChart.isScFredholmGerm,
  Polyfold.StrongBundle.isScFredholmGerm_iff_germG_wholeChart,
  Polyfold.IsFillingGerm.nonempty_kerEquiv, Polyfold.TrivialBundle.not_isFillingGerm_evenBundleChart]

end RoundTrip.V3_13
