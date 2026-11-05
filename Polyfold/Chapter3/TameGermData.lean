import Polyfold.Chapter3.TameVacuityChart
import Polyfold.Chapter3.NonVacuityCorner
import Polyfold.Chapter3.NonVacuityG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, Definitions 3.4,
3.6, 3.11 and 3.50 *(book 2017: Definitions 3.4, 3.5, 3.7 and 3.14; see `BookConcordance.md`)*:
**does an sc-Fredholm germ (Definition 3.11) have germ data in a tame chart (Definition 3.50) when
the atlas is tame?** (Findings, Chapter 3, items 199 and 350–359; comparison items V3.45, V3.103.)

# Tame germ data from a tame atlas: the filler is chart-bound

## The text, paraphrased

(Definition 3.4) A filler `g : U → F` of the principal part `f̂ : O → F` of a section of the local
strong bundle `K = R(U ◁ F) → O` satisfies (1) `g = f̂` on `O` near `0`, (2) `y ∈ U` near `0` with
`g(y) = ρ(r(y))g(y)` lies in `O`, and (3) the linearization at `0` of `y ↦ [1 − ρ(r(y))]g(y)`,
restricted to `ker Dr(0)`, is a topological linear isomorphism onto `ker ρ(0)`.  (Definition 3.11)
`(f, x₀)` is an sc-Fredholm germ if **there exists** a strong bundle chart centred at `x₀` in which
`f̂` has a filling `g` and a local sc⁺-section `s` with `g − s` conjugated to a basic germ.
(Definition 3.50) For a tame strong bundle the chart is required to have a tame local bundle.

## What is formalized

* `Polyfold.IsFillingGerm.nonempty_kerEquiv`: **condition (3) forces the normal spaces to be
  isomorphic**: a filling germ in a chart gives `ker Dr(0) ≃L[ℝ] ker ρ(0)` (the normal space of
  `O` in `E` at `0` and the normal space of the fibre `K₀ = ρ(0)F` in `F`).
  `Polyfold.not_isFillingGerm_of_ker`: **in a chart with `ker Dr(0) ≠ 0` and `ker ρ(0) = 0` no
  section has a filling.**  So whether Definition 3.4 can be satisfied is a property of the chart
  (of its strong bundle retraction), not of the section.
* **A compatible tame chart of the trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ` in which no section has a
  filling** (`TrivialBundle.evenBundleChart`, centred at `0`): the model `ℝ ⊕ ℝⁿ` without
  boundary, the base retraction `r(a, u) = (0, u)` (the product `TrivialBundle.Reven` of the
  constant retraction `TrivialBundle.zeroRetr` of `ℝ` onto `0` with the identity of `ℝⁿ`), the chart
  `x ↦ (0, x)` of `ℝⁿ` onto the retract `{0} × ℝⁿ`, and the strong bundle retraction
  `R((a, u), h) = ((0, u), h)`.  It is compatible with the translation charts
  (`isChart_evenBundleChart`) and **tame** (`Reven_isTame`, `isTameChart_evenBundleChart`: the
  degeneracy index is `0` everywhere and `ℝ ⊕ 0` is an sc-complement of `T_xO = 0 ⊕ ℝⁿ`); but
  `ker Dr(0) = ℝ ⊕ 0 ≠ 0` while `ρ(0) = 1`, so `not_isFillingGerm_evenBundleChart`: **no map `g`
  fills the principal part of any section in this chart.**
* **The strong bundle `TrivialBundle.bundleEven n k`**: the trivial bundle with the one-chart atlas
  `{evenBundleChart}`.  Its atlas consists of tame charts (`bundleEven_atlas_isTameChart`), the
  translation charts are compatible with it (`isChart_chart_even`, `isTameChart_chart_even`), the
  graph section of a `C^∞` map `φ : ℝⁿ → ℝᵏ` is an sc-Fredholm section with tame germ data
  (`isScFredholmSectionTame_graphSection_even`, Definitions 3.14 and 3.51, germ reading) — **in the
  compatible translation charts, not in the chart of the atlas, where no section has germ data**
  (`tame_atlas_no_germData_in_atlas_chart`).

## What the text leaves implicit, and the choices made

* **What this settles.**  The proof strategy of Findings item 199 — re-centre a tame chart of the
  atlas at `x₀` and transport the filling, the sc⁺-germ and the conjugation to it — cannot work in
  general: the atlas chart need not carry any filling, by the necessary condition
  `ker Dr(0) ≅ ker ρ(0)`.  Definition 3.50 must therefore be read, as the project reads it
  (`StrongBundle.IsScFredholmGermTame`, `IsTameChart`: compatible with the atlas and tame), with the
  existential over **all** compatible tame charts, never as "in the (re-centred) chart of the given
  tame atlas": with the latter reading no section of `bundleEven` would be sc-Fredholm.
* **What stays open.**  Whether germ data in some compatible chart (Definition 3.11, untamed) can
  always be moved to some compatible tame chart when the atlas is tame.  The example is not a
  counterexample to this implication: the graph section has tame germ data, in a translation chart.
  A proof would have to produce, from the chart `c` of the germ data, a compatible tame chart whose
  normal spaces are isomorphic and in which a filling can be built; the transition `c' ∘ c⁻¹` is
  defined on the retract `K` only, so the filling cannot simply be pushed forward (Findings
  350–359).
* The point `x₀ = 0` suffices: re-centring `evenBundleChart` at `(0, x₀)` gives the same base
  retraction `(a, u) ↦ (0, u)` (translation of the base only), so the obstruction is the same at
  every point; this is said, not formalized.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### Condition (3) of a filler compares the two normal spaces -/

section Normal

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- **Condition (3) of Definition 3.4 forces the normal spaces to be isomorphic**: a filling germ
`g` in a chart with the strong bundle retraction `R = (r, ρ)` gives a topological linear isomorphism
`ker Dr(0) ≃ ker ρ(0)` (the linearization of `y ↦ [1 − ρ(r(y))]g(y)` restricted to `ker Dr(0)`).
Whether a section has a filling in a chart therefore depends on the chart: the normal space of
`O = r(U)` at `0` in `E` and the normal space of the fibre `K₀ = ρ(0)F` in `F` must be isomorphic
(Findings, Chapter 3, item 350). -/
theorem IsFillingGerm.nonempty_kerEquiv (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) {fb g : E 0 → F 0}
    (h : IsFillingGerm hU hR h0 fb g) :
    Nonempty (LinearMap.ker ((scDeriv U (r R) (0 : E 1) : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0) ≃L[ℝ]
      LinearMap.ker ((ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0)) := by
  obtain ⟨-, -, -, -, -, Φ, -⟩ := h.germ
  exact ⟨Φ⟩

/-- **A chart with `ker Dr(0) ≠ 0` and `ker ρ(0) = 0` carries no filling of any map**: if some
`v ≠ 0` has `Dr(0)v = 0` while `ρ(0)` is injective, then no `g` is a filling germ of any `f̂` for
this strong bundle retraction (Definition 3.4 (3) fails).  Being fillable is a property of the
chart (Findings, Chapter 3, item 350). -/
theorem not_isFillingGerm_of_ker (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) {v : E 0}
    (hv : scDeriv U (r R) (0 : E 1) v = 0) (hv0 : v ≠ 0)
    (hρ : ∀ h : F 0, ρ R 0 h = 0 → h = 0) (fb g : E 0 → F 0) :
    ¬ IsFillingGerm hU hR h0 fb g := by
  intro h
  obtain ⟨Φ⟩ := h.nonempty_kerEquiv hU hR h0
  have hvk : v ∈ LinearMap.ker ((scDeriv U (r R) (0 : E 1) : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0) :=
    LinearMap.mem_ker.2 hv
  have hΦ : Φ ⟨v, hvk⟩ = 0 := by
    refine Subtype.ext (hρ _ ?_)
    exact LinearMap.mem_ker.1 (Φ ⟨v, hvk⟩).2
  have : (⟨v, hvk⟩ : LinearMap.ker ((scDeriv U (r R) (0 : E 1) : E 0 →L[ℝ] E 0) :
      E 0 →ₗ[ℝ] E 0)) = 0 :=
    Φ.injective (hΦ.trans Φ.map_zero.symm)
  exact hv0 (congrArg Subtype.val this)

end Normal

/-! ### A compatible tame chart of the trivial bundle without fillings -/

namespace TrivialBundle

variable {n k : ℕ}

/-- The sc-Banach space `ℝ ⊕ ℝⁿ` (constant structures) of the chart `evenBundleChart`. -/
abbrev Eeven (n : ℕ) : ScBanach := (rnSc 1).prod (rnSc n)

lemma bijective_toBase_Eeven (j : ℕ) : Bijective ((Eeven n).toBase j) :=
  bijective_toBase_prod (bijective_toBase_const _) (bijective_toBase_const _) j

/-- The presentation `E ≅ ℝ⁰ ⊕ E` of the partial quadrant `univ` (`n = 0`, as in
`isPartialQuadrant_univ`). -/
def univPres (E : ScBanach) : ScIso E ((ScBanach.const (Fin 0 → ℝ)).prod E) where
  lvl m := (ContinuousLinearEquiv.uniqueProd ℝ (E m) (Fin 0 → ℝ)).symm
  incl_comm _ _ := Prod.ext (funext fun i => i.elim0) rfl

lemma univ_eq_univPres (E : ScBanach) :
    (univ : Set (E 0)) = univPres E 0 ⁻¹' quadrant 0 E 0 := by
  ext x; simp [quadrant]

lemma univ_degIndex_eq_zero (E : ScBanach) (x : E 0) : degIndex E univ x = 0 := by
  rw [degIndex_eq (univPres E) (univ_eq_univPres E) (mem_univ x)]
  simp [degIndexWith, quadrantDeg]

lemma minimalSubspaceWith_univPres (E : ScBanach) (x : E 0) :
    minimalSubspaceWith (univPres E) x = ⊤ :=
  eq_top_iff.2 fun _ _ => (mem_minimalSubspaceWith _).2 fun i => i.elim0

/-- **The constant retraction** `a ↦ 0` of `ℝ` (no boundary) onto the point `0`. -/
def zeroRetr : ScRetraction (rnSc 1) univ where
  U := univ
  toFun := fun _ => 0
  relOpen := rn_relOpen_univ 1
  mapsTo := fun _ _ => mem_univ _
  isScSmooth := isScSmooth_of_bijective_toBase (bijective_toBase_const _) (bijective_toBase_const _)
    (isScDomain_univ _) contDiffOn_const
  idem := fun _ _ => rfl

lemma zeroRetr_retract : zeroRetr.retract = {0} := by
  ext p
  constructor
  · rintro ⟨q, -, rfl⟩; rfl
  · rintro rfl; exact ⟨0, mem_univ _, rfl⟩

/-- `zeroRetr` is tame: the degeneracy index of `ℝ` is `0` everywhere, and `T_0{0} = 0` has the
sc-complement `ℝ ⊆ E_0 = ℝ`. -/
theorem zeroRetr_isTameWith : zeroRetr.IsTameWith (univPres (rnSc 1)) := by
  refine ⟨fun x _ => ?_, fun x _ _ => ⟨⊤, ?_, ?_⟩⟩
  · rw [univ_degIndex_eq_zero, univ_degIndex_eq_zero]
  · have hD : scDeriv zeroRetr.U zeroRetr x = 0 :=
      scDeriv_eq_of_hasFDerivAt (rn_relOpen_univ 1) zeroRetr.isScSmooth.isSc1
        ((rnSc 1).mem_lvlSet.2 (mem_univ _)) (hasFDerivAt_const _ _)
    rw [hD, ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero]
    exact (rnSc 1).isScSplitting_bot_top
  · rw [minimalSubspaceWith_univPres]

/-- **The base retraction of the even chart**: `r(a, u) = (0, u)` on `ℝ ⊕ ℝⁿ`, the product of
`zeroRetr` with the identity of `ℝⁿ`, with retract `{0} × ℝⁿ`. -/
abbrev Reven (n : ℕ) : ScRetraction (Eeven n) (univ ×ˢ univ) :=
  zeroRetr.prod (ScRetraction.id (rn_relOpen_univ n))

lemma Reven_retract : (Reven n).retract = {(0 : Fin 1 → ℝ)} ×ˢ univ := by
  rw [ScRetraction.prod_retract, zeroRetr_retract]
  congr 1
  exact image_id _

lemma mem_Reven_retract {p : (Eeven n) 0} : p ∈ (Reven n).retract ↔ p.1 = 0 := by
  rw [Reven_retract]; exact ⟨fun h => h.1, fun h => ⟨h, mem_univ _⟩⟩

/-- **`Reven` is tame** (Definition 2.34): the product of the tame retractions `zeroRetr` and
`id` is tame for the product presentation (`ScRetraction.IsTameWith.prod`), hence for every
presentation (`ScRetraction.IsTameWith.isTame`). -/
theorem Reven_isTame : (Reven n).IsTame :=
  (ScRetraction.IsTameWith.prod (univ_eq_univPres (rnSc 1)) (univ_eq_univPres (rnSc n))
    zeroRetr_isTameWith
    (ScRetraction.id_isTame (rn_relOpen_univ n) 0 (rnSc n) (univPres (rnSc n))
      (univ_eq_univPres (rnSc n)))).isTame
    (prod_eq_prodPresentation (univPres (rnSc 1)) (univPres (rnSc n))
      (univ_eq_univPres (rnSc 1)) (univ_eq_univPres (rnSc n)))

/-- **The chart** `x ↦ (0, x)` of `ℝⁿ` onto the retract `{0} × ℝⁿ` of `Reven`. -/
def evenChart : MChart (Fin n → ℝ) where
  model := ⟨Eeven n, univ ×ˢ univ, (Reven n).retract, ⟨Reven n, rfl⟩⟩
  toPartialEquiv :=
    { toFun := fun x => (((0 : Fin 1 → ℝ), x) : (Eeven n) 0)
      invFun := fun p => p.2
      source := univ
      target := (Reven n).retract
      map_source' := fun _ _ => mem_Reven_retract.2 rfl
      map_target' := fun _ _ => mem_univ _
      left_inv' := fun _ _ => rfl
      right_inv' := fun _ hp => Prod.ext (mem_Reven_retract.1 hp).symm rfl }
  isOpen_source := isOpen_univ
  target_eq := rfl
  continuousOn_toFun := (continuous_const.prodMk continuous_id).continuousOn
  continuousOn_invFun := continuous_snd.continuousOn

/-- `evenChart` is centred at `0`. -/
lemma evenChart_zero : evenChart (n := n) 0 = 0 := rfl

lemma evenChart_overlap : (evenChart (n := n)).overlap (rnChart n 0) = (Reven n).retract := by
  ext p
  refine ⟨?_, fun hp => ⟨p.2, ⟨mem_univ _, mem_univ _⟩, Prod.ext (mem_Reven_retract.1 hp).symm rfl⟩⟩
  rintro ⟨x, -, rfl⟩
  exact mem_Reven_retract.2 rfl

lemma rnChart_overlap_even : (rnChart n 0).overlap (evenChart (n := n)) = univ :=
  eq_univ_of_forall fun x => ⟨x, ⟨mem_univ _, mem_univ _⟩, sub_zero x⟩

/-- `evenChart` is compatible with the chart `id` of `ℝⁿ` (transitions `(0, x) ↦ x` and
`x ↦ (0, x)`). -/
theorem isChart_evenChart : (rnPolyfold n).IsChart (evenChart (n := n)) := by
  intro ψ hψ
  rw [mem_singleton_iff.1 hψ]
  refine ⟨?_, ?_⟩
  · rw [evenChart_overlap, rnChart_overlap_even]
    refine (isScSmoothRetractMap_iff_exists ⟨Reven n, rfl⟩).2 ⟨mapsTo_univ _ _, Reven n, rfl, ?_⟩
    exact isScSmooth_of_bijective_toBase bijective_toBase_Eeven (bijective_toBase_const _)
      (Reven n).isScDomain (f := fun p : (Eeven n) 0 => (p.2 : Fin n → ℝ) - 0)
      (contDiff_snd.sub contDiff_const).contDiffOn
  · rw [evenChart_overlap, rnChart_overlap_even]
    exact isScSmoothRetractMap_of_bijective_toBase (bijective_toBase_const _)
      bijective_toBase_Eeven (rn_relOpen_univ n) (fun _ _ => mem_Reven_retract.2 rfl)
      (g := fun x : Fin n → ℝ => (((0 : Fin 1 → ℝ), x + 0) : (Eeven n) 0))
      (contDiff_const.prodMk (contDiff_id.add contDiff_const))

/-- The strong bundle retraction `R((a, u), h) = ((0, u), h)` on `(ℝ ⊕ ℝⁿ) ◁ ℝᵏ`. -/
def Rbeven : (Eeven n) 0 × (rnSc k) 0 → (Eeven n) 0 × (rnSc k) 0 :=
  fun q => (((0 : Fin 1 → ℝ), q.1.2), q.2)

lemma bijective_toBase_EevenF (j : ℕ) : Bijective (((Eeven n).prod (rnSc k)).toBase j) :=
  bijective_toBase_prod bijective_toBase_Eeven (bijective_toBase_const _) j

lemma bijective_toBase_EevenF1 (j : ℕ) : Bijective (((Eeven n).prod (rnSc k).shift).toBase j) :=
  bijective_toBase_prod bijective_toBase_Eeven (bijective_toBase_shift (bijective_toBase_const _)) j

lemma contDiff_Rbeven : ContDiff ℝ ∞ (Rbeven (n := n) (k := k)) :=
  (contDiff_const.prodMk contDiff_fst.snd).prodMk contDiff_snd

lemma isStrongBundleRetraction_Rbeven :
    IsStrongBundleRetraction (Reven n).U (Rbeven (n := n) (k := k)) where
  mapsTo q hq := ⟨(Reven n).mapsTo hq.1, mem_univ _⟩
  fst_independent _ _ _ _ := rfl
  fiber_linear _ _ := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  preserves_filtration j l _ _ _ _ _ _ :=
    ⟨(bijective_toBase_Eeven j).2 _, (bijective_toBase_const _ l).2 _⟩
  isScSmooth_zero := isScSmooth_of_bijective_toBase bijective_toBase_EevenF bijective_toBase_EevenF
    ((Reven n).relOpen.prod_univ (rnSc k)).isScDomain contDiff_Rbeven.contDiffOn
  isScSmooth_one := by
    have hU := ((Reven n).relOpen.prod_univ (rnSc k).shift).isScDomain
    refine (isScSmooth_of_bijective_toBase bijective_toBase_EevenF1 bijective_toBase_EevenF1 hU
      (f := Rbeven (n := n) (k := k)) contDiff_Rbeven.contDiffOn).congr hU fun p _ => ?_
    refine Prod.ext rfl ?_
    change p.2 = invFun ((rnSc k).toBase 1) ((rnSc k).toBase 1 p.2)
    rw [leftInverse_invFun ((rnSc k).toBase_injective 1)]
  idem _ _ := rfl

/-- **The tame strong bundle chart without fillings** of `ℝⁿ × ℝᵏ → ℝⁿ`: over `evenChart`, with
the strong bundle retraction `Rbeven`, `(x, v) ↦ ((0, x), v)`. -/
def evenBundleChart : StrongBundleChart (rnPolyfold n) (proj n k) where
  φ := evenChart
  isChart := isChart_evenChart
  F := rnSc k
  U := (Reven n).U
  R := Rbeven
  relOpen := (Reven n).relOpen
  isRetraction := isStrongBundleRetraction_Rbeven
  base_retract := rfl
  toPartialEquiv := evenChart.toPartialEquiv.prod (PartialEquiv.refl (Fin k → ℝ))
  source_eq := by
    change (univ : Set (Fin n → ℝ)) ×ˢ (univ : Set (Fin k → ℝ)) = proj n k ⁻¹' univ
    rw [univ_prod_univ, preimage_univ]
  target_eq := by
    change (Reven n).retract ×ˢ (univ : Set (Fin k → ℝ)) = Rbeven '' ((Reven n).U ×ˢ univ)
    ext ⟨p, v⟩
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, -⟩
      exact ⟨(u, v), ⟨hu, mem_univ _⟩, rfl⟩
    · rintro ⟨q, hq, hqe⟩
      rw [← hqe]
      exact ⟨⟨q.1, hq.1, rfl⟩, mem_univ _⟩
  continuousOn_toFun := evenChart.continuousOn_toFun.prodMap continuousOn_id
  continuousOn_invFun := evenChart.continuousOn_invFun.prodMap continuousOn_id
  covers _ _ := rfl
  fiber_linear x _ := isLinearMap_fibEquiv x

lemma evenBundleChart_overlap (a : Fin n → ℝ) :
    (evenBundleChart (k := k)).overlap (chart a) = (Reven n).retract ×ˢ univ := by
  ext ⟨p, v⟩
  constructor
  · rintro ⟨⟨x, w⟩, -, hxw⟩
    rw [← hxw]
    exact ⟨mem_Reven_retract.2 rfl, mem_univ _⟩
  · rintro ⟨hp, -⟩
    exact ⟨(p.2, v), ⟨⟨mem_univ _, mem_univ _⟩, mem_univ _⟩,
      Prod.ext (Prod.ext (mem_Reven_retract.1 hp).symm rfl) rfl⟩

lemma chart_overlap_even (a : Fin n → ℝ) :
    (chart (k := k) a).overlap evenBundleChart = univ := by
  refine eq_univ_of_forall fun (p : (Fin n → ℝ) × (Fin k → ℝ)) =>
    ⟨(p.1 + a, p.2), ⟨mem_univ _, ⟨mem_univ _, mem_univ _⟩⟩, ?_⟩
  change (p.1 + a - a, p.2) = p
  rw [add_sub_cancel_right]

/-- **`evenBundleChart` is compatible with every translation chart**: its transitions are
`((0, x), v) ↦ (x − a, v)` and `(x, v) ↦ ((0, x + a), v)`. -/
theorem evenBundleChart_compatible (a : Fin n → ℝ) :
    (evenBundleChart (k := k)).Compatible (chart a) := by
  let S := (Reven n).prod (ScRetraction.id (rn_relOpen_univ k))
  let S1 := (Reven n).prod (ScRetraction.id (relOpen_univ_shift k))
  have hS : S.retract = (Reven n).retract ×ˢ univ := by
    rw [ScRetraction.prod_retract]; congr 1; exact image_id _
  have hS1 : S1.retract = (Reven n).retract ×ˢ univ := by
    rw [ScRetraction.prod_retract]; congr 1; exact image_id _
  have hss : strongShiftOne ((evenBundleChart (k := k)).overlap (chart a)) =
      (Reven n).retract ×ˢ univ := by
    rw [evenBundleChart_overlap]; rfl
  have hss' : strongShiftOne ((chart (k := k) a).overlap evenBundleChart) = univ := by
    rw [chart_overlap_even]; rfl
  have hsf1 : shiftFiber ((evenBundleChart (k := k)).transition (chart a)) =
      fun p : (Eeven n) 0 × (Fin k → ℝ) => ((p.1.2 : Fin n → ℝ) - a, p.2) :=
    funext fun p => Prod.ext rfl (by
      change invFun ((rnSc k).toBase 1) ((rnSc k).toBase 1 p.2) = p.2
      exact leftInverse_invFun ((rnSc k).toBase_injective 1) p.2)
  have hsf2 : shiftFiber ((chart (k := k) a).transition evenBundleChart) =
      fun p : (Fin n → ℝ) × (Fin k → ℝ) =>
        ((((0 : Fin 1 → ℝ), p.1 + a) : (Eeven n) 0), p.2) :=
    funext fun p => Prod.ext rfl (by
      change invFun ((rnSc k).toBase 1) ((rnSc k).toBase 1 p.2) = p.2
      exact leftInverse_invFun ((rnSc k).toBase_injective 1) p.2)
  have hr : ∀ v : Fin k → ℝ, v ∈ range ((rnSc k).toBase 1) := fun v =>
    (bijective_toBase_const _ 1).2 v
  have hrel1 : IsRelOpenInQuadrant ((rnSc n).prod (rnSc k).shift) (univ ×ˢ univ) univ := by
    rw [← univ_prod_univ]; exact (rn_relOpen_univ n).prod_univ (rnSc k).shift
  refine ⟨?_, ?_, ?_, ?_, fun _ _ _ => hr _, fun _ _ _ => hr _⟩
  · rw [evenBundleChart_overlap, chart_overlap_even]
    refine (isScSmoothRetractMap_iff_exists ⟨S, hS⟩).2 ⟨mapsTo_univ _ _, S, hS, ?_⟩
    exact isScSmooth_of_bijective_toBase bijective_toBase_EevenF bijective_toBase_model
      S.isScDomain (f := fun p : (Eeven n) 0 × (Fin k → ℝ) => ((p.1.2 : Fin n → ℝ) - a, p.2))
      ((contDiff_fst.snd.sub contDiff_const).prodMk contDiff_snd).contDiffOn
  · rw [evenBundleChart_overlap, chart_overlap_even]
    exact isScSmoothRetractMap_of_bijective_toBase bijective_toBase_model bijective_toBase_EevenF
      relOpen_model (fun _ _ => ⟨mem_Reven_retract.2 rfl, mem_univ _⟩)
      (g := fun p : (Fin n → ℝ) × (Fin k → ℝ) =>
        ((((0 : Fin 1 → ℝ), p.1 + a) : (Eeven n) 0), p.2))
      ((contDiff_const.prodMk (contDiff_fst.add contDiff_const)).prodMk contDiff_snd)
  · rw [hss, hss', hsf1]
    refine (isScSmoothRetractMap_iff_exists ⟨S1, hS1⟩).2 ⟨mapsTo_univ _ _, S1, hS1, ?_⟩
    exact isScSmooth_of_bijective_toBase bijective_toBase_EevenF1
      (bijective_toBase_prod (bijective_toBase_const _)
        (bijective_toBase_shift (bijective_toBase_const _)))
      S1.isScDomain (f := fun p : (Eeven n) 0 × (Fin k → ℝ) => ((p.1.2 : Fin n → ℝ) - a, p.2))
      ((contDiff_fst.snd.sub contDiff_const).prodMk contDiff_snd).contDiffOn
  · rw [hss, hss', hsf2]
    exact isScSmoothRetractMap_of_bijective_toBase
      (bijective_toBase_prod (bijective_toBase_const _)
        (bijective_toBase_shift (bijective_toBase_const _)))
      bijective_toBase_EevenF1 hrel1 (fun _ _ => ⟨mem_Reven_retract.2 rfl, mem_univ _⟩)
      ((contDiff_const.prodMk (contDiff_fst.add contDiff_const)).prodMk contDiff_snd)

/-- `evenBundleChart` is a strong bundle chart of `TrivialBundle.bundle n k`. -/
theorem isChart_evenBundleChart : (bundle n k).IsChart (evenBundleChart (k := k)) := by
  rintro _ ⟨a, rfl⟩
  exact evenBundleChart_compatible a

/-- **`evenBundleChart` is a tame strong bundle chart** of the trivial bundle (Definition 3.50's
requirement on the chart). -/
theorem isTameChart_evenBundleChart : (bundle n k).IsTameChart (evenBundleChart (k := k)) :=
  ⟨isChart_evenBundleChart, Reven_isTame.congr rfl fun _ _ => rfl⟩

/-- The derivative of the base retraction `r(a, u) = (0, u)` of `evenBundleChart` at `0` is the
projection `(a, u) ↦ (0, u)`; it kills `(1, 0)`. -/
lemma scDeriv_r_evenBundleChart_apply :
    scDeriv (evenBundleChart (n := n) (k := k)).U
      (StrongRetr.r (evenBundleChart (n := n) (k := k)).R) (0 : (Eeven n) 1)
      (((fun _ => 1), 0) : (Eeven n) 0) = 0 := by
  let L : (Eeven n) 0 →L[ℝ] (Eeven n) 0 :=
    (ContinuousLinearMap.inr ℝ (Fin 1 → ℝ) (Fin n → ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) (Fin n → ℝ))
  have hD : scDeriv (evenBundleChart (n := n) (k := k)).U
      (StrongRetr.r (evenBundleChart (n := n) (k := k)).R) (0 : (Eeven n) 1) = L :=
    scDeriv_zero_eq_of_hasFDerivAt (evenBundleChart (n := n) (k := k)).relOpen
      ((evenBundleChart (n := n) (k := k)).isRetraction.baseRetraction
        (evenBundleChart (n := n) (k := k)).relOpen).isScSmooth.isSc1
      ⟨mem_univ _, mem_univ _⟩ L.hasFDerivAt
  rw [hD]
  rfl

/-- **No map fills the principal part of any section in `evenBundleChart`** (Definition 3.4 (3)
fails: `ker Dr(0) = ℝ ⊕ 0 ≠ 0` while `ρ(0) = 1`).  So `evenBundleChart`, a compatible tame chart
centred at `0`, carries the germ data of Definition 3.11 for no section (Findings, Chapter 3, item
351). -/
theorem not_isFillingGerm_evenBundleChart (h0 : (0 : (Eeven n) 0) ∈ (evenBundleChart (k := k)).U)
    (fb g : (Eeven n) 0 → (rnSc k) 0) :
    ¬ IsFillingGerm (evenBundleChart (k := k)).relOpen evenBundleChart.isRetraction h0 fb g :=
  not_isFillingGerm_of_ker _ _ h0 scDeriv_r_evenBundleChart_apply
    (fun h => one_ne_zero (congrFun (congrArg Prod.fst h) 0)) (fun _ hh => hh) fb g

/-! ### The trivial bundle with the one-chart tame atlas `{evenBundleChart}` -/

variable (n k) in
/-- **The trivial strong bundle `ℝⁿ × ℝᵏ → ℝⁿ` with the one-chart atlas `{evenBundleChart}`**: a
strong bundle whose atlas consists of tame charts, none of which carries germ data. -/
def bundleEven : StrongBundle (rnPolyfold n) (proj n k) where
  continuous := continuous_fst
  surjective x := ⟨(x, 0), rfl⟩
  banachable := (bundle n k).banachable
  atlas :=
    { charts := {evenBundleChart}
      compatible := by
        rintro _ rfl _ rfl
        exact evenBundleChart.compatible_self
      cover := fun y => ⟨evenBundleChart, mem_singleton _, ⟨mem_univ _, mem_univ _⟩⟩ }

/-- **The atlas of `bundleEven` consists of tame charts.** -/
theorem bundleEven_atlas_isTameChart :
    ∀ c ∈ (bundleEven n k).atlas.charts, (bundleEven n k).IsTameChart c := by
  rintro _ rfl
  exact ⟨StrongBundle.isChart_of_mem (B := bundleEven n k) (mem_singleton _),
    Reven_isTame.congr rfl fun _ _ => rfl⟩

/-- The translation charts are compatible with `bundleEven`. -/
lemma isChart_chart_even (a : Fin n → ℝ) : (bundleEven n k).IsChart (chart a) := by
  rintro _ rfl
  exact (evenBundleChart_compatible a).symm

/-- The translation charts are tame charts of `bundleEven`. -/
lemma isTameChart_chart_even (a : Fin n → ℝ) : (bundleEven n k).IsTameChart (chart a) :=
  StrongBundle.isTameChart_of_eqOn_id (isChart_chart_even a) fun _ _ => rfl

variable {φ : (Fin n → ℝ) → (Fin k → ℝ)}

/-- The graph section is sc-smooth for `bundleEven` (its local representative in `evenBundleChart`
is `u ↦ ((0, u), φ(u))`). -/
theorem isScSmoothSection_graphSection_even (hφ : ContDiff ℝ ∞ φ) :
    (bundleEven n k).IsScSmoothSection (graphSection φ) := by
  refine ⟨isSection_graphSection, MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ
    (continuous_id.prodMk hφ.continuous).continuousOn fun x _ => ?_⟩
  refine ⟨rnChart n 0, (evenBundleChart (k := k)).toMChart continuous_fst, univ, isChart_rnChart 0,
    (bundleEven n k).isChart_toMChart (mem_singleton _), isOpen_univ, mem_univ x,
    fun z _ => ⟨mem_univ _, mem_univ _⟩, fun z _ => ⟨mem_univ _, mem_univ _⟩, ?_⟩
  have himg : (rnChart n 0).toPartialEquiv '' univ = univ :=
    image_univ_of_surjective (Equiv.subRight (0 : Fin n → ℝ)).surjective
  rw [himg]
  exact isScSmoothRetractMap_of_bijective_toBase (bijective_toBase_const _)
    bijective_toBase_EevenF (rn_relOpen_univ n)
    (fun u _ => ⟨((((0 : Fin 1 → ℝ), u + 0) : (Eeven n) 0), φ (u + 0)),
      ⟨⟨mem_univ _, mem_univ _⟩, mem_univ _⟩, rfl⟩)
    (g := fun u : Fin n → ℝ => ((((0 : Fin 1 → ℝ), u + 0) : (Eeven n) 0), φ (u + 0)))
    ((contDiff_const.prodMk (contDiff_id.add contDiff_const)).prodMk
      (hφ.comp (contDiff_id.add contDiff_const)))

/-- **Tame germ data of the graph section at every point, for `bundleEven`** (Definition 3.50,
whole-chart form): the data of `germData_graphSection` in the translation chart `chart x₀`, which
is a tame chart of `bundleEven`. -/
theorem isScFredholmGermTame_graphSection_even_wholeChart (hφ : ContDiff ℝ ∞ φ) (x₀ : Fin n → ℝ) :
    (bundleEven n k).IsScFredholmGermTameWholeChart (graphSection φ) x₀ := by
  obtain ⟨hfill, hs, hs0, hconj⟩ := germData_graphSection (k := k) hφ x₀
  exact ⟨by rw [rnPolyfold_smoothSet]; exact mem_univ x₀, chart x₀, isTameChart_chart_even x₀,
    mem_univ x₀, sub_self x₀, mem_univ 0, loc φ x₀, fun _ => φ x₀, hfill, hs, hs0, hconj⟩

/-- **The graph section of a `C^∞` map is an sc-Fredholm section of `bundleEven` with tame germ
data at every point** (Definitions 3.14 and 3.51, germ reading) — the germ data lie in the
compatible translation charts. -/
theorem isScFredholmSectionTame_graphSection_even (hφ : ContDiff ℝ ∞ φ) :
    (bundleEven n k).IsScFredholmSectionTame (graphSection φ) where
  isScSmooth := isScSmoothSection_graphSection_even hφ
  regularizing m x _ _ := by rw [rnPolyfold_levelSet]; exact mem_univ x
  germ x _ :=
    (isScFredholmGermTame_graphSection_even_wholeChart hφ x).isScFredholmGermTame.isScFredholmGerm
  germTame x _ := (isScFredholmGermTame_graphSection_even_wholeChart hφ x).isScFredholmGermTame

/-- **A strong bundle with a tame atlas, an sc-Fredholm section with tame germ data, and no germ
data in any chart of the atlas** (Findings, Chapter 3, item 352): for `bundleEven n k` every chart
of the atlas is tame, the graph section of a `C^∞` map `φ : ℝⁿ → ℝᵏ` is an sc-Fredholm section
with tame germ data (in the compatible translation charts), and in every chart of the atlas no map
`g` fills the principal part of any section.  So "tame germ data" (Definition 3.50) cannot mean
"germ data in a chart of the tame atlas": it is the existential over all compatible tame charts. -/
theorem tame_atlas_no_germData_in_atlas_chart (hφ : ContDiff ℝ ∞ φ) :
    (∀ c ∈ (bundleEven n k).atlas.charts, (bundleEven n k).IsTameChart c) ∧
    (bundleEven n k).IsScFredholmSectionTame (graphSection φ) ∧
    ∀ c ∈ (bundleEven n k).atlas.charts, ∀ (f : (Fin n → ℝ) → (Fin n → ℝ) × (Fin k → ℝ))
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0),
      ¬ IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g := by
  refine ⟨bundleEven_atlas_isTameChart, isScFredholmSectionTame_graphSection_even hφ, ?_⟩
  rintro _ rfl f h0 g
  exact not_isFillingGerm_evenBundleChart h0 _ g

end TrivialBundle

end Polyfold
