import Polyfold.Chapter5.BumpFunctions
import Polyfold.Chapter4.Recentre

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, Definition 5.3.1 (preprint 5.9),
Definition 5.5.2 (preprint 5.29) and Proposition 5.5.3 (preprint 5.30) *(book 2017: Definitions 5.7, 5.13, Proposition 5.5; see
`BookConcordance.md`)*: **the weak reading of "admits sc-smooth bump functions" (`f` not identically
zero, Definition 5.5.2 (preprint 5.29) as written) against the pointwise reading (`f(x) ≠ 0`) that the proof of
Proposition 5.5.3 (preprint 5.30) uses** (Findings, Chapter 5, items 41 and 160–169; comparison items V5.16, V5.17,
V5.51).

# Weak versus pointwise bump functions

## The text, paraphrased

(Definition 5.3.1 (preprint 5.9) = 5.29) `X` admits sc-smooth bump functions if for every `x` and open `U(x)` there
is an sc-smooth `f : X → ℝ`, "`f ≠ 0`" (5.9) / "not identically zero" (5.29), with
`supp(f) ⊆ U(x)`.  (Proposition 5.5.3 (preprint 5.30)) Then there is an sc-smooth `f` with `f(x) = 1` and
`supp(f) ⊆ U(x)`; its proof starts from a bump `g` with `g(x) = 1`, i.e. from the pointwise reading.
(Before Definition 5.3.1 (preprint 5.9)) "This is, for example, the case if `X` is built on sc-Hilbert spaces".

## What is formalized

* `MPolyfold.HasBumpAt PX x` (a **bump point**: for every open `U ∋ x` an sc-smooth `f` with
  `f(x) ≠ 0` and `supp(f) ⊆ U`); `MPolyfold.admitsBumpFunctions_iff_forall_hasBumpAt` (the
  pointwise reading is "every point is a bump point"); `MPolyfold.admitsBumpFunctionsWeak_of_dense`
  (**if the bump points are dense, the weak reading holds**).
* **Translation by a non-smooth vector is not sc⁰** (`not_isSc0_add_const`,
  `not_isScSmooth_add_const`): if `a ∉ E_m`, then `v ↦ v + a` does not map `E_m` into `E_m`.  So
  the Banach-space argument "move a bump that is non-zero somewhere to `x`" is not available on an
  sc-Banach space (Findings, Chapter 5, item 41 (b)).
* **An sc-Banach space as an M-polyfold** (`scChart E`, the identity chart with the model
  `(E, E, E)`; `scPolyfold E`; `isChart_scChart`), and `isScSmoothMap_scPolyfold_iff`: a function
  `f : E → ℝ` is an sc-smooth function of the M-polyfold `E` iff it is sc-smooth on `univ`
  (Definition 2.3.8 (preprint 2.14) read in the identity chart).
* **On an sc-Banach space the weak reading gives bump points at all smooth points**
  (`AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth`): for `x ∈ E_∞` and open `U ∋ x`, a bump
  `f` not identically zero with support in `B(x, ε/2)` is non-zero on an open set, which contains a
  smooth point `y` (the smooth points are dense); `a = y − x` is smooth, so `v ↦ f(v + a)` is
  sc-smooth (`isScSmooth_add_const`), is non-zero at `x`, and has support in `B(x, ε) ⊆ U`.

## What the text leaves implicit, and the choices made

* **What is settled.**  The two readings are: pointwise = "every point is a bump point"; weak ⇐
  "the bump points are dense" (and ⇒, by a nested-neighbourhoods argument in a chart, not
  formalized).  On an sc-Banach space, weak ⇒ pointwise at every smooth point.  For M-polyfolds
  built on sc-Hilbert spaces both readings hold at every point
  (`MPolyfold.admitsBumpFunctions_of_hilbert`, `BumpFunctions.lean`).
* **What stays open** (Findings, Chapter 5, item 41): whether weak ⇒ pointwise at a non-smooth point
  `x ∈ X ∖ X_∞`, where there is no sc-smooth map moving a bump point to `x`.  A counterexample would
  be an sc-Banach space on which every sc-smooth function with small support around some
  `x ∉ E_1` vanishes at `x`, while sc-smooth bumps exist at smooth points; none is known here.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

/-! ### Bump points -/

section BumpPoints

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)

/-- **A bump point** of the M-polyfold `X`: `x` such that for every open `U ∋ x` there is an
sc-smooth `f : X → ℝ` with `f(x) ≠ 0` and `supp(f) ⊆ U` (the pointwise reading of Definition 5.3.1 (preprint 5.9)
at `x`). -/
def MPolyfold.HasBumpAt (x : X) : Prop :=
  ∀ U : Set X, IsOpen U → x ∈ U →
    ∃ f : X → ℝ, PX.IsScSmoothMap realPolyfold f ∧ f x ≠ 0 ∧ tsupport f ⊆ U

/-- The pointwise reading of Definition 5.3.1 (preprint 5.9) (`AdmitsBumpFunctions`) says that every point is a bump
point. -/
theorem MPolyfold.admitsBumpFunctions_iff_forall_hasBumpAt :
    PX.AdmitsBumpFunctions ↔ ∀ x, PX.HasBumpAt x :=
  Iff.rfl

variable {PX}

/-- **If the bump points are dense, `X` admits sc-smooth bump functions in the weak reading**
(Definition 5.5.2 (preprint 5.29) as written): a bump at a bump point `y ∈ U` is not identically zero and has support
in `U`. -/
theorem MPolyfold.admitsBumpFunctionsWeak_of_dense (h : Dense {x | PX.HasBumpAt x}) :
    PX.AdmitsBumpFunctionsWeak := by
  intro x U hU hx
  obtain ⟨y, hy, hyU⟩ := h.exists_mem_open hU ⟨x, hx⟩
  obtain ⟨f, hf, hfy, hsupp⟩ := hy U hU hyU
  exact ⟨f, hf, fun h0 => hfy (congrFun h0 y), hsupp⟩

end BumpPoints

/-! ### Translations by non-smooth vectors are not sc⁰ -/

section Translation

variable {E : ScBanach}

/-- **Translation by a vector `a ∉ E_m` is not sc⁰**: `0 ∈ E_m` is mapped to `a ∉ E_m` (Definition
1.12 asks `f(U_m) ⊆ F_m`).  This is why the Banach-space argument moving a bump to a given point is
not available on sc-Banach spaces (Findings, Chapter 5, item 41). -/
theorem not_isSc0_add_const {a : E 0} {m : ℕ} (ha : a ∉ range (E.toBase m)) :
    ¬ IsSc0 E E univ (fun v => v + a) := by
  intro h
  have := h.mem_range m 0 (E.mem_lvlSet.2 (mem_univ _))
  simp only [map_zero, zero_add] at this
  exact ha this

/-- Translation by a vector `a ∉ E_m` is not sc-smooth. -/
theorem not_isScSmooth_add_const {a : E 0} {m : ℕ} (ha : a ∉ range (E.toBase m)) :
    ¬ IsScSmooth univ (fun v : E 0 => v + a) :=
  fun h => not_isSc0_add_const ha h.isSc1.isSc0

end Translation

/-! ### An sc-Banach space as an M-polyfold -/

section ScPolyfold

variable (E : ScBanach)

lemma relOpen_univ_univ : IsRelOpenInQuadrant E univ univ :=
  ⟨isPartialQuadrant_univ _, univ, isOpen_univ, (inter_univ _).symm⟩

/-- The identity chart of the sc-Banach space `E`, modelled on `(E, E, E)` (`O = C = E`). -/
def scChart : MChart (E 0) where
  model := LocalModel.ofRelOpen (relOpen_univ_univ E)
  toPartialEquiv := PartialEquiv.refl _
  isOpen_source := isOpen_univ
  target_eq := rfl
  continuousOn_toFun := continuous_id.continuousOn
  continuousOn_invFun := continuous_id.continuousOn

/-- **An sc-Banach space `E` as an M-polyfold**, with the single chart `scChart E`. -/
def scPolyfold : MPolyfold (E 0) where
  atlas :=
    { charts := {scChart E}
      compatible := fun φ hφ ψ hψ => by
        rw [mem_singleton_iff.1 hφ, mem_singleton_iff.1 hψ]
        exact MChart.compatible_self _
      cover := fun x => ⟨scChart E, mem_singleton _, mem_univ x⟩ }

lemma isChart_scChart : (scPolyfold E).IsChart (scChart E) :=
  (scPolyfold E).isChart_of_mem (mem_singleton _)

lemma scChart_image_univ : scChart E '' univ = univ :=
  image_univ_of_surjective fun x => ⟨x, rfl⟩

variable {E}

/-- **Sc-smooth functions on the M-polyfold `E` are the sc-smooth maps `E → ℝ` on `univ`**
(Definition 2.3.8 (preprint 2.14) read in the identity chart, against Definition 1.1.15 (preprint 1.14) for the constant structure on
`ℝ`). -/
theorem isScSmoothMap_scPolyfold_iff {f : E 0 → ℝ} :
    (scPolyfold E).IsScSmoothMap realPolyfold f ↔ IsScSmooth (E := E) (F := realSc) univ f := by
  constructor
  · intro hf
    have h := (hf.real_chart (isChart_scChart E)).comp_isScSmooth
      (ScRetraction.id (relOpen_univ_univ E)) (image_id _)
    exact h.congr (isScDomain_univ _) fun _ _ => rfl
  · intro hf
    refine isScSmoothMap_real_of_local fun x => ⟨scChart E, univ, isChart_scChart E, isOpen_univ,
      mem_univ x, subset_univ _, ?_⟩
    rw [scChart_image_univ]
    refine (isScSmoothRetractMap_iff_exists (relOpen_univ_univ E).isScRetract).2
      ⟨mapsTo_univ _ _, ScRetraction.id (relOpen_univ_univ E), image_id _, ?_⟩
    exact hf.congr (isScDomain_univ _) fun _ _ => rfl

/-- **On an sc-Banach space the weak reading of "admits sc-smooth bump functions" gives bump points
at all smooth points**: if for every point and neighbourhood there is an sc-smooth function not
identically zero with support in the neighbourhood (Definition 5.5.2 (preprint 5.29) as written), then every
`x ∈ E_∞` is a bump point (the pointwise reading, which Proposition 5.5.3 (preprint 5.30)'s proof uses).  Proof:
a bump `f` with support in `B(x, ε/2)` is non-zero on a non-empty open set, which contains a smooth
point `y`; `a = y − x ∈ E_∞`, so `v ↦ f(v + a)` is sc-smooth, non-zero at `x`, with support in
`B(x, ε)`.  At non-smooth points the question is open (Findings, Chapter 5, item 161). -/
theorem MPolyfold.AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth
    (hw : (scPolyfold E).AdmitsBumpFunctionsWeak) {x : E 0} (hx : x ∈ E.smooth) :
    (scPolyfold E).HasBumpAt x := by
  intro U hU hxU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hxU
  obtain ⟨f, hf, hf0, hsupp⟩ := hw x (Metric.ball x (ε / 2)) Metric.isOpen_ball
    (Metric.mem_ball_self (by positivity))
  have hcont : Continuous f := continuousOn_univ.1 hf.continuousOn
  have hd : Dense (E.smooth : Set (E 0)) := E.dense_smooth 0
  obtain ⟨y, hys, hyf⟩ := hd.exists_mem_open hcont.isOpen_support (support_nonempty_iff.2 hf0)
  have ha : y - x ∈ E.smooth := E.smooth.sub_mem hys hx
  have hfsc : IsScSmooth (E := E) (F := realSc) univ f := isScSmoothMap_scPolyfold_iff.1 hf
  refine ⟨fun v => f (v + (y - x)), ?_, ?_, ?_⟩
  · exact isScSmoothMap_scPolyfold_iff.2 (IsScSmooth.comp (isScDomain_univ _) (isScDomain_univ _)
      hfsc (isScSmooth_add_const ha (isScDomain_univ _)) (mapsTo_univ _ _))
  · change f (x + (y - x)) ≠ 0
    rw [add_sub_cancel]; exact hyf
  · intro v hv
    have h1 : v + (y - x) ∈ tsupport f := by
      have : tsupport (fun v => f (v + (y - x))) ⊆ (fun v => v + (y - x)) ⁻¹' tsupport f := by
        change closure (support (f ∘ fun v => v + (y - x))) ⊆ _
        rw [support_comp_eq_preimage f (fun v => v + (y - x))]
        exact (continuous_add_const (y - x)).closure_preimage_subset _
      exact this hv
    have h2 : dist (v + (y - x)) x < ε / 2 := hsupp h1
    have h3 : dist y x < ε / 2 := hsupp (subset_closure hyf)
    refine hball ?_
    rw [dist_eq_norm] at h2 h3
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖v - x‖ = ‖(v + (y - x) - x) - (y - x)‖ := by congr 1; abel
      _ ≤ ‖v + (y - x) - x‖ + ‖y - x‖ := norm_sub_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add h2 h3
      _ = ε := add_halves ε

/-- The same, for every smooth point and every neighbourhood, in the form of Definition 5.3.1 (preprint 5.9). -/
theorem MPolyfold.AdmitsBumpFunctionsWeak.exists_bump_of_mem_smooth
    (hw : (scPolyfold E).AdmitsBumpFunctionsWeak) {x : E 0} (hx : x ∈ E.smooth) {U : Set (E 0)}
    (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ f : E 0 → ℝ, (scPolyfold E).IsScSmoothMap realPolyfold f ∧ f x ≠ 0 ∧ tsupport f ⊆ U :=
  hw.hasBumpAt_of_mem_smooth hx U hU hxU

end ScPolyfold

end Polyfold
