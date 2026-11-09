import Polyfold.Chapter5.BumpWeakPointwise

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Definition 5.5.2** and
**Proposition 5.5.3** (pp. 229–230), **Definition 5.3.1** (p. 216), **Definition 5.5.6** and
**Theorem 5.5.7** (p. 231) *(2017: Definitions 5.13, 5.7, 5.15, Theorem 5.11; preprint 2014:
Definitions 5.29, 5.9, 5.33, Proposition 5.30, Theorem 5.34)*: **the open question of Findings,
Chapter 5, item 163 — can the bump points of an sc-Banach space be dense without being
everything? — is settled for sc-Banach spaces: they cannot** (research file; Findings, Chapter 5,
items 160–163).

# Bump points of an sc-Banach space: all or nothing

## The question (Findings, Chapter 5, item 163)

Is there an sc-Banach space `E` (or an M-polyfold `X`) and a point `x ∉ E_∞` such that every
sc-smooth `f : E → ℝ` with support in some neighbourhood of `x` vanishes at `x`, while the bump
points (`MPolyfold.HasBumpAt`, `BumpWeakPointwise.lean`) are dense?  Equivalently: can the weak
reading of "admits sc-smooth bump functions" (Definition 5.5.2 as written, `f` not identically
zero) hold on `E` while the pointwise reading (Definition 5.3.1 read as `f(x) ≠ 0`, which the proof
of Proposition 5.5.3 uses) fails?

Item 161 proved the pointwise reading at the smooth points only, by moving a bump `f` with
`f(y) ≠ 0` to `x` along the translation `v ↦ v + (y − x)`, which is sc-smooth exactly when
`y − x ∈ E_∞` (`isScSmooth_add_const`, `not_isScSmooth_add_const`); item 163 records that at a
non-smooth `x` "there is no sc-smooth map moving a bump point to `x`".

## The answer: no such `E` and `x` exist

The missing observation is that the bump need not be moved *exactly*.  An sc-smooth
`f : E → ℝ` is continuous on `E₀`, so `f ≠ 0` on an `E₀`-ball `B(y, δ)` around a point `y` with
`f(y) ≠ 0`; since `E_∞` is dense in `E₀`, there is a **smooth** vector `a ∈ E_∞` with
`‖a − (y − x)‖ < δ`, and `v ↦ f(v + a)` is sc-smooth (translation by a smooth vector), non-zero at
`x` (because `‖(x + a) − y‖ < δ`), and supported in `supp(f) − a`, which lies in a prescribed ball
around `x` when `δ` and the support of `f` are small.  The text's own remark after Definition
5.5.2 — "we can use the Banach space structure to rescale and translate" — survives on an
sc-Banach space in this approximate form, with translations by smooth vectors only.

Consequences, all for the M-polyfold `scPolyfold E` (the sc-Banach space `E` with its identity
chart):

* **one bump point gives all** (`MPolyfold.HasBumpAt.scPolyfold_all`): if some `x₀ ∈ E` is a bump
  point, every `x ∈ E` is;
* **the bump points are `∅` or `E`** (`MPolyfold.hasBumpAt_scPolyfold_all_or_nothing`); in
  particular they are dense only if they are everything, which answers item 163 for sc-Banach
  spaces in the negative;
* **weak = pointwise on an sc-Banach space**
  (`MPolyfold.AdmitsBumpFunctionsWeak.admitsBumpFunctions_scPolyfold`,
  `MPolyfold.admitsBumpFunctionsWeak_iff_admitsBumpFunctions_scPolyfold`): Definition 5.5.2 as
  written and the pointwise reading of Definition 5.3.1 are equivalent for `X = E`.

## Consequences for M-polyfolds (Definition 5.5.6, Theorem 5.5.7)

* **A local model whose sc-Banach space has one bump point has the sc-smooth bump function
  property** (`LocalModel.hasBumpProperty_of_hasBumpAt`): a bump of `E` at `x ∈ O` with support in
  `W` restricts to `O` (its composition with any retraction onto `O` is sc-smooth by the chain
  rule), and the support in `O` lies in `W`.
* **An M-polyfold each of whose points has a chart whose model sc-Banach space has a bump point
  (for instance, admits bump functions in the weak reading) admits sc-smooth bump functions in
  the pointwise reading** (`MPolyfold.admitsBumpFunctions_of_model_hasBumpAt`,
  `MPolyfold.admitsBumpFunctions_of_model_weak`), by Theorem 5.5.7.  So for an M-polyfold the
  pointwise reading depends only on the model sc-Banach spaces: it holds as soon as each of them
  admits a single sc-smooth bump somewhere.

## What is left

For a general M-polyfold `X` the question "can the bump points of `X` be dense without being
everything?" is **not** settled here: a bump point of a retract `O` need not come from a bump of
the ambient `E` (the sc-smooth functions of `O` are the `f` with `f ∘ r` sc-smooth, and `f ∘ r` has
large support), and on `O` there is no translation.  What is proved is the sufficient condition
above.  Whether some sc-Banach space has *no* bump point at all (the sc-analogue of a Banach space
without `C¹` bump functions, Definition 5.5.4) is a different question, not touched here; the text
notes that the classical version is open ([25]).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

/-! ### Approximate translation of a non-vanishing point by a smooth vector -/

section Translate

variable {E : ScBanach}

/-- **A point where a continuous `f : E₀ → ℝ` is non-zero can be moved approximately to any `x`
by a smooth translation**: for `f(y) ≠ 0`, `x ∈ E₀` and `η > 0` there is `a ∈ E_∞` with
`‖a − (y − x)‖ < η` and `f(x + a) ≠ 0`.  (Continuity of `f` at `y` gives a ball `B(y, δ)` on which
`f ≠ 0`; `E_∞` is dense in `E₀`.) -/
theorem exists_smooth_translate_ne_zero {f : E 0 → ℝ} (hf : Continuous f) {y : E 0}
    (hy : f y ≠ 0) (x : E 0) {η : ℝ} (hη : 0 < η) :
    ∃ a ∈ E.smooth, ‖a - (y - x)‖ < η ∧ f (x + a) ≠ 0 := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.eventually_nhds_iff.1 (hf.continuousAt.eventually_ne hy)
  have hd : Dense (E.smooth : Set (E 0)) := E.dense_smooth 0
  obtain ⟨a, ha, hdist⟩ := hd.exists_dist_lt (y - x) (lt_min hδ hη)
  refine ⟨a, ha, ?_, hδf ?_⟩
  · rw [← dist_eq_norm, dist_comm]
    exact hdist.trans_le (min_le_right _ _)
  · rw [dist_eq_norm, show x + a - y = -((y - x) - a) by abel, norm_neg, ← dist_eq_norm]
    exact hdist.trans_le (min_le_left _ _)

/-- The support of `v ↦ f(v + a)` is the preimage of the support of `f` under `v ↦ v + a`. -/
lemma tsupport_comp_add_const_subset (f : E 0 → ℝ) (a : E 0) :
    tsupport (fun v => f (v + a)) ⊆ (fun v => v + a) ⁻¹' tsupport f := by
  change closure (support (f ∘ fun v => v + a)) ⊆ _
  rw [support_comp_eq_preimage f (fun v => v + a)]
  exact (continuous_add_const a).closure_preimage_subset _

/-- **Moving an sc-smooth bump of the sc-Banach space `E` to an arbitrary point**: if `f` is an
sc-smooth function of the M-polyfold `E` with `f(y) ≠ 0` and support in the ball `B(c, ρ)`, then
for every `x ∈ E` and every `ε > ‖c − y‖ + ρ` there is an sc-smooth `g` with `g(x) ≠ 0` and
support in `B(x, ε)`, namely `g(v) = f(v + a)` for a smooth `a` close to `y − x`
(`exists_smooth_translate_ne_zero`, `isScSmooth_add_const`).  No smoothness of `x`, `y` or `c` is
assumed. -/
theorem exists_bump_translate {f : E 0 → ℝ} (hf : (scPolyfold E).IsScSmoothMap realPolyfold f)
    {y : E 0} (hy : f y ≠ 0) {c : E 0} {ρ : ℝ} (hsupp : tsupport f ⊆ Metric.ball c ρ) (x : E 0)
    {ε : ℝ} (hε : ‖c - y‖ + ρ < ε) :
    ∃ g : E 0 → ℝ, (scPolyfold E).IsScSmoothMap realPolyfold g ∧ g x ≠ 0 ∧
      tsupport g ⊆ Metric.ball x ε := by
  have hfsc : IsScSmooth (E := E) (F := realSc) univ f := isScSmoothMap_scPolyfold_iff.1 hf
  have hcont : Continuous f := continuousOn_univ.1 hf.continuousOn
  obtain ⟨a, ha, hanear, hfxa⟩ :=
    exists_smooth_translate_ne_zero hcont hy x (η := ε - (‖c - y‖ + ρ)) (by linarith)
  refine ⟨fun v => f (v + a), ?_, hfxa, ?_⟩
  · exact isScSmoothMap_scPolyfold_iff.2 (IsScSmooth.comp (isScDomain_univ _) (isScDomain_univ _)
      hfsc (isScSmooth_add_const ha (isScDomain_univ _)) (mapsTo_univ _ _))
  · intro v hv
    have h1 : v + a ∈ tsupport f := tsupport_comp_add_const_subset f a hv
    have h2 : dist (v + a) c < ρ := hsupp h1
    rw [dist_eq_norm] at h2
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖v - x‖ = ‖(v + a - c) + (c - y) + ((y - x) - a)‖ := by congr 1; abel
      _ ≤ ‖v + a - c‖ + ‖c - y‖ + ‖(y - x) - a‖ := norm_add₃_le
      _ < ρ + ‖c - y‖ + (ε - (‖c - y‖ + ρ)) := by
          have : ‖(y - x) - a‖ < ε - (‖c - y‖ + ρ) := by rwa [norm_sub_rev]
          linarith
      _ = ε := by ring

end Translate

/-! ### Bump points of an sc-Banach space: all or nothing -/

section ScBanachBump

variable {E : ScBanach}

/-- **One bump point of an sc-Banach space gives all of them**: if `x₀ ∈ E` is a bump point of
the M-polyfold `E` (`MPolyfold.HasBumpAt`), then so is every `x ∈ E`, smooth or not.  (A bump at
`x₀` with support in `B(x₀, ε/2)` is moved to `x` by `exists_bump_translate`.)  This answers the
question of Findings, Chapter 5, item 163 for sc-Banach spaces: the bump points cannot be dense
without being everything. -/
theorem MPolyfold.HasBumpAt.scPolyfold_all {x₀ : E 0} (h : (scPolyfold E).HasBumpAt x₀)
    (x : E 0) : (scPolyfold E).HasBumpAt x := by
  intro U hU hxU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hxU
  obtain ⟨f, hf, hf0, hsupp⟩ := h (Metric.ball x₀ (ε / 2)) Metric.isOpen_ball
    (Metric.mem_ball_self (by positivity))
  obtain ⟨g, hg, hgx, hgsupp⟩ := exists_bump_translate hf hf0 hsupp x (ε := ε)
    (by rw [sub_self, norm_zero, zero_add]; linarith)
  exact ⟨g, hg, hgx, hgsupp.trans hball⟩

/-- **The bump points of an sc-Banach space are `∅` or everything.** -/
theorem MPolyfold.hasBumpAt_scPolyfold_all_or_nothing :
    {x | (scPolyfold E).HasBumpAt x} = ∅ ∨ {x | (scPolyfold E).HasBumpAt x} = univ := by
  rcases eq_empty_or_nonempty {x | (scPolyfold E).HasBumpAt x} with h | ⟨x₀, hx₀⟩
  · exact Or.inl h
  · exact Or.inr (eq_univ_of_forall fun x => hx₀.scPolyfold_all x)

/-- **Dense bump points of an sc-Banach space are all points.** -/
theorem MPolyfold.hasBumpAt_scPolyfold_of_dense (h : Dense {x | (scPolyfold E).HasBumpAt x})
    (x : E 0) : (scPolyfold E).HasBumpAt x := by
  obtain ⟨x₀, hx₀⟩ := h.nonempty
  exact hx₀.scPolyfold_all x

/-- **On an sc-Banach space the weak reading of "admits sc-smooth bump functions" (Definition
5.5.2 as written) gives the pointwise reading at every point** (Definition 5.3.1 read as
`f(x) ≠ 0`, which the proof of Proposition 5.5.3 uses), smooth or not: a bump `f ≢ 0` with support
in `B(x, ε/3)` is non-zero at some `y ∈ B(x, ε/3)`, and `exists_bump_translate` moves it to `x`
with support in `B(x, ε)`.  This removes the restriction to smooth points of
`AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth` (Findings, Chapter 5, item 161). -/
theorem MPolyfold.AdmitsBumpFunctionsWeak.admitsBumpFunctions_scPolyfold
    (hw : (scPolyfold E).AdmitsBumpFunctionsWeak) : (scPolyfold E).AdmitsBumpFunctions := by
  intro x U hU hxU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hxU
  obtain ⟨f, hf, hf0, hsupp⟩ := hw x (Metric.ball x (ε / 3)) Metric.isOpen_ball
    (Metric.mem_ball_self (by positivity))
  obtain ⟨y, hy⟩ : (support f).Nonempty := support_nonempty_iff.2 hf0
  have hyx : dist y x < ε / 3 := hsupp (subset_closure hy)
  obtain ⟨g, hg, hgx, hgsupp⟩ := exists_bump_translate hf hy hsupp x (ε := ε) (by
    rw [← dist_eq_norm, dist_comm]; linarith)
  exact ⟨g, hg, hgx, hgsupp.trans hball⟩

/-- **Weak = pointwise on an sc-Banach space.** -/
theorem MPolyfold.admitsBumpFunctionsWeak_iff_admitsBumpFunctions_scPolyfold :
    (scPolyfold E).AdmitsBumpFunctionsWeak ↔ (scPolyfold E).AdmitsBumpFunctions :=
  ⟨fun h => h.admitsBumpFunctions_scPolyfold, fun h => h.weak⟩

/-- The weak reading on an sc-Banach space makes every point a bump point (the form of
`AdmitsBumpFunctionsWeak.exists_bump_of_mem_smooth` without the smoothness hypothesis). -/
theorem MPolyfold.AdmitsBumpFunctionsWeak.exists_bump_scPolyfold
    (hw : (scPolyfold E).AdmitsBumpFunctionsWeak) (x : E 0) {U : Set (E 0)} (hU : IsOpen U)
    (hxU : x ∈ U) :
    ∃ f : E 0 → ℝ, (scPolyfold E).IsScSmoothMap realPolyfold f ∧ f x ≠ 0 ∧ tsupport f ⊆ U :=
  hw.admitsBumpFunctions_scPolyfold x U hU hxU

end ScBanachBump

/-! ### Local models and M-polyfolds whose model spaces have a bump point -/

section LocalModels

/-- **A local model `(O, C, E)` whose sc-Banach space `E` has a bump point has the sc-smooth bump
function property** (Definition 5.5.6): the bump of `E` at `x ∈ O` with support in `W`
(`HasBumpAt.scPolyfold_all`) is an sc-smooth function of `O` (its composition with every
retraction onto `O` is sc-smooth, by the chain rule), and its support in `O` lies in `W`. -/
theorem LocalModel.hasBumpProperty_of_hasBumpAt (M : LocalModel) {x₀ : M.E 0}
    (h : (scPolyfold M.E).HasBumpAt x₀) : M.HasBumpProperty := by
  intro x _ W hW hxW _
  obtain ⟨f, hf, hfx, hsupp⟩ := h.scPolyfold_all x W hW hxW
  have hfsc : IsScSmooth (E := M.E) (F := realSc) univ f := isScSmoothMap_scPolyfold_iff.1 hf
  refine ⟨f, ⟨mapsTo_univ _ _, fun R _ => ?_⟩, hfx, fun p hp => ?_⟩
  · exact IsScSmooth.comp R.isScDomain (isScDomain_univ _) hfsc R.isScSmooth (mapsTo_univ _ _)
  · exact hsupp (closure_mono inter_subset_right hp.1)

/-- A local model whose sc-Banach space admits sc-smooth bump functions in the weak reading
(Definition 5.5.2 as written) has the sc-smooth bump function property. -/
theorem LocalModel.hasBumpProperty_of_weak (M : LocalModel)
    (h : (scPolyfold M.E).AdmitsBumpFunctionsWeak) : M.HasBumpProperty :=
  M.hasBumpProperty_of_hasBumpAt (x₀ := 0) (h.admitsBumpFunctions_scPolyfold 0)

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **An M-polyfold admits sc-smooth bump functions (pointwise reading) as soon as every point
has a chart whose model sc-Banach space has a bump point** (Theorem 5.5.7 with
`LocalModel.hasBumpProperty_of_hasBumpAt`). -/
theorem MPolyfold.admitsBumpFunctions_of_model_hasBumpAt
    (h : ∀ x, ∃ φ : MChart X, PX.IsChart φ ∧ x ∈ φ.source ∧
      ∃ x₀, (scPolyfold φ.model.E).HasBumpAt x₀) :
    PX.AdmitsBumpFunctions := by
  refine theorem_5_34.2 ⟨{φ | PX.IsChart φ ∧ ∃ x₀, (scPolyfold φ.model.E).HasBumpAt x₀},
    fun φ hφ => hφ.1, fun x => ?_, fun φ hφ => ?_⟩
  · obtain ⟨φ, hφ, hx, hb⟩ := h x
    exact ⟨φ, ⟨hφ, hb⟩, hx⟩
  · obtain ⟨x₀, hx₀⟩ := hφ.2
    exact φ.model.hasBumpProperty_of_hasBumpAt hx₀

/-- **An M-polyfold whose model sc-Banach spaces admit sc-smooth bump functions in the weak
reading admits them in the pointwise reading**: for an M-polyfold the two readings of Definition
5.3.1/5.5.2 differ at most through the retracts, never through the model spaces. -/
theorem MPolyfold.admitsBumpFunctions_of_model_weak
    (h : ∀ x, ∃ φ : MChart X, PX.IsChart φ ∧ x ∈ φ.source ∧
      (scPolyfold φ.model.E).AdmitsBumpFunctionsWeak) :
    PX.AdmitsBumpFunctions :=
  MPolyfold.admitsBumpFunctions_of_model_hasBumpAt fun x => by
    obtain ⟨φ, hφ, hx, hw⟩ := h x
    exact ⟨φ, hφ, hx, 0, hw.admitsBumpFunctions_scPolyfold 0⟩

end LocalModels

end Polyfold
