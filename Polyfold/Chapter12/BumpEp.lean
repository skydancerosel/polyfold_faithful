import Polyfold.Chapter7.PartitionsOfUnity
import Polyfold.Chapter5.BumpWeakPointwise

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §12.3, p. 579:
**Definition 12.3.1** (2017: Definition 12.6) and **Theorem 12.3.2** (2017: Theorem 12.4):
sc-smooth bump functions on ep-groupoids.

# Sc-smooth bump functions on ep-groupoids

## The text, paraphrased

(Definition 12.3.1) An ep-groupoid `X` admits sc-smooth bump functions if for every object `x`
and every saturated open neighbourhood `U(x)` there is an sc-smooth `f : X → ℝ`, not identically
`0`, with support in `U(x)` and `f(y) = f(z)` whenever there is a morphism `y → z`.
(Theorem 12.3.2) (1) `X` admits sc-smooth bump functions iff the object M-polyfold does; (2) if
`X` admits them, then for every `x` and saturated open `U(x)` there is an sc-smooth bump function
`f : X → [0, 1]` with `f(x) = 1` and `supp f ⊆ U(x)`.  *Proof*: (1, ⇒) cut the ep-bump function off
to a `G_x`-invariant `W(x)` with `cl W(x) ⊆ V(x)` (natural action on `V(x)`): near a point of
`cl W(x) ∖ W(x)` the cut-off vanishes.  (1, ⇐) average an object bump function supported in
`W(x)` over `G_x` and extend it to the saturation by the morphisms; the properness of `cl V(x)`
makes the extension sc-smooth.  (2) the same with Part I's Proposition 5.5.3.

## What is formalized (namespace `Polyfold.EpGroupoid`)

* **Definition 12.3.1**: `AdmitsBumpFunctions` (as printed: `f` not identically zero) and
  `AdmitsBumpFunctionsPointwise` (`f(x) ≠ 0`, the reading of Part I's Definition 5.3.1 in the
  project, `MPolyfold.AdmitsBumpFunctions`); `AdmitsBumpFunctionsPointwise.weak`.
* The two steps of the proof: `exists_objBump_of_epBump` (cut-off, (1) ⇒) and
  `exists_epBump_of_objBump` (average and extension, (1) ⇐), with the averaging lemma
  `exists_natAverage` and the extension lemma `exists_invariant_extension`.
* **Theorem 12.3.2 (1)**: `theorem_12_3_2_1` (pointwise readings on both sides) and
  `theorem_12_3_2_1_weak` (the "not identically zero" readings on both sides).
* **Theorem 12.3.2 (2)**: `theorem_12_3_2_2` (from the pointwise reading), with the morphism
  invariance of `f` stated (it is part of being an ep-bump function).
* Witnesses: `admitsBumpFunctionsPointwise_of_objects` and
  `admitsBumpFunctionsPointwise_trivial_rn` (the trivial ep-groupoid on `ℝⁿ`).

## Reading

* **"not identically 0" versus "`f(x) ≠ 0`".**  Definition 12.3.1 says "not identically 0"; Part I's
  Definition 5.3.1 is read pointwise in this project (Findings, Chapter 5, item 41; whether the weak
  reading implies the pointwise one at non-smooth points is open there).  Theorem 12.3.2 (1) is
  proved for both readings, each on both sides: the text's proof of (⇒) gives a function non-zero
  at some point of `W(x)`, and at `x` when the ep-bump function is non-zero at `x`.  As printed
  (ep "not identically zero" ⇔ object pointwise), the forward implication would be Part I's open
  weak-to-pointwise question; the backward one holds (`AdmitsBumpFunctionsPointwise.weak`).
* **Averaging can cancel.**  The text averages an object bump function `f` over `G_x`; the average
  of a function taking both signs may vanish identically.  We average `f²` (sc-smooth, `≥ 0`), whose
  average is non-zero where `f` is; for (2) the function of Proposition 5.5.3 is already `≥ 0`.
* "`supp f ⊆ U`" is `tsupport f ⊆ U`; the morphism condition is `f (s φ) = f (t φ)`.
* The properness of `t : s⁻¹(cl V(x)) → X` is used only in (⇐), for the closedness of the
  saturation of the support (Proposition 7.5.10 (1), `isClosed_saturation_of_isProperSubset`).
-/

open Set Function Filter Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### Definition 12.3.1 -/

/-- **Definition 12.3.1, p. 579** (2017: Definition 12.6): the ep-groupoid `X` **admits sc-smooth
bump functions** if for every object `x` and every saturated open neighbourhood `U` of `x` there
is an sc-smooth `f : X → ℝ`, not identically `0`, with `supp f ⊆ U` and `f(s φ) = f(t φ)` for every
morphism `φ`. -/
def AdmitsBumpFunctions : Prop :=
  ∀ x (U : Set Obj), IsOpen U → X.IsSaturated U → x ∈ U →
    ∃ f : Obj → ℝ, X.PObj.IsScSmoothMap realPolyfold f ∧ f ≠ 0 ∧ tsupport f ⊆ U ∧
      ∀ φ : Mor, f (X.src φ) = f (X.tgt φ)

/-- **Definition 12.3.1, pointwise reading** (as Part I's Definition 5.3.1 in this project,
`MPolyfold.AdmitsBumpFunctions`): the bump function is non-zero at `x`. -/
def AdmitsBumpFunctionsPointwise : Prop :=
  ∀ x (U : Set Obj), IsOpen U → X.IsSaturated U → x ∈ U →
    ∃ f : Obj → ℝ, X.PObj.IsScSmoothMap realPolyfold f ∧ f x ≠ 0 ∧ tsupport f ⊆ U ∧
      ∀ φ : Mor, f (X.src φ) = f (X.tgt φ)

variable {X}

/-- The pointwise reading implies the reading as printed. -/
theorem AdmitsBumpFunctionsPointwise.weak (h : X.AdmitsBumpFunctionsPointwise) :
    X.AdmitsBumpFunctions := fun x U hU hsat hx => by
  obtain ⟨f, hf, hfx, hsupp, hinv⟩ := h x U hU hsat hx
  exact ⟨f, hf, fun h0 => hfx (congrFun h0 x), hsupp, hinv⟩

/-! ### Helpers -/

section Helpers

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}

/-- A function which is sc-smooth on an open neighbourhood of every point is sc-smooth. -/
private theorem isScSmoothMap_real_of_isScSmoothOn_nhds' {f : Z → ℝ}
    (h : ∀ y, ∃ N : Set Z, y ∈ N ∧ PZ.IsScSmoothOn realPolyfold f N) :
    PZ.IsScSmoothMap realPolyfold f := by
  refine isScSmoothMap_real_of_local fun y => ?_
  obtain ⟨N, hyN, hN⟩ := h y
  obtain ⟨φ, hφ, hyφ⟩ := PZ.exists_isChart_mem_source y
  have hVo : IsOpen (N ∩ φ.source) := hN.isOpen.inter φ.isOpen_source
  exact ⟨φ, N ∩ φ.source, hφ, hVo, ⟨hyN, hyφ⟩, inter_subset_right,
    hN.smooth φ realChart hφ isChart_realChart _ hVo subset_rfl (mapsTo_univ _ _)⟩

/-- The zero function is sc-smooth on every open set. -/
private theorem isScSmoothOn_real_zero {N : Set Z} (hN : IsOpen N) {f : Z → ℝ} (hf : EqOn f 0 N) :
    PZ.IsScSmoothOn realPolyfold f N :=
  ((isScSmoothMap_real_const (PX := PZ) 0).mono hN (subset_univ _)).congr fun _z hz => (hf hz).symm

/-- **Extension by zero**: a function sc-smooth on an open set containing its support is
sc-smooth. -/
private theorem isScSmoothMap_real_of_tsupport_subset' {f : Z → ℝ} {N : Set Z}
    (hf : PZ.IsScSmoothOn realPolyfold f N) (hN : tsupport f ⊆ N) :
    PZ.IsScSmoothMap realPolyfold f := by
  refine isScSmoothMap_real_of_isScSmoothOn_nhds' fun y => ?_
  by_cases hy : y ∈ N
  · exact ⟨N, hy, hf⟩
  · exact ⟨(tsupport f)ᶜ, fun h => hy (hN h), isScSmoothOn_real_zero
      (isClosed_tsupport f).isOpen_compl fun z hz => image_eq_zero_of_notMem_tsupport hz⟩

end Helpers

variable (X) in
/-- The saturation of an open set is open (`π` is open, Proposition 7.1.8). -/
theorem isOpen_saturation_of_isOpen {V : Set Obj} (hV : IsOpen V) : IsOpen (X.saturation V) :=
  (X.proposition_7_1_8 V hV).preimage X.continuous_π

variable (X) in
/-- A saturation is saturated. -/
theorem isSaturated_saturation (A : Set Obj) : X.IsSaturated (X.saturation A) := by
  change X.π ⁻¹' (X.π '' (X.π ⁻¹' (X.π '' A))) = X.π ⁻¹' (X.π '' A)
  rw [image_preimage_eq _ X.surjective_π]

/-- The saturation of a subset of a saturated set lies in it. -/
theorem saturation_subset_of_isSaturated {A U : Set Obj} (hU : X.IsSaturated U) (hAU : A ⊆ U) :
    X.saturation A ⊆ U := by
  rw [← hU]; exact preimage_mono (image_mono hAU)

/-- A function constant along morphisms is constant on orbits. -/
theorem eq_of_π_eq {f : Obj → ℝ} (hf : ∀ φ : Mor, f (X.src φ) = f (X.tgt φ)) {y z : Obj}
    (h : X.π y = X.π z) : f y = f z := by
  obtain ⟨φ, hs, ht⟩ := X.π_eq_π_iff.1 h
  rw [← hs, ← ht]; exact hf φ

/-! ### Averaging over `G_x` and extending to the saturation -/

section Average

/-- **The `G_x`-average** (proofs of Theorems 12.3.2 and 12.3.3): for an sc-smooth `g` supported
in an open `G_x`-invariant `V` with `cl V ⊆ U(x) = R.U`, the function
`h(y) = |G_x|⁻¹ ∑_k g(Φ(k)(y))` on `U(x)`, `0` off `U(x)`, is sc-smooth, supported in `V` and
`G_x`-invariant on `U(x)`. -/
theorem exists_natAverage {x : Obj} (R : X.NaturalRep x) {V : Set Obj}
    (hVinv : ∀ k, MapsTo (R.Φ k) V V) (hVcl : closure V ⊆ R.U) {g : Obj → ℝ}
    (hg : X.PObj.IsScSmoothMap realPolyfold g) (hgV : tsupport g ⊆ V) :
    ∃ h : Obj → ℝ, X.PObj.IsScSmoothMap realPolyfold h ∧ support h ⊆ V ∧
      (∀ k, ∀ y ∈ R.U, h (R.Φ k y) = h y) ∧
      ∀ y ∈ R.U, h y = (Nat.card (X.Isotropy x) : ℝ)⁻¹ * ∑ᶠ k, g (R.Φ k y) := by
  classical
  have := Fintype.ofFinite (X.Isotropy x)
  set c : ℝ := (Nat.card (X.Isotropy x) : ℝ)⁻¹ with hc
  let gk : X.Isotropy x → Obj → ℝ := fun k => R.U.indicator fun y => g (R.Φ k y)
  have hgk_eq : ∀ k, ∀ y ∈ R.U, gk k y = g (R.Φ k y) := fun k y hy => indicator_of_mem hy _
  have hgk_supp : ∀ k, support (gk k) ⊆ V := by
    intro k y hy
    by_cases hyR : y ∈ R.U
    · rw [mem_support, hgk_eq k y hyR] at hy
      have h1 := hVinv k⁻¹ (hgV (subset_tsupport g hy))
      rwa [R.Φ_inv_Φ k hyR] at h1
    · exact absurd (indicator_of_notMem hyR _) hy
  have hgk_sc : ∀ k, X.PObj.IsScSmoothMap realPolyfold (gk k) := fun k =>
    isScSmoothMap_real_of_tsupport_subset'
      ((MPolyfold.IsScSmoothOn.comp hg (R.isScDiffeoOn_Φ k).isScSmoothOn
        (mapsTo_univ _ _)).congr fun y hy => (hgk_eq k y hy).symm)
      ((closure_mono (hgk_supp k)).trans hVcl)
  refine ⟨fun y => c * ∑ k, gk k y, (isScSmoothMap_real_const _).real_mul
    (isScSmoothMap_real_finsetSum Finset.univ fun k _ => hgk_sc k), ?_, ?_, ?_⟩
  · refine support_subset_iff'.2 fun y hy => ?_
    rw [Finset.sum_eq_zero fun k _ => notMem_support.1 fun h => hy (hgk_supp k h), mul_zero]
  · intro k' y hy
    have hΦy := R.mapsTo_Φ k' hy
    have hsum : ∑ k, gk k (R.Φ k' y) = ∑ k, gk k y := by
      calc ∑ k, gk k (R.Φ k' y) = ∑ k, gk (k * k') y := Finset.sum_congr rfl fun k _ => by
            rw [hgk_eq k _ hΦy, hgk_eq (k * k') y hy, R.Φ_mul k k' y hy]
        _ = ∑ k, gk k y := Equiv.sum_comp (Equiv.mulRight k') fun k => gk k y
    simp only [hsum]
  · intro y hy
    rw [finsum_eq_sum_of_fintype]
    exact congrArg (c * ·) (Finset.sum_congr rfl fun k _ => hgk_eq k y hy)

/-- **The extension to the saturation** (proofs of Theorems 12.3.2 and 12.3.3): a `G_x`-invariant
sc-smooth `h` supported in `V`, `cl V ⊆ U(x)` proper, extends to an sc-smooth `β : X → ℝ` constant
along morphisms, equal to `h` on `U(x)` and supported in the saturation of `cl V`. -/
theorem exists_invariant_extension {x : Obj} (R : X.NaturalRep x) {V : Set Obj}
    (hVcl : closure V ⊆ R.U) (hVprop : X.IsProperSubset (closure V)) {h : Obj → ℝ}
    (hh : X.PObj.IsScSmoothMap realPolyfold h) (hhV : support h ⊆ V)
    (hinv : ∀ k, ∀ y ∈ R.U, h (R.Φ k y) = h y) :
    ∃ β : Obj → ℝ, X.PObj.IsScSmoothMap realPolyfold β ∧ (∀ φ : Mor, β (X.src φ) = β (X.tgt φ)) ∧
      (∀ y ∈ R.U, β y = h y) ∧ tsupport β ⊆ X.saturation (closure V) ∧
      ∀ y, β y ∈ h '' R.U ∪ {0} := by
  classical
  have hts : tsupport h ⊆ closure V := closure_mono hhV
  have hprop : X.IsProperSubset (tsupport h) := hVprop.of_subset hts (isClosed_tsupport h)
  refine ⟨X.orbitExtension R h ∘ X.π,
    X.isScSmoothMap_orbitExtension R hh hinv (hts.trans hVcl) hprop,
    fun φ => by simp only [Function.comp_apply, X.π_src_eq_π_tgt],
    fun y hy => X.orbitExtension_π R hinv hy, ?_, fun y => ?_⟩
  · refine closure_minimal ?_ (X.isClosed_saturation_of_isProperSubset hVprop)
    intro y hy
    obtain ⟨w, hw, hwy⟩ := X.support_orbitExtension_subset R h hy
    exact ⟨w, subset_closure (hhV hw.2), hwy⟩
  · change X.orbitExtension R h (X.π y) ∈ _
    rw [orbitExtension]
    split_ifs with hy
    · exact Or.inl ⟨_, hy.choose_spec.1, rfl⟩
    · exact Or.inr rfl

end Average

/-! ### The two directions of Theorem 12.3.2 (1) -/

section Directions

/-- **Theorem 12.3.2 (1), (⇒), the cut-off**: an ep-bump function `f` for the saturation of an
invariant `W(x)` (with `cl W(x) ⊆ U(x)` carrying the natural action), cut off to `W(x)`, is an
sc-smooth function of the object M-polyfold, non-zero wherever `f` is non-zero on `W(x)`, with
support in `cl W(x)`. -/
theorem exists_objBump_of_epBump {x : Obj} (R : X.NaturalRep x) {V : Set Obj} (hVo : IsOpen V)
    (hVinv : ∀ k, MapsTo (R.Φ k) V V) (hVcl : closure V ⊆ R.U) {f : Obj → ℝ}
    (hf : X.PObj.IsScSmoothMap realPolyfold f) (hfV : tsupport f ⊆ X.saturation V)
    (hfinv : ∀ φ : Mor, f (X.src φ) = f (X.tgt φ)) :
    X.PObj.IsScSmoothMap realPolyfold (V.indicator f) ∧ tsupport (V.indicator f) ⊆ closure V ∧
      (f ≠ 0 → V.indicator f ≠ 0) ∧ ∀ y ∈ V, V.indicator f y = f y := by
  have hsupp : tsupport (V.indicator f) ⊆ closure V :=
    closure_mono (support_indicator_subset)
  refine ⟨isScSmoothMap_real_of_isScSmoothOn_nhds' fun y => ?_, hsupp, fun hne => ?_,
    fun y hy => indicator_of_mem hy f⟩
  · by_cases hyV : y ∈ V
    · exact ⟨V, hyV, (hf.mono hVo (subset_univ _)).congr fun z hz => (indicator_of_mem hz f).symm⟩
    by_cases hycl : y ∈ closure V
    · -- `y ∈ cl W(x) ∖ W(x)` is not in `supp f`: otherwise it is isomorphic to a point of
      -- `W(x)`, hence in `W(x)` by invariance (Theorem 7.1.13 (3))
      have hyf : y ∉ tsupport f := fun hy =>
        hyV (mem_of_π_mem_image_of_invariant R (subset_closure.trans hVcl) hVinv (hVcl hycl)
          (hfV hy))
      refine ⟨(tsupport f)ᶜ, hyf, isScSmoothOn_real_zero (isClosed_tsupport f).isOpen_compl
        fun z hz => ?_⟩
      by_cases hzV : z ∈ V
      · rw [indicator_of_mem hzV]; exact image_eq_zero_of_notMem_tsupport hz
      · exact indicator_of_notMem hzV f
    · exact ⟨(closure V)ᶜ, hycl, isScSmoothOn_real_zero isClosed_closure.isOpen_compl
        fun z hz => indicator_of_notMem (fun h => hz (subset_closure h)) f⟩
  · obtain ⟨z, hz⟩ : ∃ z, f z ≠ 0 := by
      by_contra hall
      exact hne (funext fun z => not_not.1 fun h => hall ⟨z, h⟩)
    obtain ⟨y, hyV, hyz⟩ := hfV (subset_tsupport f hz)
    intro h0
    have hfy : f y = f z := eq_of_π_eq hfinv hyz
    have := congrFun h0 y
    rw [indicator_of_mem hyV] at this
    exact hz (hfy ▸ this)

/-- **Theorem 12.3.2 (1), (⇐), averaging and extension**: an object bump function `g` supported in
an invariant `W(x)` (with `cl W(x)` proper inside `U(x)` carrying the natural action) gives an
ep-bump function `β ≥ 0`, constant along morphisms, supported in the saturation of `cl W(x)`, with
`β(y) ≥ |G_x|⁻¹ g(y)²` on `U(x)`. -/
theorem exists_epBump_of_objBump {x : Obj} (R : X.NaturalRep x) {V : Set Obj}
    (hVinv : ∀ k, MapsTo (R.Φ k) V V) (hVcl : closure V ⊆ R.U)
    (hVprop : X.IsProperSubset (closure V)) {g : Obj → ℝ}
    (hg : X.PObj.IsScSmoothMap realPolyfold g) (hgV : tsupport g ⊆ V) :
    ∃ β : Obj → ℝ, X.PObj.IsScSmoothMap realPolyfold β ∧ (∀ φ : Mor, β (X.src φ) = β (X.tgt φ)) ∧
      tsupport β ⊆ X.saturation (closure V) ∧
      ∀ y ∈ R.U, (Nat.card (X.Isotropy x) : ℝ)⁻¹ * g y ^ 2 ≤ β y := by
  have hg2 : X.PObj.IsScSmoothMap realPolyfold (fun y => g y ^ 2) :=
    hg.comp_contDiff (σ := fun s => s ^ 2) (contDiff_id.pow 2)
  have hg2V : tsupport (fun y => g y ^ 2) ⊆ V := (tsupport_comp_subset (g := fun s : ℝ => s ^ 2)
    (by norm_num) g).trans hgV
  obtain ⟨h, hh, hhV, hhinv, hheq⟩ := exists_natAverage R hVinv hVcl hg2 hg2V
  obtain ⟨β, hβ, hβinv, hβh, hβsupp, -⟩ := exists_invariant_extension R hVcl hVprop hh hhV hhinv
  refine ⟨β, hβ, hβinv, hβsupp, fun y hy => ?_⟩
  classical
  have := Fintype.ofFinite (X.Isotropy x)
  rw [hβh y hy, hheq y hy, finsum_eq_sum_of_fintype]
  have hc : (0 : ℝ) ≤ (Nat.card (X.Isotropy x) : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  refine mul_le_mul_of_nonneg_left ?_ hc
  have h1 : g y ^ 2 = g (R.Φ 1 y) ^ 2 := by rw [R.Φ_one y hy]
  rw [h1]
  exact Finset.single_le_sum (f := fun k => g (R.Φ k y) ^ 2) (fun k _ => sq_nonneg _)
    (Finset.mem_univ 1)

end Directions

/-! ### Theorem 12.3.2 -/

/-- **Theorem 12.3.2 (1), p. 579** (2017: Theorem 12.4 (1)), pointwise readings: the ep-groupoid `X`
admits sc-smooth bump functions (Definition 12.3.1 read with `f(x) ≠ 0`) iff its object
M-polyfold does (Part I's Definition 5.3.1, read with `f(x) ≠ 0`). -/
theorem theorem_12_3_2_1 : X.AdmitsBumpFunctionsPointwise ↔ X.PObj.AdmitsBumpFunctions := by
  constructor
  · intro h x U hU hx
    obtain ⟨R, V, hVo, hxV, hVinv, hVcl, hRU, -⟩ := exists_invariant_nhds_of_isOpen X x hU hx
    obtain ⟨f, hf, hfx, hfV, hfinv⟩ := h x (X.saturation V) (X.isOpen_saturation_of_isOpen hVo)
      (X.isSaturated_saturation V) (X.subset_saturation V hxV)
    obtain ⟨hsc, hsupp, -, heq⟩ := exists_objBump_of_epBump R hVo hVinv hVcl hf hfV hfinv
    exact ⟨V.indicator f, hsc, by rw [heq x hxV]; exact hfx, hsupp.trans (hVcl.trans hRU)⟩
  · intro h x U hU hsat hx
    obtain ⟨R, V, hVo, hxV, hVinv, hVcl, hRU, hprop⟩ := exists_invariant_nhds_of_isOpen X x hU hx
    obtain ⟨g, hg, hgx, hgV⟩ := h x V hVo hxV
    obtain ⟨β, hβ, hβinv, hβsupp, hβge⟩ := exists_epBump_of_objBump R hVinv hVcl hprop hg hgV
    refine ⟨β, hβ, fun h0 => ?_, hβsupp.trans (saturation_subset_of_isSaturated hsat
      (hVcl.trans hRU)), hβinv⟩
    have h1 := hβge x R.mem_U
    rw [h0] at h1
    have h2 : 0 < (Nat.card (X.Isotropy x) : ℝ)⁻¹ * g x ^ 2 :=
      mul_pos (inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)) (pow_pos_of_ne_zero hgx)
    linarith
where
  pow_pos_of_ne_zero {a : ℝ} (ha : a ≠ 0) : 0 < a ^ 2 := by positivity

/-- **Theorem 12.3.2 (1), p. 579**, the readings "not identically zero" on both sides: `X` admits
sc-smooth bump functions (Definition 12.3.1 as printed) iff the object M-polyfold admits them in
the reading of Part I's Definition 5.5.2 (`MPolyfold.AdmitsBumpFunctionsWeak`). -/
theorem theorem_12_3_2_1_weak : X.AdmitsBumpFunctions ↔ X.PObj.AdmitsBumpFunctionsWeak := by
  constructor
  · intro h x U hU hx
    obtain ⟨R, V, hVo, hxV, hVinv, hVcl, hRU, -⟩ := exists_invariant_nhds_of_isOpen X x hU hx
    obtain ⟨f, hf, hfne, hfV, hfinv⟩ := h x (X.saturation V) (X.isOpen_saturation_of_isOpen hVo)
      (X.isSaturated_saturation V) (X.subset_saturation V hxV)
    obtain ⟨hsc, hsupp, hne, -⟩ := exists_objBump_of_epBump R hVo hVinv hVcl hf hfV hfinv
    exact ⟨V.indicator f, hsc, hne hfne, hsupp.trans (hVcl.trans hRU)⟩
  · intro h x U hU hsat hx
    obtain ⟨R, V, hVo, hxV, hVinv, hVcl, hRU, hprop⟩ := exists_invariant_nhds_of_isOpen X x hU hx
    obtain ⟨g, hg, hgne, hgV⟩ := h x V hVo hxV
    obtain ⟨β, hβ, hβinv, hβsupp, hβge⟩ := exists_epBump_of_objBump R hVinv hVcl hprop hg hgV
    refine ⟨β, hβ, fun h0 => ?_, hβsupp.trans (saturation_subset_of_isSaturated hsat
      (hVcl.trans hRU)), hβinv⟩
    obtain ⟨y, hy⟩ : ∃ y, g y ≠ 0 := by
      by_contra hall
      exact hgne (funext fun z => not_not.1 fun h => hall ⟨z, h⟩)
    have hyV : y ∈ V := hgV (subset_tsupport g hy)
    have h1 := hβge y (subset_closure.trans hVcl hyV)
    rw [congrFun h0 y] at h1
    have h2 : 0 < (Nat.card (X.Isotropy x) : ℝ)⁻¹ * g y ^ 2 :=
      mul_pos (inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)) (by positivity)
    change _ ≤ (0 : ℝ) at h1
    linarith

/-- **Theorem 12.3.2 (2), p. 579** (2017: Theorem 12.4 (2)): if `X` admits sc-smooth bump functions
(pointwise reading), then for every `x` and every saturated open `U ∋ x` there is an sc-smooth
`f : X → [0, 1]`, constant along morphisms, with `f(x) = 1` and `supp f ⊆ U`.  The proof is the
text's: Part I's Proposition 5.5.3 on the object M-polyfold inside an invariant `W(x)`, averaged
over `G_x` and extended to the saturation. -/
theorem theorem_12_3_2_2 (h : X.AdmitsBumpFunctionsPointwise) {x : Obj} {U : Set Obj}
    (hU : IsOpen U) (hsat : X.IsSaturated U) (hx : x ∈ U) :
    ∃ f : Obj → ℝ, X.PObj.IsScSmoothMap realPolyfold f ∧ (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
      f x = 1 ∧ tsupport f ⊆ U ∧ ∀ φ : Mor, f (X.src φ) = f (X.tgt φ) := by
  classical
  obtain ⟨R, V, hVo, hxV, hVinv, hVcl, hRU, hprop⟩ := exists_invariant_nhds_of_isOpen X x hU hx
  obtain ⟨g, hg, hg01, hgx, hgV, -⟩ := proposition_5_5_3 (theorem_12_3_2_1.1 h) hVo hxV
  obtain ⟨h', hh, hhV, hhinv, hheq⟩ := exists_natAverage R hVinv hVcl hg hgV
  obtain ⟨β, hβ, hβinv, hβh, hβsupp, hβval⟩ :=
    exists_invariant_extension R hVcl hprop hh hhV hhinv
  have := Fintype.ofFinite (X.Isotropy x)
  have hcard : (0 : ℝ) < Fintype.card (X.Isotropy x) := Nat.cast_pos.2 Fintype.card_pos
  have hh01 : ∀ y ∈ R.U, h' y ∈ Icc (0 : ℝ) 1 := fun y hy => by
    rw [hheq y hy, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
    have hle : ∑ k, g (R.Φ k y) ≤ Fintype.card (X.Isotropy x) := by
      calc ∑ k, g (R.Φ k y) ≤ ∑ _k : X.Isotropy x, (1 : ℝ) :=
            Finset.sum_le_sum fun k _ => (hg01 _).2
        _ = Fintype.card (X.Isotropy x) := by simp
    have h0 : 0 ≤ ∑ k, g (R.Φ k y) := Finset.sum_nonneg fun k _ => (hg01 _).1
    refine ⟨mul_nonneg (inv_nonneg.2 hcard.le) h0, ?_⟩
    rw [inv_mul_le_iff₀ hcard, mul_one]
    exact hle
  refine ⟨β, hβ, fun y => ?_, ?_, hβsupp.trans (saturation_subset_of_isSaturated hsat
    (hVcl.trans hRU)), hβinv⟩
  · rcases hβval y with ⟨z, hz, hzy⟩ | hy0
    · rw [← hzy]; exact hh01 z hz
    · rw [mem_singleton_iff.1 hy0]; exact ⟨le_rfl, zero_le_one⟩
  · rw [hβh x R.mem_U, hheq x R.mem_U, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
    simp only [R.Φ_self, hgx, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hcard.ne'

/-! ### Satisfiability -/

/-- **Definition 12.3.1 is satisfiable**: by Theorem 12.3.2 (1) it holds for every ep-groupoid
whose object M-polyfold admits bump functions, e.g. the trivial ep-groupoid on `ℝⁿ` (built on a
Hilbert space, Part I's `MPolyfold.admitsBumpFunctions_of_hilbert`). -/
theorem admitsBumpFunctionsPointwise_of_objects (h : X.PObj.AdmitsBumpFunctions) :
    X.AdmitsBumpFunctionsPointwise :=
  theorem_12_3_2_1.2 h

/-- **The hypotheses of Theorems 12.3.2 (2) and 12.3.3 on `X` are satisfiable**: the trivial
ep-groupoid on `ℝⁿ` admits sc-smooth bump functions (pointwise reading) and has paracompact orbit
space (Part I partitions of unity on `ℝⁿ` give bump functions). -/
theorem admitsBumpFunctionsPointwise_trivial_rn (n : ℕ) :
    (trivial (rnPolyfold n)).AdmitsBumpFunctionsPointwise ∧
      (trivial (rnPolyfold n)).HasParacompactOrbitSpace :=
  ⟨admitsBumpFunctionsPointwise_of_objects (theorem_7_5_7_hypotheses_rn n).2.admitsBumpFunctions,
    (theorem_7_5_7_hypotheses_rn n).1⟩

end EpGroupoid

end Polyfold
