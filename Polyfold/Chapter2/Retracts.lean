import Polyfold.Chapter1.ChainRule

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.1,
Definitions 2.1.1, 2.1.3, 2.1.12, 2.1.14 (preprint 2.1, 2.3, 2.5, 2.7), Propositions 2.1.11, 2.1.13 (preprint 2.4, 2.6) and Theorem 2.1.15 (preprint 2.8); from §2.2,
Proposition 2.3.1 (preprint 2.10) (the two ways of producing new retracts, used for charts).

# Sc-smooth retractions and retracts

## The text, paraphrased

(Definition 2.1.1 (preprint 2.1)) Let `U` be a relatively open subset of a partial quadrant `C` in `E`.  An
sc-smooth map `r : U → U` with `r ∘ r = r` is an sc-smooth retraction on `U`.  (Definition 2.1.3 (preprint 2.3))
`(O, C, E)` is an sc-smooth retract if `O = r(U)` for such an `r`.  For `x ∈ O₁`, `Dr(x)` is a
projection.  (Proposition 2.1.11 (preprint 2.4)) If `r : U → U` and `r' : U' → U'` are retractions with
`r(U) = r'(U') = O`, then `Tr(TU) = Tr'(TU')`.  *Proof*: `r' ∘ r = r` and `r ∘ r' = r'`; if
`(x, h) = Tr(y, k)` then `x ∈ O₁ ⊆ U'₁` and `Tr'(x, h) = T(r' ∘ r)(y, k) = (x, h)`.
(Definition 2.1.12 (preprint 2.5)) `TO := Tr(TU)`, for any `r` onto `O`; explicitly
`TO = {(r(x), Dr(x)h) | x ∈ U₁, h ∈ E}`.  (Proposition 2.1.13 (preprint 2.6)) For `f : O → O'` and retractions `r`,
`s` onto `O`: (1) `f ∘ r` sc-smooth iff `f ∘ s` sc-smooth; (2) `T(f ∘ r) = T(f ∘ s)` on `TO`;
(3) `T(f ∘ r)` maps `TO` into `TO'`.  (Definition 2.1.14 (preprint 2.7)) `f : O → O'` is sc-smooth if `f ∘ r` is
sc-smooth for a retraction `r` onto `O`; `Tf := T(f ∘ r)|TO`.  (Theorem 2.1.15 (preprint 2.8)) Compositions of
sc-smooth maps between retracts are sc-smooth and `T(g ∘ f) = Tg ∘ Tf`.  (Proposition 2.3.1 (preprint 2.10))
(1) An open subset `O'` of a retract `O` is a retract (restrict `r` to `r⁻¹(O')`); (2) if
`s : V → V` is sc-smooth on an open `V ⊆ O` with `s ∘ s = s`, then `s(V)` is a retract
(`ρ = s ∘ r`).

## What is formalized

* `Polyfold.ScRetraction E C` (**Definition 2.1.1 (preprint 2.1)**): the data `(U, r)` of an sc-smooth retraction on
  a relatively open subset `U` of the partial quadrant `C`; `ScRetraction.retract R = r(U)`;
  `Polyfold.IsScRetract E C O` (**Definition 2.1.3 (preprint 2.3)**): `O = r(U)` for some `R`.
* `ScRetraction.tangent R = Tr(TU)`, with the fixed-point description
  `ScRetraction.mem_tangent_iff : p ∈ Tr(TU) ↔ p ∈ TU ∧ Tr(p) = p`, and
  `ScRetraction.mem_tangent_iff_mem_range`: for `x ∈ O₁`, `(x, h) ∈ TO ↔ h ∈ range Dr(x)`;
  `ScRetraction.scDeriv_comp_self`: `Dr(x) ∘ Dr(x) = Dr(x)` for `x ∈ O₁`.
* `Polyfold.proposition_2_1_11` (**Proposition 2.1.11 (preprint 2.4)**), `Polyfold.retractTangent E C O` (`TO`,
  **Definition 2.1.12 (preprint 2.5)**) with `retractTangent_eq`, and `Polyfold.tangentSpace E C O x = T_xO`
  (Definition 2.3.12 (preprint 2.17)'s fibre).
* `Polyfold.proposition_2_1_13_one`, `proposition_2_1_13_two`, `proposition_2_1_13_three` (**Proposition 2.1.13 (preprint 2.6)**);
  `Polyfold.IsScSmoothRetractMap E C O E' C' O' f` (**Definition 2.1.14 (preprint 2.7)**, in the form "for every
  retraction `r` onto `O`, `f ∘ r` is sc-smooth"; `isScSmoothRetractMap_iff_exists` recovers the
  text's "for one `r`"), `Polyfold.retractTangentMap E C O f` (`Tf`) with
  `retractTangentMap_eqOn`.
* `Polyfold.theorem_2_1_15` (**Theorem 2.1.15 (preprint 2.8)**, the chain rule for retracts), split as
  `IsScSmoothRetractMap.comp` and `retractTangentMap_comp`.
* `Polyfold.proposition_2_3_1_one`, `Polyfold.proposition_2_3_1_two` (**Proposition 2.3.1 (preprint 2.10)**),
  `IsScSmoothRetractMap.restrict` (restriction to an open subset of the source retract) and
  `IsScSmoothRetractMap.of_locally` (sc-smoothness between retracts is local).
* `Polyfold.LocalModel`: a triple `(O, C, E)` with `IsScRetract E C O`, the local models of
  M-polyfold charts; `LocalModel.restrict` is Proposition 2.3.1 (preprint 2.10) (1).
* Infrastructure on the sc-calculus the text uses silently: `IsSck.of_subset`
  (restriction of sc^k maps to smaller domains), `IsScSmooth.congr`, and
  `IsScSmooth.of_locally` (sc-smoothness is a local property).

## What the text leaves implicit, and the choices made

* A retraction is a total map `r : E₀ → E₀`; only its values on `U` matter.  `r(U) ⊆ U` is a
  field (`mapsTo`), and `r ∘ r = r` is required on `U`.
* `TO` is a subset of `TE₀ = E₁ × E₀`; `Tr` is `tangentMap U r`, built from the chosen derivative
  `scDeriv U r`, which is the derivative of the text on `U₁` (Chapter 1).  The description of `TO`
  as the fixed-point set of `Tr` on `TU` is not in the text but is what its proofs use
  ("`Tr'(x, h) = (x, h)`").
* Definition 2.1.14 (preprint 2.7) quantifies over one retraction and appeals to Proposition 2.1.13 (preprint 2.6) for independence.
  `IsScSmoothRetractMap` quantifies over all retractions onto `O`, and includes `f(O) ⊆ O'`; for
  an actual retract `O` the two readings agree (`isScSmoothRetractMap_iff_exists`).  The target
  `(O', C', E')` enters only through `f(O) ⊆ O'` and `Tf(TO) ⊆ TO'`.
* `Tf` is defined for every `f` and every `(O, C, E)` (through a choice of retraction; junk
  otherwise); on `TO` it is `T(f ∘ r)` for every `r` onto `O` (`retractTangentMap_eqOn`).
* The text's proof of Proposition 2.1.13 (preprint 2.6) (2) uses `(x, h) = Ts(x, h)` for `(x, h) ∈ TO`, i.e. the
  fixed-point description; its proof of (3) uses `ρ ∘ f ∘ r = f ∘ r` and the chain rule exactly as
  formalized.  Theorem 2.1.15 (preprint 2.8) has no proof in the text ("follows from Theorem 1.21"); the proof here
  writes `g ∘ f ∘ r = (g ∘ r') ∘ (f ∘ r)` on `U` and applies the chain rule.
* Proposition 2.3.1 (preprint 2.10) (1) needs the restriction of an sc-smooth map to a smaller relatively open set
  to be sc-smooth (`IsSck.of_subset`), which the text takes for granted; the point is that the
  tangent map is built from a chosen derivative and the choices on `U` and `U'` agree on `U'₁`.
* In Proposition 2.3.1 (preprint 2.10) (2) "`s : V → V` sc-smooth" is read as sc-smooth between the retracts
  `(V, C, E) → (V, C, E)` (Definition 2.1.14 (preprint 2.7)), as the proof does ("`ρ = s ∘ r` is sc-smooth").
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

variable {E E' E'' : ScBanach}

/-! ### Restriction and locality of sc^k maps -/

section Restriction

variable {U U' : Set (E 0)} {f : E 0 → E' 0}

lemma IsSc1With.of_subset {D : E 1 → E 0 →L[ℝ] E' 0} (h : IsSc1With U f D) (hU' : U' ⊆ U) :
    IsSc1With U' f D where
  isSc0 := h.isSc0.mono hU'
  hasFDerivWithinAt x hx := (h.hasFDerivWithinAt x (E.lvlSet_mono hU' 1 hx)).mono
    (E.lvlSet_mono hU' 1)
  tangent_isSc0 := h.tangent_isSc0.mono (E.tangentSet_mono hU')

lemma IsSc1.of_subset (h : IsSc1 U f) (hU' : U' ⊆ U) : IsSc1 U' f :=
  ⟨_, h.isSc1With_scDeriv.of_subset hU'⟩

/-- On a smaller domain `U' ⊆ U` with unique differentiability, the tangent maps built on `U` and
on `U'` agree on `TU'`. -/
lemma IsSc1.tangentMap_eqOn_of_subset (h : IsSc1 U f) (hU' : IsScDomain E U') (hsub : U' ⊆ U) :
    EqOn (tangentMap U' f) (tangentMap U f) (E.tangentSet U') :=
  IsSc1.tangentMap_eqOn (h.isSc1With_scDeriv.of_subset hsub) (hU'.uniqueDiffWithinAt 1)

/-- sc^k maps restrict to smaller domains (with unique differentiability). -/
theorem IsSck.of_subset : ∀ {k : ℕ} {E E' : ScBanach} {U U' : Set (E 0)} {f : E 0 → E' 0},
    IsScDomain E U' → U' ⊆ U → IsSck k E E' U f → IsSck k E E' U' f
  | 0, _, _, _, _, _, _, hsub, h => IsSc0.mono h hsub
  | k + 1, _, _, _, _, _, hU', hsub, h => by
    refine ⟨h.1.of_subset hsub, ?_⟩
    have := IsSck.of_subset (k := k) hU'.tangentSet (E := _) (ScBanach.tangentSet_mono _ hsub) h.2
    exact IsSck.congr hU'.tangentSet (h.1.tangentMap_eqOn_of_subset hU' hsub).symm this

theorem IsScSmooth.of_subset (hU' : IsScDomain E U') (hsub : U' ⊆ U) (h : IsScSmooth U f) :
    IsScSmooth U' f := fun k => (h k).of_subset hU' hsub

theorem IsScSmooth.congr (hU : IsScDomain E U) {f' : E 0 → E' 0} (hff' : EqOn f f' U)
    (h : IsScSmooth U f) : IsScSmooth U f' := fun k => IsSck.congr hU hff' (h k)

/-- The intersection of a relatively open subset of a partial quadrant with an open set. -/
lemma IsRelOpenInQuadrant.inter_isOpen {C : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    {W : Set (E 0)} (hW : IsOpen W) : IsRelOpenInQuadrant E C (U ∩ W) := by
  obtain ⟨O, hO, rfl⟩ := hU.relOpen
  exact ⟨hU.isPartialQuadrant, O ∩ W, hO.inter hW, by rw [inter_right_comm]⟩

lemma IsScDomain.inter_isOpen (hU : IsScDomain E U) {W : Set (E 0)} (hW : IsOpen W) :
    IsScDomain E (U ∩ W) where
  relOpenConvex m := by
    obtain ⟨O, C, hO, hC, hU⟩ := hU.relOpenConvex m
    exact ⟨O ∩ E.lvlSet W m, C, hO.inter (E.isOpen_lvlSet hW m), hC, by
      rw [ScBanach.lvlSet_inter, hU, inter_right_comm]⟩
  uniqueDiffWithinAt m x hx := by
    rw [ScBanach.lvlSet_inter] at hx ⊢
    exact (hU.uniqueDiffWithinAt m x hx.1).inter ((E.isOpen_lvlSet hW m).mem_nhds hx.2)

/-- `T(U ∩ W) = TU ∩ (W₁ × E₀)`. -/
lemma ScBanach.tangentSet_inter_isOpen (E : ScBanach) (U W : Set (E 0)) :
    E.tangentSet (U ∩ W) = E.tangentSet U ∩ (E.lvlSet W 1 ×ˢ univ) := by
  ext p
  change p.1 ∈ E.lvlSet (U ∩ W) 1 ↔ p.1 ∈ E.lvlSet U 1 ∧ p ∈ E.lvlSet W 1 ×ˢ univ
  rw [ScBanach.lvlSet_inter, mem_prod]
  simp only [mem_inter_iff, mem_univ, and_true]

/-- sc⁰ is a local property. -/
lemma IsSc0.of_locally (h : ∀ x ∈ U, ∃ W : Set (E 0), IsOpen W ∧ x ∈ W ∧ IsSc0 E E' (U ∩ W) f) :
    IsSc0 E E' U f where
  mem_range m x hx := by
    obtain ⟨W, _, hxW, hW⟩ := h _ hx
    exact hW.mem_range m x ⟨hx, hxW⟩
  continuousOn m x hx := by
    obtain ⟨W, hWo, hxW, hW⟩ := h _ hx
    have := hW.continuousOn m x ⟨hx, hxW⟩
    rw [ScBanach.lvlSet_inter] at this
    exact (this.mono_of_mem_nhdsWithin (inter_mem_nhdsWithin _
      ((E.isOpen_lvlSet hWo m).mem_nhds hxW)))

/-- Two sc¹ structures agreeing near `x` have the same derivative at `x` (on a domain with unique
differentiability). -/
lemma IsSc1With.eq_of_eq_near {D D' : E 1 → E 0 →L[ℝ] E' 0} {W W' : Set (E 0)} (hW : IsOpen W)
    (hW' : IsOpen W') (hU : IsScDomain E U) (h : IsSc1With (U ∩ W) f D)
    (h' : IsSc1With (U ∩ W') f D') {x : E 1} (hx : x ∈ E.lvlSet U 1) (hxW : x ∈ E.lvlSet W 1)
    (hxW' : x ∈ E.lvlSet W' 1) : D x = D' x := by
  have h1 : HasFDerivWithinAt (f ∘ E.toBase 1) ((D x).comp (E.toBase 1)) (E.lvlSet U 1) x := by
    have := h.hasFDerivWithinAt x (by rw [ScBanach.lvlSet_inter]; exact ⟨hx, hxW⟩)
    rw [ScBanach.lvlSet_inter] at this
    exact this.mono_of_mem_nhdsWithin (inter_mem_nhdsWithin _
      ((E.isOpen_lvlSet hW 1).mem_nhds hxW))
  have h2 : HasFDerivWithinAt (f ∘ E.toBase 1) ((D' x).comp (E.toBase 1)) (E.lvlSet U 1) x := by
    have := h'.hasFDerivWithinAt x (by rw [ScBanach.lvlSet_inter]; exact ⟨hx, hxW'⟩)
    rw [ScBanach.lvlSet_inter] at this
    exact this.mono_of_mem_nhdsWithin (inter_mem_nhdsWithin _
      ((E.isOpen_lvlSet hW' 1).mem_nhds hxW'))
  have h12 := (hU.uniqueDiffWithinAt 1 x hx).eq h1 h2
  have hd : Dense (Submodule.span ℝ (range (E.toBase 1)) : Set (E 0)) :=
    Dense.mono Submodule.subset_span (E.denseRange_inclK 0 1)
  refine ContinuousLinearMap.ext_on hd ?_
  rintro _ ⟨y, rfl⟩
  exact congrArg (fun L : E 1 →L[ℝ] E' 0 => L y) h12

/-- sc¹ is a local property (on a domain with unique differentiability). -/
theorem IsSc1.of_locally (hU : IsScDomain E U)
    (h : ∀ x ∈ U, ∃ W : Set (E 0), IsOpen W ∧ x ∈ W ∧ IsSc1 (U ∩ W) f) : IsSc1 U f := by
  classical
  -- the chosen neighbourhoods
  let W : ∀ x : E 0, x ∈ U → Set (E 0) := fun x hx => (h x hx).choose
  have hWo : ∀ x hx, IsOpen (W x hx) := fun x hx => (h x hx).choose_spec.1
  have hxW : ∀ x hx, x ∈ W x hx := fun x hx => (h x hx).choose_spec.2.1
  have hW : ∀ x hx, IsSc1 (U ∩ W x hx) f := fun x hx => (h x hx).choose_spec.2.2
  -- the glued derivative family
  let D : E 1 → E 0 →L[ℝ] E' 0 := fun x =>
    if hx : E.toBase 1 x ∈ U then scDeriv (U ∩ W _ hx) f x else 0
  have hD : ∀ x (hx : E.toBase 1 x ∈ U), D x = scDeriv (U ∩ W _ hx) f x := fun x hx => by
    simp only [D, dif_pos hx]
  -- `D` agrees with the local derivative near every point
  have hDloc : ∀ x (hx : E.toBase 1 x ∈ U),
      EqOn (tangentMapWith f D) (tangentMap (U ∩ W _ hx) f) (E.tangentSet (U ∩ W _ hx)) := by
    intro x hx p hp
    have hp1 : E.toBase 1 p.1 ∈ U ∩ W _ hx := hp
    change (levelMap f 1 p.1, D p.1 p.2) = (levelMap f 1 p.1, scDeriv (U ∩ W _ hx) f p.1 p.2)
    rw [hD p.1 hp1.1]
    congr 1
    exact congrArg (fun L : E 0 →L[ℝ] E' 0 => L p.2)
      (IsSc1With.eq_of_eq_near (hWo _ hp1.1) (hWo _ hx) hU
        (hW _ hp1.1).isSc1With_scDeriv (hW _ hx).isSc1With_scDeriv hp1.1
        (hxW _ hp1.1) hp1.2)
  refine ⟨D, ?_, ?_, ?_⟩
  · exact IsSc0.of_locally fun x hx => ⟨W x hx, hWo x hx, hxW x hx, (hW x hx).isSc0⟩
  · intro x hx
    rw [hD x hx]
    have := (hW _ hx).isSc1With_scDeriv.hasFDerivWithinAt x
      (by rw [ScBanach.lvlSet_inter]; exact ⟨hx, hxW _ hx⟩)
    rw [ScBanach.lvlSet_inter] at this
    exact this.mono_of_mem_nhdsWithin (inter_mem_nhdsWithin _
      ((E.isOpen_lvlSet (hWo _ hx) 1).mem_nhds (hxW _ hx)))
  · refine IsSc0.of_locally fun p hp => ?_
    have hp1 : E.toBase 1 p.1 ∈ U := hp
    refine ⟨E.lvlSet (W _ hp1) 1 ×ˢ univ, (E.isOpen_lvlSet (hWo _ hp1) 1).prod isOpen_univ,
      ⟨hxW _ hp1, mem_univ _⟩, ?_⟩
    rw [← ScBanach.tangentSet_inter_isOpen]
    exact (hW _ hp1).tangentMap_isSc0.congr (hDloc _ hp1).symm

/-- sc^k is a local property (on a domain with unique differentiability). -/
theorem IsSck.of_locally : ∀ {k : ℕ} {E E' : ScBanach} {U : Set (E 0)} {f : E 0 → E' 0},
    IsScDomain E U → (∀ x ∈ U, ∃ W : Set (E 0), IsOpen W ∧ x ∈ W ∧ IsSck k E E' (U ∩ W) f) →
    IsSck k E E' U f
  | 0, _, _, _, _, _, h => IsSc0.of_locally h
  | k + 1, E, E', U, f, hU, h => by
    have h1 : IsSc1 U f := IsSc1.of_locally hU fun x hx => by
      obtain ⟨W, hWo, hxW, hW⟩ := h x hx
      exact ⟨W, hWo, hxW, hW.1⟩
    refine ⟨h1, IsSck.of_locally (k := k) hU.tangentSet fun p hp => ?_⟩
    have hp1 : E.toBase 1 p.1 ∈ U := hp
    obtain ⟨W, hWo, hxW, hW⟩ := h _ hp1
    refine ⟨E.lvlSet W 1 ×ˢ univ, (E.isOpen_lvlSet hWo 1).prod isOpen_univ,
      ⟨hxW, mem_univ _⟩, ?_⟩
    rw [← ScBanach.tangentSet_inter_isOpen]
    have hUW : IsScDomain E (U ∩ W) := hU.inter_isOpen hWo
    exact IsSck.congr hUW.tangentSet (h1.tangentMap_eqOn_of_subset hUW inter_subset_left) hW.2

/-- sc-smoothness is a local property (on a domain with unique differentiability). -/
theorem IsScSmooth.of_locally (hU : IsScDomain E U)
    (h : ∀ x ∈ U, ∃ W : Set (E 0), IsOpen W ∧ x ∈ W ∧ IsScSmooth (U ∩ W) f) : IsScSmooth U f :=
  fun k => IsSck.of_locally hU fun x hx => by
    obtain ⟨W, hWo, hxW, hW⟩ := h x hx
    exact ⟨W, hWo, hxW, hW k⟩

end Restriction

/-! ### Sc-smooth retractions (Definition 2.1.1 (preprint 2.1)) and retracts (Definition 2.1.3 (preprint 2.3)) -/

/-- An **sc-smooth retraction** on a relatively open subset `U` of the partial quadrant `C ⊆ E`
(Definition 2.1.1 (preprint 2.1)): an sc-smooth map `r : U → U` with `r ∘ r = r` on `U`.  The map is a total
function `E₀ → E₀`; only its values on `U` matter. -/
structure ScRetraction (E : ScBanach) (C : Set (E 0)) where
  /-- The domain `U`, relatively open in `C`. -/
  U : Set (E 0)
  /-- The retraction `r`. -/
  toFun : E 0 → E 0
  relOpen : IsRelOpenInQuadrant E C U
  mapsTo : MapsTo toFun U U
  isScSmooth : IsScSmooth U toFun
  idem : ∀ x ∈ U, toFun (toFun x) = toFun x

namespace ScRetraction

variable {C : Set (E 0)} (R : ScRetraction E C)

instance : CoeFun (ScRetraction E C) (fun _ => E 0 → E 0) := ⟨ScRetraction.toFun⟩

lemma isScDomain : IsScDomain E R.U := R.relOpen.isScDomain

lemma isSc1 : IsSc1 R.U R := R.isScSmooth.isSc1

/-- The retract `O = r(U)`. -/
def retract : Set (E 0) := R '' R.U

lemma retract_subset : R.retract ⊆ R.U := by
  rintro _ ⟨y, hy, rfl⟩
  exact R.mapsTo hy

lemma apply_mem_retract {y : E 0} (hy : y ∈ R.U) : R y ∈ R.retract := ⟨y, hy, rfl⟩

lemma apply_eq_self_of_mem_retract {x : E 0} (hx : x ∈ R.retract) : R x = x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact R.idem y hy

lemma mem_retract_iff {x : E 0} : x ∈ R.retract ↔ x ∈ R.U ∧ R x = x :=
  ⟨fun hx => ⟨R.retract_subset hx, R.apply_eq_self_of_mem_retract hx⟩,
    fun ⟨hx, hRx⟩ => ⟨x, hx, hRx⟩⟩

lemma mapsTo_retract : MapsTo R R.U R.retract := fun _ hy => R.apply_mem_retract hy

/-- `r₁ : U₁ → U₁` fixes the points of `O₁`. -/
lemma levelMap_one_eq_self {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) : levelMap R 1 x = x :=
  levelMap_eq_of_toBase_eq (R.apply_eq_self_of_mem_retract hx).symm

lemma lvlSet_retract_subset (m : ℕ) : E.lvlSet R.retract m ⊆ E.lvlSet R.U m :=
  E.lvlSet_mono R.retract_subset m

/-! ### The tangent `TO = Tr(TU)` (Definition 2.1.12 (preprint 2.5)) -/

/-- The tangent `Tr(TU) ⊆ TE₀` of the retraction, the set the text calls `TO` (Definition 2.1.12 (preprint 2.5)). -/
def tangent : Set (E.tangent 0) := tangentMap R.U R '' E.tangentSet R.U

lemma tangentMap_mapsTo : MapsTo (tangentMap R.U R) (E.tangentSet R.U) (E.tangentSet R.U) :=
  R.isSc1.tangentMap_mapsTo R.mapsTo

/-- `Tr ∘ Tr = Tr` on `TU`: the chain rule applied to `r ∘ r = r`. -/
lemma tangentMap_tangentMap {p : E.tangent 0} (hp : p ∈ E.tangentSet R.U) :
    tangentMap R.U R (tangentMap R.U R p) = tangentMap R.U R p := by
  obtain ⟨_, h⟩ := theorem_1_3_1 R.relOpen R.relOpen R.isSc1 R.isSc1 R.mapsTo
  have h' : EqOn (tangentMap R.U (R ∘ R)) (tangentMap R.U R) (E.tangentSet R.U) :=
    (R.isSc1.tangentMap_congr R.isScDomain fun x hx => (R.idem x hx).symm).symm
  exact ((h hp).symm.trans (h' hp))

/-- The fixed-point description of `TO`: `p ∈ Tr(TU)` iff `p ∈ TU` and `Tr(p) = p`. -/
theorem mem_tangent_iff {p : E.tangent 0} :
    p ∈ R.tangent ↔ p ∈ E.tangentSet R.U ∧ tangentMap R.U R p = p := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨R.tangentMap_mapsTo hq, R.tangentMap_tangentMap hq⟩
  · rintro ⟨hp, hfix⟩
    exact ⟨p, hp, hfix⟩

lemma tangent_subset : R.tangent ⊆ E.tangentSet R.U := fun _ hp => (R.mem_tangent_iff.1 hp).1

/-- The base point of an element of `TO` lies in `O₁`. -/
lemma fst_mem_of_mem_tangent {p : E.tangent 0} (hp : p ∈ R.tangent) :
    p.1 ∈ E.lvlSet R.retract 1 := by
  obtain ⟨hpU, hfix⟩ := R.mem_tangent_iff.1 hp
  have h1 : levelMap R 1 p.1 = p.1 := congrArg Prod.fst hfix
  rw [ScBanach.mem_lvlSet, R.mem_retract_iff]
  refine ⟨hpU, ?_⟩
  have := R.isSc1.isSc0.toBase_levelMap (m := 1) hpU
  rw [h1] at this
  exact this.symm

/-- For `x ∈ O₁`, `(x, h) ∈ TO ↔ Dr(x) h = h`. -/
theorem mem_tangent_iff_of_mem {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) {h : E 0} :
    ((x, h) : E.tangent 0) ∈ R.tangent ↔ scDeriv R.U R x h = h := by
  rw [mem_tangent_iff]
  have hxU : ((x, h) : E.tangent 0) ∈ E.tangentSet R.U := R.lvlSet_retract_subset 1 hx
  constructor
  · rintro ⟨_, hfix⟩
    exact congrArg Prod.snd hfix
  · intro hDh
    refine ⟨hxU, ?_⟩
    change (levelMap R 1 x, scDeriv R.U R x h) = (x, h)
    rw [R.levelMap_one_eq_self hx, hDh]

/-- `Dr(x) ∘ Dr(x) = Dr(x)` for `x ∈ O₁` (the remark after Definition 2.1.3 (preprint 2.3)). -/
theorem scDeriv_comp_self {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) :
    (scDeriv R.U R x).comp (scDeriv R.U R x) = scDeriv R.U R x := by
  ext h
  have hxU : ((x, h) : E.tangent 0) ∈ E.tangentSet R.U := R.lvlSet_retract_subset 1 hx
  have := congrArg Prod.snd (R.tangentMap_tangentMap hxU)
  change scDeriv R.U R (levelMap R 1 x) (scDeriv R.U R x h) = scDeriv R.U R x h at this
  rw [R.levelMap_one_eq_self hx] at this
  exact this

/-- For `x ∈ O₁`, the tangent space `T_xO = {h | (x, h) ∈ TO}` is the image of the projection
`Dr(x) : E₀ → E₀` (the remark after Definition 2.3.12 (preprint 2.17)). -/
theorem mem_tangent_iff_mem_range {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) {h : E 0} :
    ((x, h) : E.tangent 0) ∈ R.tangent ↔ h ∈ range (scDeriv R.U R x) := by
  rw [R.mem_tangent_iff_of_mem hx]
  constructor
  · intro hh; exact ⟨h, hh⟩
  · rintro ⟨k, rfl⟩
    exact congrArg (fun L : E 0 →L[ℝ] E 0 => L k) (R.scDeriv_comp_self hx)

/-- The explicit description `TO = {(r(x), Dr(x) h) | x ∈ U₁, h ∈ E}` (after Definition 2.1.12 (preprint 2.5)). -/
lemma mem_tangent_iff_exists {p : E.tangent 0} :
    p ∈ R.tangent ↔ ∃ x ∈ E.lvlSet R.U 1, ∃ h : E 0, p = (levelMap R 1 x, scDeriv R.U R x h) := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.1, hq, q.2, rfl⟩
  · rintro ⟨x, hx, h, rfl⟩
    exact ⟨(x, h), hx, rfl⟩

end ScRetraction

/-- `(O, C, E)` is an **sc-smooth retract** (Definition 2.1.3 (preprint 2.3)): `O = r(U)` for an sc-smooth
retraction `r : U → U` on a relatively open subset `U` of `C`. -/
def IsScRetract (E : ScBanach) (C O : Set (E 0)) : Prop :=
  ∃ R : ScRetraction E C, R.retract = O

lemma ScRetraction.isScRetract {C : Set (E 0)} (R : ScRetraction E C) : IsScRetract E C R.retract :=
  ⟨R, rfl⟩

/-- The identity is sc¹ with derivative `id`. -/
lemma isSc1With_id (U : Set (E 0)) :
    IsSc1With U (_root_.id : E 0 → E 0) fun _ => ContinuousLinearMap.id ℝ (E 0) :=
  ⟨isSc0_id U, fun x _ => (E.toBase 1).hasFDerivWithinAt.congr_fderiv
    (ContinuousLinearMap.id_comp _).symm, by
    have : tangentMapWith (_root_.id : E 0 → E 0) (fun _ => ContinuousLinearMap.id ℝ (E 0)) =
        _root_.id := funext fun p => Prod.ext (levelMap_eq_of_toBase_eq rfl) rfl
    rw [this]; exact isSc0_id _⟩

/-- `T(id) = id` on `TU` (on a domain with unique differentiability). -/
lemma tangentMap_id_eqOn {U : Set (E 0)} (hU : IsScDomain E U) :
    EqOn (tangentMap U (_root_.id : E 0 → E 0)) _root_.id (E.tangentSet U) := by
  refine (IsSc1.tangentMap_eqOn (isSc1With_id U) (hU.uniqueDiffWithinAt 1)).trans ?_
  intro p _
  exact Prod.ext (levelMap_eq_of_toBase_eq rfl) rfl

/-- The identity is sc^k on every domain with unique differentiability. -/
theorem isSck_id : ∀ {k : ℕ} {E : ScBanach} {U : Set (E 0)}, IsScDomain E U →
    IsSck k E E U _root_.id
  | 0, _, U, _ => isSc0_id U
  | k + 1, _, U, hU =>
    ⟨(isSc1With_id U).isSc1, IsSck.congr hU.tangentSet (tangentMap_id_eqOn hU).symm
      (isSck_id (k := k) hU.tangentSet)⟩

theorem isScSmooth_id {U : Set (E 0)} (hU : IsScDomain E U) : IsScSmooth U (_root_.id : E 0 → E 0) :=
  fun _ => isSck_id hU

/-- A relatively open subset `U` of a partial quadrant is a retract (`r = id`). -/
def ScRetraction.id {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U) : ScRetraction E C where
  U := U
  toFun := _root_.id
  relOpen := hU
  mapsTo := mapsTo_id U
  isScSmooth := isScSmooth_id hU.isScDomain
  idem _ _ := rfl

lemma IsRelOpenInQuadrant.isScRetract {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U) :
    IsScRetract E C U :=
  ⟨ScRetraction.id hU, image_id U⟩

/-! ### Proposition 2.1.11 (preprint 2.4) and Definition 2.1.12 (preprint 2.5) -/

/-- If `r(U) ⊆ r'(U')` then `r' ∘ r = r` on `U` (the first step of the proof of Proposition
2.4). -/
lemma ScRetraction.comp_eq_self_of_retract_subset {C : Set (E 0)} (R R' : ScRetraction E C)
    (h : R.retract ⊆ R'.retract) {y : E 0} (hy : y ∈ R.U) : R' (R y) = R y :=
  R'.apply_eq_self_of_mem_retract (h (R.apply_mem_retract hy))

/-- `Tr(TU) ⊆ Tr'(TU')` when `r(U) ⊆ r'(U')`. -/
lemma ScRetraction.tangent_subset_of_retract_subset {C : Set (E 0)} (R R' : ScRetraction E C)
    (h : R.retract ⊆ R'.retract) : R.tangent ⊆ R'.tangent := by
  intro p hp
  obtain ⟨hpU, hfix⟩ := R.mem_tangent_iff.1 hp
  have hpU' : p ∈ E.tangentSet R'.U :=
    E.lvlSet_mono R'.retract_subset 1 (E.lvlSet_mono h 1 (R.fst_mem_of_mem_tangent hp))
  rw [R'.mem_tangent_iff]
  refine ⟨hpU', ?_⟩
  have hmaps : MapsTo R R.U R'.U := fun y hy => R'.retract_subset (h (R.apply_mem_retract hy))
  obtain ⟨_, hchain⟩ := theorem_1_3_1 R.relOpen R'.relOpen R.isSc1 R'.isSc1 hmaps
  have hcongr : EqOn (tangentMap R.U (R' ∘ R)) (tangentMap R.U R) (E.tangentSet R.U) :=
    (R.isSc1.tangentMap_congr R.isScDomain fun y hy =>
      (R.comp_eq_self_of_retract_subset R' h hy).symm).symm
  have := (hchain hpU).symm.trans (hcongr hpU)
  change tangentMap R'.U R' (tangentMap R.U R p) = tangentMap R.U R p at this
  rwa [hfix] at this

/-- **Proposition 2.1.11 (preprint 2.4)**: two sc-smooth retractions `r : U → U`, `r' : U' → U'` with
`r(U) = r'(U') = O` have `Tr(TU) = Tr'(TU')`. -/
theorem proposition_2_1_11 {C : Set (E 0)} (R R' : ScRetraction E C) (h : R.retract = R'.retract) :
    R.tangent = R'.tangent :=
  Subset.antisymm (R.tangent_subset_of_retract_subset R' h.le)
    (R'.tangent_subset_of_retract_subset R h.ge)

open scoped Classical in
/-- **Definition 2.1.12 (preprint 2.5)**: the tangent `TO ⊆ TE₀` of the sc-smooth retract `(O, C, E)`, computed with
any retraction onto `O` (empty if `O` is not a retract).  Independent of the retraction by
Proposition 2.1.11 (preprint 2.4) (`retractTangent_eq`). -/
def retractTangent (E : ScBanach) (C O : Set (E 0)) : Set (E.tangent 0) :=
  if h : IsScRetract E C O then h.choose.tangent else ∅

theorem retractTangent_eq {C : Set (E 0)} (R : ScRetraction E C) :
    retractTangent E C R.retract = R.tangent := by
  have h : IsScRetract E C R.retract := R.isScRetract
  rw [retractTangent, dif_pos h]
  exact proposition_2_1_11 _ R h.choose_spec

/-- The **tangent space** `T_xO = p⁻¹(x)` at `x ∈ O₁` (Definition 2.3.12 (preprint 2.17)), as the fibre of
`TO → O₁`. -/
def tangentSpace (E : ScBanach) (C O : Set (E 0)) (x : E 1) : Set (E 0) :=
  {h | ((x, h) : E.tangent 0) ∈ retractTangent E C O}

/-- `T_xO = Dr(x)(E)` for `x ∈ O₁` (the remark after Definition 2.3.12 (preprint 2.17)). -/
theorem tangentSpace_eq_range {C : Set (E 0)} (R : ScRetraction E C) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) :
    tangentSpace E C R.retract x = range (scDeriv R.U R x) := by
  ext h
  change ((x, h) : E.tangent 0) ∈ retractTangent E C R.retract ↔ _
  rw [retractTangent_eq, R.mem_tangent_iff_mem_range hx]

/-- `T_xO` is a closed subspace of `E₀` (it is the range of a continuous projection). -/
theorem tangentSpace_eq_coe_submodule {C : Set (E 0)} (R : ScRetraction E C) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) :
    tangentSpace E C R.retract x = (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0) : Set (E 0)) := by
  rw [tangentSpace_eq_range R hx]
  ext h
  simp [LinearMap.mem_range]

/-! ### Sc-smooth maps between retracts (Proposition 2.1.13 (preprint 2.6), Definition 2.1.14 (preprint 2.7)) -/

section Maps

variable {C : Set (E 0)} {C' : Set (E' 0)} {C'' : Set (E'' 0)} {f : E 0 → E' 0} {g : E' 0 → E'' 0}

/-- `(f ∘ r) ∘ s = f ∘ s` on `V` when `r(U) ⊇ s(V)`. -/
lemma ScRetraction.comp_comp_eqOn (R S : ScRetraction E C) (h : S.retract ⊆ R.retract) :
    EqOn ((f ∘ R) ∘ S) (f ∘ S) S.U := fun y hy => by
  simp only [Function.comp_apply, S.comp_eq_self_of_retract_subset R h hy]

/-- **Proposition 2.1.13 (preprint 2.6) (1)**: if `f ∘ r` is sc-smooth for one retraction `r` onto `O`, then `f ∘ s`
is sc-smooth for every retraction `s` onto `O`. -/
theorem proposition_2_1_13_one (R S : ScRetraction E C) (hRS : R.retract = S.retract)
    (hf : IsScSmooth R.U (f ∘ R)) : IsScSmooth S.U (f ∘ S) := by
  have hmaps : MapsTo S S.U R.U := fun y hy => R.retract_subset (hRS ▸ S.apply_mem_retract hy)
  have := IsScSmooth.comp S.isScDomain R.isScDomain hf S.isScSmooth hmaps
  exact this.congr S.isScDomain (R.comp_comp_eqOn S hRS.ge)

/-- **Proposition 2.1.13 (preprint 2.6) (2)**: `T(f ∘ r) = T(f ∘ s)` on `TO`. -/
theorem proposition_2_1_13_two (R S : ScRetraction E C) (hRS : R.retract = S.retract)
    (hf : IsScSmooth R.U (f ∘ R)) :
    EqOn (tangentMap R.U (f ∘ R)) (tangentMap S.U (f ∘ S)) R.tangent := by
  intro p hp
  have hmaps : MapsTo S S.U R.U := fun y hy => R.retract_subset (hRS ▸ S.apply_mem_retract hy)
  have hpS : p ∈ S.tangent := proposition_2_1_11 R S hRS ▸ hp
  obtain ⟨hpU, hfix⟩ := S.mem_tangent_iff.1 hpS
  obtain ⟨_, hchain⟩ := theorem_1_3_1 S.relOpen R.relOpen S.isSc1 hf.isSc1 hmaps
  have hcongr : EqOn (tangentMap S.U ((f ∘ R) ∘ S)) (tangentMap S.U (f ∘ S)) (E.tangentSet S.U) :=
    (IsScSmooth.comp S.isScDomain R.isScDomain hf S.isScSmooth hmaps).isSc1.tangentMap_congr
      S.isScDomain (R.comp_comp_eqOn S hRS.ge)
  have := (hchain hpU).symm.trans (hcongr hpU)
  change tangentMap R.U (f ∘ R) (tangentMap S.U S p) = tangentMap S.U (f ∘ S) p at this
  rwa [hfix] at this

/-- **Proposition 2.1.13 (preprint 2.6) (3)**: if `f ∘ r` is sc-smooth and `f(O) ⊆ O'`, then `T(f ∘ r)` maps `TO`
into `TO'`. -/
theorem proposition_2_1_13_three (R : ScRetraction E C) (R' : ScRetraction E' C')
    (hf : IsScSmooth R.U (f ∘ R)) (hfO : MapsTo f R.retract R'.retract) :
    MapsTo (tangentMap R.U (f ∘ R)) R.tangent R'.tangent := by
  intro p hp
  have hpU : p ∈ E.tangentSet R.U := R.tangent_subset hp
  have hmaps : MapsTo (f ∘ R) R.U R'.U := fun y hy =>
    R'.retract_subset (hfO (R.apply_mem_retract hy))
  rw [R'.mem_tangent_iff]
  refine ⟨hf.isSc1.tangentMap_mapsTo hmaps hpU, ?_⟩
  obtain ⟨_, hchain⟩ := theorem_1_3_1 R.relOpen R'.relOpen hf.isSc1 R'.isSc1 hmaps
  have hcongr : EqOn (tangentMap R.U (R' ∘ (f ∘ R))) (tangentMap R.U (f ∘ R)) (E.tangentSet R.U) :=
    (hf.isSc1.tangentMap_congr R.isScDomain fun y hy =>
      (R'.apply_eq_self_of_mem_retract (hfO (R.apply_mem_retract hy))).symm).symm
  exact (hchain hpU).symm.trans (hcongr hpU)

/-- **Definition 2.1.14 (preprint 2.7)**: `f : O → O'` is **sc-smooth between the retracts** `(O, C, E)` and
`(O', C', E')` if `f(O) ⊆ O'` and `f ∘ r : U → E'` is sc-smooth for every (equivalently, by
Proposition 2.1.13 (preprint 2.6), for one) sc-smooth retraction `r : U → U` onto `O`. -/
structure IsScSmoothRetractMap (E : ScBanach) (C O : Set (E 0)) (E' : ScBanach)
    (C' O' : Set (E' 0)) (f : E 0 → E' 0) : Prop where
  mapsTo : MapsTo f O O'
  comp_isScSmooth : ∀ R : ScRetraction E C, R.retract = O → IsScSmooth R.U (f ∘ R)

/-- Definition 2.1.14 (preprint 2.7) in the text's form: for an actual retract `O`, sc-smoothness of `f ∘ r` for one
retraction `r` onto `O` suffices. -/
theorem isScSmoothRetractMap_iff_exists {O : Set (E 0)} {O' : Set (E' 0)} (hO : IsScRetract E C O) :
    IsScSmoothRetractMap E C O E' C' O' f ↔
      MapsTo f O O' ∧ ∃ R : ScRetraction E C, R.retract = O ∧ IsScSmooth R.U (f ∘ R) := by
  constructor
  · intro h
    obtain ⟨R, hR⟩ := hO
    exact ⟨h.mapsTo, R, hR, h.comp_isScSmooth R hR⟩
  · rintro ⟨hmaps, R, hR, hf⟩
    exact ⟨hmaps, fun S hS => proposition_2_1_13_one R S (hR.trans hS.symm) hf⟩

open scoped Classical in
/-- **Definition 2.1.14 (preprint 2.7)**: the tangent map `Tf : TO → TO'` of `f : O → O'`, defined as
`T(f ∘ r)` for a retraction `r` onto `O` (junk if `O` is not a retract).  On `TO` it does not
depend on `r` (`retractTangentMap_eqOn`). -/
def retractTangentMap (E : ScBanach) (C O : Set (E 0)) (f : E 0 → E' 0) :
    E.tangent 0 → E'.tangent 0 :=
  if h : IsScRetract E C O then tangentMap h.choose.U (f ∘ h.choose) else fun _ => 0

theorem retractTangentMap_eqOn {O : Set (E 0)} {O' : Set (E' 0)}
    (hf : IsScSmoothRetractMap E C O E' C' O' f) (R : ScRetraction E C) (hR : R.retract = O) :
    EqOn (retractTangentMap E C O f) (tangentMap R.U (f ∘ R)) (retractTangent E C O) := by
  have h : IsScRetract E C O := ⟨R, hR⟩
  rw [retractTangentMap, dif_pos h]
  subst hR
  rw [retractTangent_eq]
  have h1 : (h.choose).tangent = R.tangent := proposition_2_1_11 _ R h.choose_spec
  intro p hp
  exact proposition_2_1_13_two _ R h.choose_spec (hf.comp_isScSmooth _ h.choose_spec) (h1 ▸ hp)

/-- `Tf` maps `TO` into `TO'` (the remark after Definition 2.1.14 (preprint 2.7)). -/
theorem IsScSmoothRetractMap.tangentMap_mapsTo {O : Set (E 0)} {O' : Set (E' 0)}
    (hf : IsScSmoothRetractMap E C O E' C' O' f) (hO : IsScRetract E C O)
    (hO' : IsScRetract E' C' O') :
    MapsTo (retractTangentMap E C O f) (retractTangent E C O) (retractTangent E' C' O') := by
  obtain ⟨R, rfl⟩ := hO
  obtain ⟨R', rfl⟩ := hO'
  intro p hp
  rw [retractTangentMap_eqOn hf R rfl hp, retractTangent_eq]
  rw [retractTangent_eq] at hp
  exact proposition_2_1_13_three R R' (hf.comp_isScSmooth R rfl) hf.mapsTo hp

/-- `Tf(x, h) = (f(x), Df(x) h)` on `TO`, with `Df(x) := D(f ∘ r)(x)`. -/
lemma retractTangentMap_apply {O : Set (E 0)} {O' : Set (E' 0)}
    (hf : IsScSmoothRetractMap E C O E' C' O' f) (R : ScRetraction E C) (hR : R.retract = O)
    {p : E.tangent 0} (hp : p ∈ retractTangent E C O) :
    retractTangentMap E C O f p = (levelMap (f ∘ R) 1 p.1, scDeriv R.U (f ∘ R) p.1 p.2) :=
  retractTangentMap_eqOn hf R hR hp

/-! ### Theorem 2.1.15 (preprint 2.8): the chain rule for retracts -/

/-- `(g ∘ f) ∘ r = (g ∘ r') ∘ (f ∘ r)` on `U` when `f(r(U)) ⊆ r'(U')`. -/
lemma ScRetraction.comp_comp_comp_eqOn (R : ScRetraction E C) (R' : ScRetraction E' C')
    (hfO : MapsTo f R.retract R'.retract) :
    EqOn ((g ∘ R') ∘ (f ∘ R)) ((g ∘ f) ∘ R) R.U := fun y hy => by
  simp only [Function.comp_apply, R'.apply_eq_self_of_mem_retract (hfO (R.apply_mem_retract hy))]

/-- **Theorem 2.1.15 (preprint 2.8)**, first part: the composition of sc-smooth maps between retracts is sc-smooth.
(The target `O'` must be a retract.) -/
theorem IsScSmoothRetractMap.comp {O : Set (E 0)} {O' : Set (E' 0)} {O'' : Set (E'' 0)}
    (hg : IsScSmoothRetractMap E' C' O' E'' C'' O'' g) (hf : IsScSmoothRetractMap E C O E' C' O' f)
    (hO' : IsScRetract E' C' O') : IsScSmoothRetractMap E C O E'' C'' O'' (g ∘ f) where
  mapsTo := hg.mapsTo.comp hf.mapsTo
  comp_isScSmooth R hR := by
    obtain ⟨R', hR'⟩ := hO'
    have hfO : MapsTo f R.retract R'.retract := by rw [hR, hR']; exact hf.mapsTo
    have hmaps : MapsTo (f ∘ R) R.U R'.U := fun y hy =>
      R'.retract_subset (hfO (R.apply_mem_retract hy))
    have := IsScSmooth.comp R.isScDomain R'.isScDomain (hg.comp_isScSmooth R' hR')
      (hf.comp_isScSmooth R hR) hmaps
    exact this.congr R.isScDomain (R.comp_comp_comp_eqOn R' hfO)

/-- **Theorem 2.1.15 (preprint 2.8)**, second part: `T(g ∘ f) = Tg ∘ Tf` on `TO`. -/
theorem retractTangentMap_comp {O : Set (E 0)} {O' : Set (E' 0)} {O'' : Set (E'' 0)}
    (hg : IsScSmoothRetractMap E' C' O' E'' C'' O'' g) (hf : IsScSmoothRetractMap E C O E' C' O' f)
    (hO : IsScRetract E C O) (hO' : IsScRetract E' C' O') :
    EqOn (retractTangentMap E C O (g ∘ f))
      (retractTangentMap E' C' O' g ∘ retractTangentMap E C O f) (retractTangent E C O) := by
  obtain ⟨R, rfl⟩ := hO
  obtain ⟨R', rfl⟩ := hO'
  intro p hp
  have hgf := hg.comp hf R'.isScRetract
  have hmaps : MapsTo (f ∘ R) R.U R'.U := fun y hy =>
    R'.retract_subset (hf.mapsTo (R.apply_mem_retract hy))
  have hpU : p ∈ E.tangentSet R.U := by rw [retractTangent_eq] at hp; exact R.tangent_subset hp
  have hTf : retractTangentMap E C R.retract f p ∈ retractTangent E' C' R'.retract :=
    hf.tangentMap_mapsTo R.isScRetract R'.isScRetract hp
  rw [retractTangentMap_eqOn hgf R rfl hp, Function.comp_apply, retractTangentMap_eqOn hg R' rfl hTf,
    retractTangentMap_eqOn hf R rfl hp]
  obtain ⟨_, hchain⟩ := theorem_1_3_1 R.relOpen R'.relOpen (hf.comp_isScSmooth R rfl).isSc1
    (hg.comp_isScSmooth R' rfl).isSc1 hmaps
  have hcongr : EqOn (tangentMap R.U ((g ∘ R') ∘ (f ∘ R))) (tangentMap R.U ((g ∘ f) ∘ R))
      (E.tangentSet R.U) :=
    (IsScSmooth.comp R.isScDomain R'.isScDomain (hg.comp_isScSmooth R' rfl)
      (hf.comp_isScSmooth R rfl) hmaps).isSc1.tangentMap_congr R.isScDomain
      (R.comp_comp_comp_eqOn R' hf.mapsTo)
  exact (hcongr hpU).symm.trans (hchain hpU)

/-- **Theorem 2.1.15 (preprint 2.8)** (chain rule for sc-smooth maps between retracts): if `f : O → O'` and
`g : O' → O''` are sc-smooth, then `g ∘ f : O → O''` is sc-smooth and `T(g ∘ f) = Tg ∘ Tf` on
`TO`. -/
theorem theorem_2_1_15 {O : Set (E 0)} {O' : Set (E' 0)} {O'' : Set (E'' 0)}
    (hO : IsScRetract E C O) (hO' : IsScRetract E' C' O')
    (hf : IsScSmoothRetractMap E C O E' C' O' f) (hg : IsScSmoothRetractMap E' C' O' E'' C'' O'' g) :
    IsScSmoothRetractMap E C O E'' C'' O'' (g ∘ f) ∧
      EqOn (retractTangentMap E C O (g ∘ f))
        (retractTangentMap E' C' O' g ∘ retractTangentMap E C O f) (retractTangent E C O) :=
  ⟨hg.comp hf hO', retractTangentMap_comp hg hf hO hO'⟩

/-- The identity of a retract is sc-smooth. -/
theorem isScSmoothRetractMap_id (O : Set (E 0)) : IsScSmoothRetractMap E C O E C O _root_.id where
  mapsTo := mapsTo_id O
  comp_isScSmooth R _ := R.isScSmooth

/-- A retraction `r` onto `O ⊆ U` is sc-smooth as a map `(U, C, E) → (O, C, E)`. -/
theorem ScRetraction.isScSmoothRetractMap (R : ScRetraction E C) :
    IsScSmoothRetractMap E C R.U E C R.retract R where
  mapsTo := R.mapsTo_retract
  comp_isScSmooth S hS := by
    have hmaps : MapsTo S S.U R.U := fun y hy => hS ▸ S.apply_mem_retract hy
    exact IsScSmooth.comp S.isScDomain R.isScDomain R.isScSmooth S.isScSmooth hmaps

/-- The inclusion `O → U` of a retract is sc-smooth (it is `id`), as a map `(O, C, E) → (U, C, E)`. -/
theorem ScRetraction.isScSmoothRetractMap_inclusion (R : ScRetraction E C) :
    IsScSmoothRetractMap E C R.retract E C R.U _root_.id where
  mapsTo := fun _ hx => R.retract_subset hx
  comp_isScSmooth S _ := S.isScSmooth

/-- Sc-smoothness depends only on the values of `f` on `O`. -/
theorem IsScSmoothRetractMap.congr {O : Set (E 0)} {O' : Set (E' 0)}
    (hf : IsScSmoothRetractMap E C O E' C' O' f) {f' : E 0 → E' 0} (hff' : EqOn f f' O) :
    IsScSmoothRetractMap E C O E' C' O' f' where
  mapsTo := fun _ hx => hff' hx ▸ hf.mapsTo hx
  comp_isScSmooth R hR := (hf.comp_isScSmooth R hR).congr R.isScDomain fun _ hy =>
    hff' (hR ▸ R.apply_mem_retract hy)

/-- An sc-smooth map between retracts is continuous on `O` (it is sc⁰ on level `0`). -/
theorem IsScSmoothRetractMap.continuousOn {O : Set (E 0)} {O' : Set (E' 0)}
    (hf : IsScSmoothRetractMap E C O E' C' O' f) (hO : IsScRetract E C O) : ContinuousOn f O := by
  obtain ⟨R, rfl⟩ := hO
  have := ((hf.comp_isScSmooth R rfl).isSc1.isSc0.continuousOn_base).mono R.retract_subset
  exact this.congr fun x hx => by
    simp only [Function.comp_apply, R.apply_eq_self_of_mem_retract hx]

/-- An sc-smooth map between retracts maps `O_m` into `O'_m` (it is sc⁰ on every level). -/
theorem IsScSmoothRetractMap.mem_range_toBase {O : Set (E 0)} {O' : Set (E' 0)}
    (hf : IsScSmoothRetractMap E C O E' C' O' f) (hO : IsScRetract E C O) {m : ℕ} {x : E 0}
    (hx : x ∈ O) (hxm : x ∈ range (E.toBase m)) : f x ∈ range (E'.toBase m) := by
  obtain ⟨R, rfl⟩ := hO
  obtain ⟨z, rfl⟩ := hxm
  have hz : z ∈ E.lvlSet R.U m := R.retract_subset hx
  have := (hf.comp_isScSmooth R rfl).isSc1.isSc0.mem_range m z hz
  rwa [Function.comp_apply, R.apply_eq_self_of_mem_retract hx] at this

end Maps

/-! ### Proposition 2.3.1 (preprint 2.10): new retracts from old -/

section NewRetracts

variable {C : Set (E 0)}

/-- `U ∩ r⁻¹(W)` is relatively open in `C` for `W` open (`r` is continuous on `U`). -/
lemma ScRetraction.relOpen_inter_preimage (R : ScRetraction E C) {W : Set (E 0)} (hW : IsOpen W) :
    IsRelOpenInQuadrant E C (R.U ∩ R ⁻¹' W) := by
  obtain ⟨V, hV, hUV⟩ := R.relOpen.relOpen
  refine ⟨R.relOpen.isPartialQuadrant, ?_⟩
  obtain ⟨u, hu, huU⟩ := (continuousOn_iff'.1 R.isSc1.isSc0.continuousOn_base) W hW
  refine ⟨V ∩ u, hV.inter hu, ?_⟩
  rw [inter_comm R.U, huU, hUV, inter_left_comm, ← inter_assoc]

/-- The restriction of a retraction `r : U → U` to `U ∩ r⁻¹(W)`, `W` open: a retraction onto
`r(U) ∩ W` (the proof of Proposition 2.3.1 (preprint 2.10) (1)). -/
def ScRetraction.restrict (R : ScRetraction E C) {W : Set (E 0)} (hW : IsOpen W) :
    ScRetraction E C where
  U := R.U ∩ R ⁻¹' W
  toFun := R
  relOpen := R.relOpen_inter_preimage hW
  mapsTo y hy := ⟨R.mapsTo hy.1, by
    change R (R y) ∈ W
    rw [R.idem y hy.1]; exact hy.2⟩
  isScSmooth := R.isScSmooth.of_subset (R.relOpen_inter_preimage hW).isScDomain inter_subset_left
  idem y hy := R.idem y hy.1

lemma ScRetraction.restrict_U (R : ScRetraction E C) {W : Set (E 0)} (hW : IsOpen W) :
    (R.restrict hW).U = R.U ∩ R ⁻¹' W := rfl

lemma ScRetraction.restrict_apply (R : ScRetraction E C) {W : Set (E 0)} (hW : IsOpen W) (y : E 0) :
    R.restrict hW y = R y := rfl

lemma ScRetraction.restrict_retract (R : ScRetraction E C) {W : Set (E 0)} (hW : IsOpen W) :
    (R.restrict hW).retract = R.retract ∩ W := by
  ext z
  constructor
  · rintro ⟨y, ⟨hy, hyW⟩, rfl⟩
    exact ⟨R.apply_mem_retract hy, hyW⟩
  · rintro ⟨⟨y, hy, rfl⟩, hzW⟩
    exact ⟨y, ⟨hy, hzW⟩, rfl⟩

/-- **Proposition 2.3.1 (preprint 2.10) (1)**: an open subset `O ∩ W` of an sc-smooth retract `(O, C, E)` is an
sc-smooth retract. -/
theorem proposition_2_3_1_one {O : Set (E 0)} (hO : IsScRetract E C O) {W : Set (E 0)}
    (hW : IsOpen W) : IsScRetract E C (O ∩ W) := by
  obtain ⟨R, rfl⟩ := hO
  exact ⟨R.restrict hW, R.restrict_retract hW⟩

/-- **Proposition 2.3.1 (preprint 2.10) (2)**: if `(V, C, E)` is an sc-smooth retract and `s : V → V` is sc-smooth
with `s ∘ s = s` on `V`, then `(s(V), C, E)` is an sc-smooth retract. -/
theorem proposition_2_3_1_two {V : Set (E 0)} (hV : IsScRetract E C V) {s : E 0 → E 0}
    (hs : IsScSmoothRetractMap E C V E C V s) (hss : ∀ x ∈ V, s (s x) = s x) :
    IsScRetract E C (s '' V) := by
  obtain ⟨R, rfl⟩ := hV
  let ρ : ScRetraction E C :=
    { U := R.U
      toFun := s ∘ R
      relOpen := R.relOpen
      mapsTo := fun y hy => R.retract_subset (hs.mapsTo (R.apply_mem_retract hy))
      isScSmooth := hs.comp_isScSmooth R rfl
      idem := fun y hy => by
        simp only [Function.comp_apply]
        rw [R.apply_eq_self_of_mem_retract (hs.mapsTo (R.apply_mem_retract hy)),
          hss _ (R.apply_mem_retract hy)] }
  refine ⟨ρ, ?_⟩
  change (s ∘ R) '' R.U = s '' R.retract
  rw [image_comp]; rfl

/-- The restriction of an sc-smooth map between retracts to an open subset of the source. -/
theorem IsScSmoothRetractMap.restrict {C' : Set (E' 0)} {O : Set (E 0)} {O' : Set (E' 0)}
    {f : E 0 → E' 0} (hf : IsScSmoothRetractMap E C O E' C' O' f) (hO : IsScRetract E C O)
    {W : Set (E 0)} : IsScSmoothRetractMap E C (O ∩ W) E' C' O' f where
  mapsTo := hf.mapsTo.mono_left inter_subset_left
  comp_isScSmooth S hS := by
    obtain ⟨R, rfl⟩ := hO
    have hmaps : MapsTo S S.U R.U := fun y hy =>
      R.retract_subset (hS ▸ S.apply_mem_retract hy).1
    have := IsScSmooth.comp S.isScDomain R.isScDomain (hf.comp_isScSmooth R rfl) S.isScSmooth hmaps
    refine this.congr S.isScDomain fun y hy => ?_
    simp only [Function.comp_apply, R.apply_eq_self_of_mem_retract (hS ▸ S.apply_mem_retract hy).1]

/-- Shrinking the target of an sc-smooth map between retracts. -/
theorem IsScSmoothRetractMap.mono_target {C' : Set (E' 0)} {O : Set (E 0)} {O' O'' : Set (E' 0)}
    {f : E 0 → E' 0} (hf : IsScSmoothRetractMap E C O E' C' O' f) (hmaps : MapsTo f O O'') :
    IsScSmoothRetractMap E C O E' C' O'' f :=
  ⟨hmaps, hf.comp_isScSmooth⟩

/-- Sc-smoothness between retracts is a local property: if every point of the retract `O` has an
open neighbourhood `W` with `f` sc-smooth on `(O ∩ W, C, E)`, then `f` is sc-smooth on
`(O, C, E)`. -/
theorem IsScSmoothRetractMap.of_locally {C' : Set (E' 0)} {O : Set (E 0)} {O' : Set (E' 0)}
    {f : E 0 → E' 0} (hmaps : MapsTo f O O')
    (h : ∀ x ∈ O, ∃ W : Set (E 0), IsOpen W ∧ x ∈ W ∧ IsScSmoothRetractMap E C (O ∩ W) E' C' O' f) :
    IsScSmoothRetractMap E C O E' C' O' f where
  mapsTo := hmaps
  comp_isScSmooth R hR := by
    refine IsScSmooth.of_locally R.isScDomain fun y hy => ?_
    obtain ⟨W, hWo, hxW, hW⟩ := h (R y) (hR ▸ R.apply_mem_retract hy)
    obtain ⟨u, hu, huU⟩ := (continuousOn_iff'.1 R.isSc1.isSc0.continuousOn_base) W hWo
    refine ⟨u, hu, ?_, ?_⟩
    · have : y ∈ R ⁻¹' W ∩ R.U := ⟨hxW, hy⟩
      rw [huU] at this; exact this.1
    · -- on `U ∩ u = U ∩ r⁻¹(W)`, `f ∘ r = (f ∘ r_W) ∘ r` with `r_W` the restricted retraction
      have hUu : R.U ∩ u = (R.restrict hWo).U := by
        rw [ScRetraction.restrict_U, inter_comm R.U (R ⁻¹' W), huU, inter_comm]
      rw [hUu]
      have hRW : (R.restrict hWo).retract = O ∩ W := by rw [R.restrict_retract hWo, hR]
      have hsub : MapsTo R (R.restrict hWo).U (R.restrict hWo).U := (R.restrict hWo).mapsTo
      have h1 := hW.comp_isScSmooth (R.restrict hWo) hRW
      have := IsScSmooth.comp (R.restrict hWo).isScDomain (R.restrict hWo).isScDomain h1
        (R.restrict hWo).isScSmooth hsub
      refine this.congr (R.restrict hWo).isScDomain fun z hz => ?_
      change f (R (R z)) = f (R z)
      rw [R.idem z hz.1]

end NewRetracts

/-! ### Local models -/

/-- A **local model** `(O, C, E)`: an sc-smooth retract, the local model of an M-polyfold chart. -/
structure LocalModel where
  /-- The sc-Banach space `E`. -/
  E : ScBanach
  /-- The partial quadrant `C ⊆ E`. -/
  C : Set (E 0)
  /-- The retract `O ⊆ C`. -/
  O : Set (E 0)
  isScRetract : IsScRetract E C O

namespace LocalModel

/-- Proposition 2.3.1 (preprint 2.10) (1): the restriction of a local model to an open set. -/
def restrict (M : LocalModel) {W : Set (M.E 0)} (hW : IsOpen W) : LocalModel where
  E := M.E
  C := M.C
  O := M.O ∩ W
  isScRetract := proposition_2_3_1_one M.isScRetract hW

@[simp] lemma restrict_E (M : LocalModel) {W : Set (M.E 0)} (hW : IsOpen W) :
    (M.restrict hW).E = M.E := rfl

@[simp] lemma restrict_C (M : LocalModel) {W : Set (M.E 0)} (hW : IsOpen W) :
    (M.restrict hW).C = M.C := rfl

@[simp] lemma restrict_O (M : LocalModel) {W : Set (M.E 0)} (hW : IsOpen W) :
    (M.restrict hW).O = M.O ∩ W := rfl

/-- The local model `(U, C, E)` of a relatively open subset of a partial quadrant (`r = id`). -/
def ofRelOpen {E : ScBanach} {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U) : LocalModel :=
  ⟨E, C, U, hU.isScRetract⟩

/-- The tangent `(TO, TC, TE)` of a local model (Definition 2.1.12 (preprint 2.5)), as a local model: `TO` is the
retract of the sc-smooth retraction `Tr` on `TU`.  This lemma is the sc-smoothness of `Tr`
(`T` of an sc-smooth map is sc-smooth, `isScSmooth_iff`); the local model itself is
`LocalModel.tangent` in `TangentBundle.lean`, with `IsPartialQuadrant.tangentSet` (`TC` is a
partial quadrant in `TE`), `IsRelOpenInQuadrant.tangentSet` and `ScRetraction.tangentRetraction`. -/
lemma tangent_isScSmooth {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C) :
    IsScSmooth (E.tangentSet R.U) (tangentMap R.U R) :=
  (isScSmooth_iff.1 R.isScSmooth).2

end LocalModel

end Polyfold
