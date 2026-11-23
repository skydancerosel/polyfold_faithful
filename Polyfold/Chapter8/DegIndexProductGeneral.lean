import Polyfold.Chapter5.DenseSmoothPoints
import Polyfold.Chapter6.IntervalEndInclusion
import Polyfold.Chapter8.DegIndexProduct

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Definition 2.4.1 (p. 54),
Lemma 2.4.6, and §8.5, after Definition 8.5.1 (p. 383) (comparison item V8.28).

# The degeneracy index of a product: the factors bound the product from below

For arbitrary M-polyfolds `X`, `Y` (no tameness, no condition on the points):

* `MPolyfold.isSubMPolyfold_sliceLeft`: for a smooth point `y`, the slice `X × {y}` is a
  sub-M-polyfold of `X × Y` (the retraction is `(a, b) ↦ (a, y)`), and
  `MPolyfold.isScDiffeoOn_sliceLeft`: `X → X × {y}` is an sc-diffeomorphism.
* `MPolyfold.degIndex_le_degIndex_prod_left`, `MPolyfold.degIndex_le_degIndex_prod_right`:
  `d_X(x) ≤ d_{X × Y}(x, y)` and `d_Y(y) ≤ d_{X × Y}(x, y)` at all points.  A chart of `X × Y`
  around `(x, y)` restricts on a slice `X × {y'}` to a chart of the slice with the same partial
  quadrant (Lemma 2.4.6: a sub-retract of a retract is a retract); `y'` is a smooth point near
  `y`, and Lemma 2.4.3 compares `(x, y')` with `(x, y)`.
* `MPolyfold.degIndex_prod_of_degIndex_eq_zero_right` / `_left`: the product formula
  `d_{X × Y}(x, y) = d_X(x) + d_Y(y)` whenever one of the two indices vanishes (for instance
  when one factor has no boundary).
* `MPolyfold.degIndex_prod_of_exists_slice`: the product formula at `(x, y)` follows from one point
  `y'` with `d_{X × Y}(x, y') + d_Y(y) ≤ d_{X × Y}(x, y)` (the index drops by `d_Y(y)` along the
  slice `{x} × Y`); `MPolyfold.degIndex_prod_iff_exists_slice` near a point with `d_Y = 0`.
* V8.28: `EpFunctor.IsProperCovering.degIndex_le_degIndex_prod_fibredMap`
  (`d_𝐘(φ) ≤ d_{𝐗 × Y}(F φ, s φ) ≤ 2 d_𝐘(φ)`), and
  `EpFunctor.IsProperCovering.degIndex_prod_fibredMap_of_degIndex_eq_zero`.

## What is left

The product formula at a pair of points with `d_X(x) > 0`, `d_Y(y) > 0` at which the bound of
Theorem 2.4.12 is not attained is not settled here.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : MPolyfold X} {Q : MPolyfold Y}

/-! ### Slices -/

/-- The slice `X × {y}`. -/
def sliceLeft (y : Y) : Set (X × Y) := {p | p.2 = y}

/-- The slice `{x} × Y`. -/
def sliceRight (x : X) : Set (X × Y) := {p | p.1 = x}

/-- The retraction `(a, b) ↦ (a, y)` of `X × Y` onto `X × {y}` is sc-smooth for smooth `y`. -/
theorem isScSmoothMap_sliceLeftRetr [ParacompactSpace (X × Y)] {y : Y} (hy : y ∈ Q.smoothSet) :
    (P.prod Q).IsScSmoothMap (P.prod Q) fun p : X × Y => (p.1, y) :=
  IsScSmoothOn.prodMk (isScSmoothMap_fst (P := P) (Q := Q)) (isScSmoothMap_const hy)

/-- The retraction `(a, b) ↦ (x, b)` of `X × Y` onto `{x} × Y` is sc-smooth for smooth `x`. -/
theorem isScSmoothMap_sliceRightRetr [ParacompactSpace (X × Y)] {x : X} (hx : x ∈ P.smoothSet) :
    (P.prod Q).IsScSmoothMap (P.prod Q) fun p : X × Y => (x, p.2) :=
  IsScSmoothOn.prodMk (isScSmoothMap_const hx) (isScSmoothMap_snd (P := P) (Q := Q))

/-- For a smooth point `y`, the slice `X × {y}` is a sub-M-polyfold of `X × Y`
(Definition 2.3.18). -/
theorem isSubMPolyfold_sliceLeft [ParacompactSpace (X × Y)] {y : Y} (hy : y ∈ Q.smoothSet) :
    (P.prod Q).IsSubMPolyfold (sliceLeft (X := X) y) := fun a _ =>
  ⟨univ, isOpen_univ, mem_univ a, fun p => (p.1, y), mapsTo_univ _ _,
    isScSmoothMap_sliceLeftRetr hy, fun _ _ => rfl, by
      ext p
      simp only [image_univ, mem_range, inter_univ, sliceLeft, mem_ofPred_eq]
      constructor
      · rintro ⟨q, rfl⟩; rfl
      · intro hp; exact ⟨p, Prod.ext rfl hp.symm⟩⟩

/-- For a smooth point `x`, the slice `{x} × Y` is a sub-M-polyfold of `X × Y`. -/
theorem isSubMPolyfold_sliceRight [ParacompactSpace (X × Y)] {x : X} (hx : x ∈ P.smoothSet) :
    (P.prod Q).IsSubMPolyfold (sliceRight (Y := Y) x) := fun a _ =>
  ⟨univ, isOpen_univ, mem_univ a, fun p => (x, p.2), mapsTo_univ _ _,
    isScSmoothMap_sliceRightRetr hx, fun _ _ => rfl, by
      ext p
      simp only [image_univ, mem_range, inter_univ, sliceRight, mem_ofPred_eq]
      constructor
      · rintro ⟨q, rfl⟩; rfl
      · intro hp; exact ⟨p, Prod.ext hp.symm rfl⟩⟩

/-- `X → X × {y}`, `a ↦ (a, y)`, is an sc-diffeomorphism onto the slice (with its structure of
sub-M-polyfold, Proposition 2.3.19). -/
theorem isScDiffeoOn_sliceLeft [ParacompactSpace (X × Y)] {y : Y} (hy : y ∈ Q.smoothSet)
    [ParacompactSpace (sliceLeft (X := X) y)] :
    P.IsScDiffeoOn (subPolyfold (isSubMPolyfold_sliceLeft (P := P) hy))
      (fun a => ⟨(a, y), rfl⟩) (fun p => p.1.1) univ univ where
  isScSmoothOn := isScSmoothOn_subPolyfold_of_val _
    (IsScSmoothOn.prodMk (isScSmoothMap_id (P := P)) (isScSmoothMap_const hy))
  isScSmoothOn_inv := IsScSmoothOn.comp (isScSmoothMap_fst (P := P) (Q := Q))
    (subPolyfold_inclusion_isScSmooth _) (mapsTo_univ _ _)
  mapsTo := mapsTo_univ _ _
  mapsTo_inv := mapsTo_univ _ _
  left_inv _ _ := rfl
  right_inv p _ := Subtype.ext (Prod.ext rfl p.2.symm)

/-- `Y → {x} × Y`, `b ↦ (x, b)`, is an sc-diffeomorphism onto the slice. -/
theorem isScDiffeoOn_sliceRight [ParacompactSpace (X × Y)] {x : X} (hx : x ∈ P.smoothSet)
    [ParacompactSpace (sliceRight (Y := Y) x)] :
    Q.IsScDiffeoOn (subPolyfold (isSubMPolyfold_sliceRight (Q := Q) hx))
      (fun b => ⟨(x, b), rfl⟩) (fun p => p.1.2) univ univ where
  isScSmoothOn := isScSmoothOn_subPolyfold_of_val _
    (IsScSmoothOn.prodMk (isScSmoothMap_const hx) (isScSmoothMap_id (P := Q)))
  isScSmoothOn_inv := IsScSmoothOn.comp (isScSmoothMap_snd (P := P) (Q := Q))
    (subPolyfold_inclusion_isScSmooth _) (mapsTo_univ _ _)
  mapsTo := mapsTo_univ _ _
  mapsTo_inv := mapsTo_univ _ _
  left_inv _ _ := rfl
  right_inv p _ := Subtype.ext (Prod.ext p.2.symm rfl)

/-! ### The factors bound the product from below -/

/-- `d_X(x) ≤ d_{X × Y}(x, y)` for a smooth point `y` (Proposition 2.4.4 for `X ≅ X × {y}` and
Lemma 2.4.6 for the sub-M-polyfold `X × {y}`). -/
theorem degIndex_le_degIndex_prod_left_of_mem_smoothSet [ParacompactSpace (X × Y)] (x : X) {y : Y}
    (hy : y ∈ Q.smoothSet) : P.degIndex x ≤ (P.prod Q).degIndex (x, y) := by
  have := (P.prod Q).paracompactSpace_subtype (sliceLeft (X := X) y)
  rw [proposition_2_4_4 (isScDiffeoOn_sliceLeft (P := P) hy) (mem_univ x)]
  exact lemma_2_4_6 (isSubMPolyfold_sliceLeft (P := P) hy) ⟨(x, y), rfl⟩

/-- `d_Y(y) ≤ d_{X × Y}(x, y)` for a smooth point `x`. -/
theorem degIndex_le_degIndex_prod_right_of_mem_smoothSet [ParacompactSpace (X × Y)] {x : X}
    (hx : x ∈ P.smoothSet) (y : Y) : Q.degIndex y ≤ (P.prod Q).degIndex (x, y) := by
  have := (P.prod Q).paracompactSpace_subtype (sliceRight (Y := Y) x)
  rw [proposition_2_4_4 (isScDiffeoOn_sliceRight (Q := Q) hx) (mem_univ y)]
  exact lemma_2_4_6 (isSubMPolyfold_sliceRight (Q := Q) hx) ⟨(x, y), rfl⟩

variable (P Q)

/-- **`d_X(x) ≤ d_{X × Y}(x, y)`** for all M-polyfolds and all points (Definition 2.4.1, p. 54;
no tameness).  The slice `X × {y'}` through a smooth point `y'` near `y` is a sub-M-polyfold
sc-diffeomorphic to `X`, and `d_{X × Y}(x, y') ≤ d_{X × Y}(x, y)` by Lemma 2.4.3. -/
theorem degIndex_le_degIndex_prod_left [ParacompactSpace (X × Y)] (x : X) (y : Y) :
    P.degIndex x ≤ (P.prod Q).degIndex (x, y) := by
  have hev : ∀ᶠ y' in 𝓝 y, (P.prod Q).degIndex (x, y') ≤ (P.prod Q).degIndex (x, y) :=
    (Continuous.prodMk_right x).continuousAt.eventually (lemma_2_4_3 (P.prod Q) (x, y))
  have hfr : ∃ᶠ y' in 𝓝 y, y' ∈ Q.smoothSet := mem_closure_iff_frequently.1 (Q.dense_smoothSet y)
  obtain ⟨y', hy', hle⟩ := (hfr.and_eventually hev).exists
  exact (degIndex_le_degIndex_prod_left_of_mem_smoothSet x hy').trans hle

/-- **`d_Y(y) ≤ d_{X × Y}(x, y)`** for all M-polyfolds and all points. -/
theorem degIndex_le_degIndex_prod_right [ParacompactSpace (X × Y)] (x : X) (y : Y) :
    Q.degIndex y ≤ (P.prod Q).degIndex (x, y) := by
  have hev : ∀ᶠ x' in 𝓝 x, (P.prod Q).degIndex (x', y) ≤ (P.prod Q).degIndex (x, y) :=
    (Continuous.prodMk_left y).continuousAt.eventually (lemma_2_4_3 (P.prod Q) (x, y))
  have hfr : ∃ᶠ x' in 𝓝 x, x' ∈ P.smoothSet := mem_closure_iff_frequently.1 (P.dense_smoothSet x)
  obtain ⟨x', hx', hle⟩ := (hfr.and_eventually hev).exists
  exact (degIndex_le_degIndex_prod_right_of_mem_smoothSet hx' y).trans hle

/-- `max(d_X(x), d_Y(y)) ≤ d_{X × Y}(x, y) ≤ d_X(x) + d_Y(y)`. -/
theorem max_degIndex_le_degIndex_prod [ParacompactSpace (X × Y)] (x : X) (y : Y) :
    max (P.degIndex x) (Q.degIndex y) ≤ (P.prod Q).degIndex (x, y) ∧
      (P.prod Q).degIndex (x, y) ≤ P.degIndex x + Q.degIndex y :=
  ⟨max_le (P.degIndex_le_degIndex_prod_left Q x y) (P.degIndex_le_degIndex_prod_right Q x y),
    P.degIndex_prod_le Q x y⟩

/-- **The product formula where `d_Y(y) = 0`**: `d_{X × Y}(x, y) = d_X(x) + d_Y(y)`, for all
M-polyfolds `X`, `Y` and every `x`. -/
theorem degIndex_prod_of_degIndex_eq_zero_right [ParacompactSpace (X × Y)] (x : X) {y : Y}
    (hy : Q.degIndex y = 0) : (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y :=
  le_antisymm (P.degIndex_prod_le Q x y)
    (by rw [hy, add_zero]; exact P.degIndex_le_degIndex_prod_left Q x y)

/-- **The product formula where `d_X(x) = 0`**. -/
theorem degIndex_prod_of_degIndex_eq_zero_left [ParacompactSpace (X × Y)] {x : X}
    (hx : P.degIndex x = 0) (y : Y) : (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y :=
  le_antisymm (P.degIndex_prod_le Q x y)
    (by rw [hx, zero_add]; exact P.degIndex_le_degIndex_prod_right Q x y)

/-- The product formula for a factor without boundary (Definition 2.4.5). -/
theorem degIndex_prod_of_isWithoutBoundary_right [ParacompactSpace (X × Y)]
    (hQ : Q.IsWithoutBoundary) (x : X) (y : Y) :
    (P.prod Q).degIndex (x, y) = P.degIndex x :=
  (P.degIndex_prod_of_degIndex_eq_zero_right Q x (hQ y)).trans (by rw [hQ y, add_zero])

/-- **A reduction of the product formula to the slice `{x} × Y`**: if at one point `y'` the index
of `X × Y` at `(x, y')` is at least `d_Y(y)` below its value at `(x, y)`, then
`d_{X × Y}(x, y) = d_X(x) + d_Y(y)`. -/
theorem degIndex_prod_of_exists_slice [ParacompactSpace (X × Y)] {x : X} {y : Y}
    (h : ∃ y', (P.prod Q).degIndex (x, y') + Q.degIndex y ≤ (P.prod Q).degIndex (x, y)) :
    (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y := by
  obtain ⟨y', hy'⟩ := h
  exact le_antisymm (P.degIndex_prod_le Q x y)
    ((Nat.add_le_add_right (P.degIndex_le_degIndex_prod_left Q x y') _).trans hy')

/-- If `Y` has a point `y'` with `d_Y(y') = 0`, the product formula at `(x, y)` is equivalent to
a drop of the index of `X × Y` by `d_Y(y)` between `(x, y)` and some point of `{x} × Y`. -/
theorem degIndex_prod_iff_exists_slice [ParacompactSpace (X × Y)] (x : X) (y : Y) {y₀ : Y}
    (hy₀ : Q.degIndex y₀ = 0) :
    (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y ↔
      ∃ y', (P.prod Q).degIndex (x, y') + Q.degIndex y ≤ (P.prod Q).degIndex (x, y) := by
  refine ⟨fun h => ⟨y₀, ?_⟩, P.degIndex_prod_of_exists_slice Q⟩
  rw [h, P.degIndex_prod_of_degIndex_eq_zero_right Q x hy₀, hy₀, add_zero]

end MPolyfold

/-! ### The remark after Definition 8.5.1 (comparison item V8.28) -/

section Fibres

universe u v

variable {ObjY MorY : Type u} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type v} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX} {F : EpFunctor Y X}

/-- **The remark after Definition 8.5.1 (p. 383) in general** (comparison item V8.28): for a proper
covering `F` and every morphism `φ`, `d_𝐘(φ) ≤ d_{𝐗 × Y}(F(φ), s(φ)) ≤ 2 · d_𝐘(φ)`. -/
theorem EpFunctor.IsProperCovering.degIndex_le_degIndex_prod_fibredMap
    (hF : F.IsProperCovering) (φ : MorY) :
    letI := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
    Y.PMor.degIndex φ ≤ (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ) ∧
      (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ) ≤ 2 * Y.PMor.degIndex φ := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  refine ⟨?_, hF.degIndex_prod_fibredMap_le φ⟩
  rw [← hF.degIndex_mor φ]
  exact X.PMor.degIndex_le_degIndex_prod_left Y.PObj _ _

/-- **V8.28 at interior morphisms**: if `d_𝐘(φ) = 0`, then `d_{𝐗 × Y}(F(φ), s(φ)) = 2 · d_𝐘(φ)`
and `2 · d_{𝐗 ₛ×_F Y}(F(φ), s(φ)) = d_{𝐗 × Y}(F(φ), s(φ))`; no tameness and no condition on the
charts. -/
theorem EpFunctor.IsProperCovering.degIndex_prod_fibredMap_of_degIndex_eq_zero
    (hF : F.IsProperCovering) (φ : MorY) (h0 : Y.PMor.degIndex φ = 0) :
    letI := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
    letI := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
    (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ) = 2 * Y.PMor.degIndex φ ∧
      2 * (MPolyfold.subPolyfold (MPolyfold.isSubMPolyfold_fibredProduct
        X.isLocalScDiffeo_src F.isScSmoothMap_obj)).degIndex (F.fibredMap φ) =
        (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ) := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
  have h : (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ) = 2 * Y.PMor.degIndex φ :=
    le_antisymm (hF.degIndex_prod_fibredMap_le φ) (by rw [h0]; exact Nat.zero_le _)
  exact ⟨h, by rw [h, ← hF.degIndex_fibredMap]⟩

/-- **V8.28 and the product formula**: for a proper covering `F`, the equality
`2 · d_{𝐗 ₛ×_F Y}(F(φ), s(φ)) = d_{𝐗 × Y}(F(φ), s(φ))` of the remark after Definition 8.5.1 holds at
`φ` exactly when the product formula holds at `(F(φ), s(φ))`. -/
theorem EpFunctor.IsProperCovering.two_mul_degIndex_fibredMap_eq_iff
    (hF : F.IsProperCovering) (φ : MorY) :
    letI := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
    letI := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
    2 * (MPolyfold.subPolyfold (MPolyfold.isSubMPolyfold_fibredProduct
        X.isLocalScDiffeo_src F.isScSmoothMap_obj)).degIndex (F.fibredMap φ) =
        (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ) ↔
      (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ) =
        X.PMor.degIndex (F.mor φ) + Y.PObj.degIndex (Y.src φ) := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
  rw [← hF.degIndex_fibredMap, hF.degIndex_mor, ← Y.degIndex_src]
  constructor <;> intro h <;> omega

end Fibres

end Polyfold

#print axioms Polyfold.MPolyfold.degIndex_le_degIndex_prod_left
#print axioms Polyfold.MPolyfold.degIndex_le_degIndex_prod_right
#print axioms Polyfold.MPolyfold.degIndex_prod_of_degIndex_eq_zero_right
#print axioms Polyfold.MPolyfold.degIndex_prod_of_degIndex_eq_zero_left
#print axioms Polyfold.MPolyfold.degIndex_prod_of_exists_slice
#print axioms Polyfold.MPolyfold.degIndex_prod_iff_exists_slice
#print axioms Polyfold.EpFunctor.IsProperCovering.degIndex_le_degIndex_prod_fibredMap
#print axioms Polyfold.EpFunctor.IsProperCovering.degIndex_prod_fibredMap_of_degIndex_eq_zero
#print axioms Polyfold.EpFunctor.IsProperCovering.two_mul_degIndex_fibredMap_eq_iff
