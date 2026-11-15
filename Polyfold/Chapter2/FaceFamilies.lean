import Polyfold.Chapter2.Tame

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §2.5, p. 72:
**Definition 2.5.10** (faces, face-structured), for a degeneracy function given explicitly.

# Recognising the faces of `d`

## The text, paraphrased

(Definition 2.5.10) A face of a tame M-polyfold `X` is the closure of a connected component of
`\{x | d_X(x) = 1\}`; `X` is face-structured if every `x ∈ X` lies in exactly `d_X(x)` faces.

## What is formalized

The definition only involves the topology of `X` and the function `d_X`, so we state it for a
function `d : Z → ℕ` on a topological space (`IsFaceCount d`;
`MPolyfold.isFaceStructured_iff_isFaceCount`: `X` is face-structured iff `IsFaceCount d_X`).

* `connectedComponentIn_eq_of_family`, **`isFaceCount_of_family`**: let `(U_i)` be open sets
  covering `\{d = 1\}` such that the sets `A_i = \{d = 1\} ∩ U_i` are pairwise disjoint,
  preconnected and non-empty, with pairwise distinct closures `G_i`.  Then the `A_i` are the
  connected components of `\{d = 1\}`, the `G_i` are the faces (`isFace_iff_of_family`), and if
  every `x` lies in exactly `d(x)` of the `G_i`, then `IsFaceCount d`.
* `family_preimage`, `isFaceCount_of_homeomorph`, `isFace_iff_of_homeomorph`: the same data
  on `M`, transported along a homeomorphism `e : Z ≃ₜ M` with `d = d' ∘ e`.
* **`isFaceCount_square`**: the square `[0, 1]²` with `d(t, s) = d_{[0,1]}(t) + d_{[0,1]}(s)`
  (`d_{[0,1]}` is `1` at the end points and `0` inside) has the four faces `\{0\} × [0, 1]`,
  `\{1\} × [0, 1]`, `[0, 1] × \{0\}`, `[0, 1] × \{1\}`, and every point lies in exactly `d` of
  them.
-/

open Set Topology

noncomputable section

namespace Polyfold

universe u v w

section FaceFamilies

variable {Z : Type u} [TopologicalSpace Z]

/-- **The face count of Definition 2.5.10 for a function `d`**: every `x` lies in exactly `d(x)`
of the closures of the connected components of `\{d = 1\}`. -/
def IsFaceCount (d : Z → ℕ) : Prop :=
  ∀ x : Z, {F : Set Z | (∃ y, d y = 1 ∧ F = closure (connectedComponentIn {y | d y = 1} y)) ∧
    x ∈ F}.encard = (d x : ℕ∞)

/-- **The components of `\{d = 1\}`**: if open sets `U_i` cover `\{d = 1\}` and the sets
`A_i = \{d = 1\} ∩ U_i` are pairwise disjoint and preconnected, then the connected component of
`\{d = 1\}` through `y ∈ A_i` is `A_i`. -/
theorem connectedComponentIn_eq_of_family {d : Z → ℕ} {ι : Type v} {U A : ι → Set Z}
    (hU : ∀ i, IsOpen (U i)) (hA : ∀ i, {y | d y = 1} ∩ U i = A i)
    (hcov : ∀ y, d y = 1 → ∃ i, y ∈ U i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)) (hconn : ∀ i, IsPreconnected (A i))
    {i : ι} {y : Z} (hy : y ∈ A i) :
    connectedComponentIn {y | d y = 1} y = A i := by
  have hAD : ∀ j, A j ⊆ {y | d y = 1} := fun j z hz => ((hA j).symm.subset hz).1
  refine Subset.antisymm ?_ ((hconn i).subset_connectedComponentIn hy (hAD i))
  have hyD : y ∈ {y | d y = 1} := hAD i hy
  have hsub := connectedComponentIn_subset {y | d y = 1} y
  have hmem := mem_connectedComponentIn hyD
  have hcov' : connectedComponentIn {y | d y = 1} y ⊆ U i ∪ ⋃ j ∈ {j | j ≠ i}, U j := by
    intro z hz
    obtain ⟨j, hj⟩ := hcov z (hsub hz)
    by_cases hji : j = i
    · subst hji
      exact Or.inl hj
    · exact Or.inr (mem_iUnion₂.2 ⟨j, hji, hj⟩)
  have hempty : connectedComponentIn {y | d y = 1} y ∩ (U i ∩ ⋃ j ∈ {j | j ≠ i}, U j) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun z ⟨hz, hzi, hzV⟩ => ?_
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.1 hzV
    exact Set.disjoint_left.1 (hdisj i j (Ne.symm hj)) ((hA i).subset ⟨hsub hz, hzi⟩)
      ((hA j).subset ⟨hsub hz, hzj⟩)
  rcases isPreconnected_iff_subset_of_disjoint.1 isPreconnected_connectedComponentIn (U i)
      (⋃ j ∈ {j | j ≠ i}, U j) (hU i) (isOpen_biUnion fun j _ => hU j) hcov' hempty with h | h
  · intro z hz
    exact (hA i).subset ⟨hsub hz, h hz⟩
  · exfalso
    obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.1 (h hmem)
    exact Set.disjoint_left.1 (hdisj i j (Ne.symm hj)) hy ((hA j).subset ⟨hyD, hyj⟩)

/-- **The faces of `d`** (Definition 2.5.10): under the hypotheses of
`connectedComponentIn_eq_of_family`, with the `A_i` non-empty and `G_i = closure A_i`, the faces
of `d` are exactly the sets `G_i`. -/
theorem isFace_iff_of_family {d : Z → ℕ} {ι : Type v} {U A G : ι → Set Z}
    (hU : ∀ i, IsOpen (U i)) (hA : ∀ i, {y | d y = 1} ∩ U i = A i)
    (hcov : ∀ y, d y = 1 → ∃ i, y ∈ U i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)) (hconn : ∀ i, IsPreconnected (A i))
    (hne : ∀ i, (A i).Nonempty) (hcl : ∀ i, closure (A i) = G i) (F : Set Z) :
    (∃ y, d y = 1 ∧ F = closure (connectedComponentIn {y | d y = 1} y)) ↔ ∃ i, F = G i := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, hi⟩ := hcov y hy
    refine ⟨i, ?_⟩
    rw [connectedComponentIn_eq_of_family hU hA hcov hdisj hconn ((hA i).subset ⟨hy, hi⟩), hcl]
  · rintro ⟨i, rfl⟩
    obtain ⟨y, hy⟩ := hne i
    refine ⟨y, ((hA i).symm.subset hy).1, ?_⟩
    rw [connectedComponentIn_eq_of_family hU hA hcov hdisj hconn hy, hcl]

/-- **Recognising a face count** (Definition 2.5.10): let open sets `U_i` cover `\{d = 1\}`, let
`A_i = \{d = 1\} ∩ U_i` be pairwise disjoint, preconnected and non-empty, and let the closures
`G_i = closure A_i` be pairwise distinct.  If every `x` lies in exactly `d(x)` of the `G_i`, then
every `x` lies in exactly `d(x)` faces of `d`. -/
theorem isFaceCount_of_family {d : Z → ℕ} {ι : Type v} {U A G : ι → Set Z}
    (hU : ∀ i, IsOpen (U i)) (hA : ∀ i, {y | d y = 1} ∩ U i = A i)
    (hcov : ∀ y, d y = 1 → ∃ i, y ∈ U i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)) (hconn : ∀ i, IsPreconnected (A i))
    (hne : ∀ i, (A i).Nonempty) (hcl : ∀ i, closure (A i) = G i)
    (hinj : Function.Injective G) (hcount : ∀ x, {i | x ∈ G i}.encard = (d x : ℕ∞)) :
    IsFaceCount d := by
  intro x
  have hfaces : {F : Set Z | (∃ y, d y = 1 ∧ F = closure (connectedComponentIn {y | d y = 1} y)) ∧
      x ∈ F} = G '' {i | x ∈ G i} := by
    ext F
    rw [mem_ofPred_eq, isFace_iff_of_family hU hA hcov hdisj hconn hne hcl]
    constructor
    · rintro ⟨⟨i, rfl⟩, hx⟩
      exact ⟨i, hx, rfl⟩
    · rintro ⟨i, hx, rfl⟩
      exact ⟨⟨i, rfl⟩, hx⟩
  rw [hfaces, hinj.encard_image, hcount]

/-- **Transport along a homeomorphism**: the data of `isFaceCount_of_family` for `d'` on `M`
pull back along `e : Z ≃ₜ M` to the same data for `d = d' ∘ e`. -/
theorem family_preimage {M : Type w} [TopologicalSpace M] (e : Z ≃ₜ M) {d : Z → ℕ}
    {d' : M → ℕ} (hd : ∀ z, d z = d' (e z)) {ι : Type v} {U A G : ι → Set M}
    (hU : ∀ i, IsOpen (U i)) (hA : ∀ i, {y | d' y = 1} ∩ U i = A i)
    (hcov : ∀ y, d' y = 1 → ∃ i, y ∈ U i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)) (hconn : ∀ i, IsPreconnected (A i))
    (hne : ∀ i, (A i).Nonempty) (hcl : ∀ i, closure (A i) = G i)
    (hinj : Function.Injective G) (hcount : ∀ x, {i | x ∈ G i}.encard = (d' x : ℕ∞)) :
    (∀ i, IsOpen (e ⁻¹' U i)) ∧ (∀ i, {y | d y = 1} ∩ e ⁻¹' U i = e ⁻¹' A i) ∧
    (∀ y, d y = 1 → ∃ i, y ∈ e ⁻¹' U i) ∧
    (∀ i j, i ≠ j → Disjoint (e ⁻¹' A i) (e ⁻¹' A j)) ∧ (∀ i, IsPreconnected (e ⁻¹' A i)) ∧
    (∀ i, (e ⁻¹' A i).Nonempty) ∧ (∀ i, closure (e ⁻¹' A i) = e ⁻¹' G i) ∧
    Function.Injective (fun i => e ⁻¹' G i) ∧
    (∀ x, {i | x ∈ e ⁻¹' G i}.encard = (d x : ℕ∞)) := by
  refine ⟨fun i => (hU i).preimage e.continuous, fun i => ?_,
    fun y hy => hcov (e y) ((hd y) ▸ hy), fun i j h => (hdisj i j h).preimage e,
    fun i => ?_, fun i => ?_, fun i => ?_,
    fun i j h => hinj (e.surjective.preimage_injective h), fun x => ?_⟩
  · rw [← hA i]
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, hd]
  · rw [← e.image_symm]
    exact (hconn i).image _ e.symm.continuous.continuousOn
  · obtain ⟨y, hy⟩ := hne i
    exact ⟨e.symm y, by rw [mem_preimage, e.apply_symm_apply]; exact hy⟩
  · rw [← e.preimage_closure, hcl i]
  · rw [hd]
    exact hcount (e x)

/-- **Recognising a face count through a homeomorphism**: the data of `isFaceCount_of_family`
for `d'` on `M` give `IsFaceCount d` for `d = d' ∘ e`, `e : Z ≃ₜ M`. -/
theorem isFaceCount_of_homeomorph {M : Type w} [TopologicalSpace M] (e : Z ≃ₜ M) {d : Z → ℕ}
    {d' : M → ℕ} (hd : ∀ z, d z = d' (e z)) {ι : Type v} {U A G : ι → Set M}
    (hU : ∀ i, IsOpen (U i)) (hA : ∀ i, {y | d' y = 1} ∩ U i = A i)
    (hcov : ∀ y, d' y = 1 → ∃ i, y ∈ U i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)) (hconn : ∀ i, IsPreconnected (A i))
    (hne : ∀ i, (A i).Nonempty) (hcl : ∀ i, closure (A i) = G i)
    (hinj : Function.Injective G) (hcount : ∀ x, {i | x ∈ G i}.encard = (d' x : ℕ∞)) :
    IsFaceCount d := by
  obtain ⟨hU', hA', hcov', hdisj', hconn', hne', hcl', hinj', hcount'⟩ :=
    family_preimage e hd hU hA hcov hdisj hconn hne hcl hinj hcount
  exact isFaceCount_of_family hU' hA' hcov' hdisj' hconn' hne' hcl' hinj' hcount'

/-- **The faces through a homeomorphism**: under the hypotheses of `isFaceCount_of_homeomorph`,
the faces of `d = d' ∘ e` are exactly the sets `e⁻¹(G_i)`. -/
theorem isFace_iff_of_homeomorph {M : Type w} [TopologicalSpace M] (e : Z ≃ₜ M) {d : Z → ℕ}
    {d' : M → ℕ} (hd : ∀ z, d z = d' (e z)) {ι : Type v} {U A G : ι → Set M}
    (hU : ∀ i, IsOpen (U i)) (hA : ∀ i, {y | d' y = 1} ∩ U i = A i)
    (hcov : ∀ y, d' y = 1 → ∃ i, y ∈ U i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)) (hconn : ∀ i, IsPreconnected (A i))
    (hne : ∀ i, (A i).Nonempty) (hcl : ∀ i, closure (A i) = G i)
    (hinj : Function.Injective G) (hcount : ∀ x, {i | x ∈ G i}.encard = (d' x : ℕ∞))
    (F : Set Z) :
    (∃ y, d y = 1 ∧ F = closure (connectedComponentIn {y | d y = 1} y)) ↔ ∃ i, F = e ⁻¹' G i := by
  obtain ⟨hU', hA', hcov', hdisj', hconn', hne', hcl', -, -⟩ :=
    family_preimage e hd hU hA hcov hdisj hconn hne hcl hinj hcount
  exact isFace_iff_of_family hU' hA' hcov' hdisj' hconn' hne' hcl' F

end FaceFamilies

/-- **Definition 2.5.10 through `IsFaceCount`**: `X` is face-structured iff every `x` lies in
exactly `d_X(x)` faces of the function `d_X`. -/
theorem MPolyfold.isFaceStructured_iff_isFaceCount {X : Type u} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] (P : MPolyfold X) : P.IsFaceStructured ↔ IsFaceCount P.degIndex :=
  Iff.rfl

/-! ### The square `[0, 1]²` -/

section Square

/-- `d_{[0, 1]}(t)`: `1` at the end points, `0` inside. -/
def endDeg (t : unitInterval) : ℕ := if (t : ℝ) = 0 ∨ (t : ℝ) = 1 then 1 else 0

/-- The end point `0` (for `false`) or `1` (for `true`) of `[0, 1]`. -/
def endPt (b : Bool) : unitInterval := if b then 1 else 0

/-- The half `[0, 1/2)` (for `false`) or `(1/2, 1]` (for `true`) of `[0, 1]` near `endPt b`. -/
def endHalf (b : Bool) : Set unitInterval :=
  if b then {t | (1 / 2 : ℝ) < t} else {t | (t : ℝ) < 1 / 2}

theorem isOpen_endHalf (b : Bool) : IsOpen (endHalf b) := by
  cases b
  · exact isOpen_lt continuous_subtype_val continuous_const
  · exact isOpen_lt continuous_const continuous_subtype_val

theorem endPt_mem_endHalf (b : Bool) : endPt b ∈ endHalf b := by
  cases b
  · change ((0 : unitInterval) : ℝ) < 1 / 2
    norm_num
  · change (1 / 2 : ℝ) < ((1 : unitInterval) : ℝ)
    norm_num

theorem mem_Ioo_iff_endDeg_eq_zero (t : unitInterval) :
    t ∈ Ioo (0 : unitInterval) 1 ↔ endDeg t = 0 := by
  have h0 : (0 : ℝ) ≤ t := t.2.1
  have h1 : (t : ℝ) ≤ 1 := t.2.2
  rw [endDeg, mem_Ioo, ← Subtype.coe_lt_coe, ← Subtype.coe_lt_coe]
  change 0 < (t : ℝ) ∧ (t : ℝ) < 1 ↔ _
  split_ifs with h
  · simp only [iff_false, not_and, not_lt]
    rcases h with h | h <;> intro h' <;> linarith
  · simp only [not_or] at h
    simp only [iff_true]
    exact ⟨lt_of_le_of_ne h0 (Ne.symm h.1), lt_of_le_of_ne h1 h.2⟩

theorem endDeg_eq_one_iff (t : unitInterval) : endDeg t = 1 ↔ ∃ b, t = endPt b := by
  rw [endDeg]
  constructor
  · intro h
    split_ifs at h with h'
    · rcases h' with h' | h'
      · exact ⟨false, Subtype.ext h'⟩
      · exact ⟨true, Subtype.ext h'⟩
  · rintro ⟨b, rfl⟩
    cases b
    · exact if_pos (Or.inl rfl)
    · exact if_pos (Or.inr rfl)

theorem endDeg_le_one (t : unitInterval) : endDeg t ≤ 1 := by
  unfold endDeg
  split_ifs <;> omega

theorem endPt_mem_endHalf_iff (b c : Bool) : endPt c ∈ endHalf b ↔ c = b := by
  cases b <;> cases c <;> simp only [endPt, endHalf, Bool.false_eq_true, ↓reduceIte, mem_ofPred_eq,
    reduceCtorEq, iff_false, iff_true] <;> norm_num

theorem endPt_injective : Function.Injective endPt := fun b c h =>
  (endPt_mem_endHalf_iff c b).1 (by rw [h]; exact endPt_mem_endHalf c)

theorem encard_endPt (t : unitInterval) : {b : Bool | t = endPt b}.encard = (endDeg t : ℕ∞) := by
  by_cases h0 : (t : ℝ) = 0
  · have : {b : Bool | t = endPt b} = {false} := by
      ext b
      cases b <;> simp [endPt, Subtype.ext_iff, h0]
    rw [this, encard_singleton, endDeg, if_pos (Or.inl h0)]
    rfl
  · by_cases h1 : (t : ℝ) = 1
    · have : {b : Bool | t = endPt b} = {true} := by
        ext b
        cases b <;> simp [endPt, Subtype.ext_iff, h1]
      rw [this, encard_singleton, endDeg, if_pos (Or.inr h1)]
      rfl
    · have : {b : Bool | t = endPt b} = ∅ := by
        ext b
        cases b <;> simp [endPt, Subtype.ext_iff, h0, h1]
      rw [this, encard_empty, endDeg, if_neg (not_or.2 ⟨h0, h1⟩)]
      rfl

/-- `d(t, s) = d_{[0,1]}(t) + d_{[0,1]}(s)` on the square `[0, 1]²`. -/
def squareDeg (p : unitInterval × unitInterval) : ℕ := endDeg p.1 + endDeg p.2

/-- The open sets `U_i` of the square: `endHalf b × (0, 1)` and `(0, 1) × endHalf b`. -/
def squareU : Bool ⊕ Bool → Set (unitInterval × unitInterval)
  | .inl b => endHalf b ×ˢ Ioo 0 1
  | .inr b => Ioo 0 1 ×ˢ endHalf b

/-- The components `A_i` of `\{d = 1\}`: `\{b\} × (0, 1)` and `(0, 1) × \{b\}`. -/
def squareA : Bool ⊕ Bool → Set (unitInterval × unitInterval)
  | .inl b => {endPt b} ×ˢ Ioo 0 1
  | .inr b => Ioo 0 1 ×ˢ {endPt b}

/-- The faces `G_i` of the square: `\{b\} × [0, 1]` and `[0, 1] × \{b\}`. -/
def squareG : Bool ⊕ Bool → Set (unitInterval × unitInterval)
  | .inl b => {p | p.1 = endPt b}
  | .inr b => {p | p.2 = endPt b}

theorem closure_Ioo_unitInterval : closure (Ioo (0 : unitInterval) 1) = univ := by
  rw [closure_Ioo zero_ne_one]
  exact eq_univ_of_forall fun t => ⟨t.2.1, t.2.2⟩

/-- **The faces of the square** (Definition 2.5.10): the data of `isFaceCount_of_family` for the
square `[0, 1]²` with `d(t, s) = d_{[0,1]}(t) + d_{[0,1]}(s)`. -/
theorem squareFamily :
    (∀ i, IsOpen (squareU i)) ∧ (∀ i, {y | squareDeg y = 1} ∩ squareU i = squareA i) ∧
    (∀ y, squareDeg y = 1 → ∃ i, y ∈ squareU i) ∧
    (∀ i j, i ≠ j → Disjoint (squareA i) (squareA j)) ∧ (∀ i, IsPreconnected (squareA i)) ∧
    (∀ i, (squareA i).Nonempty) ∧ (∀ i, closure (squareA i) = squareG i) ∧
    Function.Injective squareG ∧
    (∀ x, {i | x ∈ squareG i}.encard = (squareDeg x : ℕ∞)) := by
  have hmid : (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) ∈ Ioo (0 : unitInterval) 1 := by
    rw [mem_Ioo, ← Subtype.coe_lt_coe, ← Subtype.coe_lt_coe]
    change (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1
    norm_num
  have hone : ∀ t : unitInterval, endDeg t = 1 ∨ endDeg t = 0 := fun t => by
    have := endDeg_le_one t
    omega
  have hmid0 : endDeg (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) = 0 :=
    (mem_Ioo_iff_endDeg_eq_zero _).1 hmid
  have hmidne : ∀ c, (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) ≠ endPt c := fun c h => by
    rw [h, (endDeg_eq_one_iff _).2 ⟨c, rfl⟩] at hmid0
    exact one_ne_zero hmid0
  have hpt : ∀ i, ∃ p ∈ squareG i, ∀ j, p ∈ squareG j → j = i := fun i => by
    rcases i with b | b
    · refine ⟨(endPt b, ⟨1 / 2, by norm_num, by norm_num⟩), rfl, fun j hj => ?_⟩
      rcases j with c | c
      · exact congrArg Sum.inl (endPt_injective hj).symm
      · exact absurd hj (hmidne c)
    · refine ⟨(⟨1 / 2, by norm_num, by norm_num⟩, endPt b), rfl, fun j hj => ?_⟩
      rcases j with c | c
      · exact absurd hj (hmidne c)
      · exact congrArg Sum.inr (endPt_injective hj).symm
  refine ⟨fun i => ?_, fun i => ?_, fun y hy => ?_, fun i j hij => ?_, fun i => ?_, fun i => ?_,
    fun i => ?_, fun i j hij => ?_, fun x => ?_⟩
  · rcases i with b | b
    · exact (isOpen_endHalf b).prod isOpen_Ioo
    · exact isOpen_Ioo.prod (isOpen_endHalf b)
  · ext ⟨t, s⟩
    rcases i with b | b
    · simp only [squareU, squareA, squareDeg, mem_inter_iff, mem_ofPred_eq, mem_prod,
        mem_singleton_iff, mem_Ioo_iff_endDeg_eq_zero]
      constructor
      · rintro ⟨h, ht, hs⟩
        rw [hs, add_zero, endDeg_eq_one_iff] at h
        obtain ⟨c, rfl⟩ := h
        rw [(endPt_mem_endHalf_iff b c).1 ht]
        exact ⟨rfl, hs⟩
      · rintro ⟨rfl, hs⟩
        exact ⟨by rw [hs, add_zero, endDeg_eq_one_iff]; exact ⟨b, rfl⟩, endPt_mem_endHalf b, hs⟩
    · simp only [squareU, squareA, squareDeg, mem_inter_iff, mem_ofPred_eq, mem_prod,
        mem_singleton_iff, mem_Ioo_iff_endDeg_eq_zero]
      constructor
      · rintro ⟨h, ht, hs⟩
        rw [ht, zero_add, endDeg_eq_one_iff] at h
        obtain ⟨c, rfl⟩ := h
        rw [(endPt_mem_endHalf_iff b c).1 hs]
        exact ⟨ht, rfl⟩
      · rintro ⟨ht, rfl⟩
        exact ⟨by rw [ht, zero_add, endDeg_eq_one_iff]; exact ⟨b, rfl⟩, ht, endPt_mem_endHalf b⟩
  · obtain ⟨t, s⟩ := y
    simp only [squareDeg] at hy
    rcases hone t with ht | ht
    · rw [ht] at hy
      have hs : endDeg s = 0 := by omega
      obtain ⟨b, rfl⟩ := (endDeg_eq_one_iff t).1 ht
      exact ⟨.inl b, endPt_mem_endHalf b, (mem_Ioo_iff_endDeg_eq_zero s).2 hs⟩
    · rw [ht, zero_add, endDeg_eq_one_iff] at hy
      obtain ⟨b, rfl⟩ := hy
      exact ⟨.inr b, (mem_Ioo_iff_endDeg_eq_zero t).2 ht, endPt_mem_endHalf b⟩
  · refine Set.disjoint_left.2 fun ⟨t, s⟩ hi hj => ?_
    rcases i with b | b <;> rcases j with c | c
    · obtain ⟨h1, -⟩ := hi
      obtain ⟨h2, -⟩ := hj
      have h1 : t = endPt b := h1
      have h2 : t = endPt c := h2
      have := (endPt_mem_endHalf_iff c b).1 (h1 ▸ h2 ▸ endPt_mem_endHalf c)
      exact hij (by rw [this])
    · obtain ⟨h1, -⟩ := hi
      obtain ⟨h2, -⟩ := hj
      have h1 : t = endPt b := h1
      rw [h1, mem_Ioo_iff_endDeg_eq_zero, (endDeg_eq_one_iff _).2 ⟨b, rfl⟩] at h2
      exact one_ne_zero h2
    · obtain ⟨h1, -⟩ := hi
      obtain ⟨h2, -⟩ := hj
      have h2 : t = endPt c := h2
      rw [h2, mem_Ioo_iff_endDeg_eq_zero, (endDeg_eq_one_iff _).2 ⟨c, rfl⟩] at h1
      exact one_ne_zero h1
    · obtain ⟨-, h1⟩ := hi
      obtain ⟨-, h2⟩ := hj
      have h1 : s = endPt b := h1
      have h2 : s = endPt c := h2
      have := (endPt_mem_endHalf_iff c b).1 (h1 ▸ h2 ▸ endPt_mem_endHalf c)
      exact hij (by rw [this])
  · rcases i with b | b
    · exact isPreconnected_singleton.prod isPreconnected_Ioo
    · exact isPreconnected_Ioo.prod isPreconnected_singleton
  · rcases i with b | b
    · exact ⟨(endPt b, _), rfl, hmid⟩
    · exact ⟨(_, endPt b), hmid, rfl⟩
  · rcases i with b | b
    · change closure ({endPt b} ×ˢ Ioo 0 1) = _
      rw [closure_prod_eq, closure_singleton, closure_Ioo_unitInterval]
      ext p
      simp [squareG]
    · change closure (Ioo 0 1 ×ˢ {endPt b}) = _
      rw [closure_prod_eq, closure_singleton, closure_Ioo_unitInterval]
      ext p
      simp [squareG]
  · obtain ⟨p, hp, hpj⟩ := hpt i
    exact (hpj j (hij ▸ hp)).symm
  · have hset : {i | x ∈ squareG i} =
        Sum.inl '' {b | x.1 = endPt b} ∪ Sum.inr '' {b | x.2 = endPt b} := by
      ext i
      rcases i with b | b <;> simp [squareG]
    rw [hset, encard_union_eq, Sum.inl_injective.encard_image, Sum.inr_injective.encard_image,
      encard_endPt, encard_endPt, squareDeg, Nat.cast_add]
    exact Set.disjoint_left.2 fun i ⟨b, _, hb⟩ ⟨c, _, hc⟩ => by
      rw [← hb] at hc
      exact Sum.inr_ne_inl hc

/-- **The square `[0, 1]²` is face-structured** (Definition 2.5.10): every `(t, s)` lies in
exactly `d_{[0,1]}(t) + d_{[0,1]}(s)` faces of `d`. -/
theorem isFaceCount_square : IsFaceCount squareDeg := by
  obtain ⟨hU, hA, hcov, hdisj, hconn, hne, hcl, hinj, hcount⟩ := squareFamily
  exact isFaceCount_of_family hU hA hcov hdisj hconn hne hcl hinj hcount

end Square

end Polyfold
