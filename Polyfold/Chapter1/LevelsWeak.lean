import Polyfold.Chapter2.StrongBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §1.2,
**Proposition 1.2.4 (preprint 1.19) and Corollary 1.2.5 (preprint 1.20) under the text's hypothesis** (the proofs are those of
[25] = arXiv 1002.3381, Proposition 2.4 and Corollary 2.5, with the inductive statement `(S_k)`
written out in `Exposition/Chapter1.md` §3.4).

# Proposition 1.2.4 (preprint 1.19) with the shifted-level hypothesis

## The text

(Proposition 1.2.4 (preprint 1.19)) Let `U` be a relatively open subset of a partial quadrant in an sc-Banach space
`E` and `F` another sc-Banach space.  Assume that for every `m ≥ 0` and `0 ≤ l ≤ k` the map `f`
induces a map `f : U_{m+l} → F_m` of class `C^{l+1}`.  Then `f` is sc^{k+1}.  (Corollary 1.2.5 (preprint 1.20)) If
`f : U → ℝᴺ` and for all `0 ≤ l ≤ k` the map `f : U_l → ℝᴺ` is `C^{l+1}`, then `f` is sc^{k+1}.

`Polyfold/Chapter1/Levels.lean` proves both under the stronger hypothesis that every level map
`f : U_m → F_m` is `C^{k+1}`; this file proves them as stated.

## The proof, and what is formalized

The text's hypothesis is **sufficient**; the proof is an induction carrying along a description of
the iterated tangent maps `T^j f`, whose components are *elementary maps*
`(x, h₁, …, h_i) ↦ d^i f(x)(h₁, …, h_i)` on mixed levels (the statement `(S_k)` of [25]).  The
induction cannot be run on the hypothesis itself: if `f` satisfies it with `k`, `Tf` does not in
general satisfy it with `k − 1` (the second component `(x, h) ↦ Df(x)h : U_{m+l+1} × E_{m+l} → F_m`
is only `C^l`, one order short, `Df(x)h` for `h ∈ E_{m+l}` being the derivative of the `C^{l+1}`
map `f : U_{m+l} → F_m`); the elementary maps remember `f`, whose lower-level regularity supplies
the missing order.

* `Polyfold.IsDerivTower k U f Φ Ψ` (**the derivative tower**): `Ψ i m l x`, `x ∈ U_{m+l}`, is the
  `i`-th derivative of `f : U_{m+l} → F_m` as a continuous `i`-linear map on `E_{m+l}`, for
  `i ≤ l + 1` and `i ≤ k + 1` (this is where the hypothesis `f : U_{m+l} → F_m ∈ C^{l+1}` enters:
  the `i`-th derivative exists and is continuous for `i ≤ l + 1`); it is differentiable with
  derivative `Ψ (i+1) m l x` for `i ≤ l`, `i ≤ k`; and all these multilinear maps are restrictions
  of one base-level function `Φ i` (the compatibility across levels, which the text uses tacitly
  through the single symbol `d^j f(x)`).  `Polyfold.isDerivTower_of_contDiffOn_levels` builds the
  tower from the text's hypothesis with Mathlib's `iteratedFDerivWithin`.
* `Polyfold.ElemData E X i` (**elementary maps**, the "maps of type `(p, l; n₁, …, n_j)`" of the
  exposition): on an sc-Banach space `X`, an sc-operator `π₀ : X → E^p` (the base-point slot) and
  sc-operators `π_a : X → E^{n_a}` (`a < i`, the vector slots) with target shift `m`;
  `ElemData.map Φ : X → F^m` is `z ↦ Φ i (π₀ z) (π_1 z, …, π_i z)`, i.e.
  `d^i f(π₀ z)(π_1 z, …, π_i z)`, on the domain `π₀⁻¹(U_p)`.  Under the index conditions
  `m + i ≤ p` and `m + i ≤ n_a + 1` (the `j + l - 1 ≤ n_a` of `(S_k)`; the upper bound `n_a ≤ k`
  of `(S_k)` is replaced by `i ≤ k`, which is what the proof uses):
  - `ElemData.isSc0`: the elementary map is sc⁰;
  - `ElemData.isSc1Levels`, `ElemData.isSc1With`: it is sc¹, by the level criterion of
    Proposition 1.2.1 (preprint 1.16) (`IsSc1Levels`), with the derivative (3.5) of the exposition
    `(δx, δh) ↦ d^{i+1}f(x)(δx, h) + Σ_a d^i f(x)(h with h_a := δh_a)`, which is continuous one
    level down because `d^{i+1} f` and `d^i f` exist one level further down;
  - `ElemData.tangentMap_eqOn`: its tangent map is the pairing of the shifted elementary map
    with the sum of `i + 1` elementary maps on `TX` (the "form of `T^{k+2} f`" of the exposition);
  - `ElemData.isSck`: by induction on `s`, every elementary map with `i + s ≤ k + 1` is sc^s.
* **Proposition 1.2.4 (preprint 1.19)** (`Polyfold.proposition_1_2_4_text`): `f : U → F` sc⁰ on an sc-domain with
  `f : U_{m+l} → F_m` of class `C^{l+1}` for all `m` and `l ≤ k` is sc^{k+1}: it is the elementary
  map `ElemData.base` with `i = 0`, `p = m = 0`, transported along `E ≅ E^0`, `F^0 ≅ F`.
  `Polyfold.IsScSmooth.of_contDiffOn_levels_text`: if `f : U_{m+l} → F_m` is `C^{l+1}` for all
  `m, l`, then `f` is sc-smooth.
* **Corollary 1.2.5 (preprint 1.20)** (`Polyfold.corollary_1_2_5_text`): `f : U → V` into a finite-dimensional space
  (constant sc-structure) with `f : U_l → V` of class `C^{l+1}` for `l ≤ k` is sc^{k+1};
  `Polyfold.IsScSmooth.of_contDiffOn_levels_finiteDimensional_text`: `C^{l+1}` on `U_l` for every
  `l` gives sc-smooth.

## What the text leaves implicit, and the choices made

* The compatibility of `d^j f(x)` taken on different levels (domain level lowered, target level
  raised) is the field `IsDerivTower.toBase`; it is proved from Mathlib's
  `iteratedFDerivWithin_comp_left/right` (chain rule for compositions with continuous linear maps).
* The index bookkeeping of `(S_k)` is carried by `ElemData` with the two inequalities above; the
  text's third inequality `n_a ≤ k` is not needed.
* The shifted spaces `E^p` are `ScBanach.shiftAdd E p` with `(E^p)_l = E_{p+l}` definitionally;
  `(E^p)^1 ≅ E^{p+1}` and `E ≅ E^0` are sc-isomorphisms given by casts along `p + (l+1) = p+1+l`
  and `l = 0 + l` (`ScBanach.castCLE`), used through their compatibility with the inclusions to the
  base level (`toBase_castCLE`) only.
* Pairings and sc-operators: `IsSck.scPair`, `ScOperator.isScSmooth`, `isScDomain_univ` of
  `Polyfold/Chapter2/StrongBundle.lean` and `Polyfold/Chapter2/TangentBundle.lean` are Chapter-1
  facts that live in Chapter 2 files; this file imports them (hence the import of a Chapter 2 file
  from Chapter 1).
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### Casts between levels, the shift `E^p`, inclusions `E_a → E_b` for `b ≤ a` -/

namespace ScBanach

variable (E : ScBanach)

/-- The identification `E_a = E_b` for `a = b`. -/
def castCLE {a b : ℕ} (h : a = b) : E a ≃L[ℝ] E b := by
  subst h; exact ContinuousLinearEquiv.refl ℝ (E a)

lemma toBase_castCLE {a b : ℕ} (h : a = b) (x : E a) :
    E.toBase b (E.castCLE h x) = E.toBase a x := by
  subst h; rfl

lemma castCLE_symm {a b : ℕ} (h : a = b) : (E.castCLE h).symm = E.castCLE h.symm := by
  subst h; rfl

lemma toBase_castCLE_symm {a b : ℕ} (h : a = b) (y : E b) :
    E.toBase a ((E.castCLE h).symm y) = E.toBase b y := by
  rw [castCLE_symm, toBase_castCLE]

/-- The inclusion `E_a → E_b` for `b ≤ a`. -/
def inclLE {a b : ℕ} (h : b ≤ a) : E a →L[ℝ] E b :=
  (E.inclK b (a - b)).comp (E.castCLE (show a = b + (a - b) by omega)).toContinuousLinearMap

lemma toBase_inclLE {a b : ℕ} (h : b ≤ a) (x : E a) : E.toBase b (E.inclLE h x) = E.toBase a x := by
  simp only [inclLE, ContinuousLinearMap.comp_apply]
  rw [E.toBase_inclK]
  exact E.toBase_castCLE _ x

/-- Two level vectors with the same image in `E₀` are equal when their levels coincide. -/
lemma eq_of_toBase_eq {a : ℕ} {x y : E a} (h : E.toBase a x = E.toBase a y) : x = y :=
  E.toBase_injective a h

lemma inclLE_mem_lvlSet {U : Set (E 0)} {a b : ℕ} (h : b ≤ a) {x : E a} (hx : x ∈ E.lvlSet U a) :
    E.inclLE h x ∈ E.lvlSet U b := by
  rw [mem_lvlSet, toBase_inclLE]; exact hx

lemma preimage_inclLE_lvlSet (U : Set (E 0)) {a b : ℕ} (h : b ≤ a) :
    E.inclLE h ⁻¹' E.lvlSet U b = E.lvlSet U a := by
  ext x; rw [mem_preimage, mem_lvlSet, mem_lvlSet, toBase_inclLE]

end ScBanach

namespace ScScale

variable (E : ScScale)

/-- The scale `E^p` with `(E^p)_l = E_{p+l}` (definitionally). -/
abbrev shiftAddScale (p : ℕ) : ScScale where
  lvl l := E (p + l)
  incl l := E.incl (p + l)
  incl_injective l := E.incl_injective (p + l)
  incl_isCompactOperator l := E.incl_isCompactOperator (p + l)

lemma shiftAddScale_toBase (p l : ℕ) (x : E (p + l)) :
    E.toBase (p + l) x = E.toBase p ((E.shiftAddScale p).toBase l x) := by
  induction l with
  | zero => rfl
  | succ l ih => exact ih _

end ScScale

namespace ScBanach

variable (E : ScBanach)

lemma shiftAddScale_smoothLvl (p l : ℕ) :
    (E.toScScale.shiftAddScale p).smoothLvl l = E.smoothLvl (p + l) := by
  ext x
  rw [ScScale.mem_smoothLvl_iff, ScScale.mem_smoothLvl_iff]
  constructor
  · intro h j
    obtain ⟨y, hy⟩ := h j
    refine ⟨E.inclLE (Nat.le_add_left j p) y, ?_⟩
    rw [toBase_inclLE, ScScale.shiftAddScale_toBase, ScScale.shiftAddScale_toBase E.toScScale p l x]
    exact congrArg (E.toBase p) hy
  · intro h j
    obtain ⟨y, hy⟩ := h (p + j)
    refine ⟨y, E.toBase_injective p ?_⟩
    rw [← ScScale.shiftAddScale_toBase, ← ScScale.shiftAddScale_toBase]
    exact hy

/-- The `p`-fold level shift `E^p`, with `(E^p)_l = E_{p+l}` definitionally (compare
`ScBanach.shiftK`, defined by iterating `shift`). -/
abbrev shiftAdd (p : ℕ) : ScBanach where
  toScScale := E.toScScale.shiftAddScale p
  dense_smooth l := by rw [shiftAddScale_smoothLvl]; exact E.dense_smooth (p + l)

@[simp] lemma shiftAdd_lvl (p l : ℕ) : E.shiftAdd p l = E (p + l) := rfl

lemma shiftAdd_toBase (p l : ℕ) (x : E (p + l)) :
    E.toBase (p + l) x = E.toBase p ((E.shiftAdd p).toBase l x) :=
  ScScale.shiftAddScale_toBase _ p l x

/-- `E ≅ E^0`. -/
def shiftAddZeroIso : ScIso E (E.shiftAdd 0) where
  lvl l := E.castCLE (Nat.zero_add l).symm
  incl_comm l x := by
    apply E.toBase_injective (0 + l)
    exact (E.toBase_castCLE (Nat.zero_add (l + 1)).symm x).trans
      ((E.toBase_succ l x).trans (E.toBase_castCLE (Nat.zero_add l).symm (E.incl l x)).symm)

lemma toBase_shiftAddZeroIso (l : ℕ) (x : E l) :
    E.toBase (0 + l) (E.shiftAddZeroIso l x) = E.toBase l x :=
  E.toBase_castCLE _ x

/-- `(E^p)^1 ≅ E^{p+1}`. -/
def shiftAddShiftIso (p : ℕ) : ScIso (E.shiftAdd p).shift (E.shiftAdd (p + 1)) where
  lvl l := E.castCLE (by omega : p + (l + 1) = p + 1 + l)
  incl_comm l x := by
    apply E.toBase_injective (p + 1 + l)
    exact (E.toBase_succ (p + 1 + l) _).symm.trans
      ((E.toBase_castCLE _ x).trans ((E.toBase_succ (p + (l + 1)) x).trans
        (E.toBase_castCLE (by omega : p + (l + 1) = p + 1 + l) (E.incl (p + (l + 1)) x)).symm))

lemma toBase_shiftAddShiftIso (p l : ℕ) (x : E (p + (l + 1))) :
    E.toBase (p + 1 + l) (E.shiftAddShiftIso p l x) = E.toBase (p + (l + 1)) x :=
  E.toBase_castCLE _ x

lemma toBase_shiftAddShiftIso_symm (p l : ℕ) (y : E (p + 1 + l)) :
    E.toBase (p + (l + 1)) ((E.shiftAddShiftIso p).symm l y) = E.toBase (p + 1 + l) y :=
  E.toBase_castCLE_symm _ y

end ScBanach

/-! ### Sc-operators: shifts, projections, sums -/

namespace ScOperator

variable {X Y : ScBanach}

/-- The shift `T : X¹ → Y¹` of an sc-operator `T : X → Y`. -/
def shift (T : ScOperator X Y) : ScOperator X.shift Y.shift where
  lvl l := T (l + 1)
  incl_comm l x := T.incl_comm (l + 1) x

@[simp] lemma shift_apply (T : ScOperator X Y) (l : ℕ) (x : X (l + 1)) : T.shift l x = T (l + 1) x :=
  rfl

/-- The zero sc-operator. -/
def zeroOp (X Y : ScBanach) : ScOperator X Y where
  lvl _ := 0
  incl_comm _ _ := by simp

/-- Addition `Y ⊕ Y → Y` as an sc-operator. -/
def addOp (Y : ScBanach) : ScOperator (Y.prod Y) Y where
  lvl l := ContinuousLinearMap.fst ℝ (Y l) (Y l) + ContinuousLinearMap.snd ℝ (Y l) (Y l)
  incl_comm _ _ := by simp

end ScOperator

variable {X Y : ScBanach} {W : Set (X 0)}

/-- The constant map `0` is sc^k. -/
theorem IsSck.zero (hW : IsScDomain X W) (k : ℕ) : IsSck k X Y W (fun _ => 0) :=
  (ScOperator.zeroOp X Y).isScSmooth hW k

/-- The sum of two sc^k maps is sc^k (`g₁ + g₂ = add ∘ (g₁, g₂)`). -/
theorem IsSck.add {k : ℕ} (hW : IsScDomain X W) {g₁ g₂ : X 0 → Y 0} (h₁ : IsSck k X Y W g₁)
    (h₂ : IsSck k X Y W g₂) : IsSck k X Y W (fun z => g₁ z + g₂ z) :=
  IsSck.comp hW (isScDomain_univ _) ((ScOperator.addOp Y).isScSmooth (isScDomain_univ _) k)
    (IsSck.scPair hW h₁ h₂) (mapsTo_univ _ _)

/-- A finite sum of sc^k maps is sc^k. -/
theorem IsSck.sum {k : ℕ} (hW : IsScDomain X W) {ι : Type} (s : Finset ι) {g : ι → X 0 → Y 0}
    (hg : ∀ a ∈ s, IsSck k X Y W (g a)) : IsSck k X Y W (fun z => ∑ a ∈ s, g a z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsSck.zero hW k
  | insert a s has ih =>
    simp only [Finset.sum_insert has]
    exact IsSck.add hW (hg a (Finset.mem_insert_self a s))
      (ih fun b hb => hg b (Finset.mem_insert_of_mem hb))

/-! ### The derivative of the evaluation of a multilinear map -/

section Eval

variable {ι : Type} [Fintype ι] {M : ι → Type} [∀ a, NormedAddCommGroup (M a)]
  [∀ a, NormedSpace ℝ (M a)] {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The evaluation `(A, h) ↦ A h`, written through `flipMultilinear`. -/
lemma cmm_eval_eq :
    (fun q : ContinuousMultilinearMap ℝ M Z × (∀ a, M a) => q.1 q.2) =
      fun q => (ContinuousLinearMap.id ℝ (ContinuousMultilinearMap ℝ M Z)).flipMultilinear q.2 q.1 := by
  funext q; simp

/-- The evaluation `(A, h) ↦ A h` of continuous multilinear maps is differentiable, with derivative
`(B, η) ↦ B h + Σ_a A(h with h_a := η_a)` at `(A, h)`. -/
theorem hasFDerivAt_cmm_eval [DecidableEq ι] (A : ContinuousMultilinearMap ℝ M Z) (h : ∀ a, M a) :
    HasFDerivAt (fun q : ContinuousMultilinearMap ℝ M Z × (∀ a, M a) => q.1 q.2)
      ((ContinuousMultilinearMap.apply ℝ M Z h).comp
          (ContinuousLinearMap.fst ℝ (ContinuousMultilinearMap ℝ M Z) (∀ a, M a)) +
        (A.linearDeriv h).comp
          (ContinuousLinearMap.snd ℝ (ContinuousMultilinearMap ℝ M Z) (∀ a, M a))) (A, h) := by
  have hc : HasFDerivAt (fun q : ContinuousMultilinearMap ℝ M Z × (∀ a, M a) =>
      (ContinuousLinearMap.id ℝ (ContinuousMultilinearMap ℝ M Z)).flipMultilinear q.2)
      (((ContinuousLinearMap.id ℝ (ContinuousMultilinearMap ℝ M Z)).flipMultilinear.linearDeriv h).comp
        (ContinuousLinearMap.snd ℝ (ContinuousMultilinearMap ℝ M Z) (∀ a, M a))) (A, h) :=
    (ContinuousMultilinearMap.hasFDerivAt _ h).comp (A, h) hasFDerivAt_snd
  have hu : HasFDerivAt (fun q : ContinuousMultilinearMap ℝ M Z × (∀ a, M a) => q.1)
      (ContinuousLinearMap.fst ℝ (ContinuousMultilinearMap ℝ M Z) (∀ a, M a)) (A, h) :=
    hasFDerivAt_fst
  have h1 := hc.clm_apply hu
  rw [cmm_eval_eq]
  have hL : ∀ q : ContinuousMultilinearMap ℝ M Z × (∀ a, M a),
      ((ContinuousLinearMap.id ℝ (ContinuousMultilinearMap ℝ M Z)).flipMultilinear (A, h).2 ∘L
        ContinuousLinearMap.fst ℝ (ContinuousMultilinearMap ℝ M Z) ((a : ι) → M a) +
      ((ContinuousLinearMap.id ℝ (ContinuousMultilinearMap ℝ M Z)).flipMultilinear.linearDeriv h ∘L
            ContinuousLinearMap.snd ℝ (ContinuousMultilinearMap ℝ M Z) ((a : ι) → M a)).flip
        (A, h).1) q =
      ((ContinuousMultilinearMap.apply ℝ M Z h).comp
          (ContinuousLinearMap.fst ℝ (ContinuousMultilinearMap ℝ M Z) (∀ a, M a)) +
        (A.linearDeriv h).comp
          (ContinuousLinearMap.snd ℝ (ContinuousMultilinearMap ℝ M Z) (∀ a, M a))) q := by
    rintro ⟨B, η⟩
    simp [ContinuousMultilinearMap.linearDeriv_apply]
  exact h1.congr_fderiv (ContinuousLinearMap.ext hL)

end Eval

/-! ### The derivative tower -/

variable {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0}

/-- **The derivative tower** of `f : U → F` up to order `k + 1`: `Ψ i m l x`, for `x ∈ U_{m+l}`, is
the `i`-th derivative of `f : U_{m+l} → F_m` at `x` (a continuous `i`-linear map on `E_{m+l}`),
defined for `i ≤ l + 1` and `i ≤ k + 1` — the text's hypothesis "`f : U_{m+l} → F_m` is `C^{l+1}`"
is exactly what makes these derivatives exist and be continuous.  The fields: `Φ 0 = f`; all
`Ψ i m l` are restrictions of the one base-level function `Φ i` (`toBase`: the compatibility of
`d^i f(x)` across levels, used tacitly in the text); `Ψ i m l` is continuous on `U_{m+l}`; and for
`i ≤ l`, `i ≤ k` it is differentiable with derivative `ξ ↦ Ψ (i+1) m l x (ξ, ·)`. -/
structure IsDerivTower (k : ℕ) (U : Set (E 0)) (f : E 0 → F 0)
    (Φ : ∀ i, E 0 → (Fin i → E 0) → F 0)
    (Ψ : ∀ i m l, E (m + l) → ContinuousMultilinearMap ℝ (fun _ : Fin i => E (m + l)) (F m)) :
    Prop where
  zero : ∀ x h, Φ 0 x h = f x
  toBase : ∀ i m l, i ≤ l + 1 → i ≤ k + 1 → ∀ x ∈ E.lvlSet U (m + l), ∀ h : Fin i → E (m + l),
    F.toBase m (Ψ i m l x h) = Φ i (E.toBase (m + l) x) fun a => E.toBase (m + l) (h a)
  continuousOn : ∀ i m l, i ≤ l + 1 → i ≤ k + 1 → ContinuousOn (Ψ i m l) (E.lvlSet U (m + l))
  hasFDerivWithinAt : ∀ i m l, i ≤ l → i ≤ k → ∀ x ∈ E.lvlSet U (m + l),
    HasFDerivWithinAt (Ψ i m l) (Ψ (i + 1) m l x).curryLeft (E.lvlSet U (m + l)) x

/-! ### The tower of a map satisfying the text's hypothesis -/

/-- The `i`-th derivative of `f : U_{m+l} → F_m` (Mathlib's `iteratedFDerivWithin`). -/
def levelDerivTower (U : Set (E 0)) (f : E 0 → F 0) (i m l : ℕ) (x : E (m + l)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin i => E (m + l)) (F m) :=
  iteratedFDerivWithin ℝ i (levelMap f m ∘ E.inclK m l) (E.lvlSet U (m + l)) x

/-- The `i`-th derivative of `f` on the base level: that of `f : U_{i-1} → F_0`, at the lifts of
the arguments to `E_{i-1}` (junk outside the image of `E_{i-1}`). -/
def baseDerivTower (U : Set (E 0)) (f : E 0 → F 0) (i : ℕ) (x : E 0) (h : Fin i → E 0) : F 0 :=
  levelDerivTower U f i 0 (i - 1) (invFun (E.toBase (0 + (i - 1))) x)
    fun a => invFun (E.toBase (0 + (i - 1))) (h a)

/-- The text's hypothesis of Proposition 1.2.4 (preprint 1.19) for all `l`, with the order `min l k + 1`: the
restriction of the `C^{k+1}` map `f : U_{m+k} → F_m` to `U_{m+l}`, `l > k`, is `C^{k+1}`. -/
theorem contDiffOn_levels_min {k : ℕ}
    (h : ∀ m l, l ≤ k → ContDiffOn ℝ (l + 1) (levelMap f m ∘ E.inclK m l) (E.lvlSet U (m + l)))
    (m l : ℕ) :
    ContDiffOn ℝ (min l k + 1) (levelMap f m ∘ E.inclK m l) (E.lvlSet U (m + l)) := by
  rcases le_or_gt l k with hl | hl
  · rw [min_eq_left hl]; exact h m l hl
  · rw [min_eq_right hl.le]
    have hle : m + k ≤ m + l := by omega
    have heq : levelMap f m ∘ E.inclK m l = (levelMap f m ∘ E.inclK m k) ∘ E.inclLE hle := by
      funext x
      simp only [Function.comp_apply]
      congr 1
      apply E.toBase_injective m
      rw [E.toBase_inclK, E.toBase_inclK, E.toBase_inclLE]
    rw [heq, ← E.preimage_inclLE_lvlSet U hle]
    exact (h m k le_rfl).comp (E.inclLE hle).contDiff.contDiffOn (mapsTo_preimage _ _)

/-- Compatibility of the iterated derivatives across levels: the `i`-th derivative of
`f : U_{m+l} → F_m`, mapped to `F_0`, is the `i`-th derivative of `f : U_{i-1} → F_0` at the
images of the arguments in `E_{i-1}` (`i ≤ l + 1`, `i ≤ k + 1`). -/
theorem levelDerivTower_toBase {k : ℕ} (hU : IsScDomain E U) (hf : IsSc0 E F U f)
    (h : ∀ m l, l ≤ k → ContDiffOn ℝ (l + 1) (levelMap f m ∘ E.inclK m l) (E.lvlSet U (m + l)))
    {i m l : ℕ} (hil : i ≤ l + 1) (hik : i ≤ k + 1) {x : E (m + l)} (hx : x ∈ E.lvlSet U (m + l))
    (hv : Fin i → E (m + l)) (hle : 0 + (i - 1) ≤ m + l) :
    F.toBase m (levelDerivTower U f i m l x hv) =
      levelDerivTower U f i 0 (i - 1) (E.inclLE hle x) fun a => E.inclLE hle (hv a) := by
  have hs : UniqueDiffOn ℝ (E.lvlSet U (m + l)) := hU.uniqueDiffWithinAt (m + l)
  have hs' : UniqueDiffOn ℝ (E.lvlSet U (0 + (i - 1))) := hU.uniqueDiffWithinAt _
  have hg := contDiffOn_levels_min h m l
  have hi : (i : WithTop ℕ∞) ≤ ((min l k + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (show i ≤ min l k + 1 by omega)
  have hg₀ := contDiffOn_levels_min h 0 (i - 1)
  have hi₀ : (i : WithTop ℕ∞) ≤ ((min (i - 1) k + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (show i ≤ min (i - 1) k + 1 by omega)
  -- step 1: the target inclusion commutes with the derivative
  have e1 : F.toBase m (levelDerivTower U f i m l x hv) =
      iteratedFDerivWithin ℝ i (F.toBase m ∘ (levelMap f m ∘ E.inclK m l)) (E.lvlSet U (m + l)) x
        hv := by
    rw [(F.toBase m).iteratedFDerivWithin_comp_left (hg x hx) hs hx hi,
      ContinuousLinearMap.compContinuousMultilinearMap_coe]
    rfl
  -- step 2: on `U_{m+l}` this is `f ∘ ι_{m+l} = (f : U_{i-1} → F_0) ∘ inclLE`
  have e2 : EqOn (F.toBase m ∘ (levelMap f m ∘ E.inclK m l))
      ((levelMap f 0 ∘ E.inclK 0 (i - 1)) ∘ E.inclLE hle) (E.lvlSet U (m + l)) := by
    intro y hy
    simp only [Function.comp_apply, levelMap_zero]
    rw [hf.toBase_levelMap (E.inclK_mem_lvlSet hy), E.toBase_inclK]
    congr 1
    exact ((E.toBase_inclK 0 (i - 1) (E.inclLE hle y)).trans (E.toBase_inclLE hle y)).symm
  -- step 3: the domain inclusion commutes with the derivative
  have e3 := (E.inclLE hle).iteratedFDerivWithin_comp_right (f := levelMap f 0 ∘ E.inclK 0 (i - 1))
    hg₀ hs' (by rw [E.preimage_inclLE_lvlSet]; exact hs) (E.inclLE_mem_lvlSet hle hx) hi₀
  rw [E.preimage_inclLE_lvlSet] at e3
  rw [e1, iteratedFDerivWithin_congr e2 hx, e3, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

/-- The base-level derivative at the images of level vectors is the level derivative. -/
theorem baseDerivTower_toBase {i m l : ℕ} (x : E (m + l)) (hv : Fin i → E (m + l))
    (hle : 0 + (i - 1) ≤ m + l) :
    baseDerivTower U f i (E.toBase (m + l) x) (fun a => E.toBase (m + l) (hv a)) =
      levelDerivTower U f i 0 (i - 1) (E.inclLE hle x) fun a => E.inclLE hle (hv a) := by
  have key : ∀ y : E (m + l),
      invFun (E.toBase (0 + (i - 1))) (E.toBase (m + l) y) = E.inclLE hle y := by
    intro y
    rw [← E.toBase_inclLE hle y]
    exact leftInverse_invFun (E.toBase_injective _) _
  simp only [baseDerivTower, key]

/-- **The derivative tower of a map satisfying the text's hypothesis of Proposition 1.2.4 (preprint 1.19)**: if
`f : U → F` is sc⁰ and `f : U_{m+l} → F_m` is `C^{l+1}` for all `m` and `l ≤ k`, then the iterated
derivatives of the level maps form a derivative tower up to order `k + 1`. -/
theorem isDerivTower_of_contDiffOn_levels {k : ℕ} (hU : IsScDomain E U) (hf : IsSc0 E F U f)
    (h : ∀ m l, l ≤ k → ContDiffOn ℝ (l + 1) (levelMap f m ∘ E.inclK m l) (E.lvlSet U (m + l))) :
    IsDerivTower k U f (baseDerivTower U f) (levelDerivTower U f) where
  zero x _ := by
    simp only [baseDerivTower, levelDerivTower, iteratedFDerivWithin_zero_apply,
      Function.comp_apply, levelMap_zero]
    congr 1
    exact (E.toBase_inclK 0 (0 - 1) _).trans
      (Function.invFun_eq ⟨E.castCLE (by omega) x, E.toBase_castCLE _ x⟩)
  toBase i m l hil hik x hx hv := by
    have hle : 0 + (i - 1) ≤ m + l := by omega
    rw [levelDerivTower_toBase hU hf h hil hik hx hv hle, baseDerivTower_toBase x hv hle]
  continuousOn i m l hil hik :=
    (contDiffOn_levels_min h m l).continuousOn_iteratedFDerivWithin
      (by exact_mod_cast (show i ≤ min l k + 1 by omega)) (hU.uniqueDiffWithinAt (m + l))
  hasFDerivWithinAt i m l hil hik x hx := by
    have hs : UniqueDiffOn ℝ (E.lvlSet U (m + l)) := hU.uniqueDiffWithinAt (m + l)
    have h1 : ContDiffWithinAt ℝ 1 (levelDerivTower U f i m l) (E.lvlSet U (m + l)) x :=
      (contDiffOn_levels_min h m l x hx).iteratedFDerivWithin_right hs
        (by exact_mod_cast (show 1 + i ≤ min l k + 1 by omega)) hx
    refine (h1.differentiableWithinAt one_ne_zero).hasFDerivWithinAt.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun ξ => ContinuousMultilinearMap.ext fun hv => ?_
    rw [ContinuousMultilinearMap.curryLeft_apply]
    simp only [levelDerivTower]
    rw [iteratedFDerivWithin_succ_apply_left, Fin.cons_zero, Fin.tail_cons]
    rfl

variable {Φ : ∀ i, E 0 → (Fin i → E 0) → F 0}
  {Ψ : ∀ i m l, E (m + l) → ContinuousMultilinearMap ℝ (fun _ : Fin i => E (m + l)) (F m)}

/-- Two values of the tower with the same base points agree (same target level `m`). -/
theorem IsDerivTower.eq_of_toBase {k : ℕ} (hT : IsDerivTower k U f Φ Ψ) {i m l l' : ℕ}
    (hil : i ≤ l + 1) (hil' : i ≤ l' + 1) (hik : i ≤ k + 1) {x : E (m + l)} {x' : E (m + l')}
    (hx : x ∈ E.lvlSet U (m + l)) (hx' : x' ∈ E.lvlSet U (m + l'))
    (hxx' : E.toBase (m + l) x = E.toBase (m + l') x') {h : Fin i → E (m + l)}
    {h' : Fin i → E (m + l')} (hhh' : ∀ a, E.toBase (m + l) (h a) = E.toBase (m + l') (h' a)) :
    Ψ i m l x h = Ψ i m l' x' h' := by
  apply F.toBase_injective m
  rw [hT.toBase i m l hil hik x hx h, hT.toBase i m l' hil' hik x' hx' h', hxx']
  congr 1
  funext a
  exact hhh' a

/-! ### Elementary maps -/

/-- **Elementary data** on an sc-Banach space `X` (the exposition's "type `(p, m; n₁, …, n_i)`"):
an sc-operator `π₀ : X → E^p` (the base-point slot), `i` slots `(n_a, π_a : X → E^{n_a})`, and the
target shift `m`.  The elementary map is `z ↦ d^i f(π₀ z)(π_1 z, …, π_i z) : X → F^m`. -/
structure ElemData (E X : ScBanach) (i : ℕ) where
  /-- The level of the base-point slot. -/
  p : ℕ
  /-- The base-point slot. -/
  π₀ : ScOperator X (E.shiftAdd p)
  /-- The vector slots, with their levels. -/
  sl : Fin i → Σ n : ℕ, ScOperator X (E.shiftAdd n)
  /-- The target shift. -/
  m : ℕ

namespace ElemData

variable {X : ScBanach} {i : ℕ} (d : ElemData E X i)

/-- The index conditions `m + i ≤ p`, `m + i ≤ n_a + 1` (the `j + l - 1 ≤ n_a` of `(S_k)`) and
`i ≤ k`. -/
structure Good (k : ℕ) : Prop where
  hp : d.m + i ≤ d.p
  hn : ∀ a, d.m + i ≤ (d.sl a).1 + 1
  hi : i ≤ k

/-- The domain `π₀⁻¹(U_p)`. -/
def dom (U : Set (E 0)) : Set (X 0) := d.π₀ 0 ⁻¹' E.lvlSet U d.p

/-- The elementary map `z ↦ Φ i (π₀ z) (π_1 z, …, π_i z)`, lifted to `F_m`. -/
def map (Φ : ∀ i, E 0 → (Fin i → E 0) → F 0) : X 0 → (F.shiftAdd d.m) 0 := fun z =>
  invFun (F.toBase d.m)
    (Φ i (E.toBase d.p (d.π₀ 0 z)) fun a => E.toBase (d.sl a).1 ((d.sl a).2 0 z))

lemma mem_lvlSet_dom {U : Set (E 0)} {l : ℕ} {z : X l} :
    z ∈ X.lvlSet (d.dom U) l ↔ d.π₀ l z ∈ E.lvlSet U (d.p + l) := by
  rw [ScBanach.mem_lvlSet, dom, mem_preimage, ScBanach.mem_lvlSet, ScBanach.mem_lvlSet,
    ← d.π₀.toBase_comm, ← E.shiftAdd_toBase]

/-- The base-point slot at level `l`, viewed in `E_q`. -/
def ρ₀ (l q : ℕ) (hq : q ≤ d.p + l) : X l →L[ℝ] E q := (E.inclLE hq).comp (d.π₀ l)

/-- The vector slot `a` at level `l`, viewed in `E_q`. -/
def ρ (l q : ℕ) (hq : ∀ a, q ≤ (d.sl a).1 + l) (a : Fin i) : X l →L[ℝ] E q :=
  (E.inclLE (hq a)).comp ((d.sl a).2 l)

lemma toBase_ρ₀ {l q : ℕ} (hq : q ≤ d.p + l) (z : X l) :
    E.toBase q (d.ρ₀ l q hq z) = E.toBase (d.p + l) (d.π₀ l z) := E.toBase_inclLE hq _

lemma toBase_ρ {l q : ℕ} (hq : ∀ a, q ≤ (d.sl a).1 + l) (a : Fin i) (z : X l) :
    E.toBase q (d.ρ l q hq a z) = E.toBase ((d.sl a).1 + l) ((d.sl a).2 l z) :=
  E.toBase_inclLE (hq a) _

lemma ρ₀_incl {l q : ℕ} (hq : q ≤ d.p + l) (hq' : q ≤ d.p + (l + 1)) (z : X (l + 1)) :
    d.ρ₀ l q hq (X.incl l z) = d.ρ₀ (l + 1) q hq' z := by
  apply E.toBase_injective q
  rw [toBase_ρ₀, toBase_ρ₀, ← d.π₀.incl_comm]
  exact (E.toBase_succ (d.p + l) _).symm

lemma ρ_incl {l q : ℕ} (hq : ∀ a, q ≤ (d.sl a).1 + l) (hq' : ∀ a, q ≤ (d.sl a).1 + (l + 1))
    (a : Fin i) (z : X (l + 1)) : d.ρ l q hq a (X.incl l z) = d.ρ (l + 1) q hq' a z := by
  apply E.toBase_injective q
  rw [toBase_ρ, toBase_ρ, ← (d.sl a).2.incl_comm]
  exact (E.toBase_succ ((d.sl a).1 + l) _).symm

lemma ρ₀_mem {U : Set (E 0)} {l q : ℕ} (hq : q ≤ d.p + l) {z : X l}
    (hz : z ∈ X.lvlSet (d.dom U) l) : d.ρ₀ l q hq z ∈ E.lvlSet U q :=
  E.inclLE_mem_lvlSet hq (d.mem_lvlSet_dom.1 hz)

/-- The elementary map on the base level, through `F.toBase`. -/
theorem map_toBase {k : ℕ} (hT : IsDerivTower k U f Φ Ψ) (hG : d.Good k) {l : ℕ} {z : X l}
    (hz : z ∈ X.lvlSet (d.dom U) l) :
    F.toBase d.m (d.map Φ (X.toBase l z)) =
      Φ i (E.toBase (d.p + l) (d.π₀ l z)) fun a => E.toBase ((d.sl a).1 + l) ((d.sl a).2 l z) := by
  have hp' : d.m + l + (i - 1) ≤ d.p + l := by have := hG.hp; omega
  have hn' : ∀ a, d.m + l + (i - 1) ≤ (d.sl a).1 + l := fun a => by
    have := hG.hn a; have := Fin.pos a; omega
  have key := hT.toBase i (d.m + l) (i - 1) (by omega) (by have := hG.hi; omega) (d.ρ₀ l _ hp' z)
    (d.ρ₀_mem hp' hz) fun a => d.ρ l _ hn' a z
  simp only [toBase_ρ₀, toBase_ρ] at key
  have hbase : E.toBase d.p (d.π₀ 0 (X.toBase l z)) = E.toBase (d.p + l) (d.π₀ l z) := by
    rw [← d.π₀.toBase_comm, ← E.shiftAdd_toBase]
  have hslot : ∀ a, E.toBase (d.sl a).1 ((d.sl a).2 0 (X.toBase l z)) =
      E.toBase ((d.sl a).1 + l) ((d.sl a).2 l z) := fun a => by
    rw [← (d.sl a).2.toBase_comm, ← E.shiftAdd_toBase]
  simp only [map, hbase, hslot]
  rw [← key, F.shiftAdd_toBase]
  exact Function.invFun_eq ⟨_, rfl⟩

/-- The level-`l` map of an elementary map: `d^i f` at level `(m + l, lv)` on the slots. -/
theorem levelMap_eq {k : ℕ} (hT : IsDerivTower k U f Φ Ψ) (hG : d.Good k) {l : ℕ} (lv : ℕ)
    (hlv : i ≤ lv + 1) (hp' : d.m + l + lv ≤ d.p + l) (hn' : ∀ a, d.m + l + lv ≤ (d.sl a).1 + l)
    {z : X l} (hz : z ∈ X.lvlSet (d.dom U) l) :
    levelMap (d.map Φ) l z = Ψ i (d.m + l) lv (d.ρ₀ l _ hp' z) fun a => d.ρ l _ hn' a z := by
  apply levelMap_eq_of_toBase_eq
  apply F.toBase_injective d.m
  rw [← F.shiftAdd_toBase,
    hT.toBase i (d.m + l) lv hlv (by have := hG.hi; omega) _ (d.ρ₀_mem hp' hz),
    d.map_toBase hT hG hz]
  simp only [toBase_ρ₀, toBase_ρ]

/-- The level-`l` map of an elementary map at a level-`(l+1)` point, with the slots taken at level
`l + 1`. -/
theorem levelMap_incl_eq {k : ℕ} (hT : IsDerivTower k U f Φ Ψ) (hG : d.Good k) {l : ℕ} (lv : ℕ)
    (hlv : i ≤ lv + 1) (hp' : d.m + l + lv ≤ d.p + (l + 1))
    (hn' : ∀ a, d.m + l + lv ≤ (d.sl a).1 + (l + 1)) {z : X (l + 1)}
    (hz : z ∈ X.lvlSet (d.dom U) (l + 1)) :
    levelMap (d.map Φ) l (X.incl l z) =
      Ψ i (d.m + l) lv (d.ρ₀ (l + 1) _ hp' z) fun a => d.ρ (l + 1) _ hn' a z := by
  have hz' : X.incl l z ∈ X.lvlSet (d.dom U) l := hz
  apply levelMap_eq_of_toBase_eq
  apply F.toBase_injective d.m
  rw [← F.shiftAdd_toBase,
    hT.toBase i (d.m + l) lv hlv (by have := hG.hi; omega) _ (d.ρ₀_mem hp' hz),
    d.map_toBase hT hG hz']
  simp only [toBase_ρ₀, toBase_ρ]
  congr 1
  · rw [← d.π₀.incl_comm]; exact E.toBase_succ _ _
  · funext a
    rw [← (d.sl a).2.incl_comm]; exact E.toBase_succ _ _

/-- An elementary map is sc⁰. -/
theorem isSc0 {k : ℕ} (hT : IsDerivTower k U f Φ Ψ) (hG : d.Good k) :
    IsSc0 X (F.shiftAdd d.m) (d.dom U) (d.map Φ) where
  mem_range l z hz := by
    have hp' : d.m + l + (i - 1) ≤ d.p + l := by have := hG.hp; omega
    have hn' : ∀ a, d.m + l + (i - 1) ≤ (d.sl a).1 + l := fun a => by
      have := hG.hn a; have := Fin.pos a; omega
    refine ⟨Ψ i (d.m + l) (i - 1) (d.ρ₀ l _ hp' z) fun a => d.ρ l _ hn' a z, ?_⟩
    apply F.toBase_injective d.m
    rw [← F.shiftAdd_toBase, hT.toBase i (d.m + l) (i - 1) (by omega) (by have := hG.hi; omega) _
      (d.ρ₀_mem hp' hz), d.map_toBase hT hG hz]
    simp only [toBase_ρ₀, toBase_ρ]
  continuousOn l := by
    have hp' : d.m + l + (i - 1) ≤ d.p + l := by have := hG.hp; omega
    have hn' : ∀ a, d.m + l + (i - 1) ≤ (d.sl a).1 + l := fun a => by
      have := hG.hn a; have := Fin.pos a; omega
    refine ContinuousOn.congr ?_ fun z hz => d.levelMap_eq hT hG (i - 1) (by omega) hp' hn' hz
    exact continuous_eval.comp_continuousOn
      (((hT.continuousOn i (d.m + l) (i - 1) (by omega) (by have := hG.hi; omega)).comp
        (d.ρ₀ l _ hp').continuous.continuousOn fun z hz => d.ρ₀_mem hp' hz).prodMk
          (ContinuousLinearMap.pi (d.ρ l _ hn')).continuous.continuousOn)

/-! #### The derivative of an elementary map -/

namespace Good

variable {k : ℕ} {d}

lemma hp₁ (hG : d.Good k) (l : ℕ) : d.m + l + i ≤ d.p + (l + 1) := by have := hG.hp; omega
lemma hp₂ (hG : d.Good k) (l : ℕ) : d.m + l + i ≤ d.p + l := by have := hG.hp; omega
lemma hp₃ (hG : d.Good k) (l : ℕ) : d.m + l + (i - 1) ≤ d.p + (l + 1) := by have := hG.hp; omega
lemma hn₁ (hG : d.Good k) (l : ℕ) : ∀ a, d.m + l + i ≤ (d.sl a).1 + (l + 1) := fun a => by
  have := hG.hn a; omega
lemma hn₃ (hG : d.Good k) (l : ℕ) : ∀ a, d.m + l + (i - 1) ≤ (d.sl a).1 + (l + 1) := fun a => by
  have := hG.hn a; omega
lemma hn₄ (hG : d.Good k) (l : ℕ) : ∀ a, d.m + l + (i - 1) ≤ (d.sl a).1 + l := fun a => by
  have := hG.hn a; have := Fin.pos a; omega
lemma hil (_hG : d.Good k) : i ≤ i - 1 + 1 := by omega
lemma hik (hG : d.Good k) : i ≤ k + 1 := by have := hG.hi; omega

end Good

/-- The derivative (3.5) of the exposition of the elementary map at level `l + 1 → l`, as an
operator on level `l`: `ζ ↦ d^{i+1}f(π₀ z)(π₀ ζ, π z) + Σ_a d^i f(π₀ z)(π z with slot a := π_a ζ)`;
the first term is `d^{i+1} f` at the uniform level `m + l + i`, the sum terms `d^i f` at
`m + l + i - 1`. -/
def deriv {k : ℕ} (hG : d.Good k)
    (Ψ : ∀ i m l, E (m + l) → ContinuousMultilinearMap ℝ (fun _ : Fin i => E (m + l)) (F m))
    (l : ℕ) (z : X (l + 1)) : X l →L[ℝ] F (d.m + l) :=
  ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => E (d.m + l + i)) (F (d.m + l))
      (fun a => d.ρ (l + 1) (d.m + l + i) (hG.hn₁ l) a z)).comp
    (Ψ (i + 1) (d.m + l) i (d.ρ₀ (l + 1) (d.m + l + i) (hG.hp₁ l) z)).curryLeft).comp
    (d.ρ₀ l (d.m + l + i) (hG.hp₂ l)) +
  ∑ a, ((Ψ i (d.m + l) (i - 1)
      (d.ρ₀ (l + 1) (d.m + l + (i - 1)) (hG.hp₃ l) z)).toContinuousLinearMap
      (fun b => d.ρ (l + 1) (d.m + l + (i - 1)) (hG.hn₃ l) b z) a).comp
    (d.ρ l (d.m + l + (i - 1)) (hG.hn₄ l) a)

lemma deriv_apply {k : ℕ} (hG : d.Good k) (l : ℕ) (z : X (l + 1)) (ζ : X l) :
    d.deriv hG Ψ l z ζ =
      Ψ (i + 1) (d.m + l) i (d.ρ₀ (l + 1) _ (hG.hp₁ l) z)
        (Fin.cons (d.ρ₀ l _ (hG.hp₂ l) ζ) fun a => d.ρ (l + 1) _ (hG.hn₁ l) a z) +
      ∑ a, Ψ i (d.m + l) (i - 1) (d.ρ₀ (l + 1) _ (hG.hp₃ l) z)
        (update (fun b => d.ρ (l + 1) _ (hG.hn₃ l) b z) a (d.ρ l _ (hG.hn₄ l) a ζ)) := by
  simp [deriv, ContinuousMultilinearMap.curryLeft_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply]

/-- The derivative on the base level. -/
theorem deriv_toBase {k : ℕ} (hT : IsDerivTower k U f Φ Ψ) (hG : d.Good k) {l : ℕ} {z : X (l + 1)}
    (hz : z ∈ X.lvlSet (d.dom U) (l + 1)) (ζ : X l) :
    F.toBase (d.m + l) (d.deriv hG Ψ l z ζ) =
      Φ (i + 1) (E.toBase (d.p + (l + 1)) (d.π₀ (l + 1) z))
        (Fin.cons (E.toBase (d.p + l) (d.π₀ l ζ))
          fun a => E.toBase ((d.sl a).1 + (l + 1)) ((d.sl a).2 (l + 1) z)) +
      ∑ a, Φ i (E.toBase (d.p + (l + 1)) (d.π₀ (l + 1) z))
        (update (fun b => E.toBase ((d.sl b).1 + (l + 1)) ((d.sl b).2 (l + 1) z)) a
          (E.toBase ((d.sl a).1 + l) ((d.sl a).2 l ζ))) := by
  rw [deriv_apply, map_add, map_sum,
    hT.toBase (i + 1) (d.m + l) i (by omega) (by have := hG.hi; omega) _ (d.ρ₀_mem _ hz)]
  congr 1
  · rw [toBase_ρ₀]
    congr 1
    funext b
    refine Fin.cases ?_ (fun a => ?_) b
    · simp only [Fin.cons_zero, toBase_ρ₀]
    · simp only [Fin.cons_succ, toBase_ρ]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [hT.toBase i (d.m + l) (i - 1) (hG.hil) hG.hik _ (d.ρ₀_mem _ hz), toBase_ρ₀]
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb; simp only [update_self, toBase_ρ]
    · simp only [update_of_ne hb, toBase_ρ]

/-- The level criterion (Proposition 1.2.1 (preprint 1.16)) for an elementary map: differentiability of
`f : U_{l+1} → F_l` with the derivative `deriv`. -/
theorem hasFDerivWithinAt_level {k : ℕ} (hT : IsDerivTower k U f Φ Ψ) (hG : d.Good k) {l : ℕ}
    {z : X (l + 1)} (hz : z ∈ X.lvlSet (d.dom U) (l + 1)) :
    HasFDerivWithinAt (levelMap (d.map Φ) l ∘ X.incl l) ((d.deriv hG Ψ l z).comp (X.incl l))
      (X.lvlSet (d.dom U) (l + 1)) z := by
  set s := X.lvlSet (d.dom U) (l + 1) with hs
  -- the function on `s`
  have hfun : EqOn (levelMap (d.map Φ) l ∘ X.incl l)
      (fun z' => Ψ i (d.m + l) i (d.ρ₀ (l + 1) _ (hG.hp₁ l) z')
        fun a => d.ρ (l + 1) _ (hG.hn₁ l) a z') s := by
    intro z' hz'
    exact d.levelMap_incl_eq hT hG i (Nat.le_succ i) (hG.hp₁ l) (hG.hn₁ l) hz'
  -- the derivative of `z' ↦ d^i f(ρ₀ z')(ρ z')`
  have hΨ : HasFDerivWithinAt (fun z' => Ψ i (d.m + l) i (d.ρ₀ (l + 1) _ (hG.hp₁ l) z'))
      ((Ψ (i + 1) (d.m + l) i (d.ρ₀ (l + 1) _ (hG.hp₁ l) z)).curryLeft.comp
        (d.ρ₀ (l + 1) _ (hG.hp₁ l))) s z :=
    (hT.hasFDerivWithinAt i (d.m + l) i le_rfl hG.hi _ (d.ρ₀_mem _ hz)).comp z
      (d.ρ₀ (l + 1) _ (hG.hp₁ l)).hasFDerivWithinAt fun z' hz' => d.ρ₀_mem _ hz'
  have hG' := (hasFDerivAt_cmm_eval (Ψ i (d.m + l) i (d.ρ₀ (l + 1) _ (hG.hp₁ l) z))
    fun a => d.ρ (l + 1) _ (hG.hn₁ l) a z).comp_hasFDerivWithinAt z
    (hΨ.prodMk (ContinuousLinearMap.pi (d.ρ (l + 1) _ (hG.hn₁ l))).hasFDerivWithinAt)
  refine (hG'.congr hfun (hfun hz)).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun ζ => ?_
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.curryLeft_apply,
    ContinuousMultilinearMap.linearDeriv_apply, ContinuousLinearMap.pi_apply, deriv_apply]
  congr 1
  · rw [d.ρ₀_incl _ (hG.hp₁ l)]
  · refine Finset.sum_congr rfl fun a _ => ?_
    refine hT.eq_of_toBase (by omega) hG.hil hG.hik (d.ρ₀_mem _ hz) (d.ρ₀_mem _ hz) ?_ fun b => ?_
    · rw [toBase_ρ₀, toBase_ρ₀]
    · by_cases hb : b = a
      · subst hb
        simp only [update_self, toBase_ρ]
        rw [← (d.sl b).2.incl_comm]
        exact E.toBase_succ ((d.sl b).1 + l) _
      · simp only [update_of_ne hb, toBase_ρ]

/-- The level criterion (Proposition 1.2.1 (preprint 1.16)) for an elementary map: continuity of `(z, ζ) ↦ Dg(z)ζ`
one level down. -/
theorem continuousOn_deriv {k : ℕ} (hT : IsDerivTower k U f Φ Ψ) (hG : d.Good k) (l : ℕ) :
    ContinuousOn (fun q : X (l + 1) × X l => d.deriv hG Ψ l q.1 q.2)
      (X.lvlSet (d.dom U) (l + 1) ×ˢ univ) := by
  simp only [deriv_apply]
  refine ContinuousOn.add ?_ (continuousOn_finsetSum _ fun a _ => ?_)
  · exact continuous_eval.comp_continuousOn
      (((hT.continuousOn (i + 1) (d.m + l) i (by omega) (by have := hG.hi; omega)).comp
        ((d.ρ₀ (l + 1) _ (hG.hp₁ l)).continuous.comp continuous_fst).continuousOn
          fun q hq => d.ρ₀_mem _ hq.1).prodMk
        (Continuous.finCons ((d.ρ₀ l _ (hG.hp₂ l)).continuous.comp continuous_snd)
          ((ContinuousLinearMap.pi (d.ρ (l + 1) _ (hG.hn₁ l))).continuous.comp
            continuous_fst)).continuousOn)
  · exact continuous_eval.comp_continuousOn
      (((hT.continuousOn i (d.m + l) (i - 1) hG.hil hG.hik).comp
        ((d.ρ₀ (l + 1) _ (hG.hp₃ l)).continuous.comp continuous_fst).continuousOn
          fun q hq => d.ρ₀_mem _ hq.1).prodMk
        (((ContinuousLinearMap.pi (d.ρ (l + 1) _ (hG.hn₃ l))).continuous.comp
          continuous_fst).update a
            ((d.ρ l _ (hG.hn₄ l) a).continuous.comp continuous_snd)).continuousOn)

/-- An elementary map satisfies the level conditions of Proposition 1.2.1 (preprint 1.16). -/
theorem isSc1Levels {k : ℕ} (hT : IsDerivTower k U f Φ Ψ) (hG : d.Good k) :
    IsSc1Levels (d.dom U) (d.map Φ) fun l z => d.deriv hG Ψ l z where
  hasFDerivWithinAt _ _ hz := d.hasFDerivWithinAt_level hT hG hz
  continuousOn l := d.continuousOn_deriv hT hG l

/-- **An elementary map is sc¹**, with derivative `deriv 0`. -/
theorem isSc1With {k : ℕ} (hT : IsDerivTower k U f Φ Ψ) (hG : d.Good k)
    (hW : IsScDomain X (d.dom U)) : IsSc1With (d.dom U) (d.map Φ) (d.deriv hG Ψ 0) :=
  (d.isSc1Levels hT hG).isSc1With hW (d.isSc0 hT hG)

end ElemData

/-- `IsScDomain` for an equal set. -/
theorem IsScDomain.of_eq {X : ScBanach} {W W' : Set (X 0)} (h : IsScDomain X W) (e : W = W') :
    IsScDomain X W' := e ▸ h

/-- Equal slots give equal slot values (through the base level). -/
theorem toBase_sigma_congr {Y : ScBanach} {σ σ' : Σ n : ℕ, ScOperator Y (E.shiftAdd n)}
    (h : σ = σ') (l : ℕ) (q : Y l) :
    E.toBase (σ.1 + l) (σ.2 l q) = E.toBase (σ'.1 + l) (σ'.2 l q) := by
  subst h; rfl

/-- `IsSck` for an equal domain. -/
theorem IsSck.of_eq_set {k : ℕ} {X G : ScBanach} {W W' : Set (X 0)} {g : X 0 → G 0}
    (h : IsSck k X G W g) (hWW' : W = W') : IsSck k X G W' g := hWW' ▸ h

/-! ### The tangent of an elementary map -/

namespace ScOperator

variable {X : ScBanach}

/-- The slot `T : X → E^n` on the base-point factor of `TX = X¹ ⊕ X`, as a slot
`TX → E^{n+1}`. -/
def tangentX {n : ℕ} (T : ScOperator X (E.shiftAdd n)) :
    ScOperator X.tangent (E.shiftAdd (n + 1)) :=
  (E.shiftAddShiftIso n).toScOperator.comp (T.shift.comp (ScBanach.prodFstOp X.shift X))

/-- The slot `T : X → E^n` on the vector factor of `TX = X¹ ⊕ X`, as a slot `TX → E^n`. -/
def tangentH {n : ℕ} (T : ScOperator X (E.shiftAdd n)) : ScOperator X.tangent (E.shiftAdd n) :=
  T.comp (ScBanach.prodSndOp X.shift X)

lemma toBase_tangentX {n : ℕ} (T : ScOperator X (E.shiftAdd n)) (l : ℕ) (q : X.tangent l) :
    E.toBase (n + 1 + l) (T.tangentX l q) = E.toBase (n + (l + 1)) (T (l + 1) q.1) :=
  E.toBase_shiftAddShiftIso n l _

lemma toBase_tangentX_zero {n : ℕ} (T : ScOperator X (E.shiftAdd n)) (q : X.tangent 0) :
    E.toBase (n + 1) (T.tangentX 0 q) = E.toBase (n + 1) (T 1 q.1) :=
  E.toBase_shiftAddShiftIso n 0 _

lemma tangentH_apply {n : ℕ} (T : ScOperator X (E.shiftAdd n)) (l : ℕ) (q : X.tangent l) :
    T.tangentH l q = T l q.2 := rfl

end ScOperator

namespace ElemData

variable {X : ScBanach} {i : ℕ} (d : ElemData E X i)

/-- The slot `a` of `d` on the base-point factor of `TX`, one level up. -/
abbrev slotX (a : Fin i) : Σ n : ℕ, ScOperator X.tangent (E.shiftAdd n) :=
  ⟨(d.sl a).1 + 1, (d.sl a).2.tangentX⟩

/-- The slot `a` of `d` on the vector factor of `TX`. -/
abbrev slotH (a : Fin i) : Σ n : ℕ, ScOperator X.tangent (E.shiftAdd n) :=
  ⟨(d.sl a).1, (d.sl a).2.tangentH⟩

/-- The first component of the tangent map: the elementary map on level `1`, as elementary data
of type `(p + 1, m + 1; n_a + 1)` on `TX`. -/
abbrev shiftData : ElemData E X.tangent i := ⟨d.p + 1, d.π₀.tangentX, d.slotX, d.m + 1⟩

/-- The term `d^{i+1}f(x)(δx, h)` of the derivative, as elementary data of type
`(p + 1, m; p, n_a + 1)` on `TX`. -/
abbrev derivData : ElemData E X.tangent (i + 1) :=
  ⟨d.p + 1, d.π₀.tangentX, Fin.cons ⟨d.p, d.π₀.tangentH⟩ d.slotX, d.m⟩

/-- The term `d^i f(x)(h with h_a := δh_a)` of the derivative, as elementary data of type
`(p + 1, m; n_b + 1 (b ≠ a), n_a)` on `TX`. -/
abbrev slotData (a : Fin i) : ElemData E X.tangent i :=
  ⟨d.p + 1, d.π₀.tangentX, update d.slotX a (d.slotH a), d.m⟩

variable {d}

theorem Good.shiftData {k : ℕ} (hG : d.Good k) : d.shiftData.Good k where
  hp := by show d.m + 1 + i ≤ d.p + 1; have := hG.hp; omega
  hn a := by show d.m + 1 + i ≤ (d.sl a).1 + 1 + 1; have := hG.hn a; omega
  hi := hG.hi

theorem Good.derivData {k : ℕ} (hG : d.Good k) (hik : i + 1 ≤ k) : d.derivData.Good k where
  hp := by show d.m + (i + 1) ≤ d.p + 1; have := hG.hp; omega
  hn a := by
    refine Fin.cases ?_ (fun b => ?_) a
    · show d.m + (i + 1) ≤ d.p + 1; have := hG.hp; omega
    · show d.m + (i + 1) ≤ (d.sl b).1 + 1 + 1; have := hG.hn b; omega
  hi := hik

theorem Good.slotData {k : ℕ} (hG : d.Good k) (a : Fin i) : (d.slotData a).Good k where
  hp := by show d.m + i ≤ d.p + 1; have := hG.hp; omega
  hn b := by
    by_cases hb : b = a
    · subst hb; simp only [update_self]; exact hG.hn b
    · simp only [update_of_ne hb]; have := hG.hn b; omega
  hi := hG.hi

/-- `T(dom) = dom` of the tangent data. -/
theorem tangentSet_dom (U : Set (E 0)) : X.tangentSet (d.dom U) = d.shiftData.dom U := by
  ext q
  rw [ScBanach.mem_tangentSet, d.mem_lvlSet_dom, dom, mem_preimage, ScBanach.mem_lvlSet,
    ScBanach.mem_lvlSet]
  exact Iff.of_eq (congrArg (· ∈ U) (ScOperator.toBase_tangentX_zero d.π₀ q).symm)

/-- **The tangent map of an elementary map** is the pairing of the shifted elementary map with
the sum of the `i + 1` elementary maps of the derivative (3.5) (the "form of `T^{k+2} f`" in the
exposition's proof of `(S_{k+1})`). -/
theorem tangentMap_eqOn {k : ℕ} (hT : IsDerivTower k U f Φ Ψ) (hG : d.Good k)
    (hW : IsScDomain X (d.dom U)) (hik : i + 1 ≤ k) :
    EqOn (tangentMap (d.dom U) (d.map Φ))
      (scPair (fun q => (F.shiftAddShiftIso d.m).symm 0 (d.shiftData.map Φ q))
        fun q => d.derivData.map Φ q + ∑ a, (d.slotData a).map Φ q) (X.tangentSet (d.dom U)) := by
  intro q hq
  have h1 := d.isSc1With hT hG hW
  rw [IsSc1.tangentMap_eqOn h1 (hW.uniqueDiffWithinAt 1) hq]
  have hq1 : q.1 ∈ X.lvlSet (d.dom U) 1 := hq
  have hq' : q ∈ X.tangent.lvlSet (d.shiftData.dom U) 0 := by
    rw [ScBanach.lvlSet_zero, ← d.tangentSet_dom]; exact hq
  refine Prod.ext ?_ ?_
  · change levelMap (d.map Φ) 1 q.1 = (F.shiftAddShiftIso d.m).symm 0 (d.shiftData.map Φ q)
    apply F.toBase_injective (d.m + 1)
    have e1 : F.toBase (d.m + 1) (levelMap (d.map Φ) 1 q.1) =
        F.toBase d.m (d.map Φ (X.toBase 1 q.1)) := by
      rw [F.shiftAdd_toBase, (d.isSc0 hT hG).toBase_levelMap hq1]
    rw [e1, d.map_toBase hT hG hq1]
    refine Eq.trans ?_ (F.toBase_shiftAddShiftIso_symm d.m 0 _).symm
    refine Eq.trans ?_ (d.shiftData.map_toBase hT hG.shiftData hq').symm
    exact congrArg₂ (Φ i) (ScOperator.toBase_tangentX_zero d.π₀ q).symm
      (funext fun a => (ScOperator.toBase_tangentX_zero (d.sl a).2 q).symm)
  · change d.deriv hG Ψ 0 q.1 q.2 = d.derivData.map Φ q + ∑ a, (d.slotData a).map Φ q
    apply F.toBase_injective d.m
    rw [map_add, map_sum]
    refine (d.deriv_toBase hT hG hq1 q.2).trans ?_
    congr 1
    · refine Eq.trans ?_ (d.derivData.map_toBase hT (hG.derivData hik) hq').symm
      refine congrArg₂ (Φ (i + 1)) (ScOperator.toBase_tangentX_zero d.π₀ q).symm (funext fun b => ?_)
      refine Fin.cases ?_ (fun a => ?_) b
      · simp only [ElemData.derivData, Fin.cons_zero]; rfl
      · simp only [ElemData.derivData, Fin.cons_succ]
        exact (ScOperator.toBase_tangentX_zero (d.sl a).2 q).symm
    · refine Finset.sum_congr rfl fun a _ => ?_
      refine Eq.trans ?_ ((d.slotData a).map_toBase hT (hG.slotData a) hq').symm
      refine congrArg₂ (Φ i) (ScOperator.toBase_tangentX_zero d.π₀ q).symm (funext fun b => ?_)
      by_cases hb : b = a
      · subst hb
        rw [Function.update_self]
        exact (toBase_sigma_congr (Function.update_self b (d.slotH b) d.slotX) 0 q).symm
      · rw [Function.update_of_ne hb]
        exact (ScOperator.toBase_tangentX_zero (d.sl b).2 q).symm.trans
          (toBase_sigma_congr (Function.update_of_ne hb (d.slotH a) d.slotX) 0 q).symm

/-- **Elementary maps are sc^s** for `i + s ≤ k + 1` (the inductive statement `(S_k)`): by
induction on `s`, using the sc¹ criterion and the form of the tangent map. -/
theorem isSck {k : ℕ} (hT : IsDerivTower k U f Φ Ψ) (s : ℕ) :
    ∀ {X : ScBanach} {i : ℕ} (d : ElemData E X i), d.Good k → IsScDomain X (d.dom U) →
      i + s ≤ k + 1 → IsSck s X (F.shiftAdd d.m) (d.dom U) (d.map Φ) := by
  induction s with
  | zero => exact fun d hG _ _ => d.isSc0 hT hG
  | succ s ih =>
    intro X i d hG hW hs
    have h1 := d.isSc1With hT hG hW
    refine ⟨h1.isSc1, ?_⟩
    cases s with
    | zero => exact h1.isSc1.tangentMap_isSc0
    | succ s =>
      have hik : i + 1 ≤ k := by clear ih h1 hW hG hT; omega
      have hs' : i + (s + 1) ≤ k + 1 := by clear ih h1 hW hG hT; omega
      have hs'' : i + 1 + (s + 1) ≤ k + 1 := by clear ih h1 hW hG hT; omega
      have hdom := d.tangentSet_dom U
      have hW' : IsScDomain X.tangent (X.tangentSet (d.dom U)) := hW.tangentSet
      have hW'' : IsScDomain X.tangent (d.shiftData.dom U) := hW'.of_eq hdom
      refine IsSck.congr hW' (d.tangentMap_eqOn hT hG hW hik).symm ?_
      refine IsSck.scPair hW' ?_ ?_
      · have h₀ := (ih d.shiftData hG.shiftData hW'' hs').of_eq_set hdom.symm
        exact IsSck.comp hW' (isScDomain_univ _)
          ((F.shiftAddShiftIso d.m).symm.toScOperator.isScSmooth (isScDomain_univ _) (s + 1)) h₀
          (mapsTo_univ _ _)
      · have h₁ := (ih d.derivData (hG.derivData hik) hW'' hs'').of_eq_set hdom.symm
        have h₂ : ∀ a, IsSck (s + 1) X.tangent (F.shiftAdd d.m) (X.tangentSet (d.dom U))
            ((d.slotData a).map Φ) := fun a =>
          (ih (d.slotData a) (hG.slotData a) hW'' hs').of_eq_set hdom.symm
        exact IsSck.add hW' h₁ (IsSck.sum hW' Finset.univ fun a _ => h₂ a)

end ElemData

/-! ### Proposition 1.2.4 (preprint 1.19) and Corollary 1.2.5 (preprint 1.20) under the text's hypothesis -/

/-- `f` itself as elementary data: `i = 0`, `p = m = 0`, with the base slot `E ≅ E^0`. -/
def ElemData.base (E : ScBanach) : ElemData E E 0 :=
  ⟨0, E.shiftAddZeroIso.toScOperator, Fin.elim0, 0⟩

lemma ElemData.base_dom (U : Set (E 0)) : (ElemData.base E).dom U = U := by
  ext z
  exact Iff.of_eq (congrArg (· ∈ U) (E.toBase_shiftAddZeroIso 0 z))

lemma ElemData.base_good (k : ℕ) : (ElemData.base E).Good k :=
  ⟨Nat.zero_le _, fun a => a.elim0, Nat.zero_le _⟩

/-- **Proposition 1.2.4 (preprint 1.19)** (as stated): let `U` be an sc-domain in `E` (e.g. a relatively open subset
of a partial quadrant) and `f : U → F` sc⁰.  If for every `m ≥ 0` and `0 ≤ l ≤ k` the induced map
`f : U_{m+l} → F_m` is of class `C^{l+1}`, then `f` is sc^{k+1}.  (`f` is the elementary map with
`i = 0` and `p = m = 0`; `ElemData.isSck` with `s = k + 1`.) -/
theorem proposition_1_2_4_text {k : ℕ} (hU : IsScDomain E U) (hf : IsSc0 E F U f)
    (h : ∀ m l, l ≤ k → ContDiffOn ℝ (l + 1) (levelMap f m ∘ E.inclK m l) (E.lvlSet U (m + l))) :
    IsSck (k + 1) E F U f := by
  have hT := isDerivTower_of_contDiffOn_levels hU hf h
  have hdom := ElemData.base_dom (E := E) U
  have hW : IsScDomain E ((ElemData.base E).dom U) := hU.of_eq hdom.symm
  have hs := (ElemData.isSck hT (k + 1) (ElemData.base E) (ElemData.base_good k) hW
    (Nat.zero_add (k + 1)).le).of_eq_set hdom
  have hcomp := IsSck.comp hU (isScDomain_univ _)
    (F.shiftAddZeroIso.symm.toScOperator.isScSmooth (isScDomain_univ _) (k + 1)) hs
    (mapsTo_univ _ _)
  refine IsSck.congr hU (fun z hz => ?_) hcomp
  have hz' : z ∈ E.lvlSet ((ElemData.base E).dom U) 0 := by
    rw [ScBanach.lvlSet_zero, hdom]; exact hz
  have e1 := (ElemData.base E).map_toBase hT (ElemData.base_good k) hz'
  have e2 := hT.zero (E.toBase (0 + 0) ((ElemData.base E).π₀ 0 z))
    fun a => E.toBase (((ElemData.base E).sl a).1 + 0) (((ElemData.base E).sl a).2 0 z)
  have e3 := E.toBase_shiftAddZeroIso 0 z
  have e4 := F.toBase_castCLE_symm (Nat.zero_add 0).symm
    ((ElemData.base E).map (baseDerivTower U f) z)
  exact e4.trans (e1.trans (e2.trans (congrArg f e3)))

/-- **Proposition 1.2.4 (preprint 1.19) for sc-smoothness**: if `f : U → F` is sc⁰ and `f : U_{m+l} → F_m` is
`C^{l+1}` for all `m, l ≥ 0`, then `f` is sc-smooth. -/
theorem IsScSmooth.of_contDiffOn_levels_text (hU : IsScDomain E U) (hf : IsSc0 E F U f)
    (h : ∀ m l : ℕ, ContDiffOn ℝ (l + 1) (levelMap f m ∘ E.inclK m l) (E.lvlSet U (m + l))) :
    IsScSmooth U f := by
  intro k
  cases k with
  | zero => exact hf
  | succ k => exact proposition_1_2_4_text hU hf fun m l _ => h m l

/-- **Corollary 1.2.5 (preprint 1.20)** (as stated): let `U` be an sc-domain and `f : U → V` a map into a
finite-dimensional space (constant sc-structure).  If for some `k` and all `0 ≤ l ≤ k` the map
`f : U_l → V` is of class `C^{l+1}`, then `f` is sc^{k+1}. -/
theorem corollary_1_2_5_text {k : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (hU : IsScDomain E U) {f : E 0 → (ScBanach.const V) 0}
    (h : ∀ l, l ≤ k → ContDiffOn ℝ (l + 1) (f ∘ E.toBase l) (E.lvlSet U l)) :
    IsSck (k + 1) E (ScBanach.const V) U f := by
  have hlvl : ∀ m, levelMap f m = f ∘ E.toBase m := fun m => funext fun x =>
    levelMap_eq_of_toBase_eq (ScBanach.const_toBase V m _)
  have hf : IsSc0 E (ScBanach.const V) U f :=
    ⟨fun m x _ => ⟨f (E.toBase m x), ScBanach.const_toBase V m _⟩, fun m => by
      rw [hlvl]
      exact (h 0 (Nat.zero_le k)).continuousOn.comp (E.toBase m).continuous.continuousOn
        (E.mapsTo_toBase_lvlSet U m)⟩
  refine proposition_1_2_4_text hU hf fun m l hl => ?_
  have hle : l ≤ m + l := Nat.le_add_left l m
  have heq : levelMap f m ∘ E.inclK m l = (f ∘ E.toBase l) ∘ E.inclLE hle := by
    funext x
    simp only [hlvl, Function.comp_apply, E.toBase_inclK, E.toBase_inclLE]
  rw [heq, ← E.preimage_inclLE_lvlSet U hle]
  exact (h l hl).comp (E.inclLE hle).contDiff.contDiffOn (mapsTo_preimage _ _)

/-- **Corollary 1.2.5 (preprint 1.20) for sc-smoothness**: if `f : U_l → V` is `C^{l+1}` for every `l ≥ 0`, then
`f : U → V` is sc-smooth (the exposition's "middle claim"). -/
theorem IsScSmooth.of_contDiffOn_levels_finiteDimensional_text {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (hU : IsScDomain E U)
    {f : E 0 → (ScBanach.const V) 0}
    (h : ∀ l : ℕ, ContDiffOn ℝ (l + 1) (f ∘ E.toBase l) (E.lvlSet U l)) : IsScSmooth U f := by
  intro k
  cases k with
  | zero => exact (corollary_1_2_5_text (k := 0) hU fun l _ => h l).isSc0
  | succ k => exact corollary_1_2_5_text hU fun l _ => h l

end Polyfold
