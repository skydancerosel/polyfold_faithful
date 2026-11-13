import Polyfold.Chapter4.GapP3_K4_BoundaryWedge

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4, p. 199
(2017 p. 150; preprint p. 168): "We define the differential algebra `Ω*_∞(X, ∂X)` by
`Ω*_∞(X, ∂X) := Ω*_∞(X) ⊕ Ω*⁻¹_∞(∂X)` with differential `d(ω, τ) = (dω, j^*ω − dτ)`".

# The product on the relative complex `Ω*_∞(X, ∂X)`

## The reading

The text calls `Ω*_∞(X, ∂X)` a differential algebra but gives no product.  We take the product of
the mapping cone of the morphism `j^* : Ω*_∞(X) → Ω*_∞(∂X)` of graded differential algebras:
for `(ω, τ)` of degree `k` (so `ω ∈ Ωᵏ_∞(X)`, `τ ∈ Ωᵏ⁻¹_∞(∂X)`) and `(ω', τ')` of degree `l`,
`(ω, τ) · (ω', τ') = (ω ∧ ω', (−1)ᵏ j^*ω ∧ τ')`.
With it `d` is a derivation of degree `+1`, `d(x y) = (dx) y + (−1)ᵏ x (dy)`, the product is
associative, and `(1, 0)` is a unit on the left; there is no unit on the right
(`(ω, τ) · (1, 0) = (ω, 0)`), as there is none in relative cohomology `H*(X, ∂X)` in general.
The product is not graded commutative on forms (it is on cohomology).  The projection
`(ω, τ) ↦ ω` is multiplicative.

## What is proved

* `relWedge hP k l : RelForms k × RelForms l → RelForms (k + l)`, bilinear, with its components
  `relFst_relWedge` (`ω ∧ ω'`), `relSnd_relWedge_succ` (`(−1)ᵏ j^*ω ∧ τ'`), `relSnd_relWedge_zero`.
* **`relD_relWedge`**: the Leibniz rule `d(x y) = (dx) y + (−1)ᵏ x (dy)` (degree `(k + 1) + l`
  read as `(k + l) + 1` by `relCast`).
* **`relWedge_assoc`**: `(x y) z = x (y z)` (degree `k + (l + m)` read as `(k + l) + m`).
* `relCast_relWedge_relOne`: `(1, 0) x = x` (degree `0 + l` read as `l`).
* `relGraded hP = ⊕ₖ Ωᵏ_∞(X, ∂X)`: `relGNonUnitalNonAssocSemiring` (Mathlib's graded
  `GNonUnitalNonAssocSemiring`, so `⊕ₖ Ωᵏ_∞(X, ∂X)` is a non-unital non-associative ring),
  `relGraded_mul_assoc` (it is associative: `relGradedNonUnitalRing`), `relGradedD` (`d` of
  degree `+1`) with `relGradedD_comp_self` (`d² = 0`) and **`relGradedD_of_mul_of`** (`d` is a
  graded derivation): the differential algebra of p. 199.
-/

open Set Function

noncomputable section

namespace Polyfold

namespace MPolyfold

open BundledMPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  (hP : P.IsTame)

/-! ### Components and casts -/

/-- The `Ω*_∞(X)` component `ω` of a relative form `(ω, τ)`. -/
def relFst : ∀ k, RelForms hP k →ₗ[ℝ] (BundledMPolyfold.of P).formsInfty k
  | 0 => LinearMap.id
  | k + 1 => LinearMap.fst ℝ ((BundledMPolyfold.of P).formsInfty (k + 1)) (bFormsInfty hP k)

/-- The `Ω*_∞(∂X)` component `τ` of a relative form `(ω, τ)` of degree `k + 1`. -/
def relSnd (k : ℕ) : RelForms hP (k + 1) →ₗ[ℝ] bFormsInfty hP k :=
  LinearMap.snd ℝ ((BundledMPolyfold.of P).formsInfty (k + 1)) (bFormsInfty hP k)

variable {hP} in
theorem relForms_ext_zero {x y : RelForms hP 0} (h : relFst hP 0 x = relFst hP 0 y) : x = y := h

variable {hP} in
theorem relForms_ext_succ {k : ℕ} {x y : RelForms hP (k + 1)}
    (h₁ : relFst hP (k + 1) x = relFst hP (k + 1) y) (h₂ : relSnd hP k x = relSnd hP k y) :
    x = y :=
  Prod.ext h₁ h₂

/-- Reading the degree `n` of `Ωⁿ_∞(X, ∂X)` as `n' = n`. -/
def relCast {n n' : ℕ} (h : n = n') : RelForms hP n →ₗ[ℝ] RelForms hP n' :=
  h ▸ LinearMap.id

theorem relCast_rfl {n : ℕ} (x : RelForms hP n) : relCast hP (n := n) rfl x = x := rfl

theorem relFst_relCast {n n' : ℕ} (h : n = n') (x : RelForms hP n) :
    relFst hP n' (relCast hP h x) = (BundledMPolyfold.of P).formsInftyCast h (relFst hP n x) := by
  subst h; rfl

theorem relSnd_relCast {n n' : ℕ} (h : n + 1 = n' + 1) (x : RelForms hP (n + 1)) :
    relSnd hP n' (relCast hP h x) =
      agreeDFormsInftyCast (bdryMap hP) (Nat.succ_injective h) (relSnd hP n x) := by
  obtain rfl : n = n' := Nat.succ_injective h
  rfl

theorem gradedMonoid_mk_relCast {i j : ℕ} (h : i = j) (x : RelForms hP i) :
    (GradedMonoid.mk j (relCast hP h x) : GradedMonoid fun k => RelForms hP k) =
      GradedMonoid.mk i x := by
  subst h; rfl

/-! ### The differential, componentwise -/

theorem relFst_relD (n : ℕ) (x : RelForms hP n) :
    relFst hP (n + 1) (relD hP n x) = (BundledMPolyfold.of P).formsInftyD n (relFst hP n x) := by
  cases n <;> rfl

theorem relSnd_relD_zero (x : RelForms hP 0) : relSnd hP 0 (relD hP 0 x) = jStar hP 0 x := rfl

theorem relSnd_relD_succ (n : ℕ) (x : RelForms hP (n + 1)) :
    relSnd hP (n + 1) (relD hP (n + 1) x) =
      jStar hP (n + 1) (relFst hP (n + 1) x) - bFormsInftyD hP n (relSnd hP n x) := rfl

/-! ### The product -/

/-- The product in degrees `(0, l + 1)`: `(a, (ω', τ')) ↦ (a ∧ ω', j^*a ∧ τ')`. -/
def relWedgeZS (l : ℕ) : (BundledMPolyfold.of P).formsInfty 0 →ₗ[ℝ]
    ((BundledMPolyfold.of P).formsInfty (l + 1) × bFormsInfty hP l) →ₗ[ℝ]
      ((BundledMPolyfold.of P).formsInfty (0 + (l + 1)) × bFormsInfty hP (0 + l)) :=
  LinearMap.mk₂ ℝ (fun a y => ((BundledMPolyfold.of P).formsInftyWedge 0 (l + 1) a y.1,
      bFormsInftyWedge hP 0 l (jStar hP 0 a) y.2))
    (fun a₁ a₂ y => Prod.ext (LinearMap.map_add₂ _ _ _ _)
      (show bFormsInftyWedge hP 0 l (jStar hP 0 (a₁ + a₂)) y.2 =
        bFormsInftyWedge hP 0 l (jStar hP 0 a₁) y.2 + bFormsInftyWedge hP 0 l (jStar hP 0 a₂) y.2
        by rw [map_add, LinearMap.map_add₂]))
    (fun c a y => Prod.ext (LinearMap.map_smul₂ _ _ _ _)
      (show bFormsInftyWedge hP 0 l (jStar hP 0 (c • a)) y.2 =
        c • bFormsInftyWedge hP 0 l (jStar hP 0 a) y.2
        by rw [LinearMap.map_smul, LinearMap.map_smul₂]))
    (fun a y₁ y₂ => Prod.ext (map_add _ _ _) (map_add _ _ _))
    (fun c a y => Prod.ext (map_smul _ _ _) (map_smul _ _ _))

set_option synthInstance.maxHeartbeats 200000 in
-- The `MulAction` instance on the product type is slow to synthesise at the default limit.
/-- The product in degrees `(k + 1, 0)`: `((ω, τ), a) ↦ (ω ∧ a, 0)`. -/
def relWedgeSZ (k : ℕ) :
    ((BundledMPolyfold.of P).formsInfty (k + 1) × bFormsInfty hP k) →ₗ[ℝ]
      (BundledMPolyfold.of P).formsInfty 0 →ₗ[ℝ]
      ((BundledMPolyfold.of P).formsInfty (k + 1) × bFormsInfty hP k) :=
  LinearMap.mk₂ ℝ (fun x a => ((BundledMPolyfold.of P).formsInftyWedge (k + 1) 0 x.1 a,
      (0 : bFormsInfty hP k)))
    (fun _ _ _ => Prod.ext (LinearMap.map_add₂ _ _ _ _) (add_zero 0).symm)
    (fun c _ _ => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (smul_zero c).symm)
    (fun _ _ _ => Prod.ext (map_add _ _ _) (add_zero 0).symm)
    (fun c _ _ => Prod.ext (map_smul _ _ _) (smul_zero c).symm)

/-- The product in degrees `(k + 1, l + 1)`:
`((ω, τ), (ω', τ')) ↦ (ω ∧ ω', (−1)ᵏ⁺¹ j^*ω ∧ τ')`. -/
def relWedgeSS (k l : ℕ) :
    ((BundledMPolyfold.of P).formsInfty (k + 1) × bFormsInfty hP k) →ₗ[ℝ]
      ((BundledMPolyfold.of P).formsInfty (l + 1) × bFormsInfty hP l) →ₗ[ℝ]
      ((BundledMPolyfold.of P).formsInfty (k + 1 + (l + 1)) × bFormsInfty hP (k + 1 + l)) :=
  LinearMap.mk₂ ℝ (fun x y => ((BundledMPolyfold.of P).formsInftyWedge (k + 1) (l + 1) x.1 y.1,
      (-1 : ℝ) ^ (k + 1) • bFormsInftyWedge hP (k + 1) l (jStar hP (k + 1) x.1) y.2))
    (fun x₁ x₂ y => Prod.ext (LinearMap.map_add₂ _ _ _ _)
      (show (-1 : ℝ) ^ (k + 1) •
          bFormsInftyWedge hP (k + 1) l (jStar hP (k + 1) (x₁.1 + x₂.1)) y.2 =
        (-1 : ℝ) ^ (k + 1) • bFormsInftyWedge hP (k + 1) l (jStar hP (k + 1) x₁.1) y.2 +
        (-1 : ℝ) ^ (k + 1) • bFormsInftyWedge hP (k + 1) l (jStar hP (k + 1) x₂.1) y.2
        by rw [← smul_add, ← LinearMap.map_add₂, ← map_add]))
    (fun c x y => Prod.ext (LinearMap.map_smul₂ _ _ _ _)
      (show (-1 : ℝ) ^ (k + 1) • bFormsInftyWedge hP (k + 1) l (jStar hP (k + 1) (c • x.1)) y.2 =
        c • (-1 : ℝ) ^ (k + 1) • bFormsInftyWedge hP (k + 1) l (jStar hP (k + 1) x.1) y.2
        by rw [LinearMap.map_smul, LinearMap.map_smul₂, smul_comm]))
    (fun x y₁ y₂ => Prod.ext (map_add _ _ _)
      (show (-1 : ℝ) ^ (k + 1) •
          bFormsInftyWedge hP (k + 1) l (jStar hP (k + 1) x.1) (y₁.2 + y₂.2) =
        (-1 : ℝ) ^ (k + 1) • bFormsInftyWedge hP (k + 1) l (jStar hP (k + 1) x.1) y₁.2 +
        (-1 : ℝ) ^ (k + 1) • bFormsInftyWedge hP (k + 1) l (jStar hP (k + 1) x.1) y₂.2
        by rw [← smul_add, ← map_add]))
    (fun c x y => Prod.ext (map_smul _ _ _)
      (show (-1 : ℝ) ^ (k + 1) • bFormsInftyWedge hP (k + 1) l (jStar hP (k + 1) x.1) (c • y.2) =
        c • (-1 : ℝ) ^ (k + 1) • bFormsInftyWedge hP (k + 1) l (jStar hP (k + 1) x.1) y.2
        by rw [map_smul, smul_comm]))

/-- **2021 p. 199: the product of the differential algebra `Ω*_∞(X, ∂X)`** (the text gives none;
see the module docstring): `(ω, τ) (ω', τ') = (ω ∧ ω', (−1)ᵏ j^*ω ∧ τ')` for `(ω, τ)` of
degree `k`, bilinear, `Ωᵏ_∞(X, ∂X) × Ωˡ_∞(X, ∂X) → Ωᵏ⁺ˡ_∞(X, ∂X)`. -/
def relWedge : ∀ k l, RelForms hP k →ₗ[ℝ] RelForms hP l →ₗ[ℝ] RelForms hP (k + l)
  | 0, 0 => (BundledMPolyfold.of P).formsInftyWedge 0 0
  | 0, l + 1 => relWedgeZS hP l
  | k + 1, 0 => relWedgeSZ hP k
  | k + 1, l + 1 => relWedgeSS hP k l

/-- The `Ω*_∞(X)` component of a product is `ω ∧ ω'`. -/
theorem relFst_relWedge (k l : ℕ) (x : RelForms hP k) (y : RelForms hP l) :
    relFst hP (k + l) (relWedge hP k l x y) =
      (BundledMPolyfold.of P).formsInftyWedge k l (relFst hP k x) (relFst hP l y) := by
  cases k <;> cases l <;> rfl

/-- The `Ω*_∞(∂X)` component of a product of degree `k + (l + 1)` is `(−1)ᵏ j^*ω ∧ τ'`. -/
theorem relSnd_relWedge_succ (k l : ℕ) (x : RelForms hP k) (y : RelForms hP (l + 1)) :
    relSnd hP (k + l) (relWedge hP k (l + 1) x y) =
      (-1 : ℝ) ^ k • bFormsInftyWedge hP k l (jStar hP k (relFst hP k x)) (relSnd hP l y) := by
  cases k with
  | zero => exact (one_smul ℝ _).symm
  | succ k => rfl

/-- The `Ω*_∞(∂X)` component of a product of degree `(k + 1) + 0` is `0`. -/
theorem relSnd_relWedge_zero (k : ℕ) (x : RelForms hP (k + 1)) (y : RelForms hP 0) :
    relSnd hP k (relWedge hP (k + 1) 0 x y) = 0 := rfl

/-! ### The Leibniz rule -/

theorem relSnd_relD_relWedge_zero (k : ℕ) (x : RelForms hP k) (y : RelForms hP 0) :
    relSnd hP k (relD hP k (relWedge hP k 0 x y)) =
      jStar hP k ((BundledMPolyfold.of P).formsInftyWedge k 0 (relFst hP k x) (relFst hP 0 y)) := by
  cases k with
  | zero => rfl
  | succ k =>
    refine (relSnd_relD_succ hP k _).trans ?_
    rw [relSnd_relWedge_zero, map_zero, sub_zero]
    rfl

theorem relFst_relD_relWedge (k l : ℕ) (h : k + 1 + l = k + l + 1) (x : RelForms hP k)
    (y : RelForms hP l) :
    relFst hP (k + l + 1) (relD hP (k + l) (relWedge hP k l x y)) =
      relFst hP (k + l + 1) (relCast hP h (relWedge hP (k + 1) l (relD hP k x) y)) +
        (-1 : ℝ) ^ k • relFst hP (k + l + 1) (relWedge hP k (l + 1) x (relD hP l y)) := by
  have h1 : relFst hP (k + l + 1) (relCast hP h (relWedge hP (k + 1) l (relD hP k x) y)) =
      (BundledMPolyfold.of P).formsInftyCast h ((BundledMPolyfold.of P).formsInftyWedge (k + 1) l
        ((BundledMPolyfold.of P).formsInftyD k (relFst hP k x)) (relFst hP l y)) :=
    (relFst_relCast hP h _).trans (congrArg _ ((relFst_relWedge hP (k + 1) l _ y).trans
      (congrArg (fun z => (BundledMPolyfold.of P).formsInftyWedge (k + 1) l z (relFst hP l y))
        (relFst_relD hP k x))))
  have h2 : relFst hP (k + l + 1) (relWedge hP k (l + 1) x (relD hP l y)) =
      (BundledMPolyfold.of P).formsInftyWedge k (l + 1) (relFst hP k x)
        ((BundledMPolyfold.of P).formsInftyD l (relFst hP l y)) :=
    (relFst_relWedge hP k (l + 1) x _).trans (congrArg _ (relFst_relD hP l y))
  rw [h1, h2]
  exact (relFst_relD hP (k + l) _).trans ((congrArg _ (relFst_relWedge hP k l x y)).trans
    ((BundledMPolyfold.of P).formsInftyD_formsInftyWedge h _ _))

theorem relSnd_relD_relWedge (k l : ℕ) (h : k + 1 + l = k + l + 1) (x : RelForms hP k)
    (y : RelForms hP l) :
    relSnd hP (k + l) (relD hP (k + l) (relWedge hP k l x y)) =
      relSnd hP (k + l) (relCast hP h (relWedge hP (k + 1) l (relD hP k x) y)) +
        (-1 : ℝ) ^ k • relSnd hP (k + l) (relWedge hP k (l + 1) x (relD hP l y)) := by
  cases l with
  | zero =>
    have e1 : relSnd hP k (relCast hP h (relWedge hP (k + 1) 0 (relD hP k x) y)) = 0 :=
      (relSnd_relCast hP (n := k) (n' := k) h _).trans (by rw [relSnd_relWedge_zero, map_zero])
    have e2 : relSnd hP k (relWedge hP k (0 + 1) x (relD hP 0 y)) =
        (-1 : ℝ) ^ k • bFormsInftyWedge hP k 0 (jStar hP k (relFst hP k x)) (jStar hP 0 y) :=
      relSnd_relWedge_succ hP k 0 x _
    refine (relSnd_relD_relWedge_zero hP k x y).trans ?_
    change _ = relSnd hP k (relCast hP h (relWedge hP (k + 1) 0 (relD hP k x) y)) +
        (-1 : ℝ) ^ k • relSnd hP k (relWedge hP k (0 + 1) x (relD hP 0 y))
    rw [e1, e2, zero_add, smul_smul, wedge_neg_one_pow_mul_self, one_smul]
    exact jStar_formsInftyWedge hP _ _
  | succ l =>
    have e0 : relSnd hP (k + l + 1) (relD hP (k + l + 1) (relWedge hP k (l + 1) x y)) =
        jStar hP (k + l + 1) ((BundledMPolyfold.of P).formsInftyWedge k (l + 1) (relFst hP k x)
          (relFst hP (l + 1) y)) -
        bFormsInftyD hP (k + l) ((-1 : ℝ) ^ k • bFormsInftyWedge hP k l
          (jStar hP k (relFst hP k x)) (relSnd hP l y)) :=
      (relSnd_relD_succ hP (k + l) _).trans (congrArg₂ (· - ·)
        (congrArg _ (relFst_relWedge hP k (l + 1) x y))
        (congrArg _ (relSnd_relWedge_succ hP k l x y)))
    have e1 : relSnd hP (k + l + 1) (relCast hP h (relWedge hP (k + 1) (l + 1) (relD hP k x) y)) =
        agreeDFormsInftyCast (bdryMap hP) (Nat.add_right_comm k 1 l)
          ((-1 : ℝ) ^ (k + 1) • bFormsInftyWedge hP (k + 1) l
            (bFormsInftyD hP k (jStar hP k (relFst hP k x))) (relSnd hP l y)) := by
      refine (relSnd_relCast hP (n := k + 1 + l) (n' := k + l + 1) h _).trans ?_
      refine congrArg _ ((relSnd_relWedge_succ hP (k + 1) l _ y).trans ?_)
      rw [relFst_relD]
      exact congrArg (fun z => (-1 : ℝ) ^ (k + 1) • bFormsInftyWedge hP (k + 1) l z (relSnd hP l y))
        (LinearMap.congr_fun (jStar_comp_D hP k) (relFst hP k x)).symm
    have e2 : relSnd hP (k + l + 1) (relWedge hP k (l + 1 + 1) x (relD hP (l + 1) y)) =
        (-1 : ℝ) ^ k • bFormsInftyWedge hP k (l + 1) (jStar hP k (relFst hP k x))
          (jStar hP (l + 1) (relFst hP (l + 1) y) - bFormsInftyD hP l (relSnd hP l y)) :=
      relSnd_relWedge_succ hP k (l + 1) x _
    change relSnd hP (k + l + 1) (relD hP (k + l + 1) (relWedge hP k (l + 1) x y)) =
      relSnd hP (k + l + 1) (relCast hP h (relWedge hP (k + 1) (l + 1) (relD hP k x) y)) +
        (-1 : ℝ) ^ k • relSnd hP (k + l + 1) (relWedge hP k (l + 1 + 1) x (relD hP (l + 1) y))
    have e3 : jStar hP (k + l + 1) ((BundledMPolyfold.of P).formsInftyWedge k (l + 1)
        (relFst hP k x) (relFst hP (l + 1) y)) = bFormsInftyWedge hP k (l + 1)
          (jStar hP k (relFst hP k x)) (jStar hP (l + 1) (relFst hP (l + 1) y)) :=
      jStar_formsInftyWedge hP _ _
    have e4 : bFormsInftyD hP (k + l) ((-1 : ℝ) ^ k • bFormsInftyWedge hP k l
        (jStar hP k (relFst hP k x)) (relSnd hP l y)) = (-1 : ℝ) ^ k •
          (agreeDFormsInftyCast (bdryMap hP) (Nat.add_right_comm k 1 l)
            (bFormsInftyWedge hP (k + 1) l (bFormsInftyD hP k (jStar hP k (relFst hP k x)))
              (relSnd hP l y)) + (-1 : ℝ) ^ k • bFormsInftyWedge hP k (l + 1)
                (jStar hP k (relFst hP k x)) (bFormsInftyD hP l (relSnd hP l y))) := by
      rw [map_smul]
      exact congrArg _ (agreeDFormsInftyD_agreeDFormsInftyWedge _ _ _ _)
    rw [e0, e1, e2, e3, e4, map_smul, LinearMap.map_sub]
    simp only [smul_add, smul_sub, smul_smul, wedge_neg_one_pow_mul_self, one_smul, pow_succ,
      mul_neg_one, neg_smul]
    abel

/-- **2021 p. 199: `d` is a derivation of `Ω*_∞(X, ∂X)`**: `d(x y) = (dx) y + (−1)ᵏ x (dy)` for
`x` of degree `k`, the degree `(k + 1) + l` of `(dx) y` read as `(k + l) + 1`. -/
theorem relD_relWedge (k l : ℕ) (h : k + 1 + l = k + l + 1) (x : RelForms hP k)
    (y : RelForms hP l) :
    relD hP (k + l) (relWedge hP k l x y) =
      relCast hP h (relWedge hP (k + 1) l (relD hP k x) y) +
        (-1 : ℝ) ^ k • (show RelForms hP (k + l + 1) from relWedge hP k (l + 1) x (relD hP l y)) :=
  relForms_ext_succ
    ((relFst_relD_relWedge hP k l h x y).trans (by rw [map_add, map_smul]))
    ((relSnd_relD_relWedge hP k l h x y).trans (by rw [map_add, map_smul]))

/-! ### Associativity -/

theorem relFst_relWedge_assoc (k l m : ℕ) (x : RelForms hP k) (y : RelForms hP l)
    (z : RelForms hP m) :
    relFst hP (k + l + m) (relWedge hP (k + l) m (relWedge hP k l x y) z) =
      relFst hP (k + l + m) (relCast hP (Nat.add_assoc k l m).symm
        (relWedge hP k (l + m) x (relWedge hP l m y z))) := by
  rw [relFst_relCast, relFst_relWedge, relFst_relWedge, relFst_relWedge, relFst_relWedge]
  exact (BundledMPolyfold.of P).formsInftyWedge_assoc _ _ _

theorem relSnd_relWedge_assoc_succ (k l m : ℕ) (x : RelForms hP k) (y : RelForms hP l)
    (z : RelForms hP (m + 1)) :
    relSnd hP (k + l + m) (relWedge hP (k + l) (m + 1) (relWedge hP k l x y) z) =
      relSnd hP (k + l + m) (relCast hP (Nat.add_assoc k l (m + 1)).symm
        (relWedge hP k (l + (m + 1)) x (relWedge hP l (m + 1) y z))) := by
  have e1 : relSnd hP (k + l + m) (relWedge hP (k + l) (m + 1) (relWedge hP k l x y) z) =
      (-1 : ℝ) ^ (k + l) • agreeDFormsInftyCast (bdryMap hP) (Nat.add_assoc k l m).symm
        (bFormsInftyWedge hP k (l + m) (jStar hP k (relFst hP k x))
          (bFormsInftyWedge hP l m (jStar hP l (relFst hP l y)) (relSnd hP m z))) := by
    refine (relSnd_relWedge_succ hP (k + l) m _ z).trans ?_
    rw [relFst_relWedge, jStar_formsInftyWedge]
    exact congrArg _ (agreeDFormsInftyWedge_assoc _ _ _ _)
  have e2 : relSnd hP (k + l + m) (relCast hP (Nat.add_assoc k l (m + 1)).symm
        (relWedge hP k (l + (m + 1)) x (relWedge hP l (m + 1) y z))) =
      agreeDFormsInftyCast (bdryMap hP) (Nat.add_assoc k l m).symm
        ((-1 : ℝ) ^ k • bFormsInftyWedge hP k (l + m) (jStar hP k (relFst hP k x))
          ((-1 : ℝ) ^ l • bFormsInftyWedge hP l m (jStar hP l (relFst hP l y))
            (relSnd hP m z))) :=
    (relSnd_relCast hP (n := k + (l + m)) (n' := k + l + m) _ _).trans
      (congrArg _ ((relSnd_relWedge_succ hP k (l + m) x _).trans
        (congrArg (fun w => (-1 : ℝ) ^ k • bFormsInftyWedge hP k (l + m)
          (jStar hP k (relFst hP k x)) w) (relSnd_relWedge_succ hP l m y z))))
  rw [e1, e2, LinearMap.map_smul, map_smul, map_smul, smul_smul, pow_add]

theorem relSnd_relWedge_assoc_zero (k l : ℕ) (x : RelForms hP k) (y : RelForms hP (l + 1))
    (z : RelForms hP 0) :
    relSnd hP (k + l) (relWedge hP (k + (l + 1)) 0 (relWedge hP k (l + 1) x y) z) =
      relSnd hP (k + l) (relCast hP (Nat.add_assoc k (l + 1) 0).symm
        (relWedge hP k (l + 1 + 0) x (relWedge hP (l + 1) 0 y z))) := by
  refine (relSnd_relWedge_zero hP (k + l) _ z).trans ?_
  refine (((relSnd_relCast hP (n := k + l) (n' := k + l) _ _).trans
    (congrArg _ ((relSnd_relWedge_succ hP k l x _).trans ?_))).trans (map_zero _)).symm
  rw [relSnd_relWedge_zero, map_zero, smul_zero]

/-- **The product of `Ω*_∞(X, ∂X)` is associative**: `(x y) z = x (y z)`, the degree
`k + (l + m)` of `x (y z)` read as `(k + l) + m`. -/
theorem relWedge_assoc (k l m : ℕ) (x : RelForms hP k) (y : RelForms hP l)
    (z : RelForms hP m) :
    relWedge hP (k + l) m (relWedge hP k l x y) z =
      relCast hP (Nat.add_assoc k l m).symm
        (relWedge hP k (l + m) x (relWedge hP l m y z)) := by
  cases m with
  | succ m =>
    exact relForms_ext_succ (relFst_relWedge_assoc hP k l (m + 1) x y z)
      (relSnd_relWedge_assoc_succ hP k l m x y z)
  | zero =>
    cases l with
    | succ l =>
      exact relForms_ext_succ (relFst_relWedge_assoc hP k (l + 1) 0 x y z)
        (relSnd_relWedge_assoc_zero hP k l x y z)
    | zero =>
      cases k with
      | succ k =>
        refine relForms_ext_succ (relFst_relWedge_assoc hP (k + 1) 0 0 x y z) ?_
        exact (relSnd_relWedge_zero hP k _ z).trans
          (((relSnd_relCast hP (n := k) (n' := k) _ _).trans
            (congrArg _ (relSnd_relWedge_zero hP k x _))).trans (map_zero _)).symm
      | zero => exact relForms_ext_zero (relFst_relWedge_assoc hP 0 0 0 x y z)

/-! ### The unit on the left -/

/-- The relative form `(1, 0)` of degree `0`: the function `1` on `X`. -/
def relOne : RelForms hP 0 := (BundledMPolyfold.of P).formsInftyOne

/-- **`(1, 0)` is a unit on the left**: `(1, 0) x = x`, the degree `0 + l` read as `l`. -/
theorem relCast_relWedge_relOne (l : ℕ) (x : RelForms hP l) :
    relCast hP (Nat.zero_add l) (relWedge hP 0 l (relOne hP) x) = x := by
  cases l with
  | zero =>
    exact relForms_ext_zero ((relFst_relCast hP _ _).trans
      (((BundledMPolyfold.of P).formsInftyCast_formsInftyOne_wedge _)))
  | succ l =>
    refine relForms_ext_succ ((relFst_relCast hP _ _).trans ?_) ?_
    · rw [relFst_relWedge]
      exact (BundledMPolyfold.of P).formsInftyCast_formsInftyOne_wedge _
    · refine (relSnd_relCast hP (n := 0 + l) (n' := l) _ _).trans ?_
      rw [relSnd_relWedge_succ, pow_zero, one_smul]
      exact agreeDFormsInftyCast_agreeDFormsInftyOne_wedge _ _

/-- There is no unit on the right: `x (1, 0) = (ω, 0)` for `x = (ω, τ)` of degree `k + 1`. -/
theorem relWedge_relOne (k : ℕ) (x : RelForms hP (k + 1)) :
    relWedge hP (k + 1) 0 x (relOne hP) = (relFst hP (k + 1) x, 0) :=
  relForms_ext_succ ((relFst_relWedge hP (k + 1) 0 x _).trans
    ((BundledMPolyfold.of P).formsInftyWedge_formsInftyOne _)) rfl

/-! ### The graded differential algebra `⊕ₖ Ωᵏ_∞(X, ∂X)` -/

/-- The graded multiplication of `Ω*_∞(X, ∂X)`: `relWedge`. -/
instance relGMul : GradedMonoid.GMul fun k => RelForms hP k :=
  ⟨fun {i j} a b => relWedge hP i j a b⟩

/-- `Ω*_∞(X, ∂X)` is a graded non-unital non-associative semiring under `relWedge` (associativity
on the direct sum: `relGraded_mul_assoc`). -/
instance relGNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring fun k => RelForms hP k where
  mul_zero {i j} a := LinearMap.map_zero (relWedge hP i j a)
  zero_mul {i j} b := LinearMap.map_zero₂ (relWedge hP i j) b
  mul_add {i j} a b c := LinearMap.map_add (relWedge hP i j a) b c
  add_mul {i j} a b c := LinearMap.map_add₂ (relWedge hP i j) a b c

/-- `Ω*_∞(X, ∂X) = ⊕ₖ Ωᵏ_∞(X, ∂X)`. -/
abbrev relGraded := DirectSum ℕ fun k => RelForms hP k

theorem relGraded_of_mul_of {k l : ℕ} (a : RelForms hP k) (b : RelForms hP l) :
    (DirectSum.of (fun k => RelForms hP k) k a * DirectSum.of _ l b : relGraded hP) =
      DirectSum.of _ (k + l) (relWedge hP k l a b) :=
  DirectSum.of_mul_of a b

/-- **The product of `⊕ₖ Ωᵏ_∞(X, ∂X)` is associative** (from `relWedge_assoc`; Mathlib's
`DirectSum.mul_assoc` argument without the unit). -/
theorem relGraded_mul_assoc (a b c : relGraded hP) : a * b * c = a * (b * c) := by
  suffices AddMonoidHom.mulLeft₃ (R := relGraded hP) = AddMonoidHom.mulRight₃ by
    simpa only [AddMonoidHom.mulLeft₃_apply, AddMonoidHom.mulRight₃_apply] using
      DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this a) b) c
  ext ai ax bi bx ci cx : 6
  dsimp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.mulLeft₃_apply,
    AddMonoidHom.mulRight₃_apply]
  rw [relGraded_of_mul_of, relGraded_of_mul_of, relGraded_of_mul_of, relGraded_of_mul_of,
    relWedge_assoc]
  exact DirectSum.of_eq_of_gradedMonoid_eq (gradedMonoid_mk_relCast hP _ _)

/-- **`⊕ₖ Ωᵏ_∞(X, ∂X)` is an associative (non-unital) ring.** -/
instance relGradedNonUnitalRing : NonUnitalRing (relGraded hP) :=
  { (inferInstance : NonUnitalNonAssocRing (relGraded hP)) with
    mul_assoc := relGraded_mul_assoc hP }

/-- The differential `d` of `⊕ₖ Ωᵏ_∞(X, ∂X)`, of degree `+1`. -/
def relGradedD : relGraded hP →ₗ[ℝ] relGraded hP :=
  DirectSum.toModule ℝ ℕ _ fun j =>
    (DirectSum.lof ℝ ℕ (fun j => RelForms hP j) (j + 1)).comp (relD hP j)

theorem relGradedD_lof (j : ℕ) (x : RelForms hP j) :
    relGradedD hP (DirectSum.lof ℝ ℕ (fun j => RelForms hP j) j x) =
      DirectSum.lof ℝ ℕ (fun j => RelForms hP j) (j + 1) (relD hP j x) :=
  DirectSum.toModule_lof ℝ _ _

theorem relGradedD_of (j : ℕ) (x : RelForms hP j) :
    relGradedD hP (DirectSum.of (fun j => RelForms hP j) j x) =
      DirectSum.of (fun j => RelForms hP j) (j + 1) (relD hP j x) :=
  (congrArg (relGradedD hP) (DirectSum.lof_eq_of ℝ ℕ _ j x).symm).trans
    ((relGradedD_lof hP j x).trans (DirectSum.lof_eq_of ℝ ℕ _ _ _))

/-- `d² = 0` on `⊕ₖ Ωᵏ_∞(X, ∂X)`. -/
theorem relGradedD_comp_self : (relGradedD hP).comp (relGradedD hP) = 0 := by
  refine DirectSum.linearMap_ext ℝ fun j => LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  have h : relD hP (j + 1) (relD hP j x) = 0 := LinearMap.congr_fun (relD_comp_relD hP j) x
  rw [relGradedD_lof, relGradedD_lof, h]
  exact LinearMap.map_zero _

/-- **2021 p. 199: `Ω*_∞(X, ∂X)` is a differential algebra**: `d` is a graded derivation,
`d(a b) = (da) b + (−1)ᵏ a (db)` for `a` homogeneous of degree `k`. -/
theorem relGradedD_of_mul_of {k l : ℕ} (a : RelForms hP k) (b : RelForms hP l) :
    relGradedD hP (DirectSum.of (fun k => RelForms hP k) k a * DirectSum.of _ l b) =
      relGradedD hP (DirectSum.of _ k a) * DirectSum.of _ l b +
        ((-1 : ℝ) ^ k) • (DirectSum.of _ k a * relGradedD hP (DirectSum.of _ l b)) := by
  have hof : ∀ (j : ℕ) (c : ℝ) (x : RelForms hP j),
      DirectSum.of (fun k => RelForms hP k) j (c • x) = c • DirectSum.of _ j x := fun j c x =>
    (DirectSum.lof_eq_of ℝ ℕ _ j _).symm.trans
      ((LinearMap.map_smul _ c x).trans (congrArg _ (DirectSum.lof_eq_of ℝ ℕ _ j x)))
  calc _ = relGradedD hP (DirectSum.of _ (k + l) (relWedge hP k l a b)) :=
        congrArg _ (relGraded_of_mul_of hP a b)
    _ = DirectSum.of _ (k + l + 1) (relD hP (k + l) (relWedge hP k l a b)) := relGradedD_of hP _ _
    _ = DirectSum.of _ (k + l + 1)
          (relCast hP (Nat.add_right_comm k 1 l) (relWedge hP (k + 1) l (relD hP k a) b) +
            (-1 : ℝ) ^ k • (show RelForms hP (k + l + 1) from
              relWedge hP k (l + 1) a (relD hP l b))) :=
        congrArg _ (relD_relWedge hP k l (Nat.add_right_comm k 1 l) a b)
    _ = DirectSum.of _ (k + l + 1)
          (relCast hP (Nat.add_right_comm k 1 l) (relWedge hP (k + 1) l (relD hP k a) b)) +
          ((-1 : ℝ) ^ k) • DirectSum.of _ (k + (l + 1))
            (relWedge hP k (l + 1) a (relD hP l b)) :=
        (map_add _ _ _).trans (congrArg _ (hof _ _ _))
    _ = DirectSum.of _ (k + 1 + l) (relWedge hP (k + 1) l (relD hP k a) b) +
          ((-1 : ℝ) ^ k) • DirectSum.of _ (k + (l + 1))
            (relWedge hP k (l + 1) a (relD hP l b)) :=
        congrArg (· + _) (DirectSum.of_eq_of_gradedMonoid_eq (gradedMonoid_mk_relCast hP _ _))
    _ = _ := (congrArg₂ (fun x y => x + ((-1 : ℝ) ^ k) • y)
        ((congrArg (· * DirectSum.of _ l b) (relGradedD_of hP k a)).trans
          (relGraded_of_mul_of hP _ b)).symm
        ((congrArg (DirectSum.of _ k a * ·) (relGradedD_of hP l b)).trans
          (relGraded_of_mul_of hP a _)).symm)

end MPolyfold

end Polyfold
