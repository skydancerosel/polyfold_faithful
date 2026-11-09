import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Data.Real.Basic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.2,
pp. 203–205: the lines `λ(E) = Λ^max E`, `λ*(E) = (λ(E))*`, the induced maps `λ(Φ)`, `λ*(Φ)`,
**Definition 6.3.1 (preprint 6.3)** (the isomorphism `ι : λ(E*) → λ*(E)`) and **Proposition 6.3.2 (preprint 6.4)** *(book 2017:
Definition 6.2, Proposition 6.2; see `BookConcordance.md`)*.

# Determinant lines of finite-dimensional spaces

## The text, paraphrased

Following Zinger, `λ(E) := Λ^max E` and `λ*(E) := (λ(E))*`.  A linear map `Φ : E → F` between
spaces of the same dimension induces `λ(Φ)(a₁ ∧ … ∧ aₙ) = Φ(a₁) ∧ … ∧ Φ(aₙ)`, nonzero exactly when
`Φ` is an isomorphism, with `λ(Ψ ∘ Φ) = λ(Ψ) ∘ λ(Φ)`; `λ*(Φ) : λ*(F) → λ*(E)` is its dual.
(Definition 6.3.1 (preprint 6.3)) `ι : λ(E*) → λ*(E)` is `ι(e₁* ∧ … ∧ eₙ*)(a₁ ∧ … ∧ aₙ) = det(eᵢ*(aⱼ))`, with
`λ({0}*) = ℝ` for `n = 0`; for a basis and its dual basis `ι(e₁* ∧ … ∧ eₙ*) = (e₁ ∧ … ∧ eₙ)*`,
where `v*` is the vector of the dual line with `v*(v) = 1`.  (Proposition 6.3.2 (preprint 6.4)) For an isomorphism
`Φ : E → F`, `λ*(Φ) ∘ ι = ι ∘ λ(Φ*)`.

## What is formalized

* `Polyfold.maxPow E` (`λ(E)`): the exterior power `⋀[ℝ]^(finrank ℝ E) E` of Mathlib, a submodule
  of the exterior algebra; `Polyfold.maxPowDual E` (`λ*(E)`): its dual.  `finrank_maxPow`,
  `finrank_maxPowDual`: for finite-dimensional `E` both are lines.
* `Polyfold.wedge v h` (`v₁ ∧ … ∧ vₖ` for `k = dim E`): the product in the exterior algebra,
  as an element of `λ(E)`.  `wedge_basis_ne_zero`, `wedge_eq_zero_of_not_linearIndependent`,
  `wedge_ne_zero_iff`, and `wedge_eq_det_smul`: `w₁ ∧ … ∧ wₙ = det_b(w) · b₁ ∧ … ∧ bₙ` for a basis
  `b` (the change of basis multiplies the wedge by the determinant).
* Wedges of two blocks `u ∧ w` (`Fin.append u w`): `wedge_append_basis_left`,
  `wedge_append_basis_right` (a change of basis in one block multiplies by its determinant),
  `wedge_append_add_left`, `wedge_append_add_right` (adding to one block vectors of the span of
  the other does not change the wedge), `wedge_comp_basis`, `wedge_eq_det_smul'`,
  `wedge_ne_zero_of_span_eq_top`; behind them `alternatingMap_eq_det_smul` and
  `alternatingMap_eq_of_sub_mem_span` for any alternating map.
* `Polyfold.dualVec v` (`v*`): `v*(v) = 1` for `v ≠ 0` in a line (`dualVec_self`); every
  functional with `φ(v) = 1` is `v*` (`eq_dualVec_of_apply_eq_one`); `dualVec_smul`
  (`(c v)* = c⁻¹ v*`).
* `Polyfold.maxPowMap Φ h` (`λ(Φ)`) for `dim E = dim F`: `maxPowMap_wedge` (the defining formula),
  `maxPowMap_comp` (`λ(Ψ ∘ Φ) = λ(Ψ) ∘ λ(Φ)`), `maxPowMap_ne_zero_iff` (nonzero iff `Φ` is
  bijective); `Polyfold.maxPowDualMap Φ h` (`λ*(Φ)`, the dual map).
* **Definition 6.3.1 (preprint 6.3)**: `Polyfold.iotaDual E` (`ι`), Mathlib's `exteriorPower.pairingDual` read on
  `λ(E*)`; `iotaDual_wedge_wedge` (the defining formula), `iotaDual_wedge_dualBasis`
  (`ι(e₁* ∧ … ∧ eₙ*) = (e₁ ∧ … ∧ eₙ)*`), `iotaDual_ne_zero`.
* **Proposition 6.3.2 (preprint 6.4)**: `proposition_6_3_2`.

## Reading

`λ({0}*) = ℝ` (the text's convention for `n = 0`) holds as `⋀⁰ = ℝ` (`exteriorPower.zeroEquiv`):
the wedge of the empty family is `1`.  The text's matrix `(eᵢ*(aⱼ))` is the transpose of the one
in `exteriorPower.pairingDual_ιMulti_ιMulti`; the determinants agree.
-/

open Module

noncomputable section

namespace Polyfold

variable {E F G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G]

variable (E) in
/-- `λ(E) = Λ^max E`: the top exterior power `⋀ⁿ E`, `n = dim E`, as a submodule of the exterior
algebra of `E`. -/
abbrev maxPow : Submodule ℝ (ExteriorAlgebra ℝ E) := ⋀[ℝ]^(finrank ℝ E) E

variable (E) in
/-- `λ*(E) = (λ(E))*`, the dual of the line `λ(E)`. -/
abbrev maxPowDual : Type _ := Module.Dual ℝ (maxPow E)

/-- **`λ(E)` is a line** for finite-dimensional `E` (`n choose n = 1`). -/
theorem finrank_maxPow [FiniteDimensional ℝ E] : finrank ℝ (maxPow E) = 1 := by
  rw [exteriorPower.finrank_eq, Nat.choose_self]

instance [FiniteDimensional ℝ E] : FiniteDimensional ℝ (maxPow E) :=
  Module.finite_of_finrank_eq_succ finrank_maxPow

/-- `λ*(E)` is a line. -/
theorem finrank_maxPowDual [FiniteDimensional ℝ E] : finrank ℝ (maxPowDual E) = 1 := by
  rw [Subspace.dual_finrank_eq, finrank_maxPow]

/-! ### Lines -/

section Line

variable {L : Type*} [AddCommGroup L] [Module ℝ L]

/-- In a line, every vector is a multiple of a nonzero one. -/
theorem exists_smul_eq_of_finrank_eq_one (h1 : finrank ℝ L = 1) {v : L} (hv : v ≠ 0) (w : L) :
    ∃ c : ℝ, c • v = w :=
  (finrank_eq_one_iff_of_nonzero' v hv).1 h1 w

/-- The dual vector `v*` of a vector `v` of a line: the functional with `v*(v) = 1` (`0` if `v = 0`
or the space is not a line). -/
def dualVec (v : L) : Module.Dual ℝ L :=
  haveI := Classical.dec (v ≠ 0 ∧ finrank ℝ L = 1)
  if h : v ≠ 0 ∧ finrank ℝ L = 1 then
    (basisOfLinearIndependentOfCardEqFinrank (K := ℝ) (ι := Fin 1) (b := fun _ => v)
      (linearIndependent_unique_iff.2 h.1) (by simp [h.2])).coord 0
  else 0

/-- `v*(v) = 1` for `v ≠ 0` in a line. -/
@[simp] theorem dualVec_self (h1 : finrank ℝ L = 1) {v : L} (hv : v ≠ 0) : dualVec v v = 1 := by
  rw [dualVec, dif_pos ⟨hv, h1⟩]
  set bb := basisOfLinearIndependentOfCardEqFinrank (K := ℝ) (ι := Fin 1) (b := fun _ => v)
      (linearIndependent_unique_iff.2 hv) (by simp [h1])
  have hb : bb 0 = v := by simp [bb]
  have key : bb.coord 0 (bb 0) = 1 := by simp
  rwa [hb] at key

/-- In a line, `w = v*(w) v` for `v ≠ 0`. -/
theorem dualVec_apply_smul (h1 : finrank ℝ L = 1) {v : L} (hv : v ≠ 0) (w : L) :
    dualVec v w • v = w := by
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one h1 hv w
  simp [hv, h1]

/-- A functional on a line is determined by its value at one nonzero vector. -/
theorem dual_ext_of_ne_zero (h1 : finrank ℝ L = 1) {v : L} (hv : v ≠ 0)
    {φ ψ : Module.Dual ℝ L} (h : φ v = ψ v) : φ = ψ := by
  ext w
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one h1 hv w
  simp [h]

/-- A linear map out of a line is determined by its value at one nonzero vector. -/
theorem linearMap_ext_of_ne_zero {M : Type*} [AddCommGroup M] [Module ℝ M]
    (h1 : finrank ℝ L = 1) {v : L} (hv : v ≠ 0)
    {φ ψ : L →ₗ[ℝ] M} (h : φ v = ψ v) : φ = ψ := by
  ext w
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one h1 hv w
  simp [h]

/-- **`v*` is characterized by `v*(v) = 1`.** -/
theorem eq_dualVec_of_apply_eq_one (h1 : finrank ℝ L = 1) {v : L} (hv : v ≠ 0)
    {φ : Module.Dual ℝ L} (h : φ v = 1) : φ = dualVec v :=
  dual_ext_of_ne_zero h1 hv (by rw [h, dualVec_self h1 hv])

/-- `(c v)* = c⁻¹ v*`. -/
theorem dualVec_smul (h1 : finrank ℝ L = 1) {v : L} (hv : v ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    dualVec (c • v) = c⁻¹ • dualVec v :=
  (eq_dualVec_of_apply_eq_one h1 (smul_ne_zero hc hv) (by
    simp [dualVec_self h1 hv, hc])).symm

theorem dualVec_ne_zero (h1 : finrank ℝ L = 1) {v : L} (hv : v ≠ 0) : dualVec v ≠ 0 := by
  intro h
  have := dualVec_self h1 hv
  rw [h] at this
  simp at this

end Line

/-! ### The wedge of `dim E` vectors -/

/-- `v₁ ∧ … ∧ vₖ ∈ λ(E)` for a family of `k = dim E` vectors: the product `ι(v₁) ⋯ ι(vₖ)` in the
exterior algebra. -/
def wedge {k : ℕ} (v : Fin k → E) (hk : k = finrank ℝ E) : maxPow E :=
  ⟨ExteriorAlgebra.ιMulti ℝ k v, hk ▸ ExteriorAlgebra.ιMulti_range ℝ k (Set.mem_range_self v)⟩

@[simp] lemma coe_wedge {k : ℕ} (v : Fin k → E) (hk : k = finrank ℝ E) :
    (wedge v hk : ExteriorAlgebra ℝ E) = ExteriorAlgebra.ιMulti ℝ k v := rfl

lemma wedge_eq_ιMulti (v : Fin (finrank ℝ E) → E) :
    wedge v rfl = exteriorPower.ιMulti ℝ (finrank ℝ E) v := rfl

/-- The wedge does not depend on how the equality `k = dim E` is proved, nor on the indexing up to
`Fin.cast`. -/
lemma wedge_cast {k k' : ℕ} (v : Fin k → E) (hk : k = finrank ℝ E) (hkk : k' = k) :
    wedge (v ∘ Fin.cast hkk) (hkk.trans hk) = wedge v hk := by
  subst hkk
  rfl

/-- The wedge of a linearly dependent family vanishes. -/
theorem wedge_eq_zero_of_not_linearIndependent {k : ℕ} {v : Fin k → E} (hk : k = finrank ℝ E)
    (hv : ¬ LinearIndependent ℝ v) : wedge v hk = 0 := by
  subst hk
  rw [wedge_eq_ιMulti]
  exact (exteriorPower.ιMulti ℝ (finrank ℝ E)).map_linearDependent v hv

/-- The functional `x ↦ ι(b₁* ∧ … ∧ bₙ*)(x)` on `⋀ⁿ E` evaluates the wedge of `w` to `det_b(w)`. -/
theorem pairingDual_dualBasis_wedge [FiniteDimensional ℝ E] (b : Basis (Fin (finrank ℝ E)) ℝ E)
    (w : Fin (finrank ℝ E) → E) :
    exteriorPower.pairingDual ℝ E (finrank ℝ E)
      (exteriorPower.ιMulti ℝ (finrank ℝ E) (fun i => b.dualBasis i)) (wedge w rfl) = b.det w := by
  rw [wedge_eq_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti, Basis.det_apply,
    ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply]

/-- The wedge of a basis is not zero. -/
theorem wedge_basis_ne_zero [FiniteDimensional ℝ E] (b : Basis (Fin (finrank ℝ E)) ℝ E) :
    wedge b rfl ≠ 0 := by
  intro h
  have := pairingDual_dualBasis_wedge b b
  rw [h, map_zero, Basis.det_self] at this
  exact zero_ne_one this

/-- **Change of basis**: `w₁ ∧ … ∧ wₙ = det_b(w) · b₁ ∧ … ∧ bₙ`. -/
theorem wedge_eq_det_smul [FiniteDimensional ℝ E] (b : Basis (Fin (finrank ℝ E)) ℝ E)
    (w : Fin (finrank ℝ E) → E) : wedge w rfl = b.det w • wedge b rfl := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one finrank_maxPow (wedge_basis_ne_zero b)
    (wedge w rfl)
  rw [← hc]
  congr 1
  have := pairingDual_dualBasis_wedge b w
  rw [← hc, map_smul, pairingDual_dualBasis_wedge b b, Basis.det_self, smul_eq_mul,
    mul_one] at this
  exact this

/-- The wedge of `dim E` vectors is nonzero exactly when they are linearly independent. -/
theorem wedge_ne_zero_iff [FiniteDimensional ℝ E] {k : ℕ} {v : Fin k → E}
    (hk : k = finrank ℝ E) : wedge v hk ≠ 0 ↔ LinearIndependent ℝ v := by
  refine ⟨fun h => by_contra fun hv => h (wedge_eq_zero_of_not_linearIndependent hk hv),
    fun hv => ?_⟩
  subst hk
  have := wedge_basis_ne_zero (basisOfLinearIndependentOfCardEqFinrank' v hv (by simp))
  rwa [coe_basisOfLinearIndependentOfCardEqFinrank'] at this

/-- The wedge of a basis indexed by `Fin k`, `k = dim E`, is not zero. -/
theorem wedge_basis_ne_zero' [FiniteDimensional ℝ E] {k : ℕ} (b : Basis (Fin k) ℝ E)
    (hk : k = finrank ℝ E) : wedge b hk ≠ 0 :=
  (wedge_ne_zero_iff hk).2 b.linearIndependent

/-- `λ(E)` is spanned by the wedge of any basis: a linear map out of `λ(E)` is determined by its
value there. -/
theorem maxPow_linearMap_ext [FiniteDimensional ℝ E] {M : Type*} [AddCommGroup M] [Module ℝ M]
    {k : ℕ} (b : Basis (Fin k) ℝ E) (hk : k = finrank ℝ E) {φ ψ : maxPow E →ₗ[ℝ] M}
    (h : φ (wedge b hk) = ψ (wedge b hk)) : φ = ψ :=
  linearMap_ext_of_ne_zero finrank_maxPow (wedge_basis_ne_zero' b hk) h

/-! ### Alternating maps and wedges of two blocks -/

section AltMap

variable {W M : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup M] [Module ℝ M]

/-- An alternating map of `p` vectors of `W` is determined by its value on a basis `u` of `W`:
`g(v) = det_u(v) • g(u)` (the vector-valued form of `AlternatingMap.eq_smul_basis_det`). -/
theorem alternatingMap_eq_det_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : W [⋀^ι]→ₗ[ℝ] M) (u : Basis ι ℝ W) (v : ι → W) : g v = u.det v • g u := by
  have key : g = u.det.smulRight (g u) := by
    refine u.ext_alternating fun i h => ?_
    let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.1 h)
    change g (u ∘ σ) = (u.det.smulRight (g u)) (u ∘ σ)
    simp [AlternatingMap.map_perm, Basis.det_self]
  conv_lhs => rw [key]
  rfl

/-- Adding to the vectors indexed outside a set `I` vectors of the span of the vectors indexed by
`I` does not change the value of an alternating map. -/
theorem alternatingMap_eq_of_sub_mem_span {ι : Type*} [Finite ι]
    (g : W [⋀^ι]→ₗ[ℝ] M) (I : Set ι) {v v' : ι → W} (hI : ∀ i ∈ I, v' i = v i)
    (h : ∀ i ∉ I, v' i - v i ∈ Submodule.span ℝ (v '' I)) : g v' = g v := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ s : Finset ι, g (fun i => if i ∈ s then v' i else v i) = g v by
    simpa using H Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    set w : ι → W := fun i => if i ∈ s then v' i else v i with hw
    have hupd : (fun i => if i ∈ insert j s then v' i else v i) = Function.update w j (v' j) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, hw]
    rw [hupd]
    by_cases hjI : j ∈ I
    · have : Function.update w j (v' j) = w := by
        rw [hI j hjI]
        funext i
        by_cases hij : i = j
        · subst hij; simp [hw, hj]
        · simp [Function.update_of_ne hij]
      rw [this, ih]
    · have hwj : w j = v j := by simp [hw, hj]
      have hsplit : v' j = w j + (v' j - v j) := by rw [hwj]; abel
      rw [hsplit, g.map_update_add, Function.update_eq_self, ih]
      suffices hz : g (Function.update w j (v' j - v j)) = 0 by rw [hz, add_zero]
      apply g.map_linearDependent
      intro hli
      apply hli.notMem_span_image (s := I) hjI
      rw [Function.update_self]
      have himg : Function.update w j (v' j - v j) '' I = v '' I := by
        apply Set.image_congr
        intro i hi
        have hij : i ≠ j := fun hij => hjI (hij ▸ hi)
        rw [Function.update_of_ne hij]
        by_cases his : i ∈ s
        · simp [hw, his, hI i hi]
        · simp [hw, his]
      rw [himg]
      exact h j hjI

end AltMap

section Blocks

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- `append (update u i y) w = update (append u w) (castAdd i) y`. -/
lemma append_update_left {α : Type*} {p q : ℕ} [DecidableEq (Fin p)] [DecidableEq (Fin (p + q))]
    (u : Fin p → α) (w : Fin q → α) (i : Fin p) (y : α) :
    Fin.append (Function.update u i y) w =
      Function.update (Fin.append u w) (Fin.castAdd q i) y := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · by_cases hij : j = i
    · subst hij; simp
    · rw [Fin.append_left, Function.update_of_ne hij, Function.update_of_ne
        (fun h => hij (Fin.castAdd_injective _ _ h)), Fin.append_left]
  · rw [Fin.append_right, Function.update_of_ne (fun h => by
      have := congrArg Fin.val h; simp at this; omega), Fin.append_right]

/-- `append u (update w i y) = update (append u w) (natAdd i) y`. -/
lemma append_update_right {α : Type*} {p q : ℕ} [DecidableEq (Fin q)]
    [DecidableEq (Fin (p + q))] (u : Fin p → α) (w : Fin q → α) (i : Fin q) (y : α) :
    Fin.append u (Function.update w i y) =
      Function.update (Fin.append u w) (Fin.natAdd p i) y := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Fin.append_left, Function.update_of_ne (fun h => by
      have := congrArg Fin.val h; simp at this; omega), Fin.append_left]
  · by_cases hij : j = i
    · subst hij; simp
    · rw [Fin.append_right, Function.update_of_ne hij, Function.update_of_ne
        (fun h => hij (Fin.natAdd_injective _ _ h)), Fin.append_right]

/-- The range of `append u w` is the union of the ranges. -/
lemma range_append {α : Type*} {p q : ℕ} (u : Fin p → α) (w : Fin q → α) :
    Set.range (Fin.append u w) = Set.range u ∪ Set.range w := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    induction j using Fin.addCases with
    | left j => exact Or.inl ⟨j, (Fin.append_left u w j).symm⟩
    | right j => exact Or.inr ⟨j, (Fin.append_right u w j).symm⟩
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd q j, Fin.append_left u w j⟩
    · exact ⟨Fin.natAdd p j, Fin.append_right u w j⟩

/-- `span (append u w) = span u ⊔ span w`. -/
lemma span_range_append {p q : ℕ} (u : Fin p → E) (w : Fin q → E) :
    Submodule.span ℝ (Set.range (Fin.append u w)) =
      Submodule.span ℝ (Set.range u) ⊔ Submodule.span ℝ (Set.range w) := by
  rw [range_append, Submodule.span_union]

/-- `f ∘ append u w = append (f ∘ u) (f ∘ w)`. -/
lemma comp_append {α β : Type*} {p q : ℕ} (f : α → β) (u : Fin p → α) (w : Fin q → α) :
    f ∘ Fin.append u w = Fin.append (f ∘ u) (f ∘ w) := by
  funext j
  induction j using Fin.addCases with
  | left j => simp
  | right j => simp

/-- The image under `append u w` of the left indices is the range of `u`. -/
lemma image_append_range_castAdd {α : Type*} {p q : ℕ} (u : Fin p → α) (w : Fin q → α) :
    Fin.append u w '' Set.range (Fin.castAdd q) = Set.range u := by
  rw [← Set.range_comp]
  congr 1
  funext j
  simp

/-- The image under `append u w` of the right indices is the range of `w`. -/
lemma image_append_range_natAdd {α : Type*} {p q : ℕ} (u : Fin p → α) (w : Fin q → α) :
    Fin.append u w '' Set.range (Fin.natAdd p) = Set.range w := by
  rw [← Set.range_comp]
  congr 1
  funext j
  simp

/-- The left and the right indices of `Fin (p + q)` are complementary sets. -/
lemma isCompl_range_castAdd_natAdd (p q : ℕ) :
    IsCompl (Set.range (Fin.castAdd q : Fin p → Fin (p + q))) (Set.range (Fin.natAdd p)) := by
  constructor
  · rw [Set.disjoint_left]
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    have := congrArg Fin.val hj
    simp at this
    omega
  · rw [codisjoint_iff]
    refine Set.eq_univ_of_forall fun x => ?_
    induction x using Fin.addCases with
    | left i => exact Or.inl ⟨i, rfl⟩
    | right i => exact Or.inr ⟨i, rfl⟩

/-- The right block of a linearly independent `append u w` is linearly independent. -/
lemma linearIndependent_of_append_right {p q : ℕ} {u : Fin p → E} {w : Fin q → E}
    (h : LinearIndependent ℝ (Fin.append u w)) : LinearIndependent ℝ w := by
  have := h.comp _ (Fin.natAdd_injective q p)
  rwa [show Fin.append u w ∘ Fin.natAdd p = w from funext (Fin.append_right u w)] at this

/-- The left block of a linearly independent `append u w` is linearly independent. -/
lemma linearIndependent_of_append_left {p q : ℕ} {u : Fin p → E} {w : Fin q → E}
    (h : LinearIndependent ℝ (Fin.append u w)) : LinearIndependent ℝ u := by
  have := h.comp _ (Fin.castAdd_injective p q)
  rwa [show Fin.append u w ∘ Fin.castAdd q = u from funext (Fin.append_left u w)] at this

/-- If `append u w` is a basis, the spans of `u` and of `w` are complements. -/
lemma isCompl_span_of_append [FiniteDimensional ℝ E] {p q : ℕ} {u : Fin p → E} {w : Fin q → E}
    (h : LinearIndependent ℝ (Fin.append u w)) (hk : p + q = finrank ℝ E) :
    IsCompl (Submodule.span ℝ (Set.range u)) (Submodule.span ℝ (Set.range w)) := by
  have := h.isCompl_span_image (h.span_eq_top_of_card_eq_finrank' (by simp [hk]))
    (isCompl_range_castAdd_natAdd p q)
  rwa [image_append_range_castAdd, image_append_range_natAdd] at this

/-- The alternating map `u ↦ g(append u w)` of the left block. -/
def appendLeftMap {p q : ℕ} (g : E [⋀^Fin (p + q)]→ₗ[ℝ] M) (w : Fin q → E) :
    E [⋀^Fin p]→ₗ[ℝ] M where
  toFun u := g (Fin.append u w)
  map_update_add' u i x y := by
    simp only [append_update_left]
    exact g.map_update_add _ _ _ _
  map_update_smul' u i c x := by
    simp only [append_update_left]
    exact g.map_update_smul _ _ _ _
  map_eq_zero_of_eq' u i j hij hne :=
    g.map_eq_zero_of_eq _ (by simp [Fin.append_left, hij])
      (fun h => hne (Fin.castAdd_injective _ _ h))

/-- The alternating map `w ↦ g(append u w)` of the right block. -/
def appendRightMap {p q : ℕ} (g : E [⋀^Fin (p + q)]→ₗ[ℝ] M) (u : Fin p → E) :
    E [⋀^Fin q]→ₗ[ℝ] M where
  toFun w := g (Fin.append u w)
  map_update_add' w i x y := by
    simp only [append_update_right]
    exact g.map_update_add _ _ _ _
  map_update_smul' w i c x := by
    simp only [append_update_right]
    exact g.map_update_smul _ _ _ _
  map_eq_zero_of_eq' w i j hij hne :=
    g.map_eq_zero_of_eq _ (by simp [Fin.append_right, hij])
      (fun h => hne (Fin.natAdd_injective _ _ h))

end Blocks

/-- **Change of basis**: `f(u'₁) ∧ … ∧ f(u'ₚ) = det_u(u') · f(u₁) ∧ … ∧ f(uₚ)` for a linear map
`f : W → E` and a basis `u` of `W`. -/
theorem wedge_comp_basis {W : Type*} [AddCommGroup W] [Module ℝ W] {p : ℕ} (f : W →ₗ[ℝ] E)
    (u : Basis (Fin p) ℝ W) (u' : Fin p → W) (hk : p = finrank ℝ E) :
    wedge (f ∘ u') hk = u.det u' • wedge (f ∘ u) hk := by
  apply Subtype.ext
  simp only [coe_wedge, SetLike.val_smul]
  exact alternatingMap_eq_det_smul ((ExteriorAlgebra.ιMulti ℝ p).compLinearMap f) u u'

/-- **Change of basis**: `u'₁ ∧ … ∧ u'ₚ = det_u(u') · u₁ ∧ … ∧ uₚ` for a basis `u` of `E` indexed
by `Fin p`. -/
theorem wedge_eq_det_smul' {p : ℕ} (u : Basis (Fin p) ℝ E) (u' : Fin p → E)
    (hk : p = finrank ℝ E) : wedge u' hk = u.det u' • wedge u hk :=
  wedge_comp_basis LinearMap.id u u' hk

/-- **Change of basis in the left block**: for a linear map `f : W → E` and a basis `u` of `W`,
`f(u') ∧ w = det_u(u') · f(u) ∧ w`. -/
theorem wedge_append_basis_left {W : Type*} [AddCommGroup W] [Module ℝ W] {p q : ℕ}
    (f : W →ₗ[ℝ] E) (u : Basis (Fin p) ℝ W) (u' : Fin p → W) (w : Fin q → E)
    (hk : p + q = finrank ℝ E) :
    wedge (Fin.append (f ∘ u') w) hk = u.det u' • wedge (Fin.append (f ∘ u) w) hk := by
  apply Subtype.ext
  simp only [coe_wedge, SetLike.val_smul]
  exact alternatingMap_eq_det_smul
    ((appendLeftMap (ExteriorAlgebra.ιMulti ℝ (p + q)) w).compLinearMap f) u u'

/-- **Change of basis in the right block**: for a linear map `g : W → E` and a basis `w` of `W`,
`u ∧ g(w') = det_w(w') · u ∧ g(w)`. -/
theorem wedge_append_basis_right {W : Type*} [AddCommGroup W] [Module ℝ W] {p q : ℕ}
    (g : W →ₗ[ℝ] E) (u : Fin p → E) (w : Basis (Fin q) ℝ W) (w' : Fin q → W)
    (hk : p + q = finrank ℝ E) :
    wedge (Fin.append u (g ∘ w')) hk = w.det w' • wedge (Fin.append u (g ∘ w)) hk := by
  apply Subtype.ext
  simp only [coe_wedge, SetLike.val_smul]
  exact alternatingMap_eq_det_smul
    ((appendRightMap (ExteriorAlgebra.ιMulti ℝ (p + q)) u).compLinearMap g) w w'

/-- **Adding to the right block vectors of the span of the left block** does not change the
wedge: `u ∧ (w + x) = u ∧ w` if every `xᵢ` lies in the span of `u`. -/
theorem wedge_append_add_right {p q : ℕ} (u : Fin p → E) (w x : Fin q → E)
    (hx : ∀ i, x i ∈ Submodule.span ℝ (Set.range u)) (hk : p + q = finrank ℝ E) :
    wedge (Fin.append u (w + x)) hk = wedge (Fin.append u w) hk := by
  apply Subtype.ext
  simp only [coe_wedge]
  apply alternatingMap_eq_of_sub_mem_span _ (Set.range (Fin.castAdd q))
  · rintro _ ⟨i, rfl⟩
    simp
  · intro i hi
    rw [image_append_range_castAdd]
    induction i using Fin.addCases with
    | left i => exact absurd ⟨i, rfl⟩ hi
    | right i => simpa using hx i

/-- **Adding to the left block vectors of the span of the right block** does not change the
wedge: `(u + x) ∧ w = u ∧ w` if every `xᵢ` lies in the span of `w`. -/
theorem wedge_append_add_left {p q : ℕ} (u x : Fin p → E) (w : Fin q → E)
    (hx : ∀ i, x i ∈ Submodule.span ℝ (Set.range w)) (hk : p + q = finrank ℝ E) :
    wedge (Fin.append (u + x) w) hk = wedge (Fin.append u w) hk := by
  apply Subtype.ext
  simp only [coe_wedge]
  apply alternatingMap_eq_of_sub_mem_span _ (Set.range (Fin.natAdd p))
  · rintro _ ⟨i, rfl⟩
    simp
  · intro i hi
    rw [image_append_range_natAdd]
    induction i using Fin.addCases with
    | left i => simpa using hx i
    | right i => exact absurd ⟨i, rfl⟩ hi

/-- A family of `dim E` vectors spanning `E` has a nonzero wedge. -/
theorem wedge_ne_zero_of_span_eq_top [FiniteDimensional ℝ E] {k : ℕ} {v : Fin k → E}
    (hk : k = finrank ℝ E) (hv : ⊤ ≤ Submodule.span ℝ (Set.range v)) : wedge v hk ≠ 0 :=
  (wedge_ne_zero_iff hk).2
    (linearIndependent_of_top_le_span_of_card_eq_finrank hv (by simp [hk]))

/-- The wedge does not depend on how the blocks are bracketed: `u ∧ (v ∧ w) = (u ∧ v) ∧ w`. -/
theorem wedge_append_assoc {p q r : ℕ} (u : Fin p → E) (v : Fin q → E) (w : Fin r → E)
    (h1 : p + (q + r) = finrank ℝ E) (h2 : p + q + r = finrank ℝ E) :
    wedge (Fin.append u (Fin.append v w)) h1 = wedge (Fin.append (Fin.append u v) w) h2 := by
  rw [Fin.append_assoc]
  exact (wedge_cast _ h1 _).symm

/-! ### Induced maps -/

/-- `λ(Φ) : λ(E) → λ(F)` for `dim E = dim F`: `Φ(a₁) ∧ … ∧ Φ(aₙ)` on `a₁ ∧ … ∧ aₙ` (Mathlib's
`exteriorPower.map`, read in degree `dim F`). -/
def maxPowMap (Φ : E →ₗ[ℝ] F) (h : finrank ℝ E = finrank ℝ F) : maxPow E →ₗ[ℝ] maxPow F :=
  (LinearEquiv.ofEq _ _ (by rw [h])).toLinearMap ∘ₗ exteriorPower.map (finrank ℝ E) Φ

/-- The defining formula `λ(Φ)(a₁ ∧ … ∧ aₙ) = Φ(a₁) ∧ … ∧ Φ(aₙ)`. -/
@[simp] theorem maxPowMap_wedge (Φ : E →ₗ[ℝ] F) (h : finrank ℝ E = finrank ℝ F) {k : ℕ}
    (v : Fin k → E) (hk : k = finrank ℝ E) :
    maxPowMap Φ h (wedge v hk) = wedge (Φ ∘ v) (hk.trans h) := by
  subst hk
  apply Subtype.ext
  simp only [maxPowMap, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.coe_ofEq_apply, wedge_eq_ιMulti, exteriorPower.map_apply_ιMulti,
    exteriorPower.ιMulti_apply_coe, coe_wedge]

/-- `λ(Ψ ∘ Φ) = λ(Ψ) ∘ λ(Φ)`. -/
theorem maxPowMap_comp (Φ : E →ₗ[ℝ] F) (Ψ : F →ₗ[ℝ] G) (h : finrank ℝ E = finrank ℝ F)
    (h' : finrank ℝ F = finrank ℝ G) :
    maxPowMap (Ψ ∘ₗ Φ) (h.trans h') = maxPowMap Ψ h' ∘ₗ maxPowMap Φ h := by
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
    ← wedge_eq_ιMulti, maxPowMap_wedge, coe_wedge]
  rfl

/-- `λ(id) = id`. -/
@[simp] theorem maxPowMap_id : maxPowMap (LinearMap.id : E →ₗ[ℝ] E) rfl = LinearMap.id := by
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, ← wedge_eq_ιMulti, maxPowMap_wedge,
    LinearMap.id_coe, LinearMap.id_apply]
  rfl

/-- **`λ(Φ)` is nonzero exactly when `Φ` is an isomorphism** (for `dim E = dim F` finite). -/
theorem maxPowMap_ne_zero_iff [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (Φ : E →ₗ[ℝ] F) (h : finrank ℝ E = finrank ℝ F) :
    maxPowMap Φ h ≠ 0 ↔ Function.Bijective Φ := by
  set b := Module.finBasis ℝ E
  constructor
  · intro hne
    have hinj : Function.Injective Φ := by
      by_contra hni
      apply hne
      apply maxPow_linearMap_ext b rfl
      rw [maxPowMap_wedge, LinearMap.zero_apply]
      apply wedge_eq_zero_of_not_linearIndependent
      intro hli
      have htop := hli.span_eq_top_of_card_eq_finrank' (by simp [h])
      have hsurj : Function.Surjective Φ := by
        rw [← LinearMap.range_eq_top, eq_top_iff, ← htop, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact ⟨b i, rfl⟩
      exact hni ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).2 hsurj)
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).1 hinj⟩
  · intro hbij hz
    have := congrArg (fun φ => φ (wedge b rfl)) hz
    simp only [maxPowMap_wedge, LinearMap.zero_apply] at this
    exact (wedge_ne_zero_iff _).2 (b.linearIndependent.map' Φ (LinearMap.ker_eq_bot.2 hbij.1))
      this

/-- `λ*(Φ) : λ*(F) → λ*(E)`, the dual of `λ(Φ)`. -/
def maxPowDualMap (Φ : E →ₗ[ℝ] F) (h : finrank ℝ E = finrank ℝ F) :
    maxPowDual F →ₗ[ℝ] maxPowDual E :=
  Module.Dual.transpose (maxPowMap Φ h)

@[simp] theorem maxPowDualMap_apply (Φ : E →ₗ[ℝ] F) (h : finrank ℝ E = finrank ℝ F)
    (φ : maxPowDual F) (x : maxPow E) : maxPowDualMap Φ h φ x = φ (maxPowMap Φ h x) := rfl

/-! ### Definition 6.3.1 (preprint 6.3): `ι : λ(E*) → λ*(E)` -/

variable (E) in
/-- **Definition 6.3.1 (preprint 6.3)**: `ι : λ(E*) → λ*(E)`, `ι(e₁* ∧ … ∧ eₙ*)(a₁ ∧ … ∧ aₙ) = det(eᵢ*(aⱼ))`:
Mathlib's pairing `⋀ⁿ E* → (⋀ⁿ E)*` in degree `n = dim E = dim E*`. -/
def iotaDual : maxPow (Module.Dual ℝ E) →ₗ[ℝ] maxPowDual E :=
  exteriorPower.pairingDual ℝ E (finrank ℝ E) ∘ₗ
    (LinearEquiv.ofEq _ _ (by simp only [maxPow, Subspace.dual_finrank_eq])).toLinearMap

/-- **Definition 6.3.1 (preprint 6.3), the defining formula**: `ι(e₁* ∧ … ∧ eₙ*)(a₁ ∧ … ∧ aₙ) = det(eᵢ*(aⱼ))`. -/
theorem iotaDual_wedge_wedge {k : ℕ} (e : Fin k → Module.Dual ℝ E)
    (he : k = finrank ℝ (Module.Dual ℝ E)) (a : Fin k → E) (ha : k = finrank ℝ E) :
    iotaDual E (wedge e he) (wedge a ha) = (Matrix.of fun i j => e i (a j)).det := by
  subst ha
  have : LinearEquiv.ofEq _ _ (by simp only [maxPow, Subspace.dual_finrank_eq]) (wedge e he) =
      exteriorPower.ιMulti ℝ (finrank ℝ E) e := Subtype.ext rfl
  rw [iotaDual, LinearMap.comp_apply, LinearEquiv.coe_coe, this, wedge_eq_ιMulti,
    exteriorPower.pairingDual_ιMulti_ιMulti, ← Matrix.det_transpose]
  rfl

/-- **`ι(e₁* ∧ … ∧ eₙ*) = (e₁ ∧ … ∧ eₙ)*`** for a basis and its dual basis. -/
theorem iotaDual_wedge_dualBasis [FiniteDimensional ℝ E] {k : ℕ} (b : Basis (Fin k) ℝ E)
    (hk : k = finrank ℝ E) :
    iotaDual E (wedge (fun i => b.dualBasis i) (hk.trans Subspace.dual_finrank_eq.symm)) =
      dualVec (wedge b hk) := by
  apply eq_dualVec_of_apply_eq_one finrank_maxPow (wedge_basis_ne_zero' b hk)
  rw [iotaDual_wedge_wedge]
  convert Matrix.det_one (n := Fin k) (R := ℝ)
  ext i j
  rw [Matrix.of_apply, Basis.dualBasis_apply_self, Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

/-- `ι` is nonzero, hence an isomorphism of lines. -/
theorem iotaDual_ne_zero [FiniteDimensional ℝ E] : iotaDual E ≠ 0 := by
  intro h
  have := iotaDual_wedge_dualBasis (Module.finBasis ℝ E) rfl
  rw [h, LinearMap.zero_apply] at this
  exact dualVec_ne_zero finrank_maxPow (wedge_basis_ne_zero _) this.symm

/-! ### `λ` and `λ*` of an isomorphism -/

section Equiv

theorem maxPowMap_eq_id {Φ : E →ₗ[ℝ] E} (hΦ : Φ = LinearMap.id) (h : finrank ℝ E = finrank ℝ E) :
    maxPowMap Φ h = LinearMap.id := by
  subst hΦ; exact maxPowMap_id

/-- `λ(Φ) : λ(E) ≅ λ(F)` for a linear isomorphism `Φ : E ≅ F`. -/
def maxPowEquiv (Φ : E ≃ₗ[ℝ] F) : maxPow E ≃ₗ[ℝ] maxPow F :=
  LinearEquiv.ofLinearMap (maxPowMap Φ Φ.finrank_eq) (maxPowMap Φ.symm Φ.symm.finrank_eq)
    (by rw [← maxPowMap_comp]; exact maxPowMap_eq_id (by ext; simp) _)
    (by rw [← maxPowMap_comp]; exact maxPowMap_eq_id (by ext; simp) _)

theorem coe_maxPowEquiv (Φ : E ≃ₗ[ℝ] F) :
    (maxPowEquiv Φ : maxPow E →ₗ[ℝ] maxPow F) = maxPowMap Φ Φ.finrank_eq := rfl

@[simp] theorem maxPowEquiv_wedge (Φ : E ≃ₗ[ℝ] F) {k : ℕ} (v : Fin k → E) (hk : k = finrank ℝ E) :
    maxPowEquiv Φ (wedge v hk) = wedge (Φ ∘ v) (hk.trans Φ.finrank_eq) :=
  maxPowMap_wedge _ Φ.finrank_eq _ _

/-- `λ*(Φ) : λ*(F) ≅ λ*(E)` for a linear isomorphism `Φ : E ≅ F` (the transpose of `λ(Φ)`). -/
def maxPowDualEquiv (Φ : E ≃ₗ[ℝ] F) : maxPowDual F ≃ₗ[ℝ] maxPowDual E :=
  (maxPowEquiv Φ).dualMap

theorem coe_maxPowDualEquiv (Φ : E ≃ₗ[ℝ] F) :
    (maxPowDualEquiv Φ : maxPowDual F →ₗ[ℝ] maxPowDual E) = maxPowDualMap Φ Φ.finrank_eq := rfl

/-- `λ*(Φ)((Φ v₁ ∧ … ∧ Φ vₖ)*) = (v₁ ∧ … ∧ vₖ)*` for a basis `v`. -/
theorem maxPowDualEquiv_dualVec [FiniteDimensional ℝ E] (Φ : E ≃ₗ[ℝ] F) {k : ℕ} {v : Fin k → E}
    (hv : LinearIndependent ℝ v) (hk : k = finrank ℝ E) :
    maxPowDualEquiv Φ (dualVec (wedge (Φ ∘ v) (hk.trans Φ.finrank_eq))) = dualVec (wedge v hk) := by
  have hΦv : LinearIndependent ℝ (Φ ∘ v) := hv.map' (Φ : E →ₗ[ℝ] F) Φ.ker
  have : FiniteDimensional ℝ F := Φ.finiteDimensional
  apply eq_dualVec_of_apply_eq_one finrank_maxPow ((wedge_ne_zero_iff hk).2 hv)
  change dualVec _ (maxPowEquiv Φ (wedge v hk)) = 1
  rw [maxPowEquiv_wedge]
  exact dualVec_self finrank_maxPow ((wedge_ne_zero_iff _).2 hΦv)

/-- `λ*(Φ)(w₁ ∧ … ∧ wₖ)* = (Φ⁻¹ w₁ ∧ … ∧ Φ⁻¹ wₖ)*` for a basis `w` of `F`. -/
theorem maxPowDualEquiv_dualVec_symm [FiniteDimensional ℝ E] (Φ : E ≃ₗ[ℝ] F) {k : ℕ}
    {w : Fin k → F} (hw : LinearIndependent ℝ w) (hk : k = finrank ℝ F) :
    maxPowDualEquiv Φ (dualVec (wedge w hk)) =
      dualVec (wedge (Φ.symm ∘ w) (hk.trans Φ.symm.finrank_eq)) := by
  have hv : LinearIndependent ℝ (Φ.symm ∘ w) := hw.map' (Φ.symm : F →ₗ[ℝ] E) Φ.symm.ker
  have : ⇑Φ ∘ ⇑Φ.symm ∘ w = w := by
    funext i
    simp
  rw [← maxPowDualEquiv_dualVec Φ hv, this]

end Equiv

/-! ### Proposition 6.3.2 (preprint 6.4) -/

/-- **Proposition 6.3.2 (preprint 6.4)**: for an isomorphism `Φ : E → F` of finite-dimensional spaces and its dual
`Φ* : F* → E*`, `λ*(Φ) ∘ ι = ι ∘ λ(Φ*) : λ(F*) → λ*(E)`. -/
theorem proposition_6_3_2 [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] (Φ : E ≃ₗ[ℝ] F) :
    maxPowDualMap (Φ : E →ₗ[ℝ] F) Φ.finrank_eq ∘ₗ iotaDual F =
      iotaDual E ∘ₗ maxPowMap (Module.Dual.transpose (Φ : E →ₗ[ℝ] F))
        (by rw [Subspace.dual_finrank_eq, Subspace.dual_finrank_eq, Φ.finrank_eq]) := by
  have hn : finrank ℝ (Module.Dual ℝ F) = finrank ℝ E := by
    rw [Subspace.dual_finrank_eq, Φ.finrank_eq]
  apply maxPow_linearMap_ext ((Module.finBasis ℝ (Module.Dual ℝ F)).reindex (finCongr hn))
    hn.symm
  apply maxPow_linearMap_ext (Module.finBasis ℝ E) rfl
  simp only [LinearMap.comp_apply, maxPowDualMap_apply, maxPowMap_wedge]
  rw [iotaDual_wedge_wedge, iotaDual_wedge_wedge]
  rfl

end Polyfold
