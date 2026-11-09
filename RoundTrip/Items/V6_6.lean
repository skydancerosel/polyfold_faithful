import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_6

/-! Round trip for V6_6 (Lemma 6.5: `Φ_E` does not depend on the choices).

`A` is `Polyfold.FourTermExact.lemma_6_3_3` (universes at `0`): the project's `Φ_E`
(`FourTermExact.phi`, made from the canonical choice) satisfies (91) for every project `Choice`.
B's `Choice91` is the project's `Choice` with `n = dim A`, `l = dim D` fixed (bases indexed by
`Fin (finrank ·)`) and the two dimension equations as fields; B's wedges are definitionally the
project's `wedgeB`, `wedgeC`, `source`.  B's `Sat91 Φ χ` quantifies over all `φ_D`, `φ_C` with
`φ_D(w_D) = 1`, `φ_C(w_C) = 1`; on a line these are the dual vectors `dualVec w_D`, `dualVec w_C`.

* `A ⇒ B`: part (2) of B is A for `χ.toChoice`; part (1) (the intrinsic reading) follows: a map
  satisfying (91) for `χ₁` agrees with `Φ_E` on the nonzero source vector of `χ₁`, so it is `Φ_E`
  (the source is a line), which satisfies (91) for `χ₂` by part (2).
* `B ⇒ A`: a project choice is reindexed (`n = dim A`, `l = dim D` by `subst`) into a `Choice91`
  and part (2) of B is applied with `φ_D = w_D*`, `φ_C = w_C*`.
-/

namespace RoundTrip.V6_6
open Polyfold Module
open scoped TensorProduct

/-- The project's statement (Lemma 6.5), universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.FourTermExact.lemma_6_3_3.{0, 0, 0, 0}

theorem A_holds : A := @Polyfold.FourTermExact.lemma_6_3_3.{0, 0, 0, 0}

set_option linter.unusedSectionVars false

noncomputable section Glue
variable {A B C D : Type} [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
  [AddCommGroup C] [Module ℝ C] [AddCommGroup D] [Module ℝ D]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
  [FiniteDimensional ℝ D] {S : FourTermExact A B C D}

/-- B's choice of (91) as a project choice. -/
def Choice91.toChoice (χ : Choice91 S) : S.Choice where
  n := finrank ℝ A
  l := finrank ℝ D
  j := χ.j
  Z := χ.Z
  isCompl_Z := χ.isCompl_Z
  V := χ.V
  isCompl_V := χ.isCompl_V
  a := χ.a
  d := χ.d
  b' := χ.b'
  c := χ.c
  c_mem := χ.c_mem
  γ_c := χ.γ_c

theorem toChoice_source (χ : Choice91 S) : χ.toChoice.source = χ.wA ⊗ₜ dualVec χ.wD := rfl

theorem toChoice_value (χ : Choice91 S) : χ.toChoice.value = χ.wB ⊗ₜ dualVec χ.wC := rfl

theorem wD_ne_zero (χ : Choice91 S) : χ.wD ≠ 0 := wedge_basis_ne_zero χ.d

theorem wC_ne_zero (χ : Choice91 S) : χ.wC ≠ 0 := χ.toChoice.wedgeC_ne_zero

/-- On lines, `Sat91 Φ χ` is (91) with the dual vectors `w_D*`, `w_C*`. -/
theorem sat_iff (Φ : (maxPow A ⊗[ℝ] maxPowDual D) →ₗ[ℝ] (maxPow B ⊗[ℝ] maxPowDual C))
    (χ : Choice91 S) :
    Sat91 Φ χ ↔ Φ (χ.wA ⊗ₜ dualVec χ.wD) = χ.wB ⊗ₜ dualVec χ.wC := by
  constructor
  · intro h
    exact h _ _ (dualVec_self finrank_maxPow (wD_ne_zero χ))
      (dualVec_self finrank_maxPow (wC_ne_zero χ))
  · intro h φD φC hD hC
    rw [eq_dualVec_of_apply_eq_one finrank_maxPow (wD_ne_zero χ) hD,
      eq_dualVec_of_apply_eq_one finrank_maxPow (wC_ne_zero χ) hC]
    exact h

end Glue

/-- `A ⇒ B`. -/
theorem A_to_B : A → B := by
  intro hA A B C D _ _ _ _ _ _ _ _ _ _ _ _ S
  have h2 : ∀ χ : Choice91 S, Sat91 S.phi χ := fun χ =>
    (sat_iff _ χ).2 (hA S χ.toChoice)
  refine ⟨fun χ₁ χ₂ Φ h1 => ?_, h2⟩
  have hΦ : Φ = S.phi := by
    refine linearMap_ext_of_ne_zero (L := maxPow A ⊗[ℝ] maxPowDual D)
      (M := maxPow B ⊗[ℝ] maxPowDual C)
      FourTermExact.finrank_source χ₁.toChoice.source_ne_zero ?_
    exact ((sat_iff Φ χ₁).1 h1).trans (hA S χ₁.toChoice).symm
  subst hΦ
  exact h2 χ₂

/-- `B ⇒ A`. -/
theorem B_to_A : B → A := by
  intro hB A B C D _ _ _ _ _ _ _ _ S _ _ _ _ χ
  have hBdim := χ.hB
  have hCdim := χ.hC
  have hwC := χ.wedgeC_ne_zero
  obtain ⟨n, l, j, Z, hZ, V, hV, a, d, b', c, hc, hγc⟩ := χ
  have hn : n = finrank ℝ A := by rw [finrank_eq_card_basis a, Fintype.card_fin]
  have hl : l = finrank ℝ D := by rw [finrank_eq_card_basis d, Fintype.card_fin]
  subst hn hl
  dsimp only at hBdim hCdim
  let χ' : Choice91 S :=
    { a := a, d := d, j := j, Z := Z, isCompl_Z := hZ, b' := b', V := V, isCompl_V := hV,
      c := c, c_mem := hc, γ_c := hγc, dimB := hBdim, dimC := hCdim }
  exact (hB A B C D S).2 χ' (dualVec χ'.wD) (dualVec χ'.wC)
    (dualVec_self finrank_maxPow (wedge_basis_ne_zero d)) (dualVec_self finrank_maxPow hwC)

#rt_check RoundTrip.V6_6.A_to_B [Polyfold.FourTermExact.lemma_6_3_3]
#rt_check RoundTrip.V6_6.B_to_A [Polyfold.FourTermExact.lemma_6_3_3]
#rt_overlap RoundTrip.V6_6.B_to_A [Polyfold.FourTermExact.lemma_6_3_3]

end RoundTrip.V6_6
