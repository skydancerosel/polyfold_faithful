import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_7

/-! Round trip for V6_7 ((92) and Proposition 6.6: the isomorphism `Ψ_E`).

The listed declarations are the definitions `Polyfold.contractDual` (`ῑ`),
`Polyfold.FourTermExact.psi` (`Ψ_E`) and the theorem `Polyfold.FourTermExact.proposition_6_6`, so
`A` is `proposition_6_6` (universes at `0`): `Ψ_E(w_C ⊗ (w_A ⊗ w_D*)) = w_B` for every project
`Choice`.  B is the conjunction of (1) `ῑ(v ⊗ b ⊗ v*) = b`, (2) the defining formula (92) of
`Ψ_E`, (3) `Ψ_E` bijective, (4) the formula of Proposition 6.6 for every `Choice91` and every `φ_D`
with `φ_D(w_D) = 1`.

* `A ⇒ B`: (1) is `contractDual_tmul` (`ῑ(v ⊗ b ⊗ φ) = φ(v) b`), (2) holds by definition, both
  without A; (3) from A: `Ψ_E` is a map between lines that is nonzero at
  `w_C ⊗ (w_A ⊗ w_D*)` (A gives the value `w_B ≠ 0`, canonical choice); (4) is A for
  `χ.toChoice`, with `φ_D = w_D*` on the line `λ*(D)`.
* `B ⇒ A`: a project choice is reindexed into a `Choice91` and (4) is applied with `φ_D = w_D*`.
-/

namespace RoundTrip.V6_7
open Polyfold Module
open scoped TensorProduct

/-- The project's statement (Proposition 6.6), universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.FourTermExact.proposition_6_6.{0, 0, 0, 0}

theorem A_holds : A := @Polyfold.FourTermExact.proposition_6_6.{0, 0, 0, 0}

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

theorem toChoice_wedgeC (χ : Choice91 S) : χ.toChoice.wedgeC = χ.wC := rfl

theorem toChoice_wedgeB (χ : Choice91 S) : χ.toChoice.wedgeB = χ.wB := rfl

theorem wD_ne_zero (χ : Choice91 S) : χ.wD ≠ 0 := wedge_basis_ne_zero χ.d

/-- `λ(C) ⊗ (λ(A) ⊗ λ*(D))` is a line. -/
theorem finrank_psi_source :
    finrank ℝ (maxPow C ⊗[ℝ] (maxPow A ⊗[ℝ] maxPowDual D)) = 1 := by
  rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct, finrank_maxPow, finrank_maxPow,
    finrank_maxPowDual]

end Glue

/-- `A ⇒ B`. -/
theorem A_to_B : A → B := by
  intro hA
  refine ⟨?_, ?_⟩
  · intro B C _ _ _ _ _ _ v _ b φ hφ
    rw [contractDual_tmul, hφ, one_smul]
  · intro A B C D _ _ _ _ _ _ _ _ _ _ _ _ S
    refine ⟨fun c h => rfl, ?_, ?_⟩
    · -- `Ψ_E` is a nonzero map between lines
      have hv := tmul_ne_zero_of_ne_zero (M := maxPow C) (N := maxPow A ⊗[ℝ] maxPowDual D)
        S.canonicalChoice.wedgeC_ne_zero S.canonicalChoice.source_ne_zero
      refine bijective_of_finrank_eq_one (L := maxPow C ⊗[ℝ] (maxPow A ⊗[ℝ] maxPowDual D))
        (M := maxPow B) finrank_psi_source finrank_maxPow S.psi hv ?_
      rw [hA S S.canonicalChoice]
      exact S.canonicalChoice.wedgeB_ne_zero
    · intro χ φD hD
      rw [eq_dualVec_of_apply_eq_one finrank_maxPow (wD_ne_zero χ) hD]
      exact hA S χ.toChoice

/-- `B ⇒ A`. -/
theorem B_to_A : B → A := by
  intro hB A B C D _ _ _ _ _ _ _ _ S _ _ _ _ χ
  have hBdim := χ.hB
  have hCdim := χ.hC
  obtain ⟨n, l, j, Z, hZ, V, hV, a, d, b', c, hc, hγc⟩ := χ
  have hn : n = finrank ℝ A := by rw [finrank_eq_card_basis a, Fintype.card_fin]
  have hl : l = finrank ℝ D := by rw [finrank_eq_card_basis d, Fintype.card_fin]
  subst hn hl
  dsimp only at hBdim hCdim
  let χ' : Choice91 S :=
    { a := a, d := d, j := j, Z := Z, isCompl_Z := hZ, b' := b', V := V, isCompl_V := hV,
      c := c, c_mem := hc, γ_c := hγc, dimB := hBdim, dimC := hCdim }
  exact (hB.2 A B C D S).2.2 χ' (dualVec χ'.wD)
    (dualVec_self finrank_maxPow (wedge_basis_ne_zero d))

#rt_check RoundTrip.V6_7.A_to_B [Polyfold.FourTermExact.proposition_6_6]
#rt_check RoundTrip.V6_7.B_to_A [Polyfold.FourTermExact.proposition_6_6]
#rt_overlap RoundTrip.V6_7.B_to_A [Polyfold.FourTermExact.proposition_6_6]

end RoundTrip.V6_7
