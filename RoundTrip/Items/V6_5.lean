import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_5

/-! Round trip for V6_5 (§6.2, p. 206, (91): `Φ_E`).  The comparison row lists the definitions
`FourTermExact`, `Choice`, `Choice.value`, `canonicalChoice`, `phi`, `phiEquiv` and one theorem,
`FourTermExact.phi_ne_zero`; A is its type, universes at `0`.  B's clauses (1) (the wedges of every
choice are nonzero) and (2) (`Φ_E` is the map of (91) for some choice) are about the definitions,
not about A's theorem: they are proved here from the definitions (`phi` is (91) for
`canonicalChoice`) and the non-item lemmas `wedgeB_ne_zero`, `wedgeC_ne_zero`,
`wedge_basis_ne_zero`, `source_ne_zero`, `eq_dualVec_of_apply_eq_one`, `dualVec_self`; A is used
for (3) (bijectivity, as "a nonzero map of lines").  Lemma 6.5 (`lemma_6_3_3`, item V6_6) is not
used. -/

namespace RoundTrip.V6_5
open Polyfold Module
open scoped TensorProduct

noncomputable section

/-- The project's statement (`Φ_E ≠ 0`), universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.FourTermExact.phi_ne_zero.{0, 0, 0, 0}

theorem A_holds : A := @Polyfold.FourTermExact.phi_ne_zero.{0, 0, 0, 0}

/-- A nonzero linear map between lines is bijective. -/
theorem bijective_of_ne_zero {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] (hM : finrank ℝ M = 1) (hN : finrank ℝ N = 1) {L : M →ₗ[ℝ] N} (hL : L ≠ 0) :
    Function.Bijective L := by
  obtain ⟨x, hx⟩ : ∃ x, L x ≠ 0 := by
    by_contra h
    exact hL (LinearMap.ext fun y => not_not.1 fun hy => h ⟨y, hy⟩)
  have hx0 : x ≠ 0 := fun h => hx (by simp [h])
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨c, rfl⟩ := _root_.exists_smul_eq_of_finrank_eq_one hM hx0 y
    rw [map_smul] at hy
    rw [(smul_eq_zero.1 hy).resolve_right hx, zero_smul]
  · intro w
    obtain ⟨c, rfl⟩ := _root_.exists_smul_eq_of_finrank_eq_one hN hx w
    exact ⟨c • x, map_smul L c x⟩

/-- An injective linear map out of a line is not zero. -/
theorem ne_zero_of_injective {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] (hM : finrank ℝ M = 1) {L : M →ₗ[ℝ] N} (hL : Function.Injective L) : L ≠ 0 := by
  have := Module.finite_of_finrank_eq_succ hM
  obtain ⟨w, hw⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := M)).1 (by omega)
  intro h
  apply hw
  apply hL
  rw [h, LinearMap.zero_apply, map_zero]

section Glue
variable {A₁ B₁ C₁ D₁ : Type} [AddCommGroup A₁] [Module ℝ A₁] [AddCommGroup B₁] [Module ℝ B₁]
  [AddCommGroup C₁] [Module ℝ C₁] [AddCommGroup D₁] [Module ℝ D₁] {S : FourTermExact A₁ B₁ C₁ D₁}

/-- A blind choice of (91) is a project choice. -/
def toChoice (χ : Choice91 S) : S.Choice where
  n := finrank ℝ A₁
  l := finrank ℝ D₁
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

variable [FiniteDimensional ℝ A₁] [FiniteDimensional ℝ B₁] [FiniteDimensional ℝ C₁]
  [FiniteDimensional ℝ D₁]

omit [FiniteDimensional ℝ C₁] [FiniteDimensional ℝ D₁] in
theorem wB_eq (χ : Choice91 S) : χ.wB = (toChoice χ).wedgeB := rfl
omit [FiniteDimensional ℝ A₁] [FiniteDimensional ℝ B₁] in
theorem wC_eq (χ : Choice91 S) : χ.wC = (toChoice χ).wedgeC := rfl

/-- The project's canonical choice, as a blind choice. -/
def canon (S : FourTermExact A₁ B₁ C₁ D₁) : Choice91 S where
  a := S.canonicalChoice.a
  d := S.canonicalChoice.d
  j := S.canonicalChoice.j
  Z := S.canonicalChoice.Z
  isCompl_Z := S.canonicalChoice.isCompl_Z
  b' := S.canonicalChoice.b'
  V := S.canonicalChoice.V
  isCompl_V := S.canonicalChoice.isCompl_V
  c := S.canonicalChoice.c
  c_mem := S.canonicalChoice.c_mem
  γ_c := S.canonicalChoice.γ_c
  dimB := S.canonicalChoice.hB
  dimC := S.canonicalChoice.hC

end Glue

theorem A_to_B : A → B := by
  intro hA A₁ B₁ C₁ D₁ _ _ _ _ _ _ _ _ _ _ _ _ S
  refine ⟨fun χ => ⟨?_, ?_, ?_, ?_⟩, ⟨canon S, ?_⟩, ?_⟩
  · exact wedge_basis_ne_zero χ.a
  · exact wedge_basis_ne_zero χ.d
  · rw [wB_eq]; exact (toChoice χ).wedgeB_ne_zero
  · rw [wC_eq]; exact (toChoice χ).wedgeC_ne_zero
  · -- (91) for the canonical choice: `phi` is defined by it
    intro φD φC hD hC
    have hD' : φD = dualVec (canon S).wD :=
      eq_dualVec_of_apply_eq_one finrank_maxPow (wedge_basis_ne_zero _) hD
    have hC' : φC = dualVec (canon S).wC :=
      eq_dualVec_of_apply_eq_one finrank_maxPow (toChoice (canon S)).wedgeC_ne_zero hC
    rw [hD', hC']
    change S.phi S.canonicalChoice.source = S.canonicalChoice.value
    rw [FourTermExact.phi, LinearMap.smulRight_apply,
      dualVec_self FourTermExact.finrank_source S.canonicalChoice.source_ne_zero, one_smul]
  · -- (3) bijective: `Φ_E ≠ 0` (A) and both sides are lines
    exact bijective_of_ne_zero (M := maxPow A₁ ⊗[ℝ] maxPowDual D₁)
      (N := maxPow B₁ ⊗[ℝ] maxPowDual C₁) FourTermExact.finrank_source
      FourTermExact.finrank_target (hA S)

theorem B_to_A : B → A := by
  intro hB A₁ B₁ C₁ D₁ _ _ _ _ _ _ _ _ S _ _ _ _
  exact ne_zero_of_injective (M := maxPow A₁ ⊗[ℝ] maxPowDual D₁)
    (N := maxPow B₁ ⊗[ℝ] maxPowDual C₁) FourTermExact.finrank_source (hB A₁ B₁ C₁ D₁ S).2.2.1

#rt_check RoundTrip.V6_5.A_to_B [Polyfold.FourTermExact.phi_ne_zero]
#rt_check RoundTrip.V6_5.B_to_A [Polyfold.FourTermExact.phi_ne_zero]
#rt_overlap RoundTrip.V6_5.B_to_A [Polyfold.FourTermExact.phi_ne_zero]

end

end RoundTrip.V6_5
