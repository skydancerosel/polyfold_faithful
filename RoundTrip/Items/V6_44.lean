import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_44

/-! Round trip for V6_44 (Proposition 6.32: the push-forward does not depend on the choices).

A is the conjunction of the types of the item's theorems (`proposition_6_32` and its helpers
`IsStabKernels.congr_data`, `push_congr_data`, `push_eq_of_prefix`, `isZeroAt_sectionAdd_combo`,
`linAt_principal_combo`, `continuous_principal_pullbackSlice`), universes at `0`.

**No direction is proved.**

* The two statements are about different push-forwards.  The project's `IsStabKernels.push`
  (through `IsPush`) is `orEquivRay⁻¹ ∘ α(T₁) ∘ propagate ∘ α(T₀) ∘ orEquivRay` with
  `α(T) = stabSign T = (−1)^{dim coker T}`; B's `Facts.push` is the text's map read literally,
  `orEquivRay⁻¹ ∘ propagate ∘ orEquivRay`, with no sign.  For the same data the two differ by the
  factor `α(T₀) α(T₁)`, which depends on the choice of `s` through `T_t = (f − s(·, t))'(φ(t))`.
* B does not hold as we read it (not formalized here).  Since the signed push-forward is
  independent of the choices (A), B is equivalent to: the parity of
  `dim coker T₀ + dim coker T₁` does not depend on the choices.  It does: take `X = ℝ`
  (`rnPolyfold 1`), the trivial bundle `ℝ × ℝ → ℝ` (`TrivialBundle.bundle 1 1`, tame,
  boundaryless), `f(y) = y` (sc-Fredholm, zero set `{0}` compact; `X` is contractible and has
  sc⁺-sections through every point and along every path, so `IsGoodNbhd` holds), `φ ≡ 0`, one
  added section `s₁ ≡ 1`, and the two choices `s(y, t) = 0` and `s'(y, t) = t·y`.  Both satisfy
  (P) (`F_t(λ, y) = (1 − c t) y + λ`, `c ∈ {0, 1}`, has onto linearization and no boundary).
  Then `T_t = 1` (coker `0` at both ends, `α α = +1`) and `T'_t = 1 − t` (coker `0` at `t = 0`,
  `1` at `t = 1`, `α α = −1`), so `Facts.push` of the second choice is minus that of the first
  (`−o ≠ o` on the two-element set `Or^f_0`).  The linear-algebra core is the project's
  `StabCounterexample` / `not_isLineOrientation_stabRay_uncorrected` (the rays `Φ_E(o(T_q))` of
  formula (94) jump where `dim coker T_q` does).  A formal `not_B` would need the full instance
  (sc⁺-sections of `π*P` over `ℝ × ℝ`, slice general position, a continuous kernel family and the
  computation of the end-point cokernels); it was not attempted within the budget.
* So `A ⇒ B` is false.  Even with the sign inserted in B, `A ⇒ B` would need glue that is not
  available: `proposition_6_32` assumes `B.IsScFredholmSectionTame f` (B: `IsScFredholmSection`)
  and `PX.AdmitsBumpFunctions` (B: only `IsGoodNbhd`), and an `IsPush` datum asks
  `(f + S)(t, γ t) = 0` for `t` in a neighbourhood of `[0, 1]` (B's `s_eq`: only on `[0, 1]`).
  Conversely B's (P) and `IsGoodNbhd` are not needed by A.
* `B ⇒ A` holds only vacuously (B is false); it is not proved.
-/

namespace RoundTrip.V6_44
open Polyfold

/-- The project's statement: the theorems of the item, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.IsStabKernels.congr_data.{0, 0, 0} ∧
  type_of% @Polyfold.IsStabKernels.push_congr_data.{0, 0, 0} ∧
  type_of% @Polyfold.IsStabKernels.push_eq_of_prefix.{0, 0, 0} ∧
  type_of% @Polyfold.isZeroAt_sectionAdd_combo.{0, 0} ∧
  type_of% @Polyfold.linAt_principal_combo.{0, 0} ∧
  type_of% @Polyfold.continuous_principal_pullbackSlice.{0, 0} ∧
  type_of% @Polyfold.proposition_6_32.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.IsStabKernels.congr_data.{0, 0, 0}, @Polyfold.IsStabKernels.push_congr_data.{0, 0, 0},
    @Polyfold.IsStabKernels.push_eq_of_prefix.{0, 0, 0}, @Polyfold.isZeroAt_sectionAdd_combo.{0, 0},
    @Polyfold.linAt_principal_combo.{0, 0}, @Polyfold.continuous_principal_pullbackSlice.{0, 0},
    @Polyfold.proposition_6_32.{0, 0}⟩

/-- The sign by which B's push-forward and the project's differ at an end-point operator `T`:
`α(T) = (−1)^{dim coker T}`, `+1` for the identity of `ℝ`, `−1` for the zero map of `ℝ`
(the end-point operators `T'₀ = 1`, `T'₁ = 0` of the second choice above). -/
example : stabSign (ContinuousLinearMap.id ℝ ℝ) = 1 := by
  have : Subsingleton (ℝ ⧸ LinearMap.range ((ContinuousLinearMap.id ℝ ℝ : ℝ →L[ℝ] ℝ) :
      ℝ →ₗ[ℝ] ℝ)) :=
    Submodule.Quotient.subsingleton_iff.2 (LinearMap.range_eq_top.2 fun y => ⟨y, rfl⟩)
  rw [stabSign, Module.finrank_zero_of_subsingleton, pow_zero]

example : stabSign (0 : ℝ →L[ℝ] ℝ) = -1 := by
  have h : LinearMap.range ((0 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = ⊥ := by
    ext y; simp
  rw [stabSign, h, (Submodule.quotEquivOfEqBot ⊥ rfl).finrank_eq, Module.finrank_self, pow_one]

end RoundTrip.V6_44
