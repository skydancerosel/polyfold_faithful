import Polyfold
/-! Blind formalization of V4_3 (the text's §1.1, after Definition 1.1, p. 6; used in
Definition 4.1).

Text: a finite-dimensional Banach space `E` has precisely one sc-structure, namely the constant
structure `E_m = E`.

Choices:
- Setting: an sc-structure on a Banach space is the project's `ScBanach` (Definition 1.1:
  levels `E_m : Type`, compact injective inclusions, `E_∞` dense in every level; checked with
  `#print`); "an sc-structure on `E`" is an `ScBanach` whose level `0` is `E`.  "Finite-dimensional"
  is `FiniteDimensional ℝ (E.lvl 0)`.
- "Precisely one": B is the conjunction of
  (uniqueness) for every `ScBanach` `E` with `E₀` finite-dimensional and every `m`, the composite
  inclusion `E_m → E₀` (`E.toBase m`) is a continuous linear equivalence, i.e. `E_m = E₀` as sets
  with equivalent norms — the sc-structure is the constant one up to equivalence of the level
  norms (in finite dimension all norms are equivalent; sc-structures are only meaningful up to
  equivalent norms);
  (existence) for every finite-dimensional normed space `V` there is an `ScBanach` all of whose
  levels are `V` (isometrically) with the identity as inclusions — the constant structure is an
  sc-structure.  I did not use the project's `ScBanach.const` in the statement, to keep the
  existence claim meaningful.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_3
open Polyfold

/-- A finite-dimensional Banach space has exactly one sc-structure, the constant one: in any
sc-structure on a finite-dimensional `E₀` every level is `E₀` (the inclusion `E_m → E₀` is a
linear homeomorphism), and the constant scale `E_m = V` is an sc-structure. -/
def B : Prop :=
  -- uniqueness: every sc-structure on a finite-dimensional space is the constant one
  (∀ E : ScBanach, FiniteDimensional ℝ (E.lvl 0) →
    ∀ m : ℕ, ∃ e : E.lvl m ≃L[ℝ] E.lvl 0, ∀ x : E.lvl m, e x = E.toBase m x) ∧
  -- existence: the constant structure `E_m = V`, inclusions the identity, is an sc-structure
  (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    ∃ (E : ScBanach) (e : ∀ m : ℕ, E.lvl m ≃ₗᵢ[ℝ] V),
      ∀ (m : ℕ) (x : E.lvl (m + 1)), e m (E.incl m x) = e (m + 1) x)

end RoundTrip.V4_3
