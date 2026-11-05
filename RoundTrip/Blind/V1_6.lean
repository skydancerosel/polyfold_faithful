import Polyfold
/-! Blind formalization of V1_6 (the text's §1.1, Proposition 1.7, p. 8). Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by the project's `ScBanach`), `A ⊆ E₀` a
  subspace which is an sc-subspace (the project's `ScBanach.IsScSubspace`, checked with `#print`:
  closed, and `A ∩ E_∞` dense in every `A_m`; item V1_4 states that this is the text's notion).
- `A_m = A ∩ E_m` is the project's `ScBanach.levelSub A m` (checked: the preimage of `A` under
  `E_m → E₀`).  The level `E_m/A_m` is Mathlib's quotient `E_m ⧸ A_m` with its quotient topology
  (for closed `A_m` this is the topology of the quotient norm).  Its elements are the cosets
  `x + A_m = (x + A) ∩ E_m`, `x ∈ E_m`.  The text writes `{(x + A) ∩ E_m : x ∈ E}`; read
  literally (`x ∈ E = E₀`) this set also contains `∅` whenever `E_m + A ≠ E`, and is then not a
  vector space; I take `x ∈ E_m` (the intended quotient) and record the literal text as a slip.
- "`E/A` with the filtration `E_m/A_m` is an sc-Banach space": there is an sc-Banach space `Q`
  (`ScBanach`) and level-wise continuous linear equivalences `φ_m : Q_m ≃ E_m/A_m` which carry the
  inclusions `Q_{m+1} → Q_m` to the maps `x + A_{m+1} ↦ x + A_m` induced by `E_{m+1} → E_m`.  So the
  levels `E_m/A_m` (with norms equivalent to the quotient norms), sitting in `E₀/A₀ = E/A` through
  these maps, form an sc-structure on `E/A`.
- The hypothesis is the text's (`A` an sc-subspace), although only closedness seems to be needed.
-/
namespace RoundTrip.V1_6
open Polyfold

/-- The quotient of an sc-Banach space by an sc-subspace, with levels `E_m/A_m`, is an sc-Banach
space. -/
def B : Prop :=
  ∀ (E : ScBanach) (A : Submodule ℝ (E.lvl 0)), E.IsScSubspace A →
    ∃ (Q : ScBanach) (φ : ∀ m, Q.lvl m ≃L[ℝ] (E.lvl m ⧸ E.levelSub A m)),
      ∀ (m : ℕ) (x : E.lvl (m + 1)),
        φ m (Q.incl m ((φ (m + 1)).symm (Submodule.Quotient.mk x))) =
          Submodule.Quotient.mk (E.incl m x)

end RoundTrip.V1_6
