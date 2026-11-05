import Polyfold
/-! Blind formalization of V1_32 (the text's §1.1, Definition 1.5 and the proof of
Proposition 1.6, pp. 7–8).

Text: an sc-splitting `E = F ⊕ G` is a topological direct sum `E_m = F_m ⊕ G_m` on every level.
In the proof of Proposition 1.6: the map `P` with `P ∘ P = P`, continuous on every `E_m`, "is a
sc-projection", and `G := (1 − P)(E)` is then an sc-complement.

Choices:
- Setting: `E : ScBanach` (the project's sc-Banach space, levels in `Type`; checked with `#print`
  to be Definition 1.1).  Only its bare structure is used: levels `E.lvl m`, inclusions
  `E.incl m`, composite inclusions `E.toBase m : E_m → E₀`, `E.smooth = E_∞ ⊆ E₀`, and
  `E.levelSub A m = A_m = A ∩ E_m` (the preimage of `A` in `E_m`, a subspace of `E_m` with the
  norm of `E_m`).
- The text's notions, defined here by hand (Definition 1.5):
  * `IsScSubspaceText E A`: `A ⊆ E₀` a closed linear subspace such that `A_m = A ∩ E_m` is an
    sc-structure on `A`: every `A_m` complete (in the norm of `E_m`), the inclusions
    `A_{m+1} → A_m` compact operators, and `A_∞ = A ∩ E_∞` dense in every `A_m`.  (Completeness
    and compactness are automatic, but they are part of "defines an sc-structure", so stated.)
  * `TopDirectSum A B` (in a normed space `V`): `V = A ⊕ B` as a topological direct sum: the sum
    map `A × B → V`, `(a, b) ↦ a + b`, is a continuous linear equivalence.
  * `IsScSplittingText E F G`: `F`, `G` sc-subspaces and `E_m = F_m ⊕ G_m` topologically for
    every `m` (`G` is then an sc-complement of `F`).
  * `IsScOperatorText E P` for a linear `P : E₀ → E₀`: `P` maps every `E_m` into `E_m` with
    continuous restriction ("continuous on every `E_m`"; this presupposes `P(E_m) ⊆ E_m`, which in
    the proof holds because `P` has range in `E_∞`).
  * `IsScProjectionText E P`: an sc-operator with `P ∘ P = P` (my reading of "sc-projection").
- B is the conjunction of
  (1) the definition, as a characterization of the project's `ScBanach.IsScSplitting` (whose
      body, read with `#print`, asks only for an algebraic `IsCompl` on every level): it is
      equivalent to the text's topological sc-splitting;
  (2) the claim of the proof of Proposition 1.6, in the generality of its hypotheses: for every
      linear `P : E₀ → E₀` with `P ∘ P = P` that is continuous on every `E_m`, `P` is an
      sc-projection and `E = P(E) ⊕ (1 − P)(E)` is an sc-splitting, i.e. `(1 − P)(E)` is an
      sc-complement of `P(E)` (in the proof `P(E) = F` is the given finite-dimensional
      subspace of `E_∞`; the claim about `P` and `G` uses only `P² = P` and the level
      continuity, so it is stated for every such `P`, and `F` is written `P(E)`).
  The "is a sc-projection" part is a restatement of the hypotheses under my reading.
- Nothing looks false.
-/
namespace RoundTrip.V1_32
open Polyfold

/-- The inclusion `A_{m+1} → A_m` (restriction of `E_{m+1} → E_m`). -/
def subIncl (E : ScBanach) (A : Submodule ℝ (E.lvl 0)) (m : ℕ) :
    E.levelSub A (m + 1) → E.levelSub A m :=
  fun x => ⟨E.incl m x, x.2⟩

/-- **Definition 1.5**: `A` is an sc-subspace: closed, and `A_m = A ∩ E_m` is an sc-structure
on `A` (complete levels, compact inclusions, `A_∞ = A ∩ E_∞` dense in every `A_m`). -/
def IsScSubspaceText (E : ScBanach) (A : Submodule ℝ (E.lvl 0)) : Prop :=
  IsClosed (A : Set (E.lvl 0)) ∧
  (∀ m, CompleteSpace (E.levelSub A m)) ∧
  (∀ m, IsCompactOperator (subIncl E A m)) ∧
  (∀ m, Dense {x : E.levelSub A m | E.toBase m (x : E.lvl m) ∈ E.smooth})

/-- `V = A ⊕ B` is a topological direct sum: `(a, b) ↦ a + b` is a continuous linear
equivalence `A × B ≃ V`. -/
def TopDirectSum {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B : Submodule ℝ V) : Prop :=
  ∃ e : (A × B) ≃L[ℝ] V, ∀ p : A × B, e p = (p.1 : V) + (p.2 : V)

/-- **Definition 1.5**: `E = F ⊕ G` is an sc-splitting: `F`, `G` sc-subspaces with
`E_m = F_m ⊕ G_m` a topological direct sum on every level. -/
def IsScSplittingText (E : ScBanach) (F G : Submodule ℝ (E.lvl 0)) : Prop :=
  IsScSubspaceText E F ∧ IsScSubspaceText E G ∧
  ∀ m, TopDirectSum (E.levelSub F m) (E.levelSub G m)

/-- A linear `P : E₀ → E₀` maps every `E_m` into `E_m`, continuously. -/
def IsScOperatorText (E : ScBanach) (P : E.lvl 0 →ₗ[ℝ] E.lvl 0) : Prop :=
  ∀ m : ℕ, ∃ Pm : E.lvl m → E.lvl m,
    (∀ x, E.toBase m (Pm x) = P (E.toBase m x)) ∧ Continuous Pm

/-- An sc-projection: an sc-operator `P` with `P ∘ P = P`. -/
def IsScProjectionText (E : ScBanach) (P : E.lvl 0 →ₗ[ℝ] E.lvl 0) : Prop :=
  IsScOperatorText E P ∧ P ∘ₗ P = P

/-- Definition 1.5 (the project's sc-splittings are the text's topological ones) and the
proof of Proposition 1.6 (an idempotent continuous on every level is an sc-projection, and
`(1 − P)(E)` is an sc-complement of `P(E)`). -/
def B : Prop :=
  (∀ (E : ScBanach) (F G : Submodule ℝ (E.lvl 0)),
    E.IsScSplitting F G ↔ IsScSplittingText E F G) ∧
  (∀ (E : ScBanach) (P : E.lvl 0 →ₗ[ℝ] E.lvl 0), IsScOperatorText E P → P ∘ₗ P = P →
    IsScProjectionText E P ∧
    IsScSplittingText E (LinearMap.range P) (LinearMap.range (LinearMap.id - P)))

end RoundTrip.V1_32
