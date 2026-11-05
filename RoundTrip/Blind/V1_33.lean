import Polyfold
/-! Blind formalization of V1_33 (the text's §1.1, proof of Proposition 1.7, p. 9).

Text (in the proof): "`(E/A)_∞ = ⋂_j (E_j/A_j)` consists of all elements of the form
`x + A_∞` with `x ∈ E_∞`."

Choices:
- Setting: `E : ScBanach` (the project's sc-Banach space, levels in `Type`; checked with `#print`
  to be Definition 1.1), `A ⊆ E₀` a linear subspace.  Hypothesis on `A`: the item does not quote
  the hypothesis of Proposition 1.7; I take the one I recall from the text, "`A` an sc-subspace of
  `E`" (Definition 1.5), written by hand as `IsScSubspaceText` (same prelude as
  `RoundTrip/Blind/V1_32.lean`: `A` closed, every `A_m = A ∩ E_m` complete, compact inclusions
  `A_{m+1} → A_m`, `A_∞ = A ∩ E_∞` dense in every `A_m`).  WARNING: for `A` merely closed
  the claim is false (the project's `ScBanach.quotient` takes only `IsClosed A`).  Sketch: take a
  scale with disjointly supported `v_k ∈ E_k \ E_{k+1}` orthonormal in `E₀`, `u_k = 2^k v_k`, and
  `A = {Σ r_k v_k ∈ closed span(v_k) : Σ r_k 2^{-k} = 0}` (closed: kernel of a bounded
  functional); then `u₀ + A ∋ u_k ∈ E_k` for every `k`, but `(u₀ + A) ∩ E_∞ = ∅`.  With `A_∞`
  dense in every `A_m` the claim holds (successive corrections by elements of `A_∞`).
- `E/A` is `E₀ ⧸ A`; `E_j/A_j` is `E_j ⧸ A_j` (`A_j = E.levelSub A j`, the preimage of `A` in
  `E_j`), viewed inside `E/A` through the map induced by the inclusion `E_j → E₀` (it is
  injective since `A_j = A ∩ E_j`; that identification is presupposed by the text, not claimed
  here).  `(E/A)_∞ = ⋂_j (E_j/A_j)` is `quotSmooth`, the intersection of the images.
- "consists of all elements of the form `x + A_∞` with `x ∈ E_∞`": the map
  `E_∞/A_∞ → E/A`, `x + A_∞ ↦ x + A` (`A_∞ = A ∩ E_∞` as a subspace of `E_∞ = E.smooth`) has
  image exactly `(E/A)_∞`, and it is injective (so `(E/A)_∞` is `E_∞/A_∞`; injectivity is
  elementary but part of "consists of the elements `x + A_∞`").
- Project definitions used: `ScBanach`, `ScScale.toBase`, `ScScale.smooth` (`E_∞`, checked:
  `⨅ m, range (toBase m)`), `ScBanach.levelSub` (checked: `comap (toBase m) A`).
-/
namespace RoundTrip.V1_33
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

/-- The map `E_j/A_j → E/A = E₀/A` induced by the inclusion `E_j → E₀`. -/
def quotLevelMap (E : ScBanach) (A : Submodule ℝ (E.lvl 0)) (j : ℕ) :
    (E.lvl j ⧸ E.levelSub A j) →ₗ[ℝ] (E.lvl 0 ⧸ A) :=
  Submodule.mapQ (E.levelSub A j) A (E.toBase j : E.lvl j →ₗ[ℝ] E.lvl 0) le_rfl

/-- `(E/A)_∞ = ⋂_j (E_j/A_j)`, each `E_j/A_j` seen inside `E/A`. -/
def quotSmooth (E : ScBanach) (A : Submodule ℝ (E.lvl 0)) : Set (E.lvl 0 ⧸ A) :=
  ⋂ j : ℕ, Set.range (quotLevelMap E A j)

/-- `A_∞ = A ∩ E_∞`, as a subspace of `E_∞`. -/
def smoothSub (E : ScBanach) (A : Submodule ℝ (E.lvl 0)) : Submodule ℝ E.smooth :=
  A.comap E.smooth.subtype

/-- `E_∞/A_∞ → E/A`, `x + A_∞ ↦ x + A`. -/
def smoothQuotMap (E : ScBanach) (A : Submodule ℝ (E.lvl 0)) :
    (E.smooth ⧸ smoothSub E A) →ₗ[ℝ] (E.lvl 0 ⧸ A) :=
  Submodule.mapQ (smoothSub E A) A E.smooth.subtype le_rfl

/-- For an sc-subspace `A`, `(E/A)_∞ = ⋂_j (E_j/A_j)` consists exactly of the classes
`x + A_∞`, `x ∈ E_∞` (distinct classes giving distinct elements). -/
def B : Prop :=
  ∀ (E : ScBanach) (A : Submodule ℝ (E.lvl 0)), IsScSubspaceText E A →
    Set.range (smoothQuotMap E A) = quotSmooth E A ∧ Function.Injective (smoothQuotMap E A)

end RoundTrip.V1_33
