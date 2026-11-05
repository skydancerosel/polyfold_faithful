import Polyfold
/-! Blind formalization of V1_1 (the text's §1.1, Definition 1.1, p. 6). Choices:
- This item is a definition.  The text's notions are written here as Lean definitions from Mathlib
  alone: an sc-structure is presented as Banach spaces `X m` (`X 0` is the text's `E = E₀`) with
  continuous linear maps `ι m : X (m+1) → X m` standing for the inclusions `E_{m+1} ⊂ E_m`
  (`IsScStructure`: every `X m` complete, every `ι m` injective and a compact operator
  (Mathlib's `IsCompactOperator`), and `E_∞ = ⋂ₘ E_m ⊆ E₀` (`smoothPts`, via the composite
  inclusions `inclTo0 m : X m → X 0`) dense in every `E_m`, i.e. its preimage in `X m` is dense).
  "Decreasing" is read as `⊇` (the constant structure has equalities).  Levels live in `Type`
  (universe 0) to match the project's `ScBanach`; nothing depends on the universe.
- B is the conjunction of
  (1)/(2) the text's definition, as a characterization of the project's `ScBanach` (whose fields
      were read with `#print`): every `ScBanach` is an sc-structure in the above sense, and every
      such sc-structure is (up to level-wise continuous linear equivalences compatible with the
      inclusions) an `ScBanach`;
  (3) "a finite-dimensional space has exactly one sc-structure, the constant one": the constant
      structure `E_m = E`, `ι = id` is an sc-structure, and every sc-structure on a
      finite-dimensional `E₀` has all inclusions `E_{m+1} → E_m` continuous linear equivalences
      (so `E_m = E` with its topology: this is the constant one);
  (4) "the direct sum `E ⊕ F` has levels `E_m ⊕ F_m`": the text presupposes this is an sc-Banach
      space; claimed: `(X m × Y m, ι m × κ m)` is an sc-structure;
  (5) level shift `A^k` for `A = E`: the text presupposes that `E^k` (the space `E_k` with
      `(E^k)_m = E_{k+m}`) is an sc-Banach space (it is used so, e.g. `F¹` in Definition 1.4);
      claimed: `(X (k+m), ι (k+m))_m` is an sc-structure.
- `A_m = A ∩ E_m` and `A^k` for a general subset `A` are mere definitions (`subsetLevel`,
  `subsetShift`); "smooth"/"regularity m" are terminology.  They carry no claim.
- No project definition is used inside the text's notions; the project's `ScBanach` appears only
  in the characterization (1)/(2).  Nothing here looks false to me.
-/
namespace RoundTrip.V1_1
open Polyfold

section
variable (X : ℕ → Type) [∀ m, NormedAddCommGroup (X m)] [∀ m, NormedSpace ℝ (X m)]

/-- The composite inclusion `E_m → E₀` of the sequence presented by `ι m : E_{m+1} → E_m`. -/
def inclTo0 (ι : ∀ m, X (m + 1) →L[ℝ] X m) : ∀ m, X m →L[ℝ] X 0
  | 0 => ContinuousLinearMap.id ℝ (X 0)
  | m + 1 => (inclTo0 ι m).comp (ι m)

/-- The smooth points `E_∞ = ⋂ₘ E_m ⊆ E₀`. -/
def smoothPts (ι : ∀ m, X (m + 1) →L[ℝ] X m) : Set (X 0) :=
  ⋂ m, Set.range (inclTo0 X ι m)

/-- **Definition 1.1**: `E₀ ⊇ E₁ ⊇ ⋯` (presented by `X`, `ι`) is an sc-structure on `E = X 0`:
Banach levels, injective compact inclusions, `E_∞` dense in every `E_m`. -/
def IsScStructure (ι : ∀ m, X (m + 1) →L[ℝ] X m) : Prop :=
  (∀ m, CompleteSpace (X m)) ∧
  (∀ m, Function.Injective (ι m)) ∧
  (∀ m, IsCompactOperator (ι m)) ∧
  (∀ m, Dense (inclTo0 X ι m ⁻¹' smoothPts X ι))

/-- `A_m = A ∩ E_m` for a subset `A ⊆ E₀`, as a subset of `E_m`. -/
def subsetLevel (ι : ∀ m, X (m + 1) →L[ℝ] X m) (A : Set (X 0)) (m : ℕ) : Set (X m) :=
  inclTo0 X ι m ⁻¹' A

/-- `A^k`: the set `A_k` with the filtration `(A^k)_m = A_{k+m}` (a subset of `E_{k+m}`). -/
def subsetShift (ι : ∀ m, X (m + 1) →L[ℝ] X m) (A : Set (X 0)) (k m : ℕ) : Set (X (k + m)) :=
  subsetLevel X ι A (k + m)

end

/-- Definition 1.1: the project's `ScBanach` is exactly the text's sc-Banach space; a
finite-dimensional space has exactly the constant sc-structure; direct sums and level shifts of
sc-structures are sc-structures. -/
def B : Prop :=
  -- (1) every `ScBanach` is an sc-structure in the text's sense
  (∀ E : ScBanach, IsScStructure E.lvl E.incl) ∧
  -- (2) every sc-structure is an `ScBanach`
  (∀ (X : ℕ → Type) [∀ m, NormedAddCommGroup (X m)] [∀ m, NormedSpace ℝ (X m)]
      (ι : ∀ m, X (m + 1) →L[ℝ] X m), IsScStructure X ι →
      ∃ (E : ScBanach) (φ : ∀ m, E.lvl m ≃L[ℝ] X m),
        ∀ m (x : E.lvl (m + 1)), φ m (E.incl m x) = ι m (φ (m + 1) x)) ∧
  -- (3) finite dimension: the constant structure is an sc-structure, and it is the only one
  (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
      IsScStructure (fun _ : ℕ => V) (fun _ => ContinuousLinearMap.id ℝ V)) ∧
  (∀ (X : ℕ → Type) [∀ m, NormedAddCommGroup (X m)] [∀ m, NormedSpace ℝ (X m)]
      (ι : ∀ m, X (m + 1) →L[ℝ] X m), IsScStructure X ι → FiniteDimensional ℝ (X 0) →
      ∀ m, ∃ φ : X (m + 1) ≃L[ℝ] X m, ⇑φ = ⇑(ι m)) ∧
  -- (4) direct sums
  (∀ (X Y : ℕ → Type) [∀ m, NormedAddCommGroup (X m)] [∀ m, NormedSpace ℝ (X m)]
      [∀ m, NormedAddCommGroup (Y m)] [∀ m, NormedSpace ℝ (Y m)]
      (ι : ∀ m, X (m + 1) →L[ℝ] X m) (κ : ∀ m, Y (m + 1) →L[ℝ] Y m),
      IsScStructure X ι → IsScStructure Y κ →
      IsScStructure (fun m => X m × Y m) (fun m => (ι m).prodMap (κ m))) ∧
  -- (5) level shifts `E^k`
  (∀ (X : ℕ → Type) [∀ m, NormedAddCommGroup (X m)] [∀ m, NormedSpace ℝ (X m)]
      (ι : ∀ m, X (m + 1) →L[ℝ] X m), IsScStructure X ι →
      ∀ k : ℕ, IsScStructure (fun m => X (k + m)) (fun m => ι (k + m)))

end RoundTrip.V1_1
