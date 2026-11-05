import Polyfold
/-! Blind formalization of V1_4 (the text's §1.1, Definition 1.5, p. 7). Choices:
- This item is a definition.  Setting: an sc-Banach space `E : ScBanach` (levels in `Type`); of
  its structure only the levels, the inclusions `E.incl m : E_{m+1} → E_m` and the composite
  inclusions `E.toBase m : E_m → E₀` are used (`toBase (m+1) = toBase m ∘ incl m` holds by `rfl`).
- The text's notions, defined here:
  * `IsScStructure` is the text's sc-structure (Definition 1.1), copied from
    `RoundTrip/Blind/V1_1.lean` (complete levels, injective compact inclusions, `⋂ E_m` dense in
    every level).
  * For a subspace `A ⊆ E₀`: `A_m = A ∩ E_m` is `lvlSub E A m` (the preimage of `A` in `E_m`, a
    subspace of `E_m` with the norm of `E_m`), with the restricted inclusions
    `subIncl E A m : A_{m+1} → A_m`.  "`A_m` defines an sc-structure on `A`" is
    `IsScStructure (lvlSub E A ·) (subIncl E A)` (`IsScStructureOn`).
  * sc-subspace: `A` closed and `IsScStructureOn A`.
  * "topological direct sum `E_m = F_m ⊕ G_m`" (`IsTopDirectSum`): the addition map
    `F_m × G_m → E_m` is a continuous linear equivalence (algebraic direct sum with continuous
    inverse, i.e. continuous projections).
  * sc-complement `G` of an sc-subspace `F`: `G` is an algebraic complement of `F` in `E₀`
    (`IsCompl F G`), `G_m = G ∩ E_m` is an sc-structure on `G` (this includes completeness of
    `G₀ = G`, i.e. `G` closed: an sc-structure lives on a Banach space), and `E_m = F_m ⊕ G_m`
    topologically on every level.  sc-splitting `E = F ⊕ G`: `F` an sc-subspace and `G` an
    sc-complement of it.
- B states the definition as a characterization of the project's `ScBanach.IsScSubspace` and
  `ScBanach.IsScSplitting` (vocabulary).  The definition asserts no further property.
-/
namespace RoundTrip.V1_4
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

/-- Definition 1.1: an sc-structure on `X 0`. -/
def IsScStructure (ι : ∀ m, X (m + 1) →L[ℝ] X m) : Prop :=
  (∀ m, CompleteSpace (X m)) ∧
  (∀ m, Function.Injective (ι m)) ∧
  (∀ m, IsCompactOperator (ι m)) ∧
  (∀ m, Dense (inclTo0 X ι m ⁻¹' smoothPts X ι))

end

/-- `A_m = A ∩ E_m`, as a subspace of `E_m`. -/
def lvlSub (E : ScBanach) (A : Submodule ℝ (E.lvl 0)) (m : ℕ) : Submodule ℝ (E.lvl m) :=
  Submodule.comap (E.toBase m : E.lvl m →ₗ[ℝ] E.lvl 0) A

/-- The inclusion `A_{m+1} → A_m`. -/
def subIncl (E : ScBanach) (A : Submodule ℝ (E.lvl 0)) (m : ℕ) :
    lvlSub E A (m + 1) →L[ℝ] lvlSub E A m :=
  ((E.incl m).comp (lvlSub E A (m + 1)).subtypeL).codRestrict (lvlSub E A m) (fun x => x.2)

/-- The filtration `A_m = A ∩ E_m` is an sc-structure on `A`. -/
def IsScStructureOn (E : ScBanach) (A : Submodule ℝ (E.lvl 0)) : Prop :=
  IsScStructure (fun m => lvlSub E A m) (subIncl E A)

/-- **Definition 1.5**: `A` is an sc-subspace of `E`. -/
def IsScSubspaceText (E : ScBanach) (A : Submodule ℝ (E.lvl 0)) : Prop :=
  IsClosed (A : Set (E.lvl 0)) ∧ IsScStructureOn E A

/-- `V = P ⊕ Q` is a topological direct sum: `(p, q) ↦ p + q` is a linear homeomorphism. -/
def IsTopDirectSum {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P Q : Submodule ℝ V) : Prop :=
  ∃ e : (P × Q) ≃L[ℝ] V, ∀ (p : P) (q : Q), e (p, q) = (p : V) + q

/-- **Definition 1.5**: `G` is an sc-complement of `F`. -/
def IsScComplementText (E : ScBanach) (F G : Submodule ℝ (E.lvl 0)) : Prop :=
  IsCompl F G ∧ IsScStructureOn E G ∧ ∀ m, IsTopDirectSum (lvlSub E F m) (lvlSub E G m)

/-- **Definition 1.5**: `F` has an sc-complement. -/
def HasScComplementText (E : ScBanach) (F : Submodule ℝ (E.lvl 0)) : Prop :=
  ∃ G, IsScComplementText E F G

/-- **Definition 1.5**: `E = F ⊕ G` is an sc-splitting. -/
def IsScSplittingText (E : ScBanach) (F G : Submodule ℝ (E.lvl 0)) : Prop :=
  IsScSubspaceText E F ∧ IsScComplementText E F G

/-- Definition 1.5: the project's sc-subspaces and sc-splittings are the text's. -/
def B : Prop :=
  (∀ (E : ScBanach) (A : Submodule ℝ (E.lvl 0)), E.IsScSubspace A ↔ IsScSubspaceText E A) ∧
  (∀ (E : ScBanach) (F G : Submodule ℝ (E.lvl 0)),
    E.IsScSplitting F G ↔ IsScSplittingText E F G)

end RoundTrip.V1_4
