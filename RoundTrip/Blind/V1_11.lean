import Polyfold
/-! Blind formalization of V1_11 (the text's §1.1, Definition 1.12, p. 10). Choices:
- This item is a definition.  Setting: sc-Banach spaces `E F : ScBanach` (levels in `Type`) and
  tuples `(U, C, E)`, `(U', C', F)` in the sense of Definition 1.11, written out by hand
  (`IsRelOpenText`, the prelude of `RoundTrip/Blind/V1_10.lean`: `C` closed convex with an
  sc-isomorphism `E ≅ ℝⁿ ⊕ W` taking it to `[0,∞)ⁿ ⊕ W`, `U ⊆ C` open in `C`).
- The map `f : U → U'` is a function `f : E₀ → F₀` with `f(U) ⊆ U'`; only its values on `U` enter.
- `U_m = U ∩ E_m` is `lvlSetText E U m`, the preimage of `U` under the inclusion
  `E.toBase m : E_m → E₀`, with the topology of `E_m`.
- `IsSc0Text` (Definition 1.12): for every `m` there is `f_m : E_m → F_m` mapping `U_m` into
  `U'_m`, lying over `f` on `U_m` (`ι_m ∘ f_m = f ∘ ι_m` there, so `f_m` is the induced map, unique
  on `U_m` since `ι_m` is injective; this contains `f(U_m) ⊆ U'_m`), and continuous on `U_m`.
- B states the definition as a characterization of the project's `IsSc0 E F U f` (vocabulary:
  "`f : U → F` is sc⁰"; its target is `F`, so the comparison is made for maps with `f(U) ⊆ U'`),
  for all tuples.  The definition asserts no further property.
-/
namespace RoundTrip.V1_11
open Polyfold

/-- `C` is a partial quadrant in `E` (Definition 1.11). -/
def IsPartialQuadrantText (E : ScBanach) (C : Set (E.lvl 0)) : Prop :=
  IsClosed C ∧ Convex ℝ C ∧
    ∃ (n : ℕ) (W : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)),
      (T.lvl 0) '' C = {p | ∀ i, 0 ≤ p.1 i}

/-- The tuple `(U, C, E)`: `U` is a relatively open subset of the partial quadrant `C` in `E`. -/
def IsRelOpenText (E : ScBanach) (C U : Set (E.lvl 0)) : Prop :=
  IsPartialQuadrantText E C ∧ U ⊆ C ∧ IsOpen (Subtype.val ⁻¹' U : Set C)

/-- `U_m = U ∩ E_m`, as a subset of `E_m`. -/
def lvlSetText (E : ScBanach) (U : Set (E.lvl 0)) (m : ℕ) : Set (E.lvl m) :=
  E.toBase m ⁻¹' U

/-- **Definition 1.12**: `f : U → U'` is sc⁰: `f(U_m) ⊆ U'_m` and the induced map
`U_m → U'_m` is continuous, for every `m`. -/
def IsSc0Text (E F : ScBanach) (U : Set (E.lvl 0)) (U' : Set (F.lvl 0))
    (f : E.lvl 0 → F.lvl 0) : Prop :=
  ∀ m : ℕ, ∃ fm : E.lvl m → F.lvl m,
    Set.MapsTo fm (lvlSetText E U m) (lvlSetText F U' m) ∧
    (∀ x ∈ lvlSetText E U m, F.toBase m (fm x) = f (E.toBase m x)) ∧
    ContinuousOn fm (lvlSetText E U m)

/-- Definition 1.12: for maps `f : U → U'` between tuples, the project's `IsSc0` is the text's
sc⁰. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (C' U' : Set (F.lvl 0)) (f : E.lvl 0 → F.lvl 0),
    IsRelOpenText E C U → IsRelOpenText F C' U' → Set.MapsTo f U U' →
      (IsSc0 E F U f ↔ IsSc0Text E F U U' f)

end RoundTrip.V1_11
