import Polyfold
/-! Blind formalization of V2_31 (the text's §2.3, p. 32: the subspaces `E_x` and
`dim(E/E_x) = d_C(x)`).

Text: for `C = [0, ∞)^k ⊕ W` (in `E = ℝ^k ⊕ W`): `E_i = {a_i = 0}`, `E_I = ⋂_{i ∈ I} E_i`,
`I(x) = {i : x ∈ E_i}`, `E_x = E_{I(x)}`, `H_i = {a_i ≥ 0}` and `C_x = ⋂_{i ∈ I(x)} H_i`; and (the
item's title) `dim(E/E_x) = d_C(x)`.

Choices:
- This item is a definition plus a property.  Setting: `k : ℕ`, `W : ScBanach` (levels in `Type`,
  forced by `ScBanach`), `E = ℝ^k ⊕ W` the project's `(ScBanach.const (Fin k → ℝ)).prod W`
  (`EB k W`), whose level 0 is `(Fin k → ℝ) × W₀` (checked by `rfl`); `C = [0,∞)^k ⊕ W` is the
  project's `quadrant k W 0` (checked with `#print`: `{p | ∀ i, 0 ≤ p.1 i}`).  The text's
  indices `1, …, k` are `Fin k`.  All sets live in level 0 (`E = E₀` as a vector space).
- My definitions: `EiB i = ker (a ↦ a_i)` (a submodule), `EIB I = ⨅_{i ∈ I} E_i` (`E_∅ = E`),
  `IxB x = {i | x ∈ E_i}`, `ExB x = E_{I(x)}`, `HiB i = {a | 0 ≤ a_i}`,
  `CxB x = ⋂_{i ∈ I(x)} H_i`.
- The property `dim(E/E_x) = d_C(x)` is asserted for `x ∈ C` (where `d_C` is defined), as
  `Module.rank ℝ (E₀ ⧸ E_x) = d_C(x)` (cardinal rank, so an infinite dimension is not mistaken for
  `0`).  `d_C` is the project's `degIndex E C` (Definition 1.23, checked with `#print`: the number
  of vanishing `[0,∞)`-coordinates of `T x` for a chosen presentation `T` of `C`; for the standard
  quadrant this is `#{i | x_i = 0}` by Lemma 1.24).
- The project's general versions for a partial quadrant presented by an sc-isomorphism
  `T : E ≅ ℝⁿ ⊕ W` are `minimalSubspaceWith T x` (`E_x`) and `partialQuadrantAtWith T x` (`C_x`,
  the project's docstring cites Definition 2.33).  The text reduces a general partial quadrant to
  the standard one ("`C = [0,∞)^k ⊕ W`"), so the general notions are the transports
  `T⁻¹(E_{Tx})`, `T⁻¹(C_{Tx})`; B asserts that the project's definitions are these, for every
  presentation `T` and every `x ∈ E₀` (the definitions make sense off `C`).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_31
open Polyfold

/-- The standard sc-Banach space `ℝ^k ⊕ W`. -/
noncomputable abbrev EB (k : ℕ) (W : ScBanach) : ScBanach := (ScBanach.const (Fin k → ℝ)).prod W

variable {k : ℕ} {W : ScBanach}

/-- The coordinate `a ↦ a_i` on `(ℝ^k ⊕ W)₀`. -/
noncomputable def coordB (i : Fin k) : (EB k W).lvl 0 →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i ∘L ContinuousLinearMap.fst ℝ (Fin k → ℝ) (W.lvl 0)

/-- `E_i = {a | a_i = 0}`. -/
noncomputable def EiB (i : Fin k) : Submodule ℝ ((EB k W).lvl 0) :=
  LinearMap.ker (coordB (W := W) i : (EB k W).lvl 0 →ₗ[ℝ] ℝ)

/-- `E_I = ⋂_{i ∈ I} E_i`. -/
noncomputable def EIB (I : Set (Fin k)) : Submodule ℝ ((EB k W).lvl 0) :=
  ⨅ i ∈ I, EiB (W := W) i

/-- `I(x) = {i | x ∈ E_i}`. -/
def IxB (x : (EB k W).lvl 0) : Set (Fin k) :=
  {i | x ∈ EiB (W := W) i}

/-- `E_x = E_{I(x)}`. -/
noncomputable def ExB (x : (EB k W).lvl 0) : Submodule ℝ ((EB k W).lvl 0) :=
  EIB (W := W) (IxB x)

/-- `H_i = {a | a_i ≥ 0}`. -/
def HiB (i : Fin k) : Set ((EB k W).lvl 0) :=
  {a | 0 ≤ coordB (W := W) i a}

/-- `C_x = ⋂_{i ∈ I(x)} H_i`. -/
def CxB (x : (EB k W).lvl 0) : Set ((EB k W).lvl 0) :=
  ⋂ i ∈ IxB x, HiB (W := W) i

/-- The subspaces `E_x`, the cones `C_x`, and `dim(E/E_x) = d_C(x)`; the project's `E_x`, `C_x`
for a presented partial quadrant are the transports of the text's. -/
def B : Prop :=
  -- `dim(E/E_x) = d_C(x)` for `x ∈ C = [0,∞)^k ⊕ W`
  (∀ (k : ℕ) (W : ScBanach) (x : (EB k W).lvl 0), x ∈ quadrant k W 0 →
    Module.rank ℝ ((EB k W).lvl 0 ⧸ ExB x) = (degIndex (EB k W) (quadrant k W 0) x : Cardinal)) ∧
  -- the project's `E_x` and `C_x` for a presentation `T : E ≅ ℝⁿ ⊕ W`
  (∀ (E : ScBanach) (n : ℕ) (W : ScBanach) (T : ScIso E (EB n W)) (x : E.lvl 0),
    (minimalSubspaceWith T x : Set (E.lvl 0)) = T.lvl 0 ⁻¹' (ExB (T.lvl 0 x) : Set _) ∧
    partialQuadrantAtWith T x = T.lvl 0 ⁻¹' CxB (T.lvl 0 x))

end RoundTrip.V2_31
