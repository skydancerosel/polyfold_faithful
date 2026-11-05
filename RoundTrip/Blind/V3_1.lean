import Polyfold
/-! Blind formalization of V3_1 (the text's §3.1, Definition 3.1, p. 62). Choices:
- This item is a definition plus properties.  Setting: `E : ScBanach` (the project's sc-Banach
  space, Definition 1.1, audited in V1_1; levels in `Type`, forced by `ScBanach`), `C ⊆ E₀` a
  partial quadrant (`IsPartialQuadrant`, Definition 1.11).  No universe choices arise.
- A sequence `U₀ ⊃ U₁ ⊃ ⋯` is presented level-wise: `U m ⊆ E_m` (a subset of the level type).
  "Decreasing" is read along the inclusions: `ι_m(U_{m+1}) ⊆ U_m`.  `C_m = C ∩ E_m` is the
  preimage of `C` under the composite inclusion `E_m → E₀` (`levelB`).  "`U_m` a relatively open
  neighbourhood of `0` in `C_m`": `U_m = O ∩ C_m` with `O` open in `E_m` (level-`m` topology), and
  `0 ∈ U_m`.  My definition: `IsScGermB E C U`.
- The tangent: `TE = E¹ ⊕ E` (`TEB E = E.shift.prod E`, levels `E_{m+1} × E_m`),
  `TC = C¹ ⊕ E` (`TCB`, the `(x, h) ∈ E₁ × E₀` with `x ∈ C`), and
  `TO(C, 0) = (U_{m+1} ⊕ E_m)_m` (`TUB U`).  The text presupposes that this is again an sc-germ of
  neighbourhoods (around `0` in `TC`, it is used so in Definition 3.2); B asserts it.  (That `TC`
  is a partial quadrant of `TE` belongs to Definition 1.13 and is not claimed here.)
- The example: for `U` relatively open in `C` (`U = O ∩ C`, `O` open in `E₀`) with `0 ∈ U`, the
  sequence `U_m = U ∩ E_m` (`ofSetB`) is an sc-germ of neighbourhoods; B asserts it.
- "the size of the sets `U_m` does not matter" is an informal remark (it concerns how germ notions
  are used later); it is not formalized.
- Characterization of the project's notions: every `ScNbhdGerm E C` has levels satisfying
  `IsScGermB`, every sequence satisfying `IsScGermB` is the levels of some `ScNbhdGerm E C`, the
  project's `ScNbhdGerm.tangent` has levels `TUB` and base set `E.tangentSet C = TCB E C`, and
  `ScNbhdGerm.ofSet` has levels `ofSetB`.  (I read the field list of `ScNbhdGerm` with `#print`.)
- Nothing looks false to me.
-/
namespace RoundTrip.V3_1
open Polyfold

/-- `C_m = C ∩ E_m`, as a subset of `E_m`. -/
def levelB (E : ScBanach) (C : Set (E.lvl 0)) (m : ℕ) : Set (E.lvl m) :=
  E.toBase m ⁻¹' C

/-- **Definition 3.1**: `(U_m)_m`, `U_m ⊆ E_m`, is an sc-germ of neighbourhoods `O(C, 0)`: a
decreasing sequence of relatively open neighbourhoods `U_m` of `0` in `C_m`. -/
def IsScGermB (E : ScBanach) (C : Set (E.lvl 0)) (U : ∀ m, Set (E.lvl m)) : Prop :=
  -- decreasing: `U_{m+1} ⊆ U_m`
  (∀ m, ∀ x ∈ U (m + 1), E.incl m x ∈ U m) ∧
  -- `U_m` relatively open in `C_m`
  (∀ m, ∃ O : Set (E.lvl m), IsOpen O ∧ U m = O ∩ levelB E C m) ∧
  -- `0 ∈ U_m`
  (∀ m, (0 : E.lvl m) ∈ U m)

/-- `TE = E¹ ⊕ E`. -/
noncomputable abbrev TEB (E : ScBanach) : ScBanach := E.shift.prod E

/-- `TC = C¹ ⊕ E ⊆ (TE)₀ = E₁ × E₀`. -/
def TCB (E : ScBanach) (C : Set (E.lvl 0)) : Set ((TEB E).lvl 0) :=
  {p | E.toBase 1 p.1 ∈ C}

/-- The tangent germ `TO(C, 0)`: `(TO)_m = U_{m+1} ⊕ E_m`. -/
def TUB {E : ScBanach} (U : ∀ m, Set (E.lvl m)) : ∀ m, Set ((TEB E).lvl m) :=
  fun m => {p | p.1 ∈ U (m + 1)}

/-- The example `U_m = U ∩ E_m`. -/
def ofSetB (E : ScBanach) (U : Set (E.lvl 0)) : ∀ m, Set (E.lvl m) :=
  fun m => E.toBase m ⁻¹' U

/-- Definition 3.1: the project's `ScNbhdGerm` is the text's sc-germ of neighbourhoods; its tangent
`(U_{m+1} ⊕ E_m)_m` is an sc-germ of neighbourhoods around `0` in `TC` (and is the project's
tangent); a relatively open `U ∋ 0` with `U_m = U ∩ E_m` is an example (the project's `ofSet`). -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)), IsPartialQuadrant E C →
    -- the project's germs are the text's
    (∀ G : ScNbhdGerm E C, IsScGermB E C G.U) ∧
    (∀ U : ∀ m, Set (E.lvl m), IsScGermB E C U → ∃ G : ScNbhdGerm E C, G.U = U) ∧
    -- the tangent `TO(C, 0)` is an sc-germ of neighbourhoods around `0` in `TC`
    (∀ U : ∀ m, Set (E.lvl m), IsScGermB E C U → IsScGermB (TEB E) (TCB E C) (TUB U)) ∧
    -- the project's tangent germ is `TO(C, 0)`, around `0` in `TC`
    (E.tangentSet C = TCB E C ∧ ∀ G : ScNbhdGerm E C, G.tangent.U = TUB G.U) ∧
    -- the example `U_m = U ∩ E_m`
    (∀ U : Set (E.lvl 0), (∃ O : Set (E.lvl 0), IsOpen O ∧ U = O ∩ C) → 0 ∈ U →
      IsScGermB E C (ofSetB E U)) ∧
    (∀ (U : Set (E.lvl 0)) (hU : ∃ O : Set (E.lvl 0), IsOpen O ∧ U = O ∩ C) (h0 : 0 ∈ U),
      (ScNbhdGerm.ofSet hU h0 : ScNbhdGerm E C).U = ofSetB E U)

end RoundTrip.V3_1
