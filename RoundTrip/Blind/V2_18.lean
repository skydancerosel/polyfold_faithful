import Polyfold
/-! Blind formalization of V2_18 (the text's §2.2, Definition 2.17, pp. 25–26).

Text: for `x ∈ O_1`, `T_xO = p⁻¹(x)`, the image of `Dr(x)`.  Tuples `(x, V, φ, (O, C, E), h)`
with `x ∈ X_1`, `φ` a chart around `x` and `h ∈ T_{φ(x)}O` are equivalent,
`(x, φ, h) ∼ (x', ψ, h')`, if `x = x'` and `T(φ ∘ ψ⁻¹)(ψ(x))h' = h`.

Choices:
- This item is a definition (plus the presupposed fact that `∼` is an equivalence relation, which
  the text uses when it takes classes in Definition 2.18; I include it).
- Retracts (first part): `E : ScBanach` (levels in `Type`, forced), `(O, C, E)` an sc-smooth
  retract (`IsScRetract`, checked in `RoundTrip/Blind/V2_2.lean`), "retraction `r` onto `O`":
  `R : ScRetraction E C` with `R.retract = O`.  `TO = {(r(x), Dr(x)h) : x ∈ U₁, h ∈ E}`
  (`TOB R`, Definition 2.5 as in `RoundTrip/Blind/V2_4.lean`; `Dr` is `scDeriv`, unique on
  `U₁`), `p : TO → O_1` the first projection, so `p⁻¹(x) = {h | (x, h) ∈ TO}` (`TxOB R x₁`, `x`
  given by its level-1 point `x₁`).  As `T_xO` does not depend on `r`, the claims are made for
  EVERY retraction onto `O`; B also says the project's `tangentSpace E C O x₁` is this set.
- M-polyfold part: `X : Type` (spaces in `Type`; the project's `MPolyfold` is
  universe-polymorphic, this is `u = 0`) with `[TopologicalSpace X] [T2Space X]
  [ParacompactSpace X]`, `P : MPolyfold X` (Definition 2.13).  "Chart around `x`": `MChart X`
  with `P.IsChart φ` (maximal atlas, checked with `#print`) and `x ∈ φ.source`.  `X_1` is
  `levelSetB P 1` (as in my `RoundTrip/Blind/V2_14.lean`).  The tuple's chart carries its domain
  `V = φ.source` and model `(O, C, E) = φ.model`.
- `IsTupleB P x φ h`: `x ∈ X_1`, `φ` a chart around `x`, and `h ∈ T_{φ(x)}O`: `φ(x) = ι₁ x₁` for
  some `x₁ ∈ E_1` and `h ∈ TxOB R x₁` for every retraction `R` onto `O`.  B says the project's
  tuples `P.TangentPre` (fields checked with `#print`) are exactly these data: every `TangentPre`
  satisfies `IsTupleB`, and every such datum is (the fields of) a `TangentPre` (with `HEq` for
  `h`, whose type depends on the chart).
- `RelB p q` for `p = (x, φ, h)`, `q = (x', ψ, h')`: `x = x'` and `T(φ ∘ ψ⁻¹)(ψ(x))h' = h`, where
  `φ ∘ ψ⁻¹ : ψ(V' ∩ V) → φ(V ∩ V')` is the total map `φ ∘ ψ.symm`, and its linearization at
  `ψ(x)` is (Definition 2.7) the derivative `D(φ ∘ ψ⁻¹ ∘ r)(ψ(x))` for a retraction `r` onto the
  retract `ψ(V' ∩ V)`; I read "a retraction" existentially (the derivative on the tangent of the
  retract does not depend on `r`).  `ψ(x)` enters as its level-1 point `y₁`.
- B asserts the project's relation `TangentPre.Rel` (checked with `#print`: `x = x'` and
  `T(ψ ∘ φ⁻¹)(φ(x), h) = (ψ(x), h')`, i.e. the opposite direction, mapping the `φ`-vector to the
  `ψ`-vector) is equivalent to the text's `RelB`; the equivalence of the two directions is part of
  what B claims.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_18
open Polyfold

/-- `TE = E¹ ⊕ E`. -/
noncomputable abbrev TEB (E : ScBanach) : ScBanach := E.shift.prod E

/-- `TO = {(r(x), Dr(x)h) : x ∈ U₁, h ∈ E}`, computed with the retraction `R` (Definition 2.5). -/
def TOB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) : Set ((TEB E).lvl 0) :=
  {p | ∃ x₁ : E.lvl 1, E.toBase 1 x₁ ∈ R.U ∧ ∃ h : E.lvl 0,
    E.toBase 1 p.1 = R.toFun (E.toBase 1 x₁) ∧ p.2 = scDeriv R.U R.toFun x₁ h}

/-- `T_xO = p⁻¹(x) = {h | (x, h) ∈ TO}`, `x` given by its level-1 point `x₁`. -/
def TxOB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) (x₁ : E.lvl 1) :
    Set (E.lvl 0) :=
  {h | (x₁, h) ∈ TOB R}

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- `X_m`: the points `x` with `φ(x) ∈ O_m` for a chart `φ` around `x`. -/
def levelSetB (P : MPolyfold X) (m : ℕ) : Set X :=
  {x | ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧
    ∃ z ∈ φ.model.E.lvlSet φ.model.O m, φ.model.E.toBase m z = φ.toPartialEquiv x}

/-- `(x, V, φ, (O, C, E), h)` is a tuple of Definition 2.17: `x ∈ X_1`, `φ` a chart around `x`,
`h ∈ T_{φ(x)}O`. -/
def IsTupleB (P : MPolyfold X) (x : X) (φ : MChart X) (h : φ.model.E.lvl 0) : Prop :=
  x ∈ levelSetB P 1 ∧ P.IsChart φ ∧ x ∈ φ.source ∧
    ∃ x₁ : φ.model.E.lvl 1, φ.model.E.toBase 1 x₁ = φ.toPartialEquiv x ∧
      ∀ R : ScRetraction φ.model.E φ.model.C, R.retract = φ.model.O → h ∈ TxOB R x₁

/-- **Definition 2.17**: `(x, φ, h) ∼ (x', ψ, h')` if `x = x'` and `T(φ ∘ ψ⁻¹)(ψ(x))h' = h`. -/
def RelB {P : MPolyfold X} (p q : P.TangentPre) : Prop :=
  p.x = q.x ∧
    ∃ R : ScRetraction q.φ.model.E q.φ.model.C,
      R.retract = q.φ.toPartialEquiv '' (q.φ.source ∩ p.φ.source) ∧
      ∃ y₁ : q.φ.model.E.lvl 1, q.φ.model.E.toBase 1 y₁ = q.φ.toPartialEquiv q.x ∧
        scDeriv R.U
          (((p.φ.toPartialEquiv : X → p.φ.model.E.lvl 0) ∘ q.φ.symm) ∘ R.toFun) y₁ q.h = p.h

end

/-- Definition 2.17: `T_xO = p⁻¹(x) = Dr(x)E`; the project's tuples and their equivalence are the
text's, and `∼` is an equivalence relation. -/
def B : Prop :=
  -- `T_xO = p⁻¹(x)`, the image of `Dr(x)`
  (∀ (E : ScBanach) (C O : Set (E.lvl 0)), IsScRetract E C O →
    ∀ x₁ : E.lvl 1, E.toBase 1 x₁ ∈ O → ∀ R : ScRetraction E C, R.retract = O →
      tangentSpace E C O x₁ = TxOB R x₁ ∧ TxOB R x₁ = Set.range (scDeriv R.U R.toFun x₁)) ∧
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
    -- the project's tuples are the text's
    (∀ p : P.TangentPre, IsTupleB P p.x p.φ p.h) ∧
    (∀ (x : X) (φ : MChart X) (h : φ.model.E.lvl 0), IsTupleB P x φ h →
      ∃ p : P.TangentPre, p.x = x ∧ p.φ = φ ∧ HEq p.h h) ∧
    -- the project's equivalence is the text's
    (∀ p q : P.TangentPre, p.Rel q ↔ RelB p q) ∧
    -- `∼` is an equivalence relation
    Equivalence (fun p q : P.TangentPre => RelB p q)

end RoundTrip.V2_18
