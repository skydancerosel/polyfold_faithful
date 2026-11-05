import Polyfold
/-! Blind formalization of V2_16 (the text's §2.2, after Definition 2.14, p. 25: "the level `X^1`
is an M-polyfold").

Text: `(V_m, φ, (O_m, C_m, E_m))` is a chart on `X_m`; any two such charts are sc-smoothly
compatible, and they form an atlas on `X_m`.

Choices:
- Setting: `X : Type` (spaces put in `Type`; the project's `MPolyfold` is universe-polymorphic,
  this is the instance `u = 0`) with `[TopologicalSpace X] [T2Space X] [ParacompactSpace X]` and
  an M-polyfold structure `P : MPolyfold X` (Definition 2.13; see `RoundTrip/Blind/V2_13.lean`).
  The charts `(V, φ, (O, C, E))` of `X` are the `MChart X` with `P.IsChart φ` (charts of the
  maximal atlas, checked with `#print`).
- The quoted statement is for every level `m` (the title's `X^1` is `m = 1`), so B is for all
  `m`.  `X_m` with its topology: the project's `P.levelSet m` with `P.levelTopology m` (checked
  with `#print`; my `RoundTrip/Blind/V2_14.lean` states they are the text's), passed explicitly
  (the subtype also carries the subspace topology of `X`, which is not the one meant).
- The level-`m` chart: `V_m = V ∩ X_m` (`VmB`), `E_m` = the shifted sc-space `E^m` with levels
  `E_{m+k}` (the project's `E.shiftAdd m`, whose level `k` is `E_{m+k}` definitionally — its
  docstring; so `(E^m)_0 = E_m`), `C_m = C ∩ E_m` and `O_m = O ∩ E_m` (`E.lvlSet · m`, checked:
  `ι_m⁻¹(·)`), and `φ_m : V_m → O_m` maps `x` to the lift of `φ(x)` to `E_m` (`φmB`, via
  `Function.invFun ι_m`, the unique preimage since `ι_m` is injective).  For `m = 1` the project
  uses `E.shift` (levels `E_{k+1}`) instead of `E^1`; the two are sc-isomorphic, not equal.
- "is a chart on `X_m`" (Definition 2.11, my `IsChartB` as in `RoundTrip/Blind/V2_10.lean`, with
  the model given by its components): `V_m` is open in `X_m`, `(O_m, C_m, E^m)` is an sc-smooth
  retract (the project's `IsScRetract`, Definition 2.3, checked in `RoundTrip/Blind/V2_2.lean`),
  and `φ_m` restricts to a homeomorphism `V_m ≃ O_m` (`O_m ⊆ E_m` with the topology of `E_m`).
- "compatible" (Definition 2.11, `CompatibleB` as in `RoundTrip/Blind/V2_10.lean`): with
  `A = φ_m(V_m ∩ V'_m)`, `A' = ψ_m(V_m ∩ V'_m)`, the transition `ψ_m ∘ φ_m⁻¹` (`transB`, a total
  map choosing the preimage, junk `0` off `φ_m(V_m)`) and its inverse are sc-smooth in the sense
  of Definition 2.7 between `(A, C_m, E^m)` and `(A', C'_m, E'^m)` (existential reading: `f ∘ r`
  sc-smooth for SOME retraction `r` onto `A`, as in `RoundTrip/Blind/V2_6.lean`).
- "they form an atlas" (Definition 2.12): pairwise compatible (the second conjunct, for all charts
  `φ, ψ` of `X`) and their domains cover `X_m` (third conjunct).
- Not included: that `X_m` (or `X^1`) is an M-polyfold in the sense of Definition 2.13 (Hausdorff,
  paracompact) — the title's phrase; the quoted claims are about charts and atlas only, and
  paracompactness is Theorem 2.16 (my `RoundTrip/Blind/V2_17.lean`).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_16
open Polyfold

/-- **Definition 2.7**: `f : O → O'` is sc-smooth between the retracts `(O, C, E)` and
`(O', C', E')`: `f(O) ⊆ O'` and `f ∘ r` is sc-smooth for a retraction `r` onto `O`. -/
def IsScSmoothRetractMapB (E : ScBanach) (C O : Set (E.lvl 0)) (E' : ScBanach)
    (O' : Set (E'.lvl 0)) (f : E.lvl 0 → E'.lvl 0) : Prop :=
  Set.MapsTo f O O' ∧ ∃ R : ScRetraction E C, R.retract = O ∧ IsScSmooth R.U (f ∘ R.toFun)

section
universe u
variable {Y : Type u}

/-- **Definition 2.11**: `(V, φ, (O, C, E))` is a chart on the space `Y`: `V` open, `(O, C, E)`
an sc-smooth retract, `φ : V → O` a homeomorphism. -/
def IsChartB [TopologicalSpace Y] (V : Set Y) (E : ScBanach) (C O : Set (E.lvl 0))
    (φ : Y → E.lvl 0) : Prop :=
  IsOpen V ∧ IsScRetract E C O ∧ ∃ e : V ≃ₜ O, ∀ y : V, (e y : E.lvl 0) = φ y

open Classical in
/-- The transition map `ψ ∘ φ⁻¹`, as a total map (junk `0` off `φ(V)`). -/
noncomputable def transB (V : Set Y) {E E' : ScBanach} (φ : Y → E.lvl 0) (ψ : Y → E'.lvl 0) :
    E.lvl 0 → E'.lvl 0 :=
  fun z => if h : ∃ y ∈ V, φ y = z then ψ h.choose else 0

/-- **Definition 2.11**: the charts `(V, φ, (O, C, E))` and `(V', ψ, (O', C', E'))` are
sc-smoothly compatible. -/
def CompatibleB (V : Set Y) (E : ScBanach) (C : Set (E.lvl 0)) (φ : Y → E.lvl 0)
    (V' : Set Y) (E' : ScBanach) (C' : Set (E'.lvl 0)) (ψ : Y → E'.lvl 0) : Prop :=
  IsScSmoothRetractMapB E C (φ '' (V ∩ V')) E' (ψ '' (V ∩ V')) (transB V φ ψ) ∧
  IsScSmoothRetractMapB E' C' (ψ '' (V ∩ V')) E (φ '' (V ∩ V')) (transB V' ψ φ)

end

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- `V_m = V ∩ X_m`, as a subset of `X_m`. -/
def VmB (P : MPolyfold X) (φ : MChart X) (m : ℕ) : Set (P.levelSet m) :=
  {x | (x : X) ∈ φ.source}

/-- `φ_m : V_m → O_m`, `x ↦ φ(x)` seen in `E_m`. -/
noncomputable def φmB (P : MPolyfold X) (φ : MChart X) (m : ℕ) :
    P.levelSet m → (φ.model.E.shiftAdd m).lvl 0 :=
  fun x => Function.invFun (φ.model.E.toBase m) (φ.toPartialEquiv x)

/-- `C_m = C ∩ E_m ⊆ (E^m)_0`. -/
def CmB (φ : MChart X) (m : ℕ) : Set ((φ.model.E.shiftAdd m).lvl 0) :=
  φ.model.E.lvlSet φ.model.C m

/-- `O_m = O ∩ E_m ⊆ (E^m)_0`. -/
def OmB (φ : MChart X) (m : ℕ) : Set ((φ.model.E.shiftAdd m).lvl 0) :=
  φ.model.E.lvlSet φ.model.O m

end

/-- The charts `(V_m, φ, (O_m, C_m, E^m))` induced by the charts of `X` are charts on `X_m`, any
two are sc-smoothly compatible, and they form an atlas of `X_m`. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X) (m : ℕ),
    -- `(V_m, φ, (O_m, C_m, E^m))` is a chart on `X_m`
    (∀ φ : MChart X, P.IsChart φ →
      @IsChartB _ (P.levelTopology m) (VmB P φ m) (φ.model.E.shiftAdd m) (CmB φ m) (OmB φ m)
        (φmB P φ m)) ∧
    -- any two such charts are sc-smoothly compatible
    (∀ φ ψ : MChart X, P.IsChart φ → P.IsChart ψ →
      CompatibleB (VmB P φ m) (φ.model.E.shiftAdd m) (CmB φ m) (φmB P φ m)
        (VmB P ψ m) (ψ.model.E.shiftAdd m) (CmB ψ m) (φmB P ψ m)) ∧
    -- their domains cover `X_m`
    (∀ x : P.levelSet m, ∃ φ : MChart X, P.IsChart φ ∧ x ∈ VmB P φ m)

end RoundTrip.V2_16
