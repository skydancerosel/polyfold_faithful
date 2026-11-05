import Polyfold
/-! Blind formalization of V4_31 (the text's §4.2, Remark 4.14, p. 157, read in a chart).

Text: `s(V) ⊆ X_∞`; `T_aA = Ts(a)(T_aX)` is the image of the sc⁺-operator `Ts(a)`, hence
finite-dimensional.

Choices:
- Setting: `X : Type` (universe 0), Hausdorff paracompact, `P : MPolyfold X`, `A ⊆ X`, and the
  data of Definition 4.13: an open `V` and an sc⁺-retraction `s : V → V` with `s(V) = A ∩ V`
  (my own `IsScPlusRetractionOnB`, copied from my V4_9).  B quantifies over all such `(V, s)`,
  so it covers every point `a ∈ A` and every smaller `V`.
- "`s(V) ⊆ X_∞`": `s '' V ⊆ P.smoothSet`.
- "In a chart" (the item's title; `T_aX` has no linear structure intrinsically): a chart `φ` of
  the structure (`P.IsChart φ`) with model `(O, C, E)`, with `V` in its domain, and an sc-smooth
  retraction `r : U → U` (Definition 2.1) onto `φ(V)` (the situation "`V = φ⁻¹(O)`" of the proof
  of Theorem 4.18, item V4_30; `φ(V)` is the model of the chart restricted to `V`).  The local
  representative of `s` is `t = φ ∘ s ∘ φ⁻¹ ∘ r` (a total function on `E₀`, meaningful on `U`),
  an sc⁺-retraction onto `φ(A ∩ V)`.  For `a ∈ A ∩ V` and the level-`1` point `z` over `φ(a)`:
  * `T_aX` is `T_z(φ(V))` and `T_aA` is `T_z(φ(A ∩ V))`, the project's `tangentSpace` of these
    retracts (Definition 2.17, checked with `#print`: the fibre over `z` of `Tr''(TU'')` for a
    chosen retraction `r''` onto the retract);
  * `Ts(a)` is `Dt(z) = scDeriv r.U t z : E₀ → E₀` (the project's chosen derivative family of
    the sc¹ map `t`; unique at level-`1` points), whose restriction to `T_z(φ(V)) = Dr(z)E` is the
    tangent map of `φ ∘ s ∘ φ⁻¹` between retracts (Definition 2.7 / 2.17 convention `T f = T(f ∘ r)`
    on `TO`).
  B asserts: `T_z(φ(A ∩ V)) = Dt(z)(T_z(φ(V)))` ("`T_aA = Ts(a)(T_aX)`"), this set is the range
  of `Dt(z)` ("the image of `Ts(a)`"), `Dt(z)` is an sc⁺-operator (Definition 1.4; my own
  `IsScPlusOperatorB` copied from my V4_8: maps every `E_m` continuously into `E_{m+1}`), and the
  range is finite-dimensional.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_31
open Polyfold

/-- Definition 4.4 (second sentence): an sc-smooth retraction `r : V → V` on an open subset `V` of
the M-polyfold `X` is an **sc⁺-retraction** if `r : V → V¹` is sc-smooth. -/
def IsScPlusRetractionOnB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (r : X → X) (V : Set X) : Prop :=
  IsOpen V ∧ P.IsScSmoothOn P r V ∧ Set.MapsTo r V V ∧ (∀ x ∈ V, r (r x) = r x) ∧
  (∀ x ∈ V, r x ∈ P.levelSet 1) ∧
  ∀ g : X → P.Level 1, (∀ x ∈ V, P.levelVal 1 (g x) = r x) → P.IsScSmoothOn P.shift g V

/-- `T : E₀ → E₀` is an **sc⁺-operator** `E → E` (Definition 1.4): for every `m` it maps `E_m`
into `E_{m+1}` by a continuous linear map `E_m → E_{m+1}`. -/
def IsScPlusOperatorB (E : ScBanach) (T : E.lvl 0 →L[ℝ] E.lvl 0) : Prop :=
  ∀ m : ℕ, ∃ S : E.lvl m →L[ℝ] E.lvl (m + 1),
    ∀ x : E.lvl m, E.toBase (m + 1) (S x) = T (E.toBase m x)

/-- The local representative `t = φ ∘ s ∘ φ⁻¹ ∘ r` of `s` in the chart `φ`. -/
def localRep {X : Type} [TopologicalSpace X] (φ : MChart X) (s : X → X)
    (r : ScRetraction φ.model.E φ.model.C) : φ.model.E.lvl 0 → φ.model.E.lvl 0 :=
  fun x => φ.toPartialEquiv (s (φ.toPartialEquiv.symm (r.toFun x)))

/-- Remark 4.14: `s(V)` consists of smooth points, and in a chart `T_aA = Ts(a)(T_aX)` is the
image of the sc⁺-operator `Ts(a)`, hence finite-dimensional. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X) (s : X → X) (V : Set X),
    IsScPlusRetractionOnB P s V → s '' V = A ∩ V →
      -- `s(V) ⊆ X_∞`
      s '' V ⊆ P.smoothSet ∧
      -- in a chart: `T_aA = Ts(a)(T_aX)`, the image of the sc⁺-operator `Ts(a)`, finite-dim.
      ∀ (φ : MChart X) (r : ScRetraction φ.model.E φ.model.C), P.IsChart φ →
        V ⊆ φ.toPartialEquiv.source → r.retract = φ.toPartialEquiv '' V →
        ∀ (a : X) (z : φ.model.E.lvl 1), a ∈ A ∩ V →
          φ.model.E.toBase 1 z = φ.toPartialEquiv a →
          tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' (A ∩ V)) z =
              scDeriv r.U (localRep φ s r) z ''
                tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' V) z ∧
          tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' (A ∩ V)) z =
              Set.range (scDeriv r.U (localRep φ s r) z) ∧
          IsScPlusOperatorB φ.model.E (scDeriv r.U (localRep φ s r) z) ∧
          FiniteDimensional ℝ (LinearMap.range
            (scDeriv r.U (localRep φ s r) z : φ.model.E.lvl 0 →ₗ[ℝ] φ.model.E.lvl 0))

end RoundTrip.V4_31
