import Polyfold
/-! Blind formalization of V13_59 (the Springer 2021 book, Part II, §13.4, Proposition 13.4.2,
pp. 623–625; 2017: Proposition 13.6).

Text: for open `V ⊂ X` with `|V| = |X|` and a structured sc⁺-multisection functor `Λ` on `W|V`:
(1) `Λ` has a canonical extension `Λ̄` to an sc⁺-multisection functor on `W`; (2) given open
`O(x) ∋ x` for `x ∉ V`, `Λ̄` carries a structure which on `V` is the given one and has
`U(x) ⊂ O(x)` for `x ∉ V`.

Choices:
- Setting: universe 0; the strong bundle over the ep-groupoid is `A : SEP.{0}`; `V` an open set
  of objects.
- `|V| = |X|`: every object `x` is isomorphic to some `q ∈ V` (a morphism `x → q`, the
  project's `Isomorphic`).
- "a structured sc⁺-multisection functor `Λ` on `W|V`": the project's `StructuredOn A V`
  (`#print`ed: a functor `L.Λ` (its values over `V` matter) with `IsScPlusMultisectionOn A V`,
  a good system `(U(q))_{q ∈ V}` for the ep-groupoid `V` (`IsGoodIn`), symmetric structures
  `L.S q` on `U(q)` representing `Λ`, and correspondences `L.τ q q'` with the conditions of
  Definitions 13.3.4 and 13.3.6 on `𝒰(q, q')`).  I add `IsWFunctorOn A V L.Λ` (the text's
  "functor on `W|V`").  The structure is a tuple, not a class.
- (1) "canonical extension to an sc⁺-multisection functor on `W`": there is `Λ̄` with
  `IsScPlusMultisection A Λ̄` agreeing with `Λ` over `V`, and it is the only functor on `W`
  (`IsWFunctor`) agreeing with `Λ` over `V` (canonical = uniquely determined).
- (2) "given open `O(x) ∋ x` for `x ∉ V`": `O : X → Set X` with `O x` open and `x ∈ O x` for
  `x ∉ V` (values on `V` ignored).  "`Λ̄` carries a structure": a structured tuple `T` (the
  project's `StructuredTuple`, `#print`ed: `Λ`, sc⁺-multisection, decoration `(𝒰, S)` with a
  good system `𝒰`, correspondences `τ`) with `T.Λ = Λ̄`.  "`U(x) ⊂ O(x)` for `x ∉ V`":
  `T.dec.𝒰.U x ⊆ O x`.  "which on `V` is the given one": for `q ∈ V` the neighbourhood with its
  action is the given one (`T.dec.𝒰.nbhd q = L.nbhd q`), and the index sets are identified by
  `G_q`-equivariant bijections `e q : I_q ≃ I^L_q` under which the sections agree on `U(q)` and
  `τ_{q,q'}` agrees with `L.τ q q'` on `𝒰(q, q')` (`IndexCorr.map`).  The text says "is the given
  one"; I allow the identification of the index sets by bijections (the project's index sets are
  types).
- Possible issue: (2) keeps the given `U(q)`, `q ∈ V`, in the good system of `X`; these were
  only asked to be good for the ep-groupoid `V` (properness with closures in `V`), so if they are
  not good in `X` the literal (2) needs smaller `U(q)`.  I formalize the text literally.
-/
namespace RoundTrip.V13_59
open Polyfold Polyfold.SBLocalization

/-- The structure `T` restricted to `V` is the given structure `L`. -/
def AgreesOnV {A : SEP.{0}} {V : Set A.Obj} (L : StructuredOn A V) (T : StructuredTuple A) :
    Prop :=
  (∀ q : V, T.dec.𝒰.nbhd q = L.nbhd q) ∧
  ∃ e : ∀ q : V, (T.dec.S q).I ≃ (L.S q).I,
    (∀ (q : V) (g : A.X.Isotropy q) (i : (T.dec.S q).I), e q (g • i) = g • e q i) ∧
    (∀ (q : V) (i : (T.dec.S q).I), ∀ y ∈ (L.nbhd q).U,
      (T.dec.S q).s i y = (L.S q).s (e q i) y) ∧
    (∀ q q' : V, ∀ φ ∈ A.X.morBetween (L.nbhd q).U (L.nbhd q').U,
      (T.tau.τ q q' φ).map (e q) (e q') = L.τ q q' φ)

/-- Proposition 13.4.2: the canonical extension from `W|V`, `|V| = |X|`, and its structure. -/
def B : Prop :=
  ∀ (A : SEP.{0}) (V : Set A.Obj), IsOpen V → (∀ x : A.Obj, ∃ q ∈ V, A.X.Isomorphic x q) →
    ∀ L : StructuredOn A V, IsWFunctorOn A V L.Λ →
      ∃ Λbar : A.W → ℚ≥0,
        -- (1)
        IsScPlusMultisection A Λbar ∧
        (∀ w : A.W, A.P w ∈ V → Λbar w = L.Λ w) ∧
        (∀ Λ₂ : A.W → ℚ≥0, IsWFunctor A Λ₂ → (∀ w : A.W, A.P w ∈ V → Λ₂ w = L.Λ w) →
          Λ₂ = Λbar) ∧
        -- (2)
        ∀ O : A.Obj → Set A.Obj, (∀ x ∉ V, IsOpen (O x) ∧ x ∈ O x) →
          ∃ T : StructuredTuple A, T.Λ = Λbar ∧ (∀ x ∉ V, T.dec.𝒰.U x ⊆ O x) ∧ AgreesOnV L T

end RoundTrip.V13_59
