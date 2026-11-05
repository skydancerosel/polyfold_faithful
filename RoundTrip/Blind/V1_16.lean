import Polyfold
/-! Blind formalization of V1_16 (the text's §1.2, Proposition 1.17, p. 12).

Text: let `U` and `V` be relatively open subsets of partial quadrants in sc-Banach spaces and
`f : U → V` an `sc^k` map.  Then `f : U¹ → V¹` is also `sc^k`.

Choices:
- Setting: `E F : ScBanach` (levels in `Type`, forced by the project's `ScBanach`); `U ⊆ C ⊆ E₀`,
  `V ⊆ C' ⊆ F₀` with `IsRelOpenInQuadrant E C U`, `IsRelOpenInQuadrant F C' V` (checked with
  `#print`: `C` the preimage of `[0,∞)ⁿ ⊕ W` under an sc-isomorphism `E ≅ ℝⁿ ⊕ W`, `U = O ∩ C`,
  `O` open).  `f : E₀ → F₀` is a total function with `f(U) ⊆ V`.  `k : ℕ` (the text's `sc^k`
  with finite `k`).
- `sc^k` is the project's `IsSck k` (checked with `#print` and by `rfl`: `IsSck 0 = IsSc0`,
  `IsSck (k+1) E F U f = IsSc1 U f ∧ IsSck k (TE) (TF) (TU) (Tf)`, with `TE = E¹ ⊕ E`,
  `TU = U₁ × E₀`, and `Tf(x, h) = (f(x), Df(x)h)` built from a chosen derivative family, which is
  unique on `U₁` here).  This is Definitions 1.14–1.15.
- `U¹` is `U ∩ E₁` with the shifted sc-structure: the subset `E.lvlSet U 1 = ι₁⁻¹(U)` of
  `(E¹)₀ = E₁`, in the sc-Banach space `E.shift = E¹` (checked: levels `E_{m+1}`); likewise `V¹`.
  "`f : U¹ → V¹`" is the induced map `levelTo f 1 1 : E₁ → F₁` (the point of `F₁` over `f(x)`,
  via `Function.invFun`; junk where none exists).  B states both that it maps `U¹` into `V¹`
  (the text's "`f : U¹ → V¹`") and that it is `sc^k` from `E¹` to `F¹`.
- Nothing looks false to me.
-/
namespace RoundTrip.V1_16
open Polyfold

/-- The map `E_a → F_b` induced by `f : E₀ → F₀`: the point of `F_b` over `f(x)` (junk if none). -/
noncomputable def levelTo {E F : ScBanach} (f : E.lvl 0 → F.lvl 0) (a b : ℕ) :
    E.lvl a → F.lvl b :=
  fun x => Function.invFun (F.toBase b) (f (E.toBase a x))

/-- If `f : U → V` is `sc^k`, then so is `f : U¹ → V¹`. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (C' V : Set (F.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (k : ℕ),
    IsRelOpenInQuadrant E C U → IsRelOpenInQuadrant F C' V → Set.MapsTo f U V →
    IsSck k E F U f →
      Set.MapsTo (levelTo f 1 1) (E.lvlSet U 1) (F.lvlSet V 1) ∧
      IsSck k E.shift F.shift (E.lvlSet U 1) (levelTo f 1 1)

end RoundTrip.V1_16
