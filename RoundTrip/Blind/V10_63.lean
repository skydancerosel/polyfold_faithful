import Polyfold
/-! Blind formalization of V10_63 (the Springer 2021 book, Part II, §10.1, Proposition 10.1.10,
p. 470; 2017: Proposition 10.4, p. 340): local families `α_z` and `|TF| = |TG|`.

Text: if `X` and `Y` have (LR) and `F, G : X → Y` are equivalences with `|F| = |G|`: (1) every
`x` has a connected neighbourhood `U(x)` with the natural `G_x`-action and an sc-smooth
`z ↦ α_z : F(z) → G(z)` on it; (2) `|TF| = |TG|`.

Choices:
- Setting: universe 0 (all spaces in `Type`), `X`, `Y` objects of the project's bundled `EP.{0}`,
  `F, G : EpFunctor X.X Y.X` sc-smooth functors.
- "equivalence": the project's `EpFunctor.IsEquivalence` (2021 Definition 10.1.1, compared in
  `RoundTrip/Blind/V10_1.lean`); "(LR)": the project's `EpGroupoid.IsLR` (2021 Definition 7.4.19,
  read with `#print`; see `RoundTrip/Blind/V10_62.lean`), for both `X` and `Y` as the text says.
- `|F| = |G|`: the induced maps of orbit spaces agree, i.e. `|F(x)| = |G(x)|` in `|Y|` for every
  object `x` (`Y.π`, the project's quotient map to `Y.OrbitSpace`); this is equality of the maps
  `|X| → |Y|`, every point of `|X|` being some `|x|`.
- (1) "a connected neighbourhood `U(x)` with the natural `G_x`-action": a natural representation
  `R : X.NaturalRep x` (the project's structure, read with `#print`: open connected `U ∋ x`,
  `Φ : G_x → Diff_sc(U)`, `Γ` with every morphism between points of `U` some unique `Γ(g, ·)`; the
  data of 2021 Theorem 7.1.13, as in `RoundTrip/Blind/V8_48.lean`).  "an sc-smooth
  `z ↦ α_z : F(z) → G(z)` on it": a map `α : Obj_X → Mor_Y`, sc-smooth on the open set `U(x)`
  into the morphism M-polyfold `𝐘` (the project's `MPolyfold.IsScSmoothOn`, read with `#print`),
  with `s(α_z) = F(z)` and `t(α_z) = G(z)` for `z ∈ U(x)`.  Its values off `U(x)` are junk.
  `U(x)` is not asked to be small (the text does not say so).
- (2) `TF, TG : TX → TY`: the project's tangent functors `EpFunctor.tangent` between the tangent
  ep-groupoids `EpGroupoid.tangentEpGroupoid` (the docstrings' "Theorem 8.1, the structure" and
  "Theorem 8.2, the functor"; trusted, their object spaces live in `Type 1`); `|TF| = |TG|` read
  pointwise as in the hypothesis:
  `|TF(p)| = |TG(p)|` in `|TY|` for every tangent vector `p`.
- B is the conjunction (1) ∧ (2) under the hypotheses.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_63
open Polyfold

/-- **Proposition 10.1.10**: for equivalences `F, G : X → Y` with `|F| = |G|` between
ep-groupoids with (LR), (1) locally `z ↦ α_z : F(z) → G(z)` sc-smooth on a natural
representation, (2) `|TF| = |TG|`. -/
def B : Prop :=
  ∀ (X Y : EP.{0}) (F G : EpFunctor X.X Y.X),
    X.X.IsLR → Y.X.IsLR → F.IsEquivalence → G.IsEquivalence →
    (∀ x : X.Obj, Y.X.π (F.obj x) = Y.X.π (G.obj x)) →
    (∀ x : X.Obj, ∃ (R : X.X.NaturalRep x) (α : X.Obj → Y.Mor),
        X.X.PObj.IsScSmoothOn Y.X.PMor α R.U ∧
        ∀ z ∈ R.U, Y.X.src (α z) = F.obj z ∧ Y.X.tgt (α z) = G.obj z) ∧
    (∀ p : X.X.PObj.TangentSpace,
        Y.X.tangentEpGroupoid.π (F.tangent.obj p) = Y.X.tangentEpGroupoid.π (G.tangent.obj p))

end RoundTrip.V10_63
