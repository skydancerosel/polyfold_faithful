import Polyfold
/-! Blind formalization of V11_30 (the Springer 2021 book, Part II, §11.5, Proposition 11.5.1,
p. 547).

Text: for a generalized strong bundle isomorphism `[D]`, `[D]^*N'` and `[D]_*N` of auxiliary norms
are auxiliary norms, defined through choices of `e''` with `Φ(e'') → e`; they are mutually inverse
and depend only on `|[D]|`.

Choices:
- Setting: universe 0; strong bundles over ep-groupoids the project's `SEP.{0}` (`A = (P : W → X,
  μ)`, `A' = (P' : W' → X', μ')`), diagrams `D = W ←Φ W'' →Ψ W'` the project's `SDiagram`, classes
  `[D] = SDiagram.cls D`, generalized strong bundle maps `GenSBMap`, generalized strong bundle
  isomorphisms `GenSBMap.IsGeneralizedIso` (`#print`ed: the class of a diagram whose `Ψ` is a strong
  bundle equivalence; `Φ` is one in every diagram), as in `V10_56.lean`, `V10_58.lean`.
- "auxiliary norm" (2021 Definition 8.3.5): the project's `EpStrongBundle.IsAuxNorm` (`#print`ed:
  Part I's auxiliary norm on `W_{0,1}`, continuous, complete norm on fibres, the convergence
  condition, plus `N(μ(φ, k)) = N(k)`).  `W_{0,1}` is `StrongBundle.One`, its points `e` with
  underlying point `oneVal e ∈ W`.
- `[D]^*N'`, `[D]_*N`: the project's `GenSBMap.pullNorm`, `GenSBMap.pushNorm` (`#print`ed:
  computed on a chosen representative and a chosen preimage in the orbit space of `W''_{0,1}`).
  "Defined through choices of `e''` with `Φ(e'') → e`" (`FormulaB`): for EVERY representative `D`
  of `[D]` whose `Ψ`
  is a strong bundle equivalence and EVERY `e'' ∈ W''_{0,1}` with a morphism `Φ(e'') → e` in the
  ep-groupoid `W` (the project's `Isomorphic` in `E.toEpGroupoid`), `([D]^*N')(e) = N'(Ψ(e''))`;
  symmetrically `([D]_*N)(e') = N(Φ(e''))` for `Ψ(e'') → e'`.  `Ψ(e'')` is read as the point of
  `W'_{0,1}` whose underlying point is `Ψ(oneVal e'')`.  This pins the definition down and contains
  the independence of the choices, for auxiliary norms `N'`, `N`.
- "mutually inverse": `[D]_*[D]^*N' = N'` and `[D]^*[D]_*N = N` for auxiliary norms.  "depend only
  on `|[D]|`": two generalized strong bundle isomorphisms `f₁, f₂ : W → W'` with the same map
  `|f₁| = |f₂| : |W| → |W'|` of orbit spaces (the project's `GenSBMap.orbitMap`, compared with the
  text in `V10_52.lean`) give the same `f^*N'` and `f_*N`, for auxiliary norms.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_30
open Polyfold Polyfold.SBLocalization CategoryTheory

/-- `[D]^*N'` and `[D]_*N` are given by the formulas through choices of `e''`, for every
representative and every choice. -/
def FormulaB : Prop :=
  ∀ (A A' : SEP.{0}) (f : GenSBMap A A') (hf : f.IsGeneralizedIso)
    (D : SDiagram A A'), SEP.equivalences D.Ψ → D.cls = f →
    -- `([D]^*N')(e) = N'(Ψ(e''))` for `Φ(e'') → e`
    (∀ (N' : StrongBundle.One A'.B → ℝ), A'.E.IsAuxNorm N' →
      ∀ (e : StrongBundle.One A.B) (e'' : StrongBundle.One D.B.B) (e' : StrongBundle.One A'.B),
        A.E.toEpGroupoid.Isomorphic (D.Φ.Φ.obj (StrongBundle.oneVal D.B.B e''))
          (StrongBundle.oneVal A.B e) →
        StrongBundle.oneVal A'.B e' = D.Ψ.Φ.obj (StrongBundle.oneVal D.B.B e'') →
        GenSBMap.pullNorm hf N' e = N' e') ∧
    -- `([D]_*N)(e') = N(Φ(e''))` for `Ψ(e'') → e'`
    (∀ (N : StrongBundle.One A.B → ℝ), A.E.IsAuxNorm N →
      ∀ (e' : StrongBundle.One A'.B) (e'' : StrongBundle.One D.B.B) (e : StrongBundle.One A.B),
        A'.E.toEpGroupoid.Isomorphic (D.Ψ.Φ.obj (StrongBundle.oneVal D.B.B e''))
          (StrongBundle.oneVal A'.B e') →
        StrongBundle.oneVal A.B e = D.Φ.Φ.obj (StrongBundle.oneVal D.B.B e'') →
        GenSBMap.pushNorm hf N e' = N e)

/-- Proposition 11.5.1. -/
def B : Prop :=
  -- `[D]^*N'` and `[D]_*N` are auxiliary norms
  (∀ (A A' : SEP.{0}) (f : GenSBMap A A') (hf : f.IsGeneralizedIso),
    (∀ N' : StrongBundle.One A'.B → ℝ, A'.E.IsAuxNorm N' →
      A.E.IsAuxNorm (GenSBMap.pullNorm hf N')) ∧
    (∀ N : StrongBundle.One A.B → ℝ, A.E.IsAuxNorm N →
      A'.E.IsAuxNorm (GenSBMap.pushNorm hf N))) ∧
  -- defined through choices of `e''`
  FormulaB ∧
  -- mutually inverse
  (∀ (A A' : SEP.{0}) (f : GenSBMap A A') (hf : f.IsGeneralizedIso),
    (∀ N' : StrongBundle.One A'.B → ℝ, A'.E.IsAuxNorm N' →
      GenSBMap.pushNorm hf (GenSBMap.pullNorm hf N') = N') ∧
    (∀ N : StrongBundle.One A.B → ℝ, A.E.IsAuxNorm N →
      GenSBMap.pullNorm hf (GenSBMap.pushNorm hf N) = N)) ∧
  -- depend only on `|[D]|`
  (∀ (A A' : SEP.{0}) (f₁ f₂ : GenSBMap A A') (h₁ : f₁.IsGeneralizedIso)
    (h₂ : f₂.IsGeneralizedIso), f₁.orbitMap = f₂.orbitMap →
    (∀ N' : StrongBundle.One A'.B → ℝ, A'.E.IsAuxNorm N' →
      GenSBMap.pullNorm h₁ N' = GenSBMap.pullNorm h₂ N') ∧
    (∀ N : StrongBundle.One A.B → ℝ, A.E.IsAuxNorm N →
      GenSBMap.pushNorm h₁ N = GenSBMap.pushNorm h₂ N))

end RoundTrip.V11_30
