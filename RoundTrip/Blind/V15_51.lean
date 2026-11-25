import Polyfold
/-! Blind formalization of V15_51 (the Springer 2021 book, Part II, §15.4, Theorem 15.4.1, p. 702;
2017: Theorem 15.6): the canonical oriented lift of `T_Θ`.

Text: the tangent functor `T_Θ` of `Θ = Λ ∘ f` has a canonical lift to `Ĝr(X)`, locally
`∑_{i : f(y) = sᵢ(y)} σᵢ · ((f − sᵢ)'(y), o_{i,y})`, independent of the local sc⁺-section
structure.

Choices:
- Setting (the statement file quotes no hypotheses; I take those of §15.4 that make `T_Θ` and
  the formula meaningful): universe 0, `A : SEP.{0}` with `A.X.IsTame`; `(f, o)` an oriented
  sc-Fredholm section functor, read as in my `V15_36.lean` (`IsScFredholmSectionFunctor`,
  `o : y ↦ Or_y^f` on smooth objects with `IsSectionOrientation` (Definition 6.6.16) and
  `EpStrongBundle.IsOrInvariant` (Definition 12.5.4); the vocabulary needs
  `hsec : HasScPlusSectionsThrough` and paracompactness instances of `(Fin n → ℝ) × Obj` and its
  pull-back of `W`, taken as arguments — vocabulary presuppositions, not hypotheses of the text);
  `Λ` an sc⁺-multisection functor with `T(f,Λ)` onto on `supp(Λ ∘ f)` (`IsTransversal`) and in
  good position at the support points in `∂X` (`IsGoodPositionAt`, Definition 15.2.4), and —
  since the text speaks of the tangent functor of `Θ` — `Θ = z ↦ Λ(f(z))` a branched
  ep⁺-subgroupoid (`IsBranchedEpSubgroupoid`, Definition 9.1.2) as a presupposition.
- The local formula: the sheets `Mᵢ = {f = sᵢ}` of a local sc⁺-section structure, with
  `T_yMᵢ = ker (f − sᵢ)'(y)` oriented by `o_{i,y}` induced from `o_y`, so that the oriented member
  `((f − sᵢ)'(y), o_{i,y})` is the oriented tangent space `(T_yMᵢ, o_{i,y})` in `Ĝr(X)`.  The
  project's `KernelBranching A f Λ x` (`#print`ed: a tame local branching structure of `Θ` at `x`
  whose sheets are `{z ∈ U(x) | f(z) = sᵢ(z)}` for a local sc⁺-section structure `(sᵢ, σᵢ)` on an
  open `O ⊇ U(x)`, tangent spaces the kernels of the onto `(f − sᵢ)'(y)` in every chart) and its
  `canonSum` (`∑_{i : y ∈ Mᵢ} σᵢ · (T_yMᵢ, o_{i,y})`, `y ∈ Mᵢ ⟺ f(y) = sᵢ(y)`).
- "canonical lift of `T_Θ` to `Ĝr(X)`": a section functor `T̂` that is an orientation of `Θ` in
  the sense of Definition 9.3.2 (the project's `IsOrientation`, docstring: natural section of
  `Ĝr(X)` over `X_∞` lifting `TΘ`, locally represented with orientations), equal to the formula
  at every smooth `y` in the domain of every such local structure.
- B is the conjunction of: (a) such local structures exist at every point of `supp Θ` ("locally");
  (b) the formula does not depend on the local structure (the project's `CanonIndependent`,
  `#print`ed: two structures give the same sum at a common smooth point); (c) a lift `T̂` as above
  exists.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V15_51
open Polyfold Polyfold.SBLocalization

/-- Theorem 15.4.1. -/
def B : Prop :=
  ∀ (A : SEP.{0}) [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × A.Obj)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace A.P (Prod.snd : (Fin n → ℝ) × A.Obj → A.Obj))],
    A.X.IsTame →
    ∀ (f : A.Obj → A.W) (hF : A.E.IsScFredholmSectionFunctor f)
      (hsec : A.B.HasScPlusSectionsThrough)
      (o : (y : A.Obj) → (hy : y ∈ A.X.PObj.smoothSet) → Orx f hF.2 y hy),
      IsSectionOrientation f hF.2 o → A.E.IsOrInvariant hF hsec o →
    ∀ Λ : A.W → ℚ≥0, IsScPlusMultisection A Λ → IsTransversal f Λ →
      (∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x) →
      A.X.IsBranchedEpSubgroupoid (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) →
        -- (a) local structures described by kernels exist on the support
        (∀ x, 0 < Λ (f x) → Nonempty (KernelBranching A f Λ x)) ∧
        -- (b) the formula does not depend on the local structure
        CanonIndependent Λ hF.2 hsec o ∧
        -- (c) the canonical lift of `T_Θ` to `Ĝr(X)`
        ∃ T : A.Obj → A.X.PObj.OrTangent →₀ ℚ,
          A.X.IsOrientation (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) T ∧
          ∀ (x : A.Obj) (K : KernelBranching A f Λ x), ∀ y ∈ K.U, y ∈ A.X.PObj.smoothSet →
            T y = K.canonSum hF.2 hsec o y

end RoundTrip.V15_51
