import Polyfold
/-! Blind formalization of V15_32 (the Springer 2021 book, Part II, §15.3, Theorem 15.3.9, p. 698;
2017: Theorem 15.5): the transversal extension theorem.

Text: `X` tame, `|X|` paracompact, sc-smooth partitions of unity; `f` sc-Fredholm with `|S_f|`
compact; `(N, U)` controls compactness; `Λ : W|∂X → ℚ⁺` `(N, U)`-admissible and structurable with
`N(Λ) < h` on `∂X` for a continuous functor `h : X → (0, 1]`, and `T(f|∂X, Λ)(x)` onto with respect
to intersections of local faces at smooth `x ∈ ∂X`.  Then there is a structurable `Λ̃` with
`Λ̃|(W|∂X) = Λ`, dom-supp in `U`, `N(Λ̃) < h`, `T(f,Λ̃)` onto on `supp(Λ̃ ∘ f)`, and `Λ̃ ∘ f` a
compact tame branched ep⁺-subgroupoid.

Choices:
- Setting: universe 0, `A : SEP.{0}`.  "`X` tame": `A.X.IsTame`; "`|X|` paracompact":
  `A.X.HasParacompactOrbitSpace` (Definition 7.5.1); "sc-smooth partitions of unity": the object
  M-polyfold admits them, `A.X.PObj.AdmitsScPartitionsOfUnity` (Definition 5.5.1), as in
  `V14_43.lean`.  `f`: `IsScFredholmSectionFunctor`, `|S_f|` compact: `HasCompactSolutionSetEp`;
  `(N, U)`: `ControlsCompactness` (Definition 15.3.1), as in my `V15_29.lean`.  `h`: my
  `IsUnitFunctor` (continuous, `0 < h ≤ 1`, constant along morphisms).
- `Λ : W|∂X → ℚ⁺` is represented by a function `Λ : W → ℚ⁺` of which only the values over
  `∂X = {d_X ≥ 1}` (`A.X.PObj.boundary`) matter, as in the project's Chapter 14 notions.
  "structurable": the project's `IsBoundaryStructurable` (Definition 14.1.7, `#print`ed: an
  sc⁺-multisection over `∂X`, `IsBoundaryScPlusMultisection` (Definition 14.1.3), with a
  structure `[Λ, 𝒰, S, τ]`).
- "`(N, U)`-admissible" (Definition 15.3.3) read over `∂X` (my `IsBoundaryAdmissible`): `Λ` an
  sc⁺-multisection over `∂X`, `N(Λ)(x) ≤ 1` for `x ∈ ∂X`, and
  `{x ∈ ∂X | ∃ t ∈ [−1, 1], (tΛ)(f(x)) > 0} ⊆ U`, with `tΛ` the project's `multisectionSmul`
  (Definition 13.2.10, `(0Λ)(w) = [w = 0]`, `(aΛ)(w) = Λ(w/a)`) — the project's `IsAdmissible`
  (`#print`ed) restricted to `∂X`.  "`N(Λ) < h` on `∂X`": `pointwiseNorm N Λ x < h x` for
  `x ∈ ∂X`.
- "`T(f|∂X, Λ)(x)` onto with respect to intersections of local faces at smooth `x ∈ ∂X`": the
  project's `IsBoundaryFaceOnto f Λ` (`#print`ed): for every sc⁺-multisection `Λ'` on `W` agreeing
  with `Λ` over `∂X`, at every smooth `x ∈ ∂X` with `Λ(f(x)) > 0` every operator of `T(f,Λ')(x)`
  is onto on the reduced tangent space `T^R_xX` (the intersection of the tangent spaces of the
  local faces), in every chart and presentation.  I use it with a caveat: it quantifies over all
  extensions `Λ'` instead of speaking of `Λ` over `∂X` alone; this is the text's condition as
  long as the restriction of `(f − sᵢ)'(x)` to `T^R_xX` only depends on the face values (true for
  the derivative along `T^R_xX ⊆ T_x(∂X)`), and it is vacuous if no extension exists.
- Conclusion: `Λ̃ : W → ℚ⁺` with `IsStructurable` (Definition 13.3.6), `Λ̃(w) = Λ(w)` for every
  `w` over `∂X` ("`Λ̃|(W|∂X) = Λ`"), `domSupp Λ̃ ⊆ U`, `N(Λ̃)(x) < h(x)` at every object,
  `IsTransversal f Λ̃` (Definition 15.2.1), and `z ↦ Λ̃(f(z))` a branched ep⁺-subgroupoid
  (`IsBranchedEpSubgroupoid`), compact (`IsCompactBranched`) and tame (`IsTameBranched`).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V15_32
open Polyfold Polyfold.SBLocalization

/-- `h : X → (0, 1]` is a continuous functor. -/
def IsUnitFunctor (A : SEP.{0}) (h : A.Obj → ℝ) : Prop :=
  Continuous h ∧ (∀ x, 0 < h x ∧ h x ≤ 1) ∧ ∀ φ : A.Mor, h (A.X.src φ) = h (A.X.tgt φ)

/-- `Λ : W|∂X → ℚ⁺` is `(N, U)`-admissible for `f` (Definition 15.3.3 over `∂X`). -/
def IsBoundaryAdmissible (A : SEP.{0}) (f : A.Obj → A.W) (N : A.B.One → ℝ) (U : Set A.Obj)
    (Λ : A.W → ℚ≥0) : Prop :=
  IsBoundaryScPlusMultisection A Λ ∧
    (∀ x ∈ A.X.PObj.boundary, pointwiseNorm N Λ x ≤ 1) ∧
    {x | x ∈ A.X.PObj.boundary ∧ ∃ t ∈ Set.Icc (-1 : ℝ) 1, 0 < multisectionSmul t Λ (f x)} ⊆ U

/-- Theorem 15.3.9 (transversal extension). -/
def B : Prop :=
  ∀ (A : SEP.{0}), A.X.IsTame → A.X.HasParacompactOrbitSpace →
    A.X.PObj.AdmitsScPartitionsOfUnity →
    ∀ (f : A.Obj → A.W), A.E.IsScFredholmSectionFunctor f → A.E.HasCompactSolutionSetEp f →
    ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
    ∀ (h : A.Obj → ℝ), IsUnitFunctor A h →
    ∀ Λ : A.W → ℚ≥0, IsBoundaryAdmissible A f N U Λ → IsBoundaryStructurable A Λ →
      (∀ x ∈ A.X.PObj.boundary, pointwiseNorm N Λ x < h x) →
      IsBoundaryFaceOnto f Λ →
      ∃ Λt : A.W → ℚ≥0, IsStructurable A Λt ∧
        (∀ w : A.W, A.P w ∈ A.X.PObj.boundary → Λt w = Λ w) ∧
        domSupp Λt ⊆ U ∧
        (∀ x, pointwiseNorm N Λt x < h x) ∧
        IsTransversal f Λt ∧
        A.X.IsBranchedEpSubgroupoid (fun z => ((Λt (f z) : ℚ≥0) : ℚ)) ∧
        A.X.IsCompactBranched (fun z => ((Λt (f z) : ℚ≥0) : ℚ)) ∧
        A.X.IsTameBranched (fun z => ((Λt (f z) : ℚ≥0) : ℚ))

end RoundTrip.V15_32
