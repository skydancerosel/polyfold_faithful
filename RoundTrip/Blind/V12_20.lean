import Polyfold
/-! Blind formalization of V12_20 (the text's Part II, §12.4, Theorem 12.4.2, pp. 587–588 of the
Springer 2021 book; 2017: Theorem 12.9).

Text: for an sc-Fredholm `f` with `|X|` paracompact, proper, compact solution set and
proper`<∞` are equivalent.

Choices:
- Setting as in `RoundTrip/Blind/V12_4.lean` (universe 0, `E : EpStrongBundle X B`,
  paracompactness of `𝐗 ₛ×_P W` as an instance hypothesis).  "`|X|` paracompact":
  `X.HasParacompactOrbitSpace`.
- "sc-Fredholm `f`": an sc-Fredholm section functor, `f ∈ E.fredholmSectionFunctors`
  (Definition 8.3.4 (3); read with `#print`: an sc-smooth section functor which is an sc-Fredholm
  section of `W → X`).
- The three notions are the project's Definition 12.4.1, read with `#print`:
  `HasCompactSolutionSetEp` (`|S_f| = π(S_f)` compact), `IsProperFunctor` (`|S_f|` compact and
  for every auxiliary norm `N` a saturated open `U ⊇ S_f` with `cl |{x ∈ U | N(f(x)) ≤ 1}|`
  compact), `IsProperLtInftyFunctor` (the same with `N(f(x)) ≤ C` for every `0 < C < ∞`).  They
  match my reading of Definition 12.4.1; I trust them (in particular the quantifier "for every
  auxiliary norm" in (2) and (3)).
- B: the three are pairwise equivalent, stated as `proper ↔ compact solution set` and
  `compact solution set ↔ proper<∞`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V12_20
open Polyfold

/-- **Theorem 12.4.2**: for an sc-Fredholm section functor over an ep-groupoid with paracompact
orbit space, proper ⇔ compact solution set ⇔ proper`<∞`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B),
    X.HasParacompactOrbitSpace →
    ∀ f ∈ E.fredholmSectionFunctors,
      (E.IsProperFunctor f ↔ E.HasCompactSolutionSetEp f) ∧
      (E.HasCompactSolutionSetEp f ↔ E.IsProperLtInftyFunctor f)

end RoundTrip.V12_20
