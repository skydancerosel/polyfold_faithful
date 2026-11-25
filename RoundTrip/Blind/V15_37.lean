import Polyfold
/-! Blind formalization of V15_37 (the Springer 2021 book, Part II, §15.4, Corollary 15.4.4,
p. 703; 2017: Corollary 15.2): the invariant `Φ_{(f,o)}` on de Rham cohomology.

Text: `d_X ≡ 0`, `|X|` paracompact, `|S_f|` compact, `o` an orientation: there is a well-defined
`Φ_{(f,o)} : H*_dR(X) → ℝ`, `Φ([ω]) = ∫_{(Λ∘f, o)} ω` for a regular perturbation; effective
version with LUC.  Proof left to the reader.

Choices:
- Setting: universe 0, `A : SEP.{0}`; `d_X ≡ 0` (`degIndex = 0` at every object); "`|X|`
  paracompact": `HasParacompactOrbitSpace`; `f` an sc-Fredholm section functor
  (`IsScFredholmSectionFunctor`) with `|S_f|` compact (`HasCompactSolutionSetEp`).
- "`o` an orientation": as in my `V15_36.lean`: `o : y ↦ Or_y^f` on smooth objects with
  `IsSectionOrientation` (Definition 6.6.16) and `EpStrongBundle.IsOrInvariant` (Definition
  12.5.4, invariance); the vocabulary needs `hsec : HasScPlusSectionsThrough` and the
  paracompactness instances of `(Fin n → ℝ) × Obj` and its pull-back of `W` (taken as
  hypotheses/instance arguments: vocabulary presuppositions, not hypotheses of the text).
- The Fredholm index.  `Φ([ω])` is an integral over the `k`-dimensional `Λ ∘ f`, so only forms of
  degree `k` = the index enter; I presuppose a constant index `k` (`IsIndexAt f x k` at every
  smooth `x`) and state B for every `k`, as the conjunction over `k = m + 1 ≥ 1` (integrals) and
  `k = 0` (weighted signed counts).  In the other degrees nothing is claimed.
- `H^k_dR(X)`: the project's `EP.epDeRham` of the base ep-groupoid (`ker d / im d` on
  `Ω^k_{ep,∞}(X)`), `[ω]` the class of a closed `ω`.
- "a regular perturbation" with the orientation from `o`: for `k = m + 1`, the project's
  `OrientedRegularPerturbation A f m` (`#print`ed: a structurable regular perturbation
  `(N, U, Λ)` (Corollary 15.3.10 (1)) with `Θ = Λ ∘ f` compact branched and an orientation
  `T̂` represented by oriented tame structures of dimension `m + 1`) whose orientation is the
  canonical one for `(f, o)`: `IsCanonicalFor P.Λ o (m + 1) P.T` (Definition 15.4.2 / Theorem
  15.4.1, `#print`ed); `∫_{(Λ∘f, o)} ω` is `P.integral ω`.  For `k = 0`, the project's
  `PointPerturbation A f` with `PointPerturbation.IsCanonical` and the weighted count `P.count`.
- "there is a well-defined `Φ`": (a) such a perturbation exists (so that `Φ` is defined), and
  (b) there is `Φ : H^k_dR(X) → ℝ` with `Φ([ω]) = ∫_P ω` for every closed `ω` and every such `P`.
  Linearity of `Φ` is not stated.
- Effective version (also the separate item V15_49): under (LUC) (`A.X.IsLUC`), the same with
  `P.integralEff` (`∮`, Definition 9.5.6 (2)) and `P.countEff`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V15_37
open Polyfold Polyfold.SBLocalization

/-- The class `[ω] ∈ H^k_dR(X)` of a closed form. -/
noncomputable def cls (A : SEP.{0}) (k : ℕ) (ω : A.baseEP.epFormsInfty k)
    (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD k)) : A.baseEP.epDeRham k :=
  Submodule.Quotient.mk ⟨ω, hω⟩

/-- Corollary 15.4.4: `Φ_{(f,o)}` (and, under (LUC), `Φ^eff_{(f,o)}`) is well defined in the
degree `k` equal to the index. -/
def B : Prop :=
  ∀ (A : SEP.{0}) [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × A.Obj)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace A.P (Prod.snd : (Fin n → ℝ) × A.Obj → A.Obj))],
    (∀ x : A.Obj, A.X.PObj.degIndex x = 0) → A.X.HasParacompactOrbitSpace →
    ∀ (f : A.Obj → A.W) (hF : A.E.IsScFredholmSectionFunctor f),
      A.E.HasCompactSolutionSetEp f →
    ∀ (hsec : A.B.HasScPlusSectionsThrough)
      (o : (y : A.Obj) → (hy : y ∈ A.X.PObj.smoothSet) → Orx f hF.2 y hy),
      IsSectionOrientation f hF.2 o → A.E.IsOrInvariant hF hsec o →
      -- index `m + 1 ≥ 1`
      (∀ m : ℕ, (∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ)) →
        (∃ P : OrientedRegularPerturbation A f m, IsCanonicalFor P.Λ hF.2 hsec o (m + 1) P.T) ∧
        (∃ Φ : A.baseEP.epDeRham (m + 1) → ℝ,
          ∀ P : OrientedRegularPerturbation A f m, IsCanonicalFor P.Λ hF.2 hsec o (m + 1) P.T →
          ∀ (ω : A.baseEP.epFormsInfty (m + 1)) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD _)),
            Φ (cls A (m + 1) ω hω) = P.integral ω) ∧
        (∀ hL : A.X.IsLUC, ∃ Φ : A.baseEP.epDeRham (m + 1) → ℝ,
          ∀ P : OrientedRegularPerturbation A f m, IsCanonicalFor P.Λ hF.2 hsec o (m + 1) P.T →
          ∀ (ω : A.baseEP.epFormsInfty (m + 1)) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD _)),
            Φ (cls A (m + 1) ω hω) = P.integralEff hL ω)) ∧
      -- index `0`
      ((∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x 0) →
        (∃ P : PointPerturbation A f, P.IsCanonical hF.2 hsec o) ∧
        (∃ Φ : A.baseEP.epDeRham 0 → ℝ,
          ∀ P : PointPerturbation A f, P.IsCanonical hF.2 hsec o →
          ∀ (ω : A.baseEP.epFormsInfty 0) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD 0)),
            Φ (cls A 0 ω hω) = P.count ω) ∧
        (∀ hL : A.X.IsLUC, ∃ Φ : A.baseEP.epDeRham 0 → ℝ,
          ∀ P : PointPerturbation A f, P.IsCanonical hF.2 hsec o →
          ∀ (ω : A.baseEP.epFormsInfty 0) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD 0)),
            Φ (cls A 0 ω hω) = P.countEff hL ω))

end RoundTrip.V15_37
