import Polyfold
/-! Blind formalization of V15_49 (the Springer 2021 book, Part II, §15.4, Corollary 15.4.4,
p. 703; 2017: Corollary 15.2): the effective version.

Text: with the local unique continuation property,
`Φ^eff_{(f,o)}([ω]) = ∮_{(Λ∘f, o)} ω` is well defined.

Choices:
- Standing hypotheses of Corollary 15.4.4 exactly as in my `V15_37.lean`: universe 0,
  `A : SEP.{0}`, `d_X ≡ 0`, `HasParacompactOrbitSpace`, `f` an sc-Fredholm section functor with
  `|S_f|` compact, `o` an orientation (`IsSectionOrientation` and `IsOrInvariant`; the vocabulary
  needs `hsec : HasScPlusSectionsThrough` and paracompactness instances, taken as arguments —
  vocabulary presuppositions, not hypotheses of the text), constant Fredholm index `k`, stated
  for `k = m + 1 ≥ 1` and for `k = 0`.
- "the local unique continuation property": `A.X.IsLUC` (Definition 7.2.18).
- "a regular perturbation with the orientation from `o`": `OrientedRegularPerturbation A f m`
  with `IsCanonicalFor P.Λ o (m + 1) P.T` (for `k = 0`: `PointPerturbation` with
  `PointPerturbation.IsCanonical`), as in V15_37.  `∮_{(Λ∘f, o)} ω` is `P.integralEff`
  (Definition 9.5.6 (2)), for `k = 0` `P.countEff`.
- "well defined": such a perturbation exists, and there is `Φ^eff : H^k_dR(X) → ℝ` (the
  project's `EP.epDeRham`) with `Φ^eff([ω]) = ∮_P ω` for every closed `ω` and every such `P`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V15_49
open Polyfold Polyfold.SBLocalization

/-- The class `[ω] ∈ H^k_dR(X)` of a closed form. -/
noncomputable def cls (A : SEP.{0}) (k : ℕ) (ω : A.baseEP.epFormsInfty k)
    (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD k)) : A.baseEP.epDeRham k :=
  Submodule.Quotient.mk ⟨ω, hω⟩

/-- Corollary 15.4.4, effective version: under (LUC), `Φ^eff_{(f,o)}` is well defined in the
degree `k` equal to the index. -/
def B : Prop :=
  ∀ (A : SEP.{0}) [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × A.Obj)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace A.P (Prod.snd : (Fin n → ℝ) × A.Obj → A.Obj))],
    (∀ x : A.Obj, A.X.PObj.degIndex x = 0) → A.X.HasParacompactOrbitSpace →
    ∀ hL : A.X.IsLUC,
    ∀ (f : A.Obj → A.W) (hF : A.E.IsScFredholmSectionFunctor f),
      A.E.HasCompactSolutionSetEp f →
    ∀ (hsec : A.B.HasScPlusSectionsThrough)
      (o : (y : A.Obj) → (hy : y ∈ A.X.PObj.smoothSet) → Orx f hF.2 y hy),
      IsSectionOrientation f hF.2 o → A.E.IsOrInvariant hF hsec o →
      -- index `m + 1 ≥ 1`
      (∀ m : ℕ, (∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ)) →
        (∃ P : OrientedRegularPerturbation A f m, IsCanonicalFor P.Λ hF.2 hsec o (m + 1) P.T) ∧
        ∃ Φ : A.baseEP.epDeRham (m + 1) → ℝ,
          ∀ P : OrientedRegularPerturbation A f m, IsCanonicalFor P.Λ hF.2 hsec o (m + 1) P.T →
          ∀ (ω : A.baseEP.epFormsInfty (m + 1)) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD _)),
            Φ (cls A (m + 1) ω hω) = P.integralEff hL ω) ∧
      -- index `0`
      ((∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x 0) →
        (∃ P : PointPerturbation A f, P.IsCanonical hF.2 hsec o) ∧
        ∃ Φ : A.baseEP.epDeRham 0 → ℝ,
          ∀ P : PointPerturbation A f, P.IsCanonical hF.2 hsec o →
          ∀ (ω : A.baseEP.epFormsInfty 0) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD 0)),
            Φ (cls A 0 ω hω) = P.countEff hL ω)

end RoundTrip.V15_49
