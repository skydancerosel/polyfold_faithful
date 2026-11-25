import Polyfold
/-! Blind formalization of V15_36 (the Springer 2021 book, Part II, §15.4, Theorem 15.4.3,
pp. 702–703; 2017: Theorem 15.7): compactness, branching and Stokes for `Λ ∘ f`.

Text: `X` tame, `(f, o)` oriented sc-Fredholm of index `k` with `|S_f|` compact, `(N, U)`
controlling compactness, `Λ` with dom-supp in `U`, (1) `N(Λ) ≤ 1`, (2) `T(f,Λ)` onto on the
support, (3) good position at the support points in `∂X`.  Then `Θ = Λ ∘ f` is a compact tame
branched ep⁺-subgroupoid, oriented by `o` (Theorem 15.4.1), and `∫_Θ dω = ∫_{∂Θ} ω` for `ω` of
degree `k − 1`; with the local unique continuation property also for `∮`.

Choices:
- Setting: universe 0, `A : SEP.{0}`, `A.X.IsTame`.  The project's `IsSectionOrientation` needs
  the instances `ParacompactSpace ((Fin n → ℝ) × Obj)` and `ParacompactSpace` of the pull-back
  `(Fin n → ℝ) × Obj ×_Obj W` for all `n`; they are not inferred for a general `SEP`, so B takes
  them as instance arguments (a vocabulary presupposition, not a hypothesis of the text).
- `f`: `IsScFredholmSectionFunctor` (its second component is `A.B.IsScFredholmSection f`, `#print`ed); `|S_f|` compact:
  `HasCompactSolutionSetEp`; `(N, U)`: `ControlsCompactness` (Definition 15.3.1).
- "`(f, o)` oriented": `o : y ↦ o_y ∈ Or_y^f` on the smooth objects (the project's `Orx`), an
  orientation of the section in Part I's sense (`IsSectionOrientation`, Definition 6.6.16:
  continuous over orientable neighbourhoods) which is invariant under morphisms
  (`EpStrongBundle.IsOrInvariant`, the invariance clause of Definition 12.5.4) — the data the
  project's Chapter 15 orientation notions take.  These need `hsec : A.B.HasScPlusSectionsThrough`
  (sc⁺-sections through every smooth fibre point) as an argument; I add it as a hypothesis, a
  presupposition of the vocabulary, not of the text (doubt: it is an extra hypothesis).
- "index `k`": `A.B.IsIndexAt f x k` (Definition 6.2.1) at every smooth object `x`.
- `Λ`: an sc⁺-multisection functor (`IsScPlusMultisection`; structurability not assumed),
  `domSupp Λ ⊆ U`, (1) `pointwiseNorm N Λ x ≤ 1` for all `x`, (2) `IsTransversal f Λ`
  (Definition 15.2.1), (3) `IsGoodPositionAt f Λ x` (Definition 15.2.4) at every `x ∈ ∂X` with
  `Λ(f(x)) > 0`.
- Conclusions, for every `k`: `Θ = z ↦ Λ(f(z))` is branched (`IsBranchedEpSubgroupoid`), compact
  (`IsCompactBranched`), tame (`IsTameBranched`), and "oriented by `o` (Theorem 15.4.1)": there
  is `T̂` which is the canonical orientation of dimension `k` (the project's `IsCanonicalFor Λ o k`,
  `#print`ed: `T̂` is an orientation of `Θ` (Definition 9.3.2) and near every point of the support
  it is represented by a tame structure described by kernels, sheets `{f = sᵢ}` of dimension `k`
  oriented by the `o_{i,y}` induced by `o`).
- Stokes, for `k = m + 1 ≥ 1` (for `k = 0` there are no forms of degree `k − 1`): the oriented
  `Θ̂` is packaged as the project's `OrientedSolution A f m` `P` (`#print`ed: an sc⁺-multisection
  `P.Λ`, `P.T`, with `Θ` branched, compact, `P.T` an orientation, represented near every support
  point by an oriented tame structure of dimension `m + 1`) with `P.Λ = Λ` and `P.T` canonical.
  `∫_Θ dω` is `P.integral (d ω)` (Definition 9.5.6 (1); `d = epFormsInftyD`, forms
  `Ω^m_{ep,∞}(X)`); `∫_{∂Θ} ω` is the total mass `μ^{∂Θ̂}_ω(|supp ∂Θ|)` of the project's boundary
  measure of Theorem 9.5.15 (`EP.boundaryMeasure` for `m ≥ 1`, `EP.boundaryBranchedMeasureDim1`
  for `m = 0`), my `bdryIntegral`.  For `∮` (under `A.X.IsLUC`, Definition 7.2.18):
  `P.integralEff` and the effective boundary measures (`EP.boundaryMeasureEff`,
  `EP.boundaryBranchedMeasureEffDim1`); the latter needs the local structures to carry (LUC)
  representations, which I assert as part of the conclusion (`∃` over that proof).
- Nothing looks doubtful to me (apart from the extra `hsec` above).
-/
namespace RoundTrip.V15_36
open Polyfold Polyfold.SBLocalization

/-- `∫_{∂Θ} ω`, the total boundary measure of Theorem 9.5.15 (dimension `m + 1`). -/
noncomputable def bdryIntegral {A : SEP.{0}} {f : A.Obj → A.W} :
    (m : ℕ) → OrientedSolution A f m → A.baseEP.epFormsInfty m → ℝ
  | 0, P, ω =>
      (A.baseEP.boundaryBranchedMeasureDim1 P.isBranched P.isCompact P.isOrientation P.loc ω)
        Set.univ
  | m + 1, P, ω =>
      (A.baseEP.boundaryMeasure (Nat.succ_pos m) P.isBranched P.isCompact P.isOrientation P.loc
        ω) Set.univ

/-- The effective Stokes formula `∮_Θ dω = ∮_{∂Θ} ω` for `P` of dimension `m + 1`. -/
def EffStokes {A : SEP.{0}} {f : A.Obj → A.W} (hL : A.X.IsLUC) :
    (m : ℕ) → OrientedSolution A f m → Prop
  | 0, P =>
      ∃ hloc : (∀ x ∈ EpGroupoid.supp (fun z => ((P.Λ (f z) : ℚ≥0) : ℚ)),
          ∃ C, EpGroupoid.OrientedTameStructure.Represents C P.T ∧ C.rep.HasLUC),
        ∀ ω : A.baseEP.epFormsInfty 0,
          P.integralEff hL (A.baseEP.epFormsInftyD 0 ω) =
            (A.baseEP.boundaryBranchedMeasureEffDim1 P.isBranched P.isCompact P.isOrientation
              hloc ω) Set.univ
  | m + 1, P =>
      ∀ ω : A.baseEP.epFormsInfty (m + 1),
        P.integralEff hL (A.baseEP.epFormsInftyD (m + 1) ω) =
          (A.baseEP.boundaryMeasureEff (Nat.succ_pos m) hL P.isBranched P.isCompact
            P.isOrientation P.loc ω) Set.univ

/-- Theorem 15.4.3. -/
def B : Prop :=
  ∀ (A : SEP.{0}) [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × A.Obj)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace A.P (Prod.snd : (Fin n → ℝ) × A.Obj → A.Obj))],
    A.X.IsTame →
    ∀ (f : A.Obj → A.W) (hF : A.E.IsScFredholmSectionFunctor f)
      (hsec : A.B.HasScPlusSectionsThrough)
      (o : (y : A.Obj) → (hy : y ∈ A.X.PObj.smoothSet) → Orx f hF.2 y hy),
      IsSectionOrientation f hF.2 o → A.E.IsOrInvariant hF hsec o →
    ∀ k : ℕ, (∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x (k : ℤ)) →
      A.E.HasCompactSolutionSetEp f →
    ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
    ∀ Λ : A.W → ℚ≥0, IsScPlusMultisection A Λ → domSupp Λ ⊆ U →
      -- (1), (2), (3)
      (∀ x, pointwiseNorm N Λ x ≤ 1) → IsTransversal f Λ →
      (∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x) →
        -- `Θ` compact tame branched, oriented by `o`
        (A.X.IsBranchedEpSubgroupoid (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) ∧
          A.X.IsCompactBranched (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) ∧
          A.X.IsTameBranched (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) ∧
          ∃ T, IsCanonicalFor Λ hF.2 hsec o k T) ∧
        -- Stokes, `k = m + 1`
        (∀ m : ℕ, k = m + 1 →
          ∃ P : OrientedSolution A f m, P.Λ = Λ ∧ IsCanonicalFor Λ hF.2 hsec o k P.T ∧
            (∀ ω : A.baseEP.epFormsInfty m,
              P.integral (A.baseEP.epFormsInftyD m ω) = bdryIntegral m P ω) ∧
            ∀ hL : A.X.IsLUC, EffStokes hL m P)

end RoundTrip.V15_36
