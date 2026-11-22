import Polyfold.Chapter18.ImplicitFunctionTheorem
import Polyfold.Chapter18.OpenSubcategory
import Polyfold.Chapter17.BranchedSupport

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.1, pp. 845–846: **Theorem 18.1.5 (implicit function theorem) on the full subcategory `C_U`**,
and the Note after it.

# Theorem 18.1.5 on `C_U`

## The text, paraphrased

(Theorem 18.1.5) If the smooth object `α` has `f(α) = 0`, `f'(α)` is onto and its kernel is in
good position to the boundary, there is an open neighbourhood `U` of `|α|` in `|C|` such that
(1) `Θ : C_U → {0, 1}`, `Θ(β) = 1` iff `f(β) = 0`, is a tame orbifold-type ep⁺-subcategory of
`C_U`, and (2) at every `β` of `C_U` with `Θ(β) = 1`, `f'(β)` is onto with kernel in good
position.  (Note) `|supp(Θ)|` is a smooth orbifold with boundary with corners.

## What is formalized

* **`theorem_18_1_5_subcategory`**: the statement on the polyfold `C_U`
  (`OpenSubcategory.lean`): there is a natural representation `U(x₀)` in the model `X_Ψ` such
  that `U = |Γ|(π(U(x₀)))` is an open neighbourhood of `|α|` and
  (1) `Θ|C_U` is a branched ep⁺-subcategory of `C_U` (Definition 17.5.1 for `(F_U, M)`), of
  orbifold-type (Definition 17.5.4 (2)) and tame (Definition 17.5.4 (3)), with `Θ|C_U(β) = 1` iff
  `f(β) = 0`;
  (2) every `β` of `C_U` with `Θ(β) = 1` is isomorphic to some `Γ(y)`, `y ∈ U(x₀)`, at which
  `(f^Ψ̄, Λ₀)` is in good position (Definition 15.2.4).
* **`theorem_18_1_5_note`**: the Note, from Proposition 17.5.5 (2) for `Θ|C_U` on `C_U`: for
  every covering family of `C_U`, `supp(Γ^*Θ|C_U)` is an ep-subgroupoid and a smooth submanifold of
  the model whose orbit space is homeomorphic to `|supp(Θ|C_U)|`.

## Readings

* `C_U` is the polyfold `C.openSub U` with the structure `openSubConstruction` (the uniformizers
  of `C` restricted to the open sets `Ψ⁻¹(π⁻¹ U)`), and `Θ` on `C_U` is `Θ|C_U`.
* The hypothesis on `α` is read as in `theorem_18_1_5_model` (`ImplicitFunctionTheorem.lean`):
  `α = Ψ_λ(q₀)` for a member `Ψ̄_λ` of a family of strong bundle uniformizers, and `f_Ψ̄_λ` is in
  good position at `q₀` (Definition 3.6.6 in a tame chart); `hft` is the tame germ data of the
  standing reading, as in `theorem_18_1_5_model`.
* (2) is read in the model, as in `theorem_18_1_5_model`: `f'(β)` for `β ≅ Γ(y)` is the
  linearization of `f^Ψ̄` at `y` (`surjective_linearization_iff` for its surjectivity).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace GCT.VectorBundle

variable {C : GCT.{u}} {V : C.VectorBundle}

/-- `Θ ≥ 0`. -/
theorem SectionFunctor.zeroIndicator_nonneg (f : V.SectionFunctor) (β : C.Obj) :
    0 ≤ f.zeroIndicator β := by
  rcases f.isOrbifoldTypeBranched_zeroIndicator β with h | h <;> rw [h]; norm_num

namespace StrongPolyfoldBundleConstruction

variable {S : C.PolyfoldConstruction} (Q : V.StrongPolyfoldBundleConstruction S) {ι : Type u}
  {Ψb : ι → Q.Unif} {f : V.SectionFunctor}

open SBLocalization PolyfoldConstruction

/-- **Theorem 18.1.5 (implicit function theorem) on `C_U`**, p. 846, with tame germ data (`hft`,
the standing reading) as in `theorem_18_1_5_model`.  Let `f` be an sc-Fredholm section functor,
`Ψ̄_λ` a member of a family `Ψ̄` of strong bundle uniformizers and `q₀` a point with
`f(Ψ_λ(q₀)) = 0` at which `f_Ψ̄_λ` is in good position (the reading of "`f'(α)` onto with kernel in
good position to the boundary").  Then there are a natural representation `U(x₀)` at `x₀ = (λ, q₀)`
in the model `X_Ψ` and the open neighbourhood `U = |Γ|(π(U(x₀)))` of `|α|` in `|C|` such that, on
the polyfold `C_U` (`openSubConstruction`):
(1) `Θ|C_U` (`Θ(β) = 1` iff `f(β) = 0`) is a branched ep⁺-subcategory of `C_U`, of orbifold-type
and tame;
(2) every `β` of `C_U` with `Θ(β) = 1` is isomorphic to `Γ(y)` for some `y ∈ U(x₀)` at which
`(f^Ψ̄, Λ₀)` is in good position (Definition 15.2.4). -/
theorem theorem_18_1_5_subcategory (hf : Q.IsScFredholmSectionFunctor f)
    (hft : Q.IsScFredholmSectionFunctorTame f) {i : ι} {q₀ : (Ψb i).1.base.O}
    (h0 : (S.modelFunctor (Q.modelBase Ψb)).obj ⟨i, q₀⟩ ∈ f.zeroSet)
    (hgp : (Ψb i).1.B.IsGoodPositionGermTame ((Ψb i).1.localRep f) q₀) :
    ∃ R : (Q.modelSEP Ψb).X.NaturalRep ⟨i, q₀⟩, ∃ U : Set C.toGroupoidStr.OrbitSpace,
      ∃ hU : IsOpen U,
      U = (S.modelFunctor (Q.modelBase Ψb)).orbitMap ''
        ((S.modelEP (Q.modelBase Ψb)).X.π '' R.U) ∧
      C.toGroupoidStr.π ((S.modelFunctor (Q.modelBase Ψb)).obj ⟨i, q₀⟩) ∈ U ∧
      (S.openSubConstruction hU).IsBranchedSubcategory (restrictTheta U f.zeroIndicator) ∧
      (C.openSub U).IsOrbifoldTypeBranched (restrictTheta U f.zeroIndicator) ∧
      (S.openSubConstruction hU).IsTameSubcategory (restrictTheta U f.zeroIndicator) ∧
      (∀ β : (C.openSub U).Obj, restrictTheta U f.zeroIndicator β = 1 ↔
        (show C.objOver U from β).1 ∈ f.zeroSet) ∧
      ∀ β : (C.openSub U).Obj, restrictTheta U f.zeroIndicator β = 1 →
        ∃ y ∈ R.U, C.toGroupoidStr.Isomorphic ((S.modelFunctor (Q.modelBase Ψb)).obj y)
            (show C.objOver U from β).1 ∧
          (S.modelFunctor (Q.modelBase Ψb)).obj y ∈ f.zeroSet ∧
          SBLocalization.IsGoodPositionAt (A := Q.modelSEP Ψb) (Q.modelSection Ψb f)
            (zeroMultisection (Q.modelSEP Ψb)) y := by
  obtain ⟨R, hopen, hmem, ho, -, htame, hgpos, -, -⟩ := Q.theorem_18_1_5_model hf hft h0 hgp
  set Γ := S.modelFunctor (Q.modelBase Ψb)
  set U := Γ.orbitMap '' ((S.modelEP (Q.modelBase Ψb)).X.π '' R.U) with hUdef
  have hΘ := f.isFunctorial_zeroIndicator
  -- every object over `U` is isomorphic to some `Γ(y)`, `y ∈ U(x₀)`
  have hover : ∀ α ∈ C.objOver U, ∃ y ∈ R.U, C.toGroupoidStr.Isomorphic (Γ.obj y) α := by
    intro α hα
    obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := hα
    refine ⟨y, hy, (C.toGroupoidStr.π_eq_π_iff).1 ?_⟩
    rw [← h, GroupoidFunctor.orbitMap_π]
  have hiso : ∀ {β β'}, C.toGroupoidStr.Isomorphic β β' → β ∈ f.zeroSet → β' ∈ f.zeroSet := by
    rintro β β' ⟨φ, rfl, rfl⟩ hz
    rw [← f.zeroIndicator_pos_iff] at hz ⊢
    rwa [← hΘ φ]
  have hloc : ∀ α ∈ C.objOver U, ∀ Ψ ∈ S.F α, ∀ q ∈ Ψ.obj ⁻¹' C.objOver U,
      0 < f.zeroIndicator (Ψ.obj q) →
      ∃ B : Ψ.ep.LocalBranchingStructure (f.zeroIndicator ∘ Ψ.obj) q,
        ∀ k, Ψ.P.HasTameInducedStructure (B.M k) := by
    intro α _ Ψ hΨ q hq hpos
    obtain ⟨y, hy, hyq⟩ := hover _ hq
    have hz : Γ.obj y ∈ f.zeroSet :=
      hiso hyq.symm ((f.zeroIndicator_pos_iff _).1 hpos)
    obtain ⟨T⟩ := htame y hy hz
    obtain ⟨j, q'⟩ := y
    obtain ⟨B₁, hB₁⟩ := localBranching_summand (S := S) (Ψ := Q.modelBase Ψb)
      (Θ := f.zeroIndicator) j q' T.toLocalBranchingStructure
    obtain ⟨φ, hs, ht⟩ := hyq.symm
    let a : S.Tr ⟨Ψ, α, hΨ⟩ (Q.modelBase Ψb j) := ⟨q, φ, q', hs, ht⟩
    obtain ⟨B₂, hB₂⟩ := localBranching_of_tr hΘ a B₁
    exact ⟨B₂, hB₂ (hB₁ T.hasTameInducedStructure)⟩
  obtain ⟨hbr, htm⟩ := openSub_isBranchedSubcategory (S := S) hopen f.zeroIndicator_nonneg hΘ hloc
  refine ⟨R, U, hopen, rfl, hmem, hbr, isOrbifoldTypeBranched_restrictTheta U ho, htm,
    fun β => f.zeroIndicator_eq_one_iff _, fun β hβ => ?_⟩
  obtain ⟨y, hy, hyβ⟩ := hover _ (show C.objOver U from β).2
  have hz : Γ.obj y ∈ f.zeroSet :=
    hiso hyβ.symm ((f.zeroIndicator_eq_one_iff _).1 hβ)
  exact ⟨y, hy, hyβ, hz, hgpos y hy hz⟩

/-- **The Note after Theorem 18.1.5** (p. 846) on `C_U`: for a tame orbifold-type branched
ep⁺-subcategory `Θ|C_U` of `C_U` (as produced by `theorem_18_1_5_subcategory`) and every
covering family `Ψ` of `C_U`, `supp(Γ_Ψ^*Θ|C_U)` is an ep-subgroupoid and a smooth submanifold of
the model `X_Ψ` whose orbit space is homeomorphic to `|supp(Θ|C_U)|` through `|Γ_Ψ|`
(Proposition 17.5.5 (2), Proposition 9.1.9 (2)): `|supp(Θ|C_U)|` is a smooth orbifold. -/
theorem theorem_18_1_5_note {U : Set C.toGroupoidStr.OrbitSpace} (hU : IsOpen U)
    (hbr : (S.openSubConstruction hU).IsBranchedSubcategory (restrictTheta U f.zeroIndicator))
    (c : (S.openSubConstruction hU).CoveringFamily) :
    ∃ hA : ((S.openSubConstruction hU).modelEP c.Ψ).X.IsEpSubgroupoid
        (EpGroupoid.supp ((S.openSubConstruction hU).modelPull c.Ψ
          (restrictTheta U f.zeroIndicator))),
      ((S.openSubConstruction hU).modelEP c.Ψ).X.PObj.IsSmoothSubmanifold
          (EpGroupoid.supp ((S.openSubConstruction hU).modelPull c.Ψ
            (restrictTheta U f.zeroIndicator))) ∧
        haveI := ((S.openSubConstruction hU).modelEP c.Ψ).X.PObj.paracompactSpace_subtype
          (EpGroupoid.supp ((S.openSubConstruction hU).modelPull c.Ψ
            (restrictTheta U f.zeroIndicator)))
        ∃ e : (EpGroupoid.subEpGroupoid hA).OrbitSpace ≃ₜ
            (C.openSub U).toGroupoidStr.orbitSupp (restrictTheta U f.zeroIndicator),
          ∀ x : EpGroupoid.supp ((S.openSubConstruction hU).modelPull c.Ψ
              (restrictTheta U f.zeroIndicator)),
            (e ((EpGroupoid.subEpGroupoid hA).π x) : (C.openSub U).toGroupoidStr.OrbitSpace) =
              (C.openSub U).toGroupoidStr.π
                (((S.openSubConstruction hU).modelFunctor c.Ψ).obj x.1) :=
  ((S.openSubConstruction hU).proposition_17_5_5_two hbr
    (isOrbifoldTypeBranched_restrictTheta U f.isOrbifoldTypeBranched_zeroIndicator)).1 c

end StrongPolyfoldBundleConstruction

end GCT.VectorBundle

end Polyfold
