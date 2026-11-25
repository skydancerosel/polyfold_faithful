import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V18_52

set_option maxSynthPendingDepth 3

/-! Round trip for V18_52 (2021 Theorem 18.6.1, last sentence, p. 861; 2017: Theorem 18.8: an
orientation of `f` orients `Θ = Λ ∘ f`).

The item lists `theorem_18_6_1_oriented` (in a covering model `c`),
`theorem_18_6_1_oriented_modelFree` (`Λ` an sc⁺-multisection functor, (4) model-free) and the
witnesses `theorem_18_6_1_oriented_witness`, `theorem_18_6_1_oriented_witness_support`,
`isIndexAt_reflSingleModel` on the reflection bundle.  `A` is their conjunction at universe `0`.

## Comparison (main conjunct `theorem_18_6_1_oriented_modelFree`)

* **Hypotheses of `A` that `B` lacks.**  (i) `hidx`: `f` has Fredholm index `n` at every point of
  `supp(Γ̄^*Λ ∘ f^Ψ̄)` in the model `c`, for one `n` (the dimension of `Θ`); `B` (like the quoted
  sentence) has no index hypothesis, and nothing in `B` makes the index constant on the support.
  (ii) the model form `IsAuxNormFunctor N` against `B`'s printed `IsAuxNormBook N` (strictly
  weaker in the project, see V18_51).  The other hypotheses of `A` follow from `B`'s
  (`N(Λ) < h ≤ 1` gives `N(Λ) ≤ 1`; (4), `o`, `ho`, `hfT` are the same).  `main_partial` below
  proves `A`'s conclusion under `B`'s hypotheses plus (i), (ii).
* **The notion of "oriented".**  `A` produces an `OrientedSubcategory` (orientations of `Γ^*Θ` on
  every covering model, compatible with the comparison isomorphisms, pp. 820–821), described as
  the canonical orientation `T̂_((f^Ψ̄, Ψ̄^*o), Γ̄^*Λ)` in the model `c`.  `B` asks for a section
  `T̂Θ : C → Gr̂(C)` with `S.IsOrientationC hU Θ T̂Θ` (Definition 17.5.8 on `C` itself).  The
  project has no lemma passing from an `OrientedSubcategory` to an `IsOrientationC` section (it
  would descend the model orientations to the tangent category of `C`); this is substantial
  mathematics, not glue.
* **`B ⇒ A`** does not hold as a derivation: `A`'s hypotheses are weaker (no (3), only
  `N(Λ) ≤ 1`, no continuous `h`), and `A` names the orientation (canonical in the model `c`,
  `IsCanonicalFor`), which `B`'s bare existence cannot supply; the witnesses are concrete facts
  outside `B`. -/

namespace RoundTrip.V18_52
open Polyfold GCT.VectorBundle GCT.VectorBundle.StrongPolyfoldBundleConstruction

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_oriented.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_oriented_modelFree.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_6_1_oriented_witness) ∧
  (type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_6_1_oriented_witness_support) ∧
  (type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.isIndexAt_reflSingleModel)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_oriented.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_oriented_modelFree.{0},
    @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_6_1_oriented_witness,
    @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_6_1_oriented_witness_support,
    @Polyfold.GCT.VectorBundle.ReflectionBundle.isIndexAt_reflSingleModel⟩

/-- The main conjunct. -/
def Amain : Prop :=
  type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_oriented_modelFree.{0}

/-- **What the main conjunct gives under `B`'s hypotheses**, once the index hypothesis `hidx`
(for some covering model `c` and dimension `n`) and the model form `IsAuxNormFunctor N` are
added: an oriented branched ep⁺-subcategory (`OrientedSubcategory`, model reading) with
underlying `Θ = Λ ∘ f`.  `B` asks instead for an `IsOrientationC` section (Definition 17.5.8). -/
theorem main_partial (hM : Amain) :
    ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
      (Q : V.StrongPolyfoldBundleConstruction S)
      (hF : Q.HasStrongBundleUniformizers) (ht : S.IsTame)
      (hb : S.AdmitsModelBumpFunctions)
      (f : V.SectionFunctor) (hf : Q.IsScFredholmSectionFunctor f)
      (hfT : Q.IsScFredholmSectionFunctorTame f),
    ∀ (N : V.EObj → ENNReal) (U : Set C.toGroupoidStr.OrbitSpace),
      Q.IsAuxNormFunctor N → f.ControlsCompactness N U →
    ∀ (h : C.Obj → ℝ), (∀ α, 0 < h α ∧ h α ≤ 1) →
    ∀ Λ : V.EObj → ℚ≥0,
      Q.IsScPlusMultisectionFunctor Λ →
      (∀ α, GCT.VectorBundle.pointwiseNormFunctor N Λ α < ENNReal.ofReal (h α)) →
      GCT.VectorBundle.orbitDomSupp Λ ⊆ U →
      Q.IsInGeneralPositionFunctor f Λ →
    ∀ o : Q.OrSection hf hF, Q.IsOrientation hf hb ht hfT hF o →
    ∀ (c : Q.BundleCoveringFamily) (n : ℕ),
      (∀ x, 0 < Q.bundlePull c.Ψ Λ (Q.modelSection c.Ψ f x) →
        (Q.modelSEP c.Ψ).B.IsIndexAt (Q.modelSection c.Ψ f) x n) →
      ∃ O : S.OrientedSubcategory, O.Θ = (fun α => ((Λ (f.toFun α) : ℚ≥0) : ℚ)) := by
  intro C S V Q hF ht hb f hf hfT N U hN hcc h hh01 Λ hΛ h1 h2 h4 o ho c n hidx
  have hN1 : ∀ α, GCT.VectorBundle.pointwiseNormFunctor N Λ α ≤ 1 := fun α =>
    (h1 α).le.trans ((ENNReal.ofReal_le_ofReal (hh01 α).2).trans_eq ENNReal.ofReal_one)
  obtain ⟨O, hO, -⟩ := hM c ht hb hf hfT hF ho hN hcc hΛ hN1 h2 h4 hidx
  exact ⟨O, hO⟩

#rt_check RoundTrip.V18_52.main_partial [
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_oriented,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_oriented_modelFree,
  Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_6_1_oriented_witness,
  Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_6_1_oriented_witness_support,
  Polyfold.GCT.VectorBundle.ReflectionBundle.isIndexAt_reflSingleModel]

end RoundTrip.V18_52
