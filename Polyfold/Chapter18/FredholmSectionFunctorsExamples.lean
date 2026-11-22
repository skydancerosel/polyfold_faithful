import Polyfold.Chapter18.FredholmSectionFunctors
import Polyfold.Chapter18.ModelTransfer
import Polyfold.Chapter17.StrongBundleStructuresExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.1, p. 844: **a non-degenerate witness for Definition 18.1.1 and Remark 18.1.2** on the
reflection bundle of Chapter 17 (`StrongBundleStructuresExamples.lean`).  Numbers and pages are
the 2021 text's.

# The diagonal section of the reflection bundle

`C = ℤ/2 ⋉ ℝ`, `μ(x) = ℝ`, the generator `−1` acting by `x ↦ −x` on objects and `v ↦ −v` on the
fibres.  The section functor `f(x) = (x, x)` (`reflDiag`) is `ℤ/2`-equivariant: `−1` sends
`f(x) = (x, x)` to `(−x, −x) = f(−x)`.  Its representative in the strong bundle uniformizer
`Ψ̄ : ℤ/2 ⋉ (ℝ × ℝ) → E` is the graph section `q ↦ (q, q)` of the identity
(`localRep_reflDiag`), a linear sc-Fredholm section of index `0` with the single zero `q = 0`.

* `reflDiag`, `localRep_reflDiag`, `isScFredholmSectionFunctor_reflDiag` (Definition 18.1.1),
  `isScFredholmSectionFunctorTame_reflDiag` (its tame form), `reflDiag_model` (Remark 18.1.2 (a):
  `f^Ψ̄_Ψ` is an sc-Fredholm and tame sc-Fredholm section functor on the model with two copies of
  `Ψ̄`, whose morphisms include the non-trivial `(0, (−1, 0), 0)`), `reflDiag_germs` (the germ
  condition of Remark 18.1.2 (c)).
* Non-degeneracy (`reflDiag_nondegenerate`): `f` is not the zero section, the isotropy `−1` of
  `0` acts non-trivially on the fibre, and the solution set of the representative is `{0}`.
* The solution set (`ModelTransfer.lean`): `S_f = {0}` (`reflDiag_zeroSet`), and the orbit space of
  the model solution set is compact (`isCompact_reflDiag_modelSolutionSet`, by
  `isCompact_zeroSet_iff`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace GCT.VectorBundle.ReflectionBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor TrivialBundle
  StrongBundleUniformizerConstruction StrongBundleUniformizerData StrongPolyfoldBundleConstruction

/-- **The section functor `f(x) = (x, x)`** of the reflection bundle `P : E → ℤ/2 ⋉ ℝ`. -/
def reflDiag : reflV.SectionFunctor where
  toFun x := reflMu.objMk x x
  base_toFun _ := rfl
  toFun_tgt φ := by
    obtain ⟨g, x⟩ := φ
    rfl

/-- The representative of `f` in `Ψ̄` is the graph section `q ↦ (q, q)` of the identity. -/
theorem localRep_reflDiag : reflUnifData.localRep reflDiag = graphSection (fun q => q) := by
  funext q
  exact (reflUnifData.localRep_eq_iff reflDiag q _).2 rfl

/-- **Definition 18.1.1 holds for `f`** (every `F̄(x) = {Ψ̄}`, and `f_Ψ̄` is the graph section of
`id`, sc-Fredholm by Chapter 3). -/
theorem isScFredholmSectionFunctor_reflDiag : reflQ.IsScFredholmSectionFunctor reflDiag := by
  intro α Ψ hΨ
  obtain rfl : Ψ = reflUnif := hΨ
  change reflUnifData.B.IsScFredholmSection (reflUnifData.localRep reflDiag)
  rw [localRep_reflDiag]
  exact (isScFredholmSection_graphSection_wholeChart contDiff_id).isScFredholmSection

/-- The tame form of Definition 18.1.1 holds for `f`. -/
theorem isScFredholmSectionFunctorTame_reflDiag :
    reflQ.IsScFredholmSectionFunctorTame reflDiag := by
  intro α Ψ hΨ
  obtain rfl : Ψ = reflUnif := hΨ
  change reflUnifData.B.IsScFredholmSectionTame (reflUnifData.localRep reflDiag)
  rw [localRep_reflDiag]
  exact (isScFredholmSectionTame_graphSection_wholeChart contDiff_id).isScFredholmSectionTame

/-- **Remark 18.1.2 (a) on the witness**: on the model with two copies of `Ψ̄`, `f^Ψ̄_Ψ` is an
sc-Fredholm section functor and a tame sc-Fredholm section. -/
theorem reflDiag_model :
    (reflQ.modelEpStrongBundle reflPair.Ψ).IsScFredholmSectionFunctor
        (reflQ.modelSection reflPair.Ψ reflDiag) ∧
      (reflQ.modelSEP reflPair.Ψ).B.IsScFredholmSectionTame
        (reflQ.modelSection reflPair.Ψ reflDiag) :=
  ⟨(reflQ.remark_18_1_2_a_model reflDiag reflPair).2 isScFredholmSectionFunctor_reflDiag,
    (reflQ.remark_18_1_2_a_model_tame reflDiag reflPair).2
      isScFredholmSectionFunctorTame_reflDiag⟩

/-- `F̄(x) ≠ ∅` for every `x`. -/
theorem reflQ_hasStrongBundleUniformizers : reflQ.HasStrongBundleUniformizers :=
  fun _ => ⟨reflUnif, rfl⟩

/-- **Remark 18.1.2 (c) on the witness**: `f` is sc-smooth, regularizing, and has sc-Fredholm
germs over every smooth point. -/
theorem reflDiag_germs :
    reflQ.IsScSmoothSectionFunctor reflDiag ∧ reflQ.IsRegularizing reflDiag ∧
      reflQ.HasFredholmGerms reflDiag :=
  (reflQ.remark_18_1_2_c reflDiag reflQ_hasStrongBundleUniformizers).1
    isScFredholmSectionFunctor_reflDiag

/-- **Non-degeneracy**: `f(x) ≠ 0` for `x ≠ 0`, the isotropy `−1` of `0` acts on the fibre
`μ(0) = ℝ` by `v ↦ −v ≠ v` for `v ≠ 0`, and the representative vanishes exactly at `0`. -/
theorem reflDiag_nondegenerate :
    (∀ x : Fin 1 → ℝ, x ≠ 0 → reflDiag.toFun x ≠ reflMu.objMk x 0) ∧
      (∀ v : Fin 1 → ℝ, v ≠ 0 → reflV.map ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) v ≠ v) ∧
      {q : Fin 1 → ℝ | (reflUnifData.localRep reflDiag q).2 = 0} = {0} := by
  refine ⟨fun x hx h => hx (eq_of_heq (Sigma.mk.inj_iff.1 h).2), fun v hv => reflV_map_ne 0 hv, ?_⟩
  rw [localRep_reflDiag]
  rfl

/-- **The solution set `S_f = {0}`**. -/
theorem reflDiag_zeroSet : reflDiag.zeroSet = {0} := by
  ext x
  exact ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.1 h).2, fun h => by subst h; rfl⟩

/-- `|S_{f^Ψ̄_Ψ}|` is compact in the model with two copies of `Ψ̄` (from `|S_f| = {[0]}`). -/
theorem isCompact_reflDiag_modelSolutionSet :
    IsCompact ((reflQ.modelSEP reflPair.Ψ).X.π '' reflQ.modelSolutionSet reflPair.Ψ reflDiag) := by
  refine (reflQ.isCompact_zeroSet_iff reflPair.Ψ reflDiag reflPair.cover).1 ?_
  rw [reflDiag_zeroSet, image_singleton]
  exact isCompact_singleton

end GCT.VectorBundle.ReflectionBundle

end Polyfold
