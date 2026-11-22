import Polyfold.Chapter18.FredholmSectionFunctorsExamples
import Polyfold.Chapter18.Linearization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.2, the paragraph after (18.3), p. 849: **a solution object is smooth**.  Numbers and pages
are the 2021 text's.

# Solution objects are smooth

## The text, paraphrased

(p. 849) For an sc-Fredholm section functor `f` of `P : E → C` the solution category `S_f` is the
full subcategory of the objects `α` with `f(α) = 0`.  Since `f` is regularizing, a solution
object is smooth.

## What is formalized

* `isSmoothObj_of_mem_zeroSet`: if `f(α) = 0` and `α = Ψ(q)` for a strong bundle uniformizer
  `Ψ̄ ∈ F̄(β)`, then `α` is smooth (Definition 17.1.31: every regularity `m`).  The proof is the
  text's: `f_Ψ̄(q) = 0` lies in `E_{m,m+1}` over `C_m` (`fiberZero_mem_doubleLevel`), and Remark
  18.1.2 (b) in the levels (`remark_18_1_2_b_levels`) gives the step `C_m → C_{m+1}`.
* `isSmoothObj_of_mem_zeroSet_of_isomorphic`: the same for `α ≅ Ψ(q)` (the zero set and
  smoothness are invariant under isomorphisms).
* **`solution_isSmoothObj`**: `f(α) = 0` and `F̄(α) ≠ ∅` give `α` smooth;
  **`zeroSet_subset_isSmoothObj`**: under the standing reading `F̄(α) ≠ ∅` for every `α`
  (`HasStrongBundleUniformizers`), `S_f ⊆ C_∞`.
* Witness (`reflDiag_zeroSet_subset_isSmoothObj`): the diagonal section `f(x) = (x, x)` of the
  reflection bundle over `ℤ/2 ⋉ ℝ`, whose solution object `0` has isotropy `ℤ/2` acting by
  `v ↦ −v` on the fibre.

## Reading

"`α` is smooth" is Definition 17.1.31 (`IsSmoothObj`: `α ∈ C_m` for every `m`, p. 765).  The
smoothness of `α` is read through a uniformizer whose image contains an object isomorphic to `α`;
`F̄(α) ≠ ∅` is the standing reading of Chapter 17 (`F(α) ≠ ∅`), and the weaker form
`α ≅ Ψ(q)` is what the proof uses.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open GroupoidalCategory GroupoidalCategory.BanachFunctor StrongBundleUniformizerConstruction
  StrongBundleUniformizerData PolyfoldConstruction

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  (Q : V.StrongPolyfoldBundleConstruction S) {f : V.SectionFunctor}

/-- **A solution object is smooth** (2021 p. 849, after (18.3)): if `f(α) = 0` and `α = Ψ(q)` for
a strong bundle uniformizer `Ψ̄ ∈ F̄(β)`, then `α ∈ C_m` for every `m`.  The step `C_m → C_{m+1}` is
Remark 18.1.2 (b) (`f` is regularizing), applied to `f_Ψ̄(q) = 0 ∈ E_{m,m+1}`. -/
theorem isSmoothObj_of_mem_zeroSet (hf : Q.IsScFredholmSectionFunctor f) {α β : C.Obj}
    {Ψ : V.StrongBundleUniformizer} (hΨ : Ψ ∈ Q.F β) {q : Ψ.base.O} (hq : Ψ.base.obj q = α)
    (hα : α ∈ f.zeroSet) : S.IsSmoothObj α := by
  have hiso : C.toGroupoidStr.Isomorphic ((Q.baseUnif ⟨Ψ, β, hΨ⟩).1.obj q) α :=
    hq ▸ GroupoidStr.isomorphic_refl _ _
  have h0 : IsZeroAt Ψ.p (Ψ.localRep f) q := isZeroAt_localRep hα hq
  intro m
  induction m with
  | zero =>
    rw [hasRegularity_iff _ hiso, MPolyfold.levelSet_zero]
    exact mem_univ _
  | succ m ih =>
    refine Q.remark_18_1_2_b_levels f hf hΨ hq m ih ?_
    rw [h0]
    exact Ψ.B.fiberZero_mem_doubleLevel ((hasRegularity_iff _ hiso m).1 ih)

/-- The zero set `S_f` is closed under isomorphisms: `f(α) = 0` and `α ≅ α'` give `f(α') = 0`. -/
theorem mem_zeroSet_of_isomorphic {α α' : C.Obj} (hα : α ∈ f.zeroSet)
    (h : C.toGroupoidStr.Isomorphic α α') : α' ∈ f.zeroSet := by
  obtain ⟨φ, hs, ht⟩ := h
  exact f.toFun_eq_zero_of_mor hs ht hα

/-- **A solution object is smooth**, for `α ≅ Ψ(q)` with `Ψ̄` a strong bundle uniformizer of the
construction. -/
theorem isSmoothObj_of_mem_zeroSet_of_isomorphic (hf : Q.IsScFredholmSectionFunctor f)
    {α : C.Obj} (Ψ : Q.Unif) {q : Ψ.1.base.O}
    (hiso : C.toGroupoidStr.Isomorphic (Ψ.1.base.obj q) α) (hα : α ∈ f.zeroSet) :
    S.IsSmoothObj α := by
  obtain ⟨β, hΨ⟩ := Ψ.2
  have h := Q.isSmoothObj_of_mem_zeroSet hf hΨ rfl
    (mem_zeroSet_of_isomorphic hα hiso.symm)
  exact fun m => (h m).of_isomorphic hiso

/-- **A solution object is smooth** (2021 p. 849): `f(α) = 0` and `F̄(α) ≠ ∅` give `α ∈ C_∞`. -/
theorem solution_isSmoothObj (hf : Q.IsScFredholmSectionFunctor f) {α : C.Obj}
    (hne : (Q.F α).Nonempty) (hα : α ∈ f.zeroSet) : S.IsSmoothObj α := by
  obtain ⟨Ψ, hΨ⟩ := hne
  obtain ⟨q, hq⟩ := S.isAt α _ (Q.base_mem α Ψ hΨ)
  exact Q.isSmoothObj_of_mem_zeroSet hf hΨ hq hα

/-- **The solution category consists of smooth objects** (2021 p. 849): under the standing
reading `F̄(α) ≠ ∅`, `S_f ⊆ C_∞`. -/
theorem zeroSet_subset_isSmoothObj (hf : Q.IsScFredholmSectionFunctor f)
    (hF : Q.HasStrongBundleUniformizers) : f.zeroSet ⊆ {α | S.IsSmoothObj α} :=
  fun _ hα => Q.solution_isSmoothObj hf (hF _) hα

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

namespace GCT.VectorBundle.ReflectionBundle

open StrongPolyfoldBundleConstruction PolyfoldConstruction

/-- **Witness**: for `f(x) = (x, x)` on the reflection bundle over `ℤ/2 ⋉ ℝ`, `S_f = {0}` consists
of smooth objects; `f` is not the zero section and the isotropy `−1` of the solution object `0`
acts on the fibre by `v ↦ −v ≠ v`. -/
theorem reflDiag_zeroSet_subset_isSmoothObj :
    reflDiag.zeroSet ⊆ {α | reflectionConstruction.IsSmoothObj α} ∧
      reflDiag.zeroSet = {0} ∧ reflectionConstruction.IsSmoothObj (0 : Fin 1 → ℝ) ∧
      (∀ x : Fin 1 → ℝ, x ≠ 0 → reflDiag.toFun x ≠ reflMu.objMk x 0) ∧
      (∀ v : Fin 1 → ℝ, v ≠ 0 → reflV.map ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) v ≠ v) := by
  have h := reflQ.zeroSet_subset_isSmoothObj isScFredholmSectionFunctor_reflDiag
    reflQ_hasStrongBundleUniformizers
  refine ⟨h, reflDiag_zeroSet, h (by rw [reflDiag_zeroSet]; rfl), reflDiag_nondegenerate.1,
    reflDiag_nondegenerate.2.1⟩

end GCT.VectorBundle.ReflectionBundle

end Polyfold
