import Polyfold.Chapter18.LinearizationSet
import Polyfold.Chapter18.FredholmSectionFunctorsExamples
import Polyfold.Chapter17.BranchedSubcategoryExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.1, Definition 18.1.4, p. 845: **a non-degenerate witness for the hypothesis
`HasTransportedScPlusSections`** and for the further claims of Definition 18.1.4 on the reflection
bundle of Chapter 17 with the diagonal section `f(x) = (x, x)` (`reflDiag`).  Numbers and pages
are the 2021 text's.

* `isScPlusSection_smul_conj`: for `g ∈ ℤ/2` and an sc⁺-section `s` of `K = ℝ × ℝ → ℝ`,
  `y ↦ g ∗ s(g⁻¹ y)` is an sc⁺-section.
* `reflQ_hasTransportedScPlusSections`: the hypothesis holds for `reflQ`, with `s' = g ∗ s ∘ g⁻¹`
  for `g` the group part of `a`, and `N` the sheet of `M(Ψ, Ψ)` where the group part is `g`.
* `definition_18_1_4_reflDiag`: at the zero `0` of `f`, `Lin(f, 0)` contains `f'(0)`, equals the
  set read through `Ψ̄` and its point `0`, has one index, and is mapped into itself by `φ_*` for
  every `φ : 0 → 0`; `linPush_reflDiag_neg` is the case `φ = (−1, 0)`, whose fibre map is
  `v ↦ −v` (`reflV_map_ne`).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

namespace GCT.VectorBundle.ReflectionBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor TrivialBundle
  StrongBundleUniformizerConstruction StrongBundleUniformizerData StrongPolyfoldBundleConstruction
  PolyfoldConstruction

/-- `y ↦ g ∗ s(g⁻¹ y)`. -/
def smulConj (g : ℤˣ) (s : (Fin 1 → ℝ) → K) : (Fin 1 → ℝ) → K := fun y => g • s (g⁻¹ • y)

/-- **`y ↦ g ∗ s(g⁻¹ y)` is an sc⁺-section** of `K = ℝ × ℝ → ℝ` for an sc⁺-section `s`. -/
theorem isScPlusSection_smul_conj (g : ℤˣ) {s : (Fin 1 → ℝ) → K}
    (hs : (bundle 1 1).IsScPlusSection s) :
    (bundle 1 1).IsScPlusSection (smulConj g s) := by
  obtain ⟨hsec, G, hGf, hG⟩ := ((bundle 1 1).isScPlusSection_iff s).1 hs
  refine ((bundle 1 1).isScPlusSection_iff _).2 ⟨fun y => ?_,
    StrongBundle.oneRestrict (bundle 1 1) (bundle 1 1) (fun k : K => g • k)
      (isStrongBundleMap_smul g).mapsTo_oneSet ∘ G ∘ fun y => g⁻¹ • y, ?_, ?_⟩
  · change TrivialBundle.proj 1 1 (g • s (g⁻¹ • y)) = y
    rw [(isStrongBundleMap_smul g).covers, hsec, smul_inv_smul]
  · funext y
    simp only [comp_apply, StrongBundle.oneVal_oneRestrict]
    change g • (bundle 1 1).oneVal (G (g⁻¹ • y)) = g • s (g⁻¹ • y)
    rw [← congrFun hGf (g⁻¹ • y)]
    rfl
  · exact (isStrongBundleMap_smul g).isScSmoothMap_one.comp
      (hG.comp (EpGroupoid.Examples.isScSmoothMap_units_smul g⁻¹))

/-- **The non-degenerate witness of `HasTransportedScPlusSections`** (read with Definition
18.1.4): on `reflQ`, an sc⁺-section `s` is carried along `a` by `s' = g ∗ s ∘ g⁻¹`, `g` the group
part of `a`; on the sheet of `M(Ψ, Ψ)` with group part `g`, `t̄(b, s(s b)) = g ∗ s(s b) =
s'(t b)` (`transT_eq`). -/
theorem reflQ_hasTransportedScPlusSections : reflQ.HasTransportedScPlusSections := by
  intro Ψ Ψ' a s hs
  obtain rfl := unif_eq Ψ
  obtain rfl := unif_eq Ψ'
  refine ⟨smulConj a.mor.1 s, isScPlusSection_smul_conj a.mor.1 hs,
    sheet a.mor.1, isOpen_sheet _, rfl, fun b hb => ?_⟩
  have hb' : b.mor.1 = a.mor.1 := hb
  have h1 := transT_eq ⟨(b, s b.src), hs.1 b.src⟩
  change smulConj a.mor.1 s (show Fin 1 → ℝ from b.tgt) = _
  rw [tgt_eq_smul_src b, hb']
  refine Eq.trans ?_ h1.symm
  change smulConj a.mor.1 s (a.mor.1 • (show Fin 1 → ℝ from b.src)) =
    b.mor.1 • (show K from s b.src)
  rw [hb']
  exact congrArg (fun z => a.mor.1 • (show K from s z))
    (inv_smul_smul a.mor.1 (show Fin 1 → ℝ from b.src))

instance fact_tangentObj_zero : Fact (reflectionConstruction.TangentObj (0 : Fin 1 → ℝ)) :=
  ⟨tangentObj_reflection_zero⟩

/-- `f(0) = 0`. -/
theorem reflDiag_toFun_zero : reflDiag.toFun (0 : Fin 1 → ℝ) = reflV.objMk 0 0 := rfl

/-- The point `0` of `Ψ̄` on level `1`. -/
def linSetPoint : reflΨ.1.base.P.Level 1 :=
  reflΨ.1.base.P.levelMk 1 (show reflΨ.1.base.O from (0 : Fin 1 → ℝ)) (by
    change (0 : Fin 1 → ℝ) ∈ (rnPolyfold 1).levelSet 1
    rw [rnPolyfold_levelSet]; exact mem_univ _)

theorem obj_linSetPoint : reflΨ.1.base.obj (reflΨ.1.base.P.levelVal 1 linSetPoint) = 0 := rfl

/-- **Definition 18.1.4 on the witness**: at the zero `0` of `f(x) = (x, x)`, `Lin(f, 0)` contains
`f'(0)`, is the set read through `Ψ̄` and its point `0`, has one index, and `φ_*` maps it into
itself for every `φ : 0 → 0`. -/
theorem definition_18_1_4_reflDiag :
    reflQ.linearization reflDiag isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0
        reflDiag_toFun_zero ⟨reflUnif, rfl⟩ ∈
      reflQ.linSet reflDiag isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0 ∧
    reflQ.linSet reflDiag isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0 =
      reflQ.linSetAt reflDiag isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0
        (Ψ := reflΨ) rfl linSetPoint obj_linSetPoint ∧
    (∃ i : ℤ, ∀ L ∈ reflQ.linSet reflDiag
        isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0,
      HasFiniteIndex L ∧ linIndex L = i) ∧
    ∀ (φ : GCT.reflection.Mor) (hs : GCT.reflection.toGroupoidStr.src φ = 0)
      (ht : GCT.reflection.toGroupoidStr.tgt φ = 0),
      ∀ L ∈ reflQ.linSet reflDiag isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0,
        linPush φ hs ht L ∈
          reflQ.linSet reflDiag isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0 := by
  obtain ⟨h1, h2, h3⟩ := reflQ.definition_18_1_4_hyp reflQ_hasTransportedScPlusSections
    isScFredholmSectionFunctor_reflDiag 0
  exact ⟨reflQ.linearization_mem_linSet _ 0 reflDiag_toFun_zero ⟨reflUnif, rfl⟩,
    h1 reflΨ rfl linSetPoint obj_linSetPoint, h2,
    fun φ hs ht => h3 0 φ hs ht ⟨reflUnif, rfl⟩⟩

/-- **`φ_* f'(0) ∈ Lin(f, 0)` for `φ = (−1, 0)`**, whose fibre map `μ(φ)` is `v ↦ −v`. -/
theorem linPush_reflDiag_neg :
    linPush (V := reflV) (S := reflectionConstruction) (α := 0) (α' := 0)
        ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) rfl
        (show ((-1 : ℤˣ) • (0 : Fin 1 → ℝ)) = 0 from smul_zero _)
        (reflQ.linearization reflDiag isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor
          0 reflDiag_toFun_zero ⟨reflUnif, rfl⟩) ∈
      reflQ.linSet reflDiag isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0 ∧
    ∀ v : Fin 1 → ℝ, v ≠ 0 → reflV.map ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) v ≠ v :=
  ⟨definition_18_1_4_reflDiag.2.2.2 _ _ _ _ definition_18_1_4_reflDiag.1,
    fun _ hv => reflV_map_ne 0 hv⟩

end GCT.VectorBundle.ReflectionBundle

end Polyfold
