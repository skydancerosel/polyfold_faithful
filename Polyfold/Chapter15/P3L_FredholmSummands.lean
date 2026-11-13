import Polyfold.Chapter15.P3L_Transversality
import Polyfold.Chapter3.LinearizationChartsScG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 15,
§15.1, Theorem 15.1.1 (2) (p. 684): the summands of `T(f,Λ)(x)` are sc-Fredholm (gap G.145).

# The operators `(f − sᵢ)'(x)` are sc-Fredholm

## The text, paraphrased

(§15.1, Theorem 15.1.1 (2)) For a local sc⁺-section structure `(sᵢ, σᵢ)` of `Λ` around `x` and
`f(x) = sᵢ(x)`, `(f − sᵢ)'(x) : T_xX → W_x` is an sc-Fredholm operator (`f − sᵢ` is sc-Fredholm
near `x`, an sc⁺-perturbation of `f`), so `T(f,Λ)(x) ∈ GrF(x)`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`subDeriv_isScFredholm`**: for `f` with germ data in tame charts, `s` sc⁺ on an open
  `O ⊇ dom(c)` and `f(x) = s(x)`, the chart operator `D((f̂ − ŝ) ∘ r)(z)` (`subDeriv`, `z` over
  `φ(x)`) is an sc-operator and its restriction `T_zO → K_z` is sc-Fredholm, every level Fredholm
  with the level-`0` index: Part I's `StrongBundle.linAt_isScFredholm` for the sc-Fredholm
  section `(f − s)|O` of `W|O` (`isScFredholmSectionTame_subRestrict`, Theorem 3.1.18).
* **`linearization_summand_isScFredholm`**: every operator occurring in `T(f,Λ)(x)` is
  `(f − sᵢ)'(x) = toIntr c hx (subDeriv c f sᵢ z)` for a branch with `f(x) = sᵢ(x)`, read in any
  local section structure and chart (`LocalLinData`), and its chart operator is sc-Fredholm in
  the sense above.

## Reading

`T_xX` and `W_x` carry no sc-structure of their own in the project; "`(f − sᵢ)'(x)` is
sc-Fredholm" is read in the chart, where `T_xX ≅ T_zO` (`tangentFiberLinearEquiv`) and
`W_x ≅ K_z` (`fiberLin`), the identifications by which `toIntr` is defined.  As in §15.2 the
section `f` is assumed to have germ data in tame charts (`IsScFredholmSectionTame`): that
`f − s` is sc-Fredholm uses Part I's `theorem_3_1_18_tame`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-- **The chart operator of `(f − s)'(x)` is sc-Fredholm** (G.145, Theorem 15.1.1 (2), 2021
p. 684): for `f` with germ data in tame charts, `s` sc⁺ on the open `O ⊇ dom(c)`, `f(x) = s(x)`
and `z ∈ E₁` over `φ(x)`, `D((f̂ − ŝ) ∘ r)(z)` is an sc-operator mapping `T_zO` into `K_z`, and
its restriction `T_zO → K_z` is an sc-Fredholm operator, Fredholm on every level with the
level-`0` index. -/
theorem subDeriv_isScFredholm {f : A.Obj → A.W} (hft : A.B.IsScFredholmSectionTame f)
    {s : A.Obj → A.W} {O : Set A.Obj} (hO : IsOpen O) (hs : IsScPlusSectionOn A s O)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O) {x : A.Obj}
    (hx : x ∈ c.φ.source) (hfs : f x = s x) {z : c.φ.model.E 1}
    (hz : c.φ.model.E.toBase 1 z = c.φ x) (hzU : c.φ.model.E.toBase 1 z ∈ c.U) :
    ∃ (hD : IsScOperator (subDeriv c f s z))
      (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
      (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
      (hTK : ∀ v ∈ rangeS (scDeriv c.U (r c.R) z),
        hD.toScOperator 0 v ∈ rangeS (ρCLM c.isRetraction hzU)),
      IsScFredholm (hD.toScOperator.restrict hT hK hTK) ∧
      ∀ m, ((hD.toScOperator.restrict hT hK hTK) m).IsFredholm ∧
        fredholmIndex ((hD.toScOperator.restrict hT hK hTK) m) =
          fredholmIndex (hD.toScOperator.restrict hT hK hTK 0) := by
  have : Nonempty O := ⟨⟨x, hsub hx⟩⟩
  have := A.X.PObj.paracompactSpace_subtype O
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
    (A.X.PObj.restrictOpen hO) A.B
  have hf := hft.isScSmooth.1
  set q₀ := subRestrict (O := O) f s hf ⟨x, hsub hx⟩
  have hgO := isScFredholmSectionTame_subRestrict hO hft hs
  have hcV : (A.B.restrictOpen hO).IsChart (c.restrictTo A.B.continuous hO hsub q₀) :=
    restrictOpen_isChart_restrictTo hO hc hsub q₀
  have h0 : IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj)) (subRestrict (O := O) f s hf)
      ⟨x, hsub hx⟩ := by
    unfold subRestrict
    rw [isZeroAt_restrictSection_iff]
    exact (isZeroAt_subSec_iff hf hs.1 (hsub hx)).2 hfs
  obtain ⟨hD, hT, hK, hTK, -, hsc, hlvl⟩ :=
    StrongBundle.linAt_isScFredholm hgO.toIsScFredholmSection h0 hcV hx hz hzU
  have e := scDeriv_restrictTo_subRestrict hO hft hs hc hsub q₀ hzU
  revert hD
  rw [show scDeriv (c.restrictTo A.B.continuous hO hsub q₀).U
      ((c.restrictTo A.B.continuous hO hsub q₀).principal (subRestrict (O := O) f s hf) ∘
        r (c.restrictTo A.B.continuous hO hsub q₀).R) z = subDeriv c f s z from e]
  intro hD hTK hsc hlvl
  exact ⟨hD, hT, hK, hTK, hsc, fun m => ⟨(hlvl m).1, (hlvl m).2.1⟩⟩

/-- **The summands of `T(f,Λ)(x)` are sc-Fredholm** (G.145, Theorem 15.1.1 (2), 2021 p. 684):
for `x ∈ X₁` and any local section structure and chart (`LocalLinData`), every operator occurring
in `T(f,Λ)(x)` is `(f − sᵢ)'(x)` (`toIntr`) for a branch with `f(x) = sᵢ(x)`, and the chart
operator `D((f̂ − ŝᵢ) ∘ r)(z)` is an sc-operator whose restriction `T_zO → K_z` is sc-Fredholm. -/
theorem linearization_summand_isScFredholm {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ : A.W → ℚ≥0} {x : A.X.PObj.Level 1} (d : LocalLinData A Λ x)
    (L : A.X.PObj.tangentFiber x →ₗ[ℝ] A.P ⁻¹' {A.X.PObj.levelVal 1 x})
    (hL : L ∈ (linearization f Λ x).support) :
    ∃ i, d.s i (A.X.PObj.levelVal 1 x) = f (A.X.PObj.levelVal 1 x) ∧
      toIntr d.c d.mem (subDeriv d.c f (d.s i) (levelLift d.c.φ 1 (A.X.PObj.levelVal 1 x))) = L ∧
      ∀ hzU : d.c.φ.model.E.toBase 1 (levelLift d.c.φ 1 (A.X.PObj.levelVal 1 x)) ∈ d.c.U,
      ∃ (hD : IsScOperator
          (subDeriv d.c f (d.s i) (levelLift d.c.φ 1 (A.X.PObj.levelVal 1 x))))
        (hT : d.c.φ.model.E.IsScSubspace
          (rangeS (scDeriv d.c.U (r d.c.R) (levelLift d.c.φ 1 (A.X.PObj.levelVal 1 x)))))
        (hK : d.c.F.IsScSubspace (rangeS (ρCLM d.c.isRetraction hzU)))
        (hTK : ∀ v ∈ rangeS (scDeriv d.c.U (r d.c.R) (levelLift d.c.φ 1 (A.X.PObj.levelVal 1 x))),
          hD.toScOperator 0 v ∈ rangeS (ρCLM d.c.isRetraction hzU)),
        IsScFredholm (hD.toScOperator.restrict hT hK hTK) ∧
        ∀ m, ((hD.toScOperator.restrict hT hK hTK) m).IsFredholm ∧
          fredholmIndex ((hD.toScOperator.restrict hT hK hTK) m) =
            fredholmIndex (hD.toScOperator.restrict hT hK hTK 0) := by
  rw [linearization_eq hf d, LocalLinData.sum] at hL
  obtain ⟨i, hi, hiL⟩ := (mem_support_linSumIntr_iff hf.1.1.1 d.rep.1
    (fun i => (d.rep.2.1 i).1) d.sub d.mem L).1 hL
  refine ⟨i, hi, hiL, fun hzU => ?_⟩
  exact subDeriv_isScFredholm hft d.isOpen (d.rep.2.1 i) d.isChart d.sub d.mem hi.symm
    (A.X.PObj.toBase_levelLift d.c.isChart d.mem (levelVal_mem x)) hzU

end SBLocalization

end Polyfold
