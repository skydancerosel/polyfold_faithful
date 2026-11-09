import Polyfold.Chapter7.NonVacuity
import Polyfold.Chapter8.TangentEp

/-!
# Remark 8.1.10: the bare map `G : (φ, h) ↦ (Tφ, Ts(h))` is not injective

2021 Remark 8.1.10, pp. 364–365 (2017: Remark 8.1, pp. 264–265), describes the morphisms of the
tangent `T𝐗` by the map `G : (φ, h) ↦ (Tφ, Ts(h))` and says that `G` is a bijection of `T𝐗` onto
the pairs `(Tφ, a)` with `φ ∈ 𝐗₁` and `a ∈ T_{s(φ)}X`.  The project's `remark_8_1_10`
(`Chapter8/TangentEp.lean`) proves this with the first entry `Tφ` labelled by `φ` (`remarkG`).
Read as a map whose first entry is the bare linear map `Tφ : T_{s(φ)}X → T_{t(φ)}X`, the claim
**does not hold as we read it**: two distinct morphisms at the same point can have the same
tangent, and then `G` identifies distinct tangent vectors of `𝐗`.

The witness is the translation groupoid `ℤ/3 ⋉ ℝ` of the trivial action
(`EpGroupoid.Examples.trivialZ3EpGroupoid`, `Chapter7/NonVacuity.lean`, the ep-groupoid behind
`remark_definition_7_1_7_counterexample`).  There `s = t`, so `Tφ` is the identity for every
morphism `φ` (`tangentMor_trivialZ3`), while the three morphisms `(g, x)`, `g ∈ ℤ/3`, at a point
`x` are distinct.  Lifting one tangent vector `a ∈ T_xX` along `Ts` over `(1, x)` and over
`(g, x)`, `g ≠ 1`, gives two distinct vectors of `T𝐗` with the same image under `G`.

## What is formalized

* `EpGroupoid.Examples.tangentMor_trivialZ3`: on `ℤ/3 ⋉ ℝ`, `Tφ = id` for every morphism `φ`.
* `EpGroupoid.Examples.remark_8_1_10_not_injective`: on `ℤ/3 ⋉ ℝ`, the map
  `v ↦ (Tφ(v), Ts(v))` (with `Tφ(v) = tangentMor (tBase v)`, a function `TX → TX`) is not
  injective.  This certifies the correction of row **V8.12** (Findings, Chapter 8, item 10).

The linearity of `Tφ` (the text's "linear isomorphism") is not involved: Part I's `T_xX` carries
no linear structure in the project (gap G.7), and the counterexample uses only that `Tφ` is the
identity.
-/

open Set Function

noncomputable section

namespace Polyfold

namespace EpGroupoid

namespace Examples

/-- On `ℤ/3 ⋉ ℝ` (trivial action) the tangent `Tφ` of every morphism `φ` is the identity of
`TX`: here `t = s`, so `Tt ∘ (Ts|T_φ𝐗)⁻¹ = id` (Definition 7.1.4; 2017: Definition 7.4;
`tangentMor`). -/
theorem tangentMor_trivialZ3 (φ : Multiplicative (ZMod 3) × (Fin 1 → ℝ)) :
    trivialZ3EpGroupoid.tangentMor φ = id := by
  funext a
  unfold tangentMor
  split_ifs with hv
  · exact hv.choose_spec.2
  · rfl

/-- **2021 Remark 8.1.10, pp. 364–365 (2017: Remark 8.1), with `Tφ` a bare map, does not hold as we
read it** (row V8.12): on the translation groupoid `ℤ/3 ⋉ ℝ` of the trivial action, the map
`G : T𝐗 → (TX → TX) × TX`, `(φ, h) ↦ (Tφ, Ts(h))`, is not injective.  With `Tφ` labelled by `φ`
the map is a bijection onto its range (`remark_8_1_10`). -/
theorem remark_8_1_10_not_injective :
    ¬ Injective (fun v : trivialZ3EpGroupoid.PMor.TangentSpace =>
      (trivialZ3EpGroupoid.tangentMor (trivialZ3EpGroupoid.tBase v),
        trivialZ3EpGroupoid.tSrc v)) := by
  intro hinj
  set X := trivialZ3EpGroupoid
  -- a tangent vector `a` of `TX` over the level-`1` point `x`
  have h0 : (0 : Fin 1 → ℝ) ∈ X.PObj.levelSet 1 := by
    rw [show X.PObj = rnPolyfold 1 from rfl, rnPolyfold_levelSet]; exact mem_univ _
  obtain ⟨χ, hχ, h0χ⟩ := X.PObj.exists_isChart_mem_source 0
  let p : X.PObj.TangentPre :=
    { x := 0, φ := χ, h := 0, isChart := hχ, mem_source := h0χ, mem_level := h0
      mem_tangent := by
        refine mk_zero_mem_retractTangent χ.model.isScRetract ?_
        rw [ScBanach.mem_lvlSet, X.PObj.toBase_levelLift hχ h0χ h0]
        exact MChart.mapsTo_model _ _ h0χ }
  set a : X.PObj.TangentSpace := MPolyfold.TangentSpace.mk p
  set x : Fin 1 → ℝ := X.PObj.levelVal 1 (X.PObj.tangentProj a) with hx
  have hx1 : x ∈ X.PObj.levelSet 1 := MPolyfold.levelVal_mem _
  -- the morphisms `φ = (1, x)` and `ψ = (g, x)`, `g ≠ 1`, both on level `1`
  set g : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1
  have hg : g ≠ 1 := by decide
  have hφ1 : ((1 : Multiplicative (ZMod 3)), x) ∈ X.PMor.levelSet 1 :=
    (X.mem_levelSet_src_iff _ 1).1 hx1
  have hψ1 : (g, x) ∈ X.PMor.levelSet 1 := (X.mem_levelSet_src_iff _ 1).1 hx1
  -- lift `a` along `Ts` over both
  obtain ⟨v, hv, hva⟩ := X.exists_tSrc_eq' hφ1 (a := a) rfl
  obtain ⟨w, hw, hwa⟩ := X.exists_tSrc_eq' hψ1 (a := a) rfl
  have hvw : v = w := hinj (by
    simp only [Prod.mk.injEq]
    exact ⟨by rw [tangentMor_trivialZ3, tangentMor_trivialZ3], by rw [hva, hwa]⟩)
  have h1 := congrArg (fun u => (X.tBase u).1) hvw
  simp only [hv, hw] at h1
  exact hg h1.symm

end Examples

end EpGroupoid

end Polyfold
