import Polyfold.Chapter15.LinearizationLocalIso
import Polyfold.Chapter15.GeneralPositionBranched
import Polyfold.Chapter12.OrientationEquivalenceStep
import Polyfold.Chapter11.MultisectionLocalStructure
import Polyfold.Chapter10.FredholmEquivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 15,
§15.3, **Definition 15.3.5** (p. 693): general position of `(f, Λ)` under strong bundle
equivalences (Definition 10.4.1) and under generalized strong bundle isomorphisms (Definition
10.5.2), as needed for the polyfold notion of §16.6 (p. 739).

# General position is invariant under generalized strong bundle isomorphisms

## The text, paraphrased

(§16.6, p. 739) For an sc-Fredholm section `f` of a strong polyfold bundle and an
sc⁺-multisection `λ`, "`(f, λ)` in general position" refers to the representatives in a model;
two models differ by a generalized strong bundle isomorphism `[W ←Φ W'' →Ψ W']`, both legs
strong bundle equivalences, along which sections are pushed forward (`Ψ_* Φ^*`, Theorem 10.5.4)
and sc⁺-multisections are pulled back (Proposition 11.5.3).

## What is formalized (namespace `Polyfold.SBLocalization`)

* `isReducedOntoAtLevel_pullback_iff`: for a strong bundle equivalence `Ψ : W → W'` covering
  `ψ`, an sc-Fredholm section functor `f'` and an sc⁺-multisection `Λ'` of `W'`: the reduced
  linearization of `(Ψ^* f', Ψ^* Λ')` is onto at `x` iff that of `(f', Λ')` is onto at `ψ(x)`.
* **`isInGeneralPosition_pullback_iff`**: `(Ψ^* f', Ψ^* Λ')` is in general position iff
  `(f', Λ')` is (essential surjectivity of `ψ` and the invariance under morphisms,
  `isReducedOntoAtLevel_of_mor`).
* **`SDiagram.isInGeneralPosition_iff`**: for a diagram `D : W ←Φ W'' →Ψ W'` of strong bundle
  equivalences, an sc-Fredholm section functor `F` of `W` and sc⁺-multisections `Λ`, `Λ'` with
  `Λ(w) = Λ'(w')` whenever `|D|(|w|) = |w'|`: `(F, Λ)` is in general position iff
  `([D]_* F, Λ')` is.
* `SDiagram.isInGeneralPosition_pushMult_iff`: the same with `Λ' = [D]_* Λ`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongRetr MPolyfold Linearization15 StrongBundle EPLocalization

variable {A A' : SEP.{u}}

/-! ### One strong bundle equivalence -/

/-- **General position at a point along a strong bundle equivalence** `Ψ : W → W'` covering
`ψ`: the reduced linearization of `(Ψ^* f', Ψ^* Λ')` is onto at `x` iff that of `(f', Λ')` is
onto at `ψ(x)`. -/
theorem isReducedOntoAtLevel_pullback_iff {Ψ : A ⟶ A'} (hΨ : SEP.equivalences Ψ)
    {f' : A'.Obj → A'.W} (hf' : A'.E.IsScFredholmSectionFunctor f') {Λ' : A'.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection A' Λ') {x : A.X.PObj.Level 1} {x' : A'.X.PObj.Level 1}
    (hϕ : (SEP.Hom.ϕ Ψ).obj (A.X.PObj.levelVal 1 x) = A'.X.PObj.levelVal 1 x') :
    IsReducedOntoAtLevel ((sbe hΨ).pullback f') (pullMult Ψ Λ') x ↔
      IsReducedOntoAtLevel f' Λ' x' :=
  isReducedOntoAtLevel_localIso_iff ((sbe hΨ).locIso (A.X.PObj.levelVal 1 x))
    ((EpStrongBundle.theorem_10_4_5_fred (sbe hΨ)).2.1 hf') hf' hΛ'
    ((sbe hΨ).eqOn_locIso hf'.1.1.1 _) (fun _ _ => rfl) ((sbe hΨ).mem_locSet _) hϕ

/-- **General position (Definition 15.3.5) is invariant under strong bundle equivalences**: for
a strong bundle equivalence `Ψ : W → W'`, an sc-Fredholm section functor `f'` and an
sc⁺-multisection `Λ'` of `W'`, `(Ψ^* f', Ψ^* Λ')` is in general position iff `(f', Λ')` is. -/
theorem isInGeneralPosition_pullback_iff {Ψ : A ⟶ A'} (hΨ : SEP.equivalences Ψ)
    {f' : A'.Obj → A'.W} (hf' : A'.E.IsScFredholmSectionFunctor f') {Λ' : A'.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection A' Λ') :
    IsInGeneralPosition A ((sbe hΨ).pullback f') (pullMult Ψ Λ') ↔
      IsInGeneralPosition A' f' Λ' := by
  set h := sbe hΨ
  have hsec' : IsSection A'.P f' := hf'.1.1.1
  have hlev : ∀ a : A.Obj, (SEP.Hom.ϕ Ψ).obj a ∈ A'.X.PObj.levelSet 1 ↔
      a ∈ A.X.PObj.levelSet 1 := fun a =>
    (h.locIso a).base.mem_levelSet_iff (h.mem_locSet a) 1
  have hval : ∀ a : A.Obj, pullMult Ψ Λ' (h.pullback f' a) = Λ' (f' ((SEP.Hom.ϕ Ψ).obj a)) :=
    fun a => congrArg Λ' (h.obj_pullback hsec' a)
  constructor
  · intro H x' hpos
    set y' := A'.X.PObj.levelVal 1 x' with hy'
    set a := h.preObj y'
    set σ := h.preMor y'
    have hsrc : A'.X.src σ = (SEP.Hom.ϕ Ψ).obj a := h.src_preMor y'
    have htgt : A'.X.tgt σ = y' := h.tgt_preMor y'
    have hσ1 : σ ∈ A'.X.PMor.levelSet 1 :=
      (A'.X.mem_levelSet_tgt_iff σ 1).1 (htgt ▸ levelVal_mem x')
    have hϕa1 : (SEP.Hom.ϕ Ψ).obj a ∈ A'.X.PObj.levelSet 1 :=
      hsrc ▸ (A'.X.mem_levelSet_src_iff σ 1).2 hσ1
    have ha1 : a ∈ A.X.PObj.levelSet 1 := (hlev a).1 hϕa1
    set x := A.X.PObj.levelMk 1 a ha1
    set x'' := A'.X.PObj.levelMk 1 ((SEP.Hom.ϕ Ψ).obj a) hϕa1
    have hx : A.X.PObj.levelVal 1 x = a := A.X.PObj.levelVal_levelMk 1 _ ha1
    have hx'' : A'.X.PObj.levelVal 1 x'' = (SEP.Hom.ϕ Ψ).obj a :=
      A'.X.PObj.levelVal_levelMk 1 _ hϕa1
    have hfun := isFunctorial_comp hf' hΛ' σ
    have hpos' : 0 < Λ' (f' ((SEP.Hom.ϕ Ψ).obj a)) := by
      have e : ((Λ' (f' (A'.X.src σ)) : ℚ≥0) : ℚ) = Λ' (f' (A'.X.tgt σ)) := hfun
      rw [hsrc, htgt] at e
      have e' : Λ' (f' ((SEP.Hom.ϕ Ψ).obj a)) = Λ' (f' y') := by exact_mod_cast e
      rw [e']; exact hpos
    have hposx : 0 < pullMult Ψ Λ' (h.pullback f' (A.X.PObj.levelVal 1 x)) := by
      rw [hx, hval]; exact hpos'
    have h1 : IsReducedOntoAtLevel (h.pullback f') (pullMult Ψ Λ') x := H x hposx
    have h2 : IsReducedOntoAtLevel f' Λ' x'' :=
      (isReducedOntoAtLevel_pullback_iff hΨ hf' hΛ' (by rw [hx, hx''])).1 h1
    exact isReducedOntoAtLevel_of_mor hf' hΛ' σ (hx''.trans hsrc.symm) htgt.symm h2
  · intro H x hpos
    set a := A.X.PObj.levelVal 1 x with ha
    have hϕa1 : (SEP.Hom.ϕ Ψ).obj a ∈ A'.X.PObj.levelSet 1 := (hlev a).2 (levelVal_mem x)
    set x' := A'.X.PObj.levelMk 1 ((SEP.Hom.ϕ Ψ).obj a) hϕa1
    have hx' : A'.X.PObj.levelVal 1 x' = (SEP.Hom.ϕ Ψ).obj a :=
      A'.X.PObj.levelVal_levelMk 1 _ hϕa1
    have hpos' : 0 < Λ' (f' (A'.X.PObj.levelVal 1 x')) := by
      rw [hx', ← hval]; exact hpos
    have h1 : IsReducedOntoAtLevel f' Λ' x' := H x' hpos'
    exact (isReducedOntoAtLevel_pullback_iff hΨ hf' hΛ' hx'.symm).2 h1

/-! ### Diagrams of strong bundle equivalences -/

namespace SDiagram

/-- **General position is invariant under generalized strong bundle isomorphisms**: for a
diagram `D : W ←Φ W'' →Ψ W'` of strong bundle equivalences, an sc-Fredholm section functor `F`
of `W`, and sc⁺-multisections `Λ` of `W` and `Λ'` of `W'` with `Λ(w) = Λ'(w')` whenever
`|D|(|w|) = |w'|`, `(F, Λ)` is in general position iff `([D]_* F, Λ')` is. -/
theorem isInGeneralPosition_iff (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)
    {F : A.Obj → A.W} (hF : A.E.IsScFredholmSectionFunctor F) {Λ : A.W → ℚ≥0}
    {Λ' : A'.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (hΛ' : IsScPlusMultisection A' Λ')
    (hΛΛ' : ∀ w w', D.orbitMap (A.E.toEpGroupoid.π w) = A'.E.toEpGroupoid.π w' → Λ w = Λ' w') :
    IsInGeneralPosition A F Λ ↔ IsInGeneralPosition A' (D.pushforward hΨ F) Λ' := by
  have hF' : A'.E.IsScFredholmSectionFunctor (D.pushforward hΨ F) :=
    D.mapsTo_pushforward_fred hΨ hF
  have hmid : D.B.E.IsScFredholmSectionFunctor (D.hΦ.pullback F) :=
    (EpStrongBundle.theorem_10_4_5_fred D.hΦ).2.1 hF
  have e1 : (sbe hΨ).pullback (D.pushforward hΨ F) = D.hΦ.pullback F :=
    (sbe hΨ).pullback_pushforward hmid.1.1.1 hmid.1.2
  have e2 : SBLocalization.pullMult D.Ψ Λ' = SBLocalization.pullMult D.Φ Λ := funext fun v =>
    (hΛΛ' _ _ (D.orbitMap_orbitMap_Φ (D.B.E.toEpGroupoid.π v))).symm
  have h1 := isInGeneralPosition_pullback_iff D.isEquivalence_Φ hF hΛ
  have h2 := isInGeneralPosition_pullback_iff hΨ hF' hΛ'
  rw [e1, e2] at h2
  exact h1.symm.trans h2

/-- The same with `Λ' = [D]_* Λ` (Proposition 11.5.3). -/
theorem isInGeneralPosition_pushMult_iff (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)
    {F : A.Obj → A.W} (hF : A.E.IsScFredholmSectionFunctor F) {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) :
    IsInGeneralPosition A F Λ ↔
      IsInGeneralPosition A' (D.pushforward hΨ F) (D.pushMult hΨ Λ) :=
  D.isInGeneralPosition_iff hΨ hF hΛ (SDiagram.isScPlusMultisection_pushMult hΨ hΛ)
    fun _ _ h => (SDiagram.pushMult_eq hΛ.1 h).symm

end SDiagram

end SBLocalization

end Polyfold
