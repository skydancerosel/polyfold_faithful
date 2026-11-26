import Polyfold.Chapter17.EveryUniformizerGauge
import Polyfold.Examples.Path.PartI_MPolyfold

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
**Theorem 17.1.28, 2021 p. 766**: `M_{F¹}(Ψ¹, Ψ'¹) = (M(Ψ, Ψ'))¹` for every pair of uniformizers.

# The identification `M_{F¹}(Ψ¹, Ψ'¹) = M(Ψ, Ψ')¹` for every pair

## The text, paraphrased

`C¹` carries the polyfold structure `(F¹, M_{F¹})` with `F¹(α) = {Ψ¹ | Ψ ∈ F(α)}` and
`M_{F¹}(Ψ¹, Ψ'¹) := (M(Ψ, Ψ'))¹` with the natural identification `(q, φ, q') ↦ (q, φ, q')`.

## What is formalized

The project's `levelOneConstruction` defines `M_{F¹}(L, L')` through one chosen `Ψ` with `Ψ¹ = L`
(`levelOneData`), and `theorem_17_1_28` gives the identification for that choice.  Here: the
identification cannot hold for every pair `Ψ, Ψ'` with a single structure on `C¹`.

* `gaugeLevel P c`: the polyfold structure `gaugeConstruction` of `EveryUniformizerGauge.lean`
  with `D = U_1` (`Ψ_true` differs from `Ψ_false` only on points of level `0`), so that
  `Ψ_false¹ = Ψ_true¹` (`levelOneUnif_false_eq_true`).
* `continuous_of_isHomeomorph_levelOneTransEquiv`: if for some polyfold structure `S₁` on `C¹`
  the natural identifications of `M_{S₁}(Ψ_false¹, Ψ_false¹)` with `M(Ψ_false, Ψ_false)¹` and of
  `M_{S₁}(Ψ_false¹, Ψ_true¹)` with `M(Ψ_false, Ψ_true)¹` are homeomorphisms, the gauge `c` is
  continuous on `U_1`.
* `not_continuous_harmGauge`: on the M-polyfold `H` (weighted `ℓ²`, which has points of level `0`
  only), `c = 1` at `0` and `c = g` elsewhere is not continuous on `H_1`.
* **`theorem_17_1_28_not_every_pair`**: there are a GCT with a polyfold structure (`F(α) ≠ ∅` for
  every `α`) and two uniformizers `Ψ ≠ Ψ'` with `Ψ¹ = Ψ'¹` such that no polyfold structure `S₁` on
  `C¹` makes both `M_{S₁}(Ψ¹, Ψ¹) → M(Ψ, Ψ)¹` and `M_{S₁}(Ψ¹, Ψ'¹) → M(Ψ, Ψ')¹` homeomorphisms.

## Readings

* The text writes `M_{F¹}(Ψ¹, Ψ'¹) := (M(Ψ, Ψ'))¹`, which presupposes that `M(Ψ, Ψ')¹` depends
  only on `Ψ¹, Ψ'¹`.  As we read Definition 17.1.8, the structures on different transition sets
  are tied only by (a)–(c), and two uniformizers with the same lift may carry structures that
  differ over their common level-`1` set; the statement then holds for one representative per
  lift (`theorem_17_1_28`), not for every pair.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold.GCT.PolyfoldConstruction.EveryUniformizer

variable {U : Type} [TopologicalSpace U] [T2Space U] [ParacompactSpace U] (P : MPolyfold U)
  (c : U → Z3)

/-- The gauge structure with `D = U_1`. -/
abbrev gaugeLevel : (C P).PolyfoldConstruction := gaugeConstruction P (P.levelSet 1) c

theorem gaugeLevel_hc : (gaugeLevel P c).HasCoveringUniformizers :=
  (gaugeLevel P c).toUniformizerConstruction.hasCoveringUniformizers_of_hasUniformizers
    (gaugeConstruction_hasUniformizers _ _ _)

/-- Two local uniformizers with the same underlying uniformizer are equal. -/
theorem ext_of_toUniformizer {C' : GCT.{0}} {L L' : C'.LocalUniformizer}
    (h : L.toUniformizer = L'.toUniformizer) : L = L' := by
  obtain ⟨u, e⟩ := L
  obtain ⟨u', e'⟩ := L'
  subst h
  rfl

variable (x : U)

/-- `Ψ_false¹ = Ψ_true¹`: the two uniformizers agree on the points of level `1`. -/
theorem levelOneUnif_false_eq_true :
    (gaugeLevel P c).levelOneUnif (gaugeLevel_hc P c) (unifAt P (P.levelSet 1) c false x) =
      (gaugeLevel P c).levelOneUnif (gaugeLevel_hc P c) (unifAt P (P.levelSet 1) c true x) := by
  have hF : (gaugeLevel P c).levelOneFunctor (unifAt P (P.levelSet 1) c false x) =
      (gaugeLevel P c).levelOneFunctor (unifAt P (P.levelSet 1) c true x) := by
    refine GroupoidFunctor.ext rfl (funext fun p => Subtype.ext ?_)
    change (tw (P.levelSet 1) false (P.levelVal 1 p.2) p.1, P.levelVal 1 p.2) =
      (tw (P.levelSet 1) true (P.levelVal 1 p.2) p.1, P.levelVal 1 p.2)
    rw [tw_false, tw_of_mem _ true (MPolyfold.levelVal_mem p.2)]
  refine ext_of_toUniformizer ?_
  dsimp only [levelOneUnif]
  congr 1

/-- `Ψ_false¹ ∈ S₁.F(α)` for a polyfold structure on `C¹` with `F¹(α) = {Ψ¹ | Ψ ∈ F(α)}`. -/
theorem exists_mem_levelOneF (b : Bool) (hx : x ∈ P.levelSet 1)
    (S₁ : ((gaugeLevel P c).levelOneGCT (gaugeLevel_hc P c)).PolyfoldConstruction)
    (hS₁ : ∀ α : ((gaugeLevel P c).levelOneGCT (gaugeLevel_hc P c)).Obj,
      S₁.F α = {L | ∃ Ψ : (gaugeLevel P c).Unif, Ψ.1 ∈ (gaugeLevel P c).F α.1 ∧
        L = (gaugeLevel P c).levelOneUnif (gaugeLevel_hc P c) Ψ}) :
    ∃ α, (gaugeLevel P c).levelOneUnif (gaugeLevel_hc P c) (unifAt P (P.levelSet 1) c b x) ∈
      S₁.F α := by
  have hmem : x ∈ (gaugeLevel P c).regSet 1 :=
    mem_regSet_obj (unifAt P (P.levelSet 1) c b x) (P.levelMk 1 x hx)
  refine ⟨⟨x, hmem⟩, ?_⟩
  have := hS₁ ⟨x, hmem⟩
  rw [this]
  exact ⟨_, ⟨b, rfl⟩, rfl⟩

/-- **The key step**: if, for a polyfold structure `S₁` on `C¹`, the natural identifications
`M_{S₁}(Ψ_false¹, Ψ_false¹) → M(Ψ_false, Ψ_false)¹` and
`M_{S₁}(Ψ_false¹, Ψ_true¹) → M(Ψ_false, Ψ_true)¹` are homeomorphisms, then `c` is continuous on
`U_1` (provided some point of `U` is not of level `1`). -/
theorem continuous_of_isHomeomorph_levelOneTransEquiv {x₁ : U} (hx₁ : x₁ ∉ P.levelSet 1)
    (S₁ : ((gaugeLevel P c).levelOneGCT (gaugeLevel_hc P c)).PolyfoldConstruction)
    (h : ∃ α, (gaugeLevel P c).levelOneUnif (gaugeLevel_hc P c)
      (unifAt P (P.levelSet 1) c false x) ∈ S₁.F α)
    (h' : ∃ α, (gaugeLevel P c).levelOneUnif (gaugeLevel_hc P c)
      (unifAt P (P.levelSet 1) c true x) ∈ S₁.F α)
    (H₀ : @IsHomeomorph _ _ (S₁.topM ⟨_, h⟩ ⟨_, h⟩) _
      ((gaugeLevel P c).levelOneTransEquiv (gaugeLevel_hc P c)
        (unifAt P (P.levelSet 1) c false x) (unifAt P (P.levelSet 1) c false x)))
    (H₁ : @IsHomeomorph _ _ (S₁.topM ⟨_, h⟩ ⟨_, h'⟩) _
      ((gaugeLevel P c).levelOneTransEquiv (gaugeLevel_hc P c)
        (unifAt P (P.levelSet 1) c false x) (unifAt P (P.levelSet 1) c true x))) :
    Continuous fun q : P.Level 1 => (c (P.levelVal 1 q))⁻¹ := by
  obtain ⟨f, hf, hfm⟩ := exists_continuous_cast S₁ _ _ _ h h h'
    (levelOneUnif_false_eq_true P c x)
  let S := gaugeLevel P c
  let hc := gaugeLevel_hc P c
  let Ψ₀ := unifAt P (P.levelSet 1) c false x
  let Ψ₁ := unifAt P (P.levelSet 1) c true x
  -- the unit map on level `1`
  let u₁ : P.Level 1 → (S.transPolyfold Ψ₀ Ψ₀).Level 1 :=
    MPolyfold.levelOneMap P (S.transPolyfold Ψ₀ Ψ₀)
      (fun q => S.toTr (GroupoidStr.TransitionSet.unit q))
      ((S.isScSmoothMap_trUnit Ψ₀).mapsTo_levelSet 1)
  have hu₁ : Continuous u₁ := continuousOn_univ.1
    (MPolyfold.IsScSmoothMap.levelOne (f₁ := u₁) (S.isScSmoothMap_trUnit Ψ₀)
      fun _ => rfl).continuousOn
  let _ := S₁.topM ⟨_, h⟩ ⟨_, h⟩
  let _ := S₁.topM ⟨_, h⟩ ⟨_, h'⟩
  let e₀ := H₀.homeomorph _
  have hρ : @Continuous (S.Tr Ψ₀ Ψ₁) (Z3 × U) _ _
      (gRho P (P.levelSet 1) c (unif P (P.levelSet 1) false) (unif P (P.levelSet 1) true)) :=
    continuous_gRho P _ c _ _
  have hcomp : Continuous fun q : P.Level 1 =>
      (gRho P (P.levelSet 1) c (unif P (P.levelSet 1) false) (unif P (P.levelSet 1) true)
        ((S.transPolyfold Ψ₀ Ψ₁).levelVal 1
          (S.levelOneTransEquiv hc Ψ₀ Ψ₁ (f (e₀.symm (u₁ q)))))).1 :=
    continuous_fst.comp (hρ.comp ((MPolyfold.continuous_levelVal 1).comp (H₁.continuous.comp
      (hf.comp (e₀.symm.continuous.comp hu₁)))))
  refine hcomp.congr fun q => ?_
  have hmor : ((S.transPolyfold Ψ₀ Ψ₁).levelVal 1
      (S.levelOneTransEquiv hc Ψ₀ Ψ₁ (f (e₀.symm (u₁ q))))).mor = (1, P.levelVal 1 q) := by
    rw [levelOneTransEquiv_mor, hfm]
    have h1 := levelOneTransEquiv_mor S hc Ψ₀ Ψ₀ (e₀.symm (u₁ q))
    have h2 : S.levelOneTransEquiv hc Ψ₀ Ψ₀ (e₀.symm (u₁ q)) = u₁ q := e₀.apply_symm_apply _
    rw [h2] at h1
    exact h1.symm
  refine (congrArg Prod.fst (gRho_false_true P _ c hx₁ _)).trans ?_
  change ((S.transPolyfold Ψ₀ Ψ₁).levelVal 1
      (S.levelOneTransEquiv hc Ψ₀ Ψ₁ (f (e₀.symm (u₁ q))))).mor.1 *
    (c ((S.transPolyfold Ψ₀ Ψ₁).levelVal 1
      (S.levelOneTransEquiv hc Ψ₀ Ψ₁ (f (e₀.symm (u₁ q))))).mor.2)⁻¹ = _
  rw [hmor, one_mul]

/-! ### The M-polyfold `H` -/

section H

open Polyfold.Examples.OrbifoldSquareInf Polyfold.Examples.Path Polyfold.Examples.WeightedEllTwo

open scoped Classical in
/-- The gauge on `H`: `1` at `0`, the generator elsewhere. -/
def harmGauge (x : HObj) : Z3 := if x = h0 then 1 else gen

/-- `harmGauge` is not continuous on `H_1`: along the path `t ↦ t·v` in `H_1` it jumps at `0`. -/
theorem not_continuous_harmGauge :
    ¬ Continuous fun q : PH.Level 1 => (harmGauge (PH.levelVal 1 q))⁻¹ := by
  intro hcont
  have hφ := isChart_retractChart relOpen_H.isScRetract h0
  set φ := retractChart relOpen_H.isScRetract h0
  set x₀ : PH.Level 1 := PH.levelMk 1 h0 h0_mem_levelSet_one
  let v : H 1 := harm
  have hv : v ≠ 0 := fun h => incl_ne_harm 0 (by rw [map_zero]; exact h.symm)
  let p : ℝ → PH.Level 1 := fun t => (MPolyfold.levelChart hφ x₀).symm (t • v)
  have hO : ∀ z : H 1, H.toBase 1 z ∈ φ.model.O := fun z => mem_univ _
  have hp : Continuous p := by
    have h1 := (MPolyfold.levelChart hφ x₀).continuousOn_invFun
    have h2 : (MPolyfold.levelChart hφ x₀).model.O = univ :=
      eq_univ_of_forall fun z => hO z
    rw [h2] at h1
    exact (continuousOn_univ.1 h1).comp (continuous_id.smul continuous_const)
  have hpv : ∀ t, ((PH.levelVal 1 (p t) : HObj) : H 0) = t • H.toBase 1 v := by
    intro t
    rw [MPolyfold.levelChart_symm_apply hφ x₀ (hO _)]
    exact (φ.apply_symm_apply (hO (t • v))).trans (map_smul _ _ _)
  have hg := PreconnectedSpace.constant inferInstance (hcont.comp hp) (x := 0) (y := 1)
  have h0' : PH.levelVal 1 (p 0) = h0 := Subtype.ext (by rw [hpv, zero_smul]; rfl)
  have h1' : PH.levelVal 1 (p 1) ≠ h0 := by
    intro he
    have := congrArg Subtype.val he
    rw [hpv, one_smul] at this
    exact hv ((H.toBase_injective 1) (this.trans (map_zero _).symm))
  simp only [Function.comp_apply, harmGauge, h0', h1', if_true, if_false] at hg
  exact gen_inv_ne_one (by rw [← hg]; rfl)

end H

end Polyfold.GCT.PolyfoldConstruction.EveryUniformizer

namespace Polyfold.GCT.PolyfoldConstruction

open EveryUniformizer Polyfold.Examples.OrbifoldSquareInf Polyfold.Examples.Path

/-- **Theorem 17.1.28, 2021 p. 766, for every pair of uniformizers, does not hold as we read it**:
there are a GCT `C` with a polyfold structure `S` (`F(α) ≠ ∅` for every `α`) and uniformizers
`Ψ ≠ Ψ'` in `F(α)` for an object `α` of level `1`, with the same lift `Ψ¹ = Ψ'¹`, such that for no polyfold structure `S₁` on `C¹`
with `Ψ¹ ∈ F_{S₁}` both natural identifications `M_{S₁}(Ψ¹, Ψ¹) → M(Ψ, Ψ)¹` and
`M_{S₁}(Ψ¹, Ψ'¹) → M(Ψ, Ψ')¹` are homeomorphisms.  (`C = ℤ/3 ⋉ H`, trivial action, `H` the
weighted `ℓ²`; `Ψ, Ψ'` differ on the points of level `0`; the transition structures are
`gaugeConstruction` with `harmGauge`.)  For the representative chosen by `levelOneData` the
identification holds (`theorem_17_1_28`). -/
theorem theorem_17_1_28_not_every_pair :
    ∃ (C : GCT.{0}) (S : C.PolyfoldConstruction) (hc : S.HasCoveringUniformizers)
      (Ψ Ψ' : S.Unif), S.HasUniformizers ∧
      (∃ α : (S.levelOneGCT hc).Obj, Ψ.1 ∈ S.F α.1 ∧ Ψ'.1 ∈ S.F α.1) ∧ Ψ ≠ Ψ' ∧
      S.levelOneUnif hc Ψ = S.levelOneUnif hc Ψ' ∧
      ∀ (S₁ : (S.levelOneGCT hc).PolyfoldConstruction)
        (h : ∃ α, S.levelOneUnif hc Ψ ∈ S₁.F α) (h' : ∃ α, S.levelOneUnif hc Ψ' ∈ S₁.F α),
        ¬ (@IsHomeomorph _ _ (S₁.topM ⟨_, h⟩ ⟨_, h⟩) _ (S.levelOneTransEquiv hc Ψ Ψ) ∧
          @IsHomeomorph _ _ (S₁.topM ⟨_, h⟩ ⟨_, h'⟩) _ (S.levelOneTransEquiv hc Ψ Ψ')) := by
  refine ⟨_, gaugeLevel PH harmGauge, gaugeLevel_hc PH harmGauge,
    unifAt PH (PH.levelSet 1) harmGauge false h0, unifAt PH (PH.levelSet 1) harmGauge true h0,
    gaugeConstruction_hasUniformizers _ _ _,
    ⟨⟨h0, mem_regSet_obj (unifAt PH (PH.levelSet 1) harmGauge false h0)
      (PH.levelMk 1 h0 h0_mem_levelSet_one)⟩, ⟨false, rfl⟩, ⟨true, rfl⟩⟩, fun he => ?_,
    levelOneUnif_false_eq_true PH harmGauge h0, fun S₁ h h' ⟨H₀, H₁⟩ => ?_⟩
  · exact unif_false_ne_true PH _ hpt_harmH_not_mem_levelSet_one (congrArg Subtype.val he)
  · exact not_continuous_harmGauge (continuous_of_isHomeomorph_levelOneTransEquiv PH harmGauge
      h0 hpt_harmH_not_mem_levelSet_one S₁ h h' H₀ H₁)

end Polyfold.GCT.PolyfoldConstruction
