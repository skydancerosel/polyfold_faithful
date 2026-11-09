import Polyfold.Chapter2.SmoothPaths
import Polyfold.Chapter7.ZhouLevels
import Polyfold.Chapter8.TangentZhouLevels

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §7.4 (pp. 331–340),
Appendix 7.6.4 (p. 349), Theorem 6.6.17 (p. 275) and Proposition 8.1.17 (p. 371): the
connectedness facts the text uses for `U ∩ X_∞` and `U(x) ∩ X_m`, as theorems.

# Connected smooth parts: the hypotheses of §7.4, §7.6 and §6.6 are theorems

## The text, paraphrased

(§7.4, p. 334 and p. 336) In the proofs of Propositions 7.4.8 and 7.4.10 the text uses that
`U(x) ∩ X_∞` is connected for the connected open `U(x)`.  (Proposition 7.4.18, p. 336, and
Appendix 7.6.4, p. 349) `U(x)` is chosen so that `U(x) ∩ X_m` is connected in `X_m` for every `m`,
and `U(x) ∩ X_1` is connected in `X^1` and dense in `U(x)`.  (Theorem 6.6.17 (2), p. 275) Every
`x ∈ X_∞` has an open neighbourhood `U` such that `O_f` has exactly two continuous sections over
`U ∩ X_∞`; this needs `U ∩ X_∞` connected.

## What is formalized

From `Chapter2/SmoothPaths.lean` (`MPolyfold.isPathConnected_smoothVal_preimage`,
`MPolyfold.isPreconnected_levelVal_preimage`) and `Chapter7/SmoothPointsDense.lean`
(`MPolyfold.denseSmooth`):

* **`MPolyfold.smoothConnected`**: every M-polyfold satisfies `MPolyfold.SmoothConnected`
  (gap G.85, the connectedness fact of V7.86); `MPolyfold.smoothRegular_iff_tangent`,
  `MPolyfold.smoothRegular_of_tangent`: of the four Part I facts bundled in `SmoothRegular`, only
  the openness of `p : TX → X¹` (gap G.8) and `TangentDeterminedSmooth` remain.
* **`MPolyfold.hasConnectedSmoothNbhds`**: every M-polyfold satisfies
  `MPolyfold.HasConnectedSmoothNbhds` (gap G.90; the hypothesis of
  `hasTwoContSections_orTopology` and `theorem_6_6_17_2021`, rows V6.74, V6.75): the component
  of `x` in `W` is open (Proposition 2.3.7) and connected.
* **`EpGroupoid.NaturalRep.levelConnected`**: every natural representation satisfies
  `NaturalRep.LevelConnected` (the hypothesis of `EP.eqOn_of_level_smooth`, `EP.isVSLUC_of_isSLUC`
  and `EP.proposition_7_4_18_2021`, row V7.104); `NaturalRep.isPreconnected_liftU`,
  `NaturalRep.subset_closure_inter_levelSet`, and **`EpGroupoid.hasConnectedDenseLevelOneReps`**:
  every ep-groupoid satisfies `HasConnectedDenseLevelOneReps` (the hypothesis of
  `theorem_7_6_7_2021`, `corollary_7_6_8_2021`, `proposition_8_1_17_2021_one/two`,
  `EP.isLUC_tangent_lift`, `EP.proposition_8_1_17_two_all_2021`, rows V7.83, V8.45, V8.52).
* The §7.4, §7.6 and §8.1 results restated without these hypotheses:
  `isSmoothUC_of_isVSLUC'`, `lemma_7_4_15_2021_of_isVSLUC` (Lemma 7.4.15),
  `proposition_7_4_16_2021_of_isVSLUC`, `EP.proposition_7_4_16_all_2021_of_isVSLUC`
  (Proposition 7.4.16), `EP.proposition_7_4_17_2021_of_isVSLUC`,
  `EP.proposition_7_4_17_all_2021_of_isVSLUC` (Proposition 7.4.17),
  `EP.isVSLUC_of_isSLUC'`, **`EP.proposition_7_4_18_2021_unconditional`** (Proposition 7.4.18,
  (VSLUC) ⇔ (SLUC), with no hypothesis at all; rows V7.92, V7.103, V7.104);
  `nonEffectivePart_liftOne_eq_of_isClosed`, `theorem_7_6_7_2021_of_isLUC` (Theorem 7.6.7),
  `corollary_7_6_8_2021_of_imp` (Corollary 7.6.8; row V7.83);
  `nonEffectivePart_tangent_eq_of_isOpenMap`, `proposition_8_1_17_2021_one_of_isOpenMap`,
  `EP.proposition_8_1_17_2021_two_of_isOpenMap`, `EP.isLUC_tangent_lift_of_isOpenMap`,
  `EP.proposition_8_1_17_two_all_2021_of_isOpenMap` (Proposition 8.1.17; rows V8.45, V8.52),
  where only the openness of `p` (gap G.8) remains.
* **`EpGroupoid.Examples.JumpingRetract.not_isZhou_of_tangent`**: the example of Appendix 7.6.3
  fails (ZHOU) under the two remaining Part I facts (row V7.95).

The results of §7.4 that take `SmoothRegular` (Propositions 7.4.8, 7.4.10, 7.4.22, Corollary
7.4.11, Theorems 7.4.13, 7.4.24; rows V7.90, V7.91, V7.94, V7.102) lose two of its four fields
here; they become unconditional once `isOpenMap_tangentProj` (gap G.8) and
`TangentDeterminedSmooth` are theorems, through `MPolyfold.smoothRegular_of_tangent`.

## What the text leaves implicit, and the choices made

* The text's choice of `U(x)` in Proposition 7.4.18 and Appendix 7.6.4 is unnecessary: every
  natural representation has `U(x) ∩ X_m` connected, since `U(x)` is open and connected.
* The density `U(x) ⊆ cl(U(x) ∩ X_1)` is the density of `X_∞ ⊆ X_1` in `X` (p. 289).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **The connectedness fact of 2021 §7.4 (gap G.85)**: for every M-polyfold `X` and every
connected open `U ⊆ X`, `U ∩ X_∞` is connected in `X_∞`; Chapter 7's hypothesis
`MPolyfold.SmoothConnected` holds for every M-polyfold. -/
theorem smoothConnected : P.SmoothConnected :=
  fun _ hU hc => P.isPreconnected_smoothVal_preimage hU hc

/-- **Connected smooth parts of small neighbourhoods (gap G.90)**: every M-polyfold satisfies
`MPolyfold.HasConnectedSmoothNbhds`, the hypothesis of property (2) of 2021 Theorem 6.6.17: the
connected component of `x` in `W` is open (Proposition 2.3.7) and its smooth part is connected. -/
theorem hasConnectedSmoothNbhds : P.HasConnectedSmoothNbhds := by
  intro x W hW hxW
  exact ⟨connectedComponentIn W (P.smoothVal x), P.isOpen_connectedComponentIn hW _,
    mem_connectedComponentIn hxW, connectedComponentIn_subset _ _,
    P.isPreconnected_smoothVal_preimage (P.isOpen_connectedComponentIn hW _)
      (isConnected_connectedComponentIn_iff.2 hxW)⟩

/-- Of the four Part I facts bundled in `SmoothRegular`, the density of `X_∞` and the
connectedness of `U ∩ X_∞` hold for every M-polyfold; the openness of `p : TX → X¹` (gap G.8) and
`TangentDeterminedSmooth` remain. -/
theorem smoothRegular_iff_tangent :
    P.SmoothRegular ↔ IsOpenMap P.tangentProj ∧ P.TangentDeterminedSmooth :=
  ⟨fun h => ⟨h.isOpenMap_tangentProj, h.tangentDeterminedSmooth⟩,
    fun h => ⟨P.denseSmooth, P.smoothConnected, h.1, h.2⟩⟩

/-- `SmoothRegular` from its two remaining fields. -/
theorem smoothRegular_of_tangent (hp : IsOpenMap P.tangentProj) (ht : P.TangentDeterminedSmooth) :
    P.SmoothRegular :=
  ⟨P.denseSmooth, P.smoothConnected, hp, ht⟩

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

namespace NaturalRep

variable {X} {x : Obj} (R : X.NaturalRep x)

/-- **The choice of `U(x)` in the proof of 2021 Proposition 7.4.18 (p. 336) is automatic**: for
every natural representation, `U(x) ∩ X_m` is connected in `X_m` for every `m ≥ 1`
(`NaturalRep.LevelConnected`). -/
theorem levelConnected : R.LevelConnected := fun m =>
  X.PObj.isPreconnected_levelVal_preimage (m + 1) R.isOpen_U R.isConnected_U

/-- `U(x) ∩ X_1` is connected in `X¹` (Appendix 7.6.4, p. 349). -/
theorem isPreconnected_liftU : IsPreconnected R.liftU :=
  X.PObj.isPreconnected_levelVal_preimage 1 R.isOpen_U R.isConnected_U

/-- `U(x) ∩ X_1` is dense in `U(x)` (Appendix 7.6.4, p. 349), from the density of `X_∞` (p. 289). -/
theorem subset_closure_inter_levelSet : R.U ⊆ closure (R.U ∩ X.PObj.levelSet 1) :=
  (X.PObj.dense_smoothSet.open_subset_closure_inter R.isOpen_U).trans
    (closure_mono (inter_subset_inter_right _ fun _ hz => mem_iInter.1 hz 1))

end NaturalRep

/-- Every smooth point has a natural representation with `U(x) ∩ X_m` connected for every `m`:
the hypothesis `hR` of `EP.proposition_7_4_18_2021` and `EP.isVSLUC_of_isSLUC`. -/
theorem exists_naturalRep_levelConnected (x : Obj) :
    ∃ R : X.NaturalRep x, R.LevelConnected := by
  obtain ⟨R, -⟩ := X.theorem_7_1 x isOpen_univ (mem_univ _)
  exact ⟨R, R.levelConnected⟩

/-- **Appendix 7.6.4 (2021 p. 349)**: every ep-groupoid satisfies
`HasConnectedDenseLevelOneReps`; every natural representation `U(x)` has `U(x) ∩ X_1` connected
in `X¹` and dense in `U(x)`.  The hypothesis of `theorem_7_6_7_2021`, `corollary_7_6_8_2021`
(V7.83) and `proposition_8_1_17_2021_one` (V8.45) holds for every ep-groupoid. -/
theorem hasConnectedDenseLevelOneReps : X.HasConnectedDenseLevelOneReps := fun x => by
  obtain ⟨R, -⟩ := X.theorem_7_1 (X.PObj.levelVal 1 x) isOpen_univ (mem_univ _)
  exact ⟨R, R.isPreconnected_liftU, R.subset_closure_inter_levelSet⟩

/-! ### §7.4 without `DenseSmooth` and `SmoothConnected` -/

/-- (VSLUC) gives unique continuation through `X_∞` (the core of 2021 Lemma 7.4.15), with no
Part I hypothesis. -/
theorem isSmoothUC_of_isVSLUC' (h : X.IsVSLUC) : X.IsSmoothUC :=
  X.isSmoothUC_of_isVSLUC X.PObj.denseSmooth X.PObj.smoothConnected h

/-- **2021 Lemma 7.4.15, p. 335**: (VSLUC) ⇒ (LUC), with no Part I hypothesis (row V7.92). -/
theorem lemma_7_4_15_2021_of_isVSLUC (h : X.IsVSLUC) : X.IsLUC :=
  X.lemma_7_4_15_2021 X.PObj.denseSmooth X.PObj.smoothConnected h

/-- **2021 Proposition 7.4.16, p. 336, for `X¹`**: (VSLUC) gives (LUC) for `X` and `X¹`, with no
Part I hypothesis (row V7.92). -/
theorem proposition_7_4_16_2021_of_isVSLUC (h : X.IsVSLUC) : X.IsLUC ∧ X.liftOne.IsLUC :=
  X.proposition_7_4_16_2021 X.PObj.denseSmooth X.PObj.smoothConnected h

/-! ### Appendix 7.6.4 without `HasConnectedDenseLevelOneReps` -/

/-- **`(𝐗^T)^1 = (𝐗^1)^T`, 2021 p. 350**, under LUC for `X¹` only. -/
theorem nonEffectivePart_liftOne_eq_of_isClosed (hcl : IsClosed X.liftOne.nonEffectivePart) :
    X.liftOne.nonEffectivePart = X.PMor.levelVal 1 ⁻¹' X.nonEffectivePart :=
  X.nonEffectivePart_liftOne_eq hcl X.hasConnectedDenseLevelOneReps

/-- **2021 Theorem 7.6.7, p. 351, for `i = 1` and as sets**, under LUC for `X¹` only (row
V7.83). -/
theorem theorem_7_6_7_2021_of_isLUC (hLUC : X.liftOne.IsLUC) :
    ∃ hT : X.liftOne.nonEffectivePart = X.PMor.levelVal 1 ⁻¹' X.nonEffectivePart,
      (∀ φ, X.reducedLevelOneMap hT (X.liftOne.reducedπ φ) = X.reducedπ (X.PMor.levelVal 1 φ)) ∧
      Injective (X.reducedLevelOneMap hT) ∧ Continuous (X.reducedLevelOneMap hT) ∧
      range (X.reducedLevelOneMap hT) = X.reducedπ '' X.PMor.levelSet 1 :=
  X.theorem_7_6_7_2021 hLUC X.hasConnectedDenseLevelOneReps

/-- **2021 Corollary 7.6.8, p. 351, for `i = 1` and as sets**, with the implication from (ZHOU)
to LUC for `X¹` as the only hypothesis (row V7.83). -/
theorem corollary_7_6_8_2021_of_imp {Zhou : Prop} (hZ : Zhou) (hSLUC : Zhou → X.liftOne.IsLUC) :
    ∃ hT : X.liftOne.nonEffectivePart = X.PMor.levelVal 1 ⁻¹' X.nonEffectivePart,
      (∀ φ, X.reducedLevelOneMap hT (X.liftOne.reducedπ φ) = X.reducedπ (X.PMor.levelVal 1 φ)) ∧
      Injective (X.reducedLevelOneMap hT) ∧ Continuous (X.reducedLevelOneMap hT) ∧
      range (X.reducedLevelOneMap hT) = X.reducedπ '' X.PMor.levelSet 1 :=
  X.corollary_7_6_8_2021 hZ hSLUC X.hasConnectedDenseLevelOneReps

/-! ### Proposition 8.1.17 without `HasConnectedDenseLevelOneReps` -/

/-- `(T𝐗)^T = p⁻¹((𝐗¹)^T)` under (LUC) for `X¹`, with `p : T𝐗 → 𝐗¹` open (gap G.8) as the only
added hypothesis. -/
theorem nonEffectivePart_tangent_eq_of_isOpenMap (h : X.liftOne.IsLUC)
    (hp : IsOpenMap X.PMor.tangentProj) :
    X.tangentEpGroupoid.nonEffectivePart = X.PMor.tangentProj ⁻¹' X.liftOne.nonEffectivePart :=
  X.nonEffectivePart_tangent_eq h X.hasConnectedDenseLevelOneReps hp

/-- **2021 Proposition 8.1.17 (1), p. 371**: if `X¹` has (LUC), so has `TX`; with `p` open
(gap G.8) as the only added hypothesis (row V8.45). -/
theorem proposition_8_1_17_2021_one_of_isOpenMap (h : X.liftOne.IsLUC)
    (hp : IsOpenMap X.PMor.tangentProj) : X.tangentEpGroupoid.IsLUC :=
  X.proposition_8_1_17_2021_one h X.hasConnectedDenseLevelOneReps hp

end EpGroupoid

namespace EP

open EpGroupoid

/-- **2021 Proposition 7.4.16, p. 336**: (VSLUC) for `X` gives (VSLUC) and (LUC) for every
`X^i`, with no Part I hypothesis (row V7.103). -/
theorem proposition_7_4_16_all_2021_of_isVSLUC (A : EP.{u}) (h : A.X.IsVSLUC) (i : ℕ) :
    (A.lift i).X.IsVSLUC ∧ (A.lift i).X.IsLUC :=
  A.proposition_7_4_16_all_2021 h A.X.PObj.denseSmooth
    (fun i => (A.lift i).X.PObj.smoothConnected) i

/-- **2021 Proposition 7.4.17, p. 336**: (VSLUC) ⇒ (SLUC), with (VSLUC) for `X` only and no
Part I hypothesis (row V7.103). -/
theorem proposition_7_4_17_all_2021_of_isVSLUC (A : EP.{u}) (h : A.X.IsVSLUC) : A.IsSLUC :=
  A.proposition_7_4_17_all_2021 h A.X.PObj.denseSmooth fun i => (A.lift i).X.PObj.smoothConnected

/-- **2021 Proposition 7.4.17, p. 336**: (VSLUC) for every `X^i` gives (SLUC), with no Part I
hypothesis (row V7.92). -/
theorem proposition_7_4_17_2021_of_isVSLUC (A : EP.{u}) (h : ∀ i, (A.lift i).X.IsVSLUC) :
    A.IsSLUC :=
  proposition_7_4_17_2021 A h (fun i => (A.lift i).X.PObj.denseSmooth)
    fun i => (A.lift i).X.PObj.smoothConnected

/-- (SLUC) ⇒ (VSLUC), the new direction of 2021 Proposition 7.4.18, with no hypothesis (row
V7.104). -/
theorem isVSLUC_of_isSLUC' (A : EP.{u}) (h : A.IsSLUC) : A.X.IsVSLUC :=
  A.isVSLUC_of_isSLUC h A.X.PObj.denseSmooth fun _ => A.X.exists_naturalRep_levelConnected _

/-- **2021 Proposition 7.4.18, p. 336 (new in the 2021 edition)**: (VSLUC) ⇔ (SLUC), with no
hypothesis (rows V7.92, V7.104; the density, connectedness and `U(x)` hypotheses of
`proposition_7_4_18_2021` are theorems). -/
theorem proposition_7_4_18_2021_unconditional (A : EP.{u}) : A.X.IsVSLUC ↔ A.IsSLUC :=
  A.proposition_7_4_18_2021 A.X.PObj.denseSmooth (fun i => (A.lift i).X.PObj.smoothConnected)
    fun _ => A.X.exists_naturalRep_levelConnected _

/-- **2021 Proposition 8.1.17 (2), p. 371, for `(TX)⁰`**: (SLUC) for `X` gives (LUC) for `TX`,
with `p` open (gap G.8) as the only added hypothesis (row V8.45). -/
theorem proposition_8_1_17_2021_two_of_isOpenMap (A : EP.{u}) (h : A.IsSLUC)
    (hp : IsOpenMap A.X.PMor.tangentProj) : A.X.tangentEpGroupoid.IsLUC :=
  EpGroupoid.proposition_8_1_17_2021_two A h A.X.hasConnectedDenseLevelOneReps hp

/-- Under (SLUC) every `T(X^i)` has (LUC), with `p` open for every `X^i` (gap G.8) as the only
added hypothesis (row V8.52). -/
theorem isLUC_tangent_lift_of_isOpenMap (A : EP.{u}) (h : A.IsSLUC)
    (hp : ∀ i, IsOpenMap (A.lift i).X.PMor.tangentProj) (i : ℕ) :
    (A.lift i).X.tangentEpGroupoid.IsLUC :=
  A.isLUC_tangent_lift h (fun i => (A.lift i).X.hasConnectedDenseLevelOneReps) hp i

/-- **2021 Proposition 8.1.17 (2), p. 371**: if `X` has (SLUC), so has `TX`; with `p` open for
every `X^i` (gap G.8) as the only added hypothesis (row V8.52). -/
theorem proposition_8_1_17_two_all_2021_of_isOpenMap (A : EP.{u}) (h : A.IsSLUC)
    (hp : ∀ i, IsOpenMap (A.lift i).X.PMor.tangentProj) : A.tangentEP.IsSLUC :=
  A.proposition_8_1_17_two_all_2021 h (fun i => (A.lift i).X.hasConnectedDenseLevelOneReps) hp

end EP

namespace EpGroupoid.Examples.JumpingRetract

/-- **2021 p. 331**: the ep-groupoid of Appendix 7.6.3 does not satisfy (ZHOU), under the two
remaining Part I facts for its object M-polyfold (`p` open, gap G.8, and
`TangentDeterminedSmooth`); the density and connectedness facts are theorems (row V7.95). -/
theorem not_isZhou_of_tangent (hp : IsOpenMap X.PObj.tangentProj)
    (ht : X.PObj.TangentDeterminedSmooth) : ¬ X.IsZhou :=
  not_isZhou (X.PObj.smoothRegular_of_tangent hp ht)

end EpGroupoid.Examples.JumpingRetract

end Polyfold
