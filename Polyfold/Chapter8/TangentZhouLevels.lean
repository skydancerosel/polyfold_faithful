import Polyfold.Chapter8.TangentZhou
import Polyfold.Chapter2.TangentLiftAll

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §8.1 "Regularity Properties and Tangents": **Proposition 8.1.17 (2)** (p. 371, new in the
2021 edition) for every lift `(TX)^i`.  Numbers and pages are the 2021 text's.  Part (1) and the
case `i = 0` of part (2) are in `Polyfold/Chapter8/TangentZhou.lean`.

# (SLUC) for `X` gives (SLUC) for `TX`

## The text, paraphrased

(Proposition 8.1.17 (2), p. 371) If `X` has the strong local unique continuation property, so has
`TX`.  *Proof*: (SLUC) for `X` means (LUC) for every `X^i`; by part (1) every `T(X^i)` has (LUC);
since naturally `(TX)^i = T(X^i)`, every `(TX)^i` has (LUC), i.e. `TX` has (SLUC).

## What is formalized

* `MPolyfold.ScEquiv.toHomeomorph` (an sc-diffeomorphism is a homeomorphism).
* `EP.tangentEP` (the tangent `TX` of a bundled ep-groupoid `X ∈ EP.{u}`, in `EP.{max u 1}`).
* `EpGroupoid.EpEquiv`: sc-diffeomorphisms of the object and the morphism M-polyfolds commuting
  with source and target; `refl`, `trans`, `shift` (the index raise, to `X¹ → X'¹`),
  `EpEquiv.nonEffectivePart_eq` (`𝐗'^T` corresponds to `𝐗^T`) and `EpEquiv.isLUC` ((LUC) is
  transported, by 2021 Proposition 7.2.21).
* `EpGroupoid.tangentShiftEpEquiv`: **`T(X¹) ≡ (TX)¹` as ep-groupoids**, from 2021 Proposition
  2.3.17 for `i = 1` on objects and morphisms; it commutes with `s` and `t` by the naturality of
  the inclusion `T(X¹) → TX` (`MPolyfold.tangentLower_tangentMap`).
* `EP.tangentLiftEpEquiv`: **`T(X^i) ≡ (TX)^i` as ep-groupoids, for every `i`** (by recursion,
  as `BundledMPolyfold.tangentLiftEquiv` of `TangentLiftAll.lean`).
* `EP.isLUC_tangent_lift` (every `T(X^i)` has (LUC)) and **`EP.proposition_8_1_17_two_all_2021`**
  (Proposition 8.1.17 (2): `TX` has (SLUC)).
* Witnesses: `EpGroupoid.hasConnectedDenseLevelOneReps_of_subsingleton`,
  `Examples.proposition_8_1_17_two_all_2021_pointEP` (the hypotheses hold for the point
  ep-groupoid and all its lifts); `EpEquiv.refl` and `EP.tangentLiftEpEquiv` for `EpEquiv`.

## What the text leaves implicit, and the choices made

* "Naturally `(TX)^i = T(X^i)`" is used only through source and target: `EpEquiv` asks for
  sc-diffeomorphisms of objects and morphisms commuting with `s` and `t` (compatibility with the
  other structure maps is not needed for (LUC) and is not formalized).  (LUC) is transported
  through the characterization of 2021 Proposition 7.2.21 (`𝐗^T` closed).
* As in `proposition_8_1_17_2021_one`, part (1) is applied to every `X^i` with the hypotheses
  `HasConnectedDenseLevelOneReps` (the text's `V(x) = U(x) ∩ X₁`, connected and dense) and the
  openness of `p : T𝐗 → 𝐗¹` (Part I, gap G.8), now for every `X^i`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u v w

namespace MPolyfold.ScEquiv

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- An sc-diffeomorphism is a homeomorphism. -/
def toHomeomorph (e : ScEquiv P Q) : X ≃ₜ Y where
  toEquiv := e.toEquiv
  continuous_toFun := continuousOn_univ.1 e.isScSmoothMap_toFun.continuousOn
  continuous_invFun := continuousOn_univ.1 e.isScSmoothMap_invFun.continuousOn

end MPolyfold.ScEquiv

/-- The tangent `TX` (2021 Theorem 8.1.1; 2017 Theorem 8.1) of a bundled ep-groupoid `X ∈ EP.{u}`,
as an object of `EP.{max u 1}` (`EP.tangent` of `TangentEp.lean` for `X ∈ EP.{max u 1}`). -/
def EP.tangentEP (A : EP.{u}) : EP.{max u 1} where
  Obj := A.X.PObj.TangentSpace
  Mor := A.X.PMor.TangentSpace
  X := A.X.tangentEpGroupoid

namespace EpGroupoid

/-! ### Equivalences of ep-groupoids compatible with source and target -/

section EpEquivSec

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {Obj'' Mor'' : Type w} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']

/-- Sc-diffeomorphisms of the object and of the morphism M-polyfolds commuting with the source and
the target maps (the part of an isomorphism of ep-groupoids used for (LUC)).  Witnesses:
`EpEquiv.refl`, `EP.tangentLiftEpEquiv`. -/
structure EpEquiv (X : EpGroupoid Obj Mor) (X' : EpGroupoid Obj' Mor') where
  /-- On objects. -/
  obj : MPolyfold.ScEquiv X.PObj X'.PObj
  /-- On morphisms. -/
  mor : MPolyfold.ScEquiv X.PMor X'.PMor
  src_mor : ∀ φ, X'.src (mor φ) = obj (X.src φ)
  tgt_mor : ∀ φ, X'.tgt (mor φ) = obj (X.tgt φ)

namespace EpEquiv

variable {X : EpGroupoid Obj Mor} {X' : EpGroupoid Obj' Mor'} {X'' : EpGroupoid Obj'' Mor''}

variable (X) in
/-- The identity. -/
def refl : EpEquiv X X :=
  ⟨MPolyfold.ScEquiv.refl _, MPolyfold.ScEquiv.refl _, fun _ => rfl, fun _ => rfl⟩

/-- The composite. -/
def trans (e : EpEquiv X X') (e' : EpEquiv X' X'') : EpEquiv X X'' where
  obj := e.obj.trans e'.obj
  mor := e.mor.trans e'.mor
  src_mor φ := (e'.src_mor _).trans (congrArg e'.obj (e.src_mor φ))
  tgt_mor φ := (e'.tgt_mor _).trans (congrArg e'.obj (e.tgt_mor φ))

/-- The index raise `X¹ ≃ X'¹` (2021 Proposition 7.3.9; 2017 Proposition 7.11; Chapter 7's
`liftOne`). -/
def shift (e : EpEquiv X X') : EpEquiv X.liftOne X'.liftOne where
  obj := e.obj.shift
  mor := e.mor.shift
  src_mor φ := MPolyfold.level_ext (e.src_mor (X.PMor.levelVal 1 φ))
  tgt_mor φ := MPolyfold.level_ext (e.tgt_mor (X.PMor.levelVal 1 φ))

/-- The non-effective parts correspond: `𝐗'^T = e(𝐗^T)` (`k ∈ 𝐗^T` iff `s = t` near `k`). -/
theorem nonEffectivePart_eq (e : EpEquiv X X') :
    X'.nonEffectivePart = e.mor.invFun ⁻¹' X.nonEffectivePart := by
  ext k'
  rw [mem_preimage, X'.mem_nonEffectivePart_iff, X.mem_nonEffectivePart_iff]
  have hk : e.mor.toHomeomorph (e.mor.invFun k') = k' := e.mor.right_inv k'
  conv_lhs => rw [← hk, ← e.mor.toHomeomorph.map_nhds_eq, Filter.eventually_map]
  refine Filter.eventually_congr (Filter.Eventually.of_forall fun φ => ?_)
  change X'.src (e.mor φ) = X'.tgt (e.mor φ) ↔ _
  rw [e.src_mor, e.tgt_mor]
  exact e.obj.toEquiv.injective.eq_iff

/-- **(LUC) is transported** by an `EpEquiv` (through 2021 Proposition 7.2.21). -/
theorem isLUC (e : EpEquiv X X') (h : X.IsLUC) : X'.IsLUC := by
  rw [X'.proposition_7_2_21_2021, e.nonEffectivePart_eq]
  exact (X.proposition_7_2_21_2021.1 h).preimage e.mor.toHomeomorph.symm.continuous

end EpEquiv

end EpEquivSec

/-! ### `T(X¹) ≡ (TX)¹` as ep-groupoids -/

section TangentShift

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **`T(X¹) ≡ (TX)¹` as ep-groupoids**: 2021 Proposition 2.3.17 (`i = 1`) on the object and the
morphism M-polyfolds; `(Ts)¹ ∘ Φ = Φ ∘ T(s¹)` and likewise for `t` by the naturality of the
inclusion `T(X¹) → TX`. -/
def tangentShiftEpEquiv : EpEquiv X.liftOne.tangentEpGroupoid X.tangentEpGroupoid.liftOne where
  obj := MPolyfold.tangentShiftScEquiv X.PObj
  mor := MPolyfold.tangentShiftScEquiv X.PMor
  src_mor v := MPolyfold.level_ext (MPolyfold.tangentLower_tangentMap X.isScSmoothMap_src
    (f₁ := X.liftOne.src) (fun _ => rfl) v).symm
  tgt_mor v := MPolyfold.level_ext (MPolyfold.tangentLower_tangentMap X.isScSmoothMap_tgt
    (f₁ := X.liftOne.tgt) (fun _ => rfl) v).symm

/-- **Witness**: `HasConnectedDenseLevelOneReps` holds when there is at most one object, and it is
smooth. -/
theorem hasConnectedDenseLevelOneReps_of_subsingleton [Subsingleton Obj]
    (hs : X.PObj.smoothSet = univ) : X.HasConnectedDenseLevelOneReps := fun x => by
  obtain ⟨R, -⟩ := X.theorem_7_1 (X.PObj.levelVal 1 x) isOpen_univ (mem_univ _)
  refine ⟨R, Set.Subsingleton.isPreconnected fun _ _ _ _ =>
    MPolyfold.level_ext (Subsingleton.elim _ _), ?_⟩
  have h1 : X.PObj.levelSet 1 = univ := eq_univ_of_forall fun y =>
    MPolyfold.smoothSet_subset_levelSet 1 (by rw [hs]; exact mem_univ y)
  rw [h1, inter_univ]
  exact subset_closure

end TangentShift

end EpGroupoid

namespace EP

open EpGroupoid

/-- **`T(X^i) ≡ (TX)^i` as ep-groupoids, for every `i`**: `id` for `i = 0`, and the index raise of
the case `i` after `T((X^i)¹) ≡ (T(X^i))¹` (`tangentShiftEpEquiv`). -/
def tangentLiftEpEquiv (A : EP.{u}) :
    (i : ℕ) → EpEquiv (A.lift i).X.tangentEpGroupoid (A.tangentEP.lift i).X
  | 0 => EpEquiv.refl _
  | i + 1 => ((A.lift i).X.tangentShiftEpEquiv).trans (tangentLiftEpEquiv A i).shift

/-- Under (SLUC) every `T(X^i)` has (LUC) (2021 Proposition 8.1.17 (1) for `X^i`). -/
theorem isLUC_tangent_lift (A : EP.{u}) (h : A.IsSLUC)
    (hR : ∀ i, (A.lift i).X.HasConnectedDenseLevelOneReps)
    (hp : ∀ i, IsOpenMap (A.lift i).X.PMor.tangentProj) (i : ℕ) :
    (A.lift i).X.tangentEpGroupoid.IsLUC :=
  (A.lift i).X.proposition_8_1_17_2021_one (h (i + 1)) (hR i) (hp i)

/-- **2021 Proposition 8.1.17 (2), p. 371 (new in the 2021 edition)**: if `X` has (SLUC), so has
`TX`: every `(TX)^i` has (LUC).  The hypotheses are those of part (1)
(`proposition_8_1_17_2021_one`) for every `X^i`. -/
theorem proposition_8_1_17_two_all_2021 (A : EP.{u}) (h : A.IsSLUC)
    (hR : ∀ i, (A.lift i).X.HasConnectedDenseLevelOneReps)
    (hp : ∀ i, IsOpenMap (A.lift i).X.PMor.tangentProj) : A.tangentEP.IsSLUC := fun i =>
  (A.tangentLiftEpEquiv i).isLUC (A.isLUC_tangent_lift h hR hp i)

end EP

namespace EpGroupoid.Examples

/-- **Witness**: the hypotheses of `EP.proposition_8_1_17_two_all_2021` hold for the point
ep-groupoid. -/
theorem proposition_8_1_17_two_all_2021_pointEP : pointEP.tangentEP.IsSLUC := by
  refine pointEP.proposition_8_1_17_two_all_2021 isSLUC_pointEP (fun i => ?_) (fun i => ?_)
  · obtain ⟨h1, -, h3⟩ := lift_pointEP i
    exact (pointEP.lift i).X.hasConnectedDenseLevelOneReps_of_subsingleton h3
  · obtain ⟨-, h2, -⟩ := lift_pointEP i
    exact isOpenMap_tangentProj_of_subsingleton _

end EpGroupoid.Examples

end Polyfold
