import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_18

/-! Round trip for V10_18 (2021 Theorem 10.2.2, first claim, p. 477 (2017: Theorem 10.2):
`X ×_Y Z` is an ep-groupoid).

The item lists the definitions `Admissible`, `PA`, `PB`, `PObj`, `PMor`, `epGroupoid`
(vocabulary; the theorem itself is the *definition* `epGroupoid`) and nineteen lemmas; `A` is the
conjunction of their types, all universes at `0` (`B` lives in `Type`), one definition `Aᵢ` per
lemma (see the harness note at the end).

**Neither direction is proved.**  The two sides put different M-polyfold structures on
different carriers:

* `A` (the project): objects `Obj F G = X _F×ₛ (𝐘 ₜ×_G Z)`, a subtype of `ObjX × objRight G` where
  `objRight G ⊆ MorY × ObjZ` is itself a subtype; the M-polyfold `PObj F G h` is the *iterated*
  sub-M-polyfold structure (`objRight G ⊆ 𝐘 × Z`, then `objSet F G ⊆ X × PA G`), likewise for
  morphisms.  The hypothesis is `Admissible F G` (`F` or `G` a local sc-diffeomorphism on objects).
* `B` (blind): objects the subtype `objSetB F G` of the flat triple product
  `ObjX × MorY × ObjZ`, with the sub-M-polyfold structure of `X × (𝐘 × Z)`
  (`subPolyfold hS`, `hS : (X.PObj.prod (Y.PMor.prod Z.PObj)).IsSubMPolyfold (objSetB F G)`),
  likewise for morphisms; hypothesis `F.IsEquivalence`.

`A → B` needs (i) `hS`, `hT`: `objSetB`/`morSetB` are sub-M-polyfolds of the triple products (a
transitivity statement "a sub-M-polyfold of `X × A`, `A` a sub-M-polyfold of `𝐘 × Z`, is a
sub-M-polyfold of `X × (𝐘 × Z)`", or the text's retraction (10.8) on the triple product), and
(ii) the transport of the ep-groupoid along the entrywise homeomorphisms `objHomeo`, `morHomeo`
below, i.e. that they are sc-diffeomorphisms between `PObj F G h` and `subPolyfold hS` and that
local sc-diffeomorphisms, sc-smoothness of `u`, `ι` and condition (4) on the fibred product
`𝐋 ₛ×ₜ 𝐋` pass along them.  None of this is in the project (the project's header: "the
comparison with a structure induced from the triple product is not needed below"); it is
standard Part I mathematics (believed true), well beyond glue.  `B → A`: `A` consists of lemmas
about the project's own carriers and structures (and five general helpers), which follow from
`B` only through the same comparison in the other direction.

What is proved here (partial, for the diagnosis):
* `A_to_BIter`: `A` assembles (using its lemmas, not the definition `epGroupoid`) into an
  ep-groupoid on the project's carriers with the groupoid `groupoid F G` and the iterated
  structures `PObj`, `PMor`, for `F` an equivalence (`Admissible.of_isEquivalence_left`).
* `objHomeo`, `morHomeo`: the project's carriers are homeomorphic to `B`'s subtypes, entrywise;
  together with V10_17 (the structure maps of `groupoid F G` are the text's) this locates the
  whole gap in the M-polyfold structures (iterated vs. triple-product sub-M-polyfold). -/

namespace RoundTrip.V10_18
open Polyfold Set Function WeakFibredProduct

/-! ### The project's statement (universes at `0`) -/

def A1 : Prop := type_of% @Polyfold.WeakFibredProduct.Admissible.of_isEquivalence_left.{0, 0, 0}
def A2 : Prop := type_of% @Polyfold.WeakFibredProduct.Admissible.of_isEquivalence_right.{0, 0, 0}
def A3 : Prop := type_of% @Polyfold.WeakFibredProduct.isSubMPolyfold_objSet.{0, 0, 0}
def A4 : Prop := type_of% @Polyfold.WeakFibredProduct.isSubMPolyfold_morSet.{0, 0, 0}
def A5 : Prop := type_of% @Polyfold.WeakFibredProduct.isLocalScDiffeo_z.{0, 0, 0}
def A6 : Prop := type_of% @Polyfold.WeakFibredProduct.isLocalScDiffeo_k.{0, 0, 0}
def A7 : Prop := type_of% @Polyfold.WeakFibredProduct.isLocalScDiffeo_x.{0, 0, 0}
def A8 : Prop := type_of% @Polyfold.WeakFibredProduct.isLocalScDiffeo_h.{0, 0, 0}
def A9 : Prop := type_of% @Polyfold.WeakFibredProduct.isLocalScDiffeo_src.{0, 0, 0}
def A10 : Prop := type_of% @Polyfold.WeakFibredProduct.isLocalScDiffeo_tgt.{0, 0, 0}
def A11 : Prop := type_of% @Polyfold.WeakFibredProduct.isScSmoothMap_unit.{0, 0, 0}
def A12 : Prop := type_of% @Polyfold.WeakFibredProduct.isScSmoothMap_inv.{0, 0, 0}
def A13 : Prop := type_of% @Polyfold.WeakFibredProduct.isScSmoothComp.{0, 0, 0}
def A14 : Prop := type_of% @Polyfold.WeakFibredProduct.exists_isProperMap.{0, 0, 0}
def A15 : Prop := type_of% @Polyfold.MPolyfold.IsLocalScDiffeo.of_comm.{0, 0, 0, 0}
def A16 : Prop := type_of% @Polyfold.MPolyfold.isLocalScDiffeo_snd_fibredProduct.{0, 0, 0}
def A17 : Prop := type_of% @Polyfold.MPolyfold.isLocalScDiffeo_fst_fibredProduct.{0, 0, 0}
def A18 : Prop := type_of% @Polyfold.EpGroupoid.isScSmoothOn_comp_of.{0, 0}
def A19 : Prop := type_of% @Polyfold.EpGroupoid.tendsto_comp.{0, 0}

/-- The project's statement. -/
def A : Prop :=
  A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A6 ∧ A7 ∧ A8 ∧ A9 ∧ A10 ∧ A11 ∧ A12 ∧ A13 ∧ A14 ∧ A15 ∧ A16 ∧ A17 ∧
    A18 ∧ A19

theorem A_holds : A :=
  ⟨@Polyfold.WeakFibredProduct.Admissible.of_isEquivalence_left.{0, 0, 0},
    @Polyfold.WeakFibredProduct.Admissible.of_isEquivalence_right.{0, 0, 0},
    @Polyfold.WeakFibredProduct.isSubMPolyfold_objSet.{0, 0, 0},
    @Polyfold.WeakFibredProduct.isSubMPolyfold_morSet.{0, 0, 0},
    @Polyfold.WeakFibredProduct.isLocalScDiffeo_z.{0, 0, 0},
    @Polyfold.WeakFibredProduct.isLocalScDiffeo_k.{0, 0, 0},
    @Polyfold.WeakFibredProduct.isLocalScDiffeo_x.{0, 0, 0},
    @Polyfold.WeakFibredProduct.isLocalScDiffeo_h.{0, 0, 0},
    @Polyfold.WeakFibredProduct.isLocalScDiffeo_src.{0, 0, 0},
    @Polyfold.WeakFibredProduct.isLocalScDiffeo_tgt.{0, 0, 0},
    @Polyfold.WeakFibredProduct.isScSmoothMap_unit.{0, 0, 0},
    @Polyfold.WeakFibredProduct.isScSmoothMap_inv.{0, 0, 0},
    @Polyfold.WeakFibredProduct.isScSmoothComp.{0, 0, 0},
    @Polyfold.WeakFibredProduct.exists_isProperMap.{0, 0, 0},
    @Polyfold.MPolyfold.IsLocalScDiffeo.of_comm.{0, 0, 0, 0},
    @Polyfold.MPolyfold.isLocalScDiffeo_snd_fibredProduct.{0, 0, 0},
    @Polyfold.MPolyfold.isLocalScDiffeo_fst_fibredProduct.{0, 0, 0},
    @Polyfold.EpGroupoid.isScSmoothOn_comp_of.{0, 0},
    @Polyfold.EpGroupoid.tendsto_comp.{0, 0}⟩

/-! ### Partial results -/

/-- `B` with the project's carriers and iterated structures in place of the triple-product
sub-M-polyfolds: for an equivalence `F`, an ep-groupoid with the groupoid `groupoid F G` of
Definition 10.2.1 (checked against the text in V10_17) and the structures `PObj`, `PMor`. -/
def BIter : Prop :=
  ∀ (ObjX MorX ObjY MorY ObjZ MorZ : Type)
    [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
    [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
    (X : EpGroupoid ObjX MorX) (Y : EpGroupoid ObjY MorY) (Z : EpGroupoid ObjZ MorZ)
    (F : EpFunctor X Y) (G : EpFunctor Z Y),
    F.IsEquivalence → ∃ (h : Admissible F G) (E : EpGroupoid (Obj F G) (Mor F G)),
      E.toGroupoidStr = groupoid F G ∧ E.PObj = PObj F G h ∧ E.PMor = PMor F G h

theorem A_to_BIter : A → BIter := by
  intro hA
  obtain ⟨hleft, -, -, -, -, -, -, -, hsrc, htgt, hunit, hinv, hcomp, hprop, -⟩ := hA
  intro ObjX MorX ObjY MorY ObjZ MorZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X Y Z F G hF
  have h : Admissible F G := hleft hF
  exact ⟨h,
    { toGroupoidStr := groupoid F G
      PObj := PObj F G h
      PMor := PMor F G h
      isLocalScDiffeo_src := hsrc h
      isLocalScDiffeo_tgt := htgt h
      isScSmoothMap_unit := hunit h
      isScSmoothMap_inv := hinv h
      exists_isProperMap := hprop
      isScSmoothComp := hcomp h }, rfl, rfl, rfl⟩

section Carriers

variable {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjZ MorZ : Type} [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
  [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
  {X : EpGroupoid ObjX MorX} {Y : EpGroupoid ObjY MorY} {Z : EpGroupoid ObjZ MorZ}
  (F : EpFunctor X Y) (G : EpFunctor Z Y)

/-- The project's objects (nested subtypes) and `B`'s (a subtype of the flat triple product) are
homeomorphic, entrywise: `(x, ϕ, z) ↦ (x, ϕ, z)`. -/
def objHomeo : Obj F G ≃ₜ objSetB F G where
  toFun o := ⟨(o.x, o.φ, o.z), o.src_φ, o.tgt_φ⟩
  invFun p := Obj.mk F G p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_x.prodMk (continuous_φ.prodMk continuous_z)).subtype_mk _
  continuous_invFun := continuous_obj_of
    (show Continuous fun p : objSetB F G => p.1.1 from continuous_fst.comp continuous_subtype_val)
    (show Continuous fun p : objSetB F G => p.1.2.1 from
      (continuous_fst.comp continuous_snd).comp continuous_subtype_val)
    (show Continuous fun p : objSetB F G => p.1.2.2 from
      (continuous_snd.comp continuous_snd).comp continuous_subtype_val)

/-- The same for the morphisms: `(h, ϕ, k) ↦ (h, ϕ, k)`. -/
def morHomeo : Mor F G ≃ₜ morSetB F G where
  toFun m := ⟨(m.h, m.φ, m.k), m.src_φ, m.tgt_φ⟩
  invFun q := Mor.mk F G q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_h.prodMk (continuous_mφ.prodMk continuous_k)).subtype_mk _
  continuous_invFun := continuous_mor_of
    (show Continuous fun q : morSetB F G => q.1.1 from continuous_fst.comp continuous_subtype_val)
    (show Continuous fun q : morSetB F G => q.1.2.1 from
      (continuous_fst.comp continuous_snd).comp continuous_subtype_val)
    (show Continuous fun q : morSetB F G => q.1.2.2 from
      (continuous_snd.comp continuous_snd).comp continuous_subtype_val)

end Carriers

/-! ### Harness checks

The statements `A5`–`A13` mention the vocabulary definitions `PObj`, `PMor`, whose bodies are
`subPolyfold (isSubMPolyfold_objSet …)`, `subPolyfold (isSubMPolyfold_morSet …)` (banned theorems,
direct references), and `A13` (`isScSmoothComp`) mentions `isLocalScDiffeo_src h`,
`isLocalScDiffeo_tgt h` in its statement; `BIter` mentions `groupoid` (whose body uses the
V10_17 lemmas only) and `PObj`, `PMor`.  So plain `#rt_check` fails on `A_to_BIter` for these
names only.  `#rt_check_except_defs` is the harness traversal `rtCollect` with the bodies of
`A13`, `PObj`, `PMor` not unfolded: `A_to_BIter` takes the lemmas from its hypothesis and never
uses `epGroupoid`. -/

open Lean Elab Command in
/-- `#rt_check_except_defs T [nᵢ]`: the proof of `T` reaches the banned `nᵢ` only through the
statement `A13` and the bodies of the vocabulary definitions `PObj`, `PMor`. -/
elab "#rt_check_except_defs " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let used := rtCollect env roots.toList
    ((((NameSet.empty.insert ``RoundTrip.V10_18.A13).insert ``Polyfold.WeakFibredProduct.PObj).insert
      ``Polyfold.WeakFibredProduct.PMor))
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do
    throwError "FAIL: {t.getId} uses {bad} outside A13, PObj, PMor"
  logInfo m!"OK: {t.getId} reaches the banned theorems only through A13, PObj, PMor"

#rt_check_except_defs RoundTrip.V10_18.A_to_BIter [
  Polyfold.WeakFibredProduct.Admissible.of_isEquivalence_left,
  Polyfold.WeakFibredProduct.Admissible.of_isEquivalence_right,
  Polyfold.WeakFibredProduct.isSubMPolyfold_objSet,
  Polyfold.WeakFibredProduct.isSubMPolyfold_morSet,
  Polyfold.WeakFibredProduct.isLocalScDiffeo_z, Polyfold.WeakFibredProduct.isLocalScDiffeo_k,
  Polyfold.WeakFibredProduct.isLocalScDiffeo_x, Polyfold.WeakFibredProduct.isLocalScDiffeo_h,
  Polyfold.WeakFibredProduct.isLocalScDiffeo_src, Polyfold.WeakFibredProduct.isLocalScDiffeo_tgt,
  Polyfold.WeakFibredProduct.isScSmoothMap_unit, Polyfold.WeakFibredProduct.isScSmoothMap_inv,
  Polyfold.WeakFibredProduct.isScSmoothComp, Polyfold.WeakFibredProduct.exists_isProperMap,
  Polyfold.MPolyfold.IsLocalScDiffeo.of_comm,
  Polyfold.MPolyfold.isLocalScDiffeo_snd_fibredProduct,
  Polyfold.MPolyfold.isLocalScDiffeo_fst_fibredProduct,
  Polyfold.EpGroupoid.isScSmoothOn_comp_of, Polyfold.EpGroupoid.tendsto_comp]

/--
error: rt_check FAIL: RoundTrip.V10_18.A_to_BIter uses [Polyfold.WeakFibredProduct.isSubMPolyfold_objSet,
 Polyfold.WeakFibredProduct.isSubMPolyfold_morSet,
 Polyfold.WeakFibredProduct.isLocalScDiffeo_z,
 Polyfold.WeakFibredProduct.isLocalScDiffeo_k,
 Polyfold.WeakFibredProduct.isLocalScDiffeo_x,
 Polyfold.WeakFibredProduct.isLocalScDiffeo_h,
 Polyfold.WeakFibredProduct.isLocalScDiffeo_src,
 Polyfold.WeakFibredProduct.isLocalScDiffeo_tgt,
 Polyfold.MPolyfold.IsLocalScDiffeo.of_comm,
 Polyfold.MPolyfold.isLocalScDiffeo_snd_fibredProduct,
 Polyfold.MPolyfold.isLocalScDiffeo_fst_fibredProduct]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_18.A_to_BIter [
  Polyfold.WeakFibredProduct.Admissible.of_isEquivalence_left,
  Polyfold.WeakFibredProduct.Admissible.of_isEquivalence_right,
  Polyfold.WeakFibredProduct.isSubMPolyfold_objSet,
  Polyfold.WeakFibredProduct.isSubMPolyfold_morSet,
  Polyfold.WeakFibredProduct.isLocalScDiffeo_z, Polyfold.WeakFibredProduct.isLocalScDiffeo_k,
  Polyfold.WeakFibredProduct.isLocalScDiffeo_x, Polyfold.WeakFibredProduct.isLocalScDiffeo_h,
  Polyfold.WeakFibredProduct.isLocalScDiffeo_src, Polyfold.WeakFibredProduct.isLocalScDiffeo_tgt,
  Polyfold.WeakFibredProduct.isScSmoothMap_unit, Polyfold.WeakFibredProduct.isScSmoothMap_inv,
  Polyfold.WeakFibredProduct.isScSmoothComp, Polyfold.WeakFibredProduct.exists_isProperMap,
  Polyfold.MPolyfold.IsLocalScDiffeo.of_comm,
  Polyfold.MPolyfold.isLocalScDiffeo_snd_fibredProduct,
  Polyfold.MPolyfold.isLocalScDiffeo_fst_fibredProduct,
  Polyfold.EpGroupoid.isScSmoothOn_comp_of, Polyfold.EpGroupoid.tendsto_comp]

end RoundTrip.V10_18
