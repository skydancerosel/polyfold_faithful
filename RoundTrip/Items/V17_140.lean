import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_140

set_option maxSynthPendingDepth 3

/-! Round trip for V17_140 (2021 Proposition 17.8.15, pp. 837–838: for a proper polyfold covering
functor the bijection (17.103) `M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E` is an sc-diffeomorphism).

The item lists four theorems; `A` is the conjunction of their types at universe `0` (`B` lives on
`GCT.{0}`): **`proposition_17_8_15`** (the main conjunct: for a proper covering functor `P` with
a proper polyfold covering structure `S`, there is `g` with
`IsScDiffeoOn (MH U U') (fibred-product sub-M-polyfold) Φ g univ univ`), and the general lemmas
`MPolyfold.isLocalScDiffeo_fstOfFibredProduct` (`π₁` of a fibred product is a local
sc-diffeomorphism), `EpFunctor.isLocalScDiffeo_fibredMap` (`L_F` is a local sc-diffeomorphism),
`EpFunctor.isScDiffeo_fibredMap_iff_bijective`.

`B` writes the sc-diffeomorphism out: `p`, `s` sc-smooth, `Φ` bijective, every left inverse `g`
of `Φ` sc-smooth on the fibred product (`IsScSmoothOnFibredProduct`, i.e. the sub-M-polyfold built
from `isSubMPolyfold_fibredProduct` (`s` a local sc-diffeomorphism) instead of
`isSubMPolyfold_fibredProduct'` (`τ̂` one); `IsSubMPolyfold` is a `Prop`, so the two sub-M-polyfold
structures are the same term by proof irrelevance).

* `main_A_to_B`: bijectivity from `left_inv`/`right_inv`; a left inverse of a bijection is the
  inverse `g` of `A`, sc-smooth by `isScSmoothOn_inv`; `p`, `s` sc-smooth from the structure fields
  `isLocalScDiffeo_p`, `isLocalScDiffeo_src` (facts of the setting, not of `A`); `hs`, `hτ` from
  `isLocalScDiffeo_trSrc`, `model.isLocalScDiffeo`.
* `main_B_to_A`: `g := (Equiv.ofBijective Φ).symm`; `Φ` sc-smooth into the sub-M-polyfold from
  `p`, `s` (`isScSmoothOn_subPolyfold_of_val`, `prodMk`); `g` sc-smooth from `B`.
* The three general lemmas do not follow from `B` (`B` is about the transition sets of a proper
  polyfold covering functor); they are re-proved outright, by the project's proofs, from
  `isScDiffeoOn_fst_fibredProduct`, `isLocalScDiffeo_of_comp_eq`,
  `isLocalScDiffeo_sndOfFibredProduct`, `continuous_fibredMap`, `isScDiffeoOn_of_bijective`. -/

namespace RoundTrip.V17_140
open Polyfold Set Function
open Polyfold.ProperCoveringUniformizer Polyfold.ProperCoveringUniformizerConstruction

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.ProperPolyfoldCoveringStructure.proposition_17_8_15.{0}) ∧
  (type_of% @Polyfold.MPolyfold.isLocalScDiffeo_fstOfFibredProduct.{0, 0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.isLocalScDiffeo_fibredMap.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.isScDiffeo_fibredMap_iff_bijective.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.ProperPolyfoldCoveringStructure.proposition_17_8_15.{0},
    @Polyfold.MPolyfold.isLocalScDiffeo_fstOfFibredProduct.{0, 0, 0},
    @Polyfold.EpFunctor.isLocalScDiffeo_fibredMap.{0, 0},
    @Polyfold.EpFunctor.isScDiffeo_fibredMap_iff_bijective.{0, 0}⟩

/-! ### The main conjunct -/

theorem main_A_to_B
    (h : type_of% @Polyfold.ProperPolyfoldCoveringStructure.proposition_17_8_15.{0}) : B := by
  intro A B Pc U U'
  let := MPolyfold.paracompactSpace_prod
    (Pc.S.SB.transPolyfold (Pc.S.toC.baseUnif Pc.S.SB Pc.S.SB_F U)
      (Pc.S.toC.baseUnif Pc.S.SB Pc.S.SB_F U')) U.unif.E.PObj
  let := ((Pc.S.SB.transPolyfold (Pc.S.toC.baseUnif Pc.S.SB Pc.S.SB_F U)
    (Pc.S.toC.baseUnif Pc.S.SB Pc.S.SB_F U')).prod U.unif.E.PObj).paracompactSpace_subtype
    (MPolyfold.fibredProduct (fun a : Pc.S.BaseTr U U' => a.src) U.unif.τ.obj)
  obtain ⟨g, hg⟩ := h Pc.S Pc.isProperCovering U U'
  have hbij : Bijective (U.unif.fibredTransMap U'.unif) :=
    ⟨fun a b hab => by
      rw [← hg.left_inv a (mem_univ a), ← hg.left_inv b (mem_univ b)]
      exact congrArg g (Subtype.ext (congrArg Subtype.val hab)),
     fun q => ⟨g q, hg.right_inv q (mem_univ q)⟩⟩
  refine ⟨(Pc.S.isLocalScDiffeo_p U U').isScSmoothMap,
    (Pc.S.isLocalScDiffeo_src U U').isScSmoothMap, hbij,
    Pc.S.SB.isLocalScDiffeo_trSrc _ _, U.unif.model.isLocalScDiffeo.isScSmoothMap,
    fun g' hg' => ?_⟩
  have heq : g' = g := funext fun q => by
    obtain ⟨a, rfl⟩ := hbij.2 q
    rw [hg' a]
    exact (hg.left_inv a (mem_univ a)).symm
  subst heq
  exact hg.isScSmoothOn_inv

theorem main_B_to_A (hB : B) :
    type_of% @Polyfold.ProperPolyfoldCoveringStructure.proposition_17_8_15.{0} := by
  intro A B P S hPc U U'
  obtain ⟨hp, hs, hbij, hs', hτ, hg⟩ := hB A B ⟨P, hPc, S⟩ U U'
  let := MPolyfold.paracompactSpace_prod
    (S.SB.transPolyfold (S.toC.baseUnif S.SB S.SB_F U)
      (S.toC.baseUnif S.SB S.SB_F U')) U.unif.E.PObj
  let := ((S.SB.transPolyfold (S.toC.baseUnif S.SB S.SB_F U)
    (S.toC.baseUnif S.SB S.SB_F U')).prod U.unif.E.PObj).paracompactSpace_subtype
    (MPolyfold.fibredProduct (fun a : S.BaseTr U U' => a.src) U.unif.τ.obj)
  let e := Equiv.ofBijective _ hbij
  refine ⟨e.symm, ?_, hg e.symm (fun a => e.symm_apply_apply a), mapsTo_univ _ _,
    mapsTo_univ _ _, fun a _ => e.symm_apply_apply a, fun q _ => e.apply_symm_apply q⟩
  exact MPolyfold.isScSmoothOn_subPolyfold_of_val _ (MPolyfold.IsScSmoothOn.prodMk hp hs)

/-! ### The general lemmas, re-proved -/

theorem fst' : type_of% @Polyfold.MPolyfold.isLocalScDiffeo_fstOfFibredProduct.{0, 0, 0} := by
  intro X _ _ _ P Y _ _ _ Q Z _ _ _ S _ f g _ hf hg a
  obtain ⟨W, V, k, haW, hd⟩ := hg a.1.2
  refine ⟨_, _, _, ?_, MPolyfold.isScDiffeoOn_fst_fibredProduct
    (MPolyfold.isSubMPolyfold_fibredProduct' hf hg) hd hf a⟩
  refine ⟨?_, haW⟩
  change f a.1.1 ∈ V
  rw [show f a.1.1 = g a.1.2 from a.2]
  exact hd.mapsTo haW

theorem fibredMap' : type_of% @Polyfold.EpFunctor.isLocalScDiffeo_fibredMap.{0, 0} := by
  intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
  exact MPolyfold.isLocalScDiffeo_of_comp_eq Y.isLocalScDiffeo_src
    (MPolyfold.isLocalScDiffeo_sndOfFibredProduct X.isLocalScDiffeo_src F.isScSmoothMap_obj)
    F.continuous_fibredMap fun _ => rfl

theorem iff' : type_of% @Polyfold.EpFunctor.isScDiffeo_fibredMap_iff_bijective.{0, 0} := by
  intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨fun a b hab => by
        rw [← hg.left_inv a (mem_univ a), ← hg.left_inv b (mem_univ b), hab],
      fun q => ⟨g q, hg.right_inv q (mem_univ q)⟩⟩
  · intro h
    exact ⟨_, (fibredMap' F).isScDiffeoOn_of_bijective (Equiv.ofBijective _ h) fun _ => rfl⟩

theorem A_to_B : A → B := fun h => main_A_to_B h.1

theorem B_to_A : B → A := fun hB => ⟨main_B_to_A hB, fst', fibredMap', iff'⟩

#rt_check RoundTrip.V17_140.main_A_to_B
  [Polyfold.ProperPolyfoldCoveringStructure.proposition_17_8_15,
   Polyfold.MPolyfold.isLocalScDiffeo_fstOfFibredProduct,
   Polyfold.EpFunctor.isLocalScDiffeo_fibredMap,
   Polyfold.EpFunctor.isScDiffeo_fibredMap_iff_bijective]
#rt_check RoundTrip.V17_140.main_B_to_A
  [Polyfold.ProperPolyfoldCoveringStructure.proposition_17_8_15,
   Polyfold.MPolyfold.isLocalScDiffeo_fstOfFibredProduct,
   Polyfold.EpFunctor.isLocalScDiffeo_fibredMap,
   Polyfold.EpFunctor.isScDiffeo_fibredMap_iff_bijective]
#rt_check RoundTrip.V17_140.A_to_B
  [Polyfold.ProperPolyfoldCoveringStructure.proposition_17_8_15,
   Polyfold.MPolyfold.isLocalScDiffeo_fstOfFibredProduct,
   Polyfold.EpFunctor.isLocalScDiffeo_fibredMap,
   Polyfold.EpFunctor.isScDiffeo_fibredMap_iff_bijective]
#rt_check RoundTrip.V17_140.B_to_A
  [Polyfold.ProperPolyfoldCoveringStructure.proposition_17_8_15,
   Polyfold.MPolyfold.isLocalScDiffeo_fstOfFibredProduct,
   Polyfold.EpFunctor.isLocalScDiffeo_fibredMap,
   Polyfold.EpFunctor.isScDiffeo_fibredMap_iff_bijective]
#rt_overlap RoundTrip.V17_140.B_to_A
  [Polyfold.ProperPolyfoldCoveringStructure.proposition_17_8_15,
   Polyfold.MPolyfold.isLocalScDiffeo_fstOfFibredProduct,
   Polyfold.EpFunctor.isLocalScDiffeo_fibredMap,
   Polyfold.EpFunctor.isScDiffeo_fibredMap_iff_bijective]

end RoundTrip.V17_140
