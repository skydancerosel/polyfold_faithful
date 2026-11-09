import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_38

/-! Round trip for V8_38 (§8.6.1 / 2017 §8.5.1, before Lemma 8.6.1: the morphisms over a fibre and
the isomorphism classes).

The item lists the definitions `fiberClass`, `fiberIndex`, `fiberClasses`,
`IsProperCovering.morOnFiberEquiv` (vocabulary) and seven theorems.  `A` is the conjunction of the
types of the theorems, universes at `0`: `iUnion_fiberClass`, `pairwiseDisjoint_fiberClass`,
`nat_card_isotropy_eq_of_mem_fiberClass`, `IsProperCovering.bijective_fibredMap`,
`IsProperCovering.existsUnique_lift`, `IsProperCovering.ncard_morOn_fiber`,
`IsProperCovering.finite_morOn_fiber`.

* `A ⇒ B`: the bijection `mor(F⁻¹(x)) → G_x × F⁻¹(x)` from `bijective_fibredMap` (injectivity)
  and `existsUnique_lift` (surjectivity); finiteness and the count from `finite_morOn_fiber`,
  `ncard_morOn_fiber` (with `Nat.card G_x = #{g | s g = x = t g}`); a decomposition
  `Fin q → Set` enumerating the project's classes `fiberClass x c`, `c ∈ fiberIndex x`, using
  `iUnion_fiberClass` and `pairwiseDisjoint_fiberClass`.  B's last conjunct (the isotropy groups
  of two points of one class are isomorphic *as groups*) is stronger than A's
  `nat_card_isotropy_eq_of_mem_fiberClass` (equal cardinalities); it is proved outright from the
  non-item `EpGroupoid.nonempty_isotropy_mulEquiv`.
* `B ⇒ A`: `ncard_morOn_fiber` and `finite_morOn_fiber` come from B; the other five are not
  consequences of B (B speaks only of morphisms between points of one fibre, `bijective_fibredMap`
  and `existsUnique_lift` of all morphisms; `iUnion_fiberClass`, `pairwiseDisjoint_fiberClass`,
  `nat_card_isotropy_eq_of_mem_fiberClass` are facts about the project's vocabulary that hold for
  every functor) and are re-proved outright, by the project's (short) arguments.
-/

namespace RoundTrip.V8_38
open Polyfold Set Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.iUnion_fiberClass.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.pairwiseDisjoint_fiberClass.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.nat_card_isotropy_eq_of_mem_fiberClass.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.bijective_fibredMap.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.existsUnique_lift.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.ncard_morOn_fiber.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.finite_morOn_fiber.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.iUnion_fiberClass.{0, 0},
    @Polyfold.EpFunctor.pairwiseDisjoint_fiberClass.{0, 0},
    @Polyfold.EpFunctor.nat_card_isotropy_eq_of_mem_fiberClass.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.bijective_fibredMap.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.existsUnique_lift.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.ncard_morOn_fiber.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.finite_morOn_fiber.{0, 0}⟩

/-- `#G_x` computed on the group or on the set of morphisms `x → x`. -/
theorem nat_card_isotropy_eq_ncard {Obj Mor : Type} (G : GroupoidStr Obj Mor) (x : Obj) :
    Nat.card (G.Isotropy x) = (isoSetB G x).ncard := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    { toFun := fun g => ⟨g.val, g.src_val, g.tgt_val⟩
      invFun := fun g => ⟨g.1, g.2.1, g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem A_to_B : A → B := by
  intro hA ObjY MorY ObjX MorX _ _ _ _ _ _ _ _ _ _ _ _ Y X F hF x
  obtain ⟨hU, hD, -, hbij, hlift, hcard, hfin⟩ := hA
  refine ⟨⟨fun φ hφ => ⟨⟨(F.src_mor φ).trans hφ.1, (F.tgt_mor φ).trans hφ.2⟩, hφ.1⟩,
    fun φ _ ψ _ h => (hbij hF).1 (Subtype.ext (Prod.ext (congrArg Prod.fst h)
      (congrArg Prod.snd h))), fun p hp => ?_⟩, hfin hF x, ?_, ?_, ?_⟩
  · obtain ⟨⟨hgs, hgt⟩, hy⟩ := hp
    obtain ⟨ψ, ⟨hψm, hψs⟩, -⟩ := hlift hF (φ := p.1) (y := p.2) (hgs.trans hy.symm)
    refine ⟨ψ, ⟨show F.obj (Y.src ψ) = x by rw [hψs]; exact hy, ?_⟩, Prod.ext hψm hψs⟩
    change F.obj (Y.tgt ψ) = x
    rw [← F.tgt_mor, hψm, hgt]
  · have h := hcard hF x
    rw [nat_card_isotropy_eq_ncard] at h
    exact h
  · -- the decomposition: enumerate the project's classes
    have hfi : (F.fiberIndex x).Finite := (hF.finite_fiber x).image _
    have := hfi.to_subtype
    let e := Finite.equivFin (F.fiberIndex x)
    refine ⟨Nat.card (F.fiberIndex x), fun j => F.fiberClass x (e.symm j), fun j =>
      EpFunctor.nonempty_fiberClass_iff.2 (e.symm j).2, fun j => EpFunctor.fiberClass_subset x _,
      ?_, fun i j hij => ?_, fun j y hy y' hy' => ?_⟩
    · ext y
      simp only [mem_iUnion]
      constructor
      · rintro ⟨j, hj⟩
        exact EpFunctor.fiberClass_subset x _ hj
      · intro hy
        rw [← hU x] at hy
        obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.1 hy
        exact ⟨e ⟨c, hc⟩, by rw [Equiv.symm_apply_apply]; exact hyc⟩
    · have hne : (e.symm i : Y.OrbitSpace) ≠ e.symm j := fun h => hij (e.symm.injective
        (Subtype.ext h))
      exact hD x (mem_univ _) (mem_univ _) hne
    · rw [EpFunctor.mem_fiberClass_iff hy]
      exact ⟨fun h => h.2, fun h => ⟨hy', h⟩⟩
  · -- isomorphic isotropy groups (stronger than A's equal cardinalities; outright)
    intro q Θ hΘ j y hy y' hy'
    have hiso : IsoB Y.toGroupoidStr y y' := ((hΘ.2.2.2.2 j y hy y' (hΘ.2.1 j hy')).1 hy')
    exact Y.nonempty_isotropy_mulEquiv hiso

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `iUnion_fiberClass` (outright)
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F x
    refine Subset.antisymm (iUnion₂_subset fun c _ => EpFunctor.fiberClass_subset x c)
      fun y hy => ?_
    exact mem_iUnion₂.2 ⟨Y.π y, ⟨y, hy, rfl⟩, ⟨hy, rfl⟩⟩
  · -- `pairwiseDisjoint_fiberClass` (outright)
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F x c _ c' _ hcc'
    refine disjoint_left.2 fun y hy hy' => hcc' ?_
    exact (show Y.π y = c from hy.2).symm.trans hy'.2
  · -- `nat_card_isotropy_eq_of_mem_fiberClass` (outright)
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F x c y y' hy hy'
    exact Y.nat_card_isotropy_eq ((EpFunctor.mem_fiberClass_iff hy).1 hy').2
  · -- `bijective_fibredMap` (outright, from Definition 8.8 (3))
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF
    let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
    let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
    obtain ⟨g, hg⟩ := hF.isScDiffeo_fibredMap
    refine ⟨fun a b hab => ?_, fun p => ⟨g p, hg.right_inv p (mem_univ _)⟩⟩
    rw [← hg.left_inv a (mem_univ _), hab, hg.left_inv b (mem_univ _)]
  · -- `existsUnique_lift` (outright, from Definition 8.8 (3))
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF φ y h
    let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
    let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
    obtain ⟨g, hg⟩ := hF.isScDiffeo_fibredMap
    have hb : Bijective F.fibredMap := ⟨fun a b hab => by
      rw [← hg.left_inv a (mem_univ _), hab, hg.left_inv b (mem_univ _)],
      fun p => ⟨g p, hg.right_inv p (mem_univ _)⟩⟩
    obtain ⟨ψ, hψ⟩ := hb.2 ⟨(φ, y), h⟩
    refine ⟨ψ, ⟨congrArg (fun p => p.1.1) hψ, congrArg (fun p => p.1.2) hψ⟩, fun ψ' hψ' => ?_⟩
    exact hb.1 ((Subtype.ext (Prod.ext hψ'.1 hψ'.2)).trans hψ.symm)
  · -- `ncard_morOn_fiber`, from B
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x
    rw [nat_card_isotropy_eq_ncard]
    exact (hB ObjY MorY ObjX MorX Y X F hF x).2.2.1
  · -- `finite_morOn_fiber`, from B
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x
    exact (hB ObjY MorY ObjX MorX Y X F hF x).2.1

#rt_check RoundTrip.V8_38.A_to_B [Polyfold.EpFunctor.iUnion_fiberClass,
  Polyfold.EpFunctor.pairwiseDisjoint_fiberClass,
  Polyfold.EpFunctor.nat_card_isotropy_eq_of_mem_fiberClass,
  Polyfold.EpFunctor.IsProperCovering.bijective_fibredMap,
  Polyfold.EpFunctor.IsProperCovering.existsUnique_lift,
  Polyfold.EpFunctor.IsProperCovering.ncard_morOn_fiber,
  Polyfold.EpFunctor.IsProperCovering.finite_morOn_fiber]
#rt_check RoundTrip.V8_38.B_to_A [Polyfold.EpFunctor.iUnion_fiberClass,
  Polyfold.EpFunctor.pairwiseDisjoint_fiberClass,
  Polyfold.EpFunctor.nat_card_isotropy_eq_of_mem_fiberClass,
  Polyfold.EpFunctor.IsProperCovering.bijective_fibredMap,
  Polyfold.EpFunctor.IsProperCovering.existsUnique_lift,
  Polyfold.EpFunctor.IsProperCovering.ncard_morOn_fiber,
  Polyfold.EpFunctor.IsProperCovering.finite_morOn_fiber]
#rt_overlap RoundTrip.V8_38.B_to_A [Polyfold.EpFunctor.iUnion_fiberClass,
  Polyfold.EpFunctor.pairwiseDisjoint_fiberClass,
  Polyfold.EpFunctor.nat_card_isotropy_eq_of_mem_fiberClass,
  Polyfold.EpFunctor.IsProperCovering.bijective_fibredMap,
  Polyfold.EpFunctor.IsProperCovering.existsUnique_lift,
  Polyfold.EpFunctor.IsProperCovering.ncard_morOn_fiber,
  Polyfold.EpFunctor.IsProperCovering.finite_morOn_fiber]

end RoundTrip.V8_38
