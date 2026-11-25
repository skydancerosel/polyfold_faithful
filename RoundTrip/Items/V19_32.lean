import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_32

set_option maxSynthPendingDepth 3

/-! Round trip for V19_32 (2021 Corollary 19.5.2, p. 887).  Universes at `0`.

* `A_to_B`: `B` quantifies over EVERY family `N` of natural structures.  In such a structure `s` is
  a local sc-diffeomorphism (`sN_local`: the `F_h` are its local inverses), so by the non-item
  uniqueness lemma `isScDiffeoOn_id_of_isLocalScDiffeo_src` the identity `N.M Ψ Ψ' → transPolyfold`
  is an sc-diffeomorphism (`idN`); with `isScDiffeoOn_of_equiv` (representative `F` vs `B.rep`)
  `u`, `ι` come from the main conjunct `corollary_19_5_2` through identity sc-diffeomorphisms; `s`, `t` from `sN_local`, `isLocalScDiffeo_tgt`; `m` on `N`'s own fibred product
  by the argument `s ∘ m = s ∘ pr₂` (`mN_smooth`), not through `A`'s `isScSmoothMap_mul` (that is
  stated on `transPolyfold`'s fibred product).
* No `B_to_A`: `corollary_19_5_2` and the `TransitionData` lemmas have no hypothesis on `T`
  (no `HasClassUniformizers`, no metrizability), `B` has both.  Under them, `B` gives the main
  conjunct (`B_to_main_under`, with the family `projN` of the project's structures). -/

namespace RoundTrip.V19_32
open Polyfold Polyfold.GroupoidalCategory Set
open Polyfold.GroupoidalCategory.UniformizerConstruction

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.corollary_19_5_2.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_unit.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_inv.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_mul.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.BasicConstruction.corollary_19_5_2.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_unit.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_inv.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_mul.{0}⟩

section
variable {C : GroupoidalCategory.{0}} {U : C.UniformizerConstruction} {F : U.TransitionData}

/-- In a natural structure, `s` is a local sc-diffeomorphism (its local inverses are the `F_h`). -/
theorem sN_local (N : NatStr F) (Ψ Ψ' : U.Unif) :
    (N.M Ψ Ψ').IsLocalScDiffeo (Ψ : C.Uniformizer).P (sN N Ψ Ψ') := by
  intro a
  obtain ⟨hW, g, d⟩ := N.natural Ψ Ψ' a
  refine ⟨germ F Ψ Ψ' a '' F.dom Ψ Ψ' a, F.dom Ψ Ψ' a, germ F Ψ Ψ' a,
    ⟨a.src, F.mem_dom Ψ Ψ' a, F.map_src Ψ Ψ' a⟩, ?_⟩
  have hsg : EqOn g (sN N Ψ Ψ') (germ F Ψ Ψ' a '' F.dom Ψ Ψ' a) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [d.left_inv q hq]
    exact (F.src_map Ψ Ψ' a q hq).symm
  refine ⟨d.isScSmoothOn_inv.congr hsg, d.isScSmoothOn, ?_, d.mapsTo, ?_, ?_⟩
  · intro y hy; rw [← hsg hy]; exact d.mapsTo_inv hy
  · intro y hy; rw [← hsg hy]; exact d.right_inv y hy
  · intro q hq; rw [← hsg (d.mapsTo hq)]; exact d.left_inv q hq

/-- A natural structure agrees with the project's `transPolyfold`. -/
theorem idN (N : NatStr F) (Ψ Ψ' : U.Unif) :
    (N.M Ψ Ψ').IsScDiffeoOn (F.transPolyfold Ψ Ψ') id id univ univ :=
  F.isScDiffeoOn_id_of_isLocalScDiffeo_src Ψ Ψ' (N.M Ψ Ψ') (sN_local N Ψ Ψ')

theorem tN_smooth (N : NatStr F) (Ψ Ψ' : U.Unif) :
    (N.M Ψ Ψ').IsScSmoothMap (Ψ' : C.Uniformizer).P (tN N Ψ Ψ') := by
  have := MPolyfold.IsScSmoothMap.comp (F.isLocalScDiffeo_tgt Ψ Ψ').isScSmoothMap
    (idN N Ψ Ψ').isScSmoothOn
  exact this

theorem mN_smooth (N : NatStr F) (Ψ Ψ' Ψ'' : U.Unif) :
    MPolyfold.IsScSmoothOnFibredProduct (N.M Ψ' Ψ'') (N.M Ψ Ψ') (N.M Ψ Ψ'')
      (sN_local N Ψ' Ψ'') (tN_smooth N Ψ Ψ') (mN N Ψ Ψ' Ψ'') := by
  set M₁ := N.M Ψ' Ψ''
  set M₂ := N.M Ψ Ψ'
  have := MPolyfold.paracompactSpace_prod M₁ M₂
  have := (M₁.prod M₂).paracompactSpace_subtype (MPolyfold.fibredProduct (sN N Ψ' Ψ'')
    (tN N Ψ Ψ'))
  have hA := MPolyfold.isSubMPolyfold_fibredProduct (sN_local N Ψ' Ψ'') (tN_smooth N Ψ Ψ')
  have hval := MPolyfold.subPolyfold_inclusion_isScSmooth hA
  change (MPolyfold.subPolyfold hA).IsScSmoothMap (N.M Ψ Ψ'') _
  refine MPolyfold.isScSmoothMap_of_isLocalScDiffeo_comp (sN_local N Ψ Ψ'')
    (F.continuous_mulMap (Ψ := Ψ) (Ψ' := Ψ') (Ψ'' := Ψ'')) ?_
  exact (sN_local N Ψ Ψ').isScSmoothMap.comp ((MPolyfold.isScSmoothMap_snd M₁ M₂).comp hval)

end

theorem main_A_to_B
    (hA : type_of% @Polyfold.GroupoidalCategory.BasicConstruction.corollary_19_5_2.{0}) : B := by
  intro C B F _ hF _ N
  have e : B.rep.Equiv F := Quotient.exact (B.mk_rep.trans hF.symm)
  -- `B.rep`'s structure → `F`'s structure → `N`'s structure, all identity maps
  have hto : ∀ Ψ Ψ' : B.U.Unif, (B.transPolyfold Ψ Ψ').IsScSmoothMap (N.M Ψ Ψ')
      (fun a : B.M Ψ Ψ' => (a : NTN N Ψ Ψ')) := fun Ψ Ψ' => by
    have h1 := (TransitionData.isScDiffeoOn_of_equiv e Ψ Ψ').isScSmoothOn
    have := MPolyfold.IsScSmoothMap.comp (idN N Ψ Ψ').symm.isScSmoothOn h1
    exact this
  have hfrom : ∀ Ψ Ψ' : B.U.Unif, (N.M Ψ Ψ').IsScSmoothMap (B.transPolyfold Ψ Ψ')
      (fun a : NTN N Ψ Ψ' => (a : B.M Ψ Ψ')) := fun Ψ Ψ' => by
    have h1 := (TransitionData.isScDiffeoOn_of_equiv e Ψ Ψ').isScSmoothOn_inv
    have := MPolyfold.IsScSmoothMap.comp h1 (idN N Ψ Ψ').isScSmoothOn
    exact this
  refine ⟨fun Ψ Ψ' => (sN_local N Ψ Ψ').isScSmoothMap, fun Ψ Ψ' => tN_smooth N Ψ Ψ', fun Ψ => ?_,
    fun Ψ Ψ' => ?_, sN_local N, fun Ψ Ψ' Ψ'' => ⟨tN_smooth N Ψ Ψ', mN_smooth N Ψ Ψ' Ψ''⟩⟩
  · have := MPolyfold.IsScSmoothMap.comp (hto Ψ Ψ) (hA B Ψ Ψ Ψ).1
    exact this
  · have h1 := MPolyfold.IsScSmoothMap.comp (hA B Ψ Ψ' Ψ').2.1 (hfrom Ψ Ψ')
    have := MPolyfold.IsScSmoothMap.comp (hto Ψ' Ψ) h1
    exact this

theorem A_to_B (hA : A) : B := main_A_to_B hA.1

/-- The family of the project's structures `transPolyfold` is natural in `B`'s sense. -/
def projN {C : GroupoidalCategory.{0}} {U : C.UniformizerConstruction} (F : U.TransitionData) :
    NatStr F where
  t2 _ _ := inferInstance
  pc _ _ := inferInstance
  P Ψ Ψ' := F.transPolyfold Ψ Ψ'
  natural Ψ Ψ' h := ⟨F.isOpen_image_map Ψ Ψ' h (F.isOpen_dom Ψ Ψ' h) subset_rfl, _,
    F.isScDiffeoOn_map Ψ Ψ' h⟩

/-- `B ⇒` the main conjunct, under `B`'s extra hypotheses (`HasClassUniformizers`, `T`
metrizable), which `corollary_19_5_2` does not have. -/
theorem B_to_main_under (hB' : B) {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    (hB : B.U.HasClassUniformizers) (hm : @TopologicalSpace.MetrizableSpace _ (natT B.U))
    (Ψ Ψ' Ψ'' : B.U.Unif) :
    type_of% (@Polyfold.GroupoidalCategory.BasicConstruction.corollary_19_5_2.{0} C B Ψ Ψ' Ψ'') := by
  obtain ⟨-, -, hu, hi, _hs, hmul⟩ := hB' C B B.rep hB B.mk_rep hm (projN B.rep)
  obtain ⟨_hts, hm'⟩ := hmul Ψ Ψ' Ψ''
  exact ⟨hu Ψ, hi Ψ Ψ', hm'⟩

#rt_check RoundTrip.V19_32.A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.corollary_19_5_2,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_unit,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_inv,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_mul]
#rt_check RoundTrip.V19_32.main_A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.corollary_19_5_2,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_unit,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_inv,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_mul]
#rt_check RoundTrip.V19_32.B_to_main_under [Polyfold.GroupoidalCategory.BasicConstruction.corollary_19_5_2,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_unit,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_inv,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_mul]
#rt_overlap RoundTrip.V19_32.A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.corollary_19_5_2,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_unit,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_inv,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_mul]
#rt_overlap RoundTrip.V19_32.B_to_main_under [Polyfold.GroupoidalCategory.BasicConstruction.corollary_19_5_2,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_unit,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_inv,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isScSmoothMap_mul]

end RoundTrip.V19_32
