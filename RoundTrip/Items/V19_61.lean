import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_61

set_option maxSynthPendingDepth 3

/-! Round trip for V19_61 (2021 Theorem 19.6.13, p. 900: the strong bundle
`p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')`).

`A` is the conjunction of the types of the ten listed theorems at universe `0`
(`bundleBar`, `Theorem_19_6_13_Statement` and `altHHomeo` are definitions, i.e. vocabulary):
`theorem_19_6_13_H` (`H` is a strong bundle isomorphism onto `bundleBar`), `_total` (total space
= the natural M-polyfold `M(Ψ̄, Ψ̄')`), `_s`, `_t`, `_u`, `_inv` (an isomorphism),
`_of_bundleTransitionData` (the whole `Statement` for every `F̄`, no metrizability),
`isScSmoothMap_projBar`, and `BasicStrongBundleConstruction.theorem_19_6_13` / `_book` (the
statement for the chosen representative `Bs.rep`; `_book` with the text's hypotheses).

* `main_A_to_B_noMul`: from `_of_bundleTransitionData`, `Kb := bundleBar` satisfies every clause
  of `B` except the multiplication: `A`'s local-isomorphism clauses for `s`, `t` omit "`U`, `U'`
  open", which follows from `IsStrongBundleIsoOn.isScDiffeoOn_base` (`IsScSmoothOn` contains
  `IsOpen`); `ι` from `IsStrongBundleIso.toMap`.
* The multiplication clause of `B` is not among this item's theorems (it is item V19_62,
  `theorem_19_6_13_m`, whose proof uses `theorem_19_6_13_H` etc.); `A_and_m_to_B` shows
  `A ∧ (type of theorem_19_6_13_m) → B`.  So `A → B` is not proved.
* `B → A` is not proved: `B` is existential (some structure `Kb`) and holds only under
  `HasClassUniformizers` and metrizability of `T`, for representatives of `Bs.𝓕`; `A` is about
  the specific structure `bundleBar` (with `H` an isomorphism, the total space the natural
  M-polyfold, `ι` an isomorphism) for every `F̄` with no hypothesis.

Harness: `bundleBar`'s statement reaches the banned `isScSmoothMap_projBar` through the proof
fields of `altHHomeo`; plain `#rt_check` therefore fails (recorded) and `#rt_check_soft` passes. -/

namespace RoundTrip.V19_61
open Polyfold GroupoidalCategory
open GroupoidalCategory.StrongBundleUniformizerConstruction

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_H.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_total.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_s.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_t.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_u.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_inv.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_of_bundleTransitionData.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.isScSmoothMap_projBar.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13_book.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_H.{0},
    @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_total.{0},
    @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_s.{0},
    @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_t.{0},
    @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_u.{0},
    @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_inv.{0},
    @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_of_bundleTransitionData.{0},
    @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.isScSmoothMap_projBar.{0},
    @Polyfold.GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13.{0},
    @Polyfold.GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13_book.{0}⟩

/-- `A`'s main conjunct (the statement for every bundle transition data) gives `B` without the
multiplication clause. -/
theorem main_A_to_B_noMul :
    type_of% @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_of_bundleTransitionData.{0} →
    ∀ (C : GroupoidalCategory.{0}) (μ : C.BanFunctor) (Bs : C.BasicStrongBundleConstruction μ)
    (Fbar : Bs.U.BundleTransitionData),
      (∀ Ψ Ψ' : Bs.U.Unif,
        IsLocalSBIso (bundleBar Fbar Ψ Ψ') (Bs.U.strU Ψ).B
          (fun k : MS Fbar Ψ Ψ' => k.src) (fun h : MB Fbar Ψ Ψ' => h.src) ∧
        IsLocalSBIso (bundleBar Fbar Ψ Ψ') (Bs.U.strU Ψ').B
          (fun k : MS Fbar Ψ Ψ' => k.tgt) (fun h : MB Fbar Ψ Ψ' => h.tgt)) ∧
      (∀ Ψ : Bs.U.Unif,
        (Bs.U.strU Ψ).B.IsStrongBundleMap (bundleBar Fbar Ψ Ψ)
          (fun o => (GroupoidStr.TransitionSet.unit o : MS Fbar Ψ Ψ))
          (fun a => (GroupoidStr.TransitionSet.unit a : MB Fbar Ψ Ψ))) ∧
      (∀ Ψ Ψ' : Bs.U.Unif,
        (bundleBar Fbar Ψ Ψ').IsStrongBundleMap (bundleBar Fbar Ψ' Ψ)
          (fun k : MS Fbar Ψ Ψ' => (GroupoidStr.TransitionSet.inv k : MS Fbar Ψ' Ψ))
          (fun h : MB Fbar Ψ Ψ' => (GroupoidStr.TransitionSet.inv h : MB Fbar Ψ' Ψ))) := by
  intro hA C μ Bs Fbar
  refine ⟨fun Ψ Ψ' => ?_, fun Ψ => (hA Fbar Ψ Ψ).2.2.2.2.1,
    fun Ψ Ψ' => (hA Fbar Ψ Ψ').2.2.2.2.2.toMap⟩
  obtain ⟨-, -, ⟨hs, hsl⟩, ⟨ht, htl⟩, -⟩ := hA Fbar Ψ Ψ'
  refine ⟨⟨hs, fun x => ?_⟩, ⟨ht, fun x => ?_⟩⟩
  · obtain ⟨U, U', hx, hi⟩ := hsl x
    obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
    exact ⟨U, U', hg.isScSmoothOn.isOpen, hx, hg.isScSmoothOn_inv.isOpen, hi⟩
  · obtain ⟨U, U', hx, hi⟩ := htl x
    obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
    exact ⟨U, U', hg.isScSmoothOn.isOpen, hx, hg.isScSmoothOn_inv.isOpen, hi⟩

/-- `A` together with the multiplication clause (the main conjunct of item V19_62,
`StrongBundleUniformizerConstruction.theorem_19_6_13_m`, taken as a hypothesis) gives `B`. -/
theorem A_and_m_to_B :
    A → type_of% @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_m.{0} →
      B := by
  intro hA hm' C μ Bs hB _hm Fbar _hF
  obtain ⟨hs, hu, hi⟩ := main_A_to_B_noMul hA.2.2.2.2.2.2.1 C μ Bs Fbar
  exact ⟨fun Ψ Ψ' => bundleBar Fbar Ψ Ψ', hs, hu, hi,
    fun Ψ Ψ' Ψ'' _hpr => hm' Fbar Ψ Ψ' Ψ''⟩

/--
error: rt_check FAIL: RoundTrip.V19_61.main_A_to_B_noMul uses [Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.isScSmoothMap_projBar]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V19_61.main_A_to_B_noMul [Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_H,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_total,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_s,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_t,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_u,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_inv,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_of_bundleTransitionData,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.isScSmoothMap_projBar,
  Polyfold.GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13,
  Polyfold.GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13_book]
#rt_check_soft RoundTrip.V19_61.main_A_to_B_noMul [Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_H,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_total,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_s,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_t,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_u,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_inv,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_of_bundleTransitionData,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.isScSmoothMap_projBar,
  Polyfold.GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13,
  Polyfold.GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13_book]
#rt_check_soft RoundTrip.V19_61.A_and_m_to_B [Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_H,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_total,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_s,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_t,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_u,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_inv,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_of_bundleTransitionData,
  Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.isScSmoothMap_projBar,
  Polyfold.GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13,
  Polyfold.GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13_book]

end RoundTrip.V19_61
