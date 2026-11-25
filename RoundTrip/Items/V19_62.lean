import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_62

set_option maxSynthPendingDepth 3

/-! Round trip for V19_62 (2021 Theorem 19.6.13, last clause, p. 900: the multiplication map is a
strong bundle map).

`A` is the conjunction of the types of `StrongBundleUniformizerConstruction.theorem_19_6_13_m`
(main conjunct: for every bundle transition data `F̄`, `m̄ = mBar` is a strong bundle map
`mulBundle → bundleBar` covering `mulBase`), `BasicStrongBundleConstruction.theorem_19_6_13_m`
(the same for `Bs.rep`) and `reflBan_theorem_19_6_13` (the whole Theorem 19.6.13 statement for
the reflection example), at universe `0`.  `mulBundle` and `mBar` are definitions (vocabulary);
`mulBundle = bundleBar.pullback (isScSmoothMap_pr₂BFP …)`, so by proof irrelevance it is `B`'s
`(Kb Ψ Ψ').pullback hpr` when `Kb = bundleBar`.

* `A_to_B`: `Kb := bundleBar F̄`.  The multiplication clause is `A`'s main conjunct.  `B` also
  asks that `s̄`, `t̄` be local strong bundle isomorphisms ("natural" structure); that is not in
  this item's theorems and comes from the non-item `theorem_19_6_13_of_bundleTransitionData`
  (item V19_61), with "`U`, `U'` open" from `IsStrongBundleIsoOn.isScDiffeoOn_base`.
* `B_to_A` is not proved: `B` is existential (some structure `Kb` with `s̄`, `t̄` locally
  isomorphisms) and holds only under `HasClassUniformizers` and metrizability of `T`, for
  representatives of `Bs.𝓕`; `A` is about the specific `bundleBar`/`mulBundle` for every `F̄`
  with no hypothesis, plus the reflection example. -/

namespace RoundTrip.V19_62
open Polyfold GroupoidalCategory
open GroupoidalCategory.StrongBundleUniformizerConstruction

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_m.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13_m.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.reflBan_theorem_19_6_13)

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_m.{0},
    @Polyfold.GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13_m.{0},
    @Polyfold.GroupoidalCategory.reflBan_theorem_19_6_13⟩

/-- The "natural" clause of `B` for `bundleBar` (from item V19_61's statement, not this item). -/
theorem natural_bundleBar {C : GroupoidalCategory.{0}} {μ : C.BanFunctor}
    (Bs : C.BasicStrongBundleConstruction μ) (Fbar : Bs.U.BundleTransitionData)
    (Ψ Ψ' : Bs.U.Unif) :
    IsLocalSBIso (bundleBar Fbar Ψ Ψ') (Bs.U.strU Ψ).B
        (fun k : MS Fbar Ψ Ψ' => k.src) (fun h : MB Fbar Ψ Ψ' => h.src) ∧
      IsLocalSBIso (bundleBar Fbar Ψ Ψ') (Bs.U.strU Ψ').B
        (fun k : MS Fbar Ψ Ψ' => k.tgt) (fun h : MB Fbar Ψ Ψ' => h.tgt) := by
  obtain ⟨-, -, ⟨hs, hsl⟩, ⟨ht, htl⟩, -⟩ := theorem_19_6_13_of_bundleTransitionData Fbar Ψ Ψ'
  refine ⟨⟨hs, fun x => ?_⟩, ⟨ht, fun x => ?_⟩⟩
  · obtain ⟨U, U', hx, hi⟩ := hsl x
    obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
    exact ⟨U, U', hg.isScSmoothOn.isOpen, hx, hg.isScSmoothOn_inv.isOpen, hi⟩
  · obtain ⟨U, U', hx, hi⟩ := htl x
    obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
    exact ⟨U, U', hg.isScSmoothOn.isOpen, hx, hg.isScSmoothOn_inv.isOpen, hi⟩

theorem main_A_to_B :
    type_of% @Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_m.{0} →
      B := by
  intro hm' C μ Bs hB _hm Fbar _hF
  exact ⟨fun Ψ Ψ' => bundleBar Fbar Ψ Ψ', fun Ψ Ψ' => natural_bundleBar Bs Fbar Ψ Ψ',
    fun Ψ Ψ' Ψ'' _hpr => hm' Fbar Ψ Ψ' Ψ''⟩

theorem A_to_B : A → B := fun h => main_A_to_B h.1

#rt_check RoundTrip.V19_62.main_A_to_B [Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_m,
  Polyfold.GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13_m,
  Polyfold.GroupoidalCategory.reflBan_theorem_19_6_13]
#rt_check RoundTrip.V19_62.A_to_B [Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_m,
  Polyfold.GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13_m,
  Polyfold.GroupoidalCategory.reflBan_theorem_19_6_13]

end RoundTrip.V19_62
