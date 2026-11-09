import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_39

/-! Round trip for V8_39 (Lemma 8.6.1 / 2017: Lemma 8.9: `#G_x · #Θ_j = #mor(Θ_j)`,
`= #G_{y₀} · (#Θ_j)²`, `#G_x = #G_{y₀} · #Θ_j`).

The item lists the definition `IsProperCovering.morOnClassEquiv` (vocabulary, the bijection (8.17))
and two theorems.  `A` is the conjunction of the types of `morOn_fiberClass_eq` and
`IsProperCovering.lemma_8_6_1`, universes at `0`.

The project indexes the classes by `c ∈ |Y|` (`fiberClass x c = F⁻¹(x) ∩ π⁻¹(c)`, empty for
`c ∉ π(F⁻¹(x))`); B indexes them by a point `y₀ ∈ F⁻¹(x)` (`classB … y₀`).  The bridge:
`classB … y₀ = fiberClass x (π y₀)` (`classB_eq`), and every nonempty `fiberClass x c` is
`classB … y₀` for each of its points.

* `A ⇒ B`: B's three counts are `lemma_8_6_1 x (π y₀)` after `morOn_fiberClass_eq` and
  `Nat.card G_x = #{g | s g = x = t g}`.  B's two claims from the proof are not in A's theorems
  (A has the bijection (8.17) only as the definition `morOnClassEquiv`) and are proved outright:
  the bijection (8.17) from the non-item `bijective_fibredMap`/`existsUnique_lift`, and
  `mor(y, y') ≅ mor(y₀, y₀)` by Mathlib's `Iso.homCongr` in the groupoid bridge.
* `B ⇒ A`: `lemma_8_6_1 x c` from B at a point `y₀` of `fiberClass x c` (B at the other points for
  the `∀ y₀` part); for empty `fiberClass x c` both sides are `0`.  `morOn_fiberClass_eq` is a set
  identity, re-proved outright.
-/

namespace RoundTrip.V8_39
open Polyfold Set Function CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.morOn_fiberClass_eq.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.lemma_8_6_1.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.morOn_fiberClass_eq.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.lemma_8_6_1.{0, 0}⟩

/-- `#G_x` computed on the group or on the set of morphisms `x → x`. -/
theorem nat_card_isotropy_eq_ncard {Obj Mor : Type} (G : GroupoidStr Obj Mor) (x : Obj) :
    Nat.card (G.Isotropy x) = (isoSetB G x).ncard := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    { toFun := fun g => ⟨g.val, g.src_val, g.tgt_val⟩
      invFun := fun g => ⟨g.1, g.2.1, g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

section
variable {ObjY MorY ObjX MorX : Type}
  [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}

/-- B's class of `y₀` is the project's class `fiberClass x (π y₀)`. -/
theorem classB_eq (F : EpFunctor Y X) (x : ObjX) (y₀ : ObjY) :
    classB Y.toGroupoidStr (F.obj ⁻¹' {x}) y₀ = F.fiberClass x (Y.π y₀) := by
  ext y
  exact ⟨fun h => ⟨h.1, (Y.π_eq_π_iff.2 h.2).symm⟩, fun h => ⟨h.1, Y.π_eq_π_iff.1 h.2.symm⟩⟩

/-- A point `y₀` of `fiberClass x c` has `c = π y₀`. -/
theorem fiberClass_eq_of_mem (F : EpFunctor Y X) {x : ObjX} {c : Y.OrbitSpace} {y₀ : ObjY}
    (h : y₀ ∈ F.fiberClass x c) : F.fiberClass x c = F.fiberClass x (Y.π y₀) := by
  rw [show Y.π y₀ = c from h.2]

/-- `mor(y, y') ≅ mor(y₀, y₀)` for `y, y'` isomorphic to `y₀` (Mathlib's `Iso.homCongr` in the
groupoid bridge). -/
theorem ncard_morB_eq {Obj Mor : Type} (G : GroupoidStr Obj Mor) {y₀ y y' : Obj}
    (h : G.Isomorphic y₀ y) (h' : G.Isomorphic y₀ y') :
    (morB G y y').ncard = (morB G y₀ y₀).ncard := by
  obtain ⟨α, hα, hα'⟩ := h
  obtain ⟨β, hβ, hβ'⟩ := h'
  let a : G.toOb y₀ ≅ G.toOb y := (Groupoid.isoEquivHom _ _).symm (G.homMk α hα hα')
  let b : G.toOb y₀ ≅ G.toOb y' := (Groupoid.isoEquivHom _ _).symm (G.homMk β hβ hβ')
  let e : (G.toOb y₀ ⟶ G.toOb y₀) ≃ (G.toOb y ⟶ G.toOb y') := Iso.homCongr a b
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact (Nat.card_congr (e : ↥(morB G y₀ y₀) ≃ ↥(morB G y y'))).symm

end

theorem A_to_B : A → B := by
  intro hA ObjY MorY ObjX MorX _ _ _ _ _ _ _ _ _ _ _ _ Y X F hF x y₀ hy₀
  obtain ⟨hM, h89⟩ := hA
  have hΘ := classB_eq F x y₀
  have h₀ : y₀ ∈ F.fiberClass x (Y.π y₀) := ⟨hy₀, rfl⟩
  have hMe : {ψ : MorY | ψ ∈ morOnB Y.toGroupoidStr (F.obj ⁻¹' {x}) ∧
      Y.src ψ ∈ classB Y.toGroupoidStr (F.obj ⁻¹' {x}) y₀ ∧
      Y.tgt ψ ∈ classB Y.toGroupoidStr (F.obj ⁻¹' {x}) y₀} =
      Y.morOn (F.fiberClass x (Y.π y₀)) := by
    rw [hΘ]
    exact hM x (Y.π y₀)
  obtain ⟨h1, h2⟩ := h89 hF x (Y.π y₀)
  obtain ⟨h2, h3⟩ := h2 y₀ h₀
  simp only []
  rw [hMe, hΘ, ← nat_card_isotropy_eq_ncard, ← nat_card_isotropy_eq_ncard]
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · -- (8.17) is a bijection (outright, from the non-item unique lifting)
    refine ⟨fun ψ hψ => ⟨⟨(F.src_mor ψ).trans hψ.1.1, (F.tgt_mor ψ).trans hψ.2.1⟩, hψ.1⟩,
      fun φ _ ψ _ h => hF.bijective_fibredMap.1 (Subtype.ext (Prod.ext (congrArg Prod.fst h)
        (congrArg Prod.snd h))), fun p hp => ?_⟩
    obtain ⟨⟨hgs, hgt⟩, hy⟩ := hp
    obtain ⟨ψ, ⟨hψm, hψs⟩, -⟩ := hF.existsUnique_lift (φ := p.1) (y := p.2)
      (hgs.trans hy.1.symm)
    have ht : F.obj (Y.tgt ψ) = x := by rw [← F.tgt_mor, hψm, hgt]
    have hs : Y.src ψ ∈ F.fiberClass x (Y.π y₀) := hψs ▸ hy
    exact ⟨ψ, ⟨hs, ht, (Y.π_src_eq_π_tgt ψ).symm.trans hs.2⟩, Prod.ext hψm hψs⟩
  · -- `mor(y, y')` nonempty with `#G_{y₀}` elements (outright)
    intro y hy y' hy'
    have hyy : Y.Isomorphic y₀ y := ((EpFunctor.mem_fiberClass_iff h₀).1 hy).2
    have hyy' : Y.Isomorphic y₀ y' := ((EpFunctor.mem_fiberClass_iff h₀).1 hy').2
    obtain ⟨φ, hφ, hφ'⟩ := hyy.symm.trans hyy'
    exact ⟨⟨φ, hφ, hφ'⟩, ncard_morB_eq Y.toGroupoidStr hyy hyy'⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · -- `morOn_fiberClass_eq` (outright, a set identity)
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F x c
    exact Set.ext fun _ => ⟨fun h => h.2, fun h => ⟨⟨h.1.1, h.2.1⟩, h⟩⟩
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x c
    -- B at a point `y₀` of the class, rewritten to the project's indexing
    have key : ∀ y₀ ∈ F.fiberClass x c,
        Nat.card (X.Isotropy x) * (F.fiberClass x c).ncard = (Y.morOn (F.fiberClass x c)).ncard ∧
        (Y.morOn (F.fiberClass x c)).ncard =
          Nat.card (Y.Isotropy y₀) * (F.fiberClass x c).ncard ^ 2 ∧
        Nat.card (X.Isotropy x) = Nat.card (Y.Isotropy y₀) * (F.fiberClass x c).ncard := by
      intro y₀ h₀
      have h := hB ObjY MorY ObjX MorX Y X F hF x y₀ h₀.1
      simp only [] at h
      have hΘ : classB Y.toGroupoidStr (F.obj ⁻¹' {x}) y₀ = F.fiberClass x c := by
        rw [classB_eq, ← fiberClass_eq_of_mem F h₀]
      have hMe : {ψ : MorY | ψ ∈ morOnB Y.toGroupoidStr (F.obj ⁻¹' {x}) ∧
          Y.src ψ ∈ classB Y.toGroupoidStr (F.obj ⁻¹' {x}) y₀ ∧
          Y.tgt ψ ∈ classB Y.toGroupoidStr (F.obj ⁻¹' {x}) y₀} =
          Y.morOn (F.fiberClass x c) := by
        rw [hΘ]
        exact Set.ext fun _ => ⟨fun h => h.2, fun h => ⟨⟨h.1.1, h.2.1⟩, h⟩⟩
      rw [hMe, hΘ, ← nat_card_isotropy_eq_ncard, ← nat_card_isotropy_eq_ncard] at h
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    by_cases hne : (F.fiberClass x c).Nonempty
    · obtain ⟨y₀, h₀⟩ := hne
      exact ⟨(key y₀ h₀).1, fun y₁ h₁ => (key y₁ h₁).2⟩
    · rw [not_nonempty_iff_eq_empty] at hne
      refine ⟨?_, fun y₀ h₀ => by rw [hne] at h₀; exact absurd h₀ (Set.notMem_empty _)⟩
      rw [hne]
      have : Y.morOn (∅ : Set ObjY) = ∅ := Set.eq_empty_of_forall_notMem fun ψ h => h.1
      rw [this]
      simp

#rt_check RoundTrip.V8_39.A_to_B [Polyfold.EpFunctor.morOn_fiberClass_eq,
  Polyfold.EpFunctor.IsProperCovering.lemma_8_6_1]
#rt_check RoundTrip.V8_39.B_to_A [Polyfold.EpFunctor.morOn_fiberClass_eq,
  Polyfold.EpFunctor.IsProperCovering.lemma_8_6_1]
#rt_overlap RoundTrip.V8_39.B_to_A [Polyfold.EpFunctor.morOn_fiberClass_eq,
  Polyfold.EpFunctor.IsProperCovering.lemma_8_6_1]

end RoundTrip.V8_39
