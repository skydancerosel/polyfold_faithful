import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_35

/-! Round trip for V7_35 (Lemma 7.3, pp. 239–240: effectiveness and injective natural
representations).

`A` is the conjunction of the types of `NaturalRep.injective_Φ_iff`, `NaturalRep.kerΦ_eq_bot_iff`,
`IsEffective.eq_one`, `isEffective_iff_forall_naturalRep` and `lemma_7_2_3`, universes at `0`
(`NaturalRep.kerΦ` is vocabulary).

Dictionary:
* `B`'s `IsEffectiveB` is the project's `IsEffective` (`g.val ≠ 1_x` vs `g ≠ 1`, `Isotropy.ext`).
* `B`'s `NatRepB X x` and the project's `NaturalRep x` have the same fields except that `B` asks
  `Φ(g)` to be an sc-diffeomorphism of `U` with *some* inverse, the project with inverse `Φ(g⁻¹)`.
  `toB` forgets; `ofB` rebuilds the project's field: `Φ(1) = id` on `U` (`Φ(1)` is injective and
  idempotent), so `Φ(g⁻¹)` is the inverse of `Φ(g)`.  Both keep `U`, `Φ`, `Γ`.
* `B`'s injectivity (`Φ g = Φ h` on `U` ⇒ `g = h`) and the project's (`Φ g = id` on `U` ⇒ `g = 1`)
  are equivalent (the second is `A`'s `injective_Φ_iff`; in `B → A` it is re-proved).

* `A → B`: `lemma_7_2_3` through the dictionary.
* `B → A`: `lemma_7_2_3` is `B` through the dictionary.  `IsEffective.eq_one` (for *every* natural
  representation, not only small ones) follows from `B` and the uniqueness of `Φ` on connected sets
  (`NaturalRep.Φ_eqOn`): `B` gives a natural representation `R'` with `R'.U ⊆ R.U` and `Φ'`
  injective; `Φ' g = Φ g = id` on `R'.U`, so `g = 1`.  `isEffective_iff_forall_naturalRep`
  follows from these two and `theorem_7_1_13`.  `injective_Φ_iff` and `kerΦ_eq_bot_iff` are facts
  about an arbitrary natural representation, re-proved outright from its fields.
-/

namespace RoundTrip.V7_35
open Polyfold Set Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.NaturalRep.injective_Φ_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.kerΦ_eq_bot_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.IsEffective.eq_one.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isEffective_iff_forall_naturalRep.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_7_2_3.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.NaturalRep.injective_Φ_iff.{0},
    @Polyfold.EpGroupoid.NaturalRep.kerΦ_eq_bot_iff.{0},
    @Polyfold.EpGroupoid.IsEffective.eq_one.{0},
    @Polyfold.EpGroupoid.isEffective_iff_forall_naturalRep.{0},
    @Polyfold.EpGroupoid.lemma_7_2_3.{0}⟩

section Dictionary
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor} {x : Obj}

theorem isEffectiveB_iff : IsEffectiveB X ↔ X.IsEffective := by
  refine ⟨fun h x g hg W hW hgW => h x g (fun he => hg (GroupoidStr.Isotropy.ext he)) W hW hgW,
    fun h x g hg W hW hgW => h x g (fun he => hg (by rw [he]; rfl)) W hW hgW⟩

/-- The project's natural representation as `B`'s. -/
def toB (R : X.NaturalRep x) : NatRepB X x where
  U := R.U
  isOpen_U := R.isOpen_U
  isConnected_U := R.isConnected_U
  mem_U := R.mem_U
  Φ := R.Φ
  Γ := R.Γ
  diffeo g := ⟨_, R.isScDiffeoOn_Φ g⟩
  hom := R.Φ_mul
  smooth := R.isScSmoothOn_Γ
  Γ_x := R.Γ_self
  src_Γ := R.src_Γ
  tgt_Γ := R.tgt_Γ
  unique := R.existsUnique_Γ

theorem NatRepB.Φ_one (R : NatRepB X x) : ∀ y ∈ R.U, R.Φ 1 y = y := by
  intro y hy
  obtain ⟨ψ, hψ⟩ := R.diffeo 1
  have h := R.hom 1 1 y hy
  rw [mul_one] at h
  have := congrArg ψ h
  rw [hψ.left_inv _ hy, hψ.left_inv _ (hψ.mapsTo hy)] at this
  exact this.symm

/-- `B`'s natural representation as the project's. -/
def ofB (R : NatRepB X x) : X.NaturalRep x where
  U := R.U
  isOpen_U := R.isOpen_U
  isConnected_U := R.isConnected_U
  mem_U := R.mem_U
  Φ := R.Φ
  Γ := R.Γ
  isScDiffeoOn_Φ g := by
    obtain ⟨ψ, hψ⟩ := R.diffeo g
    obtain ⟨ψ', hψ'⟩ := R.diffeo g⁻¹
    exact ⟨hψ.isScSmoothOn, hψ'.isScSmoothOn, hψ.mapsTo, hψ'.mapsTo,
      fun y hy => by rw [← R.hom _ _ y hy, inv_mul_cancel, R.Φ_one y hy],
      fun y hy => by rw [← R.hom _ _ y hy, mul_inv_cancel, R.Φ_one y hy]⟩
  Φ_mul := R.hom
  isScSmoothOn_Γ := R.smooth
  Γ_self := R.Γ_x
  src_Γ := R.src_Γ
  tgt_Γ := R.tgt_Γ
  existsUnique_Γ := R.unique

/-- `Φ g = id` on `U` only for `g = 1` gives injectivity of `g ↦ Φ g|_U`, for `B`'s data. -/
theorem injB_of_eq_one (R : NatRepB X x) (h : ∀ g, (∀ y ∈ R.U, R.Φ g y = y) → g = 1) :
    ∀ g h : X.Isotropy x, (∀ y ∈ R.U, R.Φ g y = R.Φ h y) → g = h := by
  intro g g' he
  refine inv_mul_eq_one.1 (h _ fun y hy => ?_)
  have hy' : R.Φ g⁻¹ (R.Φ g y) = y := by
    rw [← R.hom _ _ y hy, inv_mul_cancel, R.Φ_one y hy]
  rw [R.hom g⁻¹ g' y hy, ← he y hy, hy']

theorem eq_one_of_injB (R : NatRepB X x) (h : ∀ g h : X.Isotropy x,
    (∀ y ∈ R.U, R.Φ g y = R.Φ h y) → g = h) : ∀ g, (∀ y ∈ R.U, R.Φ g y = y) → g = 1 :=
  fun g hg => h g 1 fun y hy => by rw [hg y hy, R.Φ_one y hy]

end Dictionary

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  rw [isEffectiveB_iff, hA.2.2.2.2 X]
  refine ⟨fun h x V hV hx => ?_, fun h x V hV hx => ?_⟩
  · obtain ⟨R, hRV, hR⟩ := h x V hV hx
    exact ⟨toB R, hRV, injB_of_eq_one (toB R) hR⟩
  · obtain ⟨R, hRV, hR⟩ := h x V hV hx
    exact ⟨ofB R, hRV, eq_one_of_injB R hR⟩

section FromB
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `lemma_7_2_3` from `B`. -/
theorem lemma_7_3_of_B (hB : B) (X : EpGroupoid Obj Mor) : X.IsEffective ↔ ∀ x, ∀ V : Set Obj,
    IsOpen V → x ∈ V →
    ∃ R : X.NaturalRep x, R.U ⊆ V ∧ ∀ g, (∀ y ∈ R.U, R.Φ g y = y) → g = 1 := by
  rw [← isEffectiveB_iff, hB Obj Mor X]
  refine ⟨fun h x V hV hx => ?_, fun h x V hV hx => ?_⟩
  · obtain ⟨R, hRV, hR⟩ := h x V hV hx
    exact ⟨ofB R, hRV, eq_one_of_injB R hR⟩
  · obtain ⟨R, hRV, hR⟩ := h x V hV hx
    exact ⟨toB R, hRV, injB_of_eq_one (toB R) hR⟩

/-- `IsEffective.eq_one` from `B` and the uniqueness of `Φ` on connected sets. -/
theorem eq_one_of_B (hB : B) {X : EpGroupoid Obj Mor} (hX : X.IsEffective) {x : Obj}
    (R : X.NaturalRep x) {g : X.Isotropy x} (hg : ∀ y ∈ R.U, R.Φ g y = y) : g = 1 := by
  obtain ⟨R', hR'U, hR'⟩ := (lemma_7_3_of_B hB X).1 hX x R.U R.isOpen_U R.mem_U
  refine hR' g fun y hy => ?_
  have hC : R'.U ⊆ connectedComponentIn (R'.U ∩ R.U) x :=
    R'.isConnected_U.isPreconnected.subset_connectedComponentIn R'.mem_U
      (subset_inter subset_rfl hR'U)
  rw [R'.Φ_eqOn R g (hC hy)]
  exact hg y (hR'U hy)

end FromB

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- outright
    intro Obj Mor _ _ _ _ _ _ X x R
    refine ⟨fun h g hg => h (funext fun y => ?_), fun h g g' he => ?_⟩
    · change R.Φ g y = R.Φ 1 y
      rw [hg y y.2, R.Φ_one y y.2]
    · refine inv_mul_eq_one.1 (h _ fun y hy => ?_)
      have hy' : R.Φ g y = R.Φ g' y := congrFun he ⟨y, hy⟩
      rw [R.Φ_mul _ _ y hy, ← hy', R.Φ_inv_Φ g hy]
  · -- outright
    intro Obj Mor _ _ _ _ _ _ X x R
    simp only [Subgroup.eq_bot_iff_forall, R.mem_kerΦ]
  · intro Obj Mor _ _ _ _ _ _ X hX x R g hg
    exact eq_one_of_B hB hX R hg
  · intro Obj Mor _ _ _ _ _ _ X
    refine ⟨fun h _ R _ => eq_one_of_B hB h R, fun h => (lemma_7_3_of_B hB X).2 fun x _ hV hx =>
      (X.theorem_7_1_13 x hV hx).imp fun R hR => ⟨hR, h x R⟩⟩
  · intro Obj Mor _ _ _ _ _ _ X
    exact lemma_7_3_of_B hB X

#rt_check RoundTrip.V7_35.A_to_B [Polyfold.EpGroupoid.NaturalRep.injective_Φ_iff,
  Polyfold.EpGroupoid.NaturalRep.kerΦ_eq_bot_iff, Polyfold.EpGroupoid.IsEffective.eq_one,
  Polyfold.EpGroupoid.isEffective_iff_forall_naturalRep, Polyfold.EpGroupoid.lemma_7_2_3]
#rt_check RoundTrip.V7_35.B_to_A [Polyfold.EpGroupoid.NaturalRep.injective_Φ_iff,
  Polyfold.EpGroupoid.NaturalRep.kerΦ_eq_bot_iff, Polyfold.EpGroupoid.IsEffective.eq_one,
  Polyfold.EpGroupoid.isEffective_iff_forall_naturalRep, Polyfold.EpGroupoid.lemma_7_2_3]
#rt_overlap RoundTrip.V7_35.B_to_A [Polyfold.EpGroupoid.NaturalRep.injective_Φ_iff,
  Polyfold.EpGroupoid.NaturalRep.kerΦ_eq_bot_iff, Polyfold.EpGroupoid.IsEffective.eq_one,
  Polyfold.EpGroupoid.isEffective_iff_forall_naturalRep, Polyfold.EpGroupoid.lemma_7_2_3]

end RoundTrip.V7_35
