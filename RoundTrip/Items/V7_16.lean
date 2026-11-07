import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_16

/-! Round trip for V7_16 (p. 230, after Proposition 7.4: isomorphic objects have isomorphic
isotropy groups; the identification `g ↦ φ ∘ g ∘ φ⁻¹` depends on `φ`).

`A` is the conjunction of the types of the listed theorems, universes at `0`:
`GroupoidStr.isotropyConj_val`, `EpGroupoid.conjIsotropy_val`,
`EpGroupoid.nonempty_isotropy_mulEquiv`, `EpGroupoid.nat_card_isotropy_eq`,
`EpGroupoid.isotropyConj_eq_isotropyConj_conj` (`GroupoidStr.isotropyConj`,
`EpGroupoid.conjIsotropy` are definitions: vocabulary).

* `A → B`: by `A`'s `isotropyConj_val`, `B`'s `conj X φ g = φ ∘ (g ∘ φ⁻¹)` is the underlying
  morphism of the project's `MulEquiv` `isotropyConj φ : G_x ≃* G_y` (which is
  `(φ ∘ g) ∘ φ⁻¹`; associativity), so it is a multiplicative bijection `Gset x → Gset y`.  The
  product conventions agree (`(g * h).val = g ∘ h = X.comp g h` on both sides).
* `B → A`: `nonempty_isotropy_mulEquiv` (and so `nat_card_isotropy_eq`) from `B` (1), by
  repackaging a multiplicative bijection `Gset x → Gset y` as a `MulEquiv` of the project's
  `Isotropy` groups.  The other three conjuncts are facts about the project's definition
  `isotropyConj` (two `rfl`s and the inner-automorphism relation between the choices `φ, φ'`),
  which `B` does not mention; they are re-proved outright.  The relation of
  `isotropyConj_eq_isotropyConj_conj` ("the identification depends on `φ` only up to an inner
  automorphism of `G_x`") has no counterpart in `B`, which reads "no canonical identification"
  as a remark (`B`'s separate `Remark`, not part of `B`). -/

namespace RoundTrip.V7_16
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GroupoidStr.isotropyConj_val.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.conjIsotropy_val.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.nonempty_isotropy_mulEquiv.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.nat_card_isotropy_eq.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isotropyConj_eq_isotropyConj_conj.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidStr.isotropyConj_val.{0}, @Polyfold.EpGroupoid.conjIsotropy_val.{0},
    @Polyfold.EpGroupoid.nonempty_isotropy_mulEquiv.{0},
    @Polyfold.EpGroupoid.nat_card_isotropy_eq.{0},
    @Polyfold.EpGroupoid.isotropyConj_eq_isotropyConj_conj.{0}⟩

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `B`'s conjugation is the project's `isotropyConj`, given `isotropyConj_val`. -/
theorem conj_eq (hval : type_of% @Polyfold.GroupoidStr.isotropyConj_val.{0})
    (X : EpGroupoid Obj Mor) {x y : Obj} {φ : Mor} (hx : X.src φ = x) (hy : X.tgt φ = y)
    (g : X.Isotropy x) : conj X φ g.val = (X.isotropyConj φ hx hy g).val := by
  rw [hval X.toGroupoidStr φ hx hy g, conj,
    X.comp_assoc _ _ _ (hx.trans g.tgt_val.symm) (by rw [X.tgt_inv, hx, g.src_val])]

theorem isGroupIsoOn_conj (hval : type_of% @Polyfold.GroupoidStr.isotropyConj_val.{0})
    (X : EpGroupoid Obj Mor) {x y : Obj} {φ : Mor} (hx : X.src φ = x) (hy : X.tgt φ = y) :
    IsGroupIsoOn X x y (conj X φ) := by
  set e := X.isotropyConj φ hx hy
  have key : ∀ g (hg : g ∈ Gset X x), conj X φ g = (e ⟨g, hg.1, hg.2⟩).val := fun g hg =>
    conj_eq hval X hx hy ⟨g, hg.1, hg.2⟩
  refine ⟨⟨fun g hg => ?_, fun g hg h hh he => ?_, fun k hk => ?_⟩, fun g hg h hh => ?_⟩
  · rw [key g hg]
    exact ⟨(e _).src_val, (e _).tgt_val⟩
  · rw [key g hg, key h hh] at he
    have := e.injective (GroupoidStr.Isotropy.ext he)
    exact congrArg GroupoidStr.Isotropy.val this
  · refine ⟨(e.symm ⟨k, hk.1, hk.2⟩).val, ⟨(e.symm _).src_val, (e.symm _).tgt_val⟩, ?_⟩
    rw [key _ ⟨(e.symm _).src_val, (e.symm _).tgt_val⟩]
    change (e (e.symm ⟨k, hk.1, hk.2⟩)).val = k
    rw [e.apply_symm_apply]
  · have hgh : X.comp g h ∈ Gset X x :=
      ⟨(X.src_comp _ _ (hg.1.trans hh.2.symm)).trans hh.1,
        (X.tgt_comp _ _ (hg.1.trans hh.2.symm)).trans hg.2⟩
    rw [key _ hgh, key g hg, key h hh]
    have : (⟨X.comp g h, hgh.1, hgh.2⟩ : X.Isotropy x) =
        (⟨g, hg.1, hg.2⟩ : X.Isotropy x) * ⟨h, hh.1, hh.2⟩ := GroupoidStr.Isotropy.ext rfl
    rw [this, map_mul]
    rfl

end

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  refine ⟨fun x y ⟨φ, hx, hy⟩ => ⟨conj X φ, isGroupIsoOn_conj hA.1 X hx hy⟩,
    fun x y φ hx hy => isGroupIsoOn_conj hA.1 X hx hy⟩

/-! ### `B → A` -/

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- A multiplicative bijection `Gset x → Gset y` is a `MulEquiv` of the project's groups. -/
theorem nonempty_mulEquiv_of_isGroupIsoOn (X : EpGroupoid Obj Mor) {x y : Obj} {e : Mor → Mor}
    (he : IsGroupIsoOn X x y e) : Nonempty (X.Isotropy x ≃* X.Isotropy y) := by
  obtain ⟨hb, hm⟩ := he
  let f : X.Isotropy x →ₙ* X.Isotropy y :=
    { toFun := fun g => ⟨e g.val, (hb.mapsTo ⟨g.src_val, g.tgt_val⟩).1,
        (hb.mapsTo ⟨g.src_val, g.tgt_val⟩).2⟩
      map_mul' := fun g h => GroupoidStr.Isotropy.ext
        (hm g.val ⟨g.src_val, g.tgt_val⟩ h.val ⟨h.src_val, h.tgt_val⟩) }
  refine ⟨MulEquiv.ofBijective f ⟨fun g h hgh => ?_, fun k => ?_⟩⟩
  · have := congrArg GroupoidStr.Isotropy.val hgh
    exact GroupoidStr.Isotropy.ext
      (hb.injOn ⟨g.src_val, g.tgt_val⟩ ⟨h.src_val, h.tgt_val⟩ this)
  · obtain ⟨g, hg, hgk⟩ := hb.surjOn ⟨k.src_val, k.tgt_val⟩
    exact ⟨⟨g, hg.1, hg.2⟩, GroupoidStr.Isotropy.ext hgk⟩

end

open CategoryTheory in
/-- `isotropyConj_eq_isotropyConj_conj`, re-proved outright (as in the project). -/
theorem isotropyConj_conj' {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) {x y : Obj} {φ φ' : Mor} (hx : X.src φ = x)
    (hy : X.tgt φ = y) (hx' : X.src φ' = x) (hy' : X.tgt φ' = y) :
    ∃ h : X.Isotropy x, h.val = X.comp (X.inv φ) φ' ∧
      ∀ g, X.isotropyConj φ' hx' hy' g = X.isotropyConj φ hx hy (h * g * h⁻¹) := by
  let f := X.homMk φ hx hy
  let f' := X.homMk φ' hx' hy'
  let k : X.toOb x ⟶ X.toOb x := f' ≫ Groupoid.inv f
  refine ⟨⟨k.1, k.2.1, k.2.2⟩, rfl, fun g => GroupoidStr.Isotropy.ext ?_⟩
  let γ := X.homMk g.val g.src_val g.tgt_val
  change (Groupoid.inv f' ≫ γ ≫ f').1 =
    (Groupoid.inv f ≫ (Groupoid.inv k ≫ γ ≫ k) ≫ f).1
  congr 1
  simp [k, Groupoid.inv_eq_inv]

theorem B_to_A : B → A := by
  intro hB
  have hne : type_of% @Polyfold.EpGroupoid.nonempty_isotropy_mulEquiv.{0} := by
    intro Obj Mor _ _ _ _ _ _ X x y hxy
    obtain ⟨e, he⟩ := (hB Obj Mor X).1 x y hxy
    exact nonempty_mulEquiv_of_isGroupIsoOn X he
  refine ⟨by intros; rfl, by intros; rfl, hne, ?_, @isotropyConj_conj'⟩
  intro Obj Mor _ _ _ _ _ _ X x y hxy
  obtain ⟨e⟩ := hne X hxy
  exact Nat.card_congr e.toEquiv

#rt_check RoundTrip.V7_16.A_to_B [Polyfold.GroupoidStr.isotropyConj_val,
  Polyfold.EpGroupoid.conjIsotropy_val, Polyfold.EpGroupoid.nonempty_isotropy_mulEquiv,
  Polyfold.EpGroupoid.nat_card_isotropy_eq, Polyfold.EpGroupoid.isotropyConj_eq_isotropyConj_conj]
#rt_check RoundTrip.V7_16.B_to_A [Polyfold.GroupoidStr.isotropyConj_val,
  Polyfold.EpGroupoid.conjIsotropy_val, Polyfold.EpGroupoid.nonempty_isotropy_mulEquiv,
  Polyfold.EpGroupoid.nat_card_isotropy_eq, Polyfold.EpGroupoid.isotropyConj_eq_isotropyConj_conj]
#rt_overlap RoundTrip.V7_16.B_to_A [Polyfold.GroupoidStr.isotropyConj_val,
  Polyfold.EpGroupoid.conjIsotropy_val, Polyfold.EpGroupoid.nonempty_isotropy_mulEquiv,
  Polyfold.EpGroupoid.nat_card_isotropy_eq, Polyfold.EpGroupoid.isotropyConj_eq_isotropyConj_conj]

end RoundTrip.V7_16
