import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_55

/-!
Round trip for V9_55 (Lemma 9.5.10, 2021 p. 444, and (9.23), p. 445): the effective orders.

`A` (universes at `0`) is the conjunction of the types of
`card_effIsotropy_mul_card_trivialSubgroup`, `NaturalRep.kerΦ_eq_trivialSubgroup`,
`NaturalRep.kerΦ_le_stabilizer`, `NaturalRep.stabilizerEquivIsotropy_mem_trivialSubgroup_iff`,
`NaturalRep.card_trivialSubgroup_eq` and `NaturalRep.card_quotient_stabilizer_mul_card_effIsotropy`.

* `A ⇒ B` (`A_to_B`): B's natural action on the connected `U` is a project `NaturalRep`
  (`toNaturalRep`, as in V7_66); global LUC gives LUC for it (`isLUC_iff_forall_naturalRep`, a
  non-item lemma).  Then B's `T_x = {g | ĝ = id on a nonempty open W ⊆ U}` is A's
  `kerΦ_eq_trivialSubgroup` plus the definition of LUC; `T_x ⊆ H` is `kerΦ_le_stabilizer`; the
  identification `T_y ↔ T_x` under `H ≅ G_y` is `stabilizerEquivIsotropy_mem_trivialSubgroup_iff`
  with `e = stabilizerEquivIsotropy`; (9.23) for every set `R` of coset representatives is
  `card_quotient_stabilizer_mul_card_effIsotropy` and `♯R = ♯(G_x/H)` (`card_reps`).
* `B ⇒ A` is not proved: `A` is more general.  Its LUC hypothesis is `R.HasLUC` for the one
  representation at hand, `B` assumes LUC of the whole ep-groupoid; `card_effIsotropy_mul_card_
  trivialSubgroup` and `kerΦ_le_stabilizer` hold without any LUC, and `card_trivialSubgroup_eq`
  is not a statement of `B`.
-/

namespace RoundTrip.V9_55
open Polyfold Set

/-- The project's statements, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.card_effIsotropy_mul_card_trivialSubgroup.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.kerΦ_eq_trivialSubgroup.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.kerΦ_le_stabilizer.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.stabilizerEquivIsotropy_mem_trivialSubgroup_iff.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.card_trivialSubgroup_eq.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.card_quotient_stabilizer_mul_card_effIsotropy.{0}

theorem A_holds : A :=
  ⟨@EpGroupoid.card_effIsotropy_mul_card_trivialSubgroup,
    @EpGroupoid.NaturalRep.kerΦ_eq_trivialSubgroup, @EpGroupoid.NaturalRep.kerΦ_le_stabilizer,
    @EpGroupoid.NaturalRep.stabilizerEquivIsotropy_mem_trivialSubgroup_iff,
    @EpGroupoid.NaturalRep.card_trivialSubgroup_eq,
    @EpGroupoid.NaturalRep.card_quotient_stabilizer_mul_card_effIsotropy⟩

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `Φ(1) = id` on `V` for B's natural action. -/
theorem Φ_one_of {X : EpGroupoid Obj Mor} {x : Obj} {V : Set Obj} {Φ : X.Isotropy x → Obj → Obj}
    {Γ : X.Isotropy x → Obj → Mor} (h : IsNatAction X x V Φ Γ) {y : Obj} (hy : y ∈ V) :
    Φ 1 y = y := by
  obtain ⟨ψ, hψ⟩ := h.diffeo 1
  have hz : ψ y ∈ V := hψ.mapsTo_inv hy
  have h1 : Φ 1 (ψ y) = y := hψ.right_inv y hy
  calc Φ 1 y = Φ 1 (Φ 1 (ψ y)) := by rw [h1]
    _ = Φ (1 * 1) (ψ y) := (h.hom 1 1 _ hz).symm
    _ = y := by rw [mul_one, h1]

/-- B's natural action on a **connected** `V` is a project `NaturalRep` (as in V7_66). -/
def toNaturalRep {X : EpGroupoid Obj Mor} {x : Obj} {V : Set Obj}
    {Φ : X.Isotropy x → Obj → Obj} {Γ : X.Isotropy x → Obj → Mor} (h : IsNatAction X x V Φ Γ)
    (hc : IsConnected V) : X.NaturalRep x where
  U := V
  isOpen_U := h.isOpen
  isConnected_U := hc
  mem_U := h.mem
  Φ := Φ
  Γ := Γ
  isScDiffeoOn_Φ g :=
    { isScSmoothOn := (h.diffeo g).choose_spec.isScSmoothOn
      isScSmoothOn_inv := (h.diffeo g⁻¹).choose_spec.isScSmoothOn
      mapsTo := (h.diffeo g).choose_spec.mapsTo
      mapsTo_inv := (h.diffeo g⁻¹).choose_spec.mapsTo
      left_inv := fun y hy => by rw [← h.hom g⁻¹ g y hy, inv_mul_cancel, Φ_one_of h hy]
      right_inv := fun y hy => by rw [← h.hom g g⁻¹ y hy, mul_inv_cancel, Φ_one_of h hy] }
  Φ_mul := h.hom
  isScSmoothOn_Γ := h.smooth
  Γ_self := h.Γ_x
  src_Γ g y hy := (h.src_tgt g y hy).1
  tgt_Γ g y hy := (h.src_tgt g y hy).2
  existsUnique_Γ := h.unique

end

/-- A set of left coset representatives of `H` is in bijection with `G ⧸ H`. -/
theorem card_reps {G : Type} [Group G] (H : Subgroup G) {R : Set G}
    (hR : IsLeftCosetRepsB (H : Set G) R) : Nat.card R = Nat.card (G ⧸ H) := by
  refine Nat.card_congr (Equiv.ofBijective (fun r : R => (r.1 : G ⧸ H)) ⟨?_, ?_⟩)
  · rintro ⟨r, hr⟩ ⟨r', hr'⟩ he
    have hmem : r⁻¹ * r' ∈ H := QuotientGroup.eq.1 he
    obtain ⟨r₀, -, huniq⟩ := hR r'
    have h1 := huniq r' ⟨hr', 1, H.one_mem, (mul_one r').symm⟩
    have h2 := huniq r ⟨hr, r⁻¹ * r', hmem, by group⟩
    exact Subtype.ext (h2.trans h1.symm)
  · intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨r, ⟨hr, h, hh, rfl⟩, -⟩ := hR g
      exact ⟨⟨r, hr⟩, QuotientGroup.eq.2 (by simpa using hh)⟩

theorem A_to_B : A → B := by
  intro hA
  obtain ⟨-, hker, hkerle, hiff, -, h923⟩ := hA
  intro Obj Mor _ _ _ _ _ _ X hLUC x U Φ Γ hN hc y hy
  let R := toNaturalRep hN hc
  have hL : R.HasLUC := (EpGroupoid.isLUC_iff_forall_naturalRep X).1 hLUC x R
  let a : R.U := ⟨y, hy⟩
  have hT : R.kerΦ = X.trivialSubgroup x := hker R hL
  have hstab : ((MulAction.stabilizer (X.Isotropy x) a : Subgroup (X.Isotropy x)) :
      Set (X.Isotropy x)) = stabB Φ y := by
    ext g
    exact MulAction.mem_stabilizer_iff.trans Subtype.ext_iff
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext g
    rw [SetLike.mem_coe, ← hT, R.mem_kerΦ]
    constructor
    · intro h
      exact ⟨U, hN.isOpen, ⟨x, hN.mem⟩, subset_rfl, h⟩
    · rintro ⟨W, hWo, hWne, hWU, hW⟩
      exact hL g W hWo hWne hWU hW
  · intro g hg
    rw [SetLike.mem_coe, ← hT] at hg
    rw [← hstab]
    exact hkerle R a hg
  · refine ⟨MulAction.stabilizer (X.Isotropy x) a, R.stabilizerEquivIsotropy a, hstab,
      fun h => rfl, fun h => ?_⟩
    have h1 := hiff R hL a h
    rw [hT] at h1
    exact h1.symm
  · intro R' hR'
    rw [← hstab] at hR'
    rw [card_reps _ hR']
    have h := h923 R hL a
    have hpos : 0 < Nat.card (X.EffIsotropy y) := Nat.card_pos
    exact (Nat.div_eq_of_eq_mul_left hpos h.symm).symm

#rt_check RoundTrip.V9_55.A_to_B [Polyfold.EpGroupoid.card_effIsotropy_mul_card_trivialSubgroup,
  Polyfold.EpGroupoid.NaturalRep.kerΦ_eq_trivialSubgroup,
  Polyfold.EpGroupoid.NaturalRep.kerΦ_le_stabilizer,
  Polyfold.EpGroupoid.NaturalRep.stabilizerEquivIsotropy_mem_trivialSubgroup_iff,
  Polyfold.EpGroupoid.NaturalRep.card_trivialSubgroup_eq,
  Polyfold.EpGroupoid.NaturalRep.card_quotient_stabilizer_mul_card_effIsotropy]
#rt_overlap RoundTrip.V9_55.A_to_B [Polyfold.EpGroupoid.card_effIsotropy_mul_card_trivialSubgroup,
  Polyfold.EpGroupoid.NaturalRep.kerΦ_eq_trivialSubgroup,
  Polyfold.EpGroupoid.NaturalRep.kerΦ_le_stabilizer,
  Polyfold.EpGroupoid.NaturalRep.stabilizerEquivIsotropy_mem_trivialSubgroup_iff,
  Polyfold.EpGroupoid.NaturalRep.card_trivialSubgroup_eq,
  Polyfold.EpGroupoid.NaturalRep.card_quotient_stabilizer_mul_card_effIsotropy]
#print axioms RoundTrip.V9_55.A_to_B

end RoundTrip.V9_55
