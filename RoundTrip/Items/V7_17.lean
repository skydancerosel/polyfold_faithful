import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_17

/-! Round trip for V7_17 (Theorem 7.1, p. 231: the natural representation of `G_x`).

`A` is the conjunction of the types of the listed theorems, universes at `0`:
`NaturalRep.Φ_one`, `NaturalRep.mapsTo_Φ`, `NaturalRep.Φ_inv_Φ`, `NaturalRep.bijOn_Γ` and
`EpGroupoid.theorem_7_1_13` (`∃ R : X.NaturalRep x, R.U ⊆ V`); `EpGroupoid.NaturalRep` (the structure)
is vocabulary.

Dictionary: `B`'s `Gx X x = {g // s g = x ∧ t g = x}` and the project's `X.Isotropy x` (a
structure with the same fields) are identified by `toG`/`ofG`; the products agree
(`(g * h).val = X.comp g.val h.val`).

* `A → B`: the `R` of `theorem_7_1_13` gives `B`'s data `U = R.U`, `Φ g = R.Φ g`, `Γ g = R.Γ g`;
  each clause of `B`'s `IsNatRepData` is a field of `NaturalRep` (with inverse `Φ(g⁻¹)`), and
  the bijection clause is `A`'s `bijOn_Γ` transported along `ofG`.
* `B → A`: the project's `NaturalRep` asks two things `B` does not give: `U` **connected**, and
  the inverse of `Φ(g)` to be `Φ(g⁻¹)`.  The second follows from `B` (`Φ(1) = id` on `U` because
  `Φ(1)` is injective and idempotent, then `Φ(g⁻¹) Φ(g) = Φ(1)`).  For the first, `U` is shrunk
  to the connected component `C` of `x` in `U`: it is open (M-polyfolds are locally connected),
  and invariant under every `Φ(g)` (a homeomorphism of `U` fixing `x`).  So `theorem_7_1_13` follows
  from `B`.  The other four conjuncts are facts about an arbitrary `R : NaturalRep`, not
  consequences of `B`; they are re-proved outright from the fields. -/

namespace RoundTrip.V7_17
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.NaturalRep.Φ_one.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.mapsTo_Φ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.Φ_inv_Φ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.bijOn_Γ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.theorem_7_1_13.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.NaturalRep.Φ_one.{0}, @Polyfold.EpGroupoid.NaturalRep.mapsTo_Φ.{0},
    @Polyfold.EpGroupoid.NaturalRep.Φ_inv_Φ.{0}, @Polyfold.EpGroupoid.NaturalRep.bijOn_Γ.{0},
    @Polyfold.EpGroupoid.theorem_7_1_13.{0}⟩

section Dictionary
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor} {x : Obj}

/-- The project's `G_x` element as `B`'s. -/
def toG (g : X.Isotropy x) : Gx X x := ⟨g.val, g.src_val, g.tgt_val⟩

/-- `B`'s `G_x` element as the project's. -/
def ofG (g : Gx X x) : X.Isotropy x := ⟨g.1, g.2.1, g.2.2⟩

@[simp] theorem toG_ofG (g : Gx X x) : toG (ofG g) = g := rfl
@[simp] theorem ofG_toG (g : X.Isotropy x) : ofG (toG g) = g := rfl

end Dictionary

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X x V hV hx
  obtain ⟨R, hRV⟩ := hA.2.2.2.2 X x hV hx
  have hbij := hA.2.2.2.1 R
  refine ⟨R.U, fun g => R.Φ (ofG g), fun g => R.Γ (ofG g), R.isOpen_U, R.mem_U, hRV,
    fun g => ⟨_, R.isScDiffeoOn_Φ (ofG g)⟩, fun g h k hk y hy => ?_,
    fun g => R.isScSmoothOn_Γ (ofG g), fun g => R.Γ_self (ofG g),
    fun g y hy => ⟨R.src_Γ (ofG g) y hy, R.tgt_Γ (ofG g) y hy⟩, fun h hs ht => ?_, ?_⟩
  · have : ofG k = ofG g * ofG h := GroupoidStr.Isotropy.ext hk
    simp only [this]
    exact R.Φ_mul _ _ y hy
  · obtain ⟨g, hg, hu⟩ := R.existsUnique_Γ h hs ht
    exact ⟨toG g, hg, fun g' hg' => by
      have := hu (ofG g') hg'
      rw [← this]
      rfl⟩
  · refine ⟨fun p hp => hbij.mapsTo (show (ofG p.1, p.2) ∈ univ ×ˢ R.U from ⟨trivial, hp.2⟩),
      fun p hp q hq he => ?_, fun φ hφ => ?_⟩
    · have := hbij.injOn (show (ofG p.1, p.2) ∈ univ ×ˢ R.U from ⟨trivial, hp.2⟩)
        (show (ofG q.1, q.2) ∈ univ ×ˢ R.U from ⟨trivial, hq.2⟩) he
      exact Prod.ext (Subtype.ext (congrArg GroupoidStr.Isotropy.val (Prod.ext_iff.1 this).1))
        (Prod.ext_iff.1 this).2
    · obtain ⟨q, hq, hqe⟩ := hbij.surjOn hφ
      exact ⟨(toG q.1, q.2), ⟨trivial, hq.2⟩, hqe⟩

/-! ### `B → A` -/

section Outright
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor} {x : Obj}

theorem Φ_one' (R : X.NaturalRep x) (y : Obj) (hy : y ∈ R.U) : R.Φ 1 y = y := by
  have h1 := (R.isScDiffeoOn_Φ 1).left_inv y hy
  rw [inv_one] at h1
  have h2 := R.Φ_mul 1 1 y hy
  rw [mul_one] at h2
  rw [h2]
  exact h1

theorem bijOn_Γ' (R : X.NaturalRep x) :
    BijOn (fun p : X.Isotropy x × Obj => R.Γ p.1 p.2) (univ ×ˢ R.U) (X.morOn R.U) := by
  have hmem : ∀ g, ∀ y ∈ R.U, R.Γ g y ∈ X.morOn R.U := fun g y hy =>
    ⟨by rw [R.src_Γ g y hy]; exact hy,
      by rw [R.tgt_Γ g y hy]; exact (R.isScDiffeoOn_Φ g).mapsTo hy⟩
  refine ⟨fun p hp => hmem p.1 p.2 hp.2, fun p hp q hq he => ?_, fun φ hφ => ?_⟩
  · have h2 : p.2 = q.2 := by
      have := congrArg X.src he
      simp only [R.src_Γ _ _ hp.2, R.src_Γ _ _ hq.2] at this
      exact this
    have hm := hmem q.1 q.2 hq.2
    obtain ⟨k, -, hk⟩ := R.existsUnique_Γ _ hm.1 hm.2
    have hs : X.src (R.Γ q.1 q.2) = q.2 := R.src_Γ _ _ hq.2
    rw [hs] at hk
    have he0 : R.Γ p.1 p.2 = R.Γ q.1 q.2 := he
    have he' : R.Γ p.1 q.2 = R.Γ q.1 q.2 := by rw [h2] at he0; exact he0
    exact Prod.ext ((hk p.1 he').trans (hk q.1 rfl).symm) h2
  · obtain ⟨g, hg, -⟩ := R.existsUnique_Γ φ hφ.1 hφ.2
    exact ⟨(g, X.src φ), ⟨mem_univ _, hφ.1⟩, hg⟩

/-- **`theorem_7_1_13` from `B`'s data**: shrink `U` to the connected component of `x`. -/
theorem naturalRep_of_isNatRepData {U : Set Obj} {Φ : Gx X x → Obj → Obj}
    {Γ : Gx X x → Obj → Mor} (hUo : IsOpen U) (hxU : x ∈ U) (hd : IsNatRepData X x U Φ Γ) :
    ∃ R : X.NaturalRep x, R.U ⊆ U := by
  obtain ⟨hdiff, hmul, hsm, hself, hst, huniq, -⟩ := hd
  set Φ' : X.Isotropy x → Obj → Obj := fun g => Φ (toG g) with hΦ'
  have hmul' : ∀ g h : X.Isotropy x, ∀ y ∈ U, Φ' (g * h) y = Φ' g (Φ' h y) :=
    fun g h y hy => hmul (toG g) (toG h) (toG (g * h)) rfl y hy
  have hmaps : ∀ g, MapsTo (Φ' g) U U := fun g => by
    obtain ⟨ψ, hψ⟩ := hdiff (toG g)
    exact hψ.mapsTo
  have hone : ∀ y ∈ U, Φ' 1 y = y := fun y hy => by
    obtain ⟨ψ, hψ⟩ := hdiff (toG 1)
    have h := hmul' 1 1 y hy
    rw [mul_one] at h
    have := congrArg ψ h
    rw [hψ.left_inv _ hy, hψ.left_inv _ (hmaps 1 hy)] at this
    exact this.symm
  have hinv : ∀ g, ∀ y ∈ U, Φ' g⁻¹ (Φ' g y) = y := fun g y hy => by
    rw [← hmul' _ _ y hy, inv_mul_cancel, hone y hy]
  have hinv' : ∀ g, ∀ y ∈ U, Φ' g (Φ' g⁻¹ y) = y := fun g y hy => by
    rw [← hmul' _ _ y hy, mul_inv_cancel, hone y hy]
  have hsmΦ : ∀ g, X.PObj.IsScSmoothOn X.PObj (Φ' g) U := fun g => by
    obtain ⟨ψ, hψ⟩ := hdiff (toG g)
    exact hψ.isScSmoothOn
  have hfix : ∀ g, Φ' g x = x := fun g => by
    show Φ (toG g) x = x
    rw [← (hst (toG g) x hxU).2, hself (toG g)]
    exact g.tgt_val
  -- the connected component of `x` in `U`
  set C := connectedComponentIn U x
  have hCo : IsOpen C := X.PObj.isOpen_connectedComponentIn hUo x
  have hCU : C ⊆ U := connectedComponentIn_subset U x
  have hxC : x ∈ C := mem_connectedComponentIn hxU
  have hCinv : ∀ g, MapsTo (Φ' g) C C := fun g y hy => by
    have hpre : IsPreconnected (Φ' g '' C) :=
      isPreconnected_connectedComponentIn.image _ ((hsmΦ g).continuousOn.mono hCU)
    exact hpre.subset_connectedComponentIn ⟨x, hxC, hfix g⟩
      ((hmaps g).mono_left hCU).image_subset ⟨y, hy, rfl⟩
  refine ⟨{ U := C
            isOpen_U := hCo
            isConnected_U := isConnected_connectedComponentIn_iff.2 hxU
            mem_U := hxC
            Φ := Φ'
            Γ := fun g => Γ (toG g)
            isScDiffeoOn_Φ := fun g =>
              { isScSmoothOn := (hsmΦ g).mono hCo hCU
                isScSmoothOn_inv := (hsmΦ g⁻¹).mono hCo hCU
                mapsTo := hCinv g
                mapsTo_inv := hCinv g⁻¹
                left_inv := fun y hy => hinv g y (hCU hy)
                right_inv := fun y hy => hinv' g y (hCU hy) }
            Φ_mul := fun g h y hy => hmul' g h y (hCU hy)
            isScSmoothOn_Γ := fun g => (hsm (toG g)).mono hCo hCU
            Γ_self := fun g => hself (toG g)
            src_Γ := fun g y hy => (hst (toG g) y (hCU hy)).1
            tgt_Γ := fun g y hy => (hst (toG g) y (hCU hy)).2
            existsUnique_Γ := fun h hs ht => by
              obtain ⟨g, hg, hu⟩ := huniq h (hCU hs) (hCU ht)
              refine ⟨ofG g, hg, fun g' hg' => ?_⟩
              have := hu (toG g') hg'
              rw [← this]
              rfl }, hCU⟩

end Outright

theorem B_to_A : B → A := by
  intro hB
  refine ⟨@Φ_one', fun R g => (R.isScDiffeoOn_Φ g).mapsTo,
    fun R g y hy => (R.isScDiffeoOn_Φ g).left_inv y hy, @bijOn_Γ', ?_⟩
  intro Obj Mor _ _ _ _ _ _ X x V hV hx
  obtain ⟨U, Φ, Γ, hUo, hxU, hUV, hd⟩ := hB Obj Mor X x V hV hx
  obtain ⟨R, hRU⟩ := naturalRep_of_isNatRepData hUo hxU hd
  exact ⟨R, hRU.trans hUV⟩

#rt_check RoundTrip.V7_17.A_to_B [Polyfold.EpGroupoid.NaturalRep.Φ_one,
  Polyfold.EpGroupoid.NaturalRep.mapsTo_Φ, Polyfold.EpGroupoid.NaturalRep.Φ_inv_Φ,
  Polyfold.EpGroupoid.NaturalRep.bijOn_Γ, Polyfold.EpGroupoid.theorem_7_1_13]
#rt_check RoundTrip.V7_17.B_to_A [Polyfold.EpGroupoid.NaturalRep.Φ_one,
  Polyfold.EpGroupoid.NaturalRep.mapsTo_Φ, Polyfold.EpGroupoid.NaturalRep.Φ_inv_Φ,
  Polyfold.EpGroupoid.NaturalRep.bijOn_Γ, Polyfold.EpGroupoid.theorem_7_1_13]
#rt_overlap RoundTrip.V7_17.B_to_A [Polyfold.EpGroupoid.NaturalRep.Φ_one,
  Polyfold.EpGroupoid.NaturalRep.mapsTo_Φ, Polyfold.EpGroupoid.NaturalRep.Φ_inv_Φ,
  Polyfold.EpGroupoid.NaturalRep.bijOn_Γ, Polyfold.EpGroupoid.theorem_7_1_13]

end RoundTrip.V7_17
