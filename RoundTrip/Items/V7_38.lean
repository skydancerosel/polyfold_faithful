import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_38

/-! Round trip for V7_38 (Definition 7.12, p. 241: `𝐗^T` and the reduced morphisms `𝐗^R`).

`A` is the conjunction of the types of the listed theorems, universes at `0`:
`mem_nonEffectivePart_iff` (`k ∈ 𝐗^T ↔ s = t near k`), `nonEffectivePart_eq_interior`
(`𝐗^T = int{s = t}`), `reducedRel_iff` (`φ ∼ φ' ↔ φ = φ' ∘ k`, `k ∈ 𝐗^T`),
`reducedRel_comp_left` (`k ∘ φ ∼ φ`) and `reducedMor_eq_quotient` (`𝐗^R = Quotient reducedSetoid`).
`nonEffectivePart`, `ReducedRel`, `reducedSetoid`, `ReducedMor` are vocabulary.

Dictionary (no hypothesis needed): `B`'s `NatRepB` and the project's `NaturalRep` (`toB`, `ofB`),
hence `TxB = trivialSet`, `XTB = nonEffectivePart` and `RelB = ReducedRel` (the same formula).

* `A → B`: the first two conjuncts of `B` (the project's `𝐗^T` and `∼` are the text's) and
  surjectivity of `reducedπ` hold by the dictionary alone.  That `∼` is an equivalence relation
  is derived from `A`'s `reducedRel_iff` and `mem_nonEffectivePart_iff` (`s = t` on `𝐗^T`) with the
  closure of `𝐗^T` under units, inverses and composition (`unit_mem_nonEffectivePart`, …, from the
  subgroup `trivialSubgroup`); `reducedπ φ = reducedπ φ' ↔ φ ∼ φ'` then follows (`Quot.eq`,
  `Equivalence.eqvGen_iff`).
* `B → A`: proved outright, without `B`: `A`'s theorems are facts about the project's
  definitions that `B` does not state (the intrinsic description of `𝐗^T` comes from
  `mem_trivialSet_iff_eventually`, `Effective.lean`; the left form from
  `conj_mem_nonEffectivePart`, i.e. `φ T_x φ⁻¹ = T_y`).  The project's proofs are copied with
  the listed theorems replaced.

`#rt_check_soft` for both directions: `A` (the statement `reducedMor_eq_quotient`, which is the
type of `hA` in `A → B` and a conclusion in `B → A`) mentions `reducedSetoid`, whose proof field
`iseqv` uses the banned `reducedRel_iff` and (through `src_eq_tgt_of_mem_nonEffectivePart`)
`mem_nonEffectivePart_iff`; no proof here uses them otherwise.
-/

namespace RoundTrip.V7_38
open Polyfold Set Filter Topology Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.mem_nonEffectivePart_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.nonEffectivePart_eq_interior.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.reducedRel_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.reducedRel_comp_left.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.reducedMor_eq_quotient.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.mem_nonEffectivePart_iff.{0},
    @Polyfold.EpGroupoid.nonEffectivePart_eq_interior.{0},
    @Polyfold.EpGroupoid.reducedRel_iff.{0},
    @Polyfold.EpGroupoid.reducedRel_comp_left.{0},
    @Polyfold.EpGroupoid.reducedMor_eq_quotient.{0}⟩

section Dictionary
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor} {x : Obj}

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

theorem TxB_eq (x : Obj) : TxB X x = X.trivialSet x := by
  ext g
  exact ⟨fun ⟨R, h⟩ => ⟨ofB R, h⟩, fun ⟨R, h⟩ => ⟨toB R, h⟩⟩

theorem XTB_eq : XTB X = X.nonEffectivePart := by
  ext φ
  refine ⟨fun ⟨x, g, hg, he⟩ => ⟨x, g, ?_, he⟩, fun ⟨x, g, hg, he⟩ => ⟨x, g, ?_, he⟩⟩
  · rw [← TxB_eq]; exact hg
  · rw [TxB_eq]; exact hg

theorem relB_iff {φ φ' : Mor} : RelB X φ φ' ↔ X.ReducedRel φ φ' := by
  refine ⟨fun ⟨h1, g, hg, he⟩ => ⟨h1, g, ?_, he⟩, fun ⟨h1, g, hg, he⟩ => ⟨h1, g, ?_, he⟩⟩
  · rw [← TxB_eq]; exact hg
  · rw [TxB_eq]; exact hg

end Dictionary

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  obtain ⟨h1, -, h3, -, -⟩ := hA
  have hst : ∀ {k : Mor}, k ∈ X.nonEffectivePart → X.src k = X.tgt k := fun hk =>
    ((h1 X).1 hk).self_of_nhds
  have hrefl : ∀ φ, X.ReducedRel φ φ := fun φ =>
    h3.2 ⟨X.unit (X.src φ), X.unit_mem_nonEffectivePart _, (X.tgt_unit _).symm,
      (X.comp_unit φ).symm⟩
  have hsymm : ∀ {φ φ'}, X.ReducedRel φ φ' → X.ReducedRel φ' φ := by
    intro φ φ' h
    obtain ⟨k, hk, hc, rfl⟩ := h3.1 h
    refine h3.2 ⟨X.inv k, EpGroupoid.inv_mem_nonEffectivePart hk, ?_, ?_⟩
    · rw [X.src_comp _ _ hc, X.tgt_inv]
    · exact (GroupoidStr.comp_inv_cancel_right hc).symm
  have htrans : ∀ {φ φ' φ''}, X.ReducedRel φ φ' → X.ReducedRel φ' φ'' → X.ReducedRel φ φ'' := by
    intro φ φ' φ'' h h'
    obtain ⟨k, hk, hc, rfl⟩ := h3.1 h
    obtain ⟨k', hk', hc', rfl⟩ := h3.1 h'
    have hkk' : X.src k' = X.tgt k := (X.src_comp _ _ hc').symm.trans hc
    refine h3.2 ⟨X.comp k' k, EpGroupoid.comp_mem_nonEffectivePart hk' hk hkk', ?_, ?_⟩
    · rw [X.tgt_comp _ _ hkk']
      exact hc'
    · exact X.comp_assoc _ _ _ hc' hkk'
  have heqv : Equivalence X.ReducedRel := ⟨hrefl, hsymm, htrans⟩
  have hRB : RelB X = X.ReducedRel := funext fun φ => funext fun φ' => propext relB_iff
  refine ⟨XTB_eq.symm, fun φ φ' => relB_iff.symm, hRB ▸ heqv, Quot.mk_surjective,
    fun φ φ' => ?_⟩
  rw [hRB]
  exact Quot.eq.trans heqv.eqvGen_iff

/-! ### `B → A`, outright -/

section Outright
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

theorem mem_nonEffectivePart_iff' {k : Mor} :
    k ∈ X.nonEffectivePart ↔ ∀ᶠ ψ in 𝓝 k, X.src ψ = X.tgt ψ := by
  constructor
  · rintro ⟨x, g, hg, rfl⟩
    exact X.mem_trivialSet_iff_eventually.1 hg
  · intro h
    have hk : X.src k = X.tgt k := h.self_of_nhds
    exact ⟨X.src k, ⟨k, rfl, hk.symm⟩, X.mem_trivialSet_iff_eventually.2 h, rfl⟩

theorem nonEffectivePart_eq_interior' :
    X.nonEffectivePart = interior {ψ | X.src ψ = X.tgt ψ} := by
  ext k
  rw [mem_nonEffectivePart_iff', mem_interior_iff_mem_nhds]
  rfl

variable {X}

theorem src_eq_tgt' {k : Mor} (hk : k ∈ X.nonEffectivePart) : X.src k = X.tgt k :=
  ((mem_nonEffectivePart_iff' X).1 hk).self_of_nhds

theorem val_mem_nonEffectivePart_iff' {x : Obj} {g : X.Isotropy x} :
    g.val ∈ X.nonEffectivePart ↔ g ∈ X.trivialSet x := by
  rw [mem_nonEffectivePart_iff', X.mem_trivialSet_iff_eventually]

theorem reducedRel_iff' {φ φ' : Mor} : X.ReducedRel φ φ' ↔
    ∃ k ∈ X.nonEffectivePart, X.src φ' = X.tgt k ∧ φ = X.comp φ' k := by
  constructor
  · rintro ⟨hs, g, hg, he⟩
    exact ⟨g.val, ⟨_, g, hg, rfl⟩, by rw [g.tgt_val, hs], he⟩
  · rintro ⟨k, hk, hc, rfl⟩
    have hkk := src_eq_tgt' hk
    have hs : X.src (X.comp φ' k) = X.src k := X.src_comp _ _ hc
    refine ⟨hs.trans (hkk.trans hc.symm), ⟨k, hs.symm, hkk.symm.trans hs.symm⟩, ?_, rfl⟩
    exact val_mem_nonEffectivePart_iff'.1 hk

theorem reducedRel_comp_left' {k φ : Mor} (hk : k ∈ X.nonEffectivePart)
    (h : X.src k = X.tgt φ) : X.ReducedRel (X.comp k φ) φ := by
  have hc : X.src (X.inv φ) = X.tgt (X.comp k φ) := by
    rw [X.src_inv, X.tgt_comp _ _ h, ← h, src_eq_tgt' hk]
  refine reducedRel_iff'.2 ⟨_, EpGroupoid.conj_mem_nonEffectivePart hk h, ?_, ?_⟩
  · rw [X.tgt_comp _ _ hc, X.tgt_inv]
  · rw [← X.comp_assoc _ _ _ (X.tgt_inv φ).symm hc, X.comp_inv,
      GroupoidStr.unit_comp_of_eq (by rw [X.tgt_comp _ _ h, ← h, src_eq_tgt' hk])]

end Outright

theorem B_to_A : B → A := fun _ =>
  ⟨fun X => mem_nonEffectivePart_iff' X, fun X => nonEffectivePart_eq_interior' X,
    reducedRel_iff', reducedRel_comp_left', fun _ => rfl⟩

#rt_check_soft RoundTrip.V7_38.A_to_B [Polyfold.EpGroupoid.mem_nonEffectivePart_iff,
  Polyfold.EpGroupoid.nonEffectivePart_eq_interior, Polyfold.EpGroupoid.reducedRel_iff,
  Polyfold.EpGroupoid.reducedRel_comp_left, Polyfold.EpGroupoid.reducedMor_eq_quotient]
#rt_check_soft RoundTrip.V7_38.B_to_A [Polyfold.EpGroupoid.mem_nonEffectivePart_iff,
  Polyfold.EpGroupoid.nonEffectivePart_eq_interior, Polyfold.EpGroupoid.reducedRel_iff,
  Polyfold.EpGroupoid.reducedRel_comp_left, Polyfold.EpGroupoid.reducedMor_eq_quotient]
#rt_overlap RoundTrip.V7_38.B_to_A [Polyfold.EpGroupoid.mem_nonEffectivePart_iff,
  Polyfold.EpGroupoid.nonEffectivePart_eq_interior, Polyfold.EpGroupoid.reducedRel_iff,
  Polyfold.EpGroupoid.reducedRel_comp_left, Polyfold.EpGroupoid.reducedMor_eq_quotient]

end RoundTrip.V7_38
