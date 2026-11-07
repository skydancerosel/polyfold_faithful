import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_22

/-! Round trip for V7_22 (p. 232: the functor `Γ : G_x ⋉ U(x) → X` is fully faithful).

`A` is the conjunction of the types of the five listed theorems, universes at `0`:
`NaturalRep.Γ_mul`, `Γ_one`, `Γ_inv`, and the instances `NaturalRep.full`, `NaturalRep.faithful`
(`functor`, `epFunctor`, `GroupoidStr.fullSub` are definitions, vocabulary).  All are stated for
`R : X.NaturalRep x`, whose `U` is **connected**.

* `B` is false (`not_B`): `B`'s natural action `IsNatAction` does not require `U` connected, and
  on a disconnected `U` the conditions (1)–(3) of Theorem 7.1 do not force `Γ` to be a functor.
  Witness: the project's `trivialZ3EpGroupoid` (`ℤ/3 × ℝ ⇉ ℝ`, trivial action), `x = 0`,
  `U = {y < 1} ∪ {y > 1}`, `Φ = id`, `Γ(g, y) = (g, y)` for `y < 1` and `(g c, y)` for `y > 1`
  (`c ≠ 1`).  This is a natural action in `B`'s sense, but `Γ(1, 2) = (c, 2) ≠ 1_2`.
  Hence `A → B` is false (`A` holds).
* `B → A`: `B` applied to the natural action underlying `R` gives `Γ_mul`, `Γ_one`, `Γ_inv`
  (uniqueness of inverses) and, from the bijection `{g | Φ g y = z} → mor(y, z)` and the injectivity
  on `G × U`, `Full` and `Faithful`.  The statement of `full`/`faithful` mentions `R.functor`,
  whose proof fields use `Γ_mul`, `Γ_one`: hence `#rt_check_soft`. -/

namespace RoundTrip.V7_22
open Polyfold Polyfold.EpGroupoid.Examples Set CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.NaturalRep.Γ_mul.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.Γ_one.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.Γ_inv.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.full.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.faithful.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.NaturalRep.Γ_mul.{0}, @Polyfold.EpGroupoid.NaturalRep.Γ_one.{0},
    @Polyfold.EpGroupoid.NaturalRep.Γ_inv.{0}, @Polyfold.EpGroupoid.NaturalRep.full.{0},
    @Polyfold.EpGroupoid.NaturalRep.faithful.{0}⟩

/-! ### `B → A` -/

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor} {x : Obj}

/-- The natural action underlying a natural representation. -/
theorem isNatAction_of_rep (R : X.NaturalRep x) : IsNatAction X x R.U R.Φ R.Γ where
  isOpen := R.isOpen_U
  mem := R.mem_U
  diffeo g := ⟨_, R.isScDiffeoOn_Φ g⟩
  hom := R.Φ_mul
  smooth := R.isScSmoothOn_Γ
  Γ_x := R.Γ_self
  src_tgt g y hy := ⟨R.src_Γ g y hy, R.tgt_Γ g y hy⟩
  unique := R.existsUnique_Γ

end

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X x R g h y hy
    exact ((hB Obj Mor X x R.U R.Φ R.Γ (isNatAction_of_rep R)).1 g h y hy).symm
  · intro Obj Mor _ _ _ _ _ _ X x R y hy
    exact (hB Obj Mor X x R.U R.Φ R.Γ (isNatAction_of_rep R)).2.1 y hy
  · intro Obj Mor _ _ _ _ _ _ X x R g y hy
    have hB' := hB Obj Mor X x R.U R.Φ R.Γ (isNatAction_of_rep R)
    refine GroupoidStr.eq_inv_of_comp_eq_unit (G := X.toGroupoidStr) ?_ ?_
    · rw [R.src_Γ _ _ (R.mapsTo_Φ g hy), R.tgt_Γ g y hy]
    · rw [← hB'.1 _ _ y hy, inv_mul_cancel, hB'.2.1 y hy, R.src_Γ g y hy]
  · intro Obj Mor _ _ _ _ _ _ X x R
    have hB' := hB Obj Mor X x R.U R.Φ R.Γ (isNatAction_of_rep R)
    refine ⟨fun {y z} f => ?_⟩
    let y' : R.U := y
    let z' : R.U := z
    have hy : X.src f.1 = y'.1 := f.2.1
    have hz : X.tgt f.1 = z'.1 := f.2.2
    obtain ⟨g, hg, hgf⟩ := (hB'.2.2.1 y'.1 y'.2 z'.1 z'.2).surjOn ⟨hy, hz⟩
    refine ⟨⟨(g, y'), rfl, Subtype.ext ?_⟩, Subtype.ext hgf⟩
    exact hg
  · intro Obj Mor _ _ _ _ _ _ X x R
    have hB' := hB Obj Mor X x R.U R.Φ R.Γ (isNatAction_of_rep R)
    refine ⟨fun {y z} {f f'} he => ?_⟩
    have he' : R.Γ f.1.1 f.1.2 = R.Γ f'.1.1 f'.1.2 := congrArg Subtype.val he
    have hp := hB'.2.2.2.2
      (show (f.1.1, (f.1.2 : Obj)) ∈ (univ ×ˢ R.U : Set (X.Isotropy x × Obj)) from
        ⟨mem_univ _, f.1.2.2⟩)
      (show (f'.1.1, (f'.1.2 : Obj)) ∈ (univ ×ˢ R.U : Set (X.Isotropy x × Obj)) from
        ⟨mem_univ _, f'.1.2.2⟩) he'
    have h1 : f.1.1 = f'.1.1 := (Prod.ext_iff.1 hp).1
    have h2 : (f.1.2 : Obj) = f'.1.2 := (Prod.ext_iff.1 hp).2
    exact Subtype.ext (Prod.ext h1 (Subtype.ext h2))

/-! ### `¬ B`: a disconnected natural action on which `Γ` is not a functor -/


/-- `ℤ/3 × ℝ ⇉ ℝ` (trivial action). -/
noncomputable abbrev XZ := trivialZ3EpGroupoid

/-- A disconnected open neighbourhood of `0`. -/
def Uc : Set (Fin 1 → ℝ) := {y | y 0 < 1} ∪ {y | 1 < y 0}

def cZ : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1

/-- `Γ` twisted by `c` on the component `{y 0 > 1}`. -/
noncomputable def Γc (g : XZ.Isotropy 0) (y : Fin 1 → ℝ) : Multiplicative (ZMod 3) × (Fin 1 → ℝ) :=
  (if y 0 < 1 then g.val.1 else g.val.1 * cZ, y)

def Φc (_ : XZ.Isotropy 0) (y : Fin 1 → ℝ) : Fin 1 → ℝ := y

theorem isOpen_A : IsOpen {y : Fin 1 → ℝ | y 0 < 1} := isOpen_lt (continuous_apply 0) continuous_const
theorem isOpen_B : IsOpen {y : Fin 1 → ℝ | 1 < y 0} := isOpen_lt continuous_const (continuous_apply 0)
theorem isOpen_Uc : IsOpen Uc := isOpen_A.union isOpen_B

/-- The isotropy element `(k, 0)`. -/
def isoOf (k : Multiplicative (ZMod 3)) : XZ.Isotropy 0 := ⟨(k, 0), rfl, rfl⟩

theorem src_XZ (p : Multiplicative (ZMod 3) × (Fin 1 → ℝ)) : XZ.src p = p.2 := rfl

theorem isotropy_val (g : XZ.Isotropy 0) : g.val = (g.val.1, 0) :=
  Prod.ext rfl ((src_XZ _).symm.trans g.src_val)

theorem isNatAction_cex : IsNatAction XZ 0 Uc Φc Γc where
  isOpen := isOpen_Uc
  mem := Or.inl (by simp)
  diffeo g := ⟨id, MPolyfold.isScDiffeoOn_id isOpen_Uc⟩
  hom _ _ _ _ := rfl
  smooth g := by
    refine MPolyfold.IsScSmoothOn.of_locally isOpen_Uc fun y hy => ?_
    rcases hy with hy | hy
    · refine ⟨_, isOpen_A, hy, subset_union_left, ?_⟩
      refine ((isScSmoothMap_sheet (PX := rnPolyfold 1) g.val.1).mono isOpen_A
        (subset_univ _)).congr fun z hz => ?_
      simp only [Γc, if_pos (show z 0 < 1 from hz)]
    · refine ⟨_, isOpen_B, hy, subset_union_right, ?_⟩
      refine ((isScSmoothMap_sheet (PX := rnPolyfold 1) (g.val.1 * cZ)).mono isOpen_B
        (subset_univ _)).congr fun z hz => ?_
      have : ¬ z 0 < 1 := not_lt.2 (le_of_lt hz)
      simp only [Γc, if_neg this]
  Γ_x g := by
    rw [isotropy_val g]
    simp [Γc]
  src_tgt _ _ _ := ⟨rfl, rfl⟩
  unique h hs ht := by
    rw [src_XZ] at hs ⊢
    by_cases h1 : h.2 0 < 1
    · refine ⟨isoOf h.1, ?_, fun g hg => ?_⟩
      · simp [Γc, isoOf, h1]
      · apply GroupoidStr.Isotropy.ext
        rw [isotropy_val g]
        have := congrArg Prod.fst hg
        simp only [Γc, if_pos h1] at this
        simp [isoOf, this]
    · refine ⟨isoOf (h.1 * cZ⁻¹), ?_, fun g hg => ?_⟩
      · simp [Γc, isoOf, h1]
      · apply GroupoidStr.Isotropy.ext
        rw [isotropy_val g]
        have := congrArg Prod.fst hg
        simp only [Γc, if_neg h1] at this
        simp [isoOf, ← this]

theorem not_B : ¬ B := by
  intro hB
  have h := (hB _ _ XZ 0 Uc Φc Γc isNatAction_cex).2.1 (fun _ => 2) (Or.inr (by norm_num))
  have h1 := congrArg Prod.fst h
  simp [Γc] at h1
  exact absurd h1 (by decide)

/-- `A → B` is false: `A` holds and `B` does not. -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

#rt_check_soft RoundTrip.V7_22.B_to_A [Polyfold.EpGroupoid.NaturalRep.Γ_mul,
  Polyfold.EpGroupoid.NaturalRep.Γ_one, Polyfold.EpGroupoid.NaturalRep.Γ_inv,
  Polyfold.EpGroupoid.NaturalRep.full, Polyfold.EpGroupoid.NaturalRep.faithful]
#rt_check RoundTrip.V7_22.not_B [Polyfold.EpGroupoid.NaturalRep.Γ_mul,
  Polyfold.EpGroupoid.NaturalRep.Γ_one, Polyfold.EpGroupoid.NaturalRep.Γ_inv,
  Polyfold.EpGroupoid.NaturalRep.full, Polyfold.EpGroupoid.NaturalRep.faithful]
#rt_overlap RoundTrip.V7_22.B_to_A [Polyfold.EpGroupoid.NaturalRep.Γ_mul,
  Polyfold.EpGroupoid.NaturalRep.Γ_one, Polyfold.EpGroupoid.NaturalRep.Γ_inv,
  Polyfold.EpGroupoid.NaturalRep.full, Polyfold.EpGroupoid.NaturalRep.faithful]

end RoundTrip.V7_22
