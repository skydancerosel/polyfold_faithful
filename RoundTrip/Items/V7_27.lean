import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_27

/-! Round trip for V7_27 (Proposition 7.6, p. 236: `τ : G_x\U(x) → |U(x)|` is a homeomorphism;
the functor `G_x ⋉ U(x) → X` is fully faithful).

`A` is the conjunction of the types of the three listed **theorems**, universes at `0`:
`NaturalRep.π_eq_π_iff_exists_smul`, `NaturalRep.isOpenEmbedding_orbitQuotientMap`,
`NaturalRep.range_orbitQuotientMap`.  The other listed declarations are definitions (data):
`orbitQuotientMap` (the map `τ` into `|X|`), `proposition_7_1_19 : G_x\U(x) ≃ₜ π(U(x))`,
`proposition_7_1_19_fullyFaithful`, `proposition_7_1_19_orbitMap`, `translationOrbitHomeomorph`; the
homeomorphism `proposition_7_1_19` is built from the two theorems on `orbitQuotientMap`.  All are
stated for `R : X.NaturalRep x`, whose `U` is **connected**.

* `B` is false (`not_B`), for the same reason as V7_22: `B`'s natural action does not require `U`
  connected, and `B` includes "the obvious functor preserves units/composition", which fails on a
  disconnected `U` (the project's `trivialZ3EpGroupoid`, `U = {y < 1} ∪ {y > 1}`, `Γ` twisted by
  `c ≠ 1` on `{y > 1}`: `Γ(1, 2) ≠ 1_2`).  So `A → B` is false.  (`B`'s homeomorphism and
  full-faithfulness claims are true for disconnected `U` as well.)
* `B → A`: `π_eq_π_iff_exists_smul` from `B`'s homeomorphism `τ` (injectivity of `τ` and
  `τ[y] = |y|`; the orbit relation is an equivalence); `isOpenEmbedding_orbitQuotientMap` from
  that (injectivity) together with continuity of the quotient lift and openness of `π`
  (`proposition_7_1_8`, Proposition 7.1); `range_orbitQuotientMap` directly.  `orbitQuotientMap`'s
  well-definedness proof uses `π_eq_π_iff_exists_smul`: hence `#rt_check_soft`. -/

namespace RoundTrip.V7_27
open Polyfold Polyfold.EpGroupoid.Examples Set Topology

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.NaturalRep.π_eq_π_iff_exists_smul.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_orbitQuotientMap.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.range_orbitQuotientMap.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.NaturalRep.π_eq_π_iff_exists_smul.{0},
    @Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_orbitQuotientMap.{0},
    @Polyfold.EpGroupoid.NaturalRep.range_orbitQuotientMap.{0}⟩

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

/-- The orbit relation is an equivalence. -/
theorem orbRel_equivalence (R : X.NaturalRep x) : Equivalence (orbRel X x R.U R.Φ) where
  refl y := ⟨1, R.Φ_one y y.2⟩
  symm := by
    rintro y z ⟨g, hg⟩
    refine ⟨g⁻¹, ?_⟩
    rw [← hg, R.Φ_inv_Φ g y.2]
  trans := by
    rintro y z w ⟨g, hg⟩ ⟨h, hh⟩
    refine ⟨h * g, ?_⟩
    rw [R.Φ_mul h g y y.2, hg, hh]

/-- `π_eq_π_iff_exists_smul` from `B`'s homeomorphism `τ`. -/
theorem π_eq_π_iff_of_tau (R : X.NaturalRep x)
    (τ : Quot (orbRel X x R.U R.Φ) ≃ₜ ↥(X.π '' R.U))
    (hτ : ∀ y : R.U, (τ (Quot.mk _ y) : X.OrbitSpace) = X.π y) {y z : R.U} :
    X.π y = X.π z ↔ ∃ g : X.Isotropy x, g • y = z := by
  constructor
  · intro h
    have h1 : τ (Quot.mk _ y) = τ (Quot.mk _ z) := Subtype.ext (by rw [hτ, hτ, h])
    have h2 := Quot.eqvGen_exact (τ.injective h1)
    obtain ⟨g, hg⟩ := ((orbRel_equivalence R).eqvGen_iff).1 h2
    exact ⟨g, Subtype.ext hg⟩
  · rintro ⟨g, hg⟩
    have h1 : (Quot.mk _ y : Quot (orbRel X x R.U R.Φ)) = Quot.mk _ z :=
      Quot.sound ⟨g, congrArg Subtype.val hg⟩
    rw [← hτ, ← hτ, h1]

end

theorem B_to_A : B → A := by
  intro hB
  have key : ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (x : Obj) (R : X.NaturalRep x) (y z : R.U),
      X.π y = X.π z ↔ ∃ g : X.Isotropy x, g • y = z := by
    intro Obj Mor _ _ _ _ _ _ X x R y z
    obtain ⟨⟨τ, hτ⟩, -⟩ := hB Obj Mor X x R.U R.Φ R.Γ (isNatAction_of_rep R)
    exact π_eq_π_iff_of_tau R τ hτ
  refine ⟨?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X x R y z
    exact key Obj Mor X x R y z
  · intro Obj Mor _ _ _ _ _ _ X x R
    have hc : Continuous R.orbitQuotientMap :=
      isQuotientMap_quotient_mk'.continuous_iff.2 (X.continuous_π.comp continuous_subtype_val)
    refine .of_continuous_injective_isOpenMap hc (fun q q' h => ?_) fun S hS => ?_
    · induction q using Quotient.inductionOn with | h y => ?_
      induction q' using Quotient.inductionOn with | h z => ?_
      obtain ⟨g, hg⟩ := (key Obj Mor X x R y z).1 h
      exact Quotient.sound ⟨g⁻¹, show g⁻¹ • z = y by rw [← hg, inv_smul_smul]⟩
    · have himage : R.orbitQuotientMap '' S =
          X.π '' (Subtype.val '' (Quotient.mk (MulAction.orbitRel (X.Isotropy x) R.U) ⁻¹' S)) := by
        ext w
        constructor
        · rintro ⟨q, hq, rfl⟩
          induction q using Quotient.inductionOn with | h y => ?_
          exact ⟨y, ⟨y, hq, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
          exact ⟨Quotient.mk _ y, hy, rfl⟩
      rw [himage]
      exact X.proposition_7_1_8 _ (R.isOpen_U.isOpenMap_subtype_val _
        (hS.preimage continuous_quotient_mk'))
  · intro Obj Mor _ _ _ _ _ _ X x R
    ext w
    constructor
    · rintro ⟨q, rfl⟩
      induction q using Quotient.inductionOn with | h y => ?_
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Quotient.mk _ ⟨y, hy⟩, rfl⟩

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
  have h := (hB _ _ XZ 0 Uc Φc Γc isNatAction_cex).2.2.1 (fun _ => 2) (Or.inr (by norm_num))
  have h1 := congrArg Prod.fst h
  simp [Γc] at h1
  exact absurd h1 (by decide)

/-- `A → B` is false: `A` holds and `B` does not. -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

#rt_check_soft RoundTrip.V7_27.B_to_A [Polyfold.EpGroupoid.NaturalRep.π_eq_π_iff_exists_smul,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_orbitQuotientMap,
  Polyfold.EpGroupoid.NaturalRep.range_orbitQuotientMap]
#rt_check RoundTrip.V7_27.not_B [Polyfold.EpGroupoid.NaturalRep.π_eq_π_iff_exists_smul,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_orbitQuotientMap,
  Polyfold.EpGroupoid.NaturalRep.range_orbitQuotientMap]
#rt_overlap RoundTrip.V7_27.B_to_A [Polyfold.EpGroupoid.NaturalRep.π_eq_π_iff_exists_smul,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_orbitQuotientMap,
  Polyfold.EpGroupoid.NaturalRep.range_orbitQuotientMap]

end RoundTrip.V7_27
