import Polyfold
import Polyfold.Test
import RoundTrip.Check
import RoundTrip.Blind.V1_35

/-! Round trip for V1_35 (after Definition 1.14: in finite dimensions sc¹ is `C¹`, also at the
boundary).

`A` is the conjunction of the types of the item's theorems (all of them theorems):
`ScBanach.lvlSet_const`, `isSc1_iff_contDiffOn_const`, `isSc1_iff_fderivWithin_const`,
`isScSmooth_iff_contDiffOn_const`, `isSc1_iff_contDiffOn_of_isRelOpenInQuadrant`,
`isScSmooth_iff_contDiffOn_of_isRelOpenInQuadrant` (all in `Chapter1/ExpositionLemmas.lean`) and
`isSc1_iff_contDiffOn_of_finiteDimensional` (in `Polyfold/Test.lean`, which `import Polyfold`
does not import, hence `import Polyfold.Test`).  No universe parameters (`V W : Type`). -/

namespace RoundTrip.V1_35
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.ScBanach.lvlSet_const) ∧
  (type_of% @Polyfold.isSc1_iff_contDiffOn_const) ∧
  (type_of% @Polyfold.isSc1_iff_fderivWithin_const) ∧
  (type_of% @Polyfold.isScSmooth_iff_contDiffOn_const) ∧
  (type_of% @Polyfold.isSc1_iff_contDiffOn_of_isRelOpenInQuadrant) ∧
  (type_of% @Polyfold.isScSmooth_iff_contDiffOn_of_isRelOpenInQuadrant) ∧
  (type_of% @Polyfold.isSc1_iff_contDiffOn_of_finiteDimensional)

theorem A_holds : A :=
  ⟨@Polyfold.ScBanach.lvlSet_const, @Polyfold.isSc1_iff_contDiffOn_const,
    @Polyfold.isSc1_iff_fderivWithin_const, @Polyfold.isScSmooth_iff_contDiffOn_const,
    @Polyfold.isSc1_iff_contDiffOn_of_isRelOpenInQuadrant,
    @Polyfold.isScSmooth_iff_contDiffOn_of_isRelOpenInQuadrant,
    @Polyfold.isSc1_iff_contDiffOn_of_finiteDimensional⟩

/-! ### Glue: transport along `E ≅ const E₀` (the identity on level `0`) -/

section Glue

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem lvlSet_const' (U : Set V) (m : ℕ) : (ScBanach.const V).lvlSet U m = U := by
  ext x
  rw [ScBanach.mem_lvlSet, ScBanach.const_toBase]

/-- An sc-domain of `E` is, on level `0`, an sc-domain of `E₀` with the constant structure. -/
theorem isScDomain_const {E : ScBanach} [FiniteDimensional ℝ (E 0)] {U : Set (E 0)}
    (hU : IsScDomain E U) : IsScDomain (ScBanach.const (E 0)) U where
  relOpenConvex m := by
    obtain ⟨O, C, hO, hC, h⟩ := hU.relOpenConvex 0
    exact ⟨O, C, hO, hC, by rw [lvlSet_const']; exact h⟩
  uniqueDiffWithinAt m x hx := by
    rw [lvlSet_const'] at hx ⊢
    exact hU.uniqueDiffWithinAt 0 x hx

theorem iso_zero (E : ScBanach) [FiniteDimensional ℝ (E 0)] (x : E 0) :
    E.isoConstOfFiniteDimensional 0 x = x := by
  rw [ScBanach.isoConstOfFiniteDimensional_apply]; rfl

theorem iso_symm_zero (E : ScBanach) [FiniteDimensional ℝ (E 0)] (x : E 0) :
    (E.isoConstOfFiniteDimensional 0).symm x = x := by
  have := iso_zero E ((E.isoConstOfFiniteDimensional 0).symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply] at this
  exact this.symm

/-- sc¹ for `E → F` is sc¹ for `E₀ → F₀` with the constant structures (finite dimensions). -/
theorem isSc1_iff_const {E F : ScBanach} [FiniteDimensional ℝ (E 0)] [FiniteDimensional ℝ (F 0)]
    {U : Set (E 0)} (hU : IsScDomain E U) (f : E 0 → F 0) :
    IsSc1 (E := E) (F := F) U f ↔
      IsSc1 (E := ScBanach.const (E 0)) (F := ScBanach.const (F 0)) U f := by
  have hU' := isScDomain_const hU
  set φ := E.isoConstOfFiniteDimensional
  set ψ := F.isoConstOfFiniteDimensional
  have e1 : ∀ x, φ.symm.toScOperator 0 x = x := fun x => iso_symm_zero E x
  have e2 : ∀ x, φ.toScOperator 0 x = x := fun x => iso_zero E x
  have e3 : ∀ y, ψ.symm.toScOperator 0 y = y := fun y => iso_symm_zero F y
  have e4 : ∀ y, ψ.toScOperator 0 y = y := fun y => iso_zero F y
  constructor
  · intro hf
    have h1 := (theorem_1_3_1' hU' hU (φ.symm.toScOperator.isScSmooth hU' 1).1 hf
      (fun x hx => by rw [e1]; exact hx)).1
    have h2 := (theorem_1_3_1' hU' (isScDomain_univ F) h1
      (ψ.toScOperator.isScSmooth (isScDomain_univ F) 1).1 (Set.mapsTo_univ _ _)).1
    refine h2.congr fun x _ => ?_
    change ψ.toScOperator 0 (f (φ.symm.toScOperator 0 x)) = f x
    rw [e1, e4]
  · intro hf
    have h1 := (theorem_1_3_1' hU hU' (φ.toScOperator.isScSmooth hU 1).1 hf
      (fun x hx => by rw [e2]; exact hx)).1
    have h2 := (theorem_1_3_1' hU (isScDomain_univ _) h1
      (ψ.symm.toScOperator.isScSmooth (isScDomain_univ _) 1).1 (Set.mapsTo_univ _ _)).1
    refine h2.congr fun x _ => ?_
    change ψ.symm.toScOperator 0 (f (φ.toScOperator 0 x)) = f x
    rw [e2, e3]

end Glue

/-- `A → B`: transport along the sc-isomorphisms `E ≅ const E₀`, `F ≅ const F₀` (identity on
level `0`; `isoConstOfFiniteDimensional`, the chain rule and `ScOperator.isScSmooth`), then A's
`isSc1_iff_contDiffOn_const`. -/
theorem A_to_B : A → B := by
  intro hA E F hE hF C U f hU
  rw [isSc1_iff_const hU.isScDomain f]
  exact hA.2.1 (isScDomain_const hU.isScDomain) f

/-- What `B` does give: the sc¹ conjuncts of `A` whose domain is relatively open in a partial
quadrant (`isSc1_iff_contDiffOn_of_isRelOpenInQuadrant`) or open
(`isSc1_iff_contDiffOn_of_finiteDimensional`).  The other conjuncts of `A` (sc-domains that are
not relatively open in a quadrant; sc-smooth ⇔ `C^∞`) are not consequences of `B`. -/
theorem B_to_A_partial : B →
    (type_of% @Polyfold.isSc1_iff_contDiffOn_of_isRelOpenInQuadrant) ∧
    (type_of% @Polyfold.isSc1_iff_contDiffOn_of_finiteDimensional) := by
  intro hB
  refine ⟨fun {V W} _ _ _ _ _ _ {C U} hU f => hB _ _ inferInstance inferInstance C U f hU,
    fun {V W} _ _ _ _ _ _ {U} hU f => ?_⟩
  exact hB _ _ inferInstance inferInstance Set.univ U f
    ⟨isPartialQuadrant_univ _, U, hU, (Set.inter_univ U).symm⟩

#rt_check RoundTrip.V1_35.A_to_B [Polyfold.ScBanach.lvlSet_const,
  Polyfold.isSc1_iff_contDiffOn_const, Polyfold.isSc1_iff_fderivWithin_const,
  Polyfold.isScSmooth_iff_contDiffOn_const, Polyfold.isSc1_iff_contDiffOn_of_isRelOpenInQuadrant,
  Polyfold.isScSmooth_iff_contDiffOn_of_isRelOpenInQuadrant,
  Polyfold.isSc1_iff_contDiffOn_of_finiteDimensional]
#rt_check RoundTrip.V1_35.B_to_A_partial [Polyfold.ScBanach.lvlSet_const,
  Polyfold.isSc1_iff_contDiffOn_const, Polyfold.isSc1_iff_fderivWithin_const,
  Polyfold.isScSmooth_iff_contDiffOn_const, Polyfold.isSc1_iff_contDiffOn_of_isRelOpenInQuadrant,
  Polyfold.isScSmooth_iff_contDiffOn_of_isRelOpenInQuadrant,
  Polyfold.isSc1_iff_contDiffOn_of_finiteDimensional]
#rt_overlap RoundTrip.V1_35.A_to_B [Polyfold.ScBanach.lvlSet_const,
  Polyfold.isSc1_iff_contDiffOn_const, Polyfold.isSc1_iff_fderivWithin_const,
  Polyfold.isScSmooth_iff_contDiffOn_const, Polyfold.isSc1_iff_contDiffOn_of_isRelOpenInQuadrant,
  Polyfold.isScSmooth_iff_contDiffOn_of_isRelOpenInQuadrant,
  Polyfold.isSc1_iff_contDiffOn_of_finiteDimensional]
#rt_overlap RoundTrip.V1_35.B_to_A_partial [Polyfold.ScBanach.lvlSet_const,
  Polyfold.isSc1_iff_contDiffOn_const, Polyfold.isSc1_iff_fderivWithin_const,
  Polyfold.isScSmooth_iff_contDiffOn_const, Polyfold.isSc1_iff_contDiffOn_of_isRelOpenInQuadrant,
  Polyfold.isScSmooth_iff_contDiffOn_of_isRelOpenInQuadrant,
  Polyfold.isSc1_iff_contDiffOn_of_finiteDimensional]

end RoundTrip.V1_35
