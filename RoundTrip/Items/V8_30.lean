import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_30

/-! Round trip for V8_30 (Theorem 8.5 of the 2017 text, 2021: Theorem 8.5.3, Proper Covering I).

`A` is the conjunction of the types of the six listed theorems, universes at `0`:
`ProperCoveringLocal.exists_data`, `ProperCoveringLocal.isScSmoothOn_of_section`,
`EpFunctor.theorem_8_5_3` (a chart with `U(x)` inside any open `V ∋ x`),
`EpFunctor.theorem_8_5_3_of_naturalRep` (one open `W ∋ x` such that every natural representation on
a connected `U(x) ⊆ W` is the `R` of a chart), `CoveringExamples.theorem_8_5_3_five_as_printed`
(for `𝟭` on `ℤ/2 ⋉ ℝ` every chart at `0` has a `ψ ∈ 𝐔(−1, 0)` with `F(s ψ) ≠ t(F ψ)`) and
`..._nonvacuous` (such charts exist).  `ProperCoveringChart`, `ProperCoveringLocal.Data`,
`Data.toChart` are definitions.  The chart's (5) is the square with `s` on both sides
(`comm_src`) plus the `t` companion (`comm_tgt`); the printed (5), right arrow `t`, is flagged as a
possible misprint.

* `B` formalizes (5) literally (`t ∘ F = F ∘ s` on `𝐔(ψ₀)`) and, as its author says, is **false**:
  `not_B`, on `𝟭 : ℤ/2 ⋉ ℝ → ℤ/2 ⋉ ℝ` at `x = 0`, `ψ₀ = (−1, 0)`: any open `𝐔(ψ₀) ∋ ψ₀` contains
  `(−1, y)`, `y ≠ 0`, with `t(F(−1, y)) = −y ≠ y = F(s(−1, y))` (the argument of the project's
  `theorem_8_5_3_five_as_printed`, re-done here).  Hence `A → B` is false (`not_A_to_B`) and
  `B → A` holds only ex falso.
* `BRepaired`: `B` with (5)'s right arrow `s` instead of `t` (`s : 𝐔(F ψ₀) → U(x)` an
  sc-diffeomorphism and `s ∘ F = F ∘ s` on `𝐔(ψ₀)`), the first of the author's two suggested
  readings, and the project's `comm_src`.  `A_to_BRepaired` and `BRepaired_to_A` are both proved.
  - `A → BRepaired`: `theorem_8_5_3_of_naturalRep` (the "for every sufficiently small `U(x)`"
    reading, `B`'s) applied to the natural representation built from `B`'s action (`toRep`: `U`
    connected, inverse `Φ(g⁻¹)`); every clause is a chart field.
  - `BRepaired → A`: `theorem_8_5_3_of_naturalRep` from `BRepaired`: the chart's fields are
    `BRepaired`'s clauses except three, proved here: `connectedComponentIn_eq` (Chapter 7),
    disjointness of the `𝐔(ψ₀)` over **all** morphisms between points of `F⁻¹(x)` (`B` has it per
    `mor(y, y')`; the rest from (2) and the disjointness of the `U(y)`), and the companion square
    (`comm_tgt` by functoriality, `t : 𝐔(F ψ₀) → U(x)` from (1) at `g = F(ψ₀)`).  `theorem_8_5_3`
    follows with Chapter 7's `theorem_7_1_13`, `..._nonvacuous` from that for `𝟭`.  `exists_data`,
    `isScSmoothOn_of_section` (lemmas of the proof) and `theorem_8_5_3_five_as_printed` (a statement
    about every chart of one example) are re-proved outright. -/

namespace RoundTrip.V8_30
open Polyfold Set
open Polyfold.EpGroupoid.Examples Polyfold.CoveringExamples

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.ProperCoveringLocal.exists_data.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.ProperCoveringLocal.isScSmoothOn_of_section.{0}) ∧
  (type_of% @Polyfold.EpFunctor.theorem_8_5_3.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.theorem_8_5_3_of_naturalRep.{0, 0}) ∧
  (type_of% @Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed) ∧
  (type_of% @Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed_nonvacuous)

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.ProperCoveringLocal.exists_data.{0, 0},
    @Polyfold.EpFunctor.ProperCoveringLocal.isScSmoothOn_of_section.{0},
    @Polyfold.EpFunctor.theorem_8_5_3.{0, 0}, @Polyfold.EpFunctor.theorem_8_5_3_of_naturalRep.{0, 0},
    @Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed,
    @Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed_nonvacuous⟩

/-! ### Glue: natural actions and natural representations -/

section Glue
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor} {x : Obj}
  {U : Set Obj} {Φ : X.Isotropy x → Obj → Obj} {Γ : X.Isotropy x → Obj → Mor}

theorem Φ_one_of (h : IsNatAction X x U Φ Γ) : ∀ y ∈ U, Φ 1 y = y := fun y hy => by
  obtain ⟨ψ, hψ⟩ := h.diffeo 1
  have h1 : Φ 1 y = Φ 1 (Φ 1 y) := by rw [← h.hom 1 1 y hy, mul_one]
  calc Φ 1 y = ψ (Φ 1 (Φ 1 y)) := (hψ.left_inv _ (hψ.mapsTo hy)).symm
    _ = ψ (Φ 1 y) := by rw [← h1]
    _ = y := hψ.left_inv y hy

/-- A natural action on a connected `U` is a natural representation (inverse `Φ(g⁻¹)`). -/
def toRep (h : IsNatAction X x U Φ Γ) (hc : IsConnected U) : X.NaturalRep x where
  U := U
  isOpen_U := h.isOpen
  isConnected_U := hc
  mem_U := h.mem
  Φ := Φ
  Γ := Γ
  isScDiffeoOn_Φ g := by
    obtain ⟨ψ, hψ⟩ := h.diffeo g
    obtain ⟨ψ', hψ'⟩ := h.diffeo g⁻¹
    exact ⟨hψ.isScSmoothOn, hψ'.isScSmoothOn, hψ.mapsTo, hψ'.mapsTo,
      fun y hy => by rw [← h.hom _ _ y hy, inv_mul_cancel, Φ_one_of h y hy],
      fun y hy => by rw [← h.hom _ _ y hy, mul_inv_cancel, Φ_one_of h y hy]⟩
  Φ_mul := h.hom
  isScSmoothOn_Γ := h.smooth
  Γ_self := h.Γ_x
  src_Γ g y hy := (h.src_tgt g y hy).1
  tgt_Γ g y hy := (h.src_tgt g y hy).2
  existsUnique_Γ := h.unique

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

end Glue

/-! ### `B` is false -/

/-- In `ℤ/2 ⋉ ℝ`, every open set containing `(−1, 0)` contains some `(−1, y)` with
`(−1) • y ≠ y`. -/
theorem exists_reflection_ne {S : Set (ℤˣ × (Fin 1 → ℝ))} (hS : IsOpen S)
    (h0 : ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) ∈ S) :
    ∃ y : Fin 1 → ℝ, ((-1 : ℤˣ), y) ∈ S ∧ (-1 : ℤˣ) • y ≠ y := by
  have ho : IsOpen ((fun y : Fin 1 → ℝ => ((-1 : ℤˣ), y)) ⁻¹' S) :=
    hS.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho 0 h0
  set y : Fin 1 → ℝ := fun _ => ε / 2 with hy
  have hyb : y ∈ Metric.ball (0 : Fin 1 → ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, pi_norm_const, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  refine ⟨y, hball hyb, ?_⟩
  rw [units_smul_rn_neg_one]
  intro h
  have h1 := congrFun h 0
  simp only [hy, Pi.neg_apply] at h1
  linarith

theorem not_B : ¬ B := by
  intro hB
  obtain ⟨V, hVo, h0V, hV⟩ := hB _ _ _ _ reflectionEpGroupoid reflectionEpGroupoid
    (EpFunctor.id reflectionEpGroupoid) EpFunctor.isProperCovering_id 0
  obtain ⟨R, hRV⟩ := reflectionEpGroupoid.theorem_7_1_13 0 hVo h0V
  obtain ⟨-, Uy, UY, -, h2, h345⟩ :=
    hV R.U R.Φ R.Γ (isNatAction_of_rep R) R.isConnected_U hRV
  have hm : reflectionψ₀ ∈
      morOnB reflectionEpGroupoid.toGroupoidStr ((EpFunctor.id reflectionEpGroupoid).obj ⁻¹' {0}) :=
    reflectionψ₀_mem_morOn
  obtain ⟨hUo, -, hψ₀⟩ := (h2 _ hm.1 _ hm.2).2.2 reflectionψ₀ ⟨rfl, rfl⟩
  have hcomm := (h345 reflectionψ₀ hm).2.2.2.2.2
  obtain ⟨y, hyS, hne⟩ := exists_reflection_ne hUo hψ₀
  exact hne (hcomm _ hyS)

theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B → A` only ex falso. -/
theorem B_to_A : B → A := fun h => absurd h not_B

/-! ### The repaired statement: (5) with the right arrow `s` -/

section
variable {ObjY MorY ObjX MorX : Type}
  [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}

/-- `B`'s `Cond345` with (5)'s right arrow `s : 𝐔(F(ψ₀)) → U(s(F(ψ₀))) = U(x)` instead of `t`, so
that the square reads `s ∘ F = F ∘ s`. -/
def Cond345R (F : EpFunctor Y X) (x : ObjX) (U : Set ObjX) (Uy : ObjY → Set ObjY)
    (UY : MorY → Set MorY) : Prop :=
  ∀ ψ₀ ∈ morOnB Y.toGroupoidStr (F.obj ⁻¹' {x}),
    (∃ σ : ObjY → MorY, Y.PMor.IsScDiffeoOn Y.PObj Y.src σ (UY ψ₀) (Uy (Y.src ψ₀))) ∧
    (∃ τ : ObjY → MorY, Y.PMor.IsScDiffeoOn Y.PObj Y.tgt τ (UY ψ₀) (Uy (Y.tgt ψ₀))) ∧
    (∃ σ : MorX → MorY,
      Y.PMor.IsScDiffeoOn X.PMor F.mor σ (UY ψ₀) (compB X.toGroupoidStr U (F.mor ψ₀))) ∧
    (∃ τ : ObjX → MorX,
      X.PMor.IsScDiffeoOn X.PObj X.src τ (compB X.toGroupoidStr U (F.mor ψ₀)) U) ∧
    (∃ σ : ObjX → ObjY, Y.PObj.IsScDiffeoOn X.PObj F.obj σ (Uy (Y.src ψ₀)) U) ∧
    (∀ ψ ∈ UY ψ₀, X.src (F.mor ψ) = F.obj (Y.src ψ))

end

/-- `B` with (5) repaired (`Cond345R`). -/
def BRepaired : Prop :=
  ∀ (ObjY MorY ObjX MorX : Type)
    [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX) (F : EpFunctor Y X),
    F.IsProperCovering → ∀ x : ObjX,
      ∃ V : Set ObjX, IsOpen V ∧ x ∈ V ∧
        ∀ (U : Set ObjX) (Φ : X.Isotropy x → ObjX → ObjX) (Γ : X.Isotropy x → ObjX → MorX),
          IsNatAction X x U Φ Γ → IsConnected U → U ⊆ V →
            Cond1 X x U Γ ∧
            ∃ (Uy : ObjY → Set ObjY) (UY : MorY → Set MorY),
              Cond0 F x U Uy ∧ Cond2 F x Uy UY ∧ Cond345R F x U Uy UY

/-- The clauses of `BRepaired` for a chart. -/
theorem chart_clauses {ObjY MorY ObjX MorX : Type}
    [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX} {F : EpFunctor Y X} {x : ObjX}
    (C : F.ProperCoveringChart x) :
    Cond1 X x C.R.U C.R.Γ ∧ Cond0 F x C.R.U C.U ∧ Cond2 F x C.U C.sheet ∧
      Cond345R F x C.R.U C.U C.sheet := by
  have hsub : ∀ y ∈ F.obj ⁻¹' {x}, ∀ y' ∈ F.obj ⁻¹' {x},
      morB Y.toGroupoidStr y y' ⊆ Y.morOn (F.obj ⁻¹' {x}) := fun y hy y' hy' ψ hψ =>
    ⟨by rw [hψ.1]; exact hy, by rw [hψ.2]; exact hy'⟩
  refine ⟨⟨C.image_Γ, C.iUnion_sheetX, C.pairwise_disjoint_sheetX,
      fun g => ⟨C.isScDiffeoOn_src_sheetX g, C.isScDiffeoOn_tgt_sheetX g⟩⟩,
    ⟨fun y hy => ⟨C.isOpen_U y hy, C.isConnected_U y hy, C.mem_U y hy, C.isScDiffeoOn_obj y hy⟩,
      C.pairwiseDisjoint_U, C.preimage_eq⟩,
    fun y hy y' hy' => ⟨C.morOn_U_eq y hy y' hy', C.pairwiseDisjoint_sheet.subset (hsub y hy y' hy'),
      fun ψ₀ hψ₀ => ⟨C.isOpen_sheet ψ₀ (hsub y hy y' hy' hψ₀),
        C.isConnected_sheet ψ₀ (hsub y hy y' hy' hψ₀), C.mem_sheet ψ₀ (hsub y hy y' hy' hψ₀)⟩⟩,
    fun ψ₀ hψ₀ => ⟨C.isScDiffeoOn_src ψ₀ hψ₀, C.isScDiffeoOn_tgt ψ₀ hψ₀, C.isScDiffeoOn_mor ψ₀ hψ₀,
      C.isScDiffeoOn_src_sheetF ψ₀ hψ₀, C.isScDiffeoOn_obj _ hψ₀.1,
      fun ψ hψ => (C.comm_src ψ₀ hψ₀ ψ hψ).symm⟩⟩

theorem A_to_BRepaired : A → BRepaired := by
  intro hA ObjY MorY ObjX MorX _ _ _ _ _ _ _ _ _ _ _ _ Y X F hF x
  obtain ⟨W, hWo, hxW, hW⟩ := hA.2.2.2.1 hF x
  refine ⟨W, hWo, hxW, fun U Φ Γ h hc hUW => ?_⟩
  obtain ⟨C, hC⟩ := hW (toRep h hc) hUW
  have hU : C.R.U = U := by rw [hC]; rfl
  have hΓ : C.R.Γ = Γ := by rw [hC]; rfl
  obtain ⟨h1, h0, h2, h345⟩ := chart_clauses C
  rw [hU, hΓ] at h1
  rw [hU] at h0 h345
  exact ⟨h1, C.U, C.sheet, h0, h2, h345⟩

/-- `theorem_8_5_3_of_naturalRep` from `BRepaired`. -/
theorem naturalRep_of_BRepaired (hR : BRepaired) {ObjY MorY ObjX MorX : Type}
    [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX} {F : EpFunctor Y X}
    (hF : F.IsProperCovering) (x : ObjX) :
    ∃ W : Set ObjX, IsOpen W ∧ x ∈ W ∧
      ∀ R : X.NaturalRep x, R.U ⊆ W → ∃ C : F.ProperCoveringChart x, C.R = R := by
  obtain ⟨V, hVo, hxV, hV⟩ := hR ObjY MorY ObjX MorX Y X F hF x
  refine ⟨V, hVo, hxV, fun R hRV => ?_⟩
  obtain ⟨⟨hi, hu, hd, hst⟩, Uy, UY, ⟨h0a, h0d, h0p⟩, h2, h345⟩ :=
    hV R.U R.Φ R.Γ (isNatAction_of_rep R) R.isConnected_U hRV
  -- the pieces of (2) at `ψ₀`
  have h2' : ∀ ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}),
      IsOpen (UY ψ₀) ∧ IsConnected (UY ψ₀) ∧ ψ₀ ∈ UY ψ₀ := fun ψ₀ hψ₀ =>
    (h2 _ hψ₀.1 _ hψ₀.2).2.2 ψ₀ ⟨rfl, rfl⟩
  -- `𝐔(ψ₀) ⊆ 𝐔(s ψ₀, t ψ₀)`
  have hin : ∀ ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}), ∀ ψ ∈ UY ψ₀,
      Y.src ψ ∈ Uy (Y.src ψ₀) ∧ Y.tgt ψ ∈ Uy (Y.tgt ψ₀) := fun ψ₀ hψ₀ ψ hψ => by
    have h := (h2 _ hψ₀.1 _ hψ₀.2).1
    have : ψ ∈ ⋃ ψ₁ ∈ morB Y.toGroupoidStr (Y.src ψ₀) (Y.tgt ψ₀), UY ψ₁ :=
      mem_iUnion₂.2 ⟨ψ₀, ⟨rfl, rfl⟩, hψ⟩
    rw [← h] at this
    exact this
  -- the `𝐔(ψ₀)` are disjoint over all morphisms between points of `F⁻¹(x)`
  have hdisj : (Y.morOn (F.obj ⁻¹' {x})).PairwiseDisjoint UY := by
    intro ψ₀ hψ₀ ψ₁ hψ₁ hne
    rw [Function.onFun, Set.disjoint_left]
    intro ψ hψ0 hψ1
    have e₀ := hin ψ₀ hψ₀ ψ hψ0
    have e₁ := hin ψ₁ hψ₁ ψ hψ1
    have hs : Y.src ψ₀ = Y.src ψ₁ := by
      by_contra hne'
      exact Set.disjoint_left.1 (h0d hψ₀.1 hψ₁.1 hne') e₀.1 e₁.1
    have ht : Y.tgt ψ₀ = Y.tgt ψ₁ := by
      by_contra hne'
      exact Set.disjoint_left.1 (h0d hψ₀.2 hψ₁.2 hne') e₀.2 e₁.2
    exact Set.disjoint_left.1 ((h2 _ hψ₀.1 _ hψ₀.2).2.1 ⟨rfl, rfl⟩ ⟨hs.symm, ht.symm⟩ hne) hψ0 hψ1
  -- `F(ψ₀) ∈ G_x`
  let gF : ∀ ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}), X.Isotropy x := fun ψ₀ hψ₀ =>
    ⟨F.mor ψ₀, (F.src_mor ψ₀).trans hψ₀.1, (F.tgt_mor ψ₀).trans hψ₀.2⟩
  exact ⟨{
    R := R
    U := Uy
    sheet := UY
    isOpen_U := fun y hy => (h0a y hy).1
    isConnected_U := fun y hy => (h0a y hy).2.1
    mem_U := fun y hy => (h0a y hy).2.2.1
    pairwiseDisjoint_U := h0d
    preimage_eq := h0p
    isScDiffeoOn_obj := fun y hy => (h0a y hy).2.2.2
    image_Γ := hi
    iUnion_sheetX := hu
    pairwise_disjoint_sheetX := hd
    connectedComponentIn_eq := fun g => R.connectedComponentIn_morOn ⟨x, R.mem_U, R.Γ_self g⟩
    isScDiffeoOn_src_sheetX := fun g => (hst g).1
    isScDiffeoOn_tgt_sheetX := fun g => (hst g).2
    isOpen_sheet := fun ψ₀ hψ₀ => (h2' ψ₀ hψ₀).1
    isConnected_sheet := fun ψ₀ hψ₀ => (h2' ψ₀ hψ₀).2.1
    mem_sheet := fun ψ₀ hψ₀ => (h2' ψ₀ hψ₀).2.2
    pairwiseDisjoint_sheet := hdisj
    morOn_U_eq := fun y hy y' hy' => (h2 y hy y' hy').1
    isScDiffeoOn_src := fun ψ₀ hψ₀ => (h345 ψ₀ hψ₀).1
    isScDiffeoOn_tgt := fun ψ₀ hψ₀ => (h345 ψ₀ hψ₀).2.1
    isScDiffeoOn_mor := fun ψ₀ hψ₀ => (h345 ψ₀ hψ₀).2.2.1
    comm_src := fun ψ₀ hψ₀ ψ hψ => ((h345 ψ₀ hψ₀).2.2.2.2.2 ψ hψ).symm
    isScDiffeoOn_src_sheetF := fun ψ₀ hψ₀ => (h345 ψ₀ hψ₀).2.2.2.1
    comm_tgt := fun _ _ ψ _ => (F.tgt_mor ψ).symm
    isScDiffeoOn_tgt_sheetF := fun ψ₀ hψ₀ => (hst (gF ψ₀ hψ₀)).2 }, rfl⟩

theorem BRepaired_to_A : BRepaired → A := by
  intro hR
  have h85 : ∀ {ObjY MorY ObjX MorX : Type}
      [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
      [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
      [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
      [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
      {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX} {F : EpFunctor Y X},
      F.IsProperCovering → ∀ (x : ObjX) {V : Set ObjX}, IsOpen V → x ∈ V →
        ∃ C : F.ProperCoveringChart x, C.R.U ⊆ V := by
    intro ObjY MorY ObjX MorX _ _ _ _ _ _ _ _ _ _ _ _ Y X F hF x V hV hx
    obtain ⟨W, hWo, hxW, hW⟩ := naturalRep_of_BRepaired hR hF x
    obtain ⟨R, hRs⟩ := X.theorem_7_1_13 x (hV.inter hWo) ⟨hx, hxW⟩
    obtain ⟨C, rfl⟩ := hW R fun z hz => (hRs hz).2
    exact ⟨C, fun z hz => (hRs hz).1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `exists_data`, outright (from Definition 8.8 (2), (3))
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x
    obtain ⟨U₀, V₀, σ, hU₀o, hxU₀, hdisj, hV₀, hpre⟩ := hF.evenlyCovered x
    let := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
    let := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
    obtain ⟨Linv, hL⟩ := hF.isScDiffeo_fibredMap
    exact ⟨U₀, hU₀o, hxU₀, fun R hR => ⟨
      { R := R
        U₀ := U₀
        V₀ := V₀
        σ := σ
        Linv := Linv
        R_subset := hR
        pairwiseDisjoint_V₀ := hdisj
        mem_V₀ := fun y hy => (hV₀ y hy).1
        isScDiffeoOn_σ := fun y hy => (hV₀ y hy).2
        preimage_U₀ := hpre
        continuous_Linv := continuousOn_univ.1 hL.isScSmoothOn_inv.continuousOn
        Linv_fibredMap := fun ψ => hL.left_inv ψ (mem_univ _)
        fibredMap_Linv := fun p => hL.right_inv p (mem_univ _) }, rfl⟩⟩
  · -- `isScSmoothOn_of_section`, outright
    intro Obj Mor _ _ _ _ _ _ X U hU τ hτ hsec
    refine MPolyfold.IsScSmoothOn.of_locally hU fun z hz => ?_
    obtain ⟨W, W', h, hW, hd⟩ := X.isLocalScDiffeo_src (τ z)
    have hN : IsOpen (U ∩ τ ⁻¹' W ∩ W') :=
      (hτ.isOpen_inter_preimage hU hd.isOpen_source).inter hd.isOpen_target
    refine ⟨U ∩ τ ⁻¹' W ∩ W', hN, ⟨⟨hz, hW⟩, ?_⟩, fun w hw => hw.1.1, ?_⟩
    · rw [← hsec z hz]
      exact hd.mapsTo hW
    · refine (hd.isScSmoothOn_inv.mono hN inter_subset_right).congr fun w hw => ?_
      have h1 := hd.left_inv (τ w) hw.1.2
      rwa [hsec w hw.1.1] at h1
  · -- `theorem_8_5_3`, from `BRepaired`
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x V hV hx
    exact h85 hF x hV hx
  · -- `theorem_8_5_3_of_naturalRep`, from `BRepaired`
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x
    exact naturalRep_of_BRepaired hR hF x
  · -- `theorem_8_5_3_five_as_printed`, outright (a statement about every chart of one example)
    intro C
    have hm := reflectionψ₀_mem_morOn
    obtain ⟨y, hyS, hne⟩ := exists_reflection_ne (C.isOpen_sheet _ hm) (C.mem_sheet _ hm)
    exact ⟨_, hyS, fun h => hne h.symm⟩
  · -- `..._nonvacuous`, from the `theorem_8_5_3` derived from `BRepaired`
    obtain ⟨C, -⟩ := h85 (EpFunctor.isProperCovering_id (X := reflectionEpGroupoid)) 0
      isOpen_univ (mem_univ _)
    exact ⟨C⟩

#rt_check RoundTrip.V8_30.not_B [Polyfold.EpFunctor.ProperCoveringLocal.exists_data,
  Polyfold.EpFunctor.ProperCoveringLocal.isScSmoothOn_of_section, Polyfold.EpFunctor.theorem_8_5_3,
  Polyfold.EpFunctor.theorem_8_5_3_of_naturalRep,
  Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed,
  Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed_nonvacuous]
#rt_check RoundTrip.V8_30.B_to_A [Polyfold.EpFunctor.ProperCoveringLocal.exists_data,
  Polyfold.EpFunctor.ProperCoveringLocal.isScSmoothOn_of_section, Polyfold.EpFunctor.theorem_8_5_3,
  Polyfold.EpFunctor.theorem_8_5_3_of_naturalRep,
  Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed,
  Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed_nonvacuous]
#rt_check RoundTrip.V8_30.A_to_BRepaired [Polyfold.EpFunctor.ProperCoveringLocal.exists_data,
  Polyfold.EpFunctor.ProperCoveringLocal.isScSmoothOn_of_section, Polyfold.EpFunctor.theorem_8_5_3,
  Polyfold.EpFunctor.theorem_8_5_3_of_naturalRep,
  Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed,
  Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed_nonvacuous]
#rt_check RoundTrip.V8_30.BRepaired_to_A [Polyfold.EpFunctor.ProperCoveringLocal.exists_data,
  Polyfold.EpFunctor.ProperCoveringLocal.isScSmoothOn_of_section, Polyfold.EpFunctor.theorem_8_5_3,
  Polyfold.EpFunctor.theorem_8_5_3_of_naturalRep,
  Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed,
  Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed_nonvacuous]
#rt_overlap RoundTrip.V8_30.B_to_A [Polyfold.EpFunctor.ProperCoveringLocal.exists_data,
  Polyfold.EpFunctor.ProperCoveringLocal.isScSmoothOn_of_section, Polyfold.EpFunctor.theorem_8_5_3,
  Polyfold.EpFunctor.theorem_8_5_3_of_naturalRep,
  Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed,
  Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed_nonvacuous]
#rt_overlap RoundTrip.V8_30.BRepaired_to_A [Polyfold.EpFunctor.ProperCoveringLocal.exists_data,
  Polyfold.EpFunctor.ProperCoveringLocal.isScSmoothOn_of_section, Polyfold.EpFunctor.theorem_8_5_3,
  Polyfold.EpFunctor.theorem_8_5_3_of_naturalRep,
  Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed,
  Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed_nonvacuous]

end RoundTrip.V8_30
