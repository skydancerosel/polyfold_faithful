import Polyfold.Chapter3.LinearizationIntrinsic
import Polyfold.Chapter3.BookFormIFT2021
import Polyfold.Chapter5.GeneralPosition
import Polyfold.Chapter2.BookFormTameSub2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Theorem 3.1.22**
(preprint 3.19), p. 100: the last clause `ker f'(y) = T_yS(f, U)`, stated intrinsically.

# `ker f'(y) = T_yS` in `T_yX`

`theorem_3_1_22_book` states Theorem 3.1.22 except for its last clause, which the project had only
in a chart (`theorem_3_6_8_ker_eq_tangent`, `exists_tangentSpace_eq_linKer`).  With the intrinsic
`f'(y) : T_yX → Y_y` (`StrongBundle.linIntr`, chart independent by
`StrongBundle.linIntr_chart_independent`) and `T_yS ⊆ T_yX` read as the image of
`Ti : T_yS → T_yX` (`MPolyfold.subTangentRange`, as in Definition 2.5.19 in book form), the clause
is an equality of subspaces of `T_yX`:

* `StrongBundle.coe_map_ker_linIntr`: `Tφ(ker f'(y)) = ker Lin(z)` in the chart;
* `StrongBundle.ker_linIntr_eq_subTangentRange`: if every zero in an open `U` is in good position
  (tame germ reading) and `S(f, U)` is a sub-M-polyfold, then `ker f'(y) = Ti(T_yS(f, U))` at every
  `y ∈ S(f, U)` on level `1`, through any strong bundle chart;
* **`theorem_3_1_22_book_ker`**: `theorem_3_1_22_book` (b) with the last clause added.
-/

open Set Function Module

noncomputable section

namespace Polyfold

universe u v

open StrongRetr MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

omit [T2Space Y] [ParacompactSpace Y] in
/-- `T_zO` is the range of `D(r)(z)`, for the level-`1` point `z` over a point of the chart. -/
lemma StrongBundleChart.mem_tangentFiberModel_iff_rangeS (c : StrongBundleChart PX P)
    {x : PX.Level 1} (hx : PX.levelVal 1 x ∈ c.φ.source) (w : c.φ.model.E 0) :
    w ∈ tangentFiberModel c.isChart hx ↔
      w ∈ rangeS (scDeriv c.U (r c.R) (levelLift c.φ 1 (PX.levelVal 1 x))) := by
  have ha : c.φ.model.E.toBase 1 (levelLift c.φ 1 (PX.levelVal 1 x)) =
      c.φ (PX.levelVal 1 x) := PX.toBase_levelLift c.isChart hx (levelVal_mem x)
  have hzO : levelLift c.φ 1 (PX.levelVal 1 x) ∈
      c.φ.model.E.lvlSet (c.isRetraction.baseRetraction c.relOpen).retract 1 := by
    rw [ScBanach.mem_lvlSet, c.base_retract, ha]; exact c.φ.mapsTo_model _ hx
  have h := tangentSpace_eq_coe_submodule (c.isRetraction.baseRetraction c.relOpen) hzO
  rw [c.base_retract] at h
  change w ∈ tangentSpace c.φ.model.E c.φ.model.C c.φ.model.O _ ↔ _
  rw [h]
  rfl

/-- **`Tφ(ker f'(y)) = ker Lin(z)`**: the chart image of the kernel of the intrinsic linearization
is the kernel of `Lin(z) : T_zO → F` at the level-`1` point `z` over `φ(y)`. -/
theorem StrongBundle.coe_map_ker_linIntr (hf : B.IsScSmoothSection f)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) {x : PX.Level 1}
    (hx : PX.levelVal 1 x ∈ c.φ.source) (h0 : IsZeroAt P f (PX.levelVal 1 x)) :
    ((LinearMap.ker (B.linIntr hf hc hx h0)).map (fiberCoord c.isChart hx) : Set (c.φ.model.E 0)) =
      c.linKer f (levelLift c.φ 1 (PX.levelVal 1 x)) := by
  ext v
  simp only [SetLike.mem_coe, Submodule.mem_map, LinearMap.mem_ker]
  constructor
  · rintro ⟨α, hα, rfl⟩
    have hT := (c.mem_tangentFiberModel_iff_rangeS hx _).1 (tangentFiberEquiv c.isChart hx α).2
    refine (c.mem_linKer_iff f _ _).2 ⟨hT, ?_⟩
    rw [linAt_apply]
    have h := B.fiberLin_linIntr hf hc hx h0 α
    rw [hα, map_zero, StrongBundleChart.linChart_apply] at h
    exact h.symm
  · intro hv
    obtain ⟨hvr, hv0⟩ := (c.mem_linKer_iff f _ _).1 hv
    have hvT : v ∈ tangentFiberModel c.isChart hx := (c.mem_tangentFiberModel_iff_rangeS hx v).2 hvr
    set α := (tangentFiberLinearEquiv c.isChart hx).symm ⟨v, hvT⟩
    have hαv : fiberCoord c.isChart hx α = v := by
      change ((tangentFiberLinearEquiv c.isChart hx α : tangentFiberModel c.isChart hx) :
        c.φ.model.E 0) = v
      rw [LinearEquiv.apply_symm_apply]
    refine ⟨α, c.fiberLin_injective hx ?_, hαv⟩
    rw [B.fiberLin_linIntr hf hc hx h0 α, map_zero, StrongBundleChart.linChart_apply,
      ← fiberCoord_eq_coe, hαv]
    rw [linAt_apply] at hv0
    exact hv0

/-- **"`ker f'(y) = T_yS`", intrinsically** (Theorem 3.1.22 (preprint 3.19), last clause): if every
zero in an open `U` is in good position (tame germ reading) and `S = S(f, U)` is a sub-M-polyfold,
then at every `y ∈ S` on level `1` (`a ∈ S₁` over `x ∈ X₁`), the kernel of the intrinsic
linearization `f'(y) : T_yX → Y_y`, through any strong bundle chart, is `Ti(T_aS) ⊆ T_yX`. -/
theorem StrongBundle.ker_linIntr_eq_subTangentRange (hf : B.IsScFredholmSectionTame f)
    {U : Set X} (hU : IsOpen U) (hgp : ∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermTame f y)
    (hY : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y})
    [ParacompactSpace ↥{y ∈ U | IsZeroAt P f y}]
    {a : (subPolyfold hY).Level 1} {x : PX.Level 1}
    (hax : ((subPolyfold hY).levelVal 1 a : ↥{y ∈ U | IsZeroAt P f y}).1 = PX.levelVal 1 x)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hx : PX.levelVal 1 x ∈ c.φ.source)
    (h0 : IsZeroAt P f (PX.levelVal 1 x)) :
    LinearMap.ker (B.linIntr hf.isScSmooth hc hx h0) = subTangentRange hY hax := by
  set A := {y ∈ U | IsZeroAt P f y} with hA
  set y := PX.levelVal 1 x with hydef
  have hyA : y ∈ A := hax ▸ ((subPolyfold hY).levelVal 1 a).2
  -- the chart statement at `y`
  obtain ⟨V, hVo, hyV, -, hV⟩ := exists_tangentSpace_eq_linKer hf (hgp y hyA.1 h0) h0
  -- the sub-chart of `S` built on `φ`
  set d := hY.data hyA
  set a₀ : A := ⟨y, hyA⟩
  have ha : (subPolyfold hY).levelVal 1 a ∈ (subChart d c.isChart a₀).source := by
    rw [subChart_source]
    change ((subPolyfold hY).levelVal 1 a : A).1 ∈ d.shrink c.φ
    rw [hax]
    exact d.mem_shrink c.φ hyA (hY.mem_data_V hyA) hx
  have hmapT := coe_map_range_subInclusionCLM hY hax d c.isChart a₀ ha
  -- compare `φ(W ∩ S)` with `φ(G ∩ S(f, V))`, `G = W ∩ V ∩ U`
  set T := d.shrink c.φ ∩ A
  have hTs : T ⊆ c.φ.source := fun w hw => d.shrink_subset_source c.φ hw.1
  set s := (V ∩ U) ∩ c.φ.source
  have hso : IsOpen s := (hVo.inter hU).inter c.φ.isOpen_source
  obtain ⟨Wo, hWo, hWs⟩ := c.φ.exists_isOpen_image_eq (s := s) inter_subset_right hso
  set G := d.shrink c.φ ∩ V ∩ U
  have hGo : IsOpen G := ((d.isOpen_shrink c.φ).inter hVo).inter hU
  have hGs : G ⊆ c.φ.source := fun w hw => d.shrink_subset_source c.φ hw.1.1
  have hyG : y ∈ G := ⟨⟨d.mem_shrink c.φ hyA (hY.mem_data_V hyA) hx, hyV⟩, hyA.1⟩
  have hGS : G ∩ (solutionSet P f ∩ V) = T ∩ s := by
    ext w
    constructor
    · rintro ⟨⟨⟨hw1, hwV⟩, hwU⟩, hw0, -⟩
      exact ⟨⟨hw1, hwU, hw0⟩, ⟨hwV, hwU⟩, d.shrink_subset_source c.φ hw1⟩
    · rintro ⟨⟨hw1, hwU, hw0⟩, ⟨hwV, -⟩, -⟩
      exact ⟨⟨⟨hw1, hwV⟩, hwU⟩, hw0, hwV⟩
  have himg : c.φ '' (G ∩ (solutionSet P f ∩ V)) = c.φ '' T ∩ Wo := by
    have hTO : c.φ '' T ⊆ c.φ.model.O := by
      rintro _ ⟨t, ht, rfl⟩; exact c.φ.mapsTo_model t (hTs ht)
    rw [hGS, c.φ.toPartialEquiv.injOn.image_inter hTs inter_subset_right, hWs, ← inter_assoc,
      inter_eq_left.2 hTO]
  have hQT : IsScRetract c.φ.model.E c.φ.model.C (c.φ '' T) := d.isScRetract_image c.φ c.isChart
  have hQ : IsScRetract c.φ.model.E c.φ.model.C (c.φ '' (G ∩ (solutionSet P f ∩ V))) := by
    rw [himg]; exact proposition_2_3_1_one hQT hWo
  set z := levelLift c.φ 1 y
  have hz : c.φ.model.E.toBase 1 z = c.φ y := PX.toBase_levelLift c.isChart hx (levelVal_mem x)
  have hzT : c.φ.model.E.toBase 1 z ∈ c.φ '' T ∩ Wo := by
    rw [hz]
    refine ⟨⟨y, ⟨d.mem_shrink c.φ hyA (hY.mem_data_V hyA) hx, hyA⟩, rfl⟩, ?_⟩
    have : c.φ y ∈ c.φ '' s := ⟨y, ⟨⟨hyV, hyA.1⟩, hx⟩, rfl⟩
    rw [hWs] at this
    exact this.2
  have hker := hV y hyV h0 c hc hx G hGo hGs hyG hQ z hz
  rw [himg, tangentSpace_inter_isOpen hQT hWo hzT] at hker
  -- conclude by injectivity of `Tφ`
  have hinj : Injective (fiberCoord c.isChart hx) := fun α β h =>
    (tangentFiberLinearEquiv c.isChart hx).injective (Subtype.ext h)
  apply Submodule.map_injective_of_injective hinj
  apply SetLike.coe_injective
  rw [StrongBundle.coe_map_ker_linIntr hf.isScSmooth hc hx h0, ← hker]
  exact hmapT.symm

/-- **Theorem 3.1.22 (preprint 3.19), 2021 p. 100, part (b) with its last clause**, for the 2021
definitions: if `d_X ≡ 0`, `f` is an sc-Fredholm section with germ data in tame charts, `f(x₀) = 0`
and `f'(x₀)` is onto, there are an open `U ∋ x₀` and `d` such that every zero `y ∈ U` has `f'(y)`
onto and Fredholm of index `d` in every chart, `S(f, U)` is a sub-M-polyfold with the structure of a
`d`-dimensional manifold without boundary, and at every `y ∈ S(f, U)` on level `1`,
`ker f'(y) = T_yS(f, U)` in `T_yX`, for the intrinsic `f'(y)` (`StrongBundle.linIntr`, through
any strong bundle chart) and `T_yS(f, U)` the image of `Ti`. -/
theorem theorem_3_1_22_book_ker (hX : PX.IsWithoutBoundary)
    (hf : B.IsScFredholmSectionTame2021 f) {x₀ : X} (hx₀ : IsZeroAt P f x₀)
    (hsurj : B.IsLinSurjAt f x₀) :
    ∃ (U : Set X) (d : ℕ), IsOpen U ∧ x₀ ∈ U ∧
      (∀ y ∈ U, IsZeroAt P f y → B.IsSurjLinOfIndex f y d) ∧
      ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d ∧
          (MPolyfold.subPolyfold hsub).IsWithoutBoundary ∧
          ∀ (a : (subPolyfold hsub).Level 1) (x : PX.Level 1)
            (hax : ((subPolyfold hsub).levelVal 1 a : ↥{y ∈ U | IsZeroAt P f y}).1 =
              PX.levelVal 1 x)
            (c : StrongBundleChart PX P) (hc : B.IsChart c) (hx : PX.levelVal 1 x ∈ c.φ.source)
            (h0 : IsZeroAt P f (PX.levelVal 1 x)),
            LinearMap.ker (B.linIntr
              (StrongBundle.isScFredholmSectionTame2021_iff.1 hf).isScSmooth hc hx h0) =
              subTangentRange hsub hax := by
  have hf' := StrongBundle.isScFredholmSectionTame2021_iff.1 hf
  obtain ⟨U, d, hUo, hxU, hall, -, hsub, -, hman, hbd⟩ :=
    theorem_3_1_22_of_surjective hX hf' hx₀ hsurj
  refine ⟨U, d, hUo, hxU, fun y hy hy0 => (hall y hy hy0).2, hsub, hman, hbd,
    fun a x hax c hc hx h0 => ?_⟩
  have := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
  exact StrongBundle.ker_linIntr_eq_subTangentRange hf' hUo (fun y hy hy0 => (hall y hy hy0).1)
    hsub hax hc hx h0

end Polyfold
