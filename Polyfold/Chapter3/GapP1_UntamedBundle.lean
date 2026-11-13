import Polyfold.Chapter3.GapP1_UntamedCounterexample
import Polyfold.Chapter3.NonVacuityCorner
import Polyfold.Chapter3.GoodPositionGermG
import Polyfold.Chapter3.TangentGerm
import Polyfold.Chapter2.TameRetracts

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §3.6:
**Theorem 3.6.8** (p. 136; 2017: Theorem 3.13; preprint: Theorem 3.54) and **Definitions 3.6.3,
3.6.6** (pp. 135–136), for the untamed example of `GapP1_UntamedCounterexample.lean`.  Gap G.79.

# The untamed example as a strong bundle with a section

## The text, paraphrased

(Definition 2.6.5, p. 68) A strong bundle `P : Y → X` over an M-polyfold: a continuous surjection
with Banachable fibres and an equivalence class of strong bundle atlases.  (Definition 3.6.3,
p. 135) `(f, x)` is an sc-Fredholm germ if in a strong bundle chart around `x` the local section
has a filling `g` and an sc⁺-section `s`, `s(0) = g(0)`, with `g − s` conjugated to a basic germ.
(Definition 3.6.6, p. 136) Good position.  (Theorem 3.6.8, p. 136) near a zero in good position
the solution set is a sub-M-polyfold, a manifold with boundary with corners.

## What is formalized

The local model of `GapP1_UntamedCounterexample.lean` (`E = ℝ² ⊕ X`, `C = [0, ∞) × ℝ × X`,
`R(((a, t), w), (x, h)) = (((0, t), 0), (0, π_t h))`, `g((a, t), w) = (a + ν(w)², w + π_t v)`) as
a strong bundle over the M-polyfold `O = r(U) ≅ ℝ` (`polyO`):

* `Kt = R(U ◁ F)` (the total space, a subtype of `E₀ × F₀`), `kproj : Kt → O`, the fibre
  `kproj⁻¹(x) ≅ {h | h₁ = 0, π_t h₂ = h₂}` (`fibEquiv`), `chart0` (the strong bundle chart
  `Φ = id` onto `K`, over the chart of `polyO`, with the strong bundle retraction `R`) and
  `bundle : StrongBundle polyO kproj`.
* `sec x = (x, g(x))`: an sc-smooth section (`isScSmoothSection_sec`); every point of `O` is
  smooth (`smoothSet_polyO`); `isZeroAt_sec_iff`, `solutionSet_sec` (the zero set is the closed
  half-line `S`).
* `isScFredholmGerm2021_sec_zero`: **the germ of `sec` at `x₀ = 0` is an sc-Fredholm germ in the
  sense of 2021 Definition 3.6.3** (`StrongBundle.IsScFredholmGerm2021`), with the data of
  `theorem_3_6_8_untamed_local`; `isGoodPositionGerm_sec_zero`: it is in good position
  (`StrongBundle.IsGoodPositionGerm`, Definition 3.6.6 in the chart of the germ data);
  `subsingleton_fiber_zero`: the fibre over `x₀` is `0`, so `f'(x₀)` is onto in every reading.
* `not_exists_localRetraction`, `not_isSubMPolyfold_zeroSet`: for every open `W ∋ x₀` the set
  `{y ∈ W | f(y) = 0}` is not a sub-M-polyfold of `O`;
  `isEmpty_tangentGermChart`: the solution set has no tangent germ data (Definition 3.2.1 (2))
  at `x₀`, of any dimension.

The germ data at the other points, the tame strong bundle chart and the statements about Theorem
3.6.8 are in `GapP1_UntamedBundleFrame.lean`, `GapP1_UntamedBundleTame.lean` and
`GapP1_UntamedBundleTheorem.lean`.

## Choices

* The total space is the subtype `K ⊆ E₀ × F₀` with the induced topology; the fibre over `x` gets
  its vector space structure from the closed subspace `{h ∈ F₀ | h₁ = 0, π_t h₂ = h₂}` of `F₀`.
* The atlas of `bundle` consists of the one chart `chart0`, whose base retraction is not tame; the
  tame charts of `GapP1_UntamedBundleFrame.lean` and `GapP1_UntamedBundleTame.lean` are compatible
  with it.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace UntamedCorner

open ScOneExample Jump StrongRetr

/-! ### The total space `K = R(U ◁ F)` and the projection -/

/-- The base `O = r(U)`, as a type. -/
abbrev Ob : Type := ↥(r R '' U)

/-- The total space `K = R(U ◁ F)`, as a type. -/
abbrev Kt : Type := ↥(R '' (U ×ˢ (univ : Set (F 0))))

lemma mem_K {p : E 0 × F 0} :
    p ∈ R '' (U ×ˢ (univ : Set (F 0))) ↔
      p.1 ∈ r R '' U ∧ p.2.1 = 0 ∧ proj p.1.1.2 p.2.2 = p.2.2 := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [R_apply]
    exact ⟨mem_O.2 ⟨rfl, hq.1.2, rfl⟩, rfl, proj_proj hq.1.2 _⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨ha, ht, hw⟩ := mem_O.1 h1
    refine ⟨p, ⟨⟨ha.ge, ht⟩, mem_univ _⟩, ?_⟩
    rw [R_apply]
    exact Prod.ext (Prod.ext (Prod.ext ha.symm rfl) hw.symm) (Prod.ext h2.symm h3)

lemma zero_mem_K : (0 : E 0 × F 0) ∈ R '' (U ×ˢ (univ : Set (F 0))) :=
  mem_K.2 ⟨zero_mem_O, rfl, map_zero _⟩

/-- The projection `K → O`. -/
def kproj (y : Kt) : Ob := ⟨y.1.1, (mem_K.1 y.2).1⟩

lemma kproj_val (y : Kt) : ((kproj y : Ob) : E 0) = y.1.1 := rfl

/-- The fibre model over `t`: `{h ∈ F₀ | h₁ = 0, π_t h₂ = h₂}`. -/
def fib (t : ℝ) : Submodule ℝ (F 0) where
  carrier := {h | h.1 = 0 ∧ proj t h.2 = h.2}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · change a.1 + b.1 = 0
      rw [ha1, hb1, add_zero]
    · change proj t (a.2 + b.2) = a.2 + b.2
      rw [map_add, ha2, hb2]
  zero_mem' := ⟨rfl, map_zero _⟩
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩
    · change c • a.1 = 0
      rw [ha1, smul_zero]
    · change proj t (c • a.2) = c • a.2
      rw [map_smul, ha2]

lemma isClosed_fib (t : ℝ) : IsClosed (fib t : Set (F 0)) := by
  have h1 : IsClosed {h : F 0 | h.1 = 0} := isClosed_eq continuous_fst continuous_const
  have h2 : IsClosed {h : F 0 | proj t h.2 = h.2} :=
    isClosed_eq ((proj t).continuous.comp continuous_snd) continuous_snd
  exact h1.inter h2

instance (t : ℝ) : CompleteSpace (fib t) := (isClosed_fib t).completeSpace_coe

/-- The fibre `kproj⁻¹(x) ≃ fib t`. -/
def fibEquiv (x : Ob) : (kproj ⁻¹' {x}) ≃ fib (x : E 0).1.2 where
  toFun y := ⟨(y : Kt).1.2, by
    have hx : (y : Kt).1.1 = (x : E 0) := congrArg Subtype.val y.2
    obtain ⟨-, h2, h3⟩ := mem_K.1 (y : Kt).2
    rw [hx] at h3
    exact ⟨h2, h3⟩⟩
  invFun h := ⟨⟨((x : E 0), (h : F 0)), mem_K.2 ⟨x.2, h.2.1, h.2.2⟩⟩, rfl⟩
  left_inv y := by
    have hx : (y : Kt).1.1 = (x : E 0) := congrArg Subtype.val y.2
    exact Subtype.ext (Subtype.ext (Prod.ext hx.symm rfl))
  right_inv _ := rfl

instance (x : Ob) : AddCommGroup (kproj ⁻¹' {x}) := (fibEquiv x).addCommGroup

instance (x : Ob) : Module ℝ (kproj ⁻¹' {x}) := (fibEquiv x).module ℝ

lemma isLinearMap_fibEquiv (x : Ob) :
    IsLinearMap ℝ fun v : kproj ⁻¹' {x} => ((fibEquiv x v : fib (x : E 0).1.2) : F 0) :=
  ((fib (x : E 0).1.2).subtype.comp ((fibEquiv x).linearEquiv ℝ).toLinearMap).isLinear

/-! ### The strong bundle chart and the strong bundle -/

open scoped Classical in
/-- The bundle chart `Φ = id : K → K`. -/
def chartPE : PartialEquiv Kt (E 0 × F 0) where
  toFun y := y.1
  invFun p := if h : p ∈ R '' (U ×ˢ (univ : Set (F 0))) then ⟨p, h⟩ else ⟨0, zero_mem_K⟩
  source := univ
  target := R '' (U ×ˢ (univ : Set (F 0)))
  map_source' y _ := y.2
  map_target' _ _ := mem_univ _
  left_inv' y _ := by simp [y.2]
  right_inv' p hp := by simp [hp]

/-- The chart of `polyO`. -/
abbrev chartO : MChart Ob := modelO.selfChart ⟨0, zero_mem_O⟩

lemma isChart_chartO : polyO.IsChart chartO := polyO.isChart_of_mem (mem_singleton _)

/-- **The strong bundle chart of `K → O`**: over the chart of `polyO`, the strong bundle
retraction `R` on `U ◁ F` and `Φ = id`.  Its base retraction `r` is not tame. -/
def chart0 : StrongBundleChart polyO kproj where
  φ := chartO
  isChart := isChart_chartO
  F := F
  U := U
  R := R
  relOpen := relOpen_U
  isRetraction := isStrongBundleRetraction_R
  base_retract := rfl
  toPartialEquiv := chartPE
  source_eq := preimage_univ.symm
  target_eq := rfl
  continuousOn_toFun :=
    (show Continuous (fun y : Kt => (y : E 0 × F 0)) from continuous_subtype_val).continuousOn
  continuousOn_invFun := by
    classical
    refine continuousOn_iff_continuous_domRestrict.2 ?_
    have : (fun z : Kt => (if h : (z : E 0 × F 0) ∈ R '' (U ×ˢ (univ : Set (F 0))) then
        (⟨z, h⟩ : Kt) else ⟨0, zero_mem_K⟩)) = id := funext fun z => by simp [z.2]
    change Continuous (fun z : Kt => if h : (z : E 0 × F 0) ∈ R '' (U ×ˢ (univ : Set (F 0))) then
      (⟨z, h⟩ : Kt) else ⟨0, zero_mem_K⟩)
    rw [this]; exact continuous_id
  covers _ _ := rfl
  fiber_linear x _ := isLinearMap_fibEquiv x

lemma chart0_apply (y : Kt) : chart0 y = (y : E 0 × F 0) := rfl

/-- **The strong bundle `K → O`** over the M-polyfold `O ≅ ℝ`, with its one chart. -/
def bundle : StrongBundle polyO kproj where
  continuous := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  surjective x := ⟨⟨((x : E 0), 0), mem_K.2 ⟨x.2, rfl, map_zero _⟩⟩, rfl⟩
  banachable x := ⟨fib (x : E 0).1.2, inferInstance, inferInstance, inferInstance,
    ⟨{ toLinearEquiv := (fibEquiv x).linearEquiv ℝ
       continuous_toFun :=
        (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
       continuous_invFun :=
        ((continuous_const.prodMk continuous_subtype_val).subtype_mk _).subtype_mk _ }⟩⟩
  atlas :=
    { charts := {chart0}
      compatible := by
        rintro c hc c' hc'
        rw [mem_singleton_iff.1 hc, mem_singleton_iff.1 hc']
        exact StrongBundleChart.compatible_self _
      cover := fun _ => ⟨chart0, mem_singleton _, mem_univ _⟩ }

lemma isChart_chart0 : bundle.IsChart chart0 :=
  StrongBundle.isChart_of_mem (B := bundle) (mem_singleton _)

/-! ### Levels: every point of `O` is smooth -/

lemma val_mem_range_toBase (x : Ob) (m : ℕ) : (x : E 0) ∈ range (E.toBase m) := by
  obtain ⟨h1, -, h3⟩ := mem_O.1 x.2
  refine ⟨(((0, (x : E 0).1.2), 0) : E m), ?_⟩
  rw [E_toBase, map_zero]
  exact Prod.ext (Prod.ext h1.symm rfl) h3.symm

lemma levelSet_polyO (m : ℕ) : polyO.levelSet m = univ :=
  eq_univ_of_forall fun x =>
    (polyO.mem_levelSet_iff isChart_chartO (mem_univ x)).2 (val_mem_range_toBase x m)

/-- Every point of `O` is a smooth point. -/
lemma smoothSet_polyO : polyO.smoothSet = univ := by
  rw [MPolyfold.smoothSet]; exact iInter_eq_univ.2 levelSet_polyO

/-! ### The section `x ↦ (x, g(x))` -/

/-- **The section** `f(x) = (x, g(x))` of `K → O`. -/
def sec (x : Ob) : Kt := ⟨((x : E 0), g x), g_section x x.2⟩

lemma isSection_sec : IsSection kproj sec := fun _ => rfl

lemma chartO_symm (z : E 0) (hz : z ∈ r R '' U) : chartO.symm z = ⟨z, hz⟩ :=
  Subtype.ext (chartO.toPartialEquiv.right_inv (show z ∈ chartO.toPartialEquiv.target from hz))

/-- The principal part of `sec` in `chart0` is `g` on `O`. -/
lemma principal_sec {z : E 0} (hz : z ∈ r R '' U) : chart0.principal sec z = g z := by
  change g ((chartO.symm z : Ob) : E 0) = g z
  rw [chartO_symm z hz]

lemma continuous_g : Continuous g :=
  continuousOn_univ.1 isScSmooth_g_univ.isSc1.isSc0.continuousOn_base

/-- **`sec` is an sc-smooth section** (2021 Definition 2.6.6). -/
theorem isScSmoothSection_sec : bundle.IsScSmoothSection sec := by
  refine ⟨isSection_sec, MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ ?_ fun x _ => ?_⟩
  · exact ((continuous_subtype_val.prodMk
      (continuous_g.comp continuous_subtype_val)).subtype_mk _).continuousOn
  refine ⟨chartO, chart0.toMChart bundle.continuous, univ, isChart_chartO,
    bundle.isChart_toMChart (mem_singleton _), isOpen_univ, mem_univ x,
    fun _ _ => ⟨mem_univ _, mem_univ _⟩, fun _ _ => mem_univ _, ?_⟩
  have himg : chartO '' univ = r R '' U := by
    rw [image_univ]; exact Subtype.range_coe
  rw [himg]
  have heq : ∀ v ∈ r R '' U,
      (chart0.toMChart bundle.continuous ∘ sec ∘ chartO.symm) v = (v, g v) := by
    intro v hv
    change (((chartO.symm v : Ob) : E 0), g (chartO.symm v : Ob)) = (v, g v)
    rw [chartO_symm v hv]
  refine (isScSmoothRetractMap_iff_exists modelO.isScRetract).2
    ⟨fun v hv => ?_, baseRetr, rfl, ?_⟩
  · rw [heq v hv]; exact g_section v hv
  · have hU := relOpen_U.isScDomain
    have hr : IsScSmooth U (r R) := baseRetr.isScSmooth
    have h1 : IsScSmooth (E := E) (F := E.prod F) U (scPair (r R) (g ∘ r R)) :=
      hr.scPair hU (IsScSmooth.comp hU (isScDomain_univ _) isScSmooth_g_univ hr (mapsTo_univ _ _))
    exact h1.congr hU fun u hu => (heq _ (mem_image_of_mem _ hu)).symm

/-! ### The zero set -/

lemma fiberZero_val (x : Ob) : ((fiberZero kproj x : Kt) : E 0 × F 0) = ((x : E 0), 0) := rfl

lemma isZeroAt_sec_iff (x : Ob) : IsZeroAt kproj sec x ↔ g x = 0 := by
  constructor
  · intro h
    have := congrArg (fun y : Kt => (y : E 0 × F 0).2) h
    exact this
  · intro h
    exact Subtype.ext (Prod.ext rfl h)

lemma isZeroAt_sec_iff_mem_S (x : Ob) : IsZeroAt kproj sec x ↔ (x : E 0) ∈ S := by
  rw [isZeroAt_sec_iff]; exact g_eq_zero_iff (baseRetr.retract_subset x.2)

/-- **The solution set of `sec` is the closed half-line** `{((0, t), 0) | t ≤ 0}`. -/
theorem solutionSet_sec : solutionSet kproj sec = {x : Ob | (x : E 0) ∈ S} :=
  Set.ext fun x => isZeroAt_sec_iff_mem_S x

/-! ### The germ at `x₀ = 0` -/

/-- The point `x₀ = 0` of `O`. -/
def x0 : Ob := ⟨0, zero_mem_O⟩

lemma isZeroAt_sec_x0 : IsZeroAt kproj sec x0 := (isZeroAt_sec_iff x0).2 g_zero

/-- `g` is a 2021 filling of the principal part of `sec` in `chart0`. -/
theorem isFilling2021_sec_zero :
    IsFilling2021 chart0.relOpen chart0.isRetraction zero_mem_U (chart0.principal sec) g :=
  ⟨isFilling2021_g.r_zero, Eventually.of_forall fun _ hx => principal_sec hx,
    isFilling2021_g.mem_of_fixed, isFilling2021_g.germ⟩

/-- **The germ `(sec, x₀)` is an sc-Fredholm germ in the sense of 2021 Definition 3.6.3**
(= Definition 3.1.11, with the 2021 filling of Definitions 3.1.4/3.6.1): in the strong bundle
chart `chart0` (untamed base retraction), filling `g`, sc⁺-germ `0`, `g` a basic germ. -/
theorem isScFredholmGerm2021_sec_zero : bundle.IsScFredholmGerm2021 sec x0 :=
  ⟨by rw [smoothSet_polyO]; exact mem_univ _, chart0, isChart_chart0, mem_univ _, rfl, zero_mem_U,
    g, fun _ => 0, isFilling2021_sec_zero, isScPlusGerm_zero,
    (show F.toBase 1 (0 : F 1) = g (0 : E 0) by rw [map_zero, g_zero]),
    isConjugateToBasicGerm_g_sub⟩

/-- **The germ `(sec, x₀)` is in good position** (2021 Definition 3.6.6, in the chart of the germ
data: `Tf̃(0)` is onto and its kernel is in good position to `T₀O ∩ C` in `T₀O`). -/
theorem isGoodPositionGerm_sec_zero : bundle.IsGoodPositionGerm sec x0 :=
  ⟨by rw [smoothSet_polyO]; exact mem_univ _, chart0, isChart_chart0, mem_univ _, rfl, zero_mem_U,
    g, fun _ => 0, isFilling2021_sec_zero.isFillingGerm, isScPlusGerm_zero,
    (show F.toBase 1 (0 : F 1) = g (0 : E 0) by rw [map_zero, g_zero]),
    isConjugateToBasicGerm_g_sub,
    ScNbhdGerm.ofSet relOpen_U.relOpen zero_mem_U, scDeriv U g, fun _ hu => hu,
    isScSmooth_g.isSc1.isSc1GermWith_ofSet relOpen_U.relOpen zero_mem_U, isGoodPositionAtGerm_g⟩

/-- **The fibre over `x₀` is `0`**: `f'(x₀) : T_{x₀}X → Y_{x₀}` is onto in every reading. -/
theorem subsingleton_fiber_zero : Subsingleton (kproj ⁻¹' {x0}) := by
  have : Subsingleton (fib (x0 : E 0).1.2) := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    have h : ∀ c : fib (x0 : E 0).1.2, (c : F 0) = 0 := fun c =>
      Prod.ext c.2.1 (by rw [← c.2.2]; exact proj_of_nonpos le_rfl _)
    rw [h a, h b]
  exact (fibEquiv x0).subsingleton

/-! ### The solution set near `x₀` is not a sub-M-polyfold -/

/-- **No sc-smooth retraction of a neighbourhood of `x₀` in `O` has the half-line as image**
(the local form of `not_isSubMPolyfold_solutionSet`). -/
theorem not_exists_localRetraction :
    ¬ ∃ V : Set Ob, IsOpen V ∧ x0 ∈ V ∧ ∃ ϱ : Ob → Ob, MapsTo ϱ V V ∧
      polyO.IsScSmoothOn polyO ϱ V ∧ (∀ x ∈ V, ϱ (ϱ x) = ϱ x) ∧
      ϱ '' V = {x : Ob | (x : E 0) ∈ S} ∩ V := by
  rintro ⟨V, hVo, h0V, ϱ, hmaps, hsm, hidem, himg⟩
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hVo
  have hsymm : ∀ z (hz : z ∈ r R '' U), chartO.symm z = ⟨z, hz⟩ := chartO_symm
  have himgφ : chartO '' (Subtype.val ⁻¹' W) = r R '' U ∩ W := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
    · rintro ⟨hz, hzW⟩; exact ⟨⟨z, hz⟩, hzW, rfl⟩
  have hret := hsm.smooth chartO chartO isChart_chartO isChart_chartO (Subtype.val ⁻¹' W) hVo
    (fun y hy => ⟨hy, mem_univ _⟩) (fun y _ => mem_univ _)
  have hsc := hret.comp_isScSmooth (baseRetrOn hW) ((baseRetrOn_retract hW).trans himgφ.symm)
  refine not_exists_retraction ⟨W, fun z => ((ϱ (chartO.symm z) : Ob) : E 0), hW, h0V,
    hsc.isSc1, ?_, ?_⟩
  · rintro x ⟨hxO, hxW⟩
    have hx : (⟨x, hxO⟩ : Ob) ∈ Subtype.val ⁻¹' W := hxW
    have h1 : ϱ ⟨x, hxO⟩ ∈ ϱ '' (Subtype.val ⁻¹' W) := ⟨_, hx, rfl⟩
    rw [himg] at h1
    change ((ϱ (chartO.symm x) : Ob) : E 0) ∈ S
    rw [hsymm x hxO]; exact h1.1
  · rintro x ⟨hxS, hxW⟩
    have hxO : x ∈ r R '' U := mem_O.2 ⟨hxS.1, lt_of_le_of_lt hxS.2.1 zero_lt_one, hxS.2.2⟩
    have h1 : (⟨x, hxO⟩ : Ob) ∈ {x : Ob | (x : E 0) ∈ S} ∩ Subtype.val ⁻¹' W := ⟨hxS, hxW⟩
    rw [← himg] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    change ((ϱ (chartO.symm x) : Ob) : E 0) = x
    rw [hsymm x hxO, ← hyx, hidem y hy, hyx]

/-- **For every open `W ∋ x₀`, the zero set of `sec` in `W` is not a sub-M-polyfold of `O`**
(2021 Definition 2.3.18): conclusion (2) of 2021 Theorem 3.6.8 does not hold for `sec` at
`x₀`. -/
theorem not_isSubMPolyfold_zeroSet {W : Set Ob} (hW : IsOpen W) (h0 : x0 ∈ W) :
    ¬ polyO.IsSubMPolyfold {y ∈ W | IsZeroAt kproj sec y} := by
  intro h
  obtain ⟨V, hVo, h0V, ϱ, hmaps, hsm, hidem, himg⟩ := h x0 ⟨h0, isZeroAt_sec_x0⟩
  have hϱ : ∀ x ∈ V, ϱ x ∈ W ∧ IsZeroAt kproj sec (ϱ x) := fun x hx => by
    have : ϱ x ∈ ϱ '' V := ⟨x, hx, rfl⟩
    rw [himg] at this
    exact this.1
  refine not_exists_localRetraction ⟨V ∩ W, hVo.inter hW, ⟨h0V, h0⟩, ϱ,
    fun x hx => ⟨hmaps hx.1, (hϱ x hx.1).1⟩, hsm.mono (hVo.inter hW) inter_subset_left,
    fun x hx => hidem x hx.1, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(isZeroAt_sec_iff_mem_S _).1 (hϱ x hx.1).2, hmaps hx.1, (hϱ x hx.1).1⟩
  · rintro ⟨hyS, hyV, hyW⟩
    have : y ∈ ϱ '' V := by
      rw [himg]; exact ⟨⟨hyW, (isZeroAt_sec_iff_mem_S y).2 hyS⟩, hyV⟩
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨ϱ x, ⟨hyV, hyW⟩, hidem x hx⟩

/-! ### The solution set has no tangent germ data at `x₀` -/

/-- The coordinate `t` on `O`. -/
def tco (x : Ob) : ℝ := (x : E 0).1.2

lemma continuous_tco : Continuous tco :=
  (continuous_snd.comp continuous_fst).comp continuous_subtype_val

lemma tco_injective : Injective tco := fun x y h => by
  obtain ⟨h1, -, h3⟩ := mem_O.1 x.2
  obtain ⟨h1', -, h3'⟩ := mem_O.1 y.2
  exact Subtype.ext (Prod.ext (Prod.ext (h1.trans h1'.symm) h) (h3.trans h3'.symm))

/-- The point `((0, t), 0)` of `O`, `t < 1`. -/
def ptO (t : ℝ) (ht : t < 1) : Ob := ⟨((0, t), 0), mem_O.2 ⟨rfl, ht, rfl⟩⟩

lemma tco_ptO (t : ℝ) (ht : t < 1) : tco (ptO t ht) = t := rfl

lemma ptO_tco (x : Ob) : ptO (tco x) (mem_O.1 x.2).2.1 = x := tco_injective rfl

/-- The half-line `s ↦ ((0, min s 0), 0)` in the solution set. -/
def negPt (s : ℝ) : Ob := ptO (min s 0) (lt_of_le_of_lt (min_le_right _ _) zero_lt_one)

lemma continuous_negPt : Continuous negPt :=
  ((continuous_const.prodMk (continuous_id.min continuous_const)).prodMk
    continuous_const).subtype_mk _

lemma tco_negPt (s : ℝ) : tco (negPt s) = min s 0 := rfl

lemma negPt_zero : negPt 0 = x0 := tco_injective (min_self 0)

lemma negPt_mem_S (s : ℝ) : ((negPt s : Ob) : E 0) ∈ S := ⟨rfl, min_le_right _ _, rfl⟩

/-- **The solution set of `sec` has no tangent germ data at `x₀`** (2021 Definition 3.2.1 (2), in
the project's form `TangentGermChart`: a tame chart centred at `x₀` in which the set is a graph
over a relatively open neighbourhood of `0` in `N ∩ C`, `N` of dimension `d` in good position), for
any `d`.  In a tame chart `d_C(0) = d_X(x₀) = 0`, so the graph is over a neighbourhood of `0` in
`N`; the half-line is not such a graph.  So conclusion (2) of 2021 Theorem 3.6.8, in the form of
`theorem_3_6_8'`, does not hold for `sec` at `x₀`. -/
theorem isEmpty_tangentGermChart (d : ℕ) :
    IsEmpty (polyO.TangentGermChart (solutionSet kproj sec) x0 d) := by
  refine ⟨fun D => ?_⟩
  have hdeg : MPolyfold.chartDegIndex D.φ x0 = 0 := by
    rw [← polyO.degIndex_eq_chartDegIndex_of_isTameRetract D.isChart D.tame D.mem_source]
    exact degIndex_polyO x0
  have hint : (0 : D.φ.model.E 0) ∈ interior D.φ.model.C := by
    have h := (mem_interior_iff_degIndex_eq_zero D.φ.model.isPartialQuadrant
      (D.φ.apply_mem_C D.mem_source)).2 hdeg
    rwa [D.φ_zero] at h
  obtain ⟨O', hO', hV⟩ := D.V_relOpen
  have h0O' : (0 : D.N) ∈ O' := (hV ▸ D.zero_mem_V : (0 : D.N) ∈ O' ∩ _).1
  have hVn : D.V ∈ 𝓝 (0 : D.N) := by
    rw [hV]
    refine inter_mem (hO'.mem_nhds h0O') ?_
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds
      (mem_interior_iff_mem_nhds.1 hint)
  have hΓmem : ∀ v ∈ D.V, ∃ y ∈ solutionSet kproj sec ∩ D.φ.source, D.φ y = D.Γ v :=
    fun v hv => by
      have : D.Γ v ∈ D.φ '' (solutionSet kproj sec ∩ D.φ.source) := by
        rw [D.image_eq]; exact ⟨v, hv, rfl⟩
      exact this
  let γ : D.N → ℝ := fun v => tco (D.φ.symm (D.Γ v))
  have hγle : ∀ v ∈ D.V, γ v ≤ 0 := fun v hv => by
    obtain ⟨y, hy, hyv⟩ := hΓmem v hv
    change tco (D.φ.symm (D.Γ v)) ≤ 0
    rw [← hyv, D.φ.symm_apply_apply hy.2]
    exact ((isZeroAt_sec_iff_mem_S y).1 hy.1).2.1
  have hγinj : InjOn γ D.V := fun v hv v' hv' h => by
    obtain ⟨y, hy, hyv⟩ := hΓmem v hv
    obtain ⟨y', hy', hyv'⟩ := hΓmem v' hv'
    have h1 : D.φ.symm (D.Γ v) = D.φ.symm (D.Γ v') := tco_injective h
    rw [← hyv, ← hyv', D.φ.symm_apply_apply hy.2, D.φ.symm_apply_apply hy'.2] at h1
    have h2 : D.Γ v = D.Γ v' := by rw [← hyv, ← hyv', h1]
    have := congrArg D.π h2
    rwa [D.π_Γ, D.π_Γ] at this
  have hγcont : ContinuousOn γ D.V :=
    continuous_tco.comp_continuousOn
      (D.φ.continuousOn_invFun.comp D.Γ_continuousOn fun v hv => D.Γ_mem_O hv)
  have hΓ0 : D.Γ 0 = D.φ x0 := by
    rw [D.Γ_apply, D.δ_zero, D.φ_zero, Submodule.coe_zero, add_zero]
  have hγ0 : γ 0 = 0 := by
    change tco (D.φ.symm (D.Γ 0)) = 0
    rw [hΓ0, D.φ.symm_apply_apply D.mem_source]; rfl
  -- a second point of the solution set in the chart
  have hsrc : ∀ᶠ s in 𝓝 (0 : ℝ), negPt s ∈ D.φ.source := by
    have : D.φ.source ∈ 𝓝 (negPt 0) := by
      rw [negPt_zero]; exact D.φ.isOpen_source.mem_nhds D.mem_source
    exact continuous_negPt.continuousAt this
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hsrc
  have hx1src : negPt (-(ε / 2)) ∈ D.φ.source := hball (by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hε)]; exact half_lt_self hε)
  obtain ⟨v₁, hv₁, hv₁e⟩ : ∃ v ∈ D.V, D.Γ v = D.φ (negPt (-(ε / 2))) := by
    have : D.φ (negPt (-(ε / 2))) ∈ D.φ '' (solutionSet kproj sec ∩ D.φ.source) :=
      ⟨_, ⟨(isZeroAt_sec_iff_mem_S _).2 (negPt_mem_S _), hx1src⟩, rfl⟩
    rw [D.image_eq] at this; exact this
  have hv₁ne : v₁ ≠ 0 := by
    rintro rfl
    have h1 : D.φ (negPt (-(ε / 2))) = D.φ x0 := by rw [← hv₁e, hΓ0]
    have h2 := D.φ.toPartialEquiv.injOn hx1src D.mem_source h1
    have h3 : min (-(ε / 2)) 0 = 0 := congrArg tco h2
    rw [min_eq_left (by linarith)] at h3
    linarith
  -- a segment through `0` in `V`
  have hseg : ∀ᶠ s in 𝓝 (0 : ℝ), s • v₁ ∈ D.V := by
    have hc : Continuous fun s : ℝ => s • v₁ := continuous_id.smul continuous_const
    have : D.V ∈ 𝓝 ((0 : ℝ) • v₁) := by rw [zero_smul]; exact hVn
    exact hc.continuousAt this
  obtain ⟨η', hη', hball'⟩ := Metric.eventually_nhds_iff.1 hseg
  have hηpos : 0 < η' / 2 := half_pos hη'
  have hmemV : ∀ s ∈ Icc (-(η' / 2)) (η' / 2), s • v₁ ∈ D.V := fun s hs => hball' (by
    rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith [hs.1, hs.2])
  let c : ℝ → ℝ := fun s => γ (s • v₁)
  have hcc : ContinuousOn c (Icc (-(η' / 2)) (η' / 2)) :=
    hγcont.comp (continuous_id.smul continuous_const).continuousOn hmemV
  have hcinj : InjOn c (Icc (-(η' / 2)) (η' / 2)) := fun s hs s' hs' h =>
    smul_left_injective ℝ hv₁ne (hγinj (hmemV s hs) (hmemV s' hs') h)
  have hc0 : c 0 = 0 := by
    change γ ((0 : ℝ) • v₁) = 0
    rw [zero_smul]; exact hγ0
  have hcle : ∀ s ∈ Icc (-(η' / 2)) (η' / 2), c s ≤ 0 := fun s hs => hγle _ (hmemV s hs)
  have h0mem : (0 : ℝ) ∈ Icc (-(η' / 2)) (η' / 2) := ⟨by linarith, hηpos.le⟩
  have hηmem : η' / 2 ∈ Icc (-(η' / 2)) (η' / 2) := ⟨by linarith, le_rfl⟩
  have hnηmem : -(η' / 2) ∈ Icc (-(η' / 2)) (η' / 2) := ⟨le_rfl, by linarith⟩
  have hcη : c (η' / 2) < 0 := lt_of_le_of_ne (hcle _ hηmem) fun h => by
    have := hcinj hηmem h0mem (h.trans hc0.symm); linarith
  have hcnη : c (-(η' / 2)) < 0 := lt_of_le_of_ne (hcle _ hnηmem) fun h => by
    have := hcinj hnηmem h0mem (h.trans hc0.symm); linarith
  have hm0 : max (c (η' / 2)) (c (-(η' / 2))) < 0 := max_lt hcη hcnη
  have h1 : max (c (η' / 2)) (c (-(η' / 2))) ∈ c '' Icc 0 (η' / 2) := by
    refine intermediate_value_Icc' hηpos.le
      (hcc.mono (Icc_subset_Icc (by linarith) le_rfl)) ⟨le_max_left _ _, ?_⟩
    rw [hc0]; exact hm0.le
  have h2 : max (c (η' / 2)) (c (-(η' / 2))) ∈ c '' Icc (-(η' / 2)) 0 := by
    refine intermediate_value_Icc (by linarith)
      (hcc.mono (Icc_subset_Icc le_rfl hηpos.le)) ⟨le_max_right _ _, ?_⟩
    rw [hc0]; exact hm0.le
  obtain ⟨s₁, hs₁, hs₁m⟩ := h1
  obtain ⟨s₂, hs₂, hs₂m⟩ := h2
  have hs : s₁ = s₂ := hcinj ⟨by linarith [hs₁.1], hs₁.2⟩ ⟨hs₂.1, by linarith [hs₂.2]⟩
    (hs₁m.trans hs₂m.symm)
  have hs0 : s₁ = 0 := le_antisymm (hs ▸ hs₂.2) hs₁.1
  rw [hs0, hc0] at hs₁m
  linarith

end UntamedCorner

end Polyfold
