import Polyfold.Chapter16.HalfDiscIntervalCobordism
import Polyfold.Chapter6.IntervalCobordismDegeneracy
import Polyfold.Chapter2.FaceFamilies

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §2.5, p. 72
(**Definition 2.5.10**), and the proof of **Theorem 6.7.1**, p. 278, on the half-disc example of
`HalfDiscIntervalCobordism.lean`.

# The faces of the cobordism `S_F = [0, 1] × S_f` over `[0, 1] × H`

## The text, paraphrased

(Definition 2.5.10) A face of a tame M-polyfold is the closure of a connected component of
`\{d = 1\}`; it is face-structured if every `x` lies in exactly `d(x)` faces.  The proof of
Theorem 6.7.1 applies Stokes' theorem to the cobordism `S_F`, whose boundary consists of the
ends `\{0\} × S_{F_0}`, `\{1\} × S_{F_1}` and the part over `[0, 1] × ∂X`.

## What is formalized (namespace `Polyfold.HalfSpaceBundle`)

`H = [0, ∞) × ℝ`, `f(a, y) = ((a, y), a² + y² − 1)`, `S_f` the half circle, and `S` any
sc⁺-section over `[0, 1] × H` with `F = f̃ + S` proper, in general position and with
`S_F = [0, 1] × S_f` (the section `S = 0` of `interval_cobordism_halfDisc` is one).

* `degIndex_basePoly_one`: `d_H(a, y) = 1` if `a = 0` and `0` otherwise.
* `halfCylinderHomeomorph`: `[0, 1] × S_f ≅ [0, 1]²`, `(t, (a, y)) ↦ (t, (y + 1)/2)`.
* `degIndex_halfDisc_cobordism`: `d_{S_F}(t, (a, y)) = d_{[0,1]}(t) + d_{[0,1]}((y + 1)/2)`.
* **`isFaceStructured_halfDisc_cobordism`**: the sub-M-polyfold `S_F` is face-structured.
* **`isFace_halfDisc_cobordism_iff`**: its faces are exactly `\{0\} × S_f`, `\{1\} × S_f`,
  `[0, 1] × \{(0, −1)\}` and `[0, 1] × \{(0, 1)\}`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

open StrongBundle UnitCube MPolyfold

local instance instParacompactIvH : ParacompactSpace ((Fin 1 → unitInterval) × H 1) :=
  MPolyfold.paracompactSpace_prod (cubePolyfold 1) (basePoly 1)

local instance instParacompactIvPullback :
    ParacompactSpace (pullbackSpace (proj 1 1) (Prod.snd : (Fin 1 → unitInterval) × H 1 → H 1)) :=
  paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin 1 → unitInterval) × H 1 → H 1))
    ((cubePolyfold 1).prod (basePoly 1)) (bundle 1 1)

/-- **`d_H(a, y)`** (Corollary 2.4.13): `1` on `∂H = \{a = 0\}` and `0` otherwise. -/
theorem degIndex_basePoly_one (x : H 1) :
    (basePoly 1).degIndex x = if (x : Pm 1).1 0 = 0 then 1 else 0 := by
  change (MPolyfold.quadrantPolyfold 1 (rnSc 1)).degIndex x = _
  rw [MPolyfold.quadrantPolyfold, corollary_2_4_13 (MPolyfold.isRelOpenInQuadrant_quadrant 1 _)
    (MPolyfold.quadrant_nonempty 1 _), degIndex_quadrant x.2]
  unfold quadrantDeg
  split_ifs with h
  · rw [Finset.filter_true_of_mem fun i _ => by rw [Subsingleton.elim i 0]; exact h]
    rfl
  · rw [Finset.filter_false_of_mem fun i _ => by rw [Subsingleton.elim i 0]; exact h]
    rfl

theorem halfCircle_abs_le {a y : ℝ} (h : a ^ 2 + y ^ 2 = 1) : -1 ≤ y ∧ y ≤ 1 :=
  abs_le.1 (sq_le_one_iff_abs_le_one y |>.1 (by nlinarith [sq_nonneg a]))

/-- The coordinate `(y + 1)/2 ∈ [0, 1]` of a point `(a, y)` of the unit circle. -/
theorem halfCircle_mem_unitInterval {a y : ℝ} (h : a ^ 2 + y ^ 2 = 1) :
    (y + 1) / 2 ∈ unitInterval := by
  obtain ⟨h1, h2⟩ := halfCircle_abs_le h
  constructor <;> linarith

/-- On the half circle, `a = 0` iff `y = ±1`, i.e. `(y + 1)/2 ∈ \{0, 1\}`. -/
theorem halfCircle_eq_zero_iff {a y : ℝ} (ha : 0 ≤ a) (h : a ^ 2 + y ^ 2 = 1) :
    a = 0 ↔ (y + 1) / 2 = 0 ∨ (y + 1) / 2 = 1 := by
  constructor
  · rintro rfl
    have : (y + 1) * (y - 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h1 | h1
    · left
      linarith
    · right
      linarith
  · intro h1
    have hy : y ^ 2 = 1 := by
      rcases h1 with h1 | h1
      · have : y = -1 := by linarith
        rw [this]
        norm_num
      · have : y = 1 := by linarith
        rw [this]
        norm_num
    have ha2 : a ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff two_ne_zero |>.1 ha2

/-- The point `(√(1 − y²), y)` of the half circle, `y = 2s − 1`, `s ∈ [0, 1]`. -/
def halfCirclePt (s : unitInterval) : H 1 :=
  ⟨(show (halfSpaceSc 1) 0 from
    (fun _ => Real.sqrt (1 - (2 * (s : ℝ) - 1) ^ 2), fun _ => 2 * (s : ℝ) - 1)),
    mem_quadrant_one_iff.2 (Real.sqrt_nonneg _)⟩

theorem halfCirclePt_eq (s : unitInterval) :
    ((halfCirclePt s : Pm 1).1 0) ^ 2 + ((halfCirclePt s : Pm 1).2 0) ^ 2 = 1 := by
  change Real.sqrt (1 - (2 * (s : ℝ) - 1) ^ 2) ^ 2 + (2 * (s : ℝ) - 1) ^ 2 = 1
  have h0 : (0 : ℝ) ≤ s := s.2.1
  have h1 : (s : ℝ) ≤ 1 := s.2.2
  rw [Real.sq_sqrt (by nlinarith)]
  ring

theorem continuous_halfCirclePt : Continuous halfCirclePt := by
  refine Continuous.subtype_mk (Continuous.prodMk (continuous_pi fun _ => ?_)
    (continuous_pi fun _ => ?_)) _
  · exact Real.continuous_sqrt.comp (continuous_const.sub
      (((continuous_const.mul continuous_subtype_val).sub continuous_const).pow 2))
  · exact (continuous_const.mul continuous_subtype_val).sub continuous_const

/-- **`[0, 1] × S_f ≅ [0, 1]²`**: for `T ⊆ [0, 1] × H` the set of `(t, (a, y))` with
`a² + y² = 1`, the map `(t, (a, y)) ↦ (t, (y + 1)/2)` is a homeomorphism onto the square, with
inverse `(t, s) ↦ (t, (√(1 − (2s − 1)²), 2s − 1))`. -/
def halfCylinderHomeomorph (T : Set ((Fin 1 → unitInterval) × H 1))
    (hT : ∀ z, z ∈ T ↔ ((z.2 : Pm 1).1 0) ^ 2 + ((z.2 : Pm 1).2 0) ^ 2 = 1) :
    T ≃ₜ unitInterval × unitInterval where
  toFun z := (z.1.1 0, ⟨((z.1.2 : Pm 1).2 0 + 1) / 2, halfCircle_mem_unitInterval ((hT z.1).1 z.2)⟩)
  invFun p := ⟨(fun _ => p.1, halfCirclePt p.2), (hT _).2 (halfCirclePt_eq p.2)⟩
  left_inv z := by
    obtain ⟨⟨t, x⟩, hz⟩ := z
    have h := (hT _).1 hz
    have ha : 0 ≤ (x : Pm 1).1 0 := mem_quadrant_one_iff.1 x.2
    refine Subtype.ext (Prod.ext (funext fun i => by rw [Subsingleton.elim i 0]) ?_)
    refine Subtype.ext (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
    · rw [Subsingleton.elim i 0]
      change Real.sqrt (1 - (2 * (((x : Pm 1).2 0 + 1) / 2) - 1) ^ 2) = (x : Pm 1).1 0
      rw [show 1 - (2 * (((x : Pm 1).2 0 + 1) / 2) - 1) ^ 2 = ((x : Pm 1).1 0) ^ 2 by
        simp only at h
        linarith [h, show (2 * (((x : Pm 1).2 0 + 1) / 2) - 1) = (x : Pm 1).2 0 by ring]]
      exact Real.sqrt_sq ha
    · rw [Subsingleton.elim i 0]
      change 2 * (((x : Pm 1).2 0 + 1) / 2) - 1 = (x : Pm 1).2 0
      ring
  right_inv p := by
    refine Prod.ext rfl (Subtype.ext ?_)
    change ((2 * (p.2 : ℝ) - 1) + 1) / 2 = p.2
    ring
  continuous_toFun := by
    refine Continuous.prodMk
      ((continuous_apply 0).comp (continuous_fst.comp continuous_subtype_val))
      (Continuous.subtype_mk ?_ _)
    exact ((((continuous_apply 0).comp continuous_snd).comp (continuous_subtype_val.comp
      (continuous_snd.comp continuous_subtype_val))).add continuous_const).div_const 2
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.prodMk (continuous_pi fun _ => continuous_fst)
      (continuous_halfCirclePt.comp continuous_snd)) _

/-! ### The cobordism `S_F = [0, 1] × S_f` -/

section Cobordism

variable (hf : (bundle 1 1).IsScFredholmSectionTame (graphSection halfDiscMap))
  {S : (Fin 1 → unitInterval) × H 1 →
    pullbackSpace (proj 1 1) (Prod.snd : (Fin 1 → unitInterval) × H 1 → H 1)}

/-- If `S_F = [0, 1] × S_f`, then `(t, (a, y)) ∈ S_F` iff `a² + y² = 1`. -/
theorem mem_halfDisc_cobordism_iff
    (hsol : solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) =
      univ ×ˢ solutionSet (proj 1 1) (graphSection halfDiscMap))
    (z : (Fin 1 → unitInterval) × H 1) :
    z ∈ solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) ↔
      ((z.2 : Pm 1).1 0) ^ 2 + ((z.2 : Pm 1).2 0) ^ 2 = 1 := by
  rw [hsol]
  exact ⟨fun h => (halfDiscMap_eq_zero_iff _).1 (isZeroAt_graphSection_iff.1 h.2),
    fun h => ⟨mem_univ _, isZeroAt_graphSection_iff.2 ((halfDiscMap_eq_zero_iff _).2 h)⟩⟩

/-- **The degeneracy index of `S_F`** (`degIndex_interval_cobordism` and Corollary 2.4.13): at
`(t, (a, y)) ∈ S_F = [0, 1] × S_f`, `d_{S_F} = d_{[0,1]}(t) + d_H(a, y)`, and on the half circle
`d_H(a, y) = d_{[0,1]}((y + 1)/2)`: the degeneracy index of the square at the image under
`halfCylinderHomeomorph`. -/
theorem degIndex_halfDisc_cobordism (hS : (ivBundle (bundle 1 1)).IsScPlusSection S)
    (hP : (ivBundle (bundle 1 1)).IsProper (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
      (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S))
    (hgp : ∀ z, IsZeroAt (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) z →
      (ivBundle (bundle 1 1)).IsGeneralPositionGerm
        (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
          (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) z)
    (hSm : ((cubePolyfold 1).prod (basePoly 1)).IsSmoothSubmanifold
      (solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S)))
    (hsol : solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) =
      univ ×ˢ solutionSet (proj 1 1) (graphSection halfDiscMap))
    (z : solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S)) :
    haveI := ((cubePolyfold 1).prod (basePoly 1)).paracompactSpace_subtype
      (solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S))
    (MPolyfold.subPolyfold hSm.isSubMPolyfold).degIndex z =
      squareDeg (halfCylinderHomeomorph _ (mem_halfDisc_cobordism_iff hf hsol) z) := by
  have := ((cubePolyfold 1).prod (basePoly 1)).paracompactSpace_subtype
    (solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S))
  rw [degIndex_interval_cobordism (show (basePoly 1).IsTame from isTame_halfSEP 1 1) hf hS hP hgp
      hSm z,
    cubePolyfold_one_degIndex, degIndex_basePoly_one]
  have h := (mem_halfDisc_cobordism_iff hf hsol z.1).1 z.2
  have ha : 0 ≤ (z.1.2 : Pm 1).1 0 := mem_quadrant_one_iff.1 z.1.2.2
  change _ = endDeg (z.1.1 0) + endDeg ⟨((z.1.2 : Pm 1).2 0 + 1) / 2, _⟩
  rw [endDeg, endDeg]
  exact congrArg _ (if_congr (halfCircle_eq_zero_iff ha h) rfl rfl)

/-- **`S_F` is face-structured** (Definition 2.5.10, on the half-disc example; not in the
text): for `H = [0, ∞) × ℝ`, `f(a, y) = ((a, y), a² + y² − 1)` and an sc⁺-section `S` over
`[0, 1] × H` with `F = f̃ + S` proper, in general position and `S_F = [0, 1] × S_f`, every point of
the sub-M-polyfold `S_F` lies in exactly `d_{S_F}` faces. -/
theorem isFaceStructured_halfDisc_cobordism (hS : (ivBundle (bundle 1 1)).IsScPlusSection S)
    (hP : (ivBundle (bundle 1 1)).IsProper (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
      (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S))
    (hgp : ∀ z, IsZeroAt (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) z →
      (ivBundle (bundle 1 1)).IsGeneralPositionGerm
        (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
          (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) z)
    (hSm : ((cubePolyfold 1).prod (basePoly 1)).IsSmoothSubmanifold
      (solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S)))
    (hsol : solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) =
      univ ×ˢ solutionSet (proj 1 1) (graphSection halfDiscMap)) :
    haveI := ((cubePolyfold 1).prod (basePoly 1)).paracompactSpace_subtype
      (solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S))
    (MPolyfold.subPolyfold hSm.isSubMPolyfold).IsFaceStructured := by
  have := ((cubePolyfold 1).prod (basePoly 1)).paracompactSpace_subtype
    (solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S))
  obtain ⟨hU, hA, hcov, hdisj, hconn, hne, hcl, hinj, hcount⟩ := squareFamily
  exact (MPolyfold.isFaceStructured_iff_isFaceCount _).2
    (isFaceCount_of_homeomorph (halfCylinderHomeomorph _ (mem_halfDisc_cobordism_iff hf hsol))
      (degIndex_halfDisc_cobordism hf hS hP hgp hSm hsol) hU hA hcov hdisj hconn hne hcl hinj
      hcount)

/-- **The four faces of `S_F`** (Definition 2.5.10, on the half-disc example; not in the text):
under the hypotheses of `isFaceStructured_halfDisc_cobordism`, the faces of `S_F` are exactly
the ends `\{0\} × S_f` and `\{1\} × S_f` and the lateral faces `[0, 1] × \{(0, −1)\}` and
`[0, 1] × \{(0, 1)\}`. -/
theorem isFace_halfDisc_cobordism_iff (hS : (ivBundle (bundle 1 1)).IsScPlusSection S)
    (hP : (ivBundle (bundle 1 1)).IsProper (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
      (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S))
    (hgp : ∀ z, IsZeroAt (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) z →
      (ivBundle (bundle 1 1)).IsGeneralPositionGerm
        (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
          (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) z)
    (hSm : ((cubePolyfold 1).prod (basePoly 1)).IsSmoothSubmanifold
      (solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S)))
    (hsol : solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S) =
      univ ×ˢ solutionSet (proj 1 1) (graphSection halfDiscMap))
    (F : Set (solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S))) :
    haveI := ((cubePolyfold 1).prod (basePoly 1)).paracompactSpace_subtype
      (solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S))
    (MPolyfold.subPolyfold hSm.isSubMPolyfold).IsFace F ↔
      F = {z | (z.1.1 0 : ℝ) = 0} ∨ F = {z | (z.1.1 0 : ℝ) = 1} ∨
        F = {z | (z.1.2 : Pm 1).2 0 = -1} ∨ F = {z | (z.1.2 : Pm 1).2 0 = 1} := by
  have := ((cubePolyfold 1).prod (basePoly 1)).paracompactSpace_subtype
    (solutionSet (pullbackProj (proj 1 1) Prod.snd)
      (sectionAdd (pullbackProj (proj 1 1) Prod.snd)
        (cubeLift (n := 1) (graphSection halfDiscMap) hf.isScSmooth.1) S))
  obtain ⟨hU, hA, hcov, hdisj, hconn, hne, hcl, hinj, hcount⟩ := squareFamily
  have h := isFace_iff_of_homeomorph (halfCylinderHomeomorph _ (mem_halfDisc_cobordism_iff hf hsol))
    (degIndex_halfDisc_cobordism hf hS hP hgp hSm hsol) hU hA hcov hdisj hconn hne hcl hinj
    hcount F
  refine h.trans ?_
  have hG : ∀ i, (halfCylinderHomeomorph _ (mem_halfDisc_cobordism_iff hf hsol)) ⁻¹' squareG i =
      match i with
      | .inl false => {z | (z.1.1 0 : ℝ) = 0}
      | .inl true => {z | (z.1.1 0 : ℝ) = 1}
      | .inr false => {z | (z.1.2 : Pm 1).2 0 = -1}
      | .inr true => {z | (z.1.2 : Pm 1).2 0 = 1} := by
    rintro ((_ | _) | (_ | _)) <;> ext z
    · exact Subtype.ext_iff
    · exact Subtype.ext_iff
    · change (⟨((z.1.2 : Pm 1).2 0 + 1) / 2, _⟩ : unitInterval) = 0 ↔ _
      rw [Subtype.ext_iff]
      change ((z.1.2 : Pm 1).2 0 + 1) / 2 = 0 ↔ (z.1.2 : Pm 1).2 0 = -1
      constructor <;> intro h' <;> linarith
    · change (⟨((z.1.2 : Pm 1).2 0 + 1) / 2, _⟩ : unitInterval) = 1 ↔ _
      rw [Subtype.ext_iff]
      change ((z.1.2 : Pm 1).2 0 + 1) / 2 = 1 ↔ (z.1.2 : Pm 1).2 0 = 1
      constructor <;> intro h' <;> linarith
  constructor
  · rintro ⟨i, rfl⟩
    rw [hG i]
    rcases i with (_ | _) | (_ | _)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨.inl false, (hG (.inl false)).symm⟩
    · exact ⟨.inl true, (hG (.inl true)).symm⟩
    · exact ⟨.inr false, (hG (.inr false)).symm⟩
    · exact ⟨.inr true, (hG (.inr true)).symm⟩

end Cobordism

end HalfSpaceBundle

end Polyfold
