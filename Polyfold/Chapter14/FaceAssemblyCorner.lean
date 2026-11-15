import Polyfold.Chapter14.QuadrantBundle
import Polyfold.Chapter14.FaceAssembly

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.6, pp. 680–682:
**Definition 14.6.2** (compatible assignments `F ↦ Λ̃_F`) and **Theorem 14.6.3** (2017:
Definition 14.11, Theorem 14.4), at a corner.

# A compatible assignment whose glued functor is not an sc⁺-multisection over `∂X`

## The text, paraphrased

(Definition 13.3.8) Two tuples `(Λ, 𝒰, S, τ)`, `(Λ', 𝒰', S', τ')` are equivalent if `Λ = Λ'`, a
good system `𝒰''` lies in both, `I_x = I'_x`, and `τ = τ'` on `𝒰''(x, x')`.  (Definition 14.6.2)
`F ↦ Λ̃_F` is compatible if the classes `Λ̃_F|F'` and `Λ̃_{F'}|F` over `F ∩ F'` agree.  (p. 682)
Then `sˣ_{F,i} = sˣ_{F',i}` on `U_F(x) ∩ U_{F'}(x)`.  (Theorem 14.6.3) A compatible
assignment defines a structured `Λ̃ : W|∂X → ℚ⁺`.

## What is formalized (namespace `Polyfold.FaceCorner`)

The equivalence of Definition 13.3.8 compares the functors, the index sets and the
correspondences; the sections do not enter.  With this reading the step on p. 682 and Theorem
14.6.3 do not hold as we read them:

* `X = [0, ∞)² × ℝ` with only identities, `W = X × ℝ²` (`quadSEP 2 1 2`), points `(x₁, x₂, t)`.
  With `e = expNegInvGlue`, `h(t) = e(t) + e(−t)` and `g(t) = e(t) − e(−t)`: on every face in
  `{x₁ = 0}` the sections `±(h(t), x₂)`, on every other face (it lies in `{x₂ = 0}`) the sections
  `±(g(t), x₁)`; `I_x = {±}` with the trivial action, weights `1/2`, `τ ≡ [id]`
  (`signTuple`, `Λt`).
* `isCompatibleAssignment_Λt`: the assignment is compatible (Definition 14.6.2): on the corner
  `{x₁ = x₂ = 0}` the two functors agree, because `{±h(t)} = {±g(t)}` for every `t`.
* `not_isBoundaryScPlusMultisection_of_eq_on_faces`: no functor which agrees with `Λ_F` over
  every face `F` is an sc⁺-multisection over `∂X` (Definition 14.1.3).  For sections `sᵢ` of a
  symmetric structure near the corner `0`: along a path in `{x₁ = 0}` from `(0, 0, r)` to
  `(0, 0, −r)` through `{x₂ > 0}`, `sᵢ = ε (h, x₂)` with a constant sign `ε`, and along a path in
  `{x₂ = 0}` through `{x₁ > 0}`, `sᵢ = δ (g, x₁)` with a constant sign `δ`; at `(0, 0, r)` this
  gives `ε = δ`, at `(0, 0, −r)` it gives `ε = −δ`.
* `theorem_14_6_3_class_statement A`: Theorem 14.6.3 for a compatible assignment of classes;
  **`not_theorem_14_6_3_class_statement`**: it does not hold for `quadSEP 2 1 2`, a tame
  face-structured ep-groupoid with paracompact orbit space and sc-smooth partitions of unity.
* `not_exists_compatibleFaceData`: no choice of representatives of the classes `Λt F` satisfies
  `CompatibleFaceData` (equal sections and correspondences on the intersections of faces).

The form of Theorem 14.6.3 which holds is `CompatibleFaceData.theorem_14_6_3_hyp`
(`FaceAssembly.lean`): representatives whose sections and correspondences agree on `F ∩ F'`, the
property the text states on p. 682.  `cornerFaceData` and `theorem_14_6_3_corner_witness` give
such data on the same bundle, with a corner and non-zero sections (`±(h(t), x₂)` on the faces in
`{x₁ = 0}`, `±(h(t), x₁)` on the others).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology
open scoped ContDiff

open scoped Classical

noncomputable section

namespace Polyfold

namespace FaceCorner

open SBLocalization StrongBundle EpGroupoid MPolyfold TameBoundaryExample QuadrantBundle

/-! ### Signs and continuity -/

/-- The sign of an index: `true ↦ 1`, `false ↦ −1`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> simp [sgn]

theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]

theorem sgn_ne_zero (b : Bool) : sgn b ≠ 0 := by cases b <;> simp [sgn]

theorem sgn_eq_iff (c : ℝ) : (∃ b, c = sgn b) ↔ c = 1 ∨ c = -1 :=
  ⟨by rintro ⟨b, rfl⟩; cases b <;> simp [sgn],
    by rintro (rfl | rfl); exacts [⟨true, rfl⟩, ⟨false, rfl⟩]⟩

/-- **A continuous choice of sign is constant**: if `v` and `f` are continuous on `[−1, 1]` with
values in `ℝ²`, `f` has no zero, and `v(u) = ± f(u)` for `u ∈ (−1, 1)`, then one sign serves at
both end points. -/
theorem exists_sign_endpoints {v f : ℝ → Fin 2 → ℝ} (hv : ContinuousOn v (Icc (-1) 1))
    (hf : ContinuousOn f (Icc (-1) 1)) (hf0 : ∀ u ∈ Icc (-1 : ℝ) 1, f u ≠ 0)
    (hvf : ∀ u ∈ Ioo (-1 : ℝ) 1, ∃ b : Bool, v u = sgn b • f u) :
    ∃ b : Bool, v (-1) = sgn b • f (-1) ∧ v 1 = sgn b • f 1 := by
  set D : ℝ → ℝ := fun u => f u 0 ^ 2 + f u 1 ^ 2 with hD
  set ψ : ℝ → ℝ := fun u => (v u 0 * f u 0 + v u 1 * f u 1) / D u with hψ
  have hDpos : ∀ u ∈ Icc (-1 : ℝ) 1, 0 < D u := by
    intro u hu
    have h0 := sq_nonneg (f u 0)
    have h1 := sq_nonneg (f u 1)
    rcases (add_nonneg h0 h1).lt_or_eq with h | h
    · exact h
    · exfalso
      have e0 : f u 0 = 0 := by nlinarith
      have e1 : f u 1 = 0 := by nlinarith
      exact hf0 u hu (funext fun i => by fin_cases i <;> assumption)
  have hc : ∀ (w : ℝ → Fin 2 → ℝ) (i : Fin 2), ContinuousOn w (Icc (-1) 1) →
      ContinuousOn (fun u => w u i) (Icc (-1) 1) := fun w i hw =>
    (continuous_apply i).comp_continuousOn hw
  have hDc : ContinuousOn D (Icc (-1) 1) := ((hc f 0 hf).pow 2).add ((hc f 1 hf).pow 2)
  have hψc : ContinuousOn ψ (Icc (-1) 1) :=
    (((hc v 0 hv).mul (hc f 0 hf)).add ((hc v 1 hv).mul (hc f 1 hf))).div hDc
      fun u hu => (hDpos u hu).ne'
  have hsub : Ioo (-1 : ℝ) 1 ⊆ Icc (-1) 1 := Ioo_subset_Icc_self
  have hcl : Icc (-1 : ℝ) 1 ⊆ closure (Ioo (-1) 1) := by
    rw [closure_Ioo (by norm_num)]
  -- on the open interval `ψ` is the sign
  have hψI : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ b : Bool, v u = sgn b • f u → ψ u = sgn b := by
    intro u hu b hb
    have hd := (hDpos u (hsub hu)).ne'
    simp only [hψ, hb, Pi.smul_apply, smul_eq_mul]
    rw [div_eq_iff hd]
    simp only [hD]; ring
  have hsq : EqOn (fun u => ψ u ^ 2) (fun _ => 1) (Icc (-1) 1) := by
    refine EqOn.of_subset_closure (fun u hu => ?_) (hψc.pow 2) continuousOn_const hsub hcl
    obtain ⟨b, hb⟩ := hvf u hu
    rw [hψI u hu b hb, sq, sgn_mul_self]
  have hvec : EqOn v (fun u => ψ u • f u) (Icc (-1) 1) := by
    refine EqOn.of_subset_closure (fun u hu => ?_) hv (hψc.smul hf) hsub hcl
    obtain ⟨b, hb⟩ := hvf u hu
    rw [hψI u hu b hb, hb]
  have hpm : ∀ u ∈ Icc (-1 : ℝ) 1, ψ u = 1 ∨ ψ u = -1 := fun u hu => by
    have h1 : ψ u ^ 2 = 1 := hsq hu
    have h2 : (ψ u - 1) * (ψ u + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hm : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hp : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hno : ∀ u ∈ Icc (-1 : ℝ) 1, ψ u ≠ 0 := fun u hu h0 => by
    have := hsq hu
    simp only [h0] at this
    norm_num at this
  have heq : ψ (-1) = ψ 1 := by
    rcases hpm _ hm with h1 | h1 <;> rcases hpm _ hp with h2 | h2
    · rw [h1, h2]
    · exfalso
      obtain ⟨c, hc', hc0⟩ := intermediate_value_Icc' (by norm_num : (-1 : ℝ) ≤ 1) hψc
        (show (0 : ℝ) ∈ Icc (ψ 1) (ψ (-1)) by rw [h1, h2]; constructor <;> norm_num)
      exact hno c hc' hc0
    · exfalso
      obtain ⟨c, hc', hc0⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) hψc
        (show (0 : ℝ) ∈ Icc (ψ (-1)) (ψ 1) by rw [h1, h2]; constructor <;> norm_num)
      exact hno c hc' hc0
    · rw [h1, h2]
  obtain ⟨b, hb⟩ := (sgn_eq_iff (ψ 1)).2 (hpm _ hp)
  refine ⟨b, (hvec hm).trans ?_, (hvec hp).trans ?_⟩
  · change ψ (-1) • f (-1) = _
    rw [heq, hb]
  · change ψ 1 • f 1 = _
    rw [hb]

/-! ### The two germs -/

/-- `h(t) = e(t) + e(−t)`, `e = expNegInvGlue`: smooth, even, positive off `0`, flat at `0`. -/
def hfun (t : ℝ) : ℝ := expNegInvGlue t + expNegInvGlue (-t)

/-- `g(t) = e(t) − e(−t)`: smooth, odd, `g = h` on `t ≥ 0` and `g = −h` on `t ≤ 0`. -/
def gfun (t : ℝ) : ℝ := expNegInvGlue t - expNegInvGlue (-t)

theorem hfun_of_nonneg {t : ℝ} (ht : 0 ≤ t) : hfun t = expNegInvGlue t := by
  rw [hfun, expNegInvGlue.zero_of_nonpos (neg_nonpos.2 ht), add_zero]

theorem hfun_of_nonpos {t : ℝ} (ht : t ≤ 0) : hfun t = expNegInvGlue (-t) := by
  rw [hfun, expNegInvGlue.zero_of_nonpos ht, zero_add]

theorem gfun_of_nonneg {t : ℝ} (ht : 0 ≤ t) : gfun t = expNegInvGlue t := by
  rw [gfun, expNegInvGlue.zero_of_nonpos (neg_nonpos.2 ht), sub_zero]

theorem gfun_of_nonpos {t : ℝ} (ht : t ≤ 0) : gfun t = -expNegInvGlue (-t) := by
  rw [gfun, expNegInvGlue.zero_of_nonpos ht, zero_sub]

theorem hfun_ne_zero {t : ℝ} (ht : t ≠ 0) : hfun t ≠ 0 := by
  rcases lt_or_gt_of_ne ht with h | h
  · rw [hfun_of_nonpos h.le]; exact (expNegInvGlue.pos_of_pos (neg_pos.2 h)).ne'
  · rw [hfun_of_nonneg h.le]; exact (expNegInvGlue.pos_of_pos h).ne'

theorem gfun_ne_zero {t : ℝ} (ht : t ≠ 0) : gfun t ≠ 0 := by
  rcases lt_or_gt_of_ne ht with h | h
  · rw [gfun_of_nonpos h.le]; exact neg_ne_zero.2 (expNegInvGlue.pos_of_pos (neg_pos.2 h)).ne'
  · rw [gfun_of_nonneg h.le]; exact (expNegInvGlue.pos_of_pos h).ne'

theorem hfun_eq_or (t : ℝ) : hfun t = gfun t ∨ hfun t = -gfun t := by
  rcases le_total 0 t with h | h
  · left; rw [hfun_of_nonneg h, gfun_of_nonneg h]
  · right; rw [hfun_of_nonpos h, gfun_of_nonpos h, neg_neg]

theorem contDiff_hfun : ContDiff ℝ ∞ hfun :=
  expNegInvGlue.contDiff.add (expNegInvGlue.contDiff.comp contDiff_neg)

theorem contDiff_gfun : ContDiff ℝ ∞ gfun :=
  expNegInvGlue.contDiff.sub (expNegInvGlue.contDiff.comp contDiff_neg)

/-- The model `ℝ² × ℝ` of the base, with points `((x₁, x₂), t)`. -/
abbrev E₀ : Type := (ESc 2 1) 0

/-- `φ₁(x₁, x₂, t) = (h(t), x₂)`: the principal part on the faces in `{x₁ = 0}`. -/
def φ₁ (u : E₀) : Fin 2 → ℝ := ![hfun (u.2 0), u.1 1]

/-- `φ₂(x₁, x₂, t) = (g(t), x₁)`: the principal part on the faces in `{x₂ = 0}`. -/
def φ₂ (u : E₀) : Fin 2 → ℝ := ![gfun (u.2 0), u.1 0]

theorem contDiff_φ₁ : ContDiff ℝ ∞ φ₁ := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · change ContDiff ℝ ∞ fun u : E₀ => hfun (u.2 0)
    exact contDiff_hfun.comp ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd)
  · change ContDiff ℝ ∞ fun u : E₀ => u.1 1
    exact (contDiff_apply ℝ ℝ (1 : Fin 2)).comp contDiff_fst

theorem contDiff_φ₂ : ContDiff ℝ ∞ φ₂ := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · change ContDiff ℝ ∞ fun u : E₀ => gfun (u.2 0)
    exact contDiff_gfun.comp ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd)
  · change ContDiff ℝ ∞ fun u : E₀ => u.1 0
    exact (contDiff_apply ℝ ℝ (0 : Fin 2)).comp contDiff_fst

/-- On the corner `{x₁ = x₂ = 0}` the two principal parts agree up to sign. -/
theorem φ₁_eq_or {u : E₀} (h0 : u.1 0 = 0) (h1 : u.1 1 = 0) : φ₁ u = φ₂ u ∨ φ₁ u = -φ₂ u := by
  rcases hfun_eq_or (u.2 0) with h | h
  · left; funext i; fin_cases i <;> simp [φ₁, φ₂, h, h0, h1]
  · right; funext i; fin_cases i <;> simp [φ₁, φ₂, h, h0, h1]

/-! ### The face tuples -/

/-- `X = [0, ∞)² × ℝ` with only identities, `W = X × ℝ²`. -/
abbrev A : SEP.{0} := quadSEP 2 1 2

/-- The trivial action on the index set `{±}`. -/
@[instance_reducible]
def boolAction (G : Type) [Monoid G] : MulAction G Bool where
  smul _ b := b
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- `I_x = {±}` with the trivial action. -/
def ι : IndexFamily A where
  I _ := Bool
  fintype _ := inferInstance
  mulAction _ := boolAction _
  nonempty _ := inferInstance

/-- The section `x ↦ (x, ± v(x))`. -/
def sec (v : E₀ → Fin 2 → ℝ) (b : Bool) : A.Obj → A.W := graphSec fun u => sgn b • v u

theorem sec_eq_iff (v : E₀ → Fin 2 → ℝ) (b : Bool) (w : Q 2 1 × (Fin 2 → ℝ)) :
    sec v b (A.P w) = w ↔ sgn b • v (w.1 : E₀) = w.2 :=
  ⟨fun h => congrArg Prod.snd h, fun h => Prod.ext rfl h⟩

/-- **`Λ_v(w) = ½ #{± | w = (P(w), ± v(P(w)))}`**. -/
def signMulti (v : E₀ → Fin 2 → ℝ) (w : A.W) : ℚ≥0 :=
  (Fintype.card Bool : ℚ≥0)⁻¹ *
    ((Finset.univ.filter fun b : Bool => sec v b (A.P w) = w).card : ℚ≥0)

theorem exists_sign_of_signMulti_ne_zero {v : E₀ → Fin 2 → ℝ} {w : Q 2 1 × (Fin 2 → ℝ)}
    (h : signMulti v w ≠ 0) : ∃ b : Bool, w.2 = sgn b • v (w.1 : E₀) := by
  have hc : (Finset.univ.filter fun b : Bool => sec v b (A.P w) = w).card ≠ 0 := fun h0 =>
    h (by unfold signMulti; rw [h0, Nat.cast_zero, mul_zero])
  obtain ⟨b, hb⟩ := Finset.card_ne_zero.1 hc
  exact ⟨b, ((sec_eq_iff v b w).1 (Finset.mem_filter.1 hb).2).symm⟩

/-- `Λ_v` depends on `v(P(w))` up to sign only. -/
theorem signMulti_congr {v v' : E₀ → Fin 2 → ℝ} (w : Q 2 1 × (Fin 2 → ℝ))
    (h : v (w.1 : E₀) = v' (w.1 : E₀) ∨ v (w.1 : E₀) = -v' (w.1 : E₀)) :
    signMulti v w = signMulti v' w := by
  unfold signMulti
  congr 2
  rcases h with h | h
  · congr 1
    refine Finset.filter_congr fun b _ => ?_
    rw [sec_eq_iff, sec_eq_iff, h]
  · refine Finset.card_bij (fun b _ => !b) (fun b hb => ?_) (fun a _ b _ hab => by simpa using hab)
      fun b hb => ⟨!b, ?_, by simp⟩
    · rw [Finset.mem_filter] at hb ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [sec_eq_iff] at hb ⊢
      rw [sgn_not, ← hb.2, h, neg_smul, smul_neg]
    · rw [Finset.mem_filter] at hb ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [sec_eq_iff] at hb ⊢
      rw [sgn_not, ← hb.2, h, neg_smul, smul_neg, neg_neg]

theorem contDiff_sgn_smul {v : E₀ → Fin 2 → ℝ} (hv : ContDiff ℝ ∞ v) (b : Bool) :
    ContDiff ℝ ∞ fun u => sgn b • v u := hv.const_smul (sgn b)

/-- **The tuple `(Λ_v, 𝒰, S, τ)` on a face `F`**: `I_x = {±}`, the sections `x ↦ (x, ± v(x))`,
`τ ≡ [{±} ←id {±} →id {±}]`. -/
def signTuple {v : E₀ → Fin 2 → ℝ} (hv : ContDiff ℝ ∞ v) (F : Set A.Obj) :
    FaceStructuredTuple A F ι where
  Λ := signMulti v
  isFunctor _ _ := rfl
  nbhd x := (A.X.exists_natNbhd_isProperSubset (x : A.Obj) isOpen_univ (mem_univ _)).choose
  isProper x := isProperMap_domRestrict_of_subset_of_isClosed A.X.continuous_src
    (A.X.exists_natNbhd_isProperSubset (x : A.Obj) isOpen_univ (mem_univ _)).choose_spec.2
    (closure_mono inter_subset_left) isClosed_closure
  s _ b := sec v b
  P_s _ _ _ _ := rfl
  equivariant x g b y hy := by
    rw [fibAct_quadSEP, Φ_eq_self _ g hy.1]
    rfl
  rep _ _ _ := rfl
  τ _ _ _ := IndexCorr.ofEquiv (_root_.Equiv.refl Bool)
  locallyConstant _ _ _ _ := Eventually.of_forall fun _ => rfl
  finite _ _ := (finite_singleton (IndexCorr.ofEquiv (_root_.Equiv.refl Bool))).subset
    (by rintro _ ⟨_, _, rfl⟩; rfl)
  swap _ _ _ _ := (IndexCorr.swap_ofEquiv (_root_.Equiv.refl Bool)).symm
  diag _ _ _ _ := congrArg IndexCorr.ofEquiv (_root_.Equiv.ext fun _ => rfl)
  biact _ _ _ _ _ _ := (IndexCorr.map_refl _).symm
  compat _ _ φ _ := IndexCorr.sat_ofEquiv _ fun _ => (fibAct_quadSEP φ _).symm
  isFaceRelScPlus _ b :=
    (isFaceScPlusSectionOn_graphSec (contDiff_sgn_smul hv b) _).isFaceRelScPlusSectionOn

/-- The coordinate face `{xᵢ = 0}`. -/
def Z (i : Fin 2) : Set A.Obj := {p : Q 2 1 | coord i p = 0}

/-- The principal part on the face `F`: `φ₁` if `F ⊆ {x₁ = 0}`, else `φ₂`. -/
def germMap (F : Set A.Obj) : E₀ → Fin 2 → ℝ := if F ⊆ Z 0 then φ₁ else φ₂

theorem contDiff_germMap (F : Set A.Obj) : ContDiff ℝ ∞ (germMap F) := by
  unfold germMap; split_ifs
  exacts [contDiff_φ₁, contDiff_φ₂]

/-- **The assignment `F ↦ Λ̃_F`**: the class of the tuple with the sections `± germMap F`. -/
def Λt (F : Set A.Obj) (_ : A.X.IsEpFace F) : FaceStructuredMultisection A F :=
  Quotient.mk (FaceStructuredTuple.setoid A F) ⟨ι, signTuple (contDiff_germMap F) F⟩

/-- The functor of the class `Λt F` over `F`. -/
theorem Λt_out_Λ {F : Set A.Obj} (hF : A.X.IsEpFace F) {w : A.W} (hw : A.P w ∈ F) :
    (Quotient.out (Λt F hF)).2.Λ w = signMulti (germMap F) w :=
  (Quotient.exact (Quotient.out_eq (Λt F hF))).1 w hw

/-- A face which does not lie in `{x₁ = 0}` lies in `{x₂ = 0}`. -/
theorem subset_Z_one {F : Set A.Obj} (hF : A.X.IsEpFace F) (h : ¬ F ⊆ Z 0) : F ⊆ Z 1 := by
  obtain ⟨i, hi⟩ := isEpFace_subset_coord hF
  fin_cases i
  · exact absurd hi h
  · exact hi

/-- **The assignment is compatible** (Definition 14.6.2): `Λ̃_F|F' = Λ̃_{F'}|F` as classes over
`F ∩ F'`.  The functors agree on the corner because `{±h(t)} = {±g(t)}`; the index sets are
`{±}` and the correspondences are `[id]` on both sides. -/
theorem isCompatibleAssignment_Λt : IsCompatibleAssignment Λt := by
  intro F hF F' hF'
  refine Quotient.sound ⟨fun w hw => ?_,
    fun x => ((signTuple (contDiff_germMap F) F).nbhd ⟨x, x.2.1⟩).U ∩
      ((signTuple (contDiff_germMap F') F').nbhd ⟨x, x.2.2⟩).U,
    fun x => ((signTuple (contDiff_germMap F) F).nbhd _).isOpen_U.inter
      ((signTuple (contDiff_germMap F') F').nbhd _).isOpen_U,
    fun x => ⟨((signTuple (contDiff_germMap F) F).nbhd _).mem_U,
      ((signTuple (contDiff_germMap F') F').nbhd _).mem_U⟩,
    fun x y hy => ⟨⟨hy.1.1, hy.2⟩, ⟨hy.1.2, hy.2⟩⟩, fun _ => rfl,
    fun _ _ _ _ => (IndexCorr.map_cast_rfl _).symm⟩
  change signMulti (germMap F) w = signMulti (germMap F') w
  refine signMulti_congr w ?_
  unfold germMap
  by_cases h : F ⊆ Z 0 <;> by_cases h' : F' ⊆ Z 0
  · rw [if_pos h, if_pos h']; exact Or.inl rfl
  · rw [if_pos h, if_neg h']
    exact φ₁_eq_or (h hw.1) (subset_Z_one hF' h' hw.2)
  · rw [if_neg h, if_pos h']
    rcases φ₁_eq_or (h' hw.2) (subset_Z_one hF h hw.1) with e | e
    · exact Or.inl e.symm
    · exact Or.inr (neg_eq_iff_eq_neg.2 e).symm
  · rw [if_neg h, if_neg h']; exact Or.inl rfl

/-! ### Two paths through the corner -/

/-- The point `(max a 0, max b 0, t)` of `X`. -/
def pt (a b t : ℝ) : Q 2 1 :=
  ⟨((![max a 0, max b 0] : Fin 2 → ℝ), fun _ => t), fun i => by
    fin_cases i
    · exact le_max_right a 0
    · exact le_max_right b 0⟩

theorem continuous_pt {α : Type*} [TopologicalSpace α] {a b t : α → ℝ} (ha : Continuous a)
    (hb : Continuous b) (ht : Continuous t) : Continuous fun x => pt (a x) (b x) (t x) := by
  refine Continuous.subtype_mk
    (Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun _ => ht)) _
  fin_cases i
  · exact ha.max continuous_const
  · exact hb.max continuous_const

theorem mem_boundary_of_coord {p : Q 2 1} {i : Fin 2} (h : coord i p = 0) :
    (show A.Obj from p) ∈ A.X.PObj.boundary := by
  change 1 ≤ dq 2 (rnSc 1) p
  rw [dq_eq]
  exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩

theorem dist_pt_lt {a b t ρ : ℝ} (hρ : 0 < ρ) (ha : max a 0 < ρ) (hb : max b 0 < ρ)
    (ht : |t| < ρ) : dist (pt a b t) (pt 0 0 0) < ρ := by
  rw [Subtype.dist_eq]
  change dist (((![max a 0, max b 0] : Fin 2 → ℝ), fun _ : Fin 1 => t) :
    (Fin 2 → ℝ) × (Fin 1 → ℝ)) ((![max 0 0, max 0 0] : Fin 2 → ℝ), fun _ : Fin 1 => 0) < ρ
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · refine (dist_pi_lt_iff hρ).2 fun i => ?_
    fin_cases i
    · simpa [Real.dist_eq, abs_of_nonneg (le_max_right a 0)] using ha
    · simpa [Real.dist_eq, abs_of_nonneg (le_max_right b 0)] using hb
  · refine (dist_pi_lt_iff hρ).2 fun _ => ?_
    simpa [Real.dist_eq] using ht

/-- The path `u ↦ (0, r(1 − u²), r u)` in `{x₁ = 0}`, from `(0, 0, −r)` to `(0, 0, r)`. -/
def path₁ (r u : ℝ) : Q 2 1 := pt 0 (r * (1 - u ^ 2)) (r * u)

/-- The path `u ↦ (r(1 − u²), 0, r u)` in `{x₂ = 0}`, from `(0, 0, −r)` to `(0, 0, r)`. -/
def path₂ (r u : ℝ) : Q 2 1 := pt (r * (1 - u ^ 2)) 0 (r * u)

theorem continuous_path₁ (r : ℝ) : Continuous (path₁ r) :=
  continuous_pt continuous_const
    (continuous_const.mul (continuous_const.sub (continuous_id.pow 2)))
    (continuous_const.mul continuous_id)

theorem continuous_path₂ (r : ℝ) : Continuous (path₂ r) :=
  continuous_pt (continuous_const.mul (continuous_const.sub (continuous_id.pow 2)))
    continuous_const (continuous_const.mul continuous_id)

theorem coord_zero_path₁ (r u : ℝ) : coord 0 (path₁ r u) = 0 := max_self 0

theorem coord_one_path₂ (r u : ℝ) : coord 1 (path₂ r u) = 0 := max_self 0

theorem path₁_one (r : ℝ) : path₁ r 1 = pt 0 0 r := by simp [path₁]

theorem path₂_one (r : ℝ) : path₂ r 1 = pt 0 0 r := by simp [path₂]

theorem path₁_neg_one (r : ℝ) : path₁ r (-1) = pt 0 0 (-r) := by simp [path₁]

theorem path₂_neg_one (r : ℝ) : path₂ r (-1) = pt 0 0 (-r) := by simp [path₂]

theorem bump_pos {r u : ℝ} (hr : 0 < r) (hu : u ∈ Ioo (-1 : ℝ) 1) : 0 < r * (1 - u ^ 2) :=
  mul_pos hr (by nlinarith [hu.1, hu.2])

theorem path₁_mem_part {r u : ℝ} (hr : 0 < r) (hu : u ∈ Ioo (-1 : ℝ) 1) :
    path₁ r u ∈ part (0 : Fin 2) := by
  refine ⟨max_self 0, fun l hl => ?_⟩
  fin_cases l
  · exact absurd rfl hl
  · exact lt_max_of_lt_left (bump_pos hr hu)

theorem path₂_mem_part {r u : ℝ} (hr : 0 < r) (hu : u ∈ Ioo (-1 : ℝ) 1) :
    path₂ r u ∈ part (1 : Fin 2) := by
  refine ⟨max_self 0, fun l hl => ?_⟩
  fin_cases l
  · exact lt_max_of_lt_left (bump_pos hr hu)
  · exact absurd rfl hl

theorem dist_path₁_lt {r ρ u : ℝ} (hr : 0 < r) (hrρ : r < ρ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    dist (path₁ r u) (pt 0 0 0) < ρ := by
  have hρ : 0 < ρ := hr.trans hrρ
  refine dist_pt_lt hρ (by simpa using hρ) (max_lt ?_ hρ) (abs_lt.2 ⟨?_, ?_⟩)
  · nlinarith [sq_nonneg u]
  · nlinarith [hu.1]
  · nlinarith [hu.2]

theorem dist_path₂_lt {r ρ u : ℝ} (hr : 0 < r) (hrρ : r < ρ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    dist (path₂ r u) (pt 0 0 0) < ρ := by
  have hρ : 0 < ρ := hr.trans hrρ
  refine dist_pt_lt hρ (max_lt ?_ hρ) (by simpa using hρ) (abs_lt.2 ⟨?_, ?_⟩)
  · nlinarith [sq_nonneg u]
  · nlinarith [hu.1]
  · nlinarith [hu.2]

theorem φ₁_path₁_zero (r u : ℝ) : φ₁ (path₁ r u : E₀) 0 = hfun (r * u) := rfl

theorem φ₂_path₂_zero (r u : ℝ) : φ₂ (path₂ r u : E₀) 0 = gfun (r * u) := rfl

theorem φ₁_path₁_ne_zero {r u : ℝ} (hr : 0 < r) : φ₁ (path₁ r u : E₀) ≠ 0 := by
  intro h0
  have e0 : hfun (r * u) = 0 := congrFun h0 0
  have e1 : max (r * (1 - u ^ 2)) 0 = 0 := congrFun h0 1
  by_cases hu0 : u = 0
  · subst hu0
    have : r ≤ 0 := by simpa using e1
    linarith
  · exact hfun_ne_zero (mul_ne_zero hr.ne' hu0) e0

theorem φ₂_path₂_ne_zero {r u : ℝ} (hr : 0 < r) : φ₂ (path₂ r u : E₀) ≠ 0 := by
  intro h0
  have e0 : gfun (r * u) = 0 := congrFun h0 0
  have e1 : max (r * (1 - u ^ 2)) 0 = 0 := congrFun h0 1
  by_cases hu0 : u = 0
  · subst hu0
    have : r ≤ 0 := by simpa using e1
    linarith
  · exact gfun_ne_zero (mul_ne_zero hr.ne' hu0) e0

/-! ### The glued functor is not an sc⁺-multisection over `∂X` -/

/-- **No functor which agrees with `Λ_F` over every face `F` is an sc⁺-multisection over `∂X`**
(Definition 14.1.3).  A section `sᵢ` of a symmetric structure near the corner `0` would be
`ε (h, x₂)` along `path₁` and `δ (g, x₁)` along `path₂` with constant signs `ε`, `δ`; the two
paths have the same end points `(0, 0, ± r)`, where `h(r) = g(r)` and `h(−r) = −g(−r)` are not
zero. -/
theorem not_isBoundaryScPlusMultisection_of_eq_on_faces {Λ : A.W → ℚ≥0}
    (hΛF : ∀ F (_ : A.X.IsEpFace F) w, A.P w ∈ F → Λ w = signMulti (germMap F) w) :
    ¬ IsBoundaryScPlusMultisection A Λ := by
  intro hΛ
  have hx0 : (show A.Obj from pt 0 0 0) ∈ A.X.PObj.boundary :=
    mem_boundary_of_coord (i := 0) (max_self 0)
  obtain ⟨V, -, ⟨S⟩⟩ := hΛ.2 _ hx0
  have hopen : IsOpen (show Set (Q 2 1) from V.U) := V.isOpen_U
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen (pt 0 0 0) V.mem_U
  obtain ⟨i⟩ := S.nonempty
  have hr : 0 < ρ / 2 := half_pos hρ
  have hrρ : ρ / 2 < ρ := half_lt_self hρ
  set r := ρ / 2 with hrdef
  have hU₁ : ∀ u ∈ Icc (-1 : ℝ) 1, path₁ r u ∈ V.bdry ∧ coord 0 (path₁ r u) = 0 := fun u hu =>
    ⟨⟨hball (Metric.mem_ball.2 (dist_path₁_lt hr hrρ hu)),
      mem_boundary_of_coord (coord_zero_path₁ r u)⟩, coord_zero_path₁ r u⟩
  have hU₂ : ∀ u ∈ Icc (-1 : ℝ) 1, path₂ r u ∈ V.bdry ∧ coord 1 (path₂ r u) = 0 := fun u hu =>
    ⟨⟨hball (Metric.mem_ball.2 (dist_path₂_lt hr hrρ hu)),
      mem_boundary_of_coord (coord_one_path₂ r u)⟩, coord_one_path₂ r u⟩
  set v : Q 2 1 → Fin 2 → ℝ := fun p => (show Q 2 1 × (Fin 2 → ℝ) from S.s i p).2 with hvdef
  have hv₁ : ContinuousOn (fun u => v (path₁ r u)) (Icc (-1) 1) :=
    continuousOn_snd_comp_of_isFaceScPlusSectionOn (S.isFaceScPlus i) (continuous_path₁ r) 0 hU₁
  have hv₂ : ContinuousOn (fun u => v (path₂ r u)) (Icc (-1) 1) :=
    continuousOn_snd_comp_of_isFaceScPlusSectionOn (S.isFaceScPlus i) (continuous_path₂ r) 1 hU₂
  -- the values of `sᵢ` on a face are `± germMap F`
  have hval : ∀ y : Q 2 1, y ∈ V.bdry → ∀ F, A.X.IsEpFace F → y ∈ F →
      ∃ b : Bool, v y = sgn b • germMap F (y : E₀) := by
    intro y hy F hF hyF
    have hP : A.P (S.s i y) = y := S.P_s i hy
    have hne : Λ (S.s i y) ≠ 0 := by
      rw [S.rep (S.s i y) (by rw [hP]; exact hy), hP]
      refine mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) ?_
      exact Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, by simp⟩)
    rw [hΛF F hF _ (by rw [hP]; exact hyF)] at hne
    obtain ⟨b, hb⟩ := exists_sign_of_signMulti_ne_zero hne
    have hP' : (show Q 2 1 × (Fin 2 → ℝ) from S.s i y).1 = y := hP
    exact ⟨b, hb.trans (congrArg (fun z : Q 2 1 => sgn b • germMap F (z : E₀)) hP')⟩
  have hpart₁ : ∀ u ∈ Ioo (-1 : ℝ) 1, ∃ b : Bool,
      v (path₁ r u) = sgn b • φ₁ (path₁ r u : E₀) := by
    intro u hu
    obtain ⟨F, hF, hyF, hFZ⟩ := exists_isEpFace_mem_of_part (k := 2) (path₁_mem_part hr hu)
    obtain ⟨b, hb⟩ := hval _ (hU₁ u (Ioo_subset_Icc_self hu)).1 F hF hyF
    have hF0 : F ⊆ Z 0 := hFZ
    rw [germMap, if_pos hF0] at hb
    exact ⟨b, hb⟩
  have hpart₂ : ∀ u ∈ Ioo (-1 : ℝ) 1, ∃ b : Bool,
      v (path₂ r u) = sgn b • φ₂ (path₂ r u : E₀) := by
    intro u hu
    have hp := path₂_mem_part hr hu
    obtain ⟨F, hF, hyF, -⟩ := exists_isEpFace_mem_of_part (k := 2) hp
    obtain ⟨b, hb⟩ := hval _ (hU₂ u (Ioo_subset_Icc_self hu)).1 F hF hyF
    have hF0 : ¬ F ⊆ Z 0 := fun h0 => (hp.2 0 (by decide)).ne' (h0 hyF)
    rw [germMap, if_neg hF0] at hb
    exact ⟨b, hb⟩
  have hφ₁c : ContinuousOn (fun u => φ₁ (path₁ r u : E₀)) (Icc (-1) 1) :=
    (contDiff_φ₁.continuous.comp (continuous_subtype_val.comp (continuous_path₁ r))).continuousOn
  have hφ₂c : ContinuousOn (fun u => φ₂ (path₂ r u : E₀)) (Icc (-1) 1) :=
    (contDiff_φ₂.continuous.comp (continuous_subtype_val.comp (continuous_path₂ r))).continuousOn
  obtain ⟨b₁, hm₁, hp₁⟩ := exists_sign_endpoints hv₁ hφ₁c (fun _ _ => φ₁_path₁_ne_zero hr) hpart₁
  obtain ⟨b₂, hm₂, hp₂⟩ := exists_sign_endpoints hv₂ hφ₂c (fun _ _ => φ₂_path₂_ne_zero hr) hpart₂
  have he := expNegInvGlue.pos_of_pos hr
  have a1 : v (path₁ r 1) 0 = sgn b₁ * hfun (r * 1) := congrFun hp₁ 0
  have a2 : v (path₂ r 1) 0 = sgn b₂ * gfun (r * 1) := congrFun hp₂ 0
  have a3 : v (path₁ r (-1)) 0 = sgn b₁ * hfun (r * -1) := congrFun hm₁ 0
  have a4 : v (path₂ r (-1)) 0 = sgn b₂ * gfun (r * -1) := congrFun hm₂ 0
  rw [path₁_one, mul_one, hfun_of_nonneg hr.le] at a1
  rw [path₂_one, mul_one, gfun_of_nonneg hr.le] at a2
  rw [path₁_neg_one, mul_neg_one, hfun_of_nonpos (neg_nonpos.2 hr.le), neg_neg] at a3
  rw [path₂_neg_one, mul_neg_one, gfun_of_nonpos (neg_nonpos.2 hr.le), neg_neg] at a4
  have h1 : sgn b₁ * expNegInvGlue r = sgn b₂ * expNegInvGlue r := a1.symm.trans a2
  have h2 : sgn b₁ * expNegInvGlue r = sgn b₂ * -expNegInvGlue r := a3.symm.trans a4
  have h3 : sgn b₁ * expNegInvGlue r = 0 := by linarith
  exact mul_ne_zero (sgn_ne_zero b₁) he.ne' h3

/-! ### Theorem 14.6.3 for classes -/

/-- **2021 Theorem 14.6.3, p. 682 (2017: Theorem 14.4), for a compatible assignment of classes**
(Definition 14.6.2 with the equivalence of Definition 13.3.8): the functor `Λ(w) = Λ_F(w)`,
`P(w) ∈ F`, is structurable over `∂X`. -/
def theorem_14_6_3_class_statement (B : SEP.{0}) : Prop :=
  ∀ L : ∀ F, B.X.IsEpFace F → FaceStructuredMultisection B F, IsCompatibleAssignment L →
    ∃ Λ : B.W → ℚ≥0, IsBoundaryStructurable B Λ ∧
      ∀ F (hF : B.X.IsEpFace F) w, B.P w ∈ F → Λ w = (Quotient.out (L F hF)).2.Λ w

/-- `X = [0, ∞)² × ℝ` with only identities is a tame face-structured ep-groupoid
(Example 11.1.4 (1)). -/
theorem isEpFaceStructured_A : A.X.IsEpFaceStructured :=
  (EpGroupoid.Examples.example_11_1_4 (rnSc 1)).1

/-- **Theorem 14.6.3 for a compatible assignment of classes does not hold as we read it**: on
`W = X × ℝ² → X = [0, ∞)² × ℝ` (tame, face-structured, paracompact orbit space, sc-smooth
partitions of unity) the assignment `Λt` is compatible, and no functor which agrees with the
`Λ_F` over the faces is an sc⁺-multisection over `∂X`. -/
theorem not_theorem_14_6_3_class_statement :
    A.X.IsEpFaceStructured ∧ A.X.HasParacompactOrbitSpace ∧
      A.X.PObj.AdmitsScPartitionsOfUnity ∧ IsCompatibleAssignment Λt ∧
      (¬ ∃ Λ : A.W → ℚ≥0, IsBoundaryScPlusMultisection A Λ ∧
        ∀ F (hF : A.X.IsEpFace F) w, A.P w ∈ F → Λ w = (Quotient.out (Λt F hF)).2.Λ w) ∧
      ¬ theorem_14_6_3_class_statement A := by
  have key : ¬ ∃ Λ : A.W → ℚ≥0, IsBoundaryScPlusMultisection A Λ ∧
      ∀ F (hF : A.X.IsEpFace F) w, A.P w ∈ F → Λ w = (Quotient.out (Λt F hF)).2.Λ w := by
    rintro ⟨Λ, hΛ, hF⟩
    exact not_isBoundaryScPlusMultisection_of_eq_on_faces
      (fun F hF' w hw => (hF F hF' w hw).trans (Λt_out_Λ hF' hw)) hΛ
  refine ⟨isEpFaceStructured_A, hasParacompactOrbitSpace_quadSEP 2 1 2,
    admitsScPartitionsOfUnity_quadSEP 2 1 2, isCompatibleAssignment_Λt, key, fun h => ?_⟩
  obtain ⟨Λ, hΛ, hF⟩ := h Λt isCompatibleAssignment_Λt
  exact key ⟨Λ, hΛ.1, hF⟩

/-- **No representatives of the classes `Λt F` agree on the intersections of faces**: there is no
`CompatibleFaceData` (one index family, sections and correspondences equal on `F ∩ F'`) whose
tuples represent the classes `Λt F`.  So the step on p. 682 (`sˣ_{F,i} = sˣ_{F',i}` on
`U_F(x) ∩ U_{F'}(x)`) does not follow from the compatibility of Definition 14.6.2 as we read
it. -/
theorem not_exists_compatibleFaceData :
    ¬ ∃ D : CompatibleFaceData A, ∀ F (hF : A.X.IsEpFace F),
      Quotient.mk (FaceStructuredTuple.setoid A F) ⟨D.ι, D.T F hF⟩ = Λt F hF := by
  rintro ⟨D, hD⟩
  obtain ⟨hΛ, hF⟩ := D.theorem_14_6_3_hyp isEpFaceStructured_A
    (hasParacompactOrbitSpace_quadSEP 2 1 2)
  refine not_isBoundaryScPlusMultisection_of_eq_on_faces (fun F hF' w hw => ?_) hΛ.1
  rw [hF F hF' w hw]
  exact (Quotient.exact (hD F hF')).1 w hw

/-! ### A witness with a corner for the form which holds -/

/-- `φ₃(x₁, x₂, t) = (h(t), x₁)`: it agrees with `φ₁` on the corner `{x₁ = x₂ = 0}`. -/
def φ₃ (u : E₀) : Fin 2 → ℝ := ![hfun (u.2 0), u.1 0]

theorem contDiff_φ₃ : ContDiff ℝ ∞ φ₃ := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · change ContDiff ℝ ∞ fun u : E₀ => hfun (u.2 0)
    exact contDiff_hfun.comp ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd)
  · change ContDiff ℝ ∞ fun u : E₀ => u.1 0
    exact (contDiff_apply ℝ ℝ (0 : Fin 2)).comp contDiff_fst

theorem φ₁_eq_φ₃ {u : E₀} (h0 : u.1 0 = 0) (h1 : u.1 1 = 0) : φ₁ u = φ₃ u := by
  funext i; fin_cases i <;> simp [φ₁, φ₃, h0, h1]

/-- The principal part on the face `F`: `φ₁` if `F ⊆ {x₁ = 0}`, else `φ₃`. -/
def germMapEq (F : Set A.Obj) : E₀ → Fin 2 → ℝ := if F ⊆ Z 0 then φ₁ else φ₃

theorem contDiff_germMapEq (F : Set A.Obj) : ContDiff ℝ ∞ (germMapEq F) := by
  unfold germMapEq; split_ifs
  exacts [contDiff_φ₁, contDiff_φ₃]

theorem germMapEq_eq {F F' : Set A.Obj} (hF : A.X.IsEpFace F) (hF' : A.X.IsEpFace F')
    {y : Q 2 1} (hy : y ∈ F ∩ F') : germMapEq F (y : E₀) = germMapEq F' (y : E₀) := by
  unfold germMapEq
  by_cases h : F ⊆ Z 0 <;> by_cases h' : F' ⊆ Z 0
  · rw [if_pos h, if_pos h']
  · rw [if_pos h, if_neg h']
    exact φ₁_eq_φ₃ (h hy.1) (subset_Z_one hF' h' hy.2)
  · rw [if_neg h, if_pos h']
    exact (φ₁_eq_φ₃ (h' hy.2) (subset_Z_one hF h hy.1)).symm
  · rw [if_neg h, if_neg h']

/-- **Compatible face data with a corner and non-zero sections**: on the faces in `{x₁ = 0}` the
sections `±(h(t), x₂)`, on the others `±(h(t), x₁)`; they agree on the corner. -/
def cornerFaceData : CompatibleFaceData A where
  ι := ι
  T F _ := signTuple (contDiff_germMapEq F) F
  Λ_eq F hF F' hF' w hw := signMulti_congr w (Or.inl (germMapEq_eq hF hF' hw))
  s_eq F hF F' hF' x _ _ b y hy := by
    have e := germMapEq_eq hF hF' (y := y) ⟨hy.1.2, hy.2.2⟩
    exact Prod.ext rfl (congrArg (fun z : Fin 2 → ℝ => sgn b • z) e)
  τ_eq _ _ _ _ _ _ _ _ _ _ _ _ := rfl

theorem signMulti_sec_pos (v : E₀ → Fin 2 → ℝ) (b : Bool) (y : A.Obj) :
    0 < signMulti v (sec v b y) := by
  unfold signMulti
  refine mul_pos (inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos)) (Nat.cast_pos.2 ?_)
  exact Finset.card_pos.2 ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩

/-- **Theorem 14.6.3 for compatible representatives, at a corner with non-zero sections**: the
glued functor of `cornerFaceData` is structurable over `∂X`, it is `Λ_F` over every face `F`,
and at the point `(0, 0, 1)` of the corner stratum (`d = 2`) it charges a non-zero point of the
fibre. -/
theorem theorem_14_6_3_corner_witness :
    IsBoundaryStructurable A cornerFaceData.Λg ∧
      (∀ F (_ : A.X.IsEpFace F) w, A.P w ∈ F →
        cornerFaceData.Λg w = signMulti (germMapEq F) w) ∧
      ∃ y : A.Obj, A.X.PObj.degIndex y = 2 ∧ ∃ w, A.P w = y ∧ w ≠ fiberZero A.P y ∧
        0 < cornerFaceData.Λg w := by
  obtain ⟨hΛ, hF⟩ := cornerFaceData.theorem_14_6_3_hyp isEpFaceStructured_A
    (hasParacompactOrbitSpace_quadSEP 2 1 2)
  refine ⟨hΛ, hF, pt 0 0 1, ?_, ?_⟩
  · change dq 2 (rnSc 1) (pt 0 0 1) = 2
    rw [dq_eq, Finset.filter_true_of_mem fun i _ => by fin_cases i <;> exact max_self 0]
    rfl
  · have hb : (show A.Obj from pt 0 0 1) ∈ A.X.PObj.boundary :=
      mem_boundary_of_coord (i := 0) (max_self 0)
    obtain ⟨F, hFace, hyF⟩ := exists_isEpFace_mem isEpFaceStructured_A hb
    refine ⟨sec (germMapEq F) true (pt 0 0 1), rfl, fun h => ?_, ?_⟩
    · have h2 : sgn true • germMapEq F (pt 0 0 1 : E₀) = 0 := congrArg Prod.snd h
      have h3 : germMapEq F (pt 0 0 1 : E₀) 0 = 0 := by
        have := congrFun h2 0
        simpa [sgn] using this
      have h4 : germMapEq F (pt 0 0 1 : E₀) 0 = hfun 1 := by
        unfold germMapEq; split_ifs <;> rfl
      exact hfun_ne_zero one_ne_zero (h4.symm.trans h3)
    · rw [hF F hFace (sec (germMapEq F) true (pt 0 0 1)) hyF]
      exact signMulti_sec_pos _ _ _

end FaceCorner

end Polyfold
