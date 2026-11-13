import Polyfold.Chapter4.RemarkLocalForm
import Polyfold.Chapter2.PartialConeQuadrant

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §4.2, **Remark 4.2.2**
(p. 184; preprint: Remark 4.14, p. 157), the 2021 wording: **`A` is a manifold near the points
with `d_A(a) = 0`**.  Gap G.33, row V4.32 (Findings, Chapter 4, items 61, 165).

# Remark 4.2.2 near the points with `d_A = 0`

## The text, paraphrased

(2021 Remark 4.2.2) A smooth finite-dimensional submanifold `A ⊆ X` is a sub-M-polyfold, with
degeneracy index `d_A ≤ d_X`.  Near points `a ∈ A` with `d_A(a) = 0` it has a natural smooth
manifold structure; near points with `d_A(a) = 1`, a natural structure of a smooth manifold with
boundary.

## What is formalized

* `MPolyfold.IsSmoothSubmanifold.isSmoothSubmanifold_univ_subPolyfold`: `A`, with its induced
  M-polyfold structure, is a smooth finite-dimensional submanifold of itself (`s = id` is an
  sc⁺-retraction, by Proposition 4.2.3 (4): `A = A_∞` and `1₀¹ : A → A¹` is sc-smooth).
* `MPolyfold.remark_4_2_2_dA_zero`: the open piece `{d_A = 0}` of `A` is a smooth
  finite-dimensional submanifold of `A` whose induced structure has a corner structure
  (Definition 4.1.1) and degeneracy index `0` everywhere: a manifold without boundary.  No
  tameness of `X` or of `A` is used.
* `MPolyfold.remark_4_2_2_dA_zero_near`: the pointwise form at a point with `d_A(a) = 0`.
* `MPolyfold.remark_4_2_2_dA_one_of_isTame`: **if the induced structure of `A` is tame**, `A` has a
  corner structure, and every `a` with `d_A(a) = 1` has an open neighbourhood on which `d_A ≤ 1`
  (a manifold with boundary near `a`).  Through `MPolyfold.hasCornerStructure_of_isTame`: a tame
  M-polyfold with `X₀ = X_∞` and `1₀¹` sc-smooth has a corner structure, since the good position
  of `T₀O` assumed in Theorem 4.1.2 (2) holds automatically in a tame centred chart
  (`ScRetraction.isInGoodPosition_rangeS_of_isTameWith`, from
  `ScRetraction.interior_rangeS_scDeriv_zero_nonempty` and Lemma 4.2.8).

The preprint wording (`d_X(a) = 0`, `remark_4_2_2_near` in `RemarkLocalForm.lean`) is the special
case `d_A ≤ d_X` (Lemma 2.4.6); the new statement covers e.g. the parabola `{(y², y)}` in
`[0, ∞) × ℝ`, where `d_X = 1` and `d_A = 0` at the origin.

## What the text leaves implicit, and the choices made

* "Near `a`" is read in `A`: on the open neighbourhood `{d_A = 0}` of `a` in `A` (open since
  `d_A` is upper semicontinuous, `MPolyfold.isOpen_interior` for the induced structure).
* *Proof* of the `d_A = 0` statement: `remark_4_2_2_interior` (the preprint form, `d_X = 0`)
  applied to the M-polyfold `A` itself and its submanifold `A`: there `d_X` becomes `d_A`.  This
  is where the sc⁺ property of `A` enters: the charts of the induced structure realizing
  `d_A(a) = 0` are arbitrary charts compatible with it, and their models are sc⁺-retracts by
  Proposition 4.2.3 (4) and Proposition 4.1.8 (`isScSmoothMap_toLevelOne_iff`).
* The sentence on `d_A(a) = 1` without tameness of `A` is in `GapP1_Remark422One.lean`
  (`remark_4_2_2_dA_one`): in a chart of `A` realizing `d_A(a) = 1`, re-centred at `a`, with
  boundary coordinate `ℓ`, the tangent space `N = T_aA` is in good position when `ℓ|_N ≠ 0` (a
  complement inside `ker ℓ`), and `ℓ|_N = 0` cannot occur, since then `A` is near `a` a graph over
  an open subset of `N` and `d_A(a) = 0` (the argument of 2021 Lemma 9.2.13).
-/

open Set

noncomputable section

namespace Polyfold

/-! ### Good position of the whole tangent space of a tame retract -/

section TameGoodPosition

variable {E : ScBanach} {C : Set (E 0)} {n : ℕ} {Wq : ScBanach}

/-- **The partial cone `T₀O ∩ C` has non-empty interior in `T₀O`** at a point `0 ∈ O₁` of a
retract `O = r(U)` (so `C_0 = C`): `Dr(0)` maps `C` into `C` (the sign argument,
`ScRetraction.scDeriv_mapsTo_partialQuadrant`), and for `c` in the interior of `C` with
`B(c, δ) ⊆ C`, the ball of radius `δ` about `Dr(0)c` in `T₀O = Dr(0)E` is `Dr(0)` of
`c + (ball in T₀O)`, hence in `C`. -/
theorem ScRetraction.interior_rangeS_scDeriv_zero_nonempty (R : ScRetraction E C)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (hT : C = T 0 ⁻¹' quadrant n Wq 0)
    (h0 : (0 : E 1) ∈ E.lvlSet R.retract 1) :
    (interior (Subtype.val ⁻¹' C : Set (rangeS (scDeriv R.U R 0)))).Nonempty := by
  set π := scDeriv R.U R 0 with hπdef
  have hπC : MapsTo π C C := by
    have := R.scDeriv_mapsTo_partialQuadrant T hT h0
    rwa [map_zero, partialQuadrantAtWith_zero, ← hT] at this
  have hππ : ∀ v, π (π v) = π v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self h0)
  have hCq : IsPartialQuadrant E C := ⟨n, Wq, T, hT⟩
  obtain ⟨c, hc⟩ := hCq.interior_lvlSet_nonempty 0
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior c hc
  refine ⟨⟨π c, c, rfl⟩, mem_interior.2 ⟨Subtype.val ⁻¹' Metric.ball (π c) δ, ?_,
    Metric.isOpen_ball.preimage continuous_subtype_val, Metric.mem_ball_self hδ⟩⟩
  rintro ⟨w, u, rfl⟩ hw
  have hw' : dist (π u) (π c) < δ := hw
  have hcm : c + (π u - π c) ∈ C := by
    refine interior_subset (hball ?_)
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, ← dist_eq_norm]
    exact hw'
  have himg : π (c + (π u - π c)) = π u := by
    rw [map_add, map_sub, hππ, hππ, add_sub_cancel]
  change π u ∈ C
  rw [← himg]
  exact hπC hcm

/-- **The tangent space of a tame retract at a centred point is in good position** (Definition
3.1.24): for a tame retraction `r` (presentation `T`) with `0 ∈ O₁`, `T₀O = Dr(0)E` is in good
position to `C` in `E`.  Inside `T₀O` the whole space is in good position to `T₀O ∩ C` (the
interior is non-empty, `interior_rangeS_scDeriv_zero_nonempty`; the complement is `0`), and
Lemma 4.2.8 with the complement `(1 − Dr(0))E ⊆ E₀` (Proposition 2.5.3) gives good position in
`E`. -/
theorem ScRetraction.isInGoodPosition_rangeS_of_isTameWith (R : ScRetraction E C)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (hT : C = T 0 ⁻¹' quadrant n Wq 0)
    (hRt : R.IsTameWith T) (h0 : (0 : E 1) ∈ E.lvlSet R.retract 1) :
    IsInGoodPosition E C (rangeS (scDeriv R.U R 0)) := by
  have hs0 : (0 : E 1) ∈ E.smoothLvl 1 := by
    change E.toBase 1 0 ∈ (E.smooth : Set (E 0))
    rw [map_zero]; exact E.smooth.zero_mem
  have hK := (proposition_2_5_3 hT hRt h0 hs0).1
  rw [map_zero] at hK
  have hππ : ∀ v, scDeriv R.U R 0 (scDeriv R.U R 0 v) = scDeriv R.U R 0 v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self h0)
  refine (lemma_4_2_8 T hT (scDeriv R.U R 0) hππ hK
    ⟨le_rfl, R.interior_rangeS_scDeriv_zero_nonempty T hT h0, ⊥, bot_le, inf_bot_eq _,
      sup_bot_eq _, 1, one_pos, fun x _ p hp _ => ?_⟩).1
  rw [Submodule.mem_bot] at hp
  rw [hp, add_zero]

end TameGoodPosition

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **A smooth finite-dimensional submanifold is a smooth finite-dimensional submanifold of
itself** (for its induced structure, Proposition 2.3.19): `s = id` on `V = A` is an
sc⁺-retraction, since `A = A_∞` and `1₀¹ : A → A¹` is sc-smooth (Proposition 4.2.3 (4),
`proposition_4_2_3_four`). -/
theorem IsSmoothSubmanifold.isSmoothSubmanifold_univ_subPolyfold {A : Set X}
    (hA : P.IsSmoothSubmanifold A) [ParacompactSpace A] :
    (subPolyfold hA.isSubMPolyfold).IsSmoothSubmanifold univ := by
  intro a _
  have h1 : a ∈ (subPolyfold hA.isSubMPolyfold).levelSet 1 :=
    (hA.mem_levelSet_subPolyfold_iff a 1).2 (hA.mem_levelSet_one a.2)
  obtain ⟨hsm, -⟩ := hA.proposition_4_2_3_four ((subPolyfold hA.isSubMPolyfold).levelMk 1 a h1)
  refine ⟨univ, isOpen_univ, mem_univ a, id, ⟨isScSmoothMap_id, fun _ _ => mem_univ _,
    fun _ _ => rfl, fun x _ => smoothSet_subset_levelSet 1 (hsm x),
    fun x₀ => (hA.proposition_4_2_3_four x₀).2⟩, by simp⟩

/-- **2021 Remark 4.2.2, p. 184, near the points with `d_A = 0`** (the 2021 wording; preprint:
Remark 4.14, p. 157, with `d_X`): for a smooth finite-dimensional submanifold `A` of an
M-polyfold `X`, with its induced M-polyfold structure, the open piece `{d_A = 0}` of `A` is a
smooth finite-dimensional submanifold of `A` whose induced structure has a corner structure
(Definition 4.1.1) with degeneracy index `0` at every point: a smooth manifold without boundary.
No tameness.  *Proof*: `remark_4_2_2_interior` for the submanifold `A` of the M-polyfold `A`
(`isSmoothSubmanifold_univ_subPolyfold`), and Lemma 2.4.6 for the degeneracy index. -/
theorem remark_4_2_2_dA_zero {A : Set X} (hA : P.IsSmoothSubmanifold A) [ParacompactSpace A] :
    ∃ hS : (subPolyfold hA.isSubMPolyfold).IsSmoothSubmanifold
        (univ ∩ {b | (subPolyfold hA.isSubMPolyfold).degIndex b = 0}),
      haveI := (subPolyfold hA.isSubMPolyfold).paracompactSpace_subtype
        (univ ∩ {b | (subPolyfold hA.isSubMPolyfold).degIndex b = 0})
      (subPolyfold hS.isSubMPolyfold).HasCornerStructure ∧
        ∀ b, (subPolyfold hS.isSubMPolyfold).degIndex b = 0 := by
  obtain ⟨hS, hC⟩ := remark_4_2_2_interior hA.isSmoothSubmanifold_univ_subPolyfold
  refine ⟨hS, hC, fun b => ?_⟩
  have := (subPolyfold hA.isSubMPolyfold).paracompactSpace_subtype
    (univ ∩ {b | (subPolyfold hA.isSubMPolyfold).degIndex b = 0})
  have h := lemma_2_4_6 hS.isSubMPolyfold b
  have h0 : (subPolyfold hA.isSubMPolyfold).degIndex b.1 = 0 := b.2.2
  omega

/-- **2021 Remark 4.2.2, p. 184, near a point with `d_A(a) = 0`**: every `a ∈ A` with
`d_A(a) = 0` has an open neighbourhood `U` in `A` which is a smooth finite-dimensional
submanifold of `A` whose induced structure is a smooth manifold without boundary (a corner
structure with `d_U ≡ 0`); `U = {d_A = 0}`. -/
theorem remark_4_2_2_dA_zero_near {A : Set X} (hA : P.IsSmoothSubmanifold A) [ParacompactSpace A]
    {a : A} (h0 : (subPolyfold hA.isSubMPolyfold).degIndex a = 0) :
    ∃ U : Set A, IsOpen U ∧ a ∈ U ∧ ∃ hU : (subPolyfold hA.isSubMPolyfold).IsSmoothSubmanifold U,
      haveI := (subPolyfold hA.isSubMPolyfold).paracompactSpace_subtype U
      (subPolyfold hU.isSubMPolyfold).HasCornerStructure ∧
        ∀ b, (subPolyfold hU.isSubMPolyfold).degIndex b = 0 := by
  obtain ⟨hS, hC, hd⟩ := remark_4_2_2_dA_zero hA
  exact ⟨_, isOpen_univ.inter (subPolyfold hA.isSubMPolyfold).isOpen_interior, ⟨mem_univ a, h0⟩,
    hS, hC, hd⟩

/-- **A tame M-polyfold with `X₀ = X_∞` and `1₀¹ : X → X¹` sc-smooth has a corner structure**
(Theorem 4.1.2 (2) ⇒ (1), 2021 p. 182; preprint Theorem 4.2): the good position of `T₀O` to `C`
in a tame chart centred at a point, which the text assumes, holds automatically there
(`ScRetraction.isInGoodPosition_rangeS_of_isTameWith`); `T₀O` is finite-dimensional since the
models are sc⁺-retracts (Proposition 4.1.8, `isScSmoothMap_toLevelOne_iff`; Lemma 4.1.7). -/
theorem hasCornerStructure_of_isTame (hP : P.IsTame) (x₀ : P.Level 1)
    (hsm : ∀ x, x ∈ P.smoothSet) (hmap : P.IsScSmoothMap P.shift (P.toLevelOne x₀)) :
    P.HasCornerStructure := by
  have hplus := (isScSmoothMap_toLevelOne_iff x₀).1 ⟨hsm, hmap⟩
  refine hasCornerStructure_of_centred x₀ hsm hmap fun x => ?_
  obtain ⟨ψ, hψ, hxψ, hψ0, R, hR, hRt⟩ := hP.exists_centredChart (hsm x)
  obtain ⟨n, Wq, T, hT⟩ := ψ.model.isPartialQuadrant
  have h01 : (0 : ψ.model.E 1) ∈ ψ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hR, map_zero, ← hψ0]; exact ψ.mapsTo_model x hxψ
  obtain ⟨t, ht, htp⟩ := hplus ψ hψ
  have hRp : R.IsScPlus := lemma_4_1_5 htp (ht.trans hR.symm)
  refine ⟨ψ, hψ, hxψ, hψ0, rangeS (scDeriv R.U R 0), ?_, lemma_4_1_7_ii hRp h01,
    R.isInGoodPosition_rangeS_of_isTameWith T hT (hRt n Wq T hT) h01⟩
  rw [← hR]
  exact (tangentSpace_eq_coe_submodule R h01).symm

/-- **A smooth finite-dimensional submanifold with tame induced structure is a manifold with
boundary with corners** (Definition 4.1.1): `hasCornerStructure_of_isTame` for the induced
structure, with Proposition 4.2.3 (4).  No good position hypothesis (compare Theorem 4.2.7, where
good position gives the corner structure and the tameness). -/
theorem IsSmoothSubmanifold.hasCornerStructure_of_isTame {A : Set X}
    (hA : P.IsSmoothSubmanifold A) [ParacompactSpace A]
    (htame : (subPolyfold hA.isSubMPolyfold).IsTame) :
    (subPolyfold hA.isSubMPolyfold).HasCornerStructure := by
  by_cases hne : Nonempty A
  · obtain ⟨a₀⟩ := hne
    have h1 : a₀ ∈ (subPolyfold hA.isSubMPolyfold).levelSet 1 :=
      (hA.mem_levelSet_subPolyfold_iff a₀ 1).2 (hA.mem_levelSet_one a₀.2)
    set x₀ := (subPolyfold hA.isSubMPolyfold).levelMk 1 a₀ h1
    obtain ⟨hsm, hmap⟩ := hA.proposition_4_2_3_four x₀
    exact _root_.Polyfold.MPolyfold.hasCornerStructure_of_isTame htame x₀ hsm hmap
  · rw [hasCornerStructure_iff]
    intro x
    exact (hne ⟨x⟩).elim

/-- **2021 Remark 4.2.2, p. 184, near the points with `d_A(a) = 1`, for a tame `A`**: if the induced
structure of `A` is tame (Definition 4.2.6), it has a corner structure (Definition 4.1.1), and
every `a` with `d_A(a) = 1` has the open neighbourhood `{d_A ≤ 1}` in `A`: near `a`, `A` is a
smooth manifold with boundary.  The tameness of `A` is an added hypothesis (see the module
docstring and the hand-over note). -/
theorem remark_4_2_2_dA_one_of_isTame {A : Set X} (hA : P.IsSmoothSubmanifold A)
    [ParacompactSpace A] (htame : (subPolyfold hA.isSubMPolyfold).IsTame) :
    (subPolyfold hA.isSubMPolyfold).HasCornerStructure ∧
      ∀ a : A, (subPolyfold hA.isSubMPolyfold).degIndex a ≤ 1 →
        ∃ U : Set A, IsOpen U ∧ a ∈ U ∧
          ∀ b ∈ U, (subPolyfold hA.isSubMPolyfold).degIndex b ≤ 1 := by
  refine ⟨hA.hasCornerStructure_of_isTame htame, fun a ha => ?_⟩
  obtain ⟨U, hU, hUo, haU⟩ := mem_nhds_iff.1 (lemma_2_4_3 (subPolyfold hA.isSubMPolyfold) a)
  exact ⟨U, hUo, haU, fun b hb => (hU hb).trans ha⟩

end MPolyfold

end Polyfold
