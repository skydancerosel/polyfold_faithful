import Polyfold.Chapter16.P3W3Y_TangentFunctor
import Polyfold.Chapter7.TangentMorphismLinear
import Polyfold.Chapter5.StrongBundleShift

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.2, **Theorem 16.2.4**
(p. 719; 2017: Theorem 16.1): the tangent functor on the polyfold category.  Numbers and pages
are the 2021 text's.

# The tangent of an effective polyfold is effective

## The text, paraphrased

(p. 719) `T` is a functor on the polyfold category: `(Z, c) ↦ T(Z, c)`, `f̂ ↦ T f̂`.  The category
of Definition 16.1.11 is formalized on effective polyfolds (`EffPolyfold`, wave 3), since the
composition of Definition 16.1.10 is well defined there (`PSHom.Equiv.comp_of_isEffective`) and,
as we read it, not in general (`not_definition_16_1_10`).  For `T` to be a functor of
`EffPolyfold` one needs that `T(Z, c)` is effective when `(Z, c)` is.

## What is formalized

* `EpGroupoid.isEffective_tangentEpGroupoid (hE : X.IsEffective) (hZ : X.IsZhou)`: the tangent
  ep-groupoid `TX` (Theorem 8.1.1) of an effective ep-groupoid satisfying (ZHOU) is effective.
* `PolyfoldClass.IsEffective.tangent`: the tangent `T(Z, c)` of an effective polyfold is
  effective (polyfold structures satisfy (ZHOU), Definition 16.1.1 (2)).
* `PolyfoldClass.ScMap.tangent_comp_of_isEffective`: `T(ĝ ∘ f̂) = Tĝ ∘ T f̂` for an effective
  middle polyfold, without the hypothesis `d.tangent.IsEffective` of wave 3's `tangent_comp`.
* `EffPolyfold.tangentFunctor : EffPolyfold.{u} ⥤ EffPolyfold.{max u 1}`: Theorem 16.2.4 as a
  Mathlib functor on the polyfold category of effective polyfolds, and `theorem_16_2_4_eff`.

## The proof

Let `k ∈ T𝐗` be an isotropy element of `a ∈ TX` with `k ≠ 1_a`, `φ = p(k) ∈ 𝐗₁`, and suppose
`s_T = t_T` on an open `W ∋ k`.  Then `φ ≠ 1_{s φ}` (fibre injectivity of `Ts`).  Separate `φ`
from `1_{s φ}` by disjoint open `A`, `B`, and take a sheet `s : W_s → V_s` of `s` at `φ` with
inverse `σ`.  The set `O = {b ∈ TV_s | Tσ(b) ∈ W, p(Tσ b) ∈ A, 1_{p b} ∈ B}` is open in `TX`
and contains `a`; pick a smooth `b ∈ O` (smooth points are dense) and put `y = p(b)` (smooth,
since `p : TX → X¹` is sc-smooth) and `ψ = σ(y)`.  For every `c ∈ T_yX ∩ O` the vector
`u = Tσ(c)` lies over `ψ`, has `Ts u = c` and `Tt u = Ts u`, so `Tψ(c) = c`.  `Tψ` is linear on
`T_yX` and `T_yX ∩ O` is a nonempty open subset of `T_yX`, so `Tψ = id` on `T_yX`.  By (ZHOU)
`ψ ∈ T_y`, and `T_y = {1_y}` since `X` is effective, so `ψ = 1_y ∈ A ∩ B`, a contradiction.

(ZHOU) enters through the smooth point `y`: effectiveness of `X` alone is a statement on level
`0`, while the open sets of `T𝐗` only see level `1` of `𝐗`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-- A linear map of a real topological vector space which is the identity on a nonempty open
set is the identity. -/
theorem linearMap_eq_self_of_eqOn_isOpen {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] (L : F →ₗ[ℝ] F)
    {O : Set F} (hO : IsOpen O) {k₀ : F} (hk₀ : k₀ ∈ O) (hL : ∀ k ∈ O, L k = k) (k : F) :
    L k = k := by
  have hc : Continuous fun t : ℝ => k₀ + t • k :=
    continuous_const.add (continuous_id.smul continuous_const)
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => k₀ + t • k) ⁻¹' O := by simpa using hk₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hO.preimage hc) 0 h0
  have ht : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have h1 := hL _ (hball ht)
  rw [map_add, map_smul, hL k₀ hk₀] at h1
  exact smul_right_injective F (ne_of_gt (half_pos hε)) (add_left_cancel h1)

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- A smooth point of `TX` lies over a smooth point of `X` (`p : TX → X¹` is sc-smooth and
`(X¹)_∞ = X_∞`). -/
theorem levelVal_tangentProj_mem_smoothSet {b : X.PObj.TangentSpace}
    (hb : b ∈ X.PObj.tangentPolyfold.smoothSet) :
    X.PObj.levelVal 1 (X.PObj.tangentProj b) ∈ X.PObj.smoothSet := by
  refine (MPolyfold.mem_shift_smoothSet_iff _).1 ?_
  simp only [MPolyfold.smoothSet, mem_iInter] at hb ⊢
  exact fun m => X.PObj.tangentProj_isScSmooth.mapsTo_levelSet m (hb m)

/-- An isotropy vector of `TX` over a unit is the unit. -/
theorem tangent_isotropy_eq_one {a : X.PObj.TangentSpace} (g : X.tangentEpGroupoid.Isotropy a)
    (hφ : X.tBase g.val = X.unit (X.src (X.tBase g.val))) : g = 1 := by
  have hs : X.tSrc g.val = a := g.src_val
  refine GroupoidStr.Isotropy.ext (X.tangent_ext ?_ ?_)
  · change X.tBase g.val = X.tBase (X.tUnit a)
    rw [X.tBase_tUnit]
    have h := X.levelVal_tangentProj_tSrc g.val
    rw [hs] at h
    rw [h]
    exact hφ
  · change X.tSrc g.val = X.tSrc (X.tUnit a)
    rw [X.tSrc_tUnit, hs]

/-- **The tangent of an effective ep-groupoid with (ZHOU) is effective** (used for 2021
Theorem 16.2.4, p. 719): `TX` (Theorem 8.1.1) satisfies Definition 7.2.1. -/
theorem isEffective_tangentEpGroupoid (hE : X.IsEffective) (hZ : X.IsZhou) :
    X.tangentEpGroupoid.IsEffective := by
  intro a g hg W hW hgW
  by_contra hcon
  have hcon' : ∀ w ∈ W, X.tSrc w = X.tTgt w := fun w hw => by_contra fun h => hcon ⟨w, hw, h⟩
  set v := g.val with hvdef
  set φ := X.tBase v with hφdef
  have hvs : X.tSrc v = a := g.src_val
  -- `φ` is not a unit
  have hφne : φ ≠ X.unit (X.src φ) := fun h => hg (X.tangent_isotropy_eq_one g h)
  obtain ⟨A, B, hA, hB, hφA, huB, hAB⟩ := t2_separation hφne
  -- a sheet of `s` at `φ`
  obtain ⟨Ws, Vs, σ, hφWs, hd⟩ := X.isLocalScDiffeo_src φ
  set Λ := MPolyfold.tangentMapOn hd.isScSmoothOn_inv with hΛdef
  have hDs := hd.tangentMap X.isScSmoothMap_src
  set W₀ := W ∩ X.tBase ⁻¹' (A ∩ Ws ∩ X.src ⁻¹' (X.unit ⁻¹' B)) with hW₀def
  have hWs : IsOpen Ws := hd.isScSmoothOn.isOpen
  have hW₀ : IsOpen W₀ :=
    hW.inter (((hA.inter hWs).inter (X.isLocalScDiffeo_src.continuous.isOpen_preimage _
        (X.continuous_unit.isOpen_preimage _ hB))).preimage X.continuous_tBase)
  set O := X.PObj.tangentPreimage Vs ∩ Λ ⁻¹' W₀ with hOdef
  have hO : IsOpen O :=
    (MPolyfold.continuousOn_tangentMapOn hd.isScSmoothOn_inv).isOpen_inter_preimage
      (MPolyfold.isOpen_tangentPreimage hd.isScSmoothOn_inv.isOpen) hW₀
  -- `a ∈ O`
  have hΛv : Λ (X.tSrc v) = v := tangentMapOn_srcInv_tSrc hd hφWs
  have haO : a ∈ O := by
    refine ⟨?_, ?_⟩
    · rw [MPolyfold.mem_tangentPreimage, ← hvs, X.levelVal_tangentProj_tSrc]
      exact hd.mapsTo hφWs
    · change Λ a ∈ W₀
      rw [← hvs, hΛv]
      exact ⟨hgW, ⟨hφA, hφWs⟩, huB⟩
  -- a smooth point `b ∈ O`
  obtain ⟨b, hbs, hbO⟩ := X.PObj.tangentPolyfold.dense_smoothSet.exists_mem_open hO ⟨a, haO⟩
  set y₁ := X.PObj.tangentProj b with hy₁def
  set y := X.PObj.levelVal 1 y₁ with hydef
  have hys : y ∈ X.PObj.smoothSet := X.levelVal_tangentProj_mem_smoothSet hbs
  -- vectors over `T_yX ∩ O`
  have hfib : ∀ c ∈ O, X.PObj.levelVal 1 (X.PObj.tangentProj c) = y →
      X.tBase (Λ c) = σ y ∧ X.tSrc (Λ c) = c ∧ X.tSrc (Λ c) = X.tTgt (Λ c) := by
    intro c hc hcy
    refine ⟨?_, hDs.right_inv c hc.1, hcon' _ hc.2.1⟩
    change X.PMor.levelVal 1 (X.PMor.tangentProj (Λ c)) = σ y
    rw [MPolyfold.levelVal_tangentProj_tangentMapOn hd.isScSmoothOn_inv hc.1, hcy]
  set ψ := σ y with hψdef
  obtain ⟨hbψ, hbsrc, hbeq⟩ := hfib b hbO rfl
  have hψ1 : ψ ∈ X.PMor.levelSet 1 := hbψ ▸ X.tBase_mem_levelSet (Λ b)
  have hsrc : X.src ψ = y := by
    rw [← hbψ, ← X.levelVal_tangentProj_tSrc, hbsrc]
  have htgt : X.tgt ψ = y := by
    rw [← hbψ, ← X.levelVal_tangentProj_tTgt, ← hbeq, hbsrc]
  -- `Tψ = id` on `T_yX`
  have hfix : ∀ c ∈ X.PObj.tangentFiber y₁, X.tangentMor ψ c = c := by
    have hx : X.PObj.levelVal 1 y₁ = X.src ψ := hsrc.symm
    have hy : X.PObj.levelVal 1 y₁ = X.tgt ψ := htgt.symm
    set L := (X.tangentMorCLM hψ1 hx hy : X.PObj.tangentFiber y₁ →L[ℝ] _).toLinearMap
    have hL : ∀ c : X.PObj.tangentFiber y₁, c ∈ Subtype.val ⁻¹' O → L c = c := by
      intro c hc
      apply Subtype.ext
      change (X.tangentMorCLM hψ1 hx hy c : X.PObj.TangentSpace) = c.1
      rw [tangentMorCLM_apply]
      have hcy : X.PObj.levelVal 1 (X.PObj.tangentProj c.1) = y := by
        rw [show X.PObj.tangentProj c.1 = y₁ from c.2]
      obtain ⟨h1, h2, h3⟩ := hfib c.1 hc hcy
      have h4 := X.tangentMor_tSrc (Λ c.1)
      rw [h1, h2, ← h3, h2] at h4
      exact h4
    intro c hc
    have := linearMap_eq_self_of_eqOn_isOpen L (hO.preimage continuous_subtype_val)
      (k₀ := ⟨b, rfl⟩) hbO hL ⟨c, hc⟩
    have h5 := congrArg Subtype.val this
    change (X.tangentMorCLM hψ1 hx hy ⟨c, hc⟩ : X.PObj.TangentSpace) = c at h5
    rwa [tangentMorCLM_apply] at h5
  -- (ZHOU) and effectiveness: `ψ = 1_y`
  set ys := X.PObj.smoothMk y hys
  have hinc : X.PObj.smoothIncl ys 1 = y₁ := MPolyfold.level_ext rfl
  let gψ : X.Isotropy (X.PObj.smoothVal ys) := ⟨ψ, hsrc, htgt⟩
  have hmem := hZ ys gψ (by rw [hinc]; exact hfix)
  rw [(X.isEffective_iff_trivialSubgroup_eq_bot.1 hE _), Subgroup.mem_bot] at hmem
  have hψu : ψ = X.unit y := congrArg GroupoidStr.Isotropy.val hmem
  have hψA : ψ ∈ A := hbψ ▸ hbO.2.2.1.1
  have hψB : ψ ∈ B := by
    have h6 : X.unit (X.src (X.tBase (Λ b))) ∈ B := hbO.2.2.2
    rw [hbψ, hsrc, ← hψu] at h6
    exact h6
  exact hAB.le_bot ⟨hψA, hψB⟩

end EpGroupoid

namespace PolyfoldClass

variable {Z W V : Type u} [TopologicalSpace Z] [TopologicalSpace W] [TopologicalSpace V]

/-- **The tangent of an effective polyfold is effective** (for 2021 Theorem 16.2.4, p. 719): if
`(Z, c)` is effective, so is `T(Z, c)` (Definition 16.2.3).  The structures of `c` satisfy (ZHOU)
(Definition 16.1.1 (2)). -/
theorem IsEffective.tangent {c : PolyfoldClass Z} (hc : c.IsEffective) : c.tangent.IsEffective :=
  ⟨tangentStructure c.out (Quotient.out_eq c), rfl,
    c.out.X.X.isEffective_tangentEpGroupoid ((c.isEffective_iff.1 hc) c.out (Quotient.out_eq c))
      c.out.isZhou⟩

namespace ScMap

variable {c : PolyfoldClass Z} {d : PolyfoldClass W} {e : PolyfoldClass V}

/-- **`T(ĝ ∘ f̂) = Tĝ ∘ T f̂`** for an effective middle polyfold `(W, d)` (2021 Theorem 16.2.4,
p. 719), with `T(W, d)` effective by `IsEffective.tangent`: wave 3's `tangent_comp` without its
hypothesis `d.tangent.IsEffective`. -/
theorem tangent_comp_of_isEffective (hd : d.IsEffective) (F : ScMap c d) (G : ScMap d e) :
    tangent (comp hd F G) = comp hd.tangent (tangent F) (tangent G) :=
  tangent_comp hd hd.tangent F G

end ScMap

end PolyfoldClass

/-- The tangent `T(Z, c)` of an effective polyfold, as an object of `EffPolyfold`. -/
def EffPolyfold.tangent (A : EffPolyfold.{u}) : EffPolyfold.{max u 1} :=
  ⟨PolyfoldClass.TangentSpace A.c, A.c.tangent, A.isEffective.tangent⟩

/-- **2021 Theorem 16.2.4, p. 719 (2017: Theorem 16.1), on the polyfold category of effective
polyfolds**: `T` is a functor `EffPolyfold ⥤ EffPolyfold`, `(Z, c) ↦ T(Z, c)`,
`f̂ ↦ T f̂ = [(Tf, T𝔣)]`. -/
def EffPolyfold.tangentFunctor : EffPolyfold.{u} ⥤ EffPolyfold.{max u 1} where
  obj := EffPolyfold.tangent
  map F := PolyfoldClass.ScMap.tangent F
  map_id A := PolyfoldClass.ScMap.tangent_id A.c
  map_comp {_ B _} F G := PolyfoldClass.ScMap.tangent_comp_of_isEffective B.isEffective F G

/-- **2021 Theorem 16.2.4, p. 719 (2017: Theorem 16.1)**, the functor statement on effective
polyfolds: `T` sends effective polyfolds to effective polyfolds, `T 1 = 1`, and
`T(ĝ ∘ f̂) = Tĝ ∘ T f̂`; with wave 3's `theorem_16_2_4` (the formula `Tf ∘ Tα = Tβ ∘ |T𝔣|`). -/
theorem theorem_16_2_4_eff :
    (∀ (A : EffPolyfold.{u}), (EffPolyfold.tangentFunctor.obj A).c = A.c.tangent) ∧
    (∀ (A : EffPolyfold.{u}),
      EffPolyfold.tangentFunctor.map (𝟙 A) = 𝟙 (EffPolyfold.tangentFunctor.obj A)) ∧
    (∀ {A B C : EffPolyfold.{u}} (F : A ⟶ B) (G : B ⟶ C),
      EffPolyfold.tangentFunctor.map (F ≫ G) =
        EffPolyfold.tangentFunctor.map F ≫ EffPolyfold.tangentFunctor.map G) :=
  ⟨fun _ => rfl, fun A => EffPolyfold.tangentFunctor.map_id A,
    fun F G => EffPolyfold.tangentFunctor.map_comp F G⟩

/-- Witness: the tangent of the point polyfold is an effective polyfold. -/
example : EffPolyfold.{1} := EffPolyfold.point.tangent

end Polyfold
