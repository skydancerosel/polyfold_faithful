import Polyfold.Chapter15.RestrictedSeedsCompare

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Corollary 15.3.10 (2), (3)
(pp. 699–700) on the restriction of a strong bundle over an ep-groupoid to a saturated open
subset of the object space.

# Norms and the extension of the end data on the cylinder of the restriction

With `Φ : [0, 1] × (W|V) → [0, 1] × W` the inclusion (`cubeRestrFib`):

* `normW_collarAuxNorm`: the collar norm read on `W̃` in terms of the `W`-component.
* `normW_collarAuxNorm_restr`: the collar norm of `(N⁰|V, N¹|V)` is the collar norm of
  `(N⁰, N¹)` composed with `Φ`; `pointwiseNorm_collarAuxNorm_restr_of_comp`.
* `cubeRestrFiberEquiv`: `Φ` on a fibre, a linear isomorphism.
* `cylExtension_restrMult`: the extension of the end data of the restriction is the extension
  of the end data composed with `Φ`; `pointwiseNorm_collarAuxNorm_cylExtension_restr`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold SEP EpGroupoid

variable {A : SEP.{u}}

/-! ### The collar norm read on `W̃` -/

/-- A point of `W̃` lies in `W̃_{0,1}` iff its `W`-component lies in `W_{0,1}`. -/
theorem mem_oneSet_cubeSEP_iff (w : (A.cubeSEP 1).W) :
    w ∈ (A.cubeSEP 1).B.oneSet ↔ (cubeVal w).2 ∈ A.B.oneSet := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj) (A.X.cubeProj 1).obj
  exact A.B.mem_oneSet_pullback_iff (A.X.cubeProj 1).isScSmoothMap_obj w

/-- `pr^*N` read on `W̃` is `N` read on the `W`-component. -/
theorem normW_cubeAuxNorm (N : A.B.One → ℝ) (w : (A.cubeSEP 1).W) :
    normW (cubeAuxNorm 1 N) w = normW N (cubeVal w).2 := by
  by_cases hw : w ∈ (A.cubeSEP 1).B.oneSet
  · have hw' := (mem_oneSet_cubeSEP_iff w).1 hw
    rw [normW_of_mem _ hw, normW_of_mem _ hw']
    exact cubeAuxNorm_eq _ _ (by rw [A.B.oneVal_oneMk, (A.cubeSEP 1).B.oneVal_oneMk])
  · have hw' : (cubeVal w).2 ∉ A.B.oneSet := fun h => hw ((mem_oneSet_cubeSEP_iff w).2 h)
    unfold normW
    rw [dif_neg hw, dif_neg hw']

/-- **The collar norm read on `W̃`**:
`Ñ((t, x), h) = max(a(t)·N⁰(h), b(t)·N¹(h))`. -/
theorem normW_collarAuxNorm (N₀ N₁ : A.B.One → ℝ) (w : (A.cubeSEP 1).W) :
    normW (collarAuxNorm A N₀ N₁) w =
      max (collarWeight₀ (cubeT ((A.cubeSEP 1).P w)) * normW N₀ (cubeVal w).2)
        (collarWeight₁ (cubeT ((A.cubeSEP 1).P w)) * normW N₁ (cubeVal w).2) := by
  rw [← normW_cubeAuxNorm, ← normW_cubeAuxNorm]
  by_cases hw : w ∈ (A.cubeSEP 1).B.oneSet
  · rw [normW_of_mem _ hw, normW_of_mem _ hw, normW_of_mem _ hw]
    have ht : cubeTime ((A.cubeSEP 1).B.oneMk w hw) = cubeT ((A.cubeSEP 1).P w) := by
      change ((cubeVal ((A.cubeSEP 1).B.oneVal ((A.cubeSEP 1).B.oneMk w hw))).1.1 0 : ℝ) = _
      rw [(A.cubeSEP 1).B.oneVal_oneMk]
      rfl
    rw [collarAuxNorm, ht]
  · unfold normW
    rw [dif_neg hw, dif_neg hw, dif_neg hw, mul_zero, mul_zero, max_self]

variable {V : Set A.Obj} (hV : A.X.IsEpSubgroupoid V)

/-- **The collar norm of `(N⁰|V, N¹|V)` is the collar norm of `(N⁰, N¹)` composed with the
inclusion `Φ`.** -/
theorem normW_collarAuxNorm_restr (N₀ N₁ : A.B.One → ℝ) (w : ((A.restr hV).cubeSEP 1).W) :
    normW (collarAuxNorm (A.restr hV) (restrNorm hV N₀) (restrNorm hV N₁)) w =
      normW (collarAuxNorm A N₀ N₁) (cubeRestrFib hV w) := by
  rw [normW_collarAuxNorm, normW_collarAuxNorm, normW_restrNorm, normW_restrNorm]
  rfl

/-- **`Ñ|V(Λ')(z) = Ñ(Λ)(ϕ z)`** (Definition 13.2.3) for multisections with `Λ' = Λ ∘ Φ`. -/
theorem pointwiseNorm_collarAuxNorm_restr_of_comp (N₀ N₁ : A.B.One → ℝ)
    {Λ' : ((A.restr hV).cubeSEP 1).W → ℚ≥0} {Λ : (A.cubeSEP 1).W → ℚ≥0}
    (h : ∀ w, Λ' w = Λ (cubeRestrFib hV w)) (z : ((A.restr hV).cubeSEP 1).Obj) :
    pointwiseNorm (collarAuxNorm (A.restr hV) (restrNorm hV N₀) (restrNorm hV N₁)) Λ' z =
      pointwiseNorm (collarAuxNorm A N₀ N₁) Λ (cubeRestrBase hV z) := by
  have himg : cubeRestrFib hV '' suppAt Λ' z = suppAt Λ (cubeRestrBase hV z) := by
    ext v
    constructor
    · rintro ⟨w, ⟨hw, hpos⟩, rfl⟩
      exact ⟨by rw [P_cubeRestrFib, hw], by rw [← h]; exact hpos⟩
    · rintro ⟨hv, hpos⟩
      have hv1 : (cubeVal v).1 = cubeRestrBase hV z := hv
      have hv2 : A.P (cubeVal v).2 = (cubeVal v).1.2 :=
        (show pullbackSpace A.P (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj) from v).2
      have hk : A.P (cubeVal v).2 =
          restrBase hV (show (Fin 1 → unitInterval) × (A.restr hV).Obj from z).2 := by
        rw [hv2, hv1]; rfl
      let k : (A.restr hV).W :=
        ⟨((show (Fin 1 → unitInterval) × (A.restr hV).Obj from z).2, (cubeVal v).2), hk⟩
      let w : ((A.restr hV).cubeSEP 1).W := ⟨(z, k), rfl⟩
      have hwv : cubeRestrFib hV w = v := Subtype.ext (Prod.ext hv1.symm rfl)
      exact ⟨w, ⟨rfl, by rw [h, hwv]; exact hpos⟩, hwv⟩
  unfold pointwiseNorm
  rw [← himg, image_image]
  exact congrArg sSup (image_congr fun w _ => normW_collarAuxNorm_restr hV N₀ N₁ w)

/-! ### The fibres -/

variable (hVo : IsOpen V)

/-- **`Φ` on the fibre over `z`**, a linear isomorphism onto the fibre of `[0, 1] × W` over
`ϕ z`. -/
def cubeRestrFiberEquiv (z : ((A.restr hV).cubeSEP 1).Obj) :
    (((A.restr hV).cubeSEP 1).P ⁻¹' {z}) ≃ₗ[ℝ] ((A.cubeSEP 1).P ⁻¹' {cubeRestrBase hV z}) :=
  LinearEquiv.ofBijective
    (IsLinearMap.mk' _ ((cubeRestrIso hV hVo z).fiber_linear z (cubeRestrBase hV z)
      (mem_univ z) rfl))
    ⟨fun u u' h => Subtype.ext (cubeRestrFib_injective hV (congrArg Subtype.val h)),
      fun v => by
        set L := cubeRestrIso hV hVo z
        have hvV : (A.cubeSEP 1).P (v : (A.cubeSEP 1).W) ∈
            (Prod.snd ⁻¹' V : Set ((Fin 1 → unitInterval) × A.Obj)) := by
          rw [show (A.cubeSEP 1).P (v : (A.cubeSEP 1).W) = cubeRestrBase hV z from v.2]
          exact cubeRestrBase_mem hV z
        have hΦ : cubeRestrFib hV (L.Ψ v) = v := L.zero.right_inv _ hvV
        have hP : ((A.restr hV).cubeSEP 1).P (L.Ψ v) = z := by
          apply cubeRestrBase_injective hV
          rw [← P_cubeRestrFib, hΦ]
          exact v.2
        exact ⟨⟨L.Ψ v, hP⟩, Subtype.ext hΦ⟩⟩

@[simp] theorem cubeRestrFiberEquiv_val (z : ((A.restr hV).cubeSEP 1).Obj)
    (u : ((A.restr hV).cubeSEP 1).P ⁻¹' {z}) :
    (cubeRestrFiberEquiv hV hVo z u : (A.cubeSEP 1).W) =
      cubeRestrFib hV (u : ((A.restr hV).cubeSEP 1).W) := rfl

/-! ### The extension of the end data -/

include hVo in
/-- `(g ∘ t) ⊙ pr^*(Λ|V) = ((g ∘ t) ⊙ pr^*Λ) ∘ Φ`. -/
theorem multisectionSmulFun_cubePullMult_restr (g : ℝ → ℝ) (Λ : A.W → ℚ≥0)
    (u : ((A.restr hV).cubeSEP 1).W) :
    multisectionSmulFun (fun p => g (cubeT p)) (cubePullMult (restrMult hV Λ)) u =
      multisectionSmulFun (fun p => g (cubeT p)) (cubePullMult Λ) (cubeRestrFib hV u) := by
  classical
  set e := cubeRestrFiberEquiv hV hVo (((A.restr hV).cubeSEP 1).P u)
  set a : ℝ := g (cubeT (((A.restr hV).cubeSEP 1).P u))
  change smulAt a (cubePullMult (restrMult hV Λ)) (((A.restr hV).cubeSEP 1).P u) (toFib u) =
    smulAt a (cubePullMult Λ) (cubeRestrBase hV (((A.restr hV).cubeSEP 1).P u)) (e (toFib u))
  unfold smulAt
  by_cases ha : a = 0
  · rw [if_pos ha, if_pos ha]
    exact if_congr (map_eq_zero_iff e e.injective).symm rfl rfl
  · rw [if_neg ha, if_neg ha, ← map_smul]
    rfl

include hVo in
/-- **The extension of the end data of the restriction is the extension of the end data
composed with the inclusion `Φ`** (Corollary 15.3.10 (3), p. 699). -/
theorem cylExtension_restrMult (Λ₀ Λ₁ : A.W → ℚ≥0) (w : ((A.restr hV).cubeSEP 1).W) :
    cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁) w =
      cylExtension Λ₀ Λ₁ (cubeRestrFib hV w) := by
  classical
  set z := ((A.restr hV).cubeSEP 1).P w
  set e := cubeRestrFiberEquiv hV hVo z
  change addAt _ _ z w = addAt _ _ (cubeRestrBase hV z) (cubeRestrFib hV w)
  unfold addAt
  rw [← finsum_comp_equiv (e.toEquiv.prodCongr e.toEquiv)]
  refine finsum_congr fun p => ?_
  have h0 := multisectionSmulFun_cubePullMult_restr hV hVo collarCut₀ Λ₀
    (p.1 : ((A.restr hV).cubeSEP 1).W)
  have h1 := multisectionSmulFun_cubePullMult_restr hV hVo collarCut₁ Λ₁
    (p.2 : ((A.restr hV).cubeSEP 1).W)
  have hsum : ((e p.1 + e p.2 : (A.cubeSEP 1).P ⁻¹' {cubeRestrBase hV z}) : (A.cubeSEP 1).W) =
      cubeRestrFib hV ((p.1 + p.2 : ((A.restr hV).cubeSEP 1).P ⁻¹' {z}) :
        ((A.restr hV).cubeSEP 1).W) := by
    rw [← map_add]; rfl
  change _ = (if ((e p.1 + e p.2 : (A.cubeSEP 1).P ⁻¹' {cubeRestrBase hV z}) :
      (A.cubeSEP 1).W) = cubeRestrFib hV w then
    multisectionSmulFun (fun p => collarCut₀ (cubeT p)) (cubePullMult Λ₀)
        (cubeRestrFib hV (p.1 : ((A.restr hV).cubeSEP 1).W)) *
      multisectionSmulFun (fun p => collarCut₁ (cubeT p)) (cubePullMult Λ₁)
        (cubeRestrFib hV (p.2 : ((A.restr hV).cubeSEP 1).W)) else 0)
  rw [hsum, ← h0, ← h1]
  exact if_congr (cubeRestrFib_injective hV).eq_iff.symm rfl rfl

include hVo in
/-- **The pointwise collar norms of the two extensions agree**:
`Ñ|V(Λ̃|V)(z) = Ñ(Λ̃)(ϕ z)`. -/
theorem pointwiseNorm_collarAuxNorm_cylExtension_restr (N₀ N₁ : A.B.One → ℝ)
    (Λ₀ Λ₁ : A.W → ℚ≥0) (z : ((A.restr hV).cubeSEP 1).Obj) :
    pointwiseNorm (collarAuxNorm (A.restr hV) (restrNorm hV N₀) (restrNorm hV N₁))
        (cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁)) z =
      pointwiseNorm (collarAuxNorm A N₀ N₁) (cylExtension Λ₀ Λ₁) (cubeRestrBase hV z) :=
  pointwiseNorm_collarAuxNorm_restr_of_comp hV N₀ N₁
    (cylExtension_restrMult hV hVo Λ₀ Λ₁) z

end SBLocalization

end Polyfold
