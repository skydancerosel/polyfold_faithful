import Polyfold.Chapter15.RestrictedSeedsCut
import Polyfold.Chapter12.LocalOrientationDomains

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.9** (Transversal Extension Theorem), steps (c)–(d), pp. 698–699: the sections of
the local constructions relative to `Λ₀`, before they are cut off.

# The spanning sections relative to `Λ₀`, without bump functions

## The text, paraphrased

At a point `x` of `supp(Λ₀ ∘ f)` there are finitely many sc⁺-sections `s_j` such that for every
branch `s⁰_a` of `Λ₀` through `f(x)` the image `(f − s⁰_a)'(x)(T^R_xX)` and the `s_j(x)` span
`W_x`; this persists at the points of `supp(Λ₀ ∘ f)` near `x`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `StrongBundleChart.IsParamGP.congr_principal`: Part I's (i)–(ii) depend on the sections only
  through their principal parts at the centre.
* **`onto_of_isParamGP_restrictTo_rel`**: the converse of `isParamGP_restrictTo_of_onto_rel`:
  Part I's (i)–(ii) for `(f − s⁰)|O` and `(−s_j)|O` in a transported chart give (15.1) for the
  operator `(f − s⁰)'(x)` with the vectors `s_j(x)`.
* `exists_sections_isParamGP_branch`: for a local branch `s⁰` on `O` through `f(x)`, global
  sc⁺-sections `S_j` with (i)–(ii) for `(f − s⁰)|O` and the `(−S_j)|O` at `x` (Part I's
  `exists_sections_isParamGP_of_sections` on the restriction `W|O`).
* `exists_open_onto_branch_local`: the openness of (15.1) for one local branch along
  `{f = s⁰}`.
* **`exists_preSeedRel`**: at `x ∈ supp(Λ₀ ∘ f)` there are finitely many global sc⁺-sections
  `S_j` and an open `W ∋ x` with (15.1) relative to `Λ₀` with the vectors `S_j(y)` at every
  `y ∈ supp(Λ₀ ∘ f) ∩ W`.  Hypotheses: tame `X`, tame germ data, sc⁺-sections through the smooth
  fibre points; no bump functions.
* **`exists_seeds_of_function_rel`**, **`hasLocalParamSeedsRel_of_functions`**: the seeds at `x`
  from one sc-smooth function with support in an open `O'' ∋ x` determined before the function.

## Reading

The local branches `s⁰_a` are not extended to global sections: `f − s⁰_a` is an sc-Fredholm
section of the restriction `W|O` (`isScFredholmSectionTame_subRestrict`), and Part I's statements
are used on `W|O`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u v

/-! ### (i)–(ii) and the principal parts at the centre -/

section Congr

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- **Part I's (i)–(ii) depend on the sections only through their principal parts at `0`.** -/
theorem StrongBundleChart.IsParamGP.congr_principal {c : StrongBundleChart PX P} {g : X → Y}
    {m : ℕ} {t t' : Fin m → X → Y} {n : ℕ} {Wq : ScBanach}
    {T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)} (h : c.IsParamGP g t T)
    (ht : ∀ i, c.principal (t' i) 0 = c.principal (t i) 0) : c.IsParamGP g t' T := by
  unfold StrongBundleChart.IsParamGP at h ⊢
  simp only [ht]
  exact h

end Congr

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

section Branch

variable {O : Set A.Obj} (hO : IsOpen O) [Nonempty O] [ParacompactSpace O]
  [ParacompactSpace (pullbackSpace A.P (Subtype.val : O → A.Obj))]

set_option maxHeartbeats 1600000 in
-- the chart reading of Part I's (i)–(ii) in the transported chart
include hO in
/-- **Part I's (i)–(ii) for `(f − s⁰)|O` give (15.1) for the operator `(f − s⁰)'(x)`** (the
converse of `isParamGP_restrictTo_of_onto_rel`): in a chart `c` of `W` with domain in `O`,
centred at `x` with `f(x) = s⁰(x)`, if `F(t, y) = (f − s⁰)|O + Σ_j t_j (−s_j)|O` has the
properties (i)–(ii) in the transported chart of `W|O`, then `(v, τ) ↦ (f − s⁰)'(x)v + Σ_j τ_j
s_j(x)` maps `T^R_xX × ℝ^ℓ` onto `W_x`. -/
theorem onto_of_isParamGP_restrictTo_rel {f : A.Obj → A.W}
    (hft : A.B.IsScFredholmSectionTame f) {s₀ : A.Obj → A.W} (hs0 : IsScPlusSectionOn A s₀ O)
    {ℓ : ℕ} {s : Fin ℓ → A.Obj → A.W} (hs : ∀ j, IsScPlusSectionOn A (s j) O)
    (hsec : ∀ j, IsSection A.P (s j)) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hsub : c.φ.source ⊆ O) {x : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hφ0 : c.φ (A.X.PObj.levelVal 1 x) = 0)
    (hx0 : f (A.X.PObj.levelVal 1 x) = s₀ (A.X.PObj.levelVal 1 x)) {n : ℕ}
    {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (q₀ : pullbackSpace A.P (Subtype.val : O → A.Obj))
    (hGP : (c.restrictTo A.B.continuous hO hsub q₀).IsParamGP
      (subRestrict (O := O) f s₀ hft.isScSmooth.1)
      (fun j => negRestrict (O := O) (s j)) T) :
    ∀ w : A.P ⁻¹' {A.X.PObj.levelVal 1 x}, ∃ v ∈ reducedTangentFiber c.isChart hx T,
      ∃ τ : Fin ℓ → ℝ, toIntr c hx (subDeriv c f s₀
        (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) v +
          ∑ j, τ j • (⟨s j (A.X.PObj.levelVal 1 x), hsec j _⟩ :
            A.P ⁻¹' {A.X.PObj.levelVal 1 x}) = w := by
  classical
  have hz0 : levelLift c.φ 1 (A.X.PObj.levelVal 1 x) = 0 := by
    apply c.φ.model.E.toBase_injective 1
    rw [A.X.PObj.toBase_levelLift c.isChart hx (levelVal_mem x), hφ0, map_zero]
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O :=
    hφ0 ▸ c.φ.mapsTo_model (A.X.PObj.levelVal 1 x) hx
  have hzU : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ c.U := by
    rw [map_zero]; exact mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  have hlin : ∀ u : ↥(rangeS (scDeriv (c.restrictTo A.B.continuous hO hsub q₀).U
        (r (c.restrictTo A.B.continuous hO hsub q₀).R) 0)),
      linAt (c.restrictTo A.B.continuous hO hsub q₀).U (c.restrictTo A.B.continuous hO hsub q₀).R
        ((c.restrictTo A.B.continuous hO hsub q₀).principal
        (subRestrict (O := O) f s₀ hft.isScSmooth.1)) 0 u =
        subDeriv c f s₀ (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)) u.1 := fun u => by
    have e := scDeriv_restrictTo_subRestrict hO hft hs0 hc hsub q₀ hzU
    rw [hz0]
    exact congrArg (fun L : c.φ.model.E 0 →L[ℝ] c.F 0 => L u.1) e
  have hcol : ∀ j,
      (c.restrictTo A.B.continuous hO hsub q₀).principal (negRestrict (O := O) (s j)) 0 =
      -c.fiberLin hx ⟨s j (A.X.PObj.levelVal 1 x), hsec j (A.X.PObj.levelVal 1 x)⟩ := fun j => by
    have e := principal_eq_fiberLin hx (hsec j (A.X.PObj.levelVal 1 x))
    rw [hφ0] at e
    exact (principal_restrictTo_negRestrict hO (hs j).1 hsub q₀ h0O).trans (by rw [e])
  intro w
  set D := subDeriv c f s₀ (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)) with hD
  set Fv : Fin ℓ → c.F 0 := fun j =>
    c.fiberLin hx ⟨s j (A.X.PObj.levelVal 1 x), hsec j (A.X.PObj.levelVal 1 x)⟩ with hFv
  have hK : ((0 : c.φ.model.E 0), c.fiberLin hx w) ∈ c.K := by
    have h1 : (c.φ (A.X.PObj.levelVal 1 x), c.fiberLin hx w) ∈ c.K := by
      rw [← c.apply_fiberLin hx w, ← c.image_source]; exact ⟨_, c.fiberLin_src hx w, rfl⟩
    rwa [hφ0] at h1
  obtain ⟨u, a, hua⟩ := hGP.1 _ hK
  obtain ⟨u', a', hua', hmin⟩ := hGP.2 u
  rw [hlin] at hua hua'
  have hsum : ∀ b : Fin ℓ → ℝ, ∑ i, b i • (c.restrictTo A.B.continuous hO hsub q₀).principal
      (negRestrict (O := O) (s i)) 0 = -∑ j, b j • Fv j := fun b => by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcol j]
    exact smul_neg _ _
  have e1 : D u.1 - ∑ j, a j • Fv j = c.fiberLin hx w := by
    rw [sub_eq_add_neg, ← hsum a]; exact hua
  have e2 : D u'.1 - ∑ j, a' j • Fv j = 0 := by
    rw [sub_eq_add_neg, ← hsum a']; exact hua'
  let u0 : c.φ.model.E 0 := (u : (c.restrictTo A.B.continuous hO hsub q₀).φ.model.E 0)
  let u0' : c.φ.model.E 0 := (u' : (c.restrictTo A.B.continuous hO hsub q₀).φ.model.E 0)
  set v₀ : c.φ.model.E 0 := u0 - u0' with hv₀
  have hv₀T : v₀ ∈ tangentFiberModel c.isChart hx :=
    (c.mem_tangentFiberModel_iff_rangeS hx _).2 (by
      rw [hz0]; exact Submodule.sub_mem (rangeS (scDeriv c.U (r c.R) 0)) u.2 u'.2)
  set α := (tangentFiberEquiv c.isChart hx).symm ⟨v₀, hv₀T⟩ with hα
  have hαv : (tangentFiberEquiv c.isChart hx α : c.φ.model.E 0) = v₀ := by
    rw [hα, Equiv.apply_symm_apply]
  refine ⟨α, ?_, fun j => a' j - a j, ?_⟩
  · rw [reducedTangentFiber, Submodule.mem_comap, fiberCoord_eq_coe, hφ0, hαv]
    exact hmin
  · apply c.fiberLin_injective hx
    rw [map_add, map_sum]
    simp only [map_smul]
    rw [fiberLin_toIntr_subDeriv hft.isScSmooth hs0 hc hsub hx hx0, hαv, hv₀, map_sub, ← e1]
    have e3 : ∑ j, (a' j - a j) • Fv j = ∑ j, a' j • Fv j - ∑ j, a j • Fv j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => sub_smul _ _ _
    change D u0 - D u0' + ∑ j, (a' j - a j) • Fv j = D u0 - ∑ j, a j • Fv j
    rw [e3]
    have e4 : D u0' = ∑ j, a' j • Fv j := sub_eq_zero.1 e2
    rw [e4]
    abel


/-! ### Sections with (i)–(ii) for a local branch -/

set_option maxHeartbeats 1600000 in
-- Part I's sections on `W|O`, replaced by global sections through the same fibre points
include hO in
/-- **Global sc⁺-sections with Part I's (i)–(ii) for a local branch**: let `s⁰` be an sc⁺-section
on `O` with `f(x) = s⁰(x)`, and `c` a tame chart with domain in `O` centred at `x`.  If `W|O`
and `W` have sc⁺-sections through their smooth fibre points, there are finitely many global
sc⁺-sections `S_j` of `W` such that `F(t, y) = (f − s⁰)|O + Σ_j t_j (−S_j)|O` has the properties
(i)–(ii) at `(0, x)` in the transported chart. -/
theorem exists_sections_isParamGP_branch
    (hsecO : (A.B.restrictOpen hO).HasScPlusSectionsThrough)
    (hsec : A.B.HasScPlusSectionsThrough) {f : A.Obj → A.W}
    (hft : A.B.IsScFredholmSectionTame f) {s₀ : A.Obj → A.W} (hs0 : IsScPlusSectionOn A s₀ O)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsTameChart c) (hsub : c.φ.source ⊆ O)
    {x : A.Obj} (hxc : x ∈ c.φ.source) (hφ0 : c.φ x = 0) (hx0 : f x = s₀ x) {n : ℕ}
    {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (q₀ : pullbackSpace A.P (Subtype.val : O → A.Obj)) :
    ∃ (k : ℕ) (S : Fin k → A.Obj → A.W) (_ : ∀ i, A.B.IsScPlusSection (S i)),
      (c.restrictTo A.B.continuous hO hsub q₀).IsParamGP
        (subRestrict (O := O) f s₀ hft.isScSmooth.1)
        (fun j => negRestrict (O := O) (S j)) T := by
  classical
  have hxO : x ∈ O := hsub hxc
  set p : O := ⟨x, hxO⟩ with hp
  have hgO := isScFredholmSectionTame_subRestrict hO hft hs0
  have hy0 : IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
      (subRestrict (O := O) f s₀ hft.isScSmooth.1) p := by
    unfold subRestrict
    rw [isZeroAt_restrictSection_iff]
    exact (isZeroAt_subSec_iff hft.isScSmooth.1 hs0.1 hxO).2 hx0
  have hc'T : (A.B.restrictOpen hO).IsTameChart (c.restrictTo A.B.continuous hO hsub q₀) :=
    ⟨restrictOpen_isChart_restrictTo hO hc.1 hsub q₀, hc.2⟩
  obtain ⟨k, s', hs', hGP⟩ := exists_sections_isParamGP_of_sections hsecO hgO hy0 hc'T
    (x := p) hxc hφ0 T hT
  have hps : p ∈ (A.X.PObj.restrictOpen hO).smoothSet :=
    hgO.toIsScFredholmSection.mem_smoothSet_of_isZeroAt hy0
  have hxs : x ∈ A.X.PObj.smoothSet := (MPolyfold.mem_smoothSet_restrictOpen_iff hO p).1 hps
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model x hxc
  -- the fibre points `e_i = s'_i(x)`, read in `W`
  have hPe : ∀ i, A.P (s' i p).1.2 = x := fun i => by
    have h1 : A.P (s' i p).1.2 = ((s' i p).1.1 : A.Obj) := (s' i p).2
    have h2 : (s' i p).1.1 = p := (hs' i).1 p
    rw [h1, h2]
  have hesm : ∀ i, (s' i p).1.2 ∈ A.B.toMPolyfold0.smoothSet := fun i => by
    obtain ⟨-, G, hG, hGs⟩ := ((A.B.restrictOpen hO).isScPlusSection_iff (s' i)).1 (hs' i)
    have hsm : (A.X.PObj.restrictOpen hO).IsScSmoothMap (A.B.restrictOpen hO).toMPolyfold0
        (s' i) := by
      rw [← hG]; exact (A.B.restrictOpen hO).isScSmoothMap_oneVal.comp hGs
    have h1 : s' i p ∈ (A.B.restrictOpen hO).toMPolyfold0.smoothSet :=
      mem_iInter.2 fun m => hsm.mapsTo_levelSet m (mem_iInter.1 hps m)
    exact mem_iInter.2 fun m =>
      (A.B.isScSmoothMap_restrictIso_zero hO).mapsTo_levelSet m (mem_iInter.1 h1 m)
  have hex : ∀ i, ∃ S₀ : A.Obj → A.W, A.B.IsScPlusSection S₀ ∧ S₀ x = (s' i p).1.2 := fun i =>
    hsec x hxs _ (hesm i) (hPe i)
  choose S₀ hS₀ hS₀x using hex
  have hSsec : ∀ i, IsSection A.P (Polyfold.sectionSmul A.P (fun _ => (-1 : ℝ)) (S₀ i)) :=
    fun i => (hS₀ i).1.sectionSmul
  refine ⟨k, fun i => Polyfold.sectionSmul A.P (fun _ => (-1 : ℝ)) (S₀ i),
    fun i => (hS₀ i).smul_left (isScSmoothMap_real_const (-1)), hGP.congr_principal fun i => ?_⟩
  have hsymm : c.φ.symm 0 = x := by rw [← hφ0, c.φ.symm_apply_apply hxc]
  have hsymm' : (c.φ.restrictTo hsub).symm 0 = p :=
    Subtype.ext ((MChart.restrictTo_symm_val hsub h0O).trans hsymm)
  have e1 : (c.restrictTo A.B.continuous hO hsub q₀).principal (s' i) 0 = (c (s' i p).1.2).2 := by
    change (c (s' i ((c.φ.restrictTo hsub).symm 0)).1.2).2 = _
    rw [hsymm']
  have e2 : c.principal (S₀ i) 0 = (c (s' i p).1.2).2 := by
    change (c (S₀ i (c.φ.symm 0))).2 = _
    rw [hsymm, hS₀x i]
  refine (principal_restrictTo_negRestrict hO (fun y _ => hSsec i y) hsub q₀ h0O).trans ?_
  rw [principal_sectionSmul_const c (hS₀ i).1 (-1) h0O, e2, neg_one_smul, neg_neg]
  exact e1.symm

/-! ### Openness along a local branch -/

set_option maxHeartbeats 1600000 in
-- Part I's openness of general position for the parametrized section of `(f − s⁰)|O`
include hO in
/-- **The openness of (15.1) for one local branch along `{f = s⁰}`** (the statement of
`exists_open_onto_branch` for a branch defined on `O` only): if Part I's (i)–(ii) hold at `x`
for `(f − s⁰)|O` and global sc⁺-sections `S_j` in a tame chart centred at `x` inside `O`, then
(15.1) for `(f − s⁰)'(y)` with the vectors `S_j(y)` holds at every `y` near `x` with
`f(y) = s⁰(y)`. -/
theorem exists_open_onto_branch_local (hX : A.X.IsTame) {f : A.Obj → A.W}
    (hft : A.B.IsScFredholmSectionTame f) {s₀ : A.Obj → A.W} (hs0 : IsScPlusSectionOn A s₀ O)
    {ℓ : ℕ} {S : Fin ℓ → A.Obj → A.W} (hS : ∀ j, A.B.IsScPlusSection (S j))
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsTameChart c) (hsub : c.φ.source ⊆ O)
    {x : A.Obj} (hxc : x ∈ c.φ.source) (hφ0 : c.φ x = 0) (hx0 : f x = s₀ x) {n : ℕ}
    {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (q₀ : pullbackSpace A.P (Subtype.val : O → A.Obj))
    (hGP : (c.restrictTo A.B.continuous hO hsub q₀).IsParamGP
      (subRestrict (O := O) f s₀ hft.isScSmooth.1)
      (fun j => negRestrict (O := O) (S j)) T) :
    ∃ Wa : Set A.Obj, IsOpen Wa ∧ x ∈ Wa ∧ Wa ⊆ O ∧ ∀ y : A.X.PObj.Level 1,
      A.X.PObj.levelVal 1 y ∈ Wa → f (A.X.PObj.levelVal 1 y) = s₀ (A.X.PObj.levelVal 1 y) →
        BranchOnto f s₀ O S (fun j => (hS j).1) y := by
  classical
  have := MPolyfold.paracompactSpace_prod (rnPolyfold ℓ) (A.X.PObj.restrictOpen hO)
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin ℓ → ℝ) × O → O))
    ((rnPolyfold ℓ).prod (A.X.PObj.restrictOpen hO)) (A.B.restrictOpen hO)
  have hXO : (A.X.PObj.restrictOpen hO).IsTame := MPolyfold.isTame_restrictOpen _ hO hX
  have hxO : x ∈ O := hsub hxc
  set p : O := ⟨x, hxO⟩ with hp
  have hgO := isScFredholmSectionTame_subRestrict hO hft hs0
  have hSon : ∀ j, IsScPlusSectionOn A (S j) O := fun j =>
    IsScPlusSectionOn.of_isScPlusSection (hS j) hO
  have hSO : ∀ j, (A.B.restrictOpen hO).IsScPlusSection (negRestrict (O := O) (S j)) :=
    fun j => isScPlusSection_negRestrict hO (hSon j)
  have hzg : ∀ y : O, f y.1 = s₀ y.1 → IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
      (subRestrict (O := O) f s₀ hft.isScSmooth.1) y := fun y hy => by
    unfold subRestrict
    rw [isZeroAt_restrictSection_iff]
    exact (isZeroAt_subSec_iff hft.isScSmooth.1 hs0.1 y.2).2 hy
  have hy0 := hzg p hx0
  have hc'T : (A.B.restrictOpen hO).IsTameChart (c.restrictTo A.B.continuous hO hsub q₀) :=
    ⟨restrictOpen_isChart_restrictTo hO hc.1 hsub q₀, hc.2⟩
  have hgerm := isGeneralPositionGerm_paramSection_of_isParamGP hgO hSO hy0 hc'T (y := p) hxc
    hφ0 T hT hGP
  have hzero : ∀ y : O, IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
      (subRestrict (O := O) f s₀ hft.isScSmooth.1) y →
      IsZeroAt (pullbackProj (pullbackProj A.P (Subtype.val : O → A.Obj)) Prod.snd)
        (paramSection (subRestrict (O := O) f s₀ hft.isScSmooth.1) hgO.isScSmooth.1
          (fun j => negRestrict (O := O) (S j)) fun i => (hSO i).1)
        ((0 : Fin ℓ → ℝ), y) := by
    intro y hy
    rw [isZeroAt_paramSection_iff]
    change IsZeroAt _ (paramSlice (subRestrict (O := O) f s₀ hft.isScSmooth.1)
      hgO.isScSmooth.1 (fun j => negRestrict (O := O) (S j)) (fun i => (hSO i).1) 0) y
    rw [paramSlice_zero]
    exact hy
  obtain ⟨W₀, hW₀o, h0W₀, -, hW₀⟩ := exists_isOpen_isGeneralPositionGerm (prod_rn_isTame hXO)
    (theorem_3_1_21_tame hgO hSO) (hzero _ hy0) hgerm
  have hpre : IsOpen ((fun y : O => ((0 : Fin ℓ → ℝ), y)) ⁻¹' W₀) :=
    hW₀o.preimage (continuous_const.prodMk continuous_id)
  refine ⟨Subtype.val '' ((fun y : O => ((0 : Fin ℓ → ℝ), y)) ⁻¹' W₀),
    hO.isOpenMap_subtype_val _ hpre, ⟨p, h0W₀, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro y ⟨y', hy'W, hy'⟩ hyb c₁ hc₁ hsub₁ hy hφ1 n' Wq' T' hT' w
    have hyO : A.X.PObj.levelVal 1 y ∈ O := hsub₁ hy
    have ey : y' = ⟨A.X.PObj.levelVal 1 y, hyO⟩ := Subtype.ext hy'
    rw [ey] at hy'W
    have hgy := hzg ⟨A.X.PObj.levelVal 1 y, hyO⟩ hyb
    obtain ⟨-, hgp, -⟩ := hW₀ _ hy'W (hzero _ hgy)
    have hc₁T : (A.B.restrictOpen hO).IsTameChart (c₁.restrictTo A.B.continuous hO hsub₁ q₀) :=
      ⟨restrictOpen_isChart_restrictTo hO hc₁.1 hsub₁ q₀, hc₁.2⟩
    have hGP' := isParamGP_of_isGeneralPositionGerm hgO hSO hgy hc₁T
      (y := ⟨A.X.PObj.levelVal 1 y, hyO⟩) hy hφ1 T' hT' hgp
    exact onto_of_isParamGP_restrictTo_rel hO hft hs0 hSon (fun j => (hS j).1) hc₁.1 hsub₁ hy
      hφ1 hyb T' q₀ hGP' w

end Branch

/-! ### The spanning sections relative to `Λ₀` -/

set_option maxHeartbeats 1600000 in
-- the union over the branches of `Λ₀` through `f(x)` of Part I's sections on `W|O`
/-- **The spanning sections of the local constructions relative to `Λ₀`, without bump
functions** (steps (c)–(d) of the proof of Theorem 15.3.9, 2021 pp. 698–699): for tame `X`, an
sc-Fredholm section functor `f` with tame germ data, an sc⁺-multisection `Λ₀`, and sc⁺-sections
of `W` through the smooth fibre points, at every `x ∈ supp(Λ₀ ∘ f)` there are finitely many
global sc⁺-sections `S_j` and an open `W ∋ x` such that (15.1) relative to `Λ₀` holds with the
vectors `S_j(y)` at every `y ∈ supp(Λ₀ ∘ f) ∩ W`. -/
theorem exists_preSeedRel (hX : A.X.IsTame) (hsec : A.B.HasScPlusSectionsThrough)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ₀ : A.W → ℚ≥0} (hΛ₀ : IsScPlusMultisection A Λ₀)
    {x : A.Obj} (hx : 0 < Λ₀ (f x)) :
    ∃ (ℓ : ℕ) (S : Fin ℓ → A.Obj → A.W) (hS : ∀ j, A.B.IsScPlusSection (S j)) (W : Set A.Obj),
      IsOpen W ∧ x ∈ W ∧ ∀ y : A.X.PObj.Level 1, A.X.PObj.levelVal 1 y ∈ W →
        0 < Λ₀ (f (A.X.PObj.levelVal 1 y)) →
          IsParamOntoVecRel f Λ₀ y (fun j => ⟨S j (A.X.PObj.levelVal 1 y), (hS j).1 _⟩) := by
  classical
  have hsecf : IsSection A.P f := hft.isScSmooth.1
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  have hxs : x ∈ A.X.PObj.smoothSet := mem_smoothSet_of_pos hft hΛ₀ hx
  obtain ⟨O₂, k₀, s₀', σ₀, hO₂, hxO₂, hrep₀'⟩ := hΛ₀.exists_isLocalRepOn x
  set s₀ : Fin k₀ → A.Obj → A.W := fun a => extendZero O₂ (s₀' a) with hs₀def
  have hs₀ : ∀ a, IsSection A.P (s₀ a) := fun a => isSection_extendZero O₂ _
  obtain ⟨cat, hcat, hxcat⟩ := A.B.exists_chart_mem x
  -- a domain `O ∋ x` inside `O₂` and inside the base domain of a chart of the atlas
  let D : A.B.Dom := ⟨O₂ ∩ cat.φ.source, hO₂.inter cat.φ.isOpen_source, ⟨x, hxO₂, hxcat⟩,
    cat, hcat, inter_subset_right⟩
  set O : Set A.Obj := D.carrier with hOdef
  have hO : IsOpen O := D.isOpen
  have hxO : x ∈ O := ⟨hxO₂, hxcat⟩
  have : Nonempty O := ⟨⟨x, hxO⟩⟩
  have := A.X.PObj.paracompactSpace_subtype O
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
    (A.X.PObj.restrictOpen hO) A.B
  have hrep₀ : IsLocalRepOn A Λ₀ O s₀ σ₀ := hrep₀'.extendZero.mono hO inter_subset_left
  have hsecO : (A.B.restrictOpen hO).HasScPlusSectionsThrough := D.hasSections
  -- a tame chart centred at `x` inside `O`
  obtain ⟨-, c₀, hc₀, hxc₀, hφ0, -⟩ := hft.germTame x hxs
  set c := c₀.restrictInter hO with hcdef
  have hc : A.B.IsTameChart c := hc₀.restrictInter hO
  have hsub : c.φ.source ⊆ O := c₀.restrictInter_source_subset hO
  have hxc : x ∈ c.φ.source := ⟨hxc₀, hxO⟩
  have hφ0c : c.φ x = 0 := hφ0
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  set q₀ : pullbackSpace A.P (Subtype.val : O → A.Obj) :=
    restrictSection A.P O f hsecf ⟨x, hxO⟩ with hq₀
  -- the sections for each branch through `f(x)`
  have hpt : ∀ a, ∃ (k : ℕ) (S : Fin k → A.Obj → A.W) (_ : ∀ i, A.B.IsScPlusSection (S i)),
      (f x = s₀ a x → (c.restrictTo A.B.continuous hO hsub q₀).IsParamGP
        (subRestrict (O := O) f (s₀ a) hsecf) (fun j => negRestrict (O := O) (S j)) T) := by
    intro a
    by_cases hfa : f x = s₀ a x
    · obtain ⟨k, S, hS, hGP⟩ := exists_sections_isParamGP_branch hO hsecO hsec hft
        (hrep₀.2.1 a) hc hsub hxc hφ0c hfa T hT q₀
      exact ⟨k, S, hS, fun _ => hGP⟩
    · exact ⟨0, fun i => i.elim0, fun i => i.elim0, fun h => absurd h hfa⟩
  choose k s hs hGP using hpt
  set e := Fintype.equivFin (Σ a : Fin k₀, Fin (k a)) with hedef
  set S : Fin (Fintype.card (Σ a : Fin k₀, Fin (k a))) → A.Obj → A.W :=
    fun j => s (e.symm j).1 (e.symm j).2 with hSdef
  have hS : ∀ j, A.B.IsScPlusSection (S j) := fun j => hs _ _
  have hGPS : ∀ a, f x = s₀ a x → (c.restrictTo A.B.continuous hO hsub q₀).IsParamGP
      (subRestrict (O := O) f (s₀ a) hsecf) (fun j => negRestrict (O := O) (S j)) T :=
    fun a hfa => (hGP a hfa).comp (fun i => e ⟨a, i⟩) (fun i => by
      change negRestrict (O := O) (s a i) =
        negRestrict (O := O) (s (e.symm (e ⟨a, i⟩)).1 (e.symm (e ⟨a, i⟩)).2)
      rw [Equiv.symm_apply_apply])
  -- the openness for each branch
  have hopen : ∀ a, ∃ Wa : Set A.Obj, IsOpen Wa ∧ x ∈ Wa ∧ ∀ y : A.X.PObj.Level 1,
      A.X.PObj.levelVal 1 y ∈ Wa →
        f (A.X.PObj.levelVal 1 y) = s₀ a (A.X.PObj.levelVal 1 y) →
          BranchOnto f (s₀ a) O S (fun j => (hS j).1) y := by
    intro a
    by_cases hfa : f x = s₀ a x
    · obtain ⟨Wa, hWa, hxWa, -, h⟩ := exists_open_onto_branch_local hO hX hft (hrep₀.2.1 a) hS hc
        hsub hxc hφ0c hfa T hT q₀ (hGPS a hfa)
      exact ⟨Wa, hWa, hxWa, h⟩
    · exact ⟨{y ∈ O | f y ≠ s₀ a y}, isOpen_sep_ne hfc hO (hrep₀.2.1 a).continuousOn,
        ⟨hxO, hfa⟩, fun y hy h => absurd h hy.2⟩
  choose Wa hWao hxWa hWa using hopen
  refine ⟨_, S, hS, (⋂ a, Wa a) ∩ O, (isOpen_iInter_of_finite hWao).inter hO,
    ⟨mem_iInter.2 hxWa, hxO⟩, fun y hyW hpos => ?_⟩
  have hys : A.X.PObj.levelVal 1 y ∈ A.X.PObj.smoothSet := mem_smoothSet_of_pos hft hΛ₀ hpos
  obtain ⟨-, c₁, hc₁, hyc₁, hφ1, -⟩ := hft.germTame _ hys
  set c' := c₁.restrictInter hO with hc'def
  have hc' : A.B.IsTameChart c' := hc₁.restrictInter hO
  have hsub' : c'.φ.source ⊆ O := c₁.restrictInter_source_subset hO
  have hyc' : A.X.PObj.levelVal 1 y ∈ c'.φ.source := ⟨hyc₁, hyW.2⟩
  have hφ1' : c'.φ (A.X.PObj.levelVal 1 y) = 0 := hφ1
  obtain ⟨n', Wq', T', hT'⟩ := c'.φ.model.isPartialQuadrant
  intro L hL φ hφ hyφ m V Tφ hTφ w
  let d : LocalLinData A Λ₀ y := ⟨O, hO, k₀, s₀, σ₀, hrep₀, c', hc'.1, hsub', hyc'⟩
  rw [linearization_eq hf d] at hL
  obtain ⟨a, hay, rfl⟩ := (mem_support_linSumIntr_iff hsecf hrep₀.1
    (fun b => (hrep₀.2.1 b).1) hsub' hyc' L).1 hL
  obtain ⟨u, hu, τ, hτ⟩ := hWa a y (mem_iInter.1 hyW.1 a) hay.symm c' hc' hsub' hyc' hφ1' n'
    Wq' T' hT' w
  refine ⟨u, ?_, τ, hτ⟩
  rw [reducedTangentFiber_eq (hφ := hφ) (hx := hyφ) (T := Tφ) (hψ := c'.isChart)
    (hx' := hyc') (T' := T') hTφ hT']
  exact hu

/-! ### The seeds at a point from one function -/

/-- **The seeds of the local constructions relative to `Λ₀` at one point, from one function**
(steps (c)–(d) of the proof of Theorem 15.3.9, 2021 pp. 698–699, with a function of Remark
9.5.19 in place of bump functions).  Let `X` be tame, `f` an sc-Fredholm section functor with
tame germ data, `Λ₀` an sc⁺-multisection, `N` an auxiliary norm, and let `W` have sc⁺-sections
through its smooth fibre points.  For `x ∈ supp(Λ₀ ∘ f)`, an open `O ∋ x` and `ε > 0` there is an
open `O'' ∋ x` in `O` such that every sc-smooth `β : X → ℝ` with `β(x) ≠ 0` and support in `O''`
gives the seeds of `HasLocalParamSeedsRel` at `(x, O, ε)`. -/
theorem exists_seeds_of_function_rel (hX : A.X.IsTame) (hsec : A.B.HasScPlusSectionsThrough)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ₀ : A.W → ℚ≥0} (hΛ₀ : IsScPlusMultisection A Λ₀)
    {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) {x : A.Obj} (hx : 0 < Λ₀ (f x)) {O : Set A.Obj}
    (hO : IsOpen O) (hxO : x ∈ O) {ε : ℝ} (hε : 0 < ε) :
    ∃ O'' : Set A.Obj, IsOpen O'' ∧ x ∈ O'' ∧ O'' ⊆ O ∧
      ∀ β : A.Obj → ℝ, A.X.PObj.IsScSmoothMap realPolyfold β → β x ≠ 0 → tsupport β ⊆ O'' →
        ∃ (ℓ : ℕ) (s : Fin ℓ → A.Obj → A.W) (hs : ∀ j, A.B.IsScPlusSection (s j)),
          (∀ j, sectionSupport A.P (s j) ⊆ O) ∧ (∀ j y, normW N (s j y) ≤ ε) ∧
          ∃ W : Set A.Obj, IsOpen W ∧ x ∈ W ∧ ∀ y : A.X.PObj.Level 1,
            A.X.PObj.levelVal 1 y ∈ W → 0 < Λ₀ (f (A.X.PObj.levelVal 1 y)) →
              IsParamOntoVecRel f Λ₀ y
                (fun j => ⟨s j (A.X.PObj.levelVal 1 y), (hs j).1 _⟩) := by
  obtain ⟨ℓ, S, hS, W, hW, hxW, hon⟩ := exists_preSeedRel hX hsec hf hft hΛ₀ hx
  obtain ⟨O'', hO'', hxO'', hsubO, H⟩ := exists_seeds_of_function f Λ₀ hN hS hO hxO hε
  refine ⟨O'', hO'', hxO'', hsubO, fun β hβ hβx hsupp => ?_⟩
  obtain ⟨s, hs, hsO, hsN, hsw⟩ := H β hβ hsupp
  have hβc : Continuous β := continuousOn_univ.1 hβ.continuousOn
  exact ⟨ℓ, s, hs, hsO, hsN, W ∩ {y | β y ≠ 0}, hW.inter (isOpen_ne_fun hβc continuous_const),
    ⟨hxW, hβx⟩, fun y hy hpos => hsw y hy.2 (hon y hy.1 hpos)⟩

/-- **The analytic input of the local constructions relative to `Λ₀` from functions at the
points of `supp(Λ₀ ∘ f)`** (`HasLocalParamSeedsRel`): for tame `X`, `f` an sc-Fredholm section
functor with tame germ data, `Λ₀` an sc⁺-multisection, `N` an auxiliary norm, sc⁺-sections
through the smooth fibre points, and at every `x ∈ supp(Λ₀ ∘ f)` and every open `O'' ∋ x` an
sc-smooth function `β` with `β(x) ≠ 0` and support in `O''`. -/
theorem hasLocalParamSeedsRel_of_functions (hX : A.X.IsTame)
    (hsec : A.B.HasScPlusSectionsThrough) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ₀ : A.W → ℚ≥0} (hΛ₀ : IsScPlusMultisection A Λ₀) {N : A.B.One → ℝ}
    (hN : A.B.IsAuxNorm N)
    (hβ : ∀ x, 0 < Λ₀ (f x) → ∀ O'' : Set A.Obj, IsOpen O'' → x ∈ O'' →
      ∃ β : A.Obj → ℝ, A.X.PObj.IsScSmoothMap realPolyfold β ∧ β x ≠ 0 ∧ tsupport β ⊆ O'') :
    HasLocalParamSeedsRel A f Λ₀ N := by
  intro x hx O hO hxO ε hε
  obtain ⟨O'', hO'', hxO'', -, H⟩ :=
    exists_seeds_of_function_rel hX hsec hf hft hΛ₀ hN hx hO hxO hε
  obtain ⟨β, hβs, hβx, hβsupp⟩ := hβ x hx O'' hO'' hxO''
  exact H β hβs hβx hβsupp

end SBLocalization

end Polyfold
