import Polyfold.Chapter5.Compactness
import Polyfold.Chapter5.StrongBundleShift
import Polyfold.Chapter3.LinearizationChartsScG
import Polyfold.Chapter3.GlobalIFTNearbyOntoXi

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §5.2,
**Corollary 5.8** *(book 2017: Corollary 5.1)*, at the level of sections of the shifted strong
bundle `P¹ : Y¹ → X¹` (`Chapter5/StrongBundleShift.lean`).

# Corollary 5.8 on the shifted strong bundle

## The text, paraphrased

(Corollary 5.8) Let `f` be an sc-Fredholm section of the strong bundle `P : Y → X` over the tame
M-polyfold `X` with compact solution set.  Then `f^i` is an sc-Fredholm section of
`P^i : Y^i → X^i` with compact solution set.  ("It is a priori clear that `f^i` is sc-Fredholm.")

## What is formalized

* `StrongBundleChart.principal_sectionShift`: in the index raise `Φ¹` of a chart, **the principal
  part of `f¹` is the level-`1` map of the principal part of `f`**; `shift_φ_eq_zero` (the shifted
  chart is centred where the chart is).
* `IsFillingGerm.mem_range_toBase_of_fillDefect`: **condition (3) of Definition 3.4 holds on every
  level at the centre of every datum of Definition 3.11** (not only at a zero): for
  `v ∈ ker Dr(0)` with `Dk(0)v ∈ F_m`, `v ∈ E_m`.  Reduction to the case of a zero (Chapter 3 item
  237): `g' = g + ŝ ∘ r` with `ŝ(z) = Γ(z, −g(0))` fills `f̂ + ŝ` with the same fill defect,
  `g'(0) = 0`, and `Dg'(0)` is sc-Fredholm (Proposition 3.52 in sc form for `g'` and the sc⁺-germ
  `s + Γ¹(r(·), −s(0))`).
* `toBase_scDeriv_r_shift` (`ι Dr¹(0) = Dr(0) ι`), `toBase_ρCLM_shift` (`ι ρ¹(0) = ρ(0) ι`),
  `IsFillingGerm.germ_shift`: **the germ field of the level-`1` filling**: the fill defect of `g¹`
  is the level-`1` map of that of `g` (an sc¹-germ, `IsSc1GermWith.shift`), and `Dk¹(0)` is a
  topological isomorphism `ker Dr¹(0) → ker ρ¹(0)` (open mapping theorem).
* `StrongBundleChart.shift_filling_eq_on`, `shift_filling_mem_of_fixed`, `shift_isFillingGerm`:
  **`g¹` is a filling germ of the principal part of `f¹` in `Φ¹`**.
* `Polyfold.isScFredholmGerm_sectionShift`: `f¹` is an sc-Fredholm germ at every smooth point of
  `X¹`; **`Polyfold.corollary_5_8_isScFredholmSection`**: **`f¹` is an sc-Fredholm section of
  `P¹`** (Definition 3.14, germ reading); **`Polyfold.corollary_5_8`** (**Corollary 5.8 for
  `i = 1`**): with compact solution set; **`Polyfold.corollary_5_8_two`**: the same for
  `f² = (f¹)¹` on `P² = (P¹)¹`, by iteration.
* `Polyfold.corollary_5_8_data`: the data of the corollary unpacked in the shifted chart.

## What the text leaves implicit, and the choices made

* **"It is a priori clear that `f^i` is sc-Fredholm"** hides condition (3) of the filling on level
  `1`, which does not follow from level `0` alone (Findings, Chapter 5, item 22).  It holds for
  the data of Definition 3.11 by the argument of `IsFillingGerm.mem_range_toBase_of_fillDefect`
  (regularity of `Dg'(0)` through the conjugation to a basic germ).  No hypothesis beyond the text's
  is added.
* **Tameness**: the text assumes `X` tame; it is not used.  The tame variant (germ data in tame
  charts of `P¹`) is not stated: the tameness of the shifted charts is not proved (see
  `StrongBundleShift.lean`).
* **`i ≥ 2`**: by iteration of `StrongBundle.shift` for every fixed `i` (`corollary_5_8_two` for
  `i = 2`); a uniform family indexed by `i` is not formalized.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-! ### Condition (3) of a filling on every level, at any smooth point -/

section FillerLevels

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- The value at `0` of an sc-smooth germ into `F¹` is a smooth point of `F`. -/
lemma IsScSmoothGerm.toBase_zero_mem_smooth {G : ScNbhdGerm E C} {s : E 0 → F 1}
    (hs : IsScSmoothGerm (F := F.shift) G s) : F.toBase 1 (s 0) ∈ F.smooth := by
  have hs0 : IsSc0Germ (F := F.shift) G s := hs 0
  refine F.mem_smooth_iff.2 fun m => ?_
  obtain ⟨w, hw⟩ := hs0.mem_range m 0 (G.zero_mem m)
  rw [map_zero] at hw
  obtain ⟨y, hy⟩ := StrongBundle.range_toBase_mono F (Nat.le_succ m) ⟨w, rfl⟩
  exact ⟨y, by rw [hy, F.shift_toBase, hw]⟩

/-- **Condition (3) of a filling germ holds on every level at every centre of a datum of Definition
3.11** (not only at a zero; Findings, Chapter 5, item 144, completing item 22): let `g` be a filling
germ of `f̂` (a section of `K → O`, `0 ∈ O`) on a germ `G ⊆ U`, with a derivative family `Dk` of the
fill defect `k = [1 − ρ(r(·))]g`, `s` an sc⁺-germ with `s(0) = g(0)` and `g − s` conjugated to a
basic germ.  If `v ∈ ker Dr(0)` and `Dk(0)v ∈ F_m`, then `v ∈ E_m`.  Proof: `c₀ = g(0)` is smooth
(it is `ι s(0)`); `ŝ(z) = Γ(z, −c₀)` is a section of `K → O`, sc-smooth on `U`, so `g' = g + ŝ ∘ r`
fills `f̂ + ŝ` with **the same** `k` (Lemma 3.17, `IsFillingGerm.add_section`), `g'(0) = 0`, and
`g' − s'` with the sc⁺-germ `s' = s + Γ¹(r(·), −s(0))` is `g − s`; hence `Dg'(0)` is sc-Fredholm
(`proposition_3_52_local_sc`), `Dk(0) = (1 − ρ(0))Dg'(0)` (`fillDefect_deriv_zero_eq_rho`), and the
case of a zero applies (`IsFillingGerm.mem_range_toBase_of_scDeriv_r_eq_zero`, Chapter 3 item
237). -/
theorem IsFillingGerm.mem_range_toBase_of_fillDefect (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFillingGerm hU hR h0 fb g)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ))
    {G : ScNbhdGerm E C} (hGU : G.U 0 ⊆ U) (hg : IsScSmoothGerm G g)
    {Dk : E 1 → E 0 →L[ℝ] F 0} (hDk : IsSc1GermWith G (fillDefect R g) Dk)
    {s : E 0 → F 1} (hs : IsScPlusGerm C U s) (hs0 : F.toBase 1 (s 0) = g 0)
    (hconj : IsConjugateToBasicGerm U fun u => g u - F.toBase 1 (s u))
    {m : ℕ} {v : E 0} (hv : scDeriv U (r R) 0 v = 0) (hy : Dk 0 v ∈ range (F.toBase m)) :
    v ∈ range (E.toBase m) := by
  have hQ := hU.isPartialQuadrant.isQuadrantLike
  have hUd := hU.isScDomain
  obtain ⟨Gs, hGsU, hsG⟩ := hs
  -- the smooth value `−c₀ = −g(0) = ι(−s(0))`
  set c₁ : F 1 := -s 0 with hc₁
  have hc₁s : F.toBase 1 c₁ ∈ F.smooth := by
    rw [hc₁, map_neg]; exact F.smooth.neg_mem hsG.toBase_zero_mem_smooth
  -- `ŝ(z) = Γ(z, −c₀)` and `σ(y) = Γ¹(r(y), −s(0))`
  set sh : E 0 → F 0 := fun z => (R (z, F.toBase 1 c₁)).2 with hsh
  set σ : E 0 → F 1 := fun y => (shiftFiber R (r R y, c₁)).2 with hσ
  have hconst : IsScSmooth (E := E) (F := F.shift) U fun _ => c₁ :=
    isScSmooth_const_of_smooth hUd hc₁s
  have hsh_sm : IsScSmooth U sh := by
    have h1 : IsScSmooth (F := E.prod F) U
        (scPair (_root_.id : E 0 → E 0) fun _ => F.toBase 1 c₁) :=
      (isScSmooth_id hUd).scPair hUd (hconst.toBase_shift hUd)
    have h2 := IsScSmooth.comp (G := E.prod F) hUd (hU.prod_univ F).isScDomain hR.isScSmooth_zero h1
      fun z hz => (show (z, F.toBase 1 c₁) ∈ U ×ˢ univ from ⟨hz, mem_univ _⟩)
    exact (h2.snd hUd).congr hUd fun _ _ => rfl
  have hσ_sm : IsScSmooth (F := F.shift) U σ := by
    have h1 : IsScSmooth (F := E.prod F.shift) U (scPair (r R) fun _ => c₁) :=
      (r_isScSmooth hU hR).scPair hUd hconst
    have h2 := IsScSmooth.comp (G := E.prod F.shift) hUd (hU.prod_univ F.shift).isScDomain
      hR.isScSmooth_one h1
      fun y hy => (show (r R y, c₁) ∈ U ×ˢ univ from ⟨r_mem hR hy, mem_univ _⟩)
    exact (h2.snd hUd).congr hUd fun _ _ => rfl
  -- `ŝ` is a section of `K → O`
  have hshK : ∀ x ∈ r R '' U, (x, sh x) ∈ R '' (U ×ˢ univ) := fun x hx =>
    (hR.mem_image_iff hU).2 ⟨hx, hR.fiber_idem hU hx _⟩
  have hr0 : r R 0 = 0 := r_eq_self hR h0O
  have hgfb0 : fb 0 = g 0 := hfill.eq_on.self_of_nhds h0O
  have hK0 : ρ R 0 (g 0) = g 0 := by
    rw [← hgfb0]; exact ρ_eq_self_of_mem_K hR h0 (hfK 0 h0O)
  have hsh0 : sh 0 = -g 0 := by
    change ρ R 0 (F.toBase 1 c₁) = -g 0
    rw [hc₁, map_neg, hs0, (ρ_isLinear hR h0).map_neg, hK0]
  -- the filling `g' = g + ŝ ∘ r` of `f̂ + ŝ`
  have hfill' := hfill.add_section hU hR h0 hsh_sm hshK
  set g' : E 0 → F 0 := fun y => g y + sh (r R y) with hg'def
  have hg'0 : g' 0 = 0 := by
    change g 0 + sh (r R 0) = 0
    rw [hr0, hsh0, add_neg_cancel]
  have hfb0' : (fun x => fb x + sh x) 0 = 0 := by
    change fb 0 + sh 0 = 0
    rw [hgfb0, hsh0, add_neg_cancel]
  have hfK' : ∀ x ∈ r R '' U, (x, (fun x => fb x + sh x) x) ∈ R '' (U ×ˢ univ) := by
    intro x hx
    have h1 := ((hR.mem_image_iff hU).1 (hfK x hx)).2
    have h2 := ((hR.mem_image_iff hU).1 (hshK x hx)).2
    refine (hR.mem_image_iff hU).2 ⟨hx, ?_⟩
    change (R (x, fb x + sh x)).2 = fb x + sh x
    rw [(hR.fiber_linear x (mem_U_of_mem_O hR hx)).map_add]
    exact congrArg₂ (· + ·) h1 h2
  have hsr : IsScSmoothGerm G fun y => sh (r R y) :=
    (IsScSmooth.comp hUd hUd hsh_sm (r_isScSmooth hU hR) fun u hu => r_mem hR hu
      ).isScSmoothGerm_of_subset hQ hU.relOpen h0 hGU
  have hg' : IsScSmoothGerm G g' := hg.add hQ hsr
  have hg'1 := (hg' 1).1.isSc1GermWith_scDerivGerm
  -- the fill defect does not change
  have heq : EqOn (fillDefect R g) (fillDefect R g') (G.U 0) := by
    intro y hy
    have hyU := hGU hy
    have hfix : ρ R (r R y) (sh (r R y)) = sh (r R y) :=
      ρ_eq_self_of_mem_K hR (r_mem hR hyU) (hshK _ ⟨y, hyU, rfl⟩)
    simp only [fillDefect, hg'def]
    rw [(ρ_isLinear hR (r_mem hR hyU)).map_add, hfix]
    abel
  have hk' : IsSc1GermWith G (fillDefect R g') Dk := hDk.congr heq
  have hDkeq : Dk 0 = scDerivGerm G g' 0 - (ρCLM hR h0).comp (scDerivGerm G g' 0) :=
    fillDefect_deriv_zero_eq_rho hU hR h0 h0O hGU hg'1 hg'0 hk'
  -- the sc⁺-germ `s' = s + σ`, with `g' − s' = g − s` on `U`
  set s' : E 0 → F 1 := fun y => s y + σ y with hs'def
  have hσι : ∀ y ∈ U, F.toBase 1 (σ y) = sh (r R y) := fun y hy =>
    hR.toBase_shiftFiber_snd (p := (r R y, c₁)) (r_mem hR hy)
  have hs' : IsScSmoothGerm (F := F.shift) Gs s' :=
    hsG.add hQ (hσ_sm.isScSmoothGerm_of_subset hQ hU.relOpen h0 hGsU)
  have hs'1 := (hs' 1).1.isSc1GermWith_scDerivGerm
  have hs0' : F.toBase 1 (s' 0) = g' 0 := by
    change F.toBase 1 (s 0 + σ 0) = g 0 + sh (r R 0)
    rw [map_add, hs0, hσι 0 h0]
  have hconj' : IsConjugateToBasicGerm U fun u => g' u - F.toBase 1 (s' u) := by
    refine hconj.congr fun u hu => ?_
    change g u - F.toBase 1 (s u) = g u + sh (r R u) - F.toBase 1 (s u + σ u)
    rw [map_add, hσι u hu]
    abel
  obtain ⟨d'⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj'
  obtain ⟨hDg, -, -, -, hDgF, -⟩ :=
    proposition_3_52_local_sc hU hR h0 h0O hfill' hfb0' hfK' hGU hg'1 hs'1 hs0' d'
  have hy' : scDerivGerm G g' 0 v - ρCLM hR h0 (scDerivGerm G g' 0 v) ∈ range (F.toBase m) := by
    have := congrArg (fun T : E 0 →L[ℝ] F 0 => T v) hDkeq
    simp only [sub_apply, ContinuousLinearMap.comp_apply] at this
    rw [← this]; exact hy
  exact hfill'.mem_range_toBase_of_scDeriv_r_eq_zero hg'0 h0O hfK' hGU hg'1 hDg hDgF hv hy'

/-- **The derivative of the shifted base retraction at `0`** (Proposition 1.17 for `r`):
`ι Dr¹(0)v = Dr(0)(ι v)` for `v ∈ E₁`, `r¹ = r(R¹)` the base retraction of the index raise. -/
theorem toBase_scDeriv_r_shift (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) (v : E 1) :
    E.toBase 1 (scDeriv (E := E.shift) (F := E.shift) (E.lvlSet U 1) (r (strongShift R)) 0 v) =
      scDeriv U (r R) 0 (E.toBase 1 v) := by
  have hQ := hU.isPartialQuadrant.isQuadrantLike
  have hU1 := hU.shift
  have hR1 := hR.shift hU
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have hrG := (r_isScSmooth hU hR).isSc1.isSc1GermWith_ofSet hU.relOpen h0
  have hr1G := (r_isScSmooth hU1 hR1).isSc1.isSc1GermWith_ofSet hU1.relOpen h01
  have hUeq : ∀ m, (ScNbhdGerm.ofSet hU.relOpen h0).shift.U m =
      (ScNbhdGerm.ofSet hU1.relOpen h01).U m := by
    intro m; ext x
    simp only [ScNbhdGerm.shift_U, ScNbhdGerm.ofSet_U, ScBanach.mem_lvlSet]
    rw [E.shift_toBase]
  have hrG1 := ((hrG.shift hQ).of_U_eq hUeq).congr (f' := r (strongShift R)) fun u hu => by
    have hu' : E.toBase 1 u ∈ U := hu
    exact levelMap_eq_of_toBase_eq (hR.toIsStrongBundleMap.toBase_base_strongShift hu')
  have heqD := hrG1.eq_of_uniqueDiffWithinAt hr1G ((ScNbhdGerm.ofSet hU1.relOpen h01).zero_mem 1)
    ((ScNbhdGerm.ofSet hU1.relOpen h01).uniqueDiffWithinAt hQ.shift 1
      ((ScNbhdGerm.ofSet hU1.relOpen h01).zero_mem 1))
  rw [← heqD, hrG.toBase_levelDeriv ((ScNbhdGerm.ofSet hU.relOpen h0).zero_mem 2) v, map_zero]

/-- `ι ρ¹(0)h = ρ(0)(ι h)` for the fibre projection of the index raise at `0`. -/
lemma toBase_ρCLM_shift (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) (h01 : (0 : E 1) ∈ E.lvlSet U 1) (h : F 1) :
    F.toBase 1 (ρCLM (E := E.shift) (F := F.shift) (hR.shift hU) h01 h) =
      ρCLM hR h0 (F.toBase 1 h) := by
  rw [ρCLM_apply, ρCLM_apply]
  change F.toBase 1 (strongShift R (0, h)).2 = (R (0, F.toBase 1 h)).2
  rw [hR.toIsStrongBundleMap.toBase_strongShift_snd (by rw [map_zero]; exact h0), map_zero]

/-- **The germ part of the level-`1` filling** (Definition 3.4 (3) and the sc¹ fill defect on
level `1`; Findings, Chapter 5, item 144): for a datum `(g, s)` of Definition 3.11 in a strong
bundle chart, the level-`1` germ `g¹` on the shifted germ `G¹` has the fill defect
`k¹ = [1 − ρ¹(r¹)]g¹ = (k)₁`, an sc¹-germ with the derivative family `(Dk)₁`
(`IsSc1GermWith.shift`), and `Dk¹(0) = Dk(0)|_{E₁}` is a topological linear isomorphism
`ker Dr¹(0) → ker ρ¹(0)`: injective by condition (3) on level `0`, onto by
`IsFillingGerm.mem_range_toBase_of_fillDefect` (`m = 1`), continuous inverse by the open mapping
theorem. -/
theorem IsFillingGerm.germ_shift (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFillingGerm hU hR h0 fb g)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ))
    {s : E 0 → F 1} (hs : IsScPlusGerm C U s) (hs0 : F.toBase 1 (s 0) = g 0)
    (hconj : IsConjugateToBasicGerm U fun u => g u - F.toBase 1 (s u))
    (h01 : (0 : E 1) ∈ E.lvlSet U 1) :
    ∃ G' : ScNbhdGerm E.shift (E.lvlSet C 1), G'.U 0 ⊆ E.lvlSet U 1 ∧
      IsScSmoothGerm (F := F.shift) G' (levelMap (E := E) (F := F) g 1) ∧
      ∃ Dk' : E.shift 1 → E.shift 0 →L[ℝ] F.shift 0,
        IsSc1GermWith (F := F.shift) G'
          (fillDefect (strongShift R) (levelMap (E := E) (F := F) g 1)) Dk' ∧
        ∃ Φ : LinearMap.ker ((scDeriv (E := E.shift) (F := E.shift) (E.lvlSet U 1)
              (r (strongShift R)) (0 : E.shift 1) : E.shift 0 →L[ℝ] E.shift 0) :
              E.shift 0 →ₗ[ℝ] E.shift 0) ≃L[ℝ]
            LinearMap.ker ((ρCLM (E := E.shift) (F := F.shift) (hR.shift hU) h01 :
              F.shift 0 →L[ℝ] F.shift 0) : F.shift 0 →ₗ[ℝ] F.shift 0),
          ∀ v, ((Φ v : LinearMap.ker ((ρCLM (E := E.shift) (F := F.shift) (hR.shift hU) h01 :
              F.shift 0 →L[ℝ] F.shift 0) : F.shift 0 →ₗ[ℝ] F.shift 0)) : F.shift 0) =
            Dk' 0 (v : E.shift 0) := by
  have hQ := hU.isPartialQuadrant.isQuadrantLike
  obtain ⟨G, hGU, hg, Dk, hDk, Φ, hΦ⟩ := hfill.germ
  have hg0 : IsSc0Germ G g := hg 0
  have hRm := hR.toIsStrongBundleMap
  -- `k¹ = (k)₁` on the shifted germ
  have heq1 : EqOn (levelMap (fillDefect R g) 1)
      (fillDefect (strongShift R) (levelMap (E := E) (F := F) g 1)) (G.shift.U 0) := by
    intro y hy
    have hy1 : y ∈ G.U 1 := hy
    have hyU : E.toBase 1 y ∈ U := hGU (G.toBase_mem hy1)
    apply levelMap_eq_of_toBase_eq
    have hr : E.toBase 1 (r (strongShift R) y) = r R (E.toBase 1 y) :=
      hRm.toBase_base_strongShift hyU
    have hrU : E.toBase 1 (r (strongShift R) y) ∈ U := by rw [hr]; exact r_mem hR hyU
    have hgι : F.toBase 1 (levelMap (E := E) (F := F) g 1 y) = g (E.toBase 1 y) :=
      hg0.toBase_levelMap hy1
    change F.toBase 1 (levelMap (E := E) (F := F) g 1 y -
        (strongShift R (r (strongShift R) y, levelMap (E := E) (F := F) g 1 y)).2) =
      g (E.toBase 1 y) - (R (r R (E.toBase 1 y), g (E.toBase 1 y))).2
    rw [map_sub, hRm.toBase_strongShift_snd hrU, hr, hgι]
  have hk1 : IsSc1GermWith (F := F.shift) G.shift
      (fillDefect (strongShift R) (levelMap (E := E) (F := F) g 1)) (levelDeriv Dk 1) :=
    (hDk.shift hQ).congr heq1
  refine ⟨G.shift, fun u hu => hGU (G.toBase_mem hu), fun k => (hg k).shift hQ,
    levelDeriv Dk 1, hk1, ?_⟩
  -- the identifications on level `1`
  set D1 : E 1 →L[ℝ] E 1 :=
    scDeriv (E := E.shift) (F := E.shift) (E.lvlSet U 1) (r (strongShift R)) 0 with hD1def
  set ρ1 : F 1 →L[ℝ] F 1 := ρCLM (E := E.shift) (F := F.shift) (hR.shift hU) h01 with hρ1def
  set L1 : E 1 →L[ℝ] F 1 := levelDeriv Dk 1 (0 : E 2) with hL1def
  have hD1 : ∀ v : E 1, E.toBase 1 (D1 v) = scDeriv U (r R) 0 (E.toBase 1 v) :=
    toBase_scDeriv_r_shift hU hR h0
  have hρ1 : ∀ h : F 1, F.toBase 1 (ρ1 h) = ρCLM hR h0 (F.toBase 1 h) :=
    toBase_ρCLM_shift hU hR h0 h01
  have hL1 : ∀ v : E 1, F.toBase 1 (L1 v) = Dk 0 (E.toBase 1 v) := fun v => by
    rw [hL1def, hDk.toBase_levelDeriv (G.zero_mem 2) v, map_zero]
  have hN : ∀ v : E 1, D1 v = 0 ↔ scDeriv U (r R) 0 (E.toBase 1 v) = 0 := fun v => by
    rw [← hD1, ← map_zero (E.toBase 1)]
    exact (E.toBase_injective 1).eq_iff.symm
  have hM : ∀ h : F 1, ρ1 h = 0 ↔ ρCLM hR h0 (F.toBase 1 h) = 0 := fun h => by
    rw [← hρ1, ← map_zero (F.toBase 1)]
    exact (F.toBase_injective 1).eq_iff.symm
  -- `Dk(0)` maps `ker Dr(0)` into `ker ρ(0)`
  have hkerρ : ∀ w : E 0, scDeriv U (r R) 0 w = 0 → ρCLM hR h0 (Dk 0 w) = 0 := by
    intro w hw
    have := (Φ ⟨w, hw⟩).2
    rw [hΦ] at this
    exact this
  set N1 := LinearMap.ker (D1 : E 1 →ₗ[ℝ] E 1) with hN1
  set M1 := LinearMap.ker (ρ1 : F 1 →ₗ[ℝ] F 1) with hM1
  have hT : ∀ v : N1, L1 (v : E 1) ∈ M1 := by
    intro v
    change ρ1 (L1 v) = 0
    rw [hM, hL1]
    exact hkerρ _ ((hN v).1 v.2)
  set T : N1 →L[ℝ] M1 := (L1.comp N1.subtypeL).codRestrict M1 hT with hTdef
  have : CompleteSpace N1 := (isClosed_singleton.preimage D1.continuous).completeSpace_coe
  have : CompleteSpace M1 := (isClosed_singleton.preimage ρ1.continuous).completeSpace_coe
  have hinj : LinearMap.ker (T : N1 →ₗ[ℝ] M1) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have hv' : L1 (v : E 1) = 0 := congrArg Subtype.val hv
    have h1 : Dk 0 (E.toBase 1 v) = 0 := by rw [← hL1, hv', map_zero]
    have hw : scDeriv U (r R) 0 (E.toBase 1 v) = 0 := (hN v).1 v.2
    have h2 : Φ ⟨E.toBase 1 v, hw⟩ = 0 := Subtype.ext (by rw [hΦ]; exact h1)
    have h3 : (⟨E.toBase 1 v, hw⟩ : LinearMap.ker ((scDeriv U (r R) (0 : E 1) : E 0 →L[ℝ] E 0) :
        E 0 →ₗ[ℝ] E 0)) = 0 := by
      rw [← Φ.map_zero] at h2; exact Φ.injective h2
    exact Subtype.ext (E.toBase_injective 1 (by simpa using congrArg Subtype.val h3))
  have hsurj : LinearMap.range (T : N1 →ₗ[ℝ] M1) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro w
    have hwρ : ρCLM hR h0 (F.toBase 1 (w : F 1)) = 0 := (hM w).1 w.2
    set v₀ := Φ.symm ⟨F.toBase 1 (w : F 1), hwρ⟩ with hv₀
    have hDv₀ : Dk 0 (v₀ : E 0) = F.toBase 1 (w : F 1) := by
      rw [← hΦ, hv₀, Φ.apply_symm_apply]
    obtain ⟨v, hv⟩ := hfill.mem_range_toBase_of_fillDefect hU hR h0 h0O hfK hGU hg hDk hs hs0 hconj
      (m := 1) v₀.2 ⟨w, hDv₀.symm⟩
    have hvN : v ∈ N1 := by
      change D1 v = 0
      rw [hN, hv]; exact v₀.2
    refine ⟨⟨v, hvN⟩, Subtype.ext (F.toBase_injective 1 ?_)⟩
    change F.toBase 1 (L1 v) = _
    rw [hL1, hv, hDv₀]
  exact ⟨ContinuousLinearEquiv.ofBijective T hinj hsurj, fun v => rfl⟩

end FillerLevels

namespace StrongBundleChart

variable {c : StrongBundleChart PX P} (hc : B.IsChart c) (y₀ : B.ShiftSpace)

/-- **The principal part of `f¹` in the shifted chart is the level-`1` map of the principal part
of `f`**: `(f¹)^(z) = f̂₁(z)` for `z ∈ O¹ = O ∩ E₁`. -/
theorem principal_sectionShift (hf : B.IsScSmoothSection f) {z : c.φ.model.E 1}
    (hz : c.φ.model.E.toBase 1 z ∈ c.φ.model.O) :
    (c.shift hc y₀).principal (B.sectionShift f) z =
      levelMap (E := c.φ.model.E) (F := c.F) (c.principal f) 1 z := by
  symm
  apply levelMap_eq_of_toBase_eq
  set x' := (c.shift hc y₀).φ.symm z with hx'
  have hx'v : PX.levelVal 1 x' = c.φ.symm (c.φ.model.E.toBase 1 z) :=
    MPolyfold.levelChart_symm_apply c.isChart (B.shiftProj y₀) hz
  have hy : B.sectionShift f x' ∈ (c.shift hc y₀).toPartialEquiv.source := by
    change B.toMPolyfold0.levelVal 1 (B.sectionShift f x') ∈ c.toPartialEquiv.source
    rw [StrongBundle.levelVal_sectionShift hf, c.source_eq, mem_preimage, hf.1, hx'v]
    exact c.φ.symm_mapsTo hz
  change c.F.toBase 1 ((c.shift hc y₀) (B.sectionShift f x')).2 = _
  rw [toBase_shift_apply_snd hc y₀ hy, StrongBundle.levelVal_sectionShift hf, hx'v]
  rfl

/-- The shifted chart is centred at `x` when the chart is centred at `x`. -/
lemma shift_φ_eq_zero {x : PX.Level 1} (hx : PX.levelVal 1 x ∈ c.φ.source)
    (h0 : c.φ (PX.levelVal 1 x) = 0) : (c.shift hc y₀).φ x = 0 := by
  apply c.φ.model.E.toBase_injective 1
  change c.φ.model.E.toBase 1 (MPolyfold.levelLift c.φ 1 (PX.levelVal 1 x)) = _
  rw [PX.toBase_levelLift c.isChart hx (MPolyfold.levelVal_mem x), h0]
  exact (map_zero (c.φ.model.E.toBase 1)).symm

/-- Near `0`, a point of `U¹` lies in the level `1` of any germ of neighbourhoods in `C ⊇ U`. -/
lemma _root_.Polyfold.ScNbhdGerm.eventually_mem_one {E : ScBanach} {C U : Set (E 0)}
    (hU : U ⊆ C) (G : ScNbhdGerm E C) :
    ∀ᶠ u in 𝓝 (0 : E 1), u ∈ E.lvlSet U 1 → u ∈ G.U 1 := by
  obtain ⟨Ok, hOk, hGkeq⟩ := G.relOpen 1
  have h0Ok : (0 : E 1) ∈ Ok := by
    have := G.zero_mem 1; rw [hGkeq] at this; exact this.1
  filter_upwards [hOk.mem_nhds h0Ok] with u hu huU
  rw [hGkeq]
  exact ⟨hu, hU huU⟩

omit [T2Space Y] [ParacompactSpace Y] in
/-- `U ⊆ C` for a strong bundle chart. -/
lemma U_subset_C (c : StrongBundleChart PX P) : c.U ⊆ c.φ.model.C := by
  obtain ⟨O, -, hO⟩ := c.relOpen.relOpen
  rw [hO]; exact inter_subset_right

/-- `ι : E₁ → E₀` is continuous at `0`. -/
lemma tendsto_toBase_one (E : ScBanach) : Tendsto (E.toBase 1) (𝓝 0) (𝓝 0) := by
  have := (E.toBase 1).continuous.tendsto 0
  rwa [map_zero] at this

variable {hc y₀}

/-- **Condition (1) of the filling on level `1`** (Definition 3.4 (1) for `g¹` in the shifted
chart): `(f¹)^ = g¹` on `O¹` near `0`, from `f̂ = g` on `O` near `0`. -/
theorem shift_filling_eq_on (hf : B.IsScSmoothSection f) {g : c.φ.model.E 0 → c.F 0}
    (h1 : ∀ᶠ x in 𝓝 (0 : c.φ.model.E 0), x ∈ StrongRetr.r c.R '' c.U → c.principal f x = g x) :
    ∀ᶠ z in 𝓝 (0 : c.φ.model.E 1),
      z ∈ StrongRetr.r (c.shift hc y₀).R '' (c.shift hc y₀).U →
        (c.shift hc y₀).principal (B.sectionShift f) z =
          levelMap (E := c.φ.model.E) (F := c.F) g 1 z := by
  filter_upwards [(tendsto_toBase_one c.φ.model.E).eventually h1] with z hz hzO
  rw [(c.shift hc y₀).r_image] at hzO
  have hzO' : c.φ.model.E.toBase 1 z ∈ c.φ.model.O := hzO
  rw [principal_sectionShift hc y₀ hf hzO']
  unfold levelMap
  rw [hz (by rw [c.r_image]; exact hzO')]

/-- **Condition (2) of the filling on level `1`** (Definition 3.4 (2) for `g¹`): a point `y ∈ U¹`
near `0` with `g¹(y) = ρ¹(r¹(y))g¹(y)` lies in `O¹`; apply `ι` and condition (2) on level `0`. -/
theorem shift_filling_mem_of_fixed {g : c.φ.model.E 0 → c.F 0}
    {G : ScNbhdGerm c.φ.model.E c.φ.model.C} (hg : IsSc0Germ G g)
    (h2 : ∀ᶠ y in 𝓝 (0 : c.φ.model.E 0), y ∈ c.U →
      g y = StrongRetr.ρ c.R (StrongRetr.r c.R y) (g y) → y ∈ StrongRetr.r c.R '' c.U) :
    ∀ᶠ y in 𝓝 (0 : c.φ.model.E 1), y ∈ (c.shift hc y₀).U →
      levelMap (E := c.φ.model.E) (F := c.F) g 1 y =
        StrongRetr.ρ (c.shift hc y₀).R (StrongRetr.r (c.shift hc y₀).R y)
          (levelMap (E := c.φ.model.E) (F := c.F) g 1 y) →
      y ∈ StrongRetr.r (c.shift hc y₀).R '' (c.shift hc y₀).U := by
  have hR := c.isRetraction.toIsStrongBundleMap
  filter_upwards [(tendsto_toBase_one c.φ.model.E).eventually h2,
    G.eventually_mem_one c.U_subset_C] with y hy2 hy3 hyU hfix
  have hyG := hy3 hyU
  have hyU' : c.φ.model.E.toBase 1 y ∈ c.U := hyU
  have hr : c.φ.model.E.toBase 1 (StrongRetr.r (strongShift c.R) y) =
      StrongRetr.r c.R (c.φ.model.E.toBase 1 y) := hR.toBase_base_strongShift hyU'
  have hrU : c.φ.model.E.toBase 1 (StrongRetr.r (strongShift c.R) y) ∈ c.U := by
    rw [hr]; exact StrongRetr.r_mem c.isRetraction hyU'
  have hgι : c.F.toBase 1 (levelMap (E := c.φ.model.E) (F := c.F) g 1 y) =
      g (c.φ.model.E.toBase 1 y) := hg.toBase_levelMap hyG
  have h := congrArg (c.F.toBase 1) hfix
  change c.F.toBase 1 (levelMap (E := c.φ.model.E) (F := c.F) g 1 y) =
    c.F.toBase 1 (strongShift c.R (StrongRetr.r (strongShift c.R) y,
      levelMap (E := c.φ.model.E) (F := c.F) g 1 y)).2 at h
  rw [hR.toBase_strongShift_snd hrU, hr, hgι] at h
  have hO := hy2 hyU' h
  rw [(c.shift hc y₀).r_image]
  rw [c.r_image] at hO
  exact hO

omit [T2Space Y] [ParacompactSpace Y] in
/-- The principal part of a section is a section of `K → O`. -/
lemma principal_mem_image (hf : IsSection P f) :
    ∀ x ∈ StrongRetr.r c.R '' c.U, (x, c.principal f x) ∈ c.R '' (c.U ×ˢ univ) := by
  intro x hx
  rw [c.r_image] at hx
  rw [← c.apply_section hf hx]
  change c (f (c.φ.symm x)) ∈ c.K
  rw [← c.image_source]
  exact ⟨_, c.mem_source_of_proj (by rw [hf]; exact c.φ.symm_mapsTo hx), rfl⟩

/-- **The level-`1` filling** (Definition 3.6 for `f¹` in the index raise `Φ¹`): for a datum
`(g, s)` of Definition 3.11 of `f` in the chart `Φ` centred at a smooth point, `g¹` is a filling
germ of the principal part of `f¹` in `Φ¹`: conditions (1), (2) (`shift_filling_eq_on`,
`shift_filling_mem_of_fixed`), the sc¹ fill defect and condition (3) on level `1`
(`IsFillingGerm.germ_shift`). -/
theorem shift_isFillingGerm (hf : B.IsScSmoothSection f) (h0U : (0 : c.φ.model.E 0) ∈ c.U)
    (h0O : (0 : c.φ.model.E 0) ∈ StrongRetr.r c.R '' c.U) {g : c.φ.model.E 0 → c.F 0}
    {s : c.φ.model.E 0 → c.F 1}
    (hfill : IsFillingGerm c.relOpen c.isRetraction h0U (c.principal f) g)
    (hsP : IsScPlusGerm c.φ.model.C c.U s) (hs0 : c.F.toBase 1 (s 0) = g 0)
    (hconj : IsConjugateToBasicGerm c.U fun u => g u - c.F.toBase 1 (s u))
    (h01 : (0 : c.φ.model.E 1) ∈ (c.shift hc y₀).U) :
    IsFillingGerm (c.shift hc y₀).relOpen (c.shift hc y₀).isRetraction h01
      ((c.shift hc y₀).principal (B.sectionShift f))
      (levelMap (E := c.φ.model.E) (F := c.F) g 1) := by
  obtain ⟨G, -, hg, -⟩ := hfill.germ
  exact ⟨shift_filling_eq_on hf hfill.eq_on, shift_filling_mem_of_fixed (hg 0) hfill.mem_of_fixed,
    hfill.germ_shift c.relOpen c.isRetraction h0U h0O (c.principal_mem_image hf.1) hsP hs0 hconj
      h01⟩

end StrongBundleChart

open StrongBundle StrongBundleChart in
/-- **`f¹` is an sc-Fredholm germ at every smooth point of `X¹`** (Definition 3.11, germ reading,
for `f¹` on `P¹`): from a datum `(g, s)` of `f` at the point in a chart `Φ`, the datum `(g¹, s¹)`
in the index raise `Φ¹` (`shift_isFillingGerm`; `s¹` an sc⁺-germ on the shifted germ; `g¹ − s¹`
conjugated to a basic germ by the index raise of the conjugation,
`IsConjugateToBasicGerm.shift_germ`). -/
theorem isScFredholmGerm_sectionShift (hf : B.IsScSmoothSection f) {x : PX.Level 1}
    (hx : x ∈ PX.shift.smoothSet) (hg : B.IsScFredholmGerm f (PX.levelVal 1 x)) :
    B.shift.IsScFredholmGerm (B.sectionShift f) x := by
  obtain ⟨-, c, hc, hxV, h0, h0U, g, s, hfill, hsP, hs0, hconj⟩ := hg
  have h0O : (0 : c.φ.model.E 0) ∈ StrongRetr.r c.R '' c.U := by
    rw [c.r_image, ← h0]; exact c.φ.mapsTo_model _ hxV
  obtain ⟨Gs, hGsU, hs⟩ := id hsP
  obtain ⟨Gg, -, hgG, -⟩ := hfill.germ
  have hQ := c.isQuadrantLike
  have hg0 : IsSc0Germ Gg g := hgG 0
  have hs0' : IsSc0Germ (F := c.F.shift) Gs s := hs 0
  have hk : IsSc0Germ (Gg.inter Gs) (fun u => g u - c.F.toBase 1 (s u)) :=
    (hgG.sub_inter hQ (hs.operator_comp hQ c.F.shiftIncl)) 0
  set y₀ := B.shiftZero x
  have h01 : (0 : c.φ.model.E 1) ∈ (c.shift hc y₀).U := by
    change c.φ.model.E.toBase 1 0 ∈ c.U
    rw [map_zero]; exact h0U
  refine ⟨hx, c.shift hc y₀, B.isChart_shift hc y₀, hxV, shift_φ_eq_zero hc y₀ hxV h0, h01,
    levelMap (E := c.φ.model.E) (F := c.F) g 1, levelMap (E := c.φ.model.E) (F := c.F.shift) s 1,
    shift_isFillingGerm (hc := hc) (y₀ := y₀) hf h0U h0O hfill hsP hs0 hconj h01,
    ⟨Gs.shift, fun u hu => hGsU (Gs.toBase_mem hu), fun k => (hs k).shift hQ⟩, ?_, ?_⟩
  · -- `s¹(0) = g¹(0)`
    apply c.F.toBase_injective 1
    change c.F.toBase 1 (c.F.shift.toBase 1 (levelMap (E := c.φ.model.E) (F := c.F.shift) s 1 0)) =
      c.F.toBase 1 (levelMap (E := c.φ.model.E) (F := c.F) g 1 0)
    rw [hs0'.toBase_levelMap (Gs.zero_mem 1), hg0.toBase_levelMap (Gg.zero_mem 1), map_zero, hs0]
  · -- `g¹ − s¹ = (g − s)¹` near `0`
    refine (hconj.shift_germ c.relOpen h0U hk).congr_nhds ?_
    filter_upwards [Gg.eventually_mem_one c.U_subset_C, Gs.eventually_mem_one c.U_subset_C]
      with u hug hus huU
    apply levelMap_eq_of_toBase_eq
    change c.F.toBase 1 (levelMap (E := c.φ.model.E) (F := c.F) g 1 u -
      c.F.shift.toBase 1 (levelMap (E := c.φ.model.E) (F := c.F.shift) s 1 u)) = _
    rw [map_sub, hg0.toBase_levelMap (hug huU), hs0'.toBase_levelMap (hus huU)]

open StrongBundle in
/-- **Corollary 5.8 for `i = 1`: `f¹` is an sc-Fredholm section of `P¹ : Y¹ → X¹`** (Definition
3.14 with the text's germ reading of Definition 3.11; round-trip item V5.14, gap G.41; Findings,
Chapter 5, items 140–149): sc-smooth (`IsScSmoothSection.shift`), regularizing
(`regularizing_sectionShift`), and an sc-Fredholm germ at every smooth point of `X¹`
(`isScFredholmGerm_sectionShift`).  The text's "it is a priori clear"; condition (3) of the
filling on level `1` is `IsFillingGerm.germ_shift`.  Tameness is not used. -/
theorem corollary_5_8_isScFredholmSection (hf : B.IsScFredholmSection f) :
    B.shift.IsScFredholmSection (B.sectionShift f) :=
  ⟨hf.isScSmooth.shift, regularizing_sectionShift hf.isScSmooth hf.regularizing, fun x hx =>
    isScFredholmGerm_sectionShift hf.isScSmooth hx
      (hf.germ _ ((MPolyfold.mem_shift_smoothSet_iff x).1 hx))⟩

open StrongBundle in
/-- **Corollary 5.8 for `i = 1`, as stated**: if `f` is an sc-Fredholm section of `P : Y → X` with
compact solution set, then `f¹` is an sc-Fredholm section of `P¹ : Y¹ → X¹` with compact solution
set. -/
theorem corollary_5_8 (hf : B.IsScFredholmSection f) (hS : IsCompact (solutionSet P f)) :
    B.shift.IsScFredholmSection (B.sectionShift f) ∧
      IsCompact (solutionSet B.shiftProj (B.sectionShift f)) := by
  refine ⟨corollary_5_8_isScFredholmSection hf, ?_⟩
  rw [solutionSet_sectionShift hf.isScSmooth]
  exact isCompact_solutionSet_level hf hS 1

open StrongBundle in
/-- **Corollary 5.8 for `i = 2`, by iteration**: `f² = (f¹)¹` is an sc-Fredholm section of
`P² = (P¹)¹ : Y² → X²` with compact solution set (Corollary 5.8 for `i = 1` applied to `f¹`).
Every fixed `i` is obtained in the same way. -/
theorem corollary_5_8_two (hf : B.IsScFredholmSection f) (hS : IsCompact (solutionSet P f)) :
    B.shift.shift.IsScFredholmSection (B.shift.sectionShift (B.sectionShift f)) ∧
      IsCompact (solutionSet B.shift.shiftProj (B.shift.sectionShift (B.sectionShift f))) :=
  corollary_5_8 (corollary_5_8 hf hS).1 (corollary_5_8 hf hS).2

open StrongBundle StrongBundleChart in
/-- **The data of Corollary 5.8 in the shifted chart** (an unpacked form of `corollary_5_8`, kept
for reference): for an sc-Fredholm `f` with compact solution set, `f¹` is an sc-smooth,
regularizing section of `P¹` with compact solution set, and at every smooth point `x` of `X¹`, in
the index raise `Φ¹` of the chart `Φ` of a germ datum `(g, s)` of `f` at `x` (a chart of `P¹`
centred at `x`): conditions (1) and (2) of the filling for `g¹`, `g¹` an sc-smooth germ, `s¹` an
sc⁺-germ with `s¹(0) = g¹(0)`, and `g¹ − s¹` conjugated to a basic germ by the index raise of the
conjugating isomorphism.  The remaining field of the filling (the sc¹ fill defect and condition
(3) on level `1`) is `IsFillingGerm.germ_shift`; the full statement is `corollary_5_8`. -/
theorem corollary_5_8_data (hf : B.IsScFredholmSection f) (hS : IsCompact (solutionSet P f)) :
    B.shift.IsScSmoothSection (B.sectionShift f) ∧
    (∀ m, ∀ x ∈ PX.shift.levelSet m, B.sectionShift f x ∈ B.shift.doubleLevel m (m + 1) →
      x ∈ PX.shift.levelSet (m + 1)) ∧
    IsCompact (solutionSet B.shiftProj (B.sectionShift f)) ∧
    ∀ x ∈ PX.shift.smoothSet, ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c)
      (y₀ : B.ShiftSpace) (_ : B.shift.IsChart (c.shift hc y₀))
      (_ : x ∈ (c.shift hc y₀).φ.source) (_ : (c.shift hc y₀).φ x = 0)
      (_ : (0 : c.φ.model.E 1) ∈ (c.shift hc y₀).U)
      (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
      (∀ᶠ z in 𝓝 (0 : c.φ.model.E 1),
        z ∈ StrongRetr.r (c.shift hc y₀).R '' (c.shift hc y₀).U →
          (c.shift hc y₀).principal (B.sectionShift f) z =
            levelMap (E := c.φ.model.E) (F := c.F) g 1 z) ∧
      (∀ᶠ y in 𝓝 (0 : c.φ.model.E 1), y ∈ (c.shift hc y₀).U →
        levelMap (E := c.φ.model.E) (F := c.F) g 1 y =
          StrongRetr.ρ (c.shift hc y₀).R (StrongRetr.r (c.shift hc y₀).R y)
            (levelMap (E := c.φ.model.E) (F := c.F) g 1 y) →
        y ∈ StrongRetr.r (c.shift hc y₀).R '' (c.shift hc y₀).U) ∧
      (∃ G : ScNbhdGerm c.φ.model.E.shift (c.φ.model.E.lvlSet c.φ.model.C 1),
        G.U 0 ⊆ (c.shift hc y₀).U ∧
        IsScSmoothGerm (E := c.φ.model.E.shift) (F := c.F.shift) G
          (levelMap (E := c.φ.model.E) (F := c.F) g 1)) ∧
      IsScPlusGerm (E := c.φ.model.E.shift) (F := c.F.shift)
        (c.φ.model.E.lvlSet c.φ.model.C 1) (c.shift hc y₀).U
        (levelMap (E := c.φ.model.E) (F := c.F.shift) s 1) ∧
      c.F.shift.toBase 1 (levelMap (E := c.φ.model.E) (F := c.F.shift) s 1 0) =
        levelMap (E := c.φ.model.E) (F := c.F) g 1 0 ∧
      IsConjugateToBasicGerm (E := c.φ.model.E.shift) (F := c.F.shift) (c.shift hc y₀).U
        (fun u => levelMap (E := c.φ.model.E) (F := c.F) g 1 u -
          c.F.shift.toBase 1 (levelMap (E := c.φ.model.E) (F := c.F.shift) s 1 u)) := by
  have hfs := hf.isScSmooth
  refine ⟨hfs.shift, regularizing_sectionShift hfs hf.regularizing, ?_, fun x hx => ?_⟩
  · rw [solutionSet_sectionShift hfs]
    exact isCompact_solutionSet_level hf hS 1
  have hx' : PX.levelVal 1 x ∈ PX.smoothSet := (MPolyfold.mem_shift_smoothSet_iff x).1 hx
  obtain ⟨c, hc, hxV, h0, h0U, g, s, hfill, hsP, hs0, hs1, hconj1⟩ :=
    (corollary_5_8_chart hf hS).2 _ hx'
  obtain ⟨Gg, hGgU, hg, -⟩ := hfill.germ
  obtain ⟨Gs, -, hs⟩ := hsP
  have hQ := c.isQuadrantLike
  have hg0 : IsSc0Germ Gg g := hg 0
  have hs0' : IsSc0Germ (F := c.F.shift) Gs s := hs 0
  set y₀ := B.shiftZero x
  have h0U1 : (0 : c.φ.model.E 1) ∈ (c.shift hc y₀).U := by
    change c.φ.model.E.toBase 1 0 ∈ c.U
    rw [map_zero]; exact h0U
  refine ⟨c, hc, y₀, B.isChart_shift hc y₀, hxV, shift_φ_eq_zero hc y₀ hxV h0, h0U1, g, s,
    shift_filling_eq_on hfs hfill.eq_on, shift_filling_mem_of_fixed hg0 hfill.mem_of_fixed,
    ⟨Gg.shift, fun u hu => hGgU (Gg.toBase_mem hu), fun k => (hg k).shift hQ⟩, hs1, ?_, ?_⟩
  · -- `s¹(0) = g¹(0)`
    apply c.F.toBase_injective 1
    rw [hs0'.toBase_levelMap (Gs.zero_mem 1), hg0.toBase_levelMap (Gg.zero_mem 1), map_zero, hs0]
  · -- `g¹ − s¹ = (g − s)¹` near `0`
    refine hconj1.congr_nhds ?_
    filter_upwards [Gg.eventually_mem_one c.U_subset_C, Gs.eventually_mem_one c.U_subset_C]
      with u hug hus huU
    apply levelMap_eq_of_toBase_eq
    rw [map_sub, hg0.toBase_levelMap (hug huU), hs0'.toBase_levelMap (hus huU)]

end Polyfold
