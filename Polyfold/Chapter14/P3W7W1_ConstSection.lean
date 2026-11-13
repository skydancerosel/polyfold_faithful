import Polyfold.Chapter14.P3W7W1_HalfSpaceSEP
import Polyfold.Chapter15.P3L_LocalScPlus

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 14,
**Theorem 14.1.9** (∂-Extension Theorem, p. 646; 2017: Theorem 14.2): **a witness with
non-empty `dom-supp(Λ)`** on the half-space bundle `H × ℝᵏ → H`, `H = [0, ∞) × ℝᵐ`.

# A constant section over the boundary of the half-space

## What is formalized

* `SBLocalization.isFaceScPlusSectionOn_of_isScPlusSectionOn_w1` (general): an sc⁺-section on all
  of `X` satisfies (1) of Definition 14.1.3 on every `U` (in every tame strong bundle chart and
  tame presentation, the local face germ is a sub-retract, `corner_retraction`, and the chart
  representative restricts to it, `IsScSmoothRetractMap.mono_source`).
* `HalfSpaceBundle.constSec v`: the section `x ↦ (x, v)` for `v ∈ ℝᵏ`; it is an sc⁺-section
  (`isScPlusSectionOn_constSec`).
* `constMulti v`: the multisection `Λ_v(w) = 1` if `w = (P(w), v)`, else `0`.
  `isBoundaryStructurable_constMulti`: it is structurable over `∂X` (Definition 14.1.7, with
  `I_x = {∗}`, `s_∗ = constSec v`, `τ ≡ [{∗} ← {∗} → {∗}]`); `chargesBoundary_constMulti`;
  `boundaryDomSupp_constMulti_nonempty` (for `v ≠ 0`, `dom-supp(Λ_v) ∋ 0`);
  `pointwiseNorm_constMulti` (`N(Λ_v)(x) = N(x, v)`) and its continuity in `x`.
* **`theorem_14_1_9_constSec`**: for `v ≠ 0`, Theorem 14.1.9 (`theorem_14_1_9_charged_a6`) applies
  to `Λ_v` with `Ũ = X` and `f(x) = N(x, v) + 1`, all hypotheses discharged: there is a
  structurable `Λ'` on `H × ℝᵏ` with `N(Λ') ≤ f` and `Λ' = Λ_v` over `∂H`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-- **An sc⁺-section on `X` is sc⁺ on every local face** ((1) of Definition 14.1.3 on every `U`):
in a tame strong bundle chart, the local face germ `O ∩ V ∩ {tᵢ = 0}` at `φ(x)` is a sub-retract
(`corner_retraction`), and the chart representative of `s`, sc-smooth on `O`, restricts to it. -/
theorem isFaceScPlusSectionOn_of_isScPlusSectionOn_w1 {s : A.Obj → A.W}
    (hs : IsScPlusSectionOn A s univ) (U : Set A.Obj) : IsFaceScPlusSectionOn A s U := by
  refine ⟨fun x _ => ⟨hs.1 x (mem_univ x), hs.mem_oneSet (mem_univ x)⟩, ?_⟩
  intro c hc n W T hT x hx i hi
  have hmap := hs.isScSmoothRetractMap_localRepOne_of_isChart isOpen_univ hc.1 (subset_univ _)
  have hO := c.base_retract
  have ho : c.φ x ∈ (c.isRetraction.baseRetraction c.relOpen).retract := by
    rw [hO]; exact c.φ.mapsTo_model x hx.2
  have hσ : ∀ j ∈ ({i} : Finset (Fin n)), (T 0 (c.φ x)).1 j = 0 := fun j hj => by
    rw [Finset.mem_singleton.1 hj]; exact (mem_zeroSet T).1 hi
  obtain ⟨-, -, -, V, hV, hxV, S, -, -, hSret, -⟩ := corner_retraction {i} hT (hc.2 n W T hT) ho hσ
  have hQ : S.retract = c.φ.model.O ∩ V ∩ coordHyper T i := by
    rw [hSret, hO]; ext z; simp [coordHyper]
  exact ⟨V, hV, hxV, ⟨S, hQ⟩, fun z hz => localRepOne_fst (fun y => hs.1 y (mem_univ y)) hz.1.1,
    hmap.mono_source c.φ.model.isScRetract fun z hz => hz.1.1⟩

end SBLocalization

namespace HalfSpaceBundle

open SBLocalization StrongBundle EpGroupoid

variable {m k : ℕ}

/-- **The constant section** `x ↦ (x, v)` of `H × ℝᵏ → H`. -/
abbrev constSec (v : Fin k → ℝ) : (halfSEP m k).Obj → (halfSEP m k).W :=
  graphSection fun _ => v

/-- **The constant section is an sc⁺-section** (in the one chart of the atlas its representative
is `u ↦ (u, v)` on `H`, a `C^∞` map between finite-dimensional spaces). -/
theorem isScPlusSectionOn_constSec (v : Fin k → ℝ) :
    IsScPlusSectionOn (halfSEP m k) (constSec v) univ := by
  have hι : ∀ w : Fin k → ℝ, Function.invFun ((rnSc k).toBase 1) w = w := fun w =>
    leftInverse_invFun ((rnSc k).toBase_injective 1) w
  refine isScPlusSectionOn_of_localRepOne isOpen_univ (fun _ _ => rfl) fun x _ =>
    ⟨chart₀, mem_singleton _, mem_univ _, fun _ _ => (bijective_toBase_const _ 1).2 _, ?_⟩
  set c : StrongBundleChart (halfSEP m k).X.PObj (halfSEP m k).P := chart₀ with hcdef
  have himg : c.φ '' (univ ∩ c.φ.source) = H m := by
    rw [univ_inter]
    change (baseChart m).toPartialEquiv '' univ = H m
    rw [image_univ]; exact Subtype.range_coe
  rw [himg]
  have hval : ∀ u ∈ H m, localRepOne c (constSec v) u = (u, v) :=
    fun u hu => by
      change ((((baseChart m).symm u : H m) : (halfSpaceSc m) 0), Function.invFun
        ((rnSc k).toBase 1) v) = (u, v)
      rw [baseChart_symm_val hu, hι]
  refine (isScSmoothRetractMap_iff_exists (relOpen_H m).isScRetract).2
    ⟨fun u hu => ?_, ScRetraction.id (relOpen_H m), image_id _, ?_⟩
  · rw [hval u hu]
    exact ⟨(u, (rnSc k).toBase 1 v), ⟨hu, mem_univ _⟩, rfl⟩
  · refine (isScSmooth_of_bijective_toBase bijective_toBase_E
      (bijective_toBase_prod bijective_toBase_E (bijective_toBase_shift (bijective_toBase_const _)))
      (relOpen_H m).isScDomain (f := fun u : (halfSpaceSc m) 0 => (u, v))
      (contDiff_id.prodMk contDiff_const).contDiffOn).congr (relOpen_H m).isScDomain
        fun u hu => ?_
    exact (hval u hu).symm

/-- Over the trivial ep-groupoid the fibre action is trivial. -/
theorem fibAct_halfSEP (φ : (halfSEP m k).Mor) (w : (halfSEP m k).W) : fibAct φ w = w := by
  unfold fibAct; split <;> rfl

open scoped Classical in
/-- **The multisection of the constant section**: `Λ_v(w) = 1` if `w = (P(w), v)`, else `0`. -/
def constMulti (v : Fin k → ℝ) : (halfSEP m k).W → ℚ≥0 :=
  fun w => if w = constSec v ((halfSEP m k).P w) then 1 else 0

/-- The structure `I_x = {∗}`, `s_∗ = constSec v` of `Λ_v` on any `V`. -/
def constStructure (v : Fin k → ℝ) {x : (halfSEP m k).Obj} (V : (halfSEP m k).X.NatNbhd x) :
    BoundarySymmetricStructure (halfSEP m k) (constMulti v) V where
  I := PUnit.{1}
  s _ := constSec v
  isFaceScPlus _ := isFaceScPlusSectionOn_of_isScPlusSectionOn_w1 (isScPlusSectionOn_constSec v) _
  equivariant g _ y hy := by
    rw [fibAct_halfSEP]
    have h : V.rep.Φ g y = y := (V.tgt_Γ g hy.1).symm.trans (V.src_Γ g hy.1)
    rw [h]
  rep w _ := by
    classical
    by_cases h : w = constSec v ((halfSEP m k).P w)
    · have e : (Finset.univ.filter fun _ : PUnit.{1} => constSec v ((halfSEP m k).P w) = w) =
          Finset.univ := Finset.filter_true_of_mem fun _ _ => h.symm
      rw [e]
      simp [constMulti, if_pos h]
    · have e : (Finset.univ.filter fun _ : PUnit.{1} => constSec v ((halfSEP m k).P w) = w) =
          ∅ := Finset.filter_false_of_mem fun _ _ e => h e.symm
      rw [e]
      simp [constMulti, if_neg h]

/-- `τ ≡ [{∗} ← {∗} → {∗}]` for `Λ_v` on a good system for `∂X`. -/
def constTau (v : Fin k → ℝ) (𝒰 : (halfSEP m k).X.BoundaryGoodSystem) :
    (⟨𝒰, fun x => constStructure v (𝒰.nbhd x)⟩ :
      BoundaryDecoration (halfSEP m k) (constMulti v)).Tau where
  τ _ _ _ := IndexCorr.ofEquiv (_root_.Equiv.refl PUnit.{1})
  locallyConstant _ _ _ _ := Eventually.of_forall fun _ => rfl
  finite _ _ := (finite_singleton (IndexCorr.ofEquiv (_root_.Equiv.refl PUnit.{1}))).subset
    (by rintro _ ⟨_, _, rfl⟩; rfl)
  swap _ _ _ _ := (IndexCorr.swap_ofEquiv_of_subsingleton (α := PUnit.{1}) _).symm
  diag _ _ _ _ := IndexCorr.ofEquiv_eq_of_subsingleton (α := PUnit.{1}) _ _
  biact _ _ _ _ g' g := (IndexCorr.example_13_3_3 g' _ g).symm
  compat _ _ φ _ := IndexCorr.sat_of_forall (fun _ _ => (fibAct_halfSEP φ _).symm) _

/-- **`Λ_v` is structurable over `∂X`** (Definition 14.1.7). -/
theorem isBoundaryStructurable_constMulti (v : Fin k → ℝ) :
    IsBoundaryStructurable (halfSEP m k) (constMulti v) := by
  have hX := isTame_halfSEP m k
  obtain ⟨𝒰, -⟩ := (halfSEP m k).X.theorem_14_1_6_hyp hX (hasParacompactOrbitSpace_halfSEP m k)
    (fun _ => univ) (fun _ => isOpen_univ) (fun _ => mem_univ _)
  refine ⟨⟨fun _ _ => rfl, fun x hx => ?_⟩, _, ⟨constTau v 𝒰⟩⟩
  obtain ⟨V, -, hV⟩ := (halfSEP m k).X.exists_isGoodBoundaryNbhd hX hx isOpen_univ (mem_univ x)
  exact ⟨V, hV, ⟨constStructure v V⟩⟩

theorem constMulti_constSec (v : Fin k → ℝ) (x : (halfSEP m k).Obj) :
    constMulti v (constSec v x) = 1 := by
  unfold constMulti
  exact if_pos rfl

/-- `Λ_v` charges every fibre. -/
theorem chargesBoundary_constMulti (v : Fin k → ℝ) : ChargesBoundary (constMulti (m := m) v) :=
  fun x _ => ⟨constSec v x, rfl, by rw [constMulti_constSec]; exact one_ne_zero⟩

/-- `(x, v) ≠ 0_x` for `v ≠ 0`. -/
theorem constSec_ne_fiberZero {v : Fin k → ℝ} (hv : v ≠ 0) (x : (halfSEP m k).Obj) :
    constSec v x ≠ fiberZero (halfSEP m k).P x := fun h =>
  hv (congrArg Prod.snd h)

/-- **`dom-supp(Λ_v)` over `∂X` is non-empty** for `v ≠ 0`: it contains the corner `0`. -/
theorem boundaryDomSupp_constMulti_nonempty {v : Fin k → ℝ} (hv : v ≠ 0) :
    (boundaryDomSupp (constMulti (m := m) v)).Nonempty :=
  ⟨_, subset_closure ⟨zero_mem_boundary_halfSEP m k, constSec v _, rfl,
    constSec_ne_fiberZero hv _, lt_of_lt_of_eq one_pos (constMulti_constSec v _).symm⟩⟩

/-- `N(Λ_v)(x) = N(x, v)`. -/
theorem pointwiseNorm_constMulti (N : (halfSEP m k).B.One → ℝ) (v : Fin k → ℝ)
    (x : (halfSEP m k).Obj) : pointwiseNorm N (constMulti v) x = normW N (constSec v x) := by
  classical
  have hs : suppAt (constMulti v) x = {constSec v x} := by
    ext w
    simp only [suppAt, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hw, hpos⟩
      by_contra hne
      have : w ≠ constSec v ((halfSEP m k).P w) := by rw [hw]; exact hne
      simp [constMulti, if_neg this] at hpos
    · rintro rfl
      exact ⟨rfl, by rw [constMulti_constSec]; exact one_pos⟩
  rw [pointwiseNorm, hs, image_singleton, csSup_singleton]

/-- `x ↦ N(x, v)` is continuous (the constant section is sc⁺, so continuous into `W[1]`). -/
theorem continuous_normW_constSec {N : (halfSEP m k).B.One → ℝ}
    (hN : (halfSEP m k).B.IsAuxNorm N) (v : Fin k → ℝ) :
    Continuous fun x => normW N (constSec (m := m) v x) := by
  obtain ⟨-, G, hG, hGs⟩ := isScPlusSectionOn_constSec (m := m) v
  have e : (fun x => normW N (constSec (m := m) v x)) = N ∘ G := funext fun x => by
    have hmem := (isScPlusSectionOn_constSec (m := m) v).mem_oneSet (mem_univ x)
    rw [normW_of_mem N hmem, Function.comp_apply]
    congr 1
    exact (halfSEP m k).B.oneVal_injective (by rw [oneVal_oneMk, hG x (mem_univ x)])
  rw [e]
  exact hN.continuous.comp (continuousOn_univ.1 hGs.continuousOn)

/-- **Theorem 14.1.9 with non-empty `dom-supp(Λ)` and `∂X ≠ ∅`**: on the half-space bundle
`H × ℝᵏ → H`, for `v ≠ 0` and any auxiliary norm `N` (one exists, Theorem 12.2.2), the
multisection `Λ_v` of the constant section over `∂H` has a structurable extension `Λ'` with
`N(Λ')(x) ≤ N(x, v) + 1` (`theorem_14_1_9_charged_a6` with `Ũ = X`, `f(x) = N(x, v) + 1`, all
hypotheses discharged). -/
theorem theorem_14_1_9_constSec {v : Fin k → ℝ} (hv : v ≠ 0) :
    (boundaryDomSupp (constMulti (m := m) v)).Nonempty ∧
      ∃ N : (halfSEP m k).B.One → ℝ, (halfSEP m k).E.IsAuxNorm N ∧
      ∃ Λ' : (halfSEP m k).W → ℚ≥0, IsStructurable (halfSEP m k) Λ' ∧
        (∀ x, pointwiseNorm N Λ' x ≤ normW N (constSec v x) + 1) ∧
        ∀ w, (halfSEP m k).P w ∈ (halfSEP m k).X.PObj.boundary → Λ' w = constMulti v w := by
  have hX := isTame_halfSEP m k
  have hpara := hasParacompactOrbitSpace_halfSEP m k
  obtain ⟨N, hN⟩ := EpStrongBundle.theorem_12_2_2 (halfSEP m k).E hpara
  have hN1 : (halfSEP m k).B.IsAuxNorm N := hN.isAuxNorm
  obtain ⟨Λ', h1, h2, -, h4⟩ := theorem_14_1_9_charged_a6 hX hpara
    (admitsScPartitionsOfUnity_halfSEP m k) (hB_halfSEP m k) (constMulti v)
    (isBoundaryStructurable_constMulti v) (chargesBoundary_constMulti v) N hN univ isOpen_univ
    (GroupoidStr.isSaturated_univ _) (subset_univ _) (fun x => normW N (constSec v x) + 1)
    ((continuous_normW_constSec hN1 v).add continuous_const)
    (fun x => by have := normW_nonneg hN1 (constSec v x); linarith) (fun _ => rfl)
    (subset_univ _) fun x _ => by rw [pointwiseNorm_constMulti]; linarith
  exact ⟨boundaryDomSupp_constMulti_nonempty hv, N, hN, Λ', h1, h2, h4⟩

end HalfSpaceBundle

end Polyfold
