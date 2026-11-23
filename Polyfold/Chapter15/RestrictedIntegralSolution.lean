import Polyfold.Chapter15.RestrictedIntegral
import Polyfold.Chapter15.RestrictedBundle
import Polyfold.Chapter15.AdmissibleCylinderEnds

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4
(Theorem 15.4.3, p. 702) with Definition 9.5.6 (p. 439) and Theorems 11.4.1, 11.4.2
(pp. 543–544).  Numbers and pages are the 2021 text's.

# Oriented solution sets on the restriction of a strong bundle to a saturated open set

For a strong bundle `W → X` over an ep-groupoid, a saturated open set `V ⊆ X` and an oriented
solution set `S = (Λ, T̂)` of a section `f` with `supp(Λ ∘ f) ⊆ V`:

* `OrientedSolution.restr`: the oriented solution set `(Λ|V, i^*T̂)` of `f|V` on `W|V → X|V`
  (`i : X|V → X` the inclusion, `i^*T̂` the pull-back (11.9));
* **`OrientedSolution.integral_restr`**, **`OrientedSolution.integralEff_restr`**:
  `∫_{(Λ|V ∘ f|V, i^*T̂)} i^*ω = ∫_{(Λ ∘ f, T̂)} ω` and the same for the effective integrals.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold SEP EpGroupoid

variable {A : SEP.{u}} {V : Set A.Obj} (hV : A.X.IsEpSubgroupoid V)

/-- `Λ|V ∘ f|V = (Λ ∘ f) ∘ i`. -/
theorem restrMult_restrSec_eq_pullbackTheta {f : A.Obj → A.W} (hf : IsSection A.P f)
    (Λ : A.W → ℚ≥0) :
    (fun z => ((restrMult hV Λ (restrSec hV f hf z) : ℚ≥0) : ℚ)) =
      (A.baseEP.subFunctor hV).pullbackTheta (fun z => (Λ (f z) : ℚ)) := by
  funext z
  rfl

/-- The branched integral depends on `Θ` only. -/
theorem tameBranchedIntegral_congr_theta {B : EP.{u}} {n : ℕ} {Θa Θb : B.Obj → ℚ}
    {T : B.Obj → B.X.PObj.OrTangent →₀ ℚ} (h : Θa = Θb) (hn : 0 < n)
    (hΘa : B.X.IsBranchedEpSubgroupoid Θa) (hca : B.X.IsCompactBranched Θa)
    (hTa : B.X.IsOrientation Θa T)
    (hla : ∀ x ∈ EpGroupoid.supp Θa, ∃ C : B.X.OrientedTameStructure n Θa x, C.Represents T)
    (hΘb : B.X.IsBranchedEpSubgroupoid Θb) (hcb : B.X.IsCompactBranched Θb)
    (hTb : B.X.IsOrientation Θb T)
    (hlb : ∀ x ∈ EpGroupoid.supp Θb, ∃ C : B.X.OrientedTameStructure n Θb x, C.Represents T)
    (ω : B.epFormsInfty n) :
    (B.epFormsInftyEval n).tameBranchedIntegral hn hΘa hca hTa hla ω =
      (B.epFormsInftyEval n).tameBranchedIntegral hn hΘb hcb hTb hlb ω := by
  subst h
  rfl

/-- The effective branched integral depends on `Θ` only. -/
theorem tameBranchedIntegralEff_congr_theta {B : EP.{u}} {n : ℕ} {Θa Θb : B.Obj → ℚ}
    {T : B.Obj → B.X.PObj.OrTangent →₀ ℚ} (h : Θa = Θb) (hn : 0 < n)
    (hΘa : B.X.IsBranchedEpSubgroupoid Θa) (hca : B.X.IsCompactBranched Θa)
    (hTa : B.X.IsOrientation Θa T)
    (hla : ∀ x ∈ EpGroupoid.supp Θa, ∃ C : B.X.OrientedTameStructure n Θa x,
      C.Represents T ∧ C.rep.HasLUC)
    (hΘb : B.X.IsBranchedEpSubgroupoid Θb) (hcb : B.X.IsCompactBranched Θb)
    (hTb : B.X.IsOrientation Θb T)
    (hlb : ∀ x ∈ EpGroupoid.supp Θb, ∃ C : B.X.OrientedTameStructure n Θb x,
      C.Represents T ∧ C.rep.HasLUC)
    (ω : B.epFormsInfty n) :
    (B.epFormsInftyEval n).tameBranchedIntegralEff hn hΘa hca hTa hla ω =
      (B.epFormsInftyEval n).tameBranchedIntegralEff hn hΘb hcb hTb hlb ω := by
  subst h
  rfl

/-- **The oriented solution set `(Λ|V, i^*T̂)` of `f|V`** on the restriction `W|V → X|V` to a
saturated open set `V` containing `supp(Λ ∘ f)`. -/
def OrientedSolution.restr (hVo : IsOpen V) {f : A.Obj → A.W} (hf : IsSection A.P f) {m : ℕ}
    (S : OrientedSolution A f m) (hsupp : EpGroupoid.supp (fun z => (S.Λ (f z) : ℚ)) ⊆ V) :
    OrientedSolution (A.restr hV) (restrSec hV f hf) m where
  Λ := restrMult hV S.Λ
  isScPlusMultisection := isScPlusMultisection_restrMult hV hVo S.isScPlusMultisection
  T := (A.baseEP.subFunctor hV).pullSection S.T
  isBranched := by
    rw [restrMult_restrSec_eq_pullbackTheta hV hf]
    exact A.baseEP.isBranchedEpSubgroupoid_sub hV hVo S.isBranched S.isCompact hsupp
  isCompact := by
    rw [restrMult_restrSec_eq_pullbackTheta hV hf]
    exact A.baseEP.isCompactBranched_sub hV hVo S.isBranched.isFunctorial S.isCompact hsupp
  isOrientation := by
    rw [restrMult_restrSec_eq_pullbackTheta hV hf]
    exact A.baseEP.isOrientation_sub hV hVo S.isOrientation
  loc := by
    rw [restrMult_restrSec_eq_pullbackTheta hV hf]
    exact A.baseEP.hloc_sub hV hVo S.isBranched.isFunctorial S.isOrientation.isGrHatSection
      S.loc

@[simp] theorem OrientedSolution.restr_Λ (hVo : IsOpen V) {f : A.Obj → A.W}
    (hf : IsSection A.P f) {m : ℕ} (S : OrientedSolution A f m)
    (hsupp : EpGroupoid.supp (fun z => (S.Λ (f z) : ℚ)) ⊆ V) :
    (S.restr hV hVo hf hsupp).Λ = restrMult hV S.Λ := rfl

@[simp] theorem OrientedSolution.restr_T (hVo : IsOpen V) {f : A.Obj → A.W}
    (hf : IsSection A.P f) {m : ℕ} (S : OrientedSolution A f m)
    (hsupp : EpGroupoid.supp (fun z => (S.Λ (f z) : ℚ)) ⊆ V) :
    (S.restr hV hVo hf hsupp).T = (A.baseEP.subFunctor hV).pullSection S.T := rfl

/-- **`∫_{(Λ|V ∘ f|V, i^*T̂)} i^*ω = ∫_{(Λ ∘ f, T̂)} ω`** for `supp(Λ ∘ f) ⊆ V`
(Definition 9.5.6 (1), Theorem 11.4.1). -/
theorem OrientedSolution.integral_restr (hVo : IsOpen V) {f : A.Obj → A.W}
    (hf : IsSection A.P f) {m : ℕ} (S : OrientedSolution A f m)
    (hsupp : EpGroupoid.supp (fun z => (S.Λ (f z) : ℚ)) ⊆ V)
    (ω : A.baseEP.epFormsInfty (m + 1)) :
    (S.restr hV hVo hf hsupp).integral
        (EP.epFormsInftyPullback (A.baseEP.subFunctor hV) (m + 1) ω) = S.integral ω := by
  have hΘ₁ := A.baseEP.isBranchedEpSubgroupoid_sub hV hVo S.isBranched S.isCompact hsupp
  have hc₁ := A.baseEP.isCompactBranched_sub hV hVo S.isBranched.isFunctorial S.isCompact hsupp
  have hT₁ := A.baseEP.isOrientation_sub hV hVo S.isOrientation
  have hl₁ := A.baseEP.hloc_sub hV hVo S.isBranched.isFunctorial
    S.isOrientation.isGrHatSection S.loc
  have e := A.baseEP.tameBranchedIntegral_sub hV hVo (Nat.succ_pos m) S.isBranched S.isCompact
    S.isOrientation S.loc hsupp hΘ₁ hc₁ hT₁ hl₁ ω
  refine Eq.trans ?_ e.symm
  exact tameBranchedIntegral_congr_theta (B := A.baseEP.sub hV)
    (restrMult_restrSec_eq_pullbackTheta hV hf S.Λ) (Nat.succ_pos m)
    (S.restr hV hVo hf hsupp).isBranched (S.restr hV hVo hf hsupp).isCompact
    (S.restr hV hVo hf hsupp).isOrientation (S.restr hV hVo hf hsupp).loc hΘ₁ hc₁ hT₁ hl₁ _

/-- **`∮_{(Λ|V ∘ f|V, i^*T̂)} i^*ω = ∮_{(Λ ∘ f, T̂)} ω`** for `supp(Λ ∘ f) ⊆ V`
(Definition 9.5.6 (2), Theorem 11.4.2), for `X` with the local unique continuation property
(then `X|V` has it, `isLUC_restr`). -/
theorem OrientedSolution.integralEff_restr (hVo : IsOpen V) {f : A.Obj → A.W}
    (hf : IsSection A.P f) {m : ℕ} (hLUC : A.X.IsLUC) (S : OrientedSolution A f m)
    (hsupp : EpGroupoid.supp (fun z => (S.Λ (f z) : ℚ)) ⊆ V)
    (ω : A.baseEP.epFormsInfty (m + 1)) (hLUC₁ : (A.restr hV).X.IsLUC) :
    (S.restr hV hVo hf hsupp).integralEff hLUC₁
        (EP.epFormsInftyPullback (A.baseEP.subFunctor hV) (m + 1) ω) =
      S.integralEff hLUC ω := by
  have hΘ₁ := A.baseEP.isBranchedEpSubgroupoid_sub hV hVo S.isBranched S.isCompact hsupp
  have hc₁ := A.baseEP.isCompactBranched_sub hV hVo S.isBranched.isFunctorial S.isCompact hsupp
  have hT₁ := A.baseEP.isOrientation_sub hV hVo S.isOrientation
  have hl₁ := (A.baseEP.sub hV).hloc_hasLUC (A.baseEP.isLUC_sub hV hVo hLUC)
    (A.baseEP.hloc_sub hV hVo S.isBranched.isFunctorial S.isOrientation.isGrHatSection S.loc)
  have e := A.baseEP.tameBranchedIntegralEff_sub hV hVo (Nat.succ_pos m) hLUC S.isBranched
    S.isCompact S.isOrientation (A.baseEP.hloc_hasLUC hLUC S.loc) hsupp hΘ₁ hc₁ hT₁ hl₁ ω
  refine Eq.trans ?_ e.symm
  exact tameBranchedIntegralEff_congr_theta (B := A.baseEP.sub hV)
    (restrMult_restrSec_eq_pullbackTheta hV hf S.Λ) (Nat.succ_pos m)
    (S.restr hV hVo hf hsupp).isBranched (S.restr hV hVo hf hsupp).isCompact
    (S.restr hV hVo hf hsupp).isOrientation
    ((A.restr hV).baseEP.hloc_hasLUC hLUC₁ (S.restr hV hVo hf hsupp).loc) hΘ₁ hc₁ hT₁ hl₁ _

/-- The local unique continuation property of `X` restricts to the base of `W|V`. -/
theorem isLUC_restr (hVo : IsOpen V) (hLUC : A.X.IsLUC) : (A.restr hV).X.IsLUC :=
  A.baseEP.isLUC_sub hV hVo hLUC

end SBLocalization

end Polyfold
