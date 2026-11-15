import Polyfold.Chapter15.ParamOntoBridge
import Polyfold.Chapter15.GeneralPositionBranched
import Polyfold.Chapter15.TransversalExtension

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §13.2, p. 607 and
§15.2, Definition 15.2.1: **the multisection of one sc⁺-section** when the morphisms act
trivially.

# The multisection of a single section

For an sc⁺-section `s` of `P : W → X`, `Λ_s(w) = 1` if `w = s(P(w))` and `0` otherwise (the
local representation `k = 1`, `s₁ = s`, `σ₁ = 1` of p. 607).  It is a functor, hence an
sc⁺-multisection, when the morphisms act trivially (`t(φ) = s(φ)` and `μ(φ, w) = w`); this is
the case of the trivial ep-groupoid and of a group acting trivially.

## What is formalized (namespace `Polyfold.SBLocalization`)

Throughout, `htgt : ∀ φ, t(φ) = s(φ)` and `hμ : ∀ (φ, w), μ(φ, w) = w`.

* `sectionMulti s`; `sectionMulti_pos_iff` (`Λ_s(w) > 0 ⇔ w = s(P(w))`).
* `fibAct_of_trivial`, `isWFunctor_sectionMulti`, `isLocalRepOn_sectionMulti`,
  `isScPlusMultisection_sectionMulti` (Definition 13.2.1).
* `sectionStructure` (`I_x = {∗}`, `s_∗ = s`), `sectionTau` (`τ ≡ [{∗} ← {∗} → {∗}]`),
  **`isStructurable_sectionMulti`** (Definition 13.3.7, given paracompact orbit space).
* `pointwiseNorm_sectionMulti`: `N(Λ_s)(x) = N(s(x))`; `domSupp_sectionMulti_subset_univ`.
* **`mem_support_linearization_sectionMulti_iff`**: at `x` with `f(x) = s(x)`, the only operator
  of `T(f, Λ_s)(x)` is `(f − s)'(x)` read in a chart.
* `isReducedOntoAtPt_sectionMulti_of_zero`: if `(f − s)'(x) = (g − 0)'(x)` in a chart and `(g, Λ₀)`
  is in general position at `x` (Definition 15.3.5), so is `(f, Λ_s)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold EpGroupoid Linearization15

variable {A : SEP.{u}}

open scoped Classical in
/-- **The multisection of one section** `s`: `Λ_s(w) = 1` if `w = s(P(w))`, else `0`. -/
def sectionMulti (s : A.Obj → A.W) : A.W → ℚ≥0 :=
  fun w => if w = s (A.P w) then 1 else 0

theorem sectionMulti_pos_iff (s : A.Obj → A.W) (w : A.W) :
    0 < sectionMulti s w ↔ w = s (A.P w) := by
  classical
  unfold sectionMulti
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => one_pos⟩
  · exact ⟨fun h' => absurd h' (lt_irrefl _), fun h' => absurd h' h⟩

theorem sectionMulti_apply_self {s : A.Obj → A.W} (hs : IsSection A.P s) (x : A.Obj) :
    sectionMulti s (s x) = 1 := by
  classical
  unfold sectionMulti
  rw [if_pos (by rw [hs x])]

/-- If the morphisms act trivially on `W`, so does `fibAct`. -/
theorem fibAct_of_trivial (hμ : ∀ q : pullbackSpace A.P A.X.src, A.E.μ q = (q : A.Mor × A.W).2)
    (ψ : A.Mor) (v : A.W) : fibAct ψ v = v := by
  unfold fibAct
  split
  · exact hμ _
  · rfl

theorem isWFunctor_sectionMulti
    (hμ : ∀ q : pullbackSpace A.P A.X.src, A.E.μ q = (q : A.Mor × A.W).2) (s : A.Obj → A.W) :
    IsWFunctor A (sectionMulti s) := fun q => by rw [hμ]

/-- The section with weight one is a local representation of `Λ_s` on every open set. -/
theorem isLocalRepOn_sectionMulti {s : A.Obj → A.W} (hs : A.B.IsScPlusSection s)
    {O : Set A.Obj} (hO : IsOpen O) :
    IsLocalRepOn A (sectionMulti s) O (k := 1) (fun _ => s) (fun _ => 1) := by
  classical
  exact ⟨fun _ => one_pos, fun _ => IsScPlusSectionOn.of_isScPlusSection hs hO, by simp,
    fun w _ => by simp [sectionMulti]⟩

/-- **`Λ_s` is an sc⁺-multisection** (Definition 13.2.1) when the morphisms act trivially. -/
theorem isScPlusMultisection_sectionMulti
    (hμ : ∀ q : pullbackSpace A.P A.X.src, A.E.μ q = (q : A.Mor × A.W).2)
    {s : A.Obj → A.W} (hs : A.B.IsScPlusSection s) :
    IsScPlusMultisection A (sectionMulti s) :=
  ⟨isWFunctor_sectionMulti hμ s, fun x₀ => hasLocalSectionStructure_of_isLocalRepOn
    isOpen_univ (mem_univ x₀) (isLocalRepOn_sectionMulti hs isOpen_univ)⟩

variable (htgt : ∀ φ : A.Mor, A.X.tgt φ = A.X.src φ)
  (hμ : ∀ q : pullbackSpace A.P A.X.src, A.E.μ q = (q : A.Mor × A.W).2)
  {s : A.Obj → A.W} (hs : A.B.IsScPlusSection s)

include htgt hμ hs in
/-- The local symmetric structure `I_x = {∗}`, `s_∗ = s` of `Λ_s` on a natural neighbourhood. -/
def sectionStructure {x : A.Obj} (V : A.X.NatNbhd x) :
    SymmetricStructureOn A (sectionMulti s) V where
  I := PUnit
  mulAction := { smul := fun _ i => i, one_smul := fun _ => rfl, mul_smul := fun _ _ _ => rfl }
  s _ := s
  isScPlusSectionOn _ := IsScPlusSectionOn.of_isScPlusSection hs V.isOpen_U
  equivariant g _ y hy := by
    rw [fibAct_of_trivial hμ]
    have h : V.rep.Φ g y = y := (V.tgt_Γ g hy).symm.trans ((htgt _).trans (V.src_Γ g hy))
    rw [h]
  rep w _ := by
    classical
    rw [Fintype.card_punit, Nat.cast_one, inv_one, one_mul]
    by_cases h : w = s (A.P w)
    · have e : (Finset.univ.filter fun _ : PUnit => s (A.P w) = w) = Finset.univ :=
        Finset.filter_true_of_mem fun _ _ => h.symm
      rw [e]
      simp [sectionMulti, if_pos h]
    · have e : (Finset.univ.filter fun _ : PUnit => s (A.P w) = w) = ∅ :=
        Finset.filter_false_of_mem fun _ _ e => h e.symm
      rw [e]
      simp [sectionMulti, if_neg h]

/-- `τ ≡ [{∗} ← {∗} → {∗}]` for `Λ_s` on a good system. -/
def sectionTau (𝒰 : A.X.GoodSystem) :
    (⟨𝒰, fun x => sectionStructure htgt hμ hs (𝒰.nbhd x)⟩ :
      Decoration A (sectionMulti s)).Tau where
  τ _ _ _ := IndexCorr.ofEquiv (_root_.Equiv.refl PUnit.{u + 1})
  isCorrespondence x x' :=
    { locallyConstant := fun _ _ => Eventually.of_forall fun _ => rfl
      finite := (finite_singleton (IndexCorr.ofEquiv (_root_.Equiv.refl PUnit.{u + 1}))).subset
        (by rintro _ ⟨_, _, rfl⟩; rfl)
      biact := fun _ _ g' g => (IndexCorr.example_13_3_3 g' _ g).symm
      compat := fun _ _ => IndexCorr.sat_of_forall (fun _ _ ψ _ => by
        change s (A.X.tgt ψ) = fibAct ψ (s (A.X.src ψ))
        rw [fibAct_of_trivial hμ, htgt]) _ }
  diag _ _ _ _ := IndexCorr.ofEquiv_eq_of_subsingleton (α := PUnit.{u + 1}) _ _
  swap _ _ _ _ := (IndexCorr.swap_ofEquiv_of_subsingleton (α := PUnit.{u + 1}) _).symm

include htgt hμ hs in
/-- **`Λ_s` is structurable** (Definition 13.3.7) when the morphisms act trivially and the orbit
space is paracompact (a good system exists by Theorem 13.1.8). -/
theorem isStructurable_sectionMulti (hX : A.X.HasParacompactOrbitSpace) :
    IsStructurable A (sectionMulti s) := by
  obtain ⟨𝒰, -⟩ := A.X.theorem_13_1_8 hX (fun _ => univ) (fun _ => isOpen_univ)
    (fun _ => mem_univ _)
  exact ⟨isScPlusMultisection_sectionMulti hμ hs, _, ⟨sectionTau htgt hμ hs 𝒰⟩⟩

/-- `N(Λ_s)(x) = N(s(x))`. -/
theorem pointwiseNorm_sectionMulti (N : A.B.One → ℝ) {s : A.Obj → A.W} (hs : IsSection A.P s)
    (x : A.Obj) : pointwiseNorm N (sectionMulti s) x = normW N (s x) := by
  classical
  have hsupp : suppAt (sectionMulti s) x = {s x} := by
    ext w
    simp only [suppAt, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hw, hpos⟩
      have h := (sectionMulti_pos_iff s w).1 hpos
      rw [hw] at h
      exact h
    · rintro rfl
      exact ⟨hs x, by rw [sectionMulti_apply_self hs]; exact one_pos⟩
  rw [pointwiseNorm, hsupp, image_singleton, csSup_singleton]

include hs in
/-- **The operator of `T(f, Λ_s)(x)`**: at `x` with `f(x) = s(x)`, read in a chart `c` around `x`,
the only operator in the support is `(f − s)'(x)`. -/
theorem mem_support_linearization_sectionMulti_iff {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) {c : StrongBundleChart A.X.PObj A.P}
    (hc : A.B.IsChart c) {x : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hxs : f (A.X.PObj.levelVal 1 x) = s (A.X.PObj.levelVal 1 x))
    (L : A.X.PObj.tangentFiber x →ₗ[ℝ] A.P ⁻¹' {A.X.PObj.levelVal 1 x}) :
    L ∈ (linearization f (sectionMulti s) x).support ↔
      toIntr c hx (subDeriv c f s (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) = L := by
  let d : LocalLinData A (sectionMulti s) x :=
    ⟨univ, isOpen_univ, 1, fun _ => s, fun _ => 1, isLocalRepOn_sectionMulti hs isOpen_univ, c,
      hc, subset_univ _, hx⟩
  have key := mem_support_linSumIntr_iff (k := 1) (s := fun _ => s)
    (σ := fun _ => (1 : ℚ≥0)) hf.1.1.1 (fun _ => one_pos)
    (fun _ z _ => hs.1 z) (subset_univ _) hx L
  rw [linearization_eq hf d]
  exact key.trans ⟨fun ⟨_, _, hL⟩ => hL, fun hL => ⟨0, hxs.symm, hL⟩⟩

include hs in
/-- **General position transfers from `(g, Λ₀)` to `(f, Λ_s)`** (Definition 15.3.5 at one point)
when the operators `(f − s)'(x)` and `(g − 0)'(x)` agree in a chart around `x`. -/
theorem isReducedOntoAtPt_sectionMulti_of_zero {f g : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hg : A.E.IsScFredholmSectionFunctor g)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) {x : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hxs : f (A.X.PObj.levelVal 1 x) = s (A.X.PObj.levelVal 1 x))
    (hg0 : g (A.X.PObj.levelVal 1 x) = fiberZero A.P (A.X.PObj.levelVal 1 x))
    (hd : subDeriv c f s (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)) =
      subDeriv c g (fiberZero A.P) (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)))
    (H : IsReducedOntoAtPt g (zeroMultisection A) x) :
    IsReducedOntoAtPt f (sectionMulti s) x := by
  intro L hL
  apply H L
  rw [mem_support_linearization_zero_iff hg hc hx hg0, ← hd]
  exact (mem_support_linearization_sectionMulti_iff hs hf hc hx hxs L).1 hL

end SBLocalization

end Polyfold
