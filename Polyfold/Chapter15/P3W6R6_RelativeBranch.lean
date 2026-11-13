import Polyfold.Chapter15.P3W5GB_ParametricGP
import Polyfold.Chapter15.P3W6R6_RelativeFamilies

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.9** (2017: Theorem 15.5), steps (c)–(d), p. 699: one branch of `Λ₀ ⊕ Λ_t` read as
Part I's parametrized section, as GB did for Theorem 15.3.7 with `Λ₀` trivial.

# One branch of `Λ₀ ⊕ Λ_t`

## The text, paraphrased

Near a point `x` of `supp(Λ₀ ∘ f)` the branches of `Λ̃ = Λ₀ ⊕ Λ_t` are `s⁰_a + Σ_j t_j s_{ij}`;
for a branch `s⁰_a` of `Λ₀` through `f(x)` the map `(t, y) ↦ f(y) − s⁰_a(y) − Σ_j t_j s_{ij}(y)`
has, by (15.1) relative to `Λ₀`, a surjective linearization on `ℝ^ℓ × T^R_xX` at `(0, x)`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `isLocalRepOn_multisectionAdd`: the local representation of `Λ₀ ⊕ Λ` on a common domain
  (branches `s⁰_a + s_i`, weights `σ⁰_a σ_i`), indexed by `Fin`.
* **`paramSlice_branch_eq_rel`**: the slice at `t` of `F(t, y) = (f − s⁰)|O + Σ_j t_j (−s_j)|O`
  is `(f − (s⁰ + Σ_j t_j s_j))|O`.
* **`isParamGP_restrictTo_of_onto_rel`**: (15.1) for the operator `(f − s⁰)'(x)` gives Part I's
  properties (i)–(ii) for `F` (GB's `isParamGP_restrictTo_of_onto` with `s⁰` for `0`).
* **`isGeneralPositionGerm_branchParam_rel`**: (15.1) relative to `Λ₀` makes `F` in general
  position at `(0, x)` (Definition 5.3.9 on `ℝ^ℓ × O`) for every branch `s⁰_a` of `Λ₀` through
  `f(x)`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-! ### The local representation of a sum -/

/-- **The sum of two local representations on the same domain** (Definition 13.2.9 (3)): the
sections `s⁰_a + s_i` with the weights `σ⁰_a σ_i`, reindexed by `Fin`. -/
theorem isLocalRepOn_multisectionAdd {Λ₀ Λ : A.W → ℚ≥0} {O : Set A.Obj} (hO : IsOpen O)
    {k₀ k : ℕ} {s₀ : Fin k₀ → A.Obj → A.W} {σ₀ : Fin k₀ → ℚ≥0} {s : Fin k → A.Obj → A.W}
    {σ : Fin k → ℚ≥0} (hs₀ : ∀ a, IsSection A.P (s₀ a)) (hs : ∀ i, IsSection A.P (s i))
    (h₀ : IsLocalRepOn A Λ₀ O s₀ σ₀) (h : IsLocalRepOn A Λ O s σ) :
    IsLocalRepOn A (multisectionAdd Λ₀ Λ) O
      (fun n => Polyfold.sectionAdd A.P (s₀ ((Fintype.equivFin (Fin k₀ × Fin k)).symm n).1)
        (s ((Fintype.equivFin (Fin k₀ × Fin k)).symm n).2))
      (fun n => σ₀ ((Fintype.equivFin (Fin k₀ × Fin k)).symm n).1 *
        σ ((Fintype.equivFin (Fin k₀ × Fin k)).symm n).2) := by
  classical
  refine isLocalRepOn_of_fintype (K := Fin k₀ × Fin k)
    (fun κ => Polyfold.sectionAdd A.P (s₀ κ.1) (s κ.2)) (fun κ => σ₀ κ.1 * σ κ.2)
    (fun κ => mul_pos (h₀.1 κ.1) (h.1 κ.2)) (fun κ => ?_) ?_ (fun w hw => ?_)
  · exact IsScPlusSectionOn.sectionAdd hO (h₀.2.1 κ.1) (h.2.1 κ.2) (hs₀ _) (hs _)
  · rw [Fintype.sum_prod_type, ← h₀.2.2.1]
    refine Finset.sum_congr rfl fun a _ => ?_
    change ∑ j, σ₀ a * σ j = σ₀ a
    rw [← Finset.mul_sum, h.2.2.1, mul_one]
  · rw [multisectionAdd_eq_sum_of_isLocalRepOn h₀ h hs₀ hs hw, Fintype.sum_prod_type]

section Branch

variable {O : Set A.Obj} (hO : IsOpen O) [Nonempty O] [ParacompactSpace O]
  [ParacompactSpace (pullbackSpace A.P (Subtype.val : O → A.Obj))]

/-! ### The slices -/

/-- **The slice of the parametrized branch is the branch of `Λ₀ ⊕ Λ_t`**: with
`F(t, y) = (f − s⁰)|O + Σ_j t_j (−s_j)|O`, the slice at `t` is `(f − (s⁰ + Σ_j t_j s_j))|O`. -/
theorem paramSlice_branch_eq_rel {f : A.Obj → A.W} (hf : IsSection A.P f) {s₀ : A.Obj → A.W}
    (hs₀ : IsSection A.P s₀) {ℓ : ℕ} {s : Fin ℓ → A.Obj → A.W} (hs : ∀ j, IsSection A.P (s j))
    (t : Fin ℓ → ℝ) :
    paramSlice (subRestrict (O := O) f s₀ hf) (isSection_restrictSection _)
        (fun j => negRestrict (O := O) (s j)) (fun j => isSection_negRestrict (s j)) t =
      subRestrict (O := O) f (Polyfold.sectionAdd A.P s₀ (paramSec s t)) hf := by
  funext p
  have hlhs := isSection_paramSlice (g := subRestrict (O := O) f s₀ hf)
    (hg := isSection_restrictSection _) (t := fun j => negRestrict (O := O) (s j))
    (ht := fun j => isSection_negRestrict (s j)) t p
  have hrhs : IsSection (pullbackProj A.P (Subtype.val : O → A.Obj))
      (subRestrict (O := O) f (Polyfold.sectionAdd A.P s₀ (paramSec s t)) hf) :=
    isSection_restrictSection _
  suffices h : pbLin p ⟨_, hlhs⟩ = pbLin p ⟨_, hrhs p⟩ from
    congrArg Subtype.val (pbLin_injective p h)
  have hp : (p : A.Obj) ∈ O := p.2
  have e1 : (⟨paramSlice (subRestrict (O := O) f s₀ hf)
      (isSection_restrictSection _) (fun j => negRestrict (O := O) (s j))
      (fun j => isSection_negRestrict (s j)) t p, hlhs⟩ :
        pullbackProj A.P (Subtype.val : O → A.Obj) ⁻¹' {p}) =
      ⟨subRestrict (O := O) f s₀ hf p, isSection_restrictSection _ p⟩ +
        ∑ j, t j • (⟨negRestrict (O := O) (s j) p, isSection_negRestrict (s j) p⟩ :
          pullbackProj A.P (Subtype.val : O → A.Obj) ⁻¹' {p}) := rfl
  have hsub : ∀ (h : A.Obj → A.W), (⟨subSec f h O p, isSection_subSec hf h O p⟩ :
      A.P ⁻¹' {(p : A.Obj)}) = ⟨f p, hf p⟩ + (-1 : ℝ) • ⟨extendZero O h p,
        isSection_extendZero O h p⟩ := fun h => by
    apply Subtype.ext
    change subSec f h O p = _
    unfold subSec
    rw [sectionAdd_apply hf (isSection_extendZero O h).sectionSmul]
    congr 2
    exact Subtype.ext (sectionSmul_apply (f := fun _ => (-1 : ℝ)) (isSection_extendZero O h) _)
  have hneg : ∀ j, (⟨Polyfold.sectionSmul A.P (fun _ => (-1 : ℝ)) (extendZero O (s j)) p,
      (isSection_extendZero O (s j)).sectionSmul p⟩ : A.P ⁻¹' {(p : A.Obj)}) =
      (-1 : ℝ) • ⟨s j p, hs j p⟩ := fun j => by
    apply Subtype.ext
    change Polyfold.sectionSmul A.P (fun _ => (-1 : ℝ)) (extendZero O (s j)) p = _
    rw [sectionSmul_apply (isSection_extendZero O (s j))]
    congr 2
    exact Subtype.ext (extendZero_eqOn (fun y _ => hs j y) hp).symm
  have hz0 : (⟨extendZero O s₀ p, isSection_extendZero O _ p⟩ : A.P ⁻¹' {(p : A.Obj)}) =
      ⟨s₀ p, hs₀ p⟩ :=
    Subtype.ext (extendZero_eqOn (fun y _ => hs₀ y) hp).symm
  have hpar : (⟨extendZero O (Polyfold.sectionAdd A.P s₀ (paramSec s t)) p,
      isSection_extendZero O _ p⟩ : A.P ⁻¹' {(p : A.Obj)}) =
      ⟨s₀ p, hs₀ p⟩ + ∑ j, t j • ⟨s j p, hs j p⟩ := by
    rw [← paramFib hs t p]
    refine Subtype.ext ?_
    change extendZero O (Polyfold.sectionAdd A.P s₀ (paramSec s t)) p = _
    rw [← extendZero_eqOn (fun y _ => hs₀.sectionAdd (isSection_paramSec s t) y) hp]
    exact sectionAdd_apply hs₀ (isSection_paramSec s t) p
  rw [e1, map_add, map_sum]
  simp only [map_smul]
  change (⟨subSec f s₀ O p, _⟩ : A.P ⁻¹' {(p : A.Obj)}) +
      ∑ j, t j • (⟨Polyfold.sectionSmul A.P (fun _ => (-1 : ℝ)) (extendZero O (s j)) p, _⟩ :
        A.P ⁻¹' {(p : A.Obj)}) = ⟨subSec f (Polyfold.sectionAdd A.P s₀ (paramSec s t)) O p, _⟩
  rw [hsub, hsub, hz0, hpar]
  simp only [hneg, smul_add, Finset.smul_sum, smul_smul, add_assoc]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

/-! ### (15.1) relative to `Λ₀` gives Part I's properties (i)–(ii) -/

set_option maxHeartbeats 1600000 in
-- the chart reading of (15.1) in the transported chart, with the branch `s⁰` for `0`
include hO in
/-- **(15.1) for the operator `(f − s⁰)'(x)` gives Part I's properties (i)–(ii)** (GB's
`isParamGP_restrictTo_of_onto` with a branch `s⁰` of `Λ₀` through `f(x)` in place of `0`): in a
chart `c` of `W` with domain in `O`, centred at `x` with `f(x) = s⁰(x)`, if
`(v, τ) ↦ (f − s⁰)'(x)v + Σ_j τ_j s_j(x)` maps `T^R_xX × ℝ^ℓ` onto `W_x`, then in the transported
chart of `W|O`, `F(t, y) = (f − s⁰)|O + Σ_j t_j (−s_j)|O` has the properties (i)–(ii) of Part I's
proof of Theorem 5.3.10 (`IsParamGP`). -/
theorem isParamGP_restrictTo_of_onto_rel {f : A.Obj → A.W}
    (hft : A.B.IsScFredholmSectionTame f) {s₀ : A.Obj → A.W} (hs0 : IsScPlusSectionOn A s₀ O)
    {ℓ : ℕ} {s : Fin ℓ → A.Obj → A.W} (hs : ∀ j, IsScPlusSectionOn A (s j) O)
    (hsec : ∀ j, IsSection A.P (s j)) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hsub : c.φ.source ⊆ O) {x : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hφ0 : c.φ (A.X.PObj.levelVal 1 x) = 0)
    (hx0 : f (A.X.PObj.levelVal 1 x) = s₀ (A.X.PObj.levelVal 1 x)) {n : ℕ}
    {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hon : ∀ w : A.P ⁻¹' {A.X.PObj.levelVal 1 x}, ∃ v ∈ reducedTangentFiber c.isChart hx T,
      ∃ τ : Fin ℓ → ℝ, toIntr c hx (subDeriv c f s₀
        (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) v +
          ∑ j, τ j • (⟨s j (A.X.PObj.levelVal 1 x), hsec j _⟩ :
            A.P ⁻¹' {A.X.PObj.levelVal 1 x}) = w)
    (q₀ : pullbackSpace A.P (Subtype.val : O → A.Obj)) :
    (c.restrictTo A.B.continuous hO hsub q₀).IsParamGP
      (subRestrict (O := O) f s₀ hft.isScSmooth.1)
      (fun j => negRestrict (O := O) (s j)) T := by
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
  have hread : ∀ w : A.P ⁻¹' {A.X.PObj.levelVal 1 x},
      ∃ v ∈ reducedTangentFiber c.isChart hx T, ∃ τ : Fin ℓ → ℝ,
      subDeriv c f s₀ (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))
        (tangentFiberEquiv c.isChart hx v : c.φ.model.E 0) +
        ∑ j, τ j • c.fiberLin hx ⟨s j (A.X.PObj.levelVal 1 x),
          hsec j (A.X.PObj.levelVal 1 x)⟩ = c.fiberLin hx w := fun w => by
    obtain ⟨v, hv, τ, he⟩ := hon w
    refine ⟨v, hv, τ, ?_⟩
    have := congrArg (c.fiberLin hx) he
    rw [map_add, map_sum] at this
    simp only [map_smul] at this
    rwa [fiberLin_toIntr_subDeriv hft.isScSmooth hs0 hc hsub hx hx0] at this
  have hred : ∀ v ∈ reducedTangentFiber c.isChart hx T,
      (tangentFiberEquiv c.isChart hx v : c.φ.model.E 0) ∈ minimalSubspaceWith T 0 := by
    intro v hv
    have := hv
    rw [reducedTangentFiber, Submodule.mem_comap, fiberCoord_eq_coe, hφ0] at this
    exact this
  have hrng : ∀ v : A.X.PObj.tangentFiber x,
      (tangentFiberEquiv c.isChart hx v : c.φ.model.E 0) ∈ rangeS (scDeriv c.U (r c.R) 0) :=
    fun v => by
      have := (c.mem_tangentFiberModel_iff_rangeS hx _).1 (tangentFiberEquiv c.isChart hx v).2
      rw [hz0] at this
      exact this
  refine ⟨fun k hk => ?_, fun w => ?_⟩
  · -- (i)
    have hk' : (c.φ (A.X.PObj.levelVal 1 x), k) ∈ c.K := by rw [hφ0]; exact hk
    obtain ⟨w, rfl⟩ := c.mem_range_fiberLin hx hk'
    obtain ⟨v, -, τ, he⟩ := hread w
    refine ⟨⟨_, hrng v⟩, -τ, ?_⟩
    rw [hlin]
    refine Eq.trans ?_ he
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (congrArg (fun q : c.F 0 => (-τ) j • q) (hcol j)).trans (neg_smul_neg (τ j) _)
  · -- (ii)
    let w0 : c.φ.model.E 0 := (w : (c.restrictTo A.B.continuous hO hsub q₀).φ.model.E 0)
    have hwT : w0 ∈ tangentFiberModel c.isChart hx :=
      (c.mem_tangentFiberModel_iff_rangeS hx _).2 (by rw [hz0]; exact w.2)
    set α := (tangentFiberEquiv c.isChart hx).symm
      ⟨w0, hwT⟩ with hα
    have hαw : (tangentFiberEquiv c.isChart hx α : c.φ.model.E 0) = w0 := by
      rw [hα, Equiv.apply_symm_apply]
    obtain ⟨v, hv, τ, he⟩ :=
      hread (toIntr c hx (subDeriv c f s₀
        (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) α)
    rw [fiberLin_toIntr_subDeriv hft.isScSmooth hs0 hc hsub hx hx0, hαw] at he
    refine ⟨⟨w0 - (tangentFiberEquiv c.isChart hx v : c.φ.model.E 0),
      Submodule.sub_mem (rangeS (scDeriv c.U (r c.R) 0)) w.2 (hrng v)⟩, τ, ?_, ?_⟩
    · rw [hlin]
      have hs1 : ∀ j, τ j • (c.restrictTo A.B.continuous hO hsub q₀).principal
          (negRestrict (O := O) (s j)) 0 =
          -(τ j • c.fiberLin hx ⟨s j (A.X.PObj.levelVal 1 x), hsec j (A.X.PObj.levelVal 1 x)⟩) :=
        fun j => (congrArg (fun q : c.F 0 => τ j • q) (hcol j)).trans (smul_neg _ _)
      rw [Finset.sum_congr rfl fun j _ => hs1 j]
      change subDeriv c f s₀ (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))
        (w0 - (tangentFiberEquiv c.isChart hx v : c.φ.model.E 0)) +
          ∑ j, -(τ j • c.fiberLin hx ⟨s j (A.X.PObj.levelVal 1 x),
            hsec j (A.X.PObj.levelVal 1 x)⟩) = 0
      rw [Finset.sum_neg_distrib, map_sub, ← he]
      abel
    · change w0 - (w0 - (tangentFiberEquiv c.isChart hx v : c.φ.model.E 0)) ∈ _
      rw [sub_sub_cancel]
      exact hred v hv

/-! ### General position of the parametrized branch -/

variable {ℓ : ℕ} [ParacompactSpace ((Fin ℓ → ℝ) × O)]
  [ParacompactSpace (pullbackSpace (pullbackProj A.P (Subtype.val : O → A.Obj))
    (Prod.snd : (Fin ℓ → ℝ) × O → O))]

set_option maxHeartbeats 1600000 in
-- the chart reading of (15.1) relative to `Λ₀` and Part I's Theorem 5.3.10 step (i)–(ii)
include hO in
/-- **(15.1) relative to `Λ₀` makes the parametrized branch in general position at `(0, x)`**
(steps (c)–(d) of the proof of Theorem 15.3.9, read with Part I's proof of Theorem 5.3.10): let
`(s⁰_a, σ⁰_a)` be a local representation of `Λ₀` on `O` and `s⁰_a(x) = f(x)`.  If for every
operator `L` of `T(f, Λ₀)(x)` the map `(v, τ) ↦ L v + Σ_j τ_j s_j(x)` is onto `W_x` from
`T^R_xX × ℝ^ℓ`, then `F(t, y) = (f − s⁰_a)|O + Σ_j t_j (−s_j)|O` is in general position at
`(0, x)` (Definition 5.3.9 on `ℝ^ℓ × O`). -/
theorem isGeneralPositionGerm_branchParam_rel {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ₀ : A.W → ℚ≥0} {k₀ : ℕ} {s₀ : Fin k₀ → A.Obj → A.W} {σ₀ : Fin k₀ → ℚ≥0}
    (hrep₀ : IsLocalRepOn A Λ₀ O s₀ σ₀) (a : Fin k₀)
    {s : Fin ℓ → A.Obj → A.W} (hs : ∀ j, IsScPlusSectionOn A (s j) O)
    (hsec : ∀ j, IsSection A.P (s j)) {x : A.X.PObj.Level 1}
    (hxO : A.X.PObj.levelVal 1 x ∈ O)
    (hx0 : f (A.X.PObj.levelVal 1 x) = s₀ a (A.X.PObj.levelVal 1 x))
    (hon : ∀ L ∈ (linearization f Λ₀ x).support, ∀ (φ : MChart A.Obj)
      (hφ : A.X.PObj.IsChart φ) (hx : A.X.PObj.levelVal 1 x ∈ φ.source) (m : ℕ)
      (V : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin m → ℝ)).prod V)),
      φ.model.C = T 0 ⁻¹' quadrant m V 0 →
        ∀ w : A.P ⁻¹' {A.X.PObj.levelVal 1 x}, ∃ v ∈ reducedTangentFiber hφ hx T,
          ∃ τ : Fin ℓ → ℝ, L v + ∑ j, τ j •
            (⟨s j (A.X.PObj.levelVal 1 x), hsec j _⟩ : A.P ⁻¹' {A.X.PObj.levelVal 1 x}) = w) :
    ((A.B.restrictOpen hO).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold ℓ) (A.X.PObj.restrictOpen hO))).IsGeneralPositionGerm
      (paramSection (subRestrict (O := O) f (s₀ a) hft.isScSmooth.1)
        (isScFredholmSectionTame_subRestrict hO hft (hrep₀.2.1 a)).isScSmooth.1
        (fun j => negRestrict (O := O) (s j))
        fun j => (isScPlusSection_negRestrict hO (hs j)).1)
      (0, ⟨A.X.PObj.levelVal 1 x, hxO⟩) := by
  classical
  set y := A.X.PObj.levelVal 1 x with hy
  have hs0 : IsScPlusSectionOn A (s₀ a) O := hrep₀.2.1 a
  have hys : y ∈ A.X.PObj.smoothSet := mem_smoothSet_of_eq hft hO hs0 hxO hx0
  obtain ⟨-, c₀, hc₀, hxc₀, hφ0, -⟩ := hft.germTame y hys
  set c := c₀.restrictInter hO with hcdef
  have hc : A.B.IsTameChart c := hc₀.restrictInter hO
  have hsub : c.φ.source ⊆ O := c₀.restrictInter_source_subset hO
  have hxc : y ∈ c.φ.source := ⟨hxc₀, hxO⟩
  have hφ0c : c.φ y = 0 := hφ0
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  let d : LocalLinData A Λ₀ x := ⟨O, hO, k₀, s₀, σ₀, hrep₀, c, hc.1, hsub, hxc⟩
  have hL : toIntr c hxc (subDeriv c f (s₀ a) (levelLift c.φ 1 y)) ∈
      (linearization f Λ₀ x).support := by
    rw [linearization_eq hf d]
    exact (mem_support_linSumIntr_iff hf.1.1.1 hrep₀.1 (fun b => (hrep₀.2.1 b).1) hsub hxc
      _).2 ⟨a, hx0.symm, rfl⟩
  have hon' := hon _ hL c.φ c.isChart hxc n Wq T hT
  set q₀ := subRestrict (O := O) f (s₀ a) hft.isScSmooth.1 ⟨y, hxO⟩
  have hGP := isParamGP_restrictTo_of_onto_rel hO hft hs0 hs hsec hc.1 hsub hxc hφ0c hx0 T hon' q₀
  have hgO := isScFredholmSectionTame_subRestrict hO hft hs0
  have hy0 : IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
      (subRestrict (O := O) f (s₀ a) hft.isScSmooth.1) ⟨y, hxO⟩ := by
    unfold subRestrict
    rw [isZeroAt_restrictSection_iff]
    exact (isZeroAt_subSec_iff hft.isScSmooth.1 hs0.1 hxO).2 hx0
  have hc'T : (A.B.restrictOpen hO).IsTameChart (c.restrictTo A.B.continuous hO hsub q₀) :=
    ⟨restrictOpen_isChart_restrictTo hO hc.1 hsub q₀, hc.2⟩
  exact isGeneralPositionGerm_paramSection_of_isParamGP hgO
    (fun j => isScPlusSection_negRestrict hO (hs j)) hy0 hc'T hxc hφ0c T hT hGP

end Branch

end SBLocalization

end Polyfold
