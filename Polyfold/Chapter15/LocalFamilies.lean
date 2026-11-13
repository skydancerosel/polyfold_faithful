import Polyfold.Chapter15.ParamOntoTransport
import Polyfold.Chapter13.AtomicStructurable

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.7** (General Position; 2017: Theorem 15.4), pp. 694–696, "Local constructions at
`x ∈ S_f`": the atomic parameter families `t ↦ Λ^x_t` and GP's `HasLocalGPFamilies`.

# The local families of the proof of Theorem 15.3.7

## The text, paraphrased

At `x ∈ S_f` choose `U(x)` with the natural `G_x`-action, `V(x)` invariant with
`cl V(x) ⊆ U(x)`, and sc⁺-sections `s¹_j` supported in `V(x)` with `N(s¹_j) ≤ min{1, h}` such that
`f'(x)(T^R_xX) + span{s¹_j(x)} = W_x`; the symmetric family `s^g_t = Σ_j t_j s^g_j` gives an
atomic, hence structurable, sc⁺-multisection `Λ^x_t` for every `t ∈ ℝ^ℓ`.  The surjectivity
(15.1) holds at the points of `S_f` near `x`, then on a saturated open `Q(x)` by equivariance.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `mem_solutionSet_tgt`: `S_f` is saturated for a section functor `f`.
* `GPFamily.saturate`, **`hasLocalGPFamilies_of_nhds`**: a family on an open `V ∋ x` (not
  necessarily saturated) is a family on the saturation of `V` (the step "by equivariance", with
  `IsParamOntoAt.of_mor`).  So GP's `HasLocalGPFamilies` only needs families on neighbourhoods.
* `paramSec_eq_paramSlice`, `isScPlusSection_paramSec`, `sectionSupport_paramSec_subset`,
  `natTerm_paramSec` (the natural translates `s^g` of a seed are linear in the seed).
* `SeedData A`: `x`, `U(x)` (a natural representation with the properness property), `V(x)`,
  and seeds `s_j` supported in `V(x)`; `SeedData.atom t` the atomic data of the seed
  `Σ_j t_j s_j` (A's `SymmetricFamily.ofSeed`, `AtomicData.ofFamily`), `SeedData.Λ t` its atomic
  multisection.  Proved: structurable for every `t` (C's Theorem 13.5.3), **linear in `t`**
  (`SeedData.isLinearFamily`: on `U(x)` the branches `Σ_j t_j s^g_j`, carried along morphisms
  elsewhere, the zero section off the saturation of `cl V(x)`), `N(Λ_t) ≤ |t|₁ h`
  (`SeedData.norm_le`), `dom-supp(Λ_t) ⊆ U`, and (15.1) at every point `y ∈ S_f` of
  `Q₀ = ⋂_g (U(x) ∩ Φ_g⁻¹ W)` when (15.1) holds for the seeds at the points of `S_f ∩ W`
  (`SeedData.gpFamily`; the branches at `y` are `μ(Γ(g, ·), s_j(g⁻¹ ∗ y))`, and
  `IsParamOntoVec.of_mor` carries (15.1) from `g⁻¹ ∗ y` to `y`).
* **`HasLocalParamSeeds A f N`**: the analytic input left, stated on the object M-polyfold
  without the groupoid: at every `x ∈ S_f`, inside every open `O ∋ x` and below every `ε > 0`,
  finitely many sc⁺-sections `s_j` of `W → X` supported in `O` with `N(s_j) ≤ ε`, and an open
  `W ∋ x` such that (15.1) holds with the vectors `s_j(y)` at every `y ∈ S_f ∩ W`.
* **`hasLocalGPFamilies_of_seeds`**: `HasLocalParamSeeds` gives GP's `HasLocalGPFamilies` (good
  system, `(N, U)` controlling compactness, `h` continuous, positive, functorial).
* **`theorem_15_3_7_of_seeds`**: Theorem 15.3.7 (`theorem_15_3_7_statement`) from a good system,
  `HasLocalParamSeeds` and GP's `HasParametricGeneralPosition`.
* Witness: `hasLocalParamSeeds_epSEP_zero`, `theorem_15_3_7_statement_epSEP_zero_of_seeds`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold

variable {A : SEP.{u}}

/-! ### The solution set is saturated -/

/-- `S_f` is saturated: `f(s φ) = 0 ⇒ f(t φ) = μ(φ, 0) = 0`. -/
theorem mem_solutionSet_tgt {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (φ : A.Mor) (h : A.X.src φ ∈ solutionSet A.P f) : A.X.tgt φ ∈ solutionSet A.P f := by
  change f (A.X.tgt φ) = fiberZero A.P (A.X.tgt φ)
  rw [hf.1.2 φ]
  have h' : f (A.X.src φ) = fiberZero A.P (A.X.src φ) := h
  have e : A.E.μ (EpStrongBundle.sectionPair hf.1.1.1 φ) =
      A.E.μ ⟨(φ, fiberZero A.P (A.X.src φ)), isSection_fiberZero _⟩ :=
    A.E.μ_congr (q := EpStrongBundle.sectionPair hf.1.1.1 φ) (Prod.ext rfl h')
  exact e.trans (A.E.μ_fiberZero φ)

/-- The source of a morphism into a level-`1` point is a level-`1` point. -/
theorem src_mem_levelSet_one {φ : A.Mor} {z : A.X.PObj.Level 1}
    (hz : A.X.PObj.levelVal 1 z = A.X.tgt φ) : A.X.src φ ∈ A.X.PObj.levelSet 1 :=
  (A.X.mem_levelSet_src_iff φ 1).2 ((A.X.mem_levelSet_tgt_iff φ 1).1 (hz ▸ levelVal_mem z))

/-! ### From neighbourhoods to saturated sets -/

variable {f : A.Obj → A.W} {N : A.B.One → ℝ} {U : Set A.Obj} {h : A.Obj → ℝ}

/-- **A family on `V` is a family on the saturation of `V`** (the step "by equivariance" of the
proof of Theorem 15.3.7): (15.1) is carried along morphisms (`IsParamOntoAt.of_mor`). -/
def GPFamily.saturate (hf : A.E.IsScFredholmSectionFunctor f) {V : Set A.Obj}
    (F : GPFamily A f N U h V) : GPFamily A f N U h (A.X.saturation V) where
  ℓ := F.ℓ
  Λ := F.Λ
  isStructurable := F.isStructurable
  isLinear := F.isLinear
  norm_le := F.norm_le
  domSupp_subset := F.domSupp_subset
  paramOnto z hz hzS := by
    obtain ⟨a, haV, ha⟩ := hz
    obtain ⟨φ, hφs, hφt⟩ := A.X.π_eq_π_iff.1 ha
    have h1 := src_mem_levelSet_one (z := z) hφt.symm
    have haS : A.X.src φ ∈ solutionSet A.P f := by
      have := mem_solutionSet_tgt hf (A.X.inv φ) (by rw [A.X.src_inv, hφt]; exact hzS)
      rwa [A.X.tgt_inv] at this
    have H := F.paramOnto (A.X.PObj.levelMk 1 (A.X.src φ) h1)
      (by rw [A.X.PObj.levelVal_levelMk, hφs]; exact haV)
      (by rw [A.X.PObj.levelVal_levelMk]; exact haS)
    exact H.of_mor hf (fun t => (F.isStructurable t).1.1) φ (A.X.PObj.levelVal_levelMk _ _ _)
      hφt.symm

/-- **GP's `HasLocalGPFamilies` from families on neighbourhoods**: it suffices that every
`x ∈ S_f` has an open neighbourhood `V` (not necessarily saturated) carrying a family. -/
theorem hasLocalGPFamilies_of_nhds (hf : A.E.IsScFredholmSectionFunctor f)
    (H : ∀ x ∈ solutionSet A.P f, ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧
      Nonempty (GPFamily A f N U h V)) : HasLocalGPFamilies A f N U h := by
  intro x hx
  obtain ⟨V, hV, hxV, ⟨F⟩⟩ := H x hx
  exact ⟨A.X.saturation V, EpGroupoid.isOpen_saturation_of_isOpen A.X hV,
    EpGroupoid.isSaturated_saturation A.X V, A.X.subset_saturation V hxV, ⟨F.saturate hf⟩⟩

/-! ### Linear combinations of sc⁺-sections -/

/-- `Σ_j t_j s_j` is Part I's slice `0 + Σ_j t_j s_j`. -/
theorem paramSec_eq_paramSlice {ℓ : ℕ} {s : Fin ℓ → A.Obj → A.W}
    (hs : ∀ j, IsSection A.P (s j)) (t : Fin ℓ → ℝ) :
    paramSec s t = paramSlice (fiberZero A.P) (isSection_fiberZero (P := A.P)) s hs t := by
  funext y
  rw [paramSec_apply hs]
  change _ = (((0 : A.P ⁻¹' {y}) + ∑ j, t j • (⟨s j y, hs j y⟩ : A.P ⁻¹' {y}) :
    A.P ⁻¹' {y}) : A.W)
  rw [zero_add]

/-- `Σ_j t_j s_j` is an sc⁺-section. -/
theorem isScPlusSection_paramSec {ℓ : ℕ} {s : Fin ℓ → A.Obj → A.W}
    (hs : ∀ j, A.B.IsScPlusSection (s j)) (t : Fin ℓ → ℝ) :
    A.B.IsScPlusSection (paramSec s t) := by
  rw [paramSec_eq_paramSlice (fun j => (hs j).1)]
  exact isScPlusSection_paramSlice StrongBundle.isScPlusSection_fiberZero hs t

/-- The support of `Σ_j t_j s_j` lies in `V` if all supports do. -/
theorem sectionSupport_paramSec_subset {ℓ : ℕ} {s : Fin ℓ → A.Obj → A.W}
    (hs : ∀ j, IsSection A.P (s j)) {V : Set A.Obj} (hsV : ∀ j, sectionSupport A.P (s j) ⊆ V)
    (t : Fin ℓ → ℝ) : sectionSupport A.P (paramSec s t) ⊆ V := by
  rw [paramSec_eq_paramSlice hs]
  refine (sectionSupport_paramSlice_subset _ hs t).trans (union_subset ?_ (iUnion_subset hsV))
  intro y hy
  exfalso
  refine (closure_mono (s := {y | ¬ IsZeroAt A.P (fiberZero A.P) y}) ?_ |>.trans
    closure_empty.le) hy
  intro z hz
  exact hz rfl

/-- The fibre combination of zero sections is the zero section. -/
theorem paramSec_fiberZero {ℓ : ℕ} (t : Fin ℓ → ℝ) :
    paramSec (fun _ : Fin ℓ => fiberZero A.P) t = fiberZero A.P := by
  funext y
  rw [paramSec_apply (fun _ => isSection_fiberZero)]
  change (((∑ j, t j • (0 : A.P ⁻¹' {y})) : A.P ⁻¹' {y}) : A.W) = ((0 : A.P ⁻¹' {y}) : A.W)
  rw [Finset.sum_eq_zero fun j _ => smul_zero (t j)]

/-- **The natural translates of a seed are linear in the seed**: on `U(x)`,
`(Σ_j t_j s_j)^g = Σ_j t_j s_j^g`. -/
theorem natTerm_paramSec {x : A.Obj} (R : A.X.NaturalRep x) {ℓ : ℕ}
    {s : Fin ℓ → A.Obj → A.W} (hs : ∀ j, IsSection A.P (s j)) (t : Fin ℓ → ℝ)
    (k : A.X.Isotropy x) {y : A.Obj} (hy : y ∈ R.U) :
    EpStrongBundle.natTerm A.E R (isSection_paramSec s t) k y =
      paramSec (fun j => EpStrongBundle.natTerm A.E R (hs j) k) t y := by
  set m := R.Γ k (R.Φ k⁻¹ y)
  have htgt : A.X.tgt m = y := EpStrongBundle.tgt_Γ_Φ_inv R k hy
  have hnat : ∀ {σ : A.Obj → A.W} (hσ : IsSection A.P σ),
      EpStrongBundle.natTerm A.E R hσ k y = (muLin m rfl htgt ⟨σ (A.X.src m), hσ _⟩ : A.W) :=
    fun hσ => by
      rw [EpStrongBundle.natTerm_of_mem (E := A.E) R hσ k hy, muLin_apply]
      rfl
  rw [hnat, paramSec_apply (fun j => EpStrongBundle.isSection_natTerm (E := A.E) R (hs j) k)]
  congr 1
  rw [paramFib hs t, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  congr 1
  exact Subtype.ext (hnat (hs j)).symm

/-! ### Seed data and the atomic family -/

variable (A) in
/-- **The data of the local construction at `x`**: `U(x)` (a natural representation with the
properness property), an invariant open `V(x) ∋ x` with `cl V(x) ⊆ U(x)`, and sc⁺-sections
(seeds) `s_j` of `W → X` supported in `V(x)`. -/
structure SeedData where
  /-- The point. -/
  x : A.Obj
  /-- The natural representation on `U(x)`. -/
  R : A.X.NaturalRep x
  hprop : A.X.HasPropernessProperty R.U
  /-- The set `V(x)`. -/
  V : Set A.Obj
  isOpen_V : IsOpen V
  mem_V : x ∈ V
  mapsTo_V : ∀ g, MapsTo (R.Φ g) V V
  closure_V_subset : closure V ⊆ R.U
  /-- The number of seeds. -/
  ℓ : ℕ
  /-- The seeds. -/
  s : Fin ℓ → A.Obj → A.W
  isScPlusSection : ∀ j, A.B.IsScPlusSection (s j)
  support_subset : ∀ j, sectionSupport A.P (s j) ⊆ V

namespace SeedData

variable (S : SeedData A)

/-- **The atomic data of the seed `Σ_j t_j s_j`** (A's `SymmetricFamily.ofSeed`,
`AtomicData.ofFamily`; the family `s^g_t` of the proof). -/
def atom (t : Fin S.ℓ → ℝ) : AtomicData A :=
  AtomicData.ofFamily S.R S.hprop
    (SymmetricFamily.ofSeed S.R S.mapsTo_V S.closure_V_subset
      (isScPlusSection_paramSec S.isScPlusSection t)
      (sectionSupport_paramSec_subset (fun j => (S.isScPlusSection j).1) S.support_subset t))
    S.isOpen_V S.mem_V S.mapsTo_V S.closure_V_subset
    (fun i _ hy => SymmetricFamily.ofSeed_vanish S.mapsTo_V S.closure_V_subset _ _ i hy)

instance (t : Fin S.ℓ → ℝ) : Nonempty (S.atom t).I := ⟨(1 : A.X.Isotropy S.x)⟩

/-- **The atomic sc⁺-multisection `Λ^x_t`.** -/
def Λ (t : Fin S.ℓ → ℝ) : A.W → ℚ≥0 := (S.atom t).mult

theorem atom_R (t : Fin S.ℓ → ℝ) : (S.atom t).R = S.R := rfl

theorem atom_V (t : Fin S.ℓ → ℝ) : (S.atom t).V = S.V := rfl

theorem isAtomic_Λ (t : Fin S.ℓ → ℝ) : IsAtomic A (S.Λ t) := (S.atom t).isAtomic_mult

theorem isScPlusMultisection_Λ (t : Fin S.ℓ → ℝ) : IsScPlusMultisection A (S.Λ t) :=
  (S.atom t).isScPlusMultisection_mult

/-- The translates `s^g_j` of the seeds, indexed by `Fin |G_x|`. -/
def branch (i : Fin (@Fintype.card (A.X.Isotropy S.x) (Fintype.ofFinite _))) (j : Fin S.ℓ) :
    A.Obj → A.W :=
  EpStrongBundle.natTerm A.E S.R (S.isScPlusSection j).1
    ((@Fintype.equivFin (A.X.Isotropy S.x) (Fintype.ofFinite _)).symm i)

theorem isSection_branch (i) (j : Fin S.ℓ) : IsSection A.P (S.branch i j) :=
  EpStrongBundle.isSection_natTerm (E := A.E) S.R _ _

/-- **On `U(x)` the branches of `Λ^x_t` are `Σ_j t_j s^g_j`** (linear in `t`). -/
theorem isLocalRepOn_branch (t : Fin S.ℓ → ℝ) :
    IsLocalRepOn A (S.Λ t) S.R.U (fun i => paramSec (S.branch i) t)
      (fun _ => (@Fintype.card (A.X.Isotropy S.x) (Fintype.ofFinite _) : ℚ≥0)⁻¹) := by
  refine (S.atom t).isLocalRepOn_mult.congr_eqOn fun i y hy => ?_
  exact natTerm_paramSec S.R (fun j => (S.isScPlusSection j).1) t _ hy

/-- **Off the saturation of `cl V(x)`, `Λ^x_t` is the trivial multisection.** -/
theorem isLocalRepOn_zero (t : Fin S.ℓ → ℝ) :
    IsLocalRepOn A (S.Λ t) (A.X.saturation (closure S.V))ᶜ (k := 1)
      (fun _ => paramSec (fun _ : Fin S.ℓ => fiberZero A.P) t) (fun _ => 1) := by
  have hO : IsOpen (A.X.saturation (closure S.V))ᶜ :=
    (S.atom t).isClosed_saturation_closure_V.isOpen_compl
  rw [paramSec_fiberZero]
  refine ⟨fun _ => one_pos, fun _ => isScPlusSectionOn_fiberZero hO, by simp, fun w hw => ?_⟩
  rw [Λ, (S.atom t).mult_eq_zeroMultisection hw]
  simp [zeroMultisection]

/-- **`t ↦ Λ^x_t` is a linear family** (GP's `IsLinearFamily`). -/
theorem isLinearFamily : IsLinearFamily S.Λ := by
  intro x₀
  by_cases hr : (S.atom 0).Reach x₀
  · obtain ⟨φ, hs, ht⟩ := hr
    obtain ⟨O', s', hO', hxO', hs', hr', -⟩ := exists_linearRep_of_mor
      (fun t => (S.isScPlusMultisection_Λ t).1) (A.X.inv φ) S.R.isOpen_U
      (by rw [A.X.src_inv]; exact ht) S.isSection_branch S.isLocalRepOn_branch
    refine ⟨O', _, s', _, hO', ?_, hs', hr'⟩
    rw [A.X.tgt_inv] at hxO'
    rwa [hs] at hxO'
  · refine ⟨(A.X.saturation (closure S.V))ᶜ, 1, fun _ _ => fiberZero A.P, fun _ => 1,
      (S.atom 0).isClosed_saturation_closure_V.isOpen_compl, fun hx => hr ?_,
      fun _ _ => isSection_fiberZero, S.isLocalRepOn_zero⟩
    exact ((S.atom 0).reach_iff_mem_saturation x₀).2
      ((S.atom 0).saturation_closure_V_subset hx)

/-- **Structurable** (C's Theorem 13.5.3: atomic ⇒ structurable, given a good system). -/
theorem isStructurable_Λ (h𝒰 : Nonempty A.X.GoodSystem) (t : Fin S.ℓ → ℝ) :
    IsStructurable A (S.Λ t) :=
  theorem_13_5_3_of_goodSystem h𝒰 (S.isAtomic_Λ t)

/-- **The domain support**: `dom-supp(Λ^x_t) ⊆ π⁻¹(π(U(x)))`. -/
theorem domSupp_Λ_subset (t : Fin S.ℓ → ℝ) : domSupp (S.Λ t) ⊆ A.X.saturation S.R.U :=
  (S.atom t).domSupp_mult_subset.trans (S.atom t).saturation_closure_V_subset

/-- **The norm bound** `N(Λ^x_t)(z) ≤ |t|₁ · h(z)`, from `N(s_j) ≤ c` and `c ≤ h` on the saturation
of `U(x)` (`h ≥ 0`). -/
theorem norm_le (hN : A.E.IsAuxNorm N) {c : ℝ} (hc : 0 ≤ c)
    (hsN : ∀ j y, normW N (S.s j y) ≤ c) (hch : ∀ y ∈ A.X.saturation S.R.U, c ≤ h y)
    (hh0 : ∀ y, 0 ≤ h y) (t : Fin S.ℓ → ℝ) (z : A.Obj) :
    pointwiseNorm N (S.Λ t) z ≤ (∑ j, |t j|) * h z := by
  have ht0 : 0 ≤ ∑ j, |t j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  by_cases hr : (S.atom t).Reach z
  · have hb : 0 ≤ (∑ j, |t j|) * c := mul_nonneg ht0 hc
    have hseed : ∀ y, normW N (paramSec S.s t y) ≤ (∑ j, |t j|) * c := fun y => by
      refine (normW_paramSec_le hN.isAuxNorm (fun j => (S.isScPlusSection j).1) t
        (fun j => (S.isScPlusSection j).mem_oneSet y)).trans ?_
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hsN j y) (abs_nonneg _)
    refine ((S.atom t).pointwiseNorm_mult_le hN hb (fun i y _ =>
      SymmetricFamily.ofSeed_normW_le S.mapsTo_V S.closure_V_subset
        (isScPlusSection_paramSec S.isScPlusSection t)
        (sectionSupport_paramSec_subset (fun j => (S.isScPlusSection j).1) S.support_subset t)
        hN hb hseed i y)
      z).trans ?_
    exact mul_le_mul_of_nonneg_left (hch z (((S.atom t).reach_iff_mem_saturation z).1 hr)) ht0
  · have hz : z ∈ (A.X.saturation (closure S.V))ᶜ := fun hz =>
      hr (((S.atom t).reach_iff_mem_saturation z).2 ((S.atom t).saturation_closure_V_subset hz))
    refine pointwiseNorm_le_of_isLocalRepOn (S.isScPlusMultisection_Λ t) (S.isLocalRepOn_zero t)
      hz fun _ => ?_
    rw [paramSec_fiberZero, normW_fiberZero hN.isAuxNorm]
    exact mul_nonneg ht0 (hh0 z)

/-- **(15.1) on `Q₀ = ⋂_g (U(x) ∩ Φ_g⁻¹ W)`**: if (15.1) holds with the vectors `s_j(y)` at the
points `y ∈ S_f ∩ W`, then GP's `IsParamOntoAt f Λ^x y` holds at the points `y ∈ S_f ∩ Q₀` (the
branch `g` at `y` is `μ(Γ(g, g⁻¹ ∗ y), s_j(g⁻¹ ∗ y))`; `IsParamOntoVec.of_mor`). -/
theorem isParamOntoAt (hf : A.E.IsScFredholmSectionFunctor f) {W : Set A.Obj}
    (hW : ∀ y : A.X.PObj.Level 1, A.X.PObj.levelVal 1 y ∈ W →
      A.X.PObj.levelVal 1 y ∈ solutionSet A.P f →
        IsParamOntoVec f y (fun j => ⟨S.s j (A.X.PObj.levelVal 1 y), (S.isScPlusSection j).1 _⟩))
    (y : A.X.PObj.Level 1) (hyQ : A.X.PObj.levelVal 1 y ∈ ⋂ g, S.R.U ∩ S.R.Φ g ⁻¹' W)
    (hyS : A.X.PObj.levelVal 1 y ∈ solutionSet A.P f) : IsParamOntoAt f S.Λ y := by
  have hyU : A.X.PObj.levelVal 1 y ∈ S.R.U := (mem_iInter.1 hyQ 1).1
  refine isParamOntoAt_iff_vec.2 ⟨S.R.U, _, S.branch, _, S.isSection_branch, S.R.isOpen_U, hyU,
    S.isLocalRepOn_branch, fun i => ?_⟩
  set k := (@Fintype.equivFin (A.X.Isotropy S.x) (Fintype.ofFinite _)).symm i
  set m := S.R.Γ k (S.R.Φ k⁻¹ (A.X.PObj.levelVal 1 y))
  have hsrc : A.X.src m = S.R.Φ k⁻¹ (A.X.PObj.levelVal 1 y) :=
    S.R.src_Γ k _ (S.R.mapsTo_Φ k⁻¹ hyU)
  have htgt : A.X.tgt m = A.X.PObj.levelVal 1 y :=
    EpStrongBundle.tgt_Γ_Φ_inv S.R k hyU
  have h1 := src_mem_levelSet_one (z := y) htgt.symm
  have hmS : A.X.src m ∈ solutionSet A.P f := by
    have := mem_solutionSet_tgt hf (A.X.inv m) (by rw [A.X.src_inv, htgt]; exact hyS)
    rwa [A.X.tgt_inv] at this
  have hmW : A.X.src m ∈ W := by rw [hsrc]; exact (mem_iInter.1 hyQ k⁻¹).2
  have H := hW (A.X.PObj.levelMk 1 (A.X.src m) h1) (by rwa [A.X.PObj.levelVal_levelMk])
    (by rwa [A.X.PObj.levelVal_levelMk])
  have H' := IsParamOntoVec.of_mor hf m (A.X.PObj.levelVal_levelMk _ _ _) htgt.symm H
  have hv : (fun j => (⟨S.branch i j (A.X.PObj.levelVal 1 y), S.isSection_branch i j _⟩ :
      A.P ⁻¹' {A.X.PObj.levelVal 1 y})) = fun j =>
        muLin m (A.X.PObj.levelVal_levelMk _ _ _).symm htgt
          ⟨S.s j (A.X.PObj.levelVal 1 (A.X.PObj.levelMk 1 (A.X.src m) h1)),
            (S.isScPlusSection j).1 _⟩ := by
    funext j
    refine Subtype.ext ?_
    change EpStrongBundle.natTerm A.E S.R (S.isScPlusSection j).1 k (A.X.PObj.levelVal 1 y) = _
    rw [EpStrongBundle.natTerm_of_mem (E := A.E) S.R _ k hyU, muLin_apply]
    rfl
  rw [hv]
  exact H'

/-- **The family of the proof on `Q₀`** (GP's `GPFamily`). -/
def gpFamily (h𝒰 : Nonempty A.X.GoodSystem) (hf : A.E.IsScFredholmSectionFunctor f)
    (hN : A.E.IsAuxNorm N) {c : ℝ} (hc : 0 ≤ c) (hsN : ∀ j y, normW N (S.s j y) ≤ c)
    (hch : ∀ y ∈ A.X.saturation S.R.U, c ≤ h y) (hh0 : ∀ y, 0 ≤ h y)
    (hUsat : A.X.saturation S.R.U ⊆ U) {W : Set A.Obj}
    (hW : ∀ y : A.X.PObj.Level 1, A.X.PObj.levelVal 1 y ∈ W →
      A.X.PObj.levelVal 1 y ∈ solutionSet A.P f →
        IsParamOntoVec f y (fun j => ⟨S.s j (A.X.PObj.levelVal 1 y), (S.isScPlusSection j).1 _⟩)) :
    GPFamily A f N U h (⋂ g, S.R.U ∩ S.R.Φ g ⁻¹' W) where
  ℓ := S.ℓ
  Λ := S.Λ
  isStructurable := S.isStructurable_Λ h𝒰
  isLinear := S.isLinearFamily
  norm_le := S.norm_le hN hc hsN hch hh0
  domSupp_subset t := (S.domSupp_Λ_subset t).trans hUsat
  paramOnto := S.isParamOntoAt hf hW

end SeedData

/-! ### The analytic input and `HasLocalGPFamilies` -/

variable (A) in
/-- **The analytic input of the local constructions** (proof of Theorem 15.3.7, pp. 694–696),
stated on the object M-polyfold: at every `x ∈ S_f`, inside every open `O ∋ x` and below every
`ε > 0` there are finitely many sc⁺-sections `s_j` of `W → X` supported in `O` with
`N(s_j) ≤ ε`, and an open `W ∋ x` such that (15.1) holds with the vectors `s_j(y)` at every
`y ∈ S_f ∩ W` (`f'(y)(T^R_yX) + span{s_j(y)} = W_y`). -/
def HasLocalParamSeeds (f : A.Obj → A.W) (N : A.B.One → ℝ) : Prop :=
  ∀ x ∈ solutionSet A.P f, ∀ O : Set A.Obj, IsOpen O → x ∈ O → ∀ ε > 0,
    ∃ (ℓ : ℕ) (s : Fin ℓ → A.Obj → A.W) (hs : ∀ j, A.B.IsScPlusSection (s j)),
      (∀ j, sectionSupport A.P (s j) ⊆ O) ∧ (∀ j y, normW N (s j y) ≤ ε) ∧
      ∃ W : Set A.Obj, IsOpen W ∧ x ∈ W ∧ ∀ y : A.X.PObj.Level 1,
        A.X.PObj.levelVal 1 y ∈ W → A.X.PObj.levelVal 1 y ∈ solutionSet A.P f →
          IsParamOntoVec f y (fun j => ⟨s j (A.X.PObj.levelVal 1 y), (hs j).1 _⟩)

/-- **GP's `HasLocalGPFamilies` from the analytic input** (the local constructions of the proof of
Theorem 15.3.7): for a good system, an sc-Fredholm section functor `f`, `(N, U)` controlling
compactness and `h` continuous, positive and constant along morphisms. -/
theorem hasLocalGPFamilies_of_seeds (h𝒰 : Nonempty A.X.GoodSystem)
    (hf : A.E.IsScFredholmSectionFunctor f) (hcc : ControlsCompactness A f N U)
    (hhc : Continuous h) (hhφ : ∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) (hh : ∀ x, 0 < h x)
    (H : HasLocalParamSeeds A f N) : HasLocalGPFamilies A f N U h := by
  refine hasLocalGPFamilies_of_nhds hf fun x hx => ?_
  have hc : 0 < h x / 2 := half_pos (hh x)
  set W₁ : Set A.Obj := U ∩ {y | h x / 2 < h y}
  have hW₁ : IsOpen W₁ := hcc.2.1.inter (isOpen_lt continuous_const hhc)
  have hxW₁ : x ∈ W₁ := ⟨hcc.2.2.2.1 hx, half_lt_self (hh x)⟩
  obtain ⟨R, V, hprop, hRU, hVo, hxV, hVinv, hVcl⟩ := exists_atomicNbhd x hW₁ hxW₁
  obtain ⟨ℓ, s, hs, hsV, hsN, W, hWo, hxW, hW⟩ := H x hx V hVo hxV (h x / 2) hc
  let S : SeedData A := ⟨x, R, hprop, V, hVo, hxV, hVinv, hVcl, ℓ, s, hs, hsV⟩
  have hch : ∀ y ∈ A.X.saturation S.R.U, h x / 2 ≤ h y := by
    rintro y ⟨a, haU, hay⟩
    rw [← EpGroupoid.eq_of_π_eq (X := A.X) hhφ hay]
    exact (hRU haU).2.le
  have hUsat : A.X.saturation S.R.U ⊆ U :=
    EpGroupoid.saturation_subset_of_isSaturated (X := A.X) hcc.2.2.1 (hRU.trans inter_subset_left)
  refine ⟨⋂ g, S.R.U ∩ S.R.Φ g ⁻¹' W, isOpen_iInter_of_finite fun g =>
    (S.R.continuousOn_Φ g).isOpen_inter_preimage S.R.isOpen_U hWo,
    mem_iInter.2 fun g => ⟨S.R.mem_U, by rw [mem_preimage, S.R.Φ_self]; exact hxW⟩,
    ⟨S.gpFamily h𝒰 hf hcc.1 hc.le hsN hch (fun y => (hh y).le) hUsat hW⟩⟩

/-! ### Theorem 15.3.7 -/

/-- **Theorem 15.3.7 (General Position; 2017: Theorem 15.4), pp. 693–698, existence part**, from
a good system, the analytic input of the local constructions (`HasLocalParamSeeds`, on the object
M-polyfold) and GP's parametric transversality step (`HasParametricGeneralPosition`): there is a
structurable sc⁺-multisection functor `Λ` with (1) `N(Λ) < h`, (2) `dom-supp(Λ) ⊆ U`, (3)
`(f, Λ)` transversal, (4) in general position. -/
theorem theorem_15_3_7_hyp_seeds (h𝒰 : Nonempty A.X.GoodSystem)
    (hf : A.E.IsScFredholmSectionFunctor f) (hS : A.E.HasCompactSolutionSetEp f)
    (hcc : ControlsCompactness A f N U) (hhc : Continuous h)
    (hhφ : ∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) (hh : ∀ x, 0 < h x ∧ h x ≤ 1)
    (hseed : HasLocalParamSeeds A f N) (hsard : HasParametricGeneralPosition A f N U) :
    ∃ Λ : A.W → ℚ≥0, IsStructurable A Λ ∧ (∀ x, pointwiseNorm N Λ x < h x) ∧
      domSupp Λ ⊆ U ∧ IsTransversal f Λ ∧ IsInGeneralPosition A f Λ :=
  theorem_15_3_7_hyp h𝒰 hf hS hcc hh
    (hasLocalGPFamilies_of_seeds h𝒰 hf hcc hhc hhφ (fun x => (hh x).1) hseed) hsard

/-- **Theorem 15.3.7 as stated (`theorem_15_3_7_statement`)** from a good system and, under the
hypotheses of the theorem, `HasLocalParamSeeds` and `HasParametricGeneralPosition` (GP's
`HasLocalGPFamilies` is discharged by `hasLocalGPFamilies_of_seeds`). -/
theorem theorem_15_3_7_of_seeds (h𝒰 : Nonempty A.X.GoodSystem)
    (H : A.X.IsTame → A.X.AdmitsBumpFunctionsPointwise →
      ∀ f : A.Obj → A.W, A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
        A.E.HasCompactSolutionSetEp f →
        ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
          HasLocalParamSeeds A f N ∧ HasParametricGeneralPosition A f N U) :
    theorem_15_3_7_statement A :=
  theorem_15_3_7_of_hyp h𝒰 fun htame hbump f hf hft hS N U hcc _h hhc hhφ hh =>
    ⟨hasLocalGPFamilies_of_seeds h𝒰 hf hcc hhc hhφ (fun x => (hh x).1)
      (H htame hbump f hf hft hS N U hcc).1, (H htame hbump f hf hft hS N U hcc).2⟩

/-! ### Satisfiability on `ℝⁿ × ℝ⁰ → ℝⁿ` -/

/-- **`HasLocalParamSeeds` is satisfiable**: on `ℝⁿ × ℝ⁰ → ℝⁿ` (fibres `0`), for every `f` and
`N`, with no seeds (`ℓ = 0`) and `W = ℝⁿ`. -/
theorem hasLocalParamSeeds_epSEP_zero (n : ℕ)
    (f : (StrongBundleEquivalenceExamples.epSEP n 0).Obj →
      (StrongBundleEquivalenceExamples.epSEP n 0).W)
    (N : (StrongBundleEquivalenceExamples.epSEP n 0).B.One → ℝ) :
    HasLocalParamSeeds (StrongBundleEquivalenceExamples.epSEP n 0) f N := by
  intro x _ O _ _ ε hε
  refine ⟨0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, univ,
    isOpen_univ, mem_univ x, fun y _ _ L _ φ hφ hy m V T _ w =>
      ⟨0, zero_mem _, fun j => j.elim0, fiber_eq_epSEP_zero n _ _⟩⟩

/-- **The hypotheses of `theorem_15_3_7_of_seeds` hold together** on `ℝⁿ × ℝ⁰ → ℝⁿ`. -/
theorem theorem_15_3_7_statement_epSEP_zero_of_seeds (n : ℕ) :
    theorem_15_3_7_statement (StrongBundleEquivalenceExamples.epSEP n 0) :=
  theorem_15_3_7_of_seeds (nonempty_goodSystem_epSEP_zero n)
    fun _ _ f _ _ _ N U _ =>
      ⟨hasLocalParamSeeds_epSEP_zero n f N, hasParametricGeneralPosition_epSEP_zero n f N U⟩

end SBLocalization

end Polyfold
