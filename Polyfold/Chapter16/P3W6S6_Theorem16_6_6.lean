import Polyfold.Chapter16.P3W6S6_PerturbedSuborbifold

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.6, p. 739: **Theorem 16.6.6** (2017: Theorem 16.8), the integrals over `λ ∘ f` and their
independence of `λ`.  Numbers and pages are the 2021 text's.

## The text, paraphrased

(T16.6.6) Let `p : Y → Z` be a strong polyfold bundle with `∂Z = ∅`, `f` an oriented sc-Fredholm
section with compact solution set and index `k`, `(n, U)` controlling compactness.  For an
sc⁺-multisection `λ` controlled by `(n, U)` with `(f, λ)` in general position, the branched
integrals `∫_θ̂ τ`, `∮_θ̂ τ` of a closed sc-differential `k`-form `τ` on `Z` are well defined,
independent of `λ`, and depend only on `[τ]`; `θ̂` is `θ = λ ∘ f` with the orientation inherited
from `f` (Theorem 15.4.1, Definition 15.4.2).

## What is formalized

Polyfold level (namespace `Polyfold.PolyfoldClass`), for a polyfold `(Z, c)`:
* `OrientedRep.integral_add`, `OrientedSuborbifold.integral_add`: `∫_θ̂` is additive.
* **`OrientedRep.integral_d_eq_zero_of_boundary`**, **`OrientedSuborbifold.integral_d_eq_zero`**,
  `integral_add_d`: for `∂Z = ∅` (and partitions of unity, the hypothesis of Stokes, Theorem
  16.4.6 / 9.5.17), `∫_θ̂ dη = 0` for every tame compact oriented `θ̂`, in every dimension `≥ 1`,
  so `∫_θ̂ τ` depends only on `[τ]`; the same for `∮_θ̂` (`integralEff_d_eq_zero`).
* `CompactOrientedSuborbifold c m` (tame compact oriented, dimension `m + 1`), `.integral`,
  `.integralEff`, `integral_mk_rep` (in every model it is the ep-groupoid integral of
  Definition 9.5.6, so ep-level results such as TX's transfer); `HasCobordism P₀ P₁` (the
  cobordism of the proof of Corollary 15.4.4: a compact oriented tame `Θ̃` of dimension `m + 2`
  over an ep-groupoid `Y → X` of a model, with
  `∫_{∂Θ̃} F^*ω = ∫_{P₁} ω − ∫_{P₀} ω`); **`integral_eq_of_hasCobordism`** (closed forms have equal
  integrals, TX's `integral_eq_of_cobordism`); `hasCobordism_refl` (satisfiability); the effective
  forms `HasCobordismEff` (with (LUC) on `Y`), `integralEff_eq_of_hasCobordismEff` (Theorem 9.5.18
  on `Y`), `hasCobordismEff_refl`.

Polyfold bundle level (namespace `Polyfold.StrongPolyfoldBundle`):
* `OrientedPerturbation s m`: a tame compact oriented branched suborbifold of `Z` of dimension
  `m + 1` whose function is `λ ∘ f` for an sc⁺-multisection `λ` (`IsPerturbedSuborbifold`);
  `IsAdmissible n U` (`λ` controlled by `(n, U)`, `(f, λ)` in general position).
* **`theorem_16_6_6_statement`**: the text's statement, with the inherited orientation as a
  predicate `IsInherited o P` ("`θ̂` has the orientation inherited from `(f, o)`", Theorem
  15.4.1, not formalized): over the admissible perturbations with the inherited orientation,
  (i) `∫_θ̂ (τ + dη) = ∫_θ̂ τ` and `∮_θ̂ (τ + dη) = ∮_θ̂ τ`, (ii) closed `τ` have the same `∫` and
  the same `∮` over any two of them.  The well-definedness of each integral (independence of the
  representative and of the model) is `OrientedSuborbifold.integral_eq` (every representative
  computes it).
* **`theorem_16_6_6_hyp`**: the statement holds, for every `IsInherited`, given (a) partitions of
  unity on `Z` (Theorem 16.4.6's added hypothesis, witness `theorem_16_4_6_hyp_witness`) and
  (b) the cobordisms `HasCobordism`, `HasCobordismEff` between any two admissible perturbations
  with the inherited orientation (the content of Corollary 15.4.4's proof: Corollary 15.3.10 (3) on
  `[0, 1] × X` and `∂Θ̃ = Θ₁ ⊔ −Θ₀`; TX-6).  Nonvacuity of (b):
  `theorem_16_6_6_hyp_hcob_witness` (`hasCobordism_refl`, `hasCobordismEff_refl`).

## What still rests on other work

* The predicate `IsInherited` is Theorem 15.4.1 / Definition 15.4.2 (G.159, the canonical
  orientation of `λ ∘ f` from `(f, o)`), with PB-4 (transport of `o` between models).
* The cobordism hypothesis is Corollary 15.4.4's cobordism (TX-6): Corollary 15.3.10 (3) (TX-4,
  TX-5, T15.3.9), Theorem 15.4.1 on `[0, 1] × X`, and the identification of the boundary
  measure of `Θ̃` with `∫_{Θ₁} − ∫_{Θ₀}`.
* The existence of `θ = λ ∘ f` as a compact branched suborbifold is
  `exists_isPerturbedSuborbifold_hyp` (inherited tame germ data, G.140).
* No concrete strong polyfold bundle with a nonempty admissible oriented perturbation is built
  here; the statement is nonvacuous only through the cobordism witnesses (weak).

## Reading

* The index `k` is the dimension of `θ̂`; it is `m + 1 ≥ 1` here (Theorem 16.4.6 and the integrals
  of §16.4 are stated for dimension `≥ 1`).  That the dimension of `θ̂` is the Fredholm index is
  part of Theorem 15.4.1.
* "Independent of the perturbation `λ`": equal integrals for closed `τ` over any two admissible
  perturbations with the inherited orientation (as in Corollary 15.4.4's statement in TX).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter CategoryTheory MeasureTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization EPLocalization.EPLoc EpGroupoid MPolyfold

namespace PolyfoldClass

variable {Z : Type u} [TopologicalSpace Z] {c : PolyfoldClass Z}

/-- The representative of a sum is the sum of the representatives. -/
theorem ScForm.toStructure_add {k : ℕ} (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c)
    (τ σ : ScForm c k) :
    ScForm.toStructure q hq (τ + σ) = ScForm.toStructure q hq τ + ScForm.toStructure q hq σ :=
  (ScForm.toStructureₗ q hq).map_add τ σ

theorem ScForm.toStructure_zero {k : ℕ} (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c) :
    ScForm.toStructure q hq (0 : ScForm c k) = 0 :=
  (ScForm.toStructureₗ q hq).map_zero

/-- For `∂Z = ∅`, no object of a model lies in `∂X`. -/
theorem not_mem_boundary_of_eq_empty (hbd : c.boundary = ∅) (q : PolyfoldStructure Z)
    (hq : ⟦q⟧ = c) (x : q.X.Obj) : x ∉ q.X.X.PObj.boundary := fun hx => by
  have := (c.mem_boundary_iff q hq rfl).2 hx
  rw [hbd] at this
  exact this

namespace OrientedRep

variable {n m : ℕ}

/-- **`∫_θ̂` is additive** on a representative. -/
theorem integral_add (a : OrientedRep c) (hn : 0 < n) (hcpt : a.p.X.X.IsCompactBranched a.A.Θ)
    (hloc : a.IsTameOriented n) (τ σ : ScForm c n) :
    a.integral hn hcpt hloc (τ + σ) = a.integral hn hcpt hloc τ + a.integral hn hcpt hloc σ := by
  unfold integral
  rw [ScForm.toStructure_add]
  simp only [FormEval.tameBranchedIntegral, FormEval.concreteBranchedIntegral, branchedIntegral,
    map_add, FunLike.coe_add, Pi.add_apply]

/-- **`∮_θ̂` is additive** on a representative. -/
theorem integralEff_add (a : OrientedRep c) (hn : 0 < n)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented n) (τ σ : ScForm c n) :
    a.integralEff hn hcpt hloc (τ + σ) =
      a.integralEff hn hcpt hloc τ + a.integralEff hn hcpt hloc σ := by
  unfold integralEff
  rw [ScForm.toStructure_add]
  simp only [FormEval.tameBranchedIntegralEff, FormEval.concreteBranchedIntegralEff,
    branchedIntegralEff, map_add, FunLike.coe_add, Pi.add_apply]

/-- **`∫_θ̂ dη = 0` when `∂Z = ∅`** (Theorem 16.6.6, "only depends on `[τ]`"): Stokes (Theorem
16.4.6) and `∂Θ = 0`, for a tame compact oriented representative of dimension `m + 1 ≥ 1`, with
partitions of unity on `Z` (Stokes' hypothesis). -/
theorem integral_d_eq_zero_of_boundary (hbd : c.boundary = ∅)
    (hPU : c.AdmitsScPartitionsOfUnity) (a : OrientedRep c)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (m + 1))
    (η : ScForm c m) : a.integral (Nat.succ_pos m) hcpt hloc (ScForm.d η) = 0 := by
  have hemp : ∀ x, x ∉ a.p.X.X.PObj.boundary ∩ EpGroupoid.supp a.A.Θ := fun x hx =>
    not_mem_boundary_of_eq_empty hbd a.p a.mem x hx.1
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [theorem_16_4_6_dim1_hyp hPU a hcpt hloc η, boundaryIntegralDim1]
    exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary hemp _
  · rw [theorem_16_4_6_hyp hPU a hm hcpt hloc η, boundaryIntegral]
    exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary hemp _

/-- **`∮_θ̂ dη = 0` when `∂Z = ∅`** (the effective integral, Theorem 16.4.6). -/
theorem integralEff_d_eq_zero_of_boundary (hbd : c.boundary = ∅)
    (hPU : c.AdmitsScPartitionsOfUnity) (a : OrientedRep c)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (m + 1))
    (η : ScForm c m) : a.integralEff (Nat.succ_pos m) hcpt hloc (ScForm.d η) = 0 := by
  have hemp : ∀ x, x ∉ a.p.X.X.PObj.boundary ∩ EpGroupoid.supp a.A.Θ := fun x hx =>
    not_mem_boundary_of_eq_empty hbd a.p a.mem x hx.1
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [theorem_16_4_6_eff_dim1_hyp hPU a hcpt hloc η, boundaryIntegralEffDim1]
    exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary hemp _
  · rw [theorem_16_4_6_eff_hyp hPU a hm hcpt hloc η, boundaryIntegralEff]
    exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary hemp _

end OrientedRep

namespace OrientedSuborbifold

variable {n m : ℕ}

theorem integral_add (θ : OrientedSuborbifold c) (hn : 0 < n) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented n) (τ σ : ScForm c n) :
    θ.integral hn hcpt htame (τ + σ) = θ.integral hn hcpt htame τ + θ.integral hn hcpt htame σ :=
  OrientedRep.integral_add _ _ _ _ τ σ

theorem integralEff_add (θ : OrientedSuborbifold c) (hn : 0 < n) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented n) (τ σ : ScForm c n) :
    θ.integralEff hn hcpt htame (τ + σ) =
      θ.integralEff hn hcpt htame τ + θ.integralEff hn hcpt htame σ :=
  OrientedRep.integralEff_add _ _ _ _ τ σ

/-- **`∫_θ̂ dη = 0` for `∂Z = ∅`** (partitions of unity on `Z`). -/
theorem integral_d_eq_zero (hbd : c.boundary = ∅) (hPU : c.AdmitsScPartitionsOfUnity)
    (θ : OrientedSuborbifold c) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented (m + 1)) (η : ScForm c m) :
    θ.integral (Nat.succ_pos m) hcpt htame (ScForm.d η) = 0 :=
  OrientedRep.integral_d_eq_zero_of_boundary hbd hPU _ _ _ η

/-- **`∮_θ̂ dη = 0` for `∂Z = ∅`** (partitions of unity on `Z`). -/
theorem integralEff_d_eq_zero (hbd : c.boundary = ∅) (hPU : c.AdmitsScPartitionsOfUnity)
    (θ : OrientedSuborbifold c) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented (m + 1)) (η : ScForm c m) :
    θ.integralEff (Nat.succ_pos m) hcpt htame (ScForm.d η) = 0 :=
  OrientedRep.integralEff_d_eq_zero_of_boundary hbd hPU _ _ _ η

/-- **`∫_θ̂ τ` depends only on `[τ]`** (`∂Z = ∅`). -/
theorem integral_add_d (hbd : c.boundary = ∅) (hPU : c.AdmitsScPartitionsOfUnity)
    (θ : OrientedSuborbifold c) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented (m + 1)) (τ : ScForm c (m + 1)) (η : ScForm c m) :
    θ.integral (Nat.succ_pos m) hcpt htame (τ + ScForm.d η) =
      θ.integral (Nat.succ_pos m) hcpt htame τ := by
  rw [integral_add, integral_d_eq_zero hbd hPU, add_zero]

/-- **`∮_θ̂ τ` depends only on `[τ]`** (`∂Z = ∅`). -/
theorem integralEff_add_d (hbd : c.boundary = ∅) (hPU : c.AdmitsScPartitionsOfUnity)
    (θ : OrientedSuborbifold c) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented (m + 1)) (τ : ScForm c (m + 1)) (η : ScForm c m) :
    θ.integralEff (Nat.succ_pos m) hcpt htame (τ + ScForm.d η) =
      θ.integralEff (Nat.succ_pos m) hcpt htame τ := by
  rw [integralEff_add, integralEff_d_eq_zero hbd hPU, add_zero]

end OrientedSuborbifold

/-- A **tame compact oriented branched suborbifold of dimension `m + 1`** of `(Z, c)`
(Definitions 16.4.2, 16.4.4; the objects integrated over in §16.4). -/
structure CompactOrientedSuborbifold (c : PolyfoldClass Z) (m : ℕ) : Type (u + 1) where
  /-- The oriented branched suborbifold `θ̂`. -/
  θ : OrientedSuborbifold c
  isCompact : θ.toBranched.IsCompact
  isTame : θ.IsTameOriented (m + 1)

namespace CompactOrientedSuborbifold

variable {m : ℕ}

/-- `∫_θ̂ τ` (2021 p. 732). -/
def integral (P : CompactOrientedSuborbifold c m) (τ : ScForm c (m + 1)) : ℝ :=
  P.θ.integral (Nat.succ_pos m) P.isCompact P.isTame τ

/-- `∮_θ̂ τ` (2021 p. 732). -/
def integralEff (P : CompactOrientedSuborbifold c m) (τ : ScForm c (m + 1)) : ℝ :=
  P.θ.integralEff (Nat.succ_pos m) P.isCompact P.isTame τ

/-- **The polyfold integral is the ep-groupoid integral in every model** (2021 p. 732): for a
representative `((Θ, T̂), (X, α))` of `θ̂` and `ω ∈ Ω^{m+1}_{ep,∞}(X)`,
`∫_θ̂ [(ω, (X, α))] = ∫_{(Θ, T̂)} ω` (Definition 9.5.6). -/
theorem integral_mk_rep (P : CompactOrientedSuborbifold c m) (a : OrientedRep c) (ha : ⟦a⟧ = P.θ)
    (ω : a.p.X.epFormsInfty (m + 1)) :
    P.integral (ScForm.mk a.p a.mem ω) =
      (a.p.X.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m)
        a.A.isBranchedEpSubgroupoid (OrientedSuborbifold.isCompactBranched_of_mk P.isCompact a ha)
        a.A.isOrientation ((OrientedSuborbifold.isTameOriented_iff P.θ).1 P.isTame a ha) ω := by
  rw [integral, OrientedSuborbifold.integral_eq P.θ _ P.isCompact P.isTame _ a ha,
    OrientedRep.integral, ScForm.toStructure_mk]

/-- `P₀` and `P₁` are joined by an **oriented compact cobordism** (the proof of Corollary 15.4.4,
in a model `(X, β) ∈ c`): an ep-groupoid `Y` with partitions of unity, an sc-smooth functor
`F : Y → X` (in the text the projection `[0, 1] × X → X`) and a compact branched `Θ̃` on `Y`,
oriented and tame of dimension `m + 2`, with `∫_{∂Θ̃} F^*ω = ∫_{P₁} [ω] − ∫_{P₀} [ω]` for every
`ω ∈ Ω^{m+1}_{ep,∞}(X)`. -/
def HasCobordism (P₀ P₁ : CompactOrientedSuborbifold c m) : Prop :=
  ∃ (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c) (Y : EP.{u}) (F : EpFunctor Y.X q.X.X)
    (_ : Y.X.HasScPartitionsOfUnity) (Θ' : Y.Obj → ℚ) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ)
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T'),
    ∀ ω, Y.boundaryMeasure (Nat.succ_pos m) hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F (m + 1) ω) univ =
        P₁.integral (ScForm.mk q hq ω) - P₀.integral (ScForm.mk q hq ω)

/-- **Cobordant perturbations have the same integrals of closed forms** (Corollary 15.4.4's
argument, on the polyfold): Stokes on `Y` and `d F^* = F^* d` (TX's
`integral_eq_of_cobordism`), read in the model of the cobordism. -/
theorem integral_eq_of_hasCobordism {P₀ P₁ : CompactOrientedSuborbifold c m}
    (h : HasCobordism P₀ P₁) (τ : ScForm c (m + 1)) (hτ : ScForm.d τ = 0) :
    P₀.integral τ = P₁.integral τ := by
  obtain ⟨q, hq, Y, F, hPUY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  have hω : q.X.epFormsInftyD (m + 1) (ScForm.toStructure q hq τ) = 0 := by
    rw [← ScForm.toStructure_dFun, ← ScForm.d_apply, hτ, ScForm.toStructure_zero]
  have := SBLocalization.integral_eq_of_cobordism F hPUY hΘ' hcpt' hT' hloc'
    (fun ω => P₀.integral (ScForm.mk q hq ω)) (fun ω => P₁.integral (ScForm.mk q hq ω)) hbd
    (ScForm.toStructure q hq τ) hω
  simpa only [ScForm.mk_toStructure] using this

/-- **The cobordism hypothesis is satisfiable**: every `P` is cobordant to itself (`Y = X`,
`F = id`, `Θ̃ = 0`), when `c` admits sc-smooth partitions of unity. -/
theorem hasCobordism_refl (hPU : c.AdmitsScPartitionsOfUnity)
    (P : CompactOrientedSuborbifold c m) : HasCobordism P P := by
  set q := c.out
  have hq : (⟦q⟧ : PolyfoldClass Z) = c := Quotient.out_eq c
  have hPUq := (c.definition_16_1_5_two).1 hPU q hq
  have hemp : ∀ x, x ∉ q.X.X.PObj.boundary ∩ EpGroupoid.supp (0 : q.X.Obj → ℚ) := fun x hx =>
    lt_irrefl (0 : ℚ) hx.2
  have hcpt0 : q.X.X.IsCompactBranched (0 : q.X.Obj → ℚ) := by
    have : q.X.X.orbitSupp (0 : q.X.Obj → ℚ) = ∅ := by
      rw [orbitSupp, image_eq_empty, eq_empty_iff_forall_notMem]
      exact fun x hx => lt_irrefl (0 : ℚ) hx
    rw [IsCompactBranched, this]; exact isCompact_empty
  have hloc0 : ∀ x ∈ EpGroupoid.supp (0 : q.X.Obj → ℚ),
      ∃ C : q.X.X.OrientedTameStructure (m + 1 + 1) 0 x, C.Represents fun _ => 0 :=
    fun x hx => absurd hx (lt_irrefl (0 : ℚ))
  refine ⟨q, hq, q.X, EpFunctor.id _, hPUq, 0, fun _ => 0, q.X.X.isBranchedEpSubgroupoid_zero,
    hcpt0, q.X.X.isOrientation_zero, hloc0, fun ω => ?_⟩
  rw [sub_self]
  exact SBLocalization.boundaryMeasure_univ_eq_zero (B := q.X) (Nat.succ_pos m)
    q.X.X.isBranchedEpSubgroupoid_zero hcpt0 q.X.X.isOrientation_zero hloc0 hemp _

/-- The effective analogue of `HasCobordism` (for `∮`): the cobordism's ep-groupoid `Y` has
(LUC), and `∮_{∂Θ̃} F^*ω = ∮_{P₁} [ω] − ∮_{P₀} [ω]`. -/
def HasCobordismEff (P₀ P₁ : CompactOrientedSuborbifold c m) : Prop :=
  ∃ (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c) (Y : EP.{u}) (F : EpFunctor Y.X q.X.X)
    (_ : Y.X.HasScPartitionsOfUnity) (hLUC : Y.X.IsLUC) (Θ' : Y.Obj → ℚ)
    (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ)
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T'),
    ∀ ω, Y.boundaryMeasureEff (Nat.succ_pos m) hLUC hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F (m + 1) ω) univ =
        P₁.integralEff (ScForm.mk q hq ω) - P₀.integralEff (ScForm.mk q hq ω)

/-- **Cobordant perturbations have the same effective integrals of closed forms** (Corollary
15.4.4's argument with Theorem 9.5.18 on `Y`). -/
theorem integralEff_eq_of_hasCobordismEff {P₀ P₁ : CompactOrientedSuborbifold c m}
    (h : HasCobordismEff P₀ P₁) (τ : ScForm c (m + 1)) (hτ : ScForm.d τ = 0) :
    P₀.integralEff τ = P₁.integralEff τ := by
  obtain ⟨q, hq, Y, F, hPUY, hLUC, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  have hω : q.X.epFormsInftyD (m + 1) (ScForm.toStructure q hq τ) = 0 := by
    rw [← ScForm.toStructure_dFun, ← ScForm.d_apply, hτ, ScForm.toStructure_zero]
  set ω := ScForm.toStructure q hq τ
  have hS := Y.theorem_9_5_18 (Nat.succ_pos m) hPUY hLUC hΘ' hcpt' hT' hloc'
    (EP.epFormsInftyPullback F (m + 1) ω)
  have hd : Y.epFormsInftyD (m + 1) (EP.epFormsInftyPullback F (m + 1) ω) = 0 := by
    have := LinearMap.congr_fun (EP.epFormsInftyD_comp_epFormsInftyPullback F (m + 1)) ω
    simp only [LinearMap.comp_apply] at this
    rw [this, hω, map_zero]
  have h0 : (Y.epFormsInftyEval (m + 1 + 1)).tameBranchedIntegralEff (Nat.succ_pos (m + 1)) hΘ'
      hcpt' hT' (Y.hloc_hasLUC hLUC hloc') 0 = 0 := by
    simp only [FormEval.tameBranchedIntegralEff, FormEval.concreteBranchedIntegralEff,
      branchedIntegralEff, map_zero]
    rfl
  rw [hd, h0, hbd, ScForm.mk_toStructure] at hS
  linarith

/-- **The effective cobordism hypothesis is satisfiable**: every `P` is cobordant to itself
(`Y = X`, which has (LUC) by (ZHOU)). -/
theorem hasCobordismEff_refl (hPU : c.AdmitsScPartitionsOfUnity)
    (P : CompactOrientedSuborbifold c m) : HasCobordismEff P P := by
  set q := c.out
  have hq : (⟦q⟧ : PolyfoldClass Z) = c := Quotient.out_eq c
  have hPUq := (c.definition_16_1_5_two).1 hPU q hq
  have hemp : ∀ x, x ∉ q.X.X.PObj.boundary ∩ EpGroupoid.supp (0 : q.X.Obj → ℚ) := fun x hx =>
    lt_irrefl (0 : ℚ) hx.2
  have hcpt0 : q.X.X.IsCompactBranched (0 : q.X.Obj → ℚ) := by
    have : q.X.X.orbitSupp (0 : q.X.Obj → ℚ) = ∅ := by
      rw [orbitSupp, image_eq_empty, eq_empty_iff_forall_notMem]
      exact fun x hx => lt_irrefl (0 : ℚ) hx
    rw [IsCompactBranched, this]; exact isCompact_empty
  have hloc0 : ∀ x ∈ EpGroupoid.supp (0 : q.X.Obj → ℚ),
      ∃ C : q.X.X.OrientedTameStructure (m + 1 + 1) 0 x, C.Represents fun _ => 0 :=
    fun x hx => absurd hx (lt_irrefl (0 : ℚ))
  refine ⟨q, hq, q.X, EpFunctor.id _, hPUq, q.X.X.proposition_7_4_10_of_isZhou q.isZhou, 0,
    fun _ => 0, q.X.X.isBranchedEpSubgroupoid_zero, hcpt0, q.X.X.isOrientation_zero, hloc0,
    fun ω => ?_⟩
  rw [sub_self]
  exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary hemp _

end CompactOrientedSuborbifold

end PolyfoldClass

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- An **oriented perturbed solution set of dimension `m + 1`** of `f` (2021 p. 739): a tame
compact oriented branched suborbifold `θ̂` of `Z` whose function is `λ ∘ f` for an
sc⁺-multisection `λ`. -/
structure OrientedPerturbation (s : ScSection c) (m : ℕ) : Type (u + 1) extends
    CompactOrientedSuborbifold c.polyfold m where
  /-- The sc⁺-multisection `λ`. -/
  t : ScPlusMultisection c
  isPerturbed : IsPerturbedSuborbifold s t toCompactOrientedSuborbifold.θ.toBranched

namespace OrientedPerturbation

variable {s : ScSection c} {m : ℕ}

/-- The perturbation is **admissible** in the sense of Theorem 16.6.6: `λ` is controlled by
`(n, U)` and `(f, λ)` is in general position. -/
def IsAdmissible (P : OrientedPerturbation s m) (n : Y → ℝ) (U : Set Z) : Prop :=
  P.t.IsControlledBy n U ∧ s.IsInGeneralPositionWith P.t

end OrientedPerturbation

/-- **2021 Theorem 16.6.6, p. 739 (2017: Theorem 16.8)**, as a proposition, degree-wise in degree
`m + 1` (the dimension of `θ̂`).  `IsInherited o P` is the condition that the orientation of `θ̂`
is the one inherited from the orientation `o` of `f` (Theorem 15.4.1, Definition 15.4.2, not
formalized, so a parameter).  Under the text's hypotheses (`∂Z = ∅`, `f` oriented with compact
solution set, `(n, U)` controlling compactness), over the admissible perturbations with the
inherited orientation: (i) `∫_θ̂ τ` and `∮_θ̂ τ` depend only on `[τ]`, (ii) a closed `τ` has the
same `∫_θ̂ τ` and the same `∮_θ̂ τ` for any two of them (independence of `λ`). -/
def theorem_16_6_6_statement (s : FredholmSection c) (n : Y → ℝ) (U : Set Z) (m : ℕ)
    (IsInherited : OrientationRep s → OrientedPerturbation s.1 m → Prop) : Prop :=
  c.polyfold.boundary = ∅ → s.1.HasCompactSolutionSet → c.IsAuxNorm n → IsOpen U →
    s.1.ControlsCompactness n U → ∀ o : OrientationRep s,
    (∀ P : OrientedPerturbation s.1 m, P.IsAdmissible n U → IsInherited o P →
      ∀ (τ : ScForm c.polyfold (m + 1)) (η : ScForm c.polyfold m),
        P.integral (τ + ScForm.d η) = P.integral τ ∧
          P.integralEff (τ + ScForm.d η) = P.integralEff τ) ∧
    ∀ P₀ P₁ : OrientedPerturbation s.1 m, P₀.IsAdmissible n U → IsInherited o P₀ →
      P₁.IsAdmissible n U → IsInherited o P₁ →
      ∀ τ : ScForm c.polyfold (m + 1), ScForm.d τ = 0 →
        P₀.integral τ = P₁.integral τ ∧ P₀.integralEff τ = P₁.integralEff τ

/-- **2021 Theorem 16.6.6 from the cobordism** (p. 739; 2017: Theorem 16.8): for every
predicate `IsInherited`, the statement holds when `Z` admits sc-smooth partitions of unity
(Theorem 16.4.6's added hypothesis) and any two admissible perturbations with the inherited
orientation are joined by oriented compact cobordisms (`HasCobordism`, `HasCobordismEff`;
Corollary 15.4.4's proof, TX-6).  The parts "depends only on `[τ]`" (for `∫` and `∮`) and the
well-definedness (`OrientedSuborbifold.integral_eq`) use no cobordism. -/
theorem theorem_16_6_6_hyp (hPU : c.polyfold.AdmitsScPartitionsOfUnity) (s : FredholmSection c)
    (n : Y → ℝ) (U : Set Z) (m : ℕ)
    (IsInherited : OrientationRep s → OrientedPerturbation s.1 m → Prop)
    (hcob : ∀ o P₀ P₁, P₀.IsAdmissible n U → IsInherited o P₀ → P₁.IsAdmissible n U →
      IsInherited o P₁ →
      P₀.toCompactOrientedSuborbifold.HasCobordism P₁.toCompactOrientedSuborbifold)
    (hcobEff : ∀ o P₀ P₁, P₀.IsAdmissible n U → IsInherited o P₀ → P₁.IsAdmissible n U →
      IsInherited o P₁ →
      P₀.toCompactOrientedSuborbifold.HasCobordismEff P₁.toCompactOrientedSuborbifold) :
    theorem_16_6_6_statement s n U m IsInherited := by
  intro hbd _ _ _ _ o
  refine ⟨fun P _ _ τ η => ⟨?_, ?_⟩, fun P₀ P₁ h₀ i₀ h₁ i₁ τ hτ => ?_⟩
  · exact OrientedSuborbifold.integral_add_d hbd hPU _ _ _ τ η
  · exact OrientedSuborbifold.integralEff_add_d hbd hPU _ _ _ τ η
  exact ⟨CompactOrientedSuborbifold.integral_eq_of_hasCobordism (hcob o P₀ P₁ h₀ i₀ h₁ i₁) τ hτ,
    CompactOrientedSuborbifold.integralEff_eq_of_hasCobordismEff (hcobEff o P₀ P₁ h₀ i₀ h₁ i₁) τ
      hτ⟩

/-- **The cobordism hypotheses of `theorem_16_6_6_hyp` are satisfiable**: for the predicate that
singles out one perturbation `P` (any orientation `o`), they hold (`hasCobordism_refl`,
`hasCobordismEff_refl`). -/
theorem theorem_16_6_6_hyp_hcob_witness (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    {s : FredholmSection c} {m : ℕ} (P : OrientedPerturbation s.1 m) (n : Y → ℝ) (U : Set Z) :
    ∀ (o : OrientationRep s) (P₀ P₁ : OrientedPerturbation s.1 m), P₀.IsAdmissible n U →
      (fun _ Q => Q = P) o P₀ → P₁.IsAdmissible n U → (fun _ Q => Q = P) o P₁ →
      P₀.toCompactOrientedSuborbifold.HasCobordism P₁.toCompactOrientedSuborbifold ∧
        P₀.toCompactOrientedSuborbifold.HasCobordismEff P₁.toCompactOrientedSuborbifold := by
  rintro o P₀ P₁ - rfl - rfl
  exact ⟨CompactOrientedSuborbifold.hasCobordism_refl hPU _,
    CompactOrientedSuborbifold.hasCobordismEff_refl hPU _⟩

end StrongPolyfoldBundle

end Polyfold
