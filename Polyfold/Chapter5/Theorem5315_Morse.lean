import Polyfold.Chapter5.Theorem5315_MorseTransfer
import Polyfold.Chapter5.Theorem5315_Ends

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.3,
**Theorem 5.3.15** (p. 223; 2017: Theorem 5.8; preprint: Theorem 5.22), conclusion (2): the
globalization of the proof (p. 227).  Gap G.48.

# Theorem 5.3.15 (2): the covering argument

## The text, paraphrased

(Theorem 5.3.15) For a generalized compact homotopy with boundaryless ends in general position
and `∂X = X₀ ⊔ X₁`, there is an arbitrarily small `s₀ ∈ Γ^{+,1}_U(P)` vanishing near `∂X` such
that (1) `(f + s₀, x)` is in general position at every zero and (2) `t : S_{f+s₀} → [0, 1]` has
only Morse-type critical points.  (Proof, pp. 223–228) After (1), `d(t|S)` has no critical points
near `∂S`; at a critical point `x` of `t|S` sections `s₁, …, s_m` are built (Lemmas 5.3.16,
5.3.17) which make `(λ, y) ↦ d(t|S_λ)(y)` transversal to the zero section near `(0, x)`;
finitely many `x` suffice; the union of the sections is taken, and the parametrized Sard theorem
gives a small `λ` with `t|S_λ` a Morse function.

## What is formalized

* `famZero f σ`: the solution set `M ⊆ ℝᵏ × X` of `(μ, y) ↦ f(y) + Σ μ_j σ_j(y)`;
  `isZeroAt_paramSlice_smul_iff`: the zeros of `f + Σ λᵢ aᵢ σ_{g(i)}` (`aᵢ` functions) are the `y`
  with `(Λ(λ, y), y) ∈ M` (`famShift`).  The sections of the text's Lemma 5.3.17 have this form
  `aᵢ σ`, which makes the dependence of `S_λ` on `λ` explicit inside the fixed manifold `M`.
* `MPolyfold.IsRegularPointOn A t x` and the three local hypotheses `HasFamilyParam` (A1),
  `HasRegularFamilyParam` (A2), collected in `StrongBundle.HasMorseLocalData` with (A3).
* `not_isRegularPointOn_of_multiplier`: a Lagrange multiplier of `t` on `M` at `(0, y)` makes
  `y` a critical point of `t|S_f`.
* **`exists_morse_perturbation_hyp`** (the covering argument, p. 227): for `f` in general position
  at every zero, with (A1)–(A3), an arbitrarily small `s₀ ∈ Γ^{+,1}_U(P)` vanishing near `∂X` with
  `(f + s₀, x)` in general position at every zero and `t|S_{f+s₀}` with only Morse-type critical
  points.  The critical set `C ⊆ S` of `t|S` is compact and misses `∂X`; at `x ∈ C` (A2) gives a
  section `σ_x` and a parametrization `(p_x, q_x)` of `M_x = {f + μσ_x = 0}`; the functions are
  `1` and `arctan(q_x(0, ·)ᵢ)/2`; finitely many `U(x)` cover `C`; in the full family every zero
  `y` of `f` has a neighbourhood on which, for almost every small `λ`, the points of `S_λ` are
  regular or Morse-type critical points (`ae_isMorseOrRegularPoint_famSlice`, with
  `exists_spanning_of_group` at the points of `C`, no multiplier at regular interior points, and
  `S_λ = S` near `∂X`); general position for almost every small `λ` is
  `exists_null_isGeneralPositionGerm_paramSlice` (Theorem 5.3.10's mechanism).
* **`theorem_5_3_15_hyp`**: the theorem with both conclusions, under the printed hypotheses
  (`theorem_5_3_15_generalPosition`, file `Theorem5315_Ends.lean`) and the hypothesis that the
  perturbed sections `f + s` have the local data `HasMorseLocalData`.

## Not done in this file

* The local data (A1)–(A3) are not derived here from the implicit function theorem
  (2021 Theorem 3.6.8 for the families, with `T_{(0,y)}M = ker F'(0, y)` in the product chart,
  Lemma 5.3.16 for (A2), and the general position at `∂X` for (A3)); `theorem_5_3_15_hyp` keeps
  them as a hypothesis.  They are derived in `Theorem5315_LocalData.lean`
  (`StrongBundle.hasMorseLocalData`, 2026-11-12), and `theorem_5_3_15` (`Theorem5315_Final.lean`)
  is this theorem without the hypothesis.

## What the text leaves implicit, and the choices made

* The sections are `aᵢ σ` with one `σ` per centre and scalar functions `aᵢ` (the form of the
  section constructed in the proof of Lemma 5.3.17); then no second derivative of `f` is needed:
  `S_λ` is a level set in the solution manifold of `f + μσ`, and (5.13)–(5.14) become classical
  calculus (files `Theorem5315_MorseLagrange.lean`, `Theorem5315_MorseFamily.lean`).
* The functions `aᵢ` are the bounded coordinates `arctan(qᵢ)/2` of the parametrization, and the
  constant `1`; with them the transversality holds at every critical point in a neighbourhood
  `U(x)` given by an explicit open condition, and survives in the union of the families.
-/

open Set Function MeasureTheory Module Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### Sums over a sigma type, extended by zero from one summand -/

section SigmaSum

variable {k : ℕ} {m : Fin k → ℕ}

/-- The extension by zero of a family on the `j`-th summand of `Σ j, Fin (m j + 1)`. -/
def sigmaExtend (j : Fin k) (δ : Fin (m j + 1) → ℝ) (s : Σ j, Fin (m j + 1)) : ℝ :=
  if h : s.1 = j then δ (h ▸ s.2) else 0

lemma sum_sigmaExtend_smul (j : Fin k) (δ : Fin (m j + 1) → ℝ) {V : Type*} [AddCommGroup V]
    [Module ℝ V] (F : (Σ j, Fin (m j + 1)) → V) :
    ∑ s, sigmaExtend j δ s • F s = ∑ i, δ i • F ⟨j, i⟩ := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [sigmaExtend]
  · intro j' _ hj'
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [sigmaExtend, hj']
  · intro h; exact absurd (Finset.mem_univ j) h

end SigmaSum

/-! ### The fibre algebra of the family -/

section FibreAlgebra

variable {X : Type u} {Y : Type v} {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})]
  [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The solution set of the family `(μ, y) ↦ f(y) + Σ μ_j σ_j(y)` in `ℝᵏ × X`. -/
def famZero (f : X → Y) (hf : IsSection P f) {k : ℕ} (σ : Fin k → X → Y)
    (hσ : ∀ j, IsSection P (σ j)) : Set ((Fin k → ℝ) × X) :=
  {z | IsZeroAt P (paramSlice f hf σ hσ z.1) z.2}

variable {f : X → Y} (hf : IsSection P f) {k : ℕ} {σ : Fin k → X → Y}
  (hσ : ∀ j, IsSection P (σ j))

lemma fiberComb_smul_eq {d : ℕ} (a : Fin d → X → ℝ) (g : Fin d → Fin k) (lam : Fin d → ℝ)
    (y : X) :
    fiberComb (fun i => sectionSmul P (a i) (σ (g i))) (fun i => (hσ (g i)).sectionSmul)
        (lam, y) = fiberComb σ hσ (famShift a g lam y, y) := by
  classical
  unfold fiberComb
  have h1 : ∀ i, (⟨sectionSmul P (a i) (σ (g i)) y, (hσ (g i)).sectionSmul y⟩ : P ⁻¹' {y}) =
      a i y • (⟨σ (g i) y, hσ (g i) y⟩ : P ⁻¹' {y}) := fun i =>
    Subtype.ext (sectionSmul_apply (hσ (g i)) y)
  have h2 : ∀ j, famShift a g lam y j = ∑ i, if g i = j then lam i * a i y else 0 := fun j => by
    simp [famShift, Finset.sum_apply, Pi.single_apply, eq_comm]
  change ∑ i, lam i • (⟨sectionSmul P (a i) (σ (g i)) y, (hσ (g i)).sectionSmul y⟩ : P ⁻¹' {y}) =
    ∑ j, famShift a g lam y j • (⟨σ j y, hσ j y⟩ : P ⁻¹' {y})
  simp only [h1, h2, Finset.sum_smul, ite_smul, zero_smul, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-- **The zeros of `f + Σ λᵢ aᵢ σ_{g(i)}`** are the points `y` with `(Λ(λ, y), y)` a zero of
`(μ, y) ↦ f(y) + Σ μ_j σ_j(y)`. -/
theorem isZeroAt_paramSlice_smul_iff {d : ℕ} (a : Fin d → X → ℝ) (g : Fin d → Fin k)
    (lam : Fin d → ℝ) (y : X) :
    IsZeroAt P (paramSlice f hf (fun i => sectionSmul P (a i) (σ (g i)))
        (fun i => (hσ (g i)).sectionSmul) lam) y ↔
      (famShift a g lam y, y) ∈ famZero f hf σ hσ := by
  change ((((⟨f y, hf y⟩ : P ⁻¹' {y}) + fiberComb (fun i => sectionSmul P (a i) (σ (g i)))
      (fun i => (hσ (g i)).sectionSmul) (lam, y)) : P ⁻¹' {y}) : Y) = fiberZero P y ↔
    ((((⟨f y, hf y⟩ : P ⁻¹' {y}) + fiberComb σ hσ (famShift a g lam y, y)) : P ⁻¹' {y}) : Y) =
      fiberZero P y
  rw [fiberComb_smul_eq]

/-- Where all `σ_j` vanish, the zeros of the family are the zeros of `f`. -/
lemma mem_famZero_iff_of_zero {y : X} (hy : ∀ j, σ j y = fiberZero P y) (μ : Fin k → ℝ) :
    (μ, y) ∈ famZero f hf σ hσ ↔ IsZeroAt P f y := by
  have h0 : fiberComb σ hσ (μ, y) = 0 := by
    unfold fiberComb
    refine Finset.sum_eq_zero fun j _ => ?_
    have : (⟨σ j y, hσ j y⟩ : P ⁻¹' {y}) = 0 := Subtype.ext (hy j)
    rw [this, smul_zero]
  change ((((⟨f y, hf y⟩ : P ⁻¹' {y}) + fiberComb σ hσ (μ, y)) : P ⁻¹' {y}) : Y) =
    fiberZero P y ↔ f y = fiberZero P y
  rw [h0, add_zero]

lemma zero_mem_famZero_iff (y : X) :
    ((0 : Fin k → ℝ), y) ∈ famZero f hf σ hσ ↔ IsZeroAt P f y := by
  change IsZeroAt P (paramSlice f hf σ hσ 0) y ↔ _
  rw [paramSlice_zero]

/-- The `j`-th one-parameter subfamily. -/
lemma mem_famZero_single_iff (j : Fin k) (μ : Fin 1 → ℝ) (y : X) :
    (μ, y) ∈ famZero f hf (fun _ : Fin 1 => σ j) (fun _ => hσ j) ↔
      ((Pi.single j (μ 0) : Fin k → ℝ), y) ∈ famZero f hf σ hσ := by
  classical
  have h1 : fiberComb (fun _ : Fin 1 => σ j) (fun _ => hσ j) (μ, y) =
      fiberComb σ hσ ((Pi.single j (μ 0) : Fin k → ℝ), y) := by
    unfold fiberComb
    change ∑ i : Fin 1, μ i • (⟨σ j y, hσ j y⟩ : P ⁻¹' {y}) =
      ∑ j', (Pi.single j (μ 0) : Fin k → ℝ) j' • (⟨σ j' y, hσ j' y⟩ : P ⁻¹' {y})
    rw [Fin.sum_univ_one, Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]
    · intro j' _ hj'; rw [Pi.single_eq_of_ne hj', zero_smul]
    · intro h; exact absurd (Finset.mem_univ j) h
  change ((((⟨f y, hf y⟩ : P ⁻¹' {y}) + fiberComb (fun _ : Fin 1 => σ j) (fun _ => hσ j)
      (μ, y)) : P ⁻¹' {y}) : Y) = fiberZero P y ↔
    ((((⟨f y, hf y⟩ : P ⁻¹' {y}) + fiberComb σ hσ ((Pi.single j (μ 0) : Fin k → ℝ), y)) :
      P ⁻¹' {y}) : Y) = fiberZero P y
  rw [h1]

end FibreAlgebra

/-! ### Regular points, and the hypotheses on local parametrizations -/

section Regular

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- **A regular point of `t|A`**: in some smooth parametrization `p` of `A` around `x = p(u)`
(by a set with unique derivatives), `d(t ∘ p)(u) ≠ 0`. -/
def MPolyfold.IsRegularPointOn (PX : MPolyfold X) (A : Set X) (t : X → ℝ) (x : X) : Prop :=
  ∃ (n : ℕ) (Ω : Set (Fin n → ℝ)) (p : (Fin n → ℝ) → X) (q : X → Fin n → ℝ) (G : Set X)
    (u : Fin n → ℝ), PX.IsSmoothParam A Ω p q G ∧ UniqueDiffOn ℝ Ω ∧ u ∈ Ω ∧ p u = x ∧
      fderivWithin ℝ (t ∘ p) Ω u ≠ 0

variable {PX : MPolyfold X} {A : Set X} {t : X → ℝ} {x : X}

/-- The regular points of `t|A` form an open subset of `A`. -/
theorem MPolyfold.IsRegularPointOn.exists_isOpen (ht : PX.IsScSmoothMap realPolyfold t)
    (h : PX.IsRegularPointOn A t x) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∀ y ∈ A ∩ O, PX.IsRegularPointOn A t y := by
  obtain ⟨n, Ω, p, q, G, u, hpar, hΩ, hu, rfl, hreg⟩ := h
  obtain ⟨O, hO, hxO, -, hall⟩ := hpar.exists_isOpen_regular hΩ ht hu hreg
  refine ⟨O, hO, hxO, fun y hy => ?_⟩
  obtain ⟨u', hu', rfl, hreg'⟩ := hall y hy
  exact ⟨n, Ω, p, q, G, u', hpar, hΩ, hu', rfl, hreg'⟩

/-- A regular point of `t|A` satisfies the clause of `HasOnlyMorseCriticalPoints` for every `A'`
that coincides with `A` near the point. -/
theorem MPolyfold.IsRegularPointOn.isMorseOrRegularPoint_of_eq (h : PX.IsRegularPointOn A t x)
    {A' O : Set X} (hO : IsOpen O) (hxO : x ∈ O) (hA : A' ∩ O = A ∩ O) :
    PX.IsMorseOrRegularPoint A' t x := by
  obtain ⟨n, Ω, p, q, G, u, hpar, hΩ, hu, rfl, hreg⟩ := h
  exact hpar.isMorseOrRegularPoint_of_regular_of_eq hΩ hu hreg hO hxO hA

/-- **Hypothesis (A1)**: the set `M ⊆ ℝᵏ × X` has a smooth parametrization by an open subset of
some `ℝⁿ` around `(0, y)` on which the projection `μ` to `ℝᵏ` is a submersion at `(0, y)`. -/
def HasFamilyParam (PX : MPolyfold X) {k : ℕ} [ParacompactSpace ((Fin k → ℝ) × X)]
    (M : Set ((Fin k → ℝ) × X)) (y : X) : Prop :=
  ∃ (n : ℕ) (Ω : Set (Fin n → ℝ)) (p : (Fin n → ℝ) → (Fin k → ℝ) × X)
    (q : (Fin k → ℝ) × X → Fin n → ℝ) (G : Set ((Fin k → ℝ) × X)) (v₀ : Fin n → ℝ),
    ((rnPolyfold k).prod PX).IsSmoothParam M Ω p q G ∧ IsOpen Ω ∧ v₀ ∈ Ω ∧ p v₀ = (0, y) ∧
      Surjective (fderiv ℝ (fun v => (p v).1) v₀)

/-- **Hypothesis (A2)**: the set `M ⊆ ℝ × X` has a smooth parametrization by an open subset of
some `ℝⁿ` around `(0, x)` in which `(0, x)` is not a critical point of `t`. -/
def HasRegularFamilyParam (PX : MPolyfold X) [ParacompactSpace ((Fin 1 → ℝ) × X)]
    (M : Set ((Fin 1 → ℝ) × X)) (t : X → ℝ) (x : X) : Prop :=
  ∃ (n : ℕ) (Ω : Set (Fin n → ℝ)) (p : (Fin n → ℝ) → (Fin 1 → ℝ) × X)
    (q : (Fin 1 → ℝ) × X → Fin n → ℝ) (G : Set ((Fin 1 → ℝ) × X)) (v₀ : Fin n → ℝ),
    ((rnPolyfold 1).prod PX).IsSmoothParam M Ω p q G ∧ IsOpen Ω ∧ v₀ ∈ Ω ∧ p v₀ = (0, x) ∧
      fderiv ℝ (fun v => t (p v).2) v₀ ≠ 0

end Regular

/-! ### A multiplier in the family makes the point critical -/

section Assembly

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

omit [T2Space Y] [ParacompactSpace Y] in
lemma isScSmoothMap_zeroIncl (k : ℕ) [ParacompactSpace ((Fin k → ℝ) × X)] :
    PX.IsScSmoothMap ((rnPolyfold k).prod PX) fun y : X => ((0 : Fin k → ℝ), y) :=
  MPolyfold.IsScSmoothOn.prodMk
    (isScSmoothMap_rn_of_components fun _ => isScSmoothMap_real_const 0)
    MPolyfold.isScSmoothMap_id

omit [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] in
/-- If `t` has a Lagrange multiplier on the family at `(0, y)`, then `y` is not a regular point
of `t|S_f`. -/
theorem not_isRegularPointOn_of_multiplier {k : ℕ} [ParacompactSpace ((Fin k → ℝ) × X)]
    (hfs : IsSection P f) {σ : Fin k → X → Y} (hσ : ∀ j, IsSection P (σ j)) {t : X → ℝ}
    (ht : PX.IsScSmoothMap realPolyfold t) {n : ℕ} {Ω : Set (Fin n → ℝ)}
    {p : (Fin n → ℝ) → (Fin k → ℝ) × X} {q : (Fin k → ℝ) × X → Fin n → ℝ}
    {G : Set ((Fin k → ℝ) × X)}
    (hpar : ((rnPolyfold k).prod PX).IsSmoothParam (famZero f hfs σ hσ) Ω p q G)
    (hΩ : IsOpen Ω) {v₀ : Fin n → ℝ} (hv₀ : v₀ ∈ Ω) {y : X} (hpv₀ : p v₀ = (0, y))
    {c : (Fin k → ℝ) →L[ℝ] ℝ}
    (hc : fderiv ℝ (fun v => t (p v).2) v₀ = c.comp (fderiv ℝ (fun v => (p v).1) v₀)) :
    ¬ PX.IsRegularPointOn (solutionSet P f) t y := by
  rintro ⟨n', Ω', p', q', G', u, hS, hΩ', hu, hpu, hreg⟩
  refine hreg ?_
  have hμ : ∀ ℓ : (Fin k → ℝ) →L[ℝ] ℝ,
      ((rnPolyfold k).prod PX).IsScSmoothMap realPolyfold fun z => ℓ (Prod.fst z) := fun ℓ =>
    (isScSmoothMap_rn_real_of_contDiff ℓ.contDiff).comp
      (MPolyfold.isScSmoothMap_fst (rnPolyfold k) PX)
  exact hS.fderivWithin_eq_zero_of_multiplier hΩ' hpar hΩ (isScSmoothMap_zeroIncl k)
    (fun y' hy' => (zero_mem_famZero_iff hfs hσ y').2 hy')
    (T := t ∘ Prod.snd) (ht.comp (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX))
    (μ := Prod.fst) hμ (fun _ => rfl) hu hv₀ (by rw [hpv₀, hpu]) hc

end Assembly

/-! ### The covering argument -/

section Main

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

lemma abs_arctan_div_two_le_one (r : ℝ) : |Real.arctan r / 2| ≤ 1 := by
  rw [abs_le]
  have h1 := Real.arctan_lt_pi_div_two r
  have h2 := Real.neg_pi_div_two_lt_arctan r
  have h3 := Real.pi_le_four
  constructor <;> linarith

lemma contDiff_arctan_div_two : ContDiff ℝ ∞ fun r : ℝ => Real.arctan r / 2 :=
  Real.contDiff_arctan.div_const 2

set_option maxHeartbeats 1600000 in
-- one long assembly
/-- **2021 Theorem 5.3.15 (2), p. 223, for a section in general position, from three local
statements** (the covering argument of the proof, p. 227).  Let `X` be tame, `f` an sc-Fredholm
section (tame germ data) with compact solution set, in general position at every zero, `N` an
auxiliary norm and `t` an sc-smooth function.  Assume: (A1) for all sc⁺-sections `σ₁, …, σ_k` and
every zero `y ∉ ∂X` of `f`, the solution set of `(μ, y) ↦ f(y) + Σ μ_j σ_j(y)` has a smooth
parametrization around `(0, y)` on which `μ` is a submersion; (A2) every zero `x ∉ ∂X` has, in
every neighbourhood and with arbitrarily small norm, an sc⁺-section `σ` such that `(0, x)` is not
a critical point of `t` on the solution set of `(μ, y) ↦ f(y) + μ σ(y)`; (A3) the zeros on `∂X`
are regular points of `t|S_f`.  Then inside every open `V ⊇ S_f` there is an open `U ⊇ S_f` with
`S_{f+s}` compact for
`s ∈ Γ^{+,1}_U(P)`, and for every `ε > 0` an `s₀ ∈ Γ^{+,1}_U(P)` with `N(s₀) ≤ ε`, vanishing near
`∂X`, such that `(f + s₀, x)` is in general position at every zero and `t` has only Morse-type
critical points on `S_{f+s₀}`. -/
theorem exists_morse_perturbation_hyp (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ} (hN : B.IsAuxNorm N) {t : X → ℝ}
    (ht : PX.IsScSmoothMap realPolyfold t)
    (hgp : ∀ x, IsZeroAt P f x → B.IsGeneralPositionGerm f x) {V : Set X} (hV : IsOpen V)
    (hSV : solutionSet P f ⊆ V)
    (hA1 : ∀ (k : ℕ) (σ : Fin k → X → Y) (hσ : ∀ j, B.IsScPlusSection (σ j)) (y : X),
      IsZeroAt P f y → y ∉ PX.boundary →
      haveI := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
      HasFamilyParam PX (famZero f hf.isScSmooth.1 σ fun j => (hσ j).1) y)
    (hA2 : ∀ x, IsZeroAt P f x → x ∉ PX.boundary → ∀ W : Set X, IsOpen W → x ∈ W →
      ∀ η > 0, ∃ (σ : X → Y) (hσ : B.IsScPlusSection σ), sectionSupport P σ ⊆ W ∧
        (∀ x', B.AuxLe N (σ x') η) ∧
        haveI := MPolyfold.paracompactSpace_prod (rnPolyfold 1) PX
        HasRegularFamilyParam PX (famZero f hf.isScSmooth.1 (fun _ : Fin 1 => σ) fun _ => hσ.1)
          t x)
    (hA3 : ∀ x ∈ PX.boundary, IsZeroAt P f x → PX.IsRegularPointOn (solutionSet P f) t x) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧ U ⊆ V ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ ε > 0, ∃ s₀ ∈ B.allowableSections N U,
        (∀ x (hx : s₀ x ∈ B.oneSet), N (B.oneMk (s₀ x) hx) ≤ ε) ∧
        (∀ᶠ x in 𝓝ˢ PX.boundary, IsZeroAt P s₀ x) ∧
        (∀ x ∈ solutionSet P (sectionAdd P f s₀),
          B.IsGeneralPositionGerm (sectionAdd P f s₀) x) ∧
        PX.HasOnlyMorseCriticalPoints (solutionSet P (sectionAdd P f s₀)) t := by
  classical
  have hfs : IsSection P f := hf.isScSmooth.1
  have := MPolyfold.paracompactSpace_prod (rnPolyfold 1) PX
  obtain ⟨U, hUo, hSU, hUV, hcpt, hcptS⟩ :=
    exists_adapted_margin hf.toIsScFredholmSection hS hN hV hSV
  refine ⟨U, hUo, hSU, hUV, hcptS, fun ε hε => ?_⟩
  set ε' : ℝ := min ε 1 with hε'
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hbcl : IsClosed PX.boundary := PX.isClosed_boundary
  set S := solutionSet P f with hSdef
  -- the critical set
  set C : Set X := {y | y ∈ S ∧ ¬ PX.IsRegularPointOn S t y} with hCdef
  have hCint : ∀ y ∈ C, y ∉ PX.boundary := fun y hy hyb => hy.2 (hA3 y hyb hy.1)
  have hSclosed : IsClosed S := hS.isClosed
  have hCcl : IsClosed C := by
    choose! Or hOro hyOr hOrreg using fun (y : X) (hy : PX.IsRegularPointOn S t y) =>
      hy.exists_isOpen ht
    have hCeq : C = S \ ⋃ y ∈ {y | PX.IsRegularPointOn S t y}, Or y := by
      ext y
      constructor
      · rintro ⟨hyS, hyr⟩
        refine ⟨hyS, fun hmem => ?_⟩
        obtain ⟨y', hy', hyy'⟩ := mem_iUnion₂.1 hmem
        exact hyr (hOrreg y' hy' y ⟨hyS, hyy'⟩)
      · rintro ⟨hyS, hyn⟩
        exact ⟨hyS, fun hr => hyn (mem_iUnion₂.2 ⟨y, hr, hyOr y hr⟩)⟩
    rw [hCeq]
    exact hSclosed.sdiff (isOpen_biUnion fun y hy => hOro y hy)
  have hCc : IsCompact C := hS.of_isClosed_subset hCcl fun y hy => hy.1
  -- the centres
  set W₀ : Set X := U ∩ PX.boundaryᶜ with hW₀
  have hW₀o : IsOpen W₀ := hUo.inter hbcl.isOpen_compl
  choose σ hσ hσsupp hσN n Ω p q G v₀ hpar hΩ hv₀ hpv₀ hdT using fun x : C =>
    hA2 x.1 x.2.1 (hCint x.1 x.2) W₀ hW₀o ⟨hSU x.2.1, hCint x.1 x.2⟩ ε' hε'pos
  have hTc : ∀ x : C, ContDiffOn ℝ ∞ (fun v => t ((p x v).2)) (Ω x) := fun x =>
    (hpar x).smooth_p (t ∘ Prod.snd) (ht.comp (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX))
  set Ω' : ∀ x : C, Set (Fin (n x) → ℝ) := fun x =>
    {v | v ∈ Ω x ∧ fderiv ℝ (fun v => t ((p x v).2)) v ≠ 0} with hΩ'
  have hΩ'o : ∀ x : C, IsOpen (Ω' x) := fun x => by
    have hc : ContinuousOn (fderiv ℝ (fun v => t ((p x v).2))) (Ω x) :=
      (hTc x).continuousOn_fderiv_of_isOpen (hΩ x) (by simp)
    have := hc.isOpen_inter_preimage (hΩ x) (isOpen_compl_singleton (x := 0))
    exact this
  set Ux : C → Set X := fun x =>
    (fun y : X => (((0 : Fin 1 → ℝ), y) : (Fin 1 → ℝ) × X)) ⁻¹' (G x ∩ q x ⁻¹' Ω' x) with hUx
  have hι1 : Continuous fun y : X => (((0 : Fin 1 → ℝ), y) : (Fin 1 → ℝ) × X) :=
    continuous_const.prodMk continuous_id
  have hUxo : ∀ x : C, IsOpen (Ux x) := fun x =>
    (((hpar x).isOpen_G).inter ((hΩ'o x).preimage (hpar x).continuous_q)).preimage hι1
  have hxUx : ∀ x : C, x.1 ∈ Ux x := fun x => by
    change ((0 : Fin 1 → ℝ), x.1) ∈ G x ∧ q x ((0 : Fin 1 → ℝ), x.1) ∈ Ω' x
    rw [← hpv₀ x, (hpar x).left_inv _ (hv₀ x)]
    exact ⟨(hpar x).mem_G (hv₀ x), hv₀ x, hdT x⟩
  obtain ⟨Tc, hTc'⟩ := hCc.elim_finite_subcover Ux hUxo
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hxUx ⟨y, hy⟩⟩)
  set k := Tc.card with hk
  have := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
  set xs : Fin k → C := fun j => (Tc.equivFin.symm j).1 with hxs
  have hcover : ∀ y ∈ C, ∃ j, y ∈ Ux (xs j) := fun y hy => by
    obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.1 (hTc' hy)
    exact ⟨Tc.equivFin ⟨x, hxT⟩, by simpa [hxs] using hyx⟩
  set σs : Fin k → X → Y := fun j => σ (xs j) with hσs
  have hσsp : ∀ j, B.IsScPlusSection (σs j) := fun j => hσ (xs j)
  have hσss : ∀ j, IsSection P (σs j) := fun j => (hσsp j).1
  -- the functions and the sections of the full family
  set aι : (Σ j : Fin k, Fin (n (xs j) + 1)) → X → ℝ := fun s y' =>
    Fin.cons (α := fun _ => ℝ) 1
      (fun i => Real.arctan (q (xs s.1) ((0 : Fin 1 → ℝ), y') i) / 2) s.2 with haι
  set d := Fintype.card (Σ j : Fin k, Fin (n (xs j) + 1)) with hd
  set e : (Σ j : Fin k, Fin (n (xs j) + 1)) ≃ Fin d := Fintype.equivFin _ with he
  set a : Fin d → X → ℝ := fun i => aι (e.symm i) with ha
  set g : Fin d → Fin k := fun i => (e.symm i).1 with hg
  have haιs : ∀ s, PX.IsScSmoothMap realPolyfold (aι s) := by
    rintro ⟨j, i⟩
    induction i using Fin.cases with
    | zero =>
      have : aι ⟨j, 0⟩ = fun _ => 1 := by funext y'; simp [haι]
      rw [this]; exact isScSmoothMap_real_const 1
    | succ i =>
      have : aι ⟨j, i.succ⟩ = (fun r : ℝ => Real.arctan r / 2) ∘
          fun y' => q (xs j) ((0 : Fin 1 → ℝ), y') i := by funext y'; simp [haι]
      rw [this]
      exact (((hpar (xs j)).smooth_q (ContinuousLinearMap.proj i)).comp
        (isScSmoothMap_zeroIncl 1)).comp_contDiff contDiff_arctan_div_two
  have haιb : ∀ s y', |aι s y'| ≤ 1 := by
    rintro ⟨j, i⟩ y'
    induction i using Fin.cases with
    | zero => simp [haι]
    | succ i => simpa [haι] using abs_arctan_div_two_le_one _
  have has : ∀ i, PX.IsScSmoothMap realPolyfold (a i) := fun i => haιs _
  set s : Fin d → X → Y := fun i => sectionSmul P (a i) (σs (g i)) with hs
  have hsp : ∀ i, B.IsScPlusSection (s i) := fun i => (hσsp (g i)).smul_left (has i)
  have hss : ∀ i, IsSection P (s i) := fun i => (hsp i).1
  have hsN' : ∀ i x, B.AuxLe N (s i x) ε' := fun i x => by
    have h1 := hN.auxLe_sectionSmul (hσss (g i)) (a i) (hσN (xs (g i)) x)
    exact ⟨h1.1, h1.2.trans (by
      have := haιb (e.symm i) x
      nlinarith [abs_nonneg (a i x)])⟩
  have hsN : ∀ i x (hx : s i x ∈ B.oneSet), N (B.oneMk (s i x) hx) ≤ 1 := fun i x _ =>
    (hsN' i x).2.trans (min_le_right _ _)
  have hssupp : ∀ i, sectionSupport P (s i) ⊆ W₀ := fun i =>
    (sectionSupport_sectionSmul_subset (hσss (g i)) (a i)).trans (hσsupp (xs (g i)))
  -- general position for almost every small parameter (Theorem 5.3.10's mechanism)
  have := MPolyfold.paracompactSpace_prod (rnPolyfold d) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin d → ℝ) × X → X))
    ((rnPolyfold d).prod PX) B
  obtain ⟨δ₁, hδ₁, CV₁, hCV₁, hgen⟩ := exists_null_isGeneralPositionGerm_paramSlice hX hf hN hUo
    (hcpt 1 one_pos) s hsp hsN fun y hy =>
      isGeneralPositionGerm_paramSection_of_isGeneralPositionGerm hf hsp hy (hgp y hy)
  -- the solution sets of the slices
  set Slam : (Fin d → ℝ) → Set X := fun lam => solutionSet P (paramSlice f hfs s hss lam)
    with hSlamdef
  have hSlam : ∀ lam y', y' ∈ Slam lam ↔ (famShift a g lam y', y') ∈ famZero f hfs σs hσss :=
    fun lam y' => isZeroAt_paramSlice_smul_iff hfs hσss a g lam y'
  set Vb : Set X := (⋃ j, sectionSupport P (σs j))ᶜ with hVbdef
  have hVbo : IsOpen Vb := (isClosed_iUnion_of_finite fun j => isClosed_closure).isOpen_compl
  have hbV : PX.boundary ⊆ Vb := fun y hyb hmem => by
    obtain ⟨j, hj⟩ := mem_iUnion.1 hmem
    exact (hσsupp (xs j) hj).2 hyb
  have hzero : ∀ y' ∈ Vb, ∀ j, σs j y' = fiberZero P y' := fun y' hy' j =>
    not_not.1 fun hne => hy' (mem_iUnion.2 ⟨j, subset_closure hne⟩)
  have hVb : ∀ lam, Slam lam ∩ Vb = S ∩ Vb := fun lam => by
    ext y'
    exact and_congr_left fun hy'V =>
      (hSlam lam y').trans (mem_famZero_iff_of_zero hfs hσss (hzero y' hy'V) _)
  -- the local statements
  have hloc : ∀ y : S, ∃ εy > 0, ∃ O : Set X, IsOpen O ∧ y.1 ∈ O ∧
      ∀ᵐ lam : Fin d → ℝ, ‖lam‖ < εy → ∀ y' ∈ O, y' ∈ Slam lam →
        PX.IsMorseOrRegularPoint (Slam lam) t y' := by
    rintro ⟨y, hy⟩
    by_cases hyb : y ∈ PX.boundary
    · obtain ⟨O₁, hO₁, hyO₁, hreg⟩ := (hA3 y hyb hy).exists_isOpen ht
      refine ⟨1, one_pos, O₁ ∩ Vb, hO₁.inter hVbo, ⟨hyO₁, hbV hyb⟩,
        Filter.Eventually.of_forall fun lam _ y' hy'O hy'S => ?_⟩
      have hy'S₀ : y' ∈ S := ((Set.ext_iff.1 (hVb lam) y').1 ⟨hy'S, hy'O.2⟩).1
      exact (hreg y' ⟨hy'S₀, hy'O.1⟩).isMorseOrRegularPoint_of_eq hVbo hy'O.2 (hVb lam)
    · obtain ⟨n', Ωy, py, qy, Gy, vy, hpary, hΩy, hvy, hpvy, hsurjy⟩ :=
        hA1 k σs hσsp y hy hyb
      have hSC : ∀ c : (Fin k → ℝ) →L[ℝ] ℝ,
          fderiv ℝ (fun v => t (py v).2) vy = c.comp (fderiv ℝ (fun v => (py v).1) vy) →
          ∀ β : (Fin n' → ℝ) →L[ℝ] ℝ, ∃ δ : Fin d → ℝ, famShift a g δ y = 0 ∧
            ∀ κ, fderiv ℝ (fun v => (py v).1) vy κ = 0 →
              β κ = ∑ i, δ i * (c (Pi.single (g i) 1) *
                fderiv ℝ (fun v => a i (py v).2) vy κ) := by
        intro c hc β
        by_cases hreg : PX.IsRegularPointOn S t y
        · exact absurd hreg
            (not_isRegularPointOn_of_multiplier hfs hσss ht hpary hΩy hvy hpvy hc)
        · obtain ⟨j, hyj⟩ := hcover y ⟨hy, hreg⟩
          have hy1 : ((0 : Fin 1 → ℝ), y) ∈
              famZero f hfs (fun _ : Fin 1 => σs j) (fun _ => hσss j) :=
            (zero_mem_famZero_iff hfs _ y).2 hy
          obtain ⟨hv₁Ω, hp₁⟩ := (hpar (xs j)).p_q hy1 hyj.1
          have hv₁' : q (xs j) ((0 : Fin 1 → ℝ), y) ∈ Ω' (xs j) := hyj.2
          obtain ⟨δg, hδ0, hδ⟩ := exists_spanning_of_group (j := j)
            (fun μ y' => mem_famZero_single_iff hfs hσss j μ y') (hpar (xs j)) (hΩ (xs j))
            hpary hΩy ht hv₁Ω hvy hp₁ hpvy
            (fun c₁ hc₁ h0 => hv₁'.2 (by rw [hc₁, h0, ContinuousLinearMap.zero_comp]))
            hsurjy (Pi.basisFun ℝ (Fin (n (xs j)))) (fun i' => aι ⟨j, i'⟩)
            (by funext y'; simp [haι]) (fun i' => by funext y'; simp [haι]) hc β
          refine ⟨fun i => sigmaExtend j δg (e.symm i), ?_, fun κ hκ => ?_⟩
          · have h1 : famShift a g (fun i => sigmaExtend j δg (e.symm i)) y =
                ∑ s' : Σ j : Fin k, Fin (n (xs j) + 1), sigmaExtend j δg s' •
                  (aι s' y • (Pi.single s'.1 (1 : ℝ) : Fin k → ℝ)) := by
              unfold famShift
              rw [← Equiv.sum_comp e]
              refine Finset.sum_congr rfl fun s' _ => ?_
              simp only [ha, hg, e.symm_apply_apply, mul_smul]
            rw [h1, sum_sigmaExtend_smul]
            simp only [smul_smul]
            rw [← Finset.sum_smul, hδ0, zero_smul]
          · rw [hδ κ hκ, ← Equiv.sum_comp e]
            simp only [ha, hg, e.symm_apply_apply]
            have h2 := sum_sigmaExtend_smul j δg (fun s' : Σ j : Fin k, Fin (n (xs j) + 1) =>
              c (Pi.single s'.1 1) * fderiv ℝ (fun v => aι s' (py v).2) vy κ)
            simp only [smul_eq_mul] at h2
            rw [h2]
      obtain ⟨εy, hεy, O, hO, hyO, hae⟩ :=
        ae_isMorseOrRegularPoint_famSlice hpary hΩy ht has g hvy hpvy hsurjy hSC
      refine ⟨εy, hεy, O, hO, hyO, ?_⟩
      filter_upwards [hae] with lam hlam hlε y' hy'O hy'S
      have hset : {y | (famShift a g lam y, y) ∈ famZero f hfs σs hσss} = Slam lam := by
        ext z; exact (hSlam lam z).symm
      rw [← hset]
      exact hlam hlε y' hy'O ((hSlam lam y').1 hy'S)
  choose εy hεy O hOo hyO hae using hloc
  obtain ⟨T', hT'⟩ := hS.elim_finite_subcover (fun y : S => O y) hOo
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hyO ⟨y, hy⟩⟩)
  set Oall : Set X := ⋃ y ∈ T', O y with hOalldef
  have hOall : IsOpen Oall := isOpen_biUnion fun y _ => hOo y
  obtain ⟨εM, hεM, hεMle⟩ : ∃ εM > 0, ∀ y ∈ T', εM ≤ εy y := by
    by_cases hne : T'.Nonempty
    · exact ⟨T'.inf' hne εy, (Finset.lt_inf'_iff hne).2 fun y _ => hεy y,
        fun y hy => Finset.inf'_le _ hy⟩
    · exact ⟨1, one_pos, fun y hy => absurd ⟨y, hy⟩ hne⟩
  have haeall : ∀ᵐ lam : Fin d → ℝ, ∀ y ∈ T', ‖lam‖ < εy y → ∀ y' ∈ O y, y' ∈ Slam lam →
      PX.IsMorseOrRegularPoint (Slam lam) t y' :=
    (Filter.eventually_all_finset T').2 fun y _ => hae y
  set CV₂ : Set (Fin d → ℝ) := {lam | ¬ ∀ y ∈ T', ‖lam‖ < εy y → ∀ y' ∈ O y, y' ∈ Slam lam →
      PX.IsMorseOrRegularPoint (Slam lam) t y'} with hCV₂def
  have hCV₂ : volume CV₂ = 0 := ae_iff.1 haeall
  -- the perturbations `p_λ = Σ λᵢ sᵢ` and their size
  have hslice : ∀ lam : Fin d → ℝ,
      sectionAdd P f (paramSlice (fiberZero P) isSection_fiberZero s hss lam) =
        paramSlice f hfs s hss lam := fun lam => sectionAdd_paramSlice_fiberZero hfs hss lam
  set δ₀ : ℝ := 1 / (d + 1) with hδ₀
  have hδ₀pos : 0 < δ₀ := by positivity
  have hN' : B.IsAuxNorm fun w => (1 / ε') * N w := hN.const_mul (by positivity)
  have hallow : ∀ lam : Fin d → ℝ, ‖lam‖ ≤ δ₀ →
      ∀ x, B.AuxLe N (paramSlice (fiberZero P) isSection_fiberZero s hss lam x) ε' := by
    intro lam hlam x
    have h1 := auxLe_paramSlice hN' StrongBundle.isScPlusSection_fiberZero hsp (ε := 1)
      (fun x hx => by rw [hN'.fiberZero_eq x hx]; norm_num)
      (fun i x hx => by
        have := (hsN' i x).2
        change 1 / ε' * N (B.oneMk (s i x) hx) ≤ 1
        rw [div_mul_eq_mul_div, one_mul, div_le_one hε'pos]
        exact this)
      (lam := lam) (by
        calc (d : ℝ) * ‖lam‖ ≤ d * δ₀ := mul_le_mul_of_nonneg_left hlam (by positivity)
          _ = d / (d + 1) := by rw [hδ₀]; ring
          _ ≤ 1 := (div_le_one (by positivity)).2 (by linarith)) x
    have h2 := (StrongBundle.auxLe_const_mul_iff (B := B) (N := N) (a := 1 / ε')
      (by positivity)).1 h1
    simpa using h2
  have hsupp0 : ∀ lam : Fin d → ℝ,
      sectionSupport P (paramSlice (fiberZero P) isSection_fiberZero s hss lam) ⊆ W₀ :=
    fun lam => (sectionSupport_paramSlice_subset isSection_fiberZero hss lam).trans (by
      rw [sectionSupport_fiberZero, empty_union]
      exact iUnion_subset hssupp)
  have hzeroU : ∀ lam y', y' ∈ Slam lam → y' ∈ U := by
    intro lam y' hy'
    by_contra hU
    have hz : IsZeroAt P (paramSlice (fiberZero P) isSection_fiberZero s hss lam) y' :=
      not_not.1 fun hne => hU (hsupp0 lam (subset_closure hne)).1
    have hy'' : IsZeroAt P (sectionAdd P f
        (paramSlice (fiberZero P) isSection_fiberZero s hss lam)) y' := by
      rw [hslice]; exact hy'
    exact hU (hSU (isZeroAt_left_of_isZeroAt_sectionAdd hfs (isSection_paramSlice lam) hy'' hz))
  -- compactness: the zeros of the slices for small parameters lie in `Oall`
  set Kc := closure {x ∈ U | B.AuxLe N (f x) 1} with hKc
  have hzKc : ∀ lam : Fin d → ℝ, ‖lam‖ ≤ δ₀ → ∀ y', y' ∈ Slam lam → y' ∈ Kc := by
    intro lam hlam y' hy'
    have hy'' : IsZeroAt P (sectionAdd P f
        (paramSlice (fiberZero P) isSection_fiberZero s hss lam)) y' := by
      rw [hslice]; exact hy'
    have h1 := hallow lam hlam y'
    exact subset_closure ⟨hzeroU lam y' hy', hN.auxLe_of_sectionAdd hfs
      (isSection_paramSlice lam) hy'' ⟨h1.1, h1.2.trans (min_le_right _ _)⟩⟩
  have hFt := theorem_3_1_21_tame hf hsp
  set F := paramSection f hfs s hss with hF
  set Z : Set ((Fin d → ℝ) × X) := {z | ‖z.1‖ ≤ δ₀ ∧ z.2 ∈ Kc ∧
    IsZeroAt (pullbackProj P Prod.snd) F z} with hZdef
  have hZclosed : IsClosed Z :=
    (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
      ((isClosed_closure.preimage continuous_snd).inter (isClosed_solutionSet hFt.isScSmooth))
  have hZ : IsCompact Z :=
    ((isCompact_closedBall (0 : Fin d → ℝ) δ₀).prod (hcpt 1 one_pos)).of_isClosed_subset
      hZclosed fun z hz => ⟨mem_closedBall_zero_iff.2 hz.1, hz.2.1⟩
  obtain ⟨δt, hδt, hδtO⟩ := exists_pos_forall_mem_of_isCompact hZ
    (hOall.preimage continuous_snd) fun z hz hz1 => by
      have hz2 : IsZeroAt P f z.2 := by
        have := (isZeroAt_paramSection_iff z).1 hz.2.2
        rw [hz1, paramSlice_zero] at this; exact this
      exact hT' hz2
  -- the choice of the parameter
  set δ : ℝ := min (min δ₁ εM) (min δt δ₀) with hδ
  have hδpos : 0 < δ := lt_min (lt_min hδ₁ hεM) (lt_min hδt hδ₀pos)
  obtain ⟨lam, hlam, hlamCV⟩ := exists_norm_lt_not_mem_of_null
    (measure_union_null hCV₁ hCV₂) hδpos
  have hl₁ : ‖lam‖ < δ₁ := hlam.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hlM : ‖lam‖ < εM := hlam.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hlt : ‖lam‖ < δt := hlam.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hl₀ : ‖lam‖ ≤ δ₀ := (hlam.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  obtain ⟨hN1, hgpU⟩ := hgen lam hl₁ fun h => hlamCV (Or.inl h)
  have hMorse : ∀ y ∈ T', ‖lam‖ < εy y → ∀ y' ∈ O y, y' ∈ Slam lam →
      PX.IsMorseOrRegularPoint (Slam lam) t y' :=
    not_not.1 fun h => hlamCV (Or.inr h)
  refine ⟨paramSlice (fiberZero P) isSection_fiberZero s hss lam,
    ⟨isScPlusSection_paramSlice StrongBundle.isScPlusSection_fiberZero hsp lam,
      (hsupp0 lam).trans inter_subset_left, fun x _ => (hN1 x).2⟩,
    fun x _ => (hallow lam hl₀ x).2.trans (min_le_left _ _), ?_, ?_, ?_⟩
  · have hopen : IsOpen (sectionSupport P
        (paramSlice (fiberZero P) isSection_fiberZero s hss lam))ᶜ :=
      isClosed_closure.isOpen_compl
    have hsub : PX.boundary ⊆ (sectionSupport P
        (paramSlice (fiberZero P) isSection_fiberZero s hss lam))ᶜ :=
      fun x hxb hxs => (hsupp0 lam hxs).2 hxb
    filter_upwards [hopen.mem_nhdsSet.2 hsub] with x hx
    exact not_not.1 fun hne => hx (subset_closure hne)
  · rw [hslice]
    intro x hx
    exact hgpU x (hzeroU lam x hx) hx
  · rw [hslice]
    intro y' hy'
    have hzZ : ((lam, y') : (Fin d → ℝ) × X) ∈ Z :=
      ⟨hl₀, hzKc lam hl₀ y' hy', (isZeroAt_paramSection_iff (lam, y')).2 hy'⟩
    obtain ⟨y, hyT, hy'O⟩ := mem_iUnion₂.1 (hδtO _ hzZ hlt)
    exact hMorse y hyT (hlM.trans_le (hεMle y hyT)) y' hy'O hy'

end Main

/-! ### Theorem 5.3.15 -/

section Theorem

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
lemma sectionAdd_sectionAdd_eq {f s s' : X → Y} (hf : IsSection P f) (hs : IsSection P s)
    (hs' : IsSection P s') :
    sectionAdd P f (sectionAdd P s s') = sectionAdd P (sectionAdd P f s) s' := by
  funext x
  rw [sectionAdd_apply (hf.sectionAdd hs) hs', sectionAdd_apply hf (hs.sectionAdd hs')]
  congr 1
  have hA : (⟨sectionAdd P f s x, (hf.sectionAdd hs) x⟩ : P ⁻¹' {x}) =
      ⟨f x, hf x⟩ + ⟨s x, hs x⟩ := Subtype.ext (sectionAdd_apply hf hs x)
  have hB : (⟨sectionAdd P s s' x, (hs.sectionAdd hs') x⟩ : P ⁻¹' {x}) =
      ⟨s x, hs x⟩ + ⟨s' x, hs' x⟩ := Subtype.ext (sectionAdd_apply hs hs' x)
  rw [hA, hB, add_assoc]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
lemma isZeroAt_sectionAdd_of_isZeroAt {s s' : X → Y} (hs : IsSection P s) (hs' : IsSection P s')
    {x : X} (h : IsZeroAt P s x) (h' : IsZeroAt P s' x) : IsZeroAt P (sectionAdd P s s') x := by
  have e : (⟨s x, hs x⟩ : P ⁻¹' {x}) = 0 := Subtype.ext h
  have e' : (⟨s' x, hs' x⟩ : P ⁻¹' {x}) = 0 := Subtype.ext h'
  change sectionAdd P s s' x = fiberZero P x
  rw [sectionAdd_apply hs hs', e, e', add_zero]
  rfl

variable (B) in
/-- **The three local statements used by the covering argument**, for a section `g` (see
`exists_morse_perturbation_hyp`): (A1) smooth parametrizations of the solution sets of the
families `g + Σ μ_j σ_j` around the points `(0, y)`, `y ∉ ∂X` a zero of `g`, on which `μ` is a
submersion; (A2) at every zero `x ∉ ∂X`, small sc⁺-sections `σ` with small support for which
`(0, x)` is not a critical point of `t` on the solution set of `g + μσ`; (A3) the zeros of `g` on
`∂X` are regular points of `t|S_g`. -/
def StrongBundle.HasMorseLocalData (N : B.One → ℝ) (t : X → ℝ) (g : X → Y)
    (hg : B.IsScFredholmSectionTame g) : Prop :=
  (∀ (k : ℕ) (σ : Fin k → X → Y) (hσ : ∀ j, B.IsScPlusSection (σ j)) (y : X),
      IsZeroAt P g y → y ∉ PX.boundary →
      haveI := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
      HasFamilyParam PX (famZero g hg.isScSmooth.1 σ fun j => (hσ j).1) y) ∧
    (∀ x, IsZeroAt P g x → x ∉ PX.boundary → ∀ W : Set X, IsOpen W → x ∈ W →
      ∀ η > 0, ∃ (σ : X → Y) (hσ : B.IsScPlusSection σ), sectionSupport P σ ⊆ W ∧
        (∀ x', B.AuxLe N (σ x') η) ∧
        haveI := MPolyfold.paracompactSpace_prod (rnPolyfold 1) PX
        HasRegularFamilyParam PX (famZero g hg.isScSmooth.1 (fun _ : Fin 1 => σ) fun _ => hσ.1)
          t x) ∧
    ∀ x ∈ PX.boundary, IsZeroAt P g x → PX.IsRegularPointOn (solutionSet P g) t x

/-- **2021 Theorem 5.3.15, p. 223** (2017: Theorem 5.8; preprint: Theorem 5.22), with conclusion
(2), from the local statements `HasMorseLocalData`.  Let `X` admit sc-smooth bump functions,
`(f, t)` a generalized compact homotopy (Definition 5.3.13) whose ends `Xᵢ = t⁻¹(i)` have no
boundary and whose end problems are in general position, `∂X = X₀ ∪ X₁`, and `N` an auxiliary
norm.  Assume that every perturbed section `g = f + s` (`s` an sc⁺-section vanishing near `∂X`)
with compact solution set, in general position at every zero, has the local data
`HasMorseLocalData` (implicit function theorem statements; they are the hypothesis of this
form, discharged by `StrongBundle.hasMorseLocalData`; the unconditional statement is
`theorem_5_3_15` in `Theorem5315_Final.lean`).  Then there is an open `U ⊇ S_f` such
that `S_{f+s}` is compact for every `s ∈ Γ^{+,1}_U(P)`, and for every `ε > 0` an
`s₀ ∈ Γ^{+,1}_U(P)` with `N(s₀(x)) ≤ ε`, vanishing near `∂X`, such that (1) `(f + s₀, x)` is in
general position at every `x ∈ S_{f+s₀}` and (2) `t : S_{f+s₀} → [0, 1]` has only Morse-type
critical points (`MPolyfold.HasOnlyMorseCriticalPoints`).  *Proof*: `s₀ = s₁ + s₂`, `s₁` from
`theorem_5_3_15_generalPosition` and `s₂` from `exists_morse_perturbation_hyp` for `f + s₁`. -/
theorem theorem_5_3_15_hyp (hbump : PX.AdmitsBumpFunctions) {t : X → ℝ}
    (h : B.IsSubmersiveGenCompactHomotopy f t)
    (hends : B.IsGeneralPositionAtEnds f h.isScFredholm.isScSmooth.1 t)
    (hbd : PX.boundary = t ⁻¹' {0} ∪ t ⁻¹' {1}) {N : B.One → ℝ} (hN : B.IsAuxNorm N)
    (hloc : ∀ (s : X → Y) (hs : B.IsScPlusSection s), (∀ᶠ x in 𝓝ˢ PX.boundary, IsZeroAt P s x) →
      IsCompact (solutionSet P (sectionAdd P f s)) →
      (∀ x, IsZeroAt P (sectionAdd P f s) x → B.IsGeneralPositionGerm (sectionAdd P f s) x) →
      B.HasMorseLocalData N t (sectionAdd P f s) (theorem_3_1_18_tame h.isScFredholm hs)) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ ε > 0, ∃ s₀ ∈ B.allowableSections N U,
        (∀ x (hx : s₀ x ∈ B.oneSet), N (B.oneMk (s₀ x) hx) ≤ ε) ∧
        (∀ᶠ x in 𝓝ˢ PX.boundary, IsZeroAt P s₀ x) ∧
        (∀ x ∈ solutionSet P (sectionAdd P f s₀),
          B.IsGeneralPositionGerm (sectionAdd P f s₀) x) ∧
        PX.HasOnlyMorseCriticalPoints (solutionSet P (sectionAdd P f s₀)) t := by
  have hfs : IsSection P f := h.isScFredholm.isScSmooth.1
  obtain ⟨U, hUo, hSU, hcptS, hstep1⟩ := theorem_5_3_15_generalPosition hbump h hends hbd hN
  refine ⟨U, hUo, hSU, hcptS, fun ε hε => ?_⟩
  set η : ℝ := min ε 1 / 2 with hη
  have hηpos : 0 < η := by have := lt_min hε one_pos; positivity
  obtain ⟨s₁, hs₁, hs₁N, hs₁van, hs₁gp⟩ := hstep1 η hηpos
  have hs₁s : IsSection P s₁ := hs₁.1.1
  set f₁ := sectionAdd P f s₁ with hf₁def
  have hf₁ : B.IsScFredholmSectionTame f₁ := theorem_3_1_18_tame h.isScFredholm hs₁.1
  have hS₁ : IsCompact (solutionSet P f₁) := hcptS s₁ hs₁
  have hS₁U : solutionSet P f₁ ⊆ U := by
    intro x hx
    by_contra hU
    have hz : IsZeroAt P s₁ x := not_not.1 fun hne => hU (hs₁.2.1 (subset_closure hne))
    exact hU (hSU (isZeroAt_left_of_isZeroAt_sectionAdd hfs hs₁s hx hz))
  obtain ⟨hA1, hA2, hA3⟩ := hloc s₁ hs₁.1 hs₁van hS₁ hs₁gp
  obtain ⟨U₁, -, -, hU₁U, -, hstep2⟩ := exists_morse_perturbation_hyp h.isTame hf₁ hS₁ hN
    h.isScSmooth_t hs₁gp hUo hS₁U hA1 hA2 hA3
  obtain ⟨s₂, hs₂, hs₂N, hs₂van, hs₂gp, hs₂M⟩ := hstep2 η hηpos
  have hs₂s : IsSection P s₂ := hs₂.1.1
  have hassoc : sectionAdd P f (sectionAdd P s₁ s₂) = sectionAdd P f₁ s₂ :=
    sectionAdd_sectionAdd_eq hfs hs₁s hs₂s
  have hNsum : ∀ x, B.AuxLe N (sectionAdd P s₁ s₂ x) (min ε 1) := fun x => by
    have := hN.auxLe_sectionAdd hs₁s hs₂s (x := x) ⟨hs₁.1.mem_oneSet x, hs₁N x _⟩
      ⟨hs₂.1.mem_oneSet x, hs₂N x _⟩
    rwa [hη, add_halves] at this
  have hsupp : sectionSupport P (sectionAdd P s₁ s₂) ⊆ U := by
    have hsub : {x | sectionAdd P s₁ s₂ x ≠ fiberZero P x} ⊆
        sectionSupport P s₁ ∪ sectionSupport P s₂ := by
      intro x hx
      by_contra hcon
      rw [mem_union, not_or] at hcon
      exact hx (isZeroAt_sectionAdd_of_isZeroAt hs₁s hs₂s
        (not_not.1 fun hne => hcon.1 (subset_closure hne))
        (not_not.1 fun hne => hcon.2 (subset_closure hne)))
    exact (closure_minimal hsub (isClosed_closure.union isClosed_closure)).trans
      (union_subset hs₁.2.1 (hs₂.2.1.trans hU₁U))
  refine ⟨sectionAdd P s₁ s₂, ⟨hs₁.1.add hs₂.1, hsupp,
      fun x _ => (hNsum x).2.trans (min_le_right _ _)⟩,
    fun x _ => (hNsum x).2.trans (min_le_left _ _), ?_, ?_, ?_⟩
  · filter_upwards [hs₁van, hs₂van] with x h1 h2
    exact isZeroAt_sectionAdd_of_isZeroAt hs₁s hs₂s h1 h2
  · rw [hassoc]; exact hs₂gp
  · rw [hassoc]; exact hs₂M

end Theorem

end Polyfold
