import Polyfold.Chapter15.LinearizationIntrinsic
import Polyfold.Chapter13.MultisectionAlgebra
import Polyfold.Chapter12.CompactnessEp
import Polyfold.Chapter2.ReducedTangentIntrinsic
import Polyfold.Chapter5.ReflexiveCompactness
import Polyfold.Chapter10.StrongBundleEquivalenceExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3 "Perturbations",
pp. 691–693: **Definition 15.3.1** (controlling pairs; 2017: Definition 15.4), the sentence
before it, **Definition 15.3.3** (admissible perturbations; 2017: Definition 15.5) with the
example after it, **Definition 15.3.5** (general position; 2017: Definition 15.6) and the first
sentence of **Remark 15.3.6**.

# Controlling pairs, admissible perturbations, general position

## The text, paraphrased

(Before 15.3.1) An auxiliary norm is extended by `+∞` off `W_{0,1}`; by §12.4 there is a
saturated open `U ⊇ S_f` such that `{x ∈ U | N(f(x)) ≤ 1}` has an orbit space with compact
closure.  (15.3.1) Over an ep-groupoid with paracompact `|X|`, for an auxiliary norm `N`, an
sc-Fredholm section functor `f` and a saturated open `U ⊇ S_f`: `(N, U)` *controls the
compactness of `f`* if the orbit space of `{x ∈ U | N(f(x)) ≤ 1}` has compact closure in `|X|`.
(15.3.3) For `f` with compact `|S_f|` and `(N, U)` controlling compactness, an `(N, U)`-admissible
perturbation is an sc⁺-multisection `Λ` with `N(Λ)(x) ≤ 1` everywhere and
`{x | ∃ t ∈ [−1, 1], (tΛ)(f(x)) > 0} ⊆ U`.  (After it) If `dom-supp(Λ) ⊆ U` and `N(Λ) ≤ 1` then
`Λ` is admissible.  (15.3.5) Over a tame ep-groupoid, `(f, Λ)` is in general position if for
every `x ∈ supp(Λ ∘ f)` and every operator `Lᵢ` of `T(f,Λ)(x) = Σ σᵢ Lᵢ` (`σᵢ > 0`) the
restriction `Lᵢ|T^R_xX : T^R_xX → W_x` is surjective; `T^R_(f,Λ)(x) = Σ σᵢ Lᵢ|T^R_xX` is the
reduced linearization.  (15.3.6) In general position `T(f,Λ)(x)` is onto on `supp(Λ ∘ f)`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`ControlsCompactness A f N U`** (Definition 15.3.1), with `N(f(x)) ≤ 1` read as Part I's
  `AuxLe N (f x) 1` (`N = +∞` off `W_{0,1}`, as the text extends `N`);
  **`exists_controlsCompactness`** (the sentence before it: for an sc-Fredholm section functor
  with compact `|S_f|`, every auxiliary norm has a controlling `U`, from Theorem 12.4.2);
  `ControlsCompactness.mono` (a smaller saturated open `U' ⊇ S_f` also controls).
* **`IsAdmissible A f N U Λ`** (Definition 15.3.3) and
  **`isAdmissible_of_domSupp_subset`** (the example after it).
* **`IsInGeneralPosition A f Λ`** (Definition 15.3.5): for `x ∈ X₁` with `Λ(f(x)) > 0`, every
  operator of the support of `T(f,Λ)(x)` restricted to `T^R_xX` is surjective, with `T^R_xX`
  read in any chart and presentation (`MPolyfold.reducedTangentFiber`, Definition 2.5.8);
  `isInGeneralPosition_iff_exists` (one chart at each point suffices, by
  `reducedTangentFiber_eq`); `reducedLinearization` and
  `isInGeneralPosition_iff_reducedLinearization`.
* **`IsInGeneralPosition.surjective`** (Remark 15.3.6, first sentence).
* `isInGeneralPosition_witness`: satisfiability, over `ℝⁿ × ℝ⁰ → ℝⁿ` with the trivial
  multisection, where `supp(Λ ∘ f)` is all of `ℝⁿ`.

## Reading

* `supp(Λ ∘ f)` is taken inside `X₁`, where `T(f,Λ)` is defined (Definition 15.1.7):
  `supp(Λ ∘ f) ⊆ X₁` for an sc-Fredholm `f` (`mem_levelSet_one_of_pos`: `f(x) = sᵢ(x) ∈ W_{0,1}`
  and `f` is regularizing).
* The "operators `Lᵢ` with `σᵢ > 0`" of the formal sum `T(f,Λ)(x) ∈ GrF(x)` are the elements of
  its support (positive coefficients).
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

/-! ### Definition 15.3.1 -/

variable (A) in
/-- **Definition 15.3.1, p. 691 (2017: Definition 15.4)**: `(N, U)` **controls the compactness**
of `f`: `N` is an auxiliary norm (Definition 8.3.5), `U` a saturated open neighbourhood of `S_f`,
and the orbit space of `{x ∈ U | N(f(x)) ≤ 1}` has compact closure in `|X|`. -/
def ControlsCompactness (f : A.Obj → A.W) (N : A.B.One → ℝ) (U : Set A.Obj) : Prop :=
  A.E.IsAuxNorm N ∧ IsOpen U ∧ A.X.IsSaturated U ∧ solutionSet A.P f ⊆ U ∧
    IsCompact (closure (A.X.π '' {x ∈ U | A.B.AuxLe N (f x) 1}))

/-- **The sentence before Definition 15.3.1 (p. 691)**: for an sc-Fredholm section functor `f`
with compact `|S_f|` and every auxiliary norm `N`, some saturated open `U ⊇ S_f` makes `(N, U)`
control compactness (Theorem 12.4.2, (2) ⇒ (3)). -/
theorem exists_controlsCompactness {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hS : A.E.HasCompactSolutionSetEp f) {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N) :
    ∃ U, ControlsCompactness A f N U := by
  obtain ⟨-, h⟩ := A.E.isProperLtInftyFunctor_of_hasCompactSolutionSetEp hf hS
  obtain ⟨U, hUo, hUs, hSU, hC⟩ := h N hN
  exact ⟨U, hN, hUo, hUs, hSU, hC 1 one_pos⟩

/-- A smaller saturated open neighbourhood of `S_f` also controls compactness. -/
theorem ControlsCompactness.mono {f : A.Obj → A.W} {N : A.B.One → ℝ} {U U' : Set A.Obj}
    (h : ControlsCompactness A f N U) (hU'o : IsOpen U') (hU's : A.X.IsSaturated U')
    (hSU' : solutionSet A.P f ⊆ U') (hU'U : U' ⊆ U) : ControlsCompactness A f N U' := by
  refine ⟨h.1, hU'o, hU's, hSU', h.2.2.2.2.of_isClosed_subset isClosed_closure
    (closure_mono (image_mono fun x hx => ⟨hU'U hx.1, hx.2⟩))⟩

/-! ### Definition 15.3.3 -/

variable (A) in
/-- **Definition 15.3.3, p. 692 (2017: Definition 15.5)**: an **`(N, U)`-admissible
perturbation** for `f`: an sc⁺-multisection `Λ` with `N(Λ)(x) ≤ 1` for all `x` (Definition
13.2.3) and `{x ∈ X | ∃ t ∈ [−1, 1], (tΛ)(f(x)) > 0} ⊆ U` (`tΛ` of Definition 13.2.10). -/
def IsAdmissible (f : A.Obj → A.W) (N : A.B.One → ℝ) (U : Set A.Obj) (Λ : A.W → ℚ≥0) : Prop :=
  IsScPlusMultisection A Λ ∧ (∀ x, pointwiseNorm N Λ x ≤ 1) ∧
    {x | ∃ t ∈ Icc (-1 : ℝ) 1, 0 < multisectionSmul t Λ (f x)} ⊆ U

/-- Off the domain support, `Λ` vanishes on `W_x ∖ {0_x}`. -/
theorem eq_zero_of_not_mem_domSupp {Λ : A.W → ℚ≥0} {x : A.Obj} (hx : x ∉ domSupp Λ) {w : A.W}
    (hw : A.P w = x) (hw0 : w ≠ fiberZero A.P x) : Λ w = 0 := by
  by_contra h
  exact hx (subset_closure ⟨w, hw, hw0, pos_iff_ne_zero.2 h⟩)

/-- Off the domain support, `(tΛ)(w) > 0` forces `w = 0`. -/
theorem eq_fiberZero_of_multisectionSmul_pos {Λ : A.W → ℚ≥0} {w : A.W}
    (hx : A.P w ∉ domSupp Λ) {t : ℝ} (ht : 0 < multisectionSmul t Λ w) :
    w = fiberZero A.P (A.P w) := by
  unfold multisectionSmul smulAt at ht
  split_ifs at ht with h0 hu
  · exact congrArg Subtype.val hu
  · exact absurd ht (lt_irrefl 0)
  · by_contra hne
    set u : A.P ⁻¹' {A.P w} := t⁻¹ • toFib w
    have hu0 : u ≠ 0 := by
      intro hu
      apply hne
      have : toFib w = 0 := by
        have := congrArg (t • ·) hu
        simpa [u, smul_smul, mul_inv_cancel₀ h0] using this
      exact congrArg Subtype.val this
    have hz := eq_zero_of_not_mem_domSupp hx u.2 fun e => hu0 (Subtype.ext e)
    rw [hz] at ht
    exact lt_irrefl 0 ht

/-- **The example after Definition 15.3.3 (p. 692)**: an sc⁺-multisection with domain support in
`U` and `N(Λ) ≤ 1` is `(N, U)`-admissible, for `U ⊇ S_f`. -/
theorem isAdmissible_of_domSupp_subset {f : A.Obj → A.W} (hf : IsSection A.P f)
    {N : A.B.One → ℝ} {U : Set A.Obj} (hSU : solutionSet A.P f ⊆ U) {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) (hN : ∀ x, pointwiseNorm N Λ x ≤ 1)
    (hdom : domSupp Λ ⊆ U) : IsAdmissible A f N U Λ := by
  refine ⟨hΛ, hN, fun x ⟨t, _, ht⟩ => ?_⟩
  by_contra hxU
  have hx : A.P (f x) ∉ domSupp Λ := by rw [hf x]; exact fun h => hxU (hdom h)
  have h0 := eq_fiberZero_of_multisectionSmul_pos hx ht
  rw [hf x] at h0
  exact hxU (hSU h0)

/-! ### Definition 15.3.5 -/

variable (A) in
/-- **Definition 15.3.5, p. 693 (2017: Definition 15.6)**: `(f, Λ)` is **in general position**:
for every `x ∈ supp(Λ ∘ f)` (in `X₁`, where `T(f,Λ)` lives) every operator `L` of the formal sum
`T(f,Λ)(x)` (Definition 15.1.7) is surjective on the reduced tangent space,
`L|T^R_xX : T^R_xX → W_x`, with `T^R_xX` read in any chart `φ` around `x` and any presentation
`T` of its partial quadrant (Definition 2.5.8). -/
def IsInGeneralPosition (f : A.Obj → A.W) (Λ : A.W → ℚ≥0) : Prop :=
  ∀ x : A.X.PObj.Level 1, 0 < Λ (f (A.X.PObj.levelVal 1 x)) →
    ∀ L ∈ (linearization f Λ x).support, ∀ (φ : MChart A.Obj) (hφ : A.X.PObj.IsChart φ)
      (hx : A.X.PObj.levelVal 1 x ∈ φ.source) (k : ℕ) (V : ScBanach)
      (T : ScIso φ.model.E ((ScBanach.const (Fin k → ℝ)).prod V)),
      φ.model.C = T 0 ⁻¹' quadrant k V 0 →
        Surjective (L.domRestrict (reducedTangentFiber hφ hx T))

/-- Every point of `X₁` has a chart with a presentation of its partial quadrant. -/
theorem exists_chart_presentation (x : A.X.PObj.Level 1) :
    ∃ (φ : MChart A.Obj) (_ : A.X.PObj.IsChart φ) (_ : A.X.PObj.levelVal 1 x ∈ φ.source)
      (k : ℕ) (V : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin k → ℝ)).prod V)),
      φ.model.C = T 0 ⁻¹' quadrant k V 0 := by
  obtain ⟨φ, hφ, hx⟩ := A.X.PObj.exists_isChart_mem_source (A.X.PObj.levelVal 1 x)
  obtain ⟨k, V, T, hT⟩ := φ.model.isPartialQuadrant
  exact ⟨φ, hφ, hx, k, V, T, hT⟩

/-- **Definition 15.3.5 is chart independent**: it suffices to check one chart and presentation
at each point (`reducedTangentFiber_eq`, Proposition 2.4.10). -/
theorem isInGeneralPosition_iff_exists {f : A.Obj → A.W} {Λ : A.W → ℚ≥0} :
    IsInGeneralPosition A f Λ ↔ ∀ x : A.X.PObj.Level 1, 0 < Λ (f (A.X.PObj.levelVal 1 x)) →
      ∃ (φ : MChart A.Obj) (hφ : A.X.PObj.IsChart φ) (hx : A.X.PObj.levelVal 1 x ∈ φ.source)
        (k : ℕ) (V : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin k → ℝ)).prod V)),
        φ.model.C = T 0 ⁻¹' quadrant k V 0 ∧ ∀ L ∈ (linearization f Λ x).support,
          Surjective (L.domRestrict (reducedTangentFiber hφ hx T)) := by
  constructor
  · intro h x hx
    obtain ⟨φ, hφ, hxφ, k, V, T, hT⟩ := exists_chart_presentation (A := A) x
    exact ⟨φ, hφ, hxφ, k, V, T, hT, fun L hL => h x hx L hL φ hφ hxφ k V T hT⟩
  · intro h x hx L hL ψ hψ hxψ k' V' T' hT'
    obtain ⟨φ, hφ, hxφ, k, V, T, hT, hsurj⟩ := h x hx
    have e := reducedTangentFiber_eq (hφ := hφ) (hx := hxφ) (T := T) (hψ := hψ) (hx' := hxψ)
      (T' := T') hT hT'
    rw [← e]
    exact hsurj L hL

/-- **The reduced linearization** `T^R_(f,Λ)(x) = Σ σᵢ Lᵢ|T^R_xX` (Definition 15.3.5), in a chart
and presentation. -/
def reducedLinearization (f : A.Obj → A.W) (Λ : A.W → ℚ≥0) (x : A.X.PObj.Level 1)
    {φ : MChart A.Obj} (hφ : A.X.PObj.IsChart φ) (hx : A.X.PObj.levelVal 1 x ∈ φ.source)
    {k : ℕ} {V : ScBanach} (T : ScIso φ.model.E ((ScBanach.const (Fin k → ℝ)).prod V)) :
    (reducedTangentFiber hφ hx T →ₗ[ℝ] A.P ⁻¹' {A.X.PObj.levelVal 1 x}) →₀ ℚ≥0 :=
  (linearization f Λ x).mapDomain fun L => L.domRestrict (reducedTangentFiber hφ hx T)

/-- With coefficients in `ℚ≥0` nothing cancels: the support of a push-forward of formal sums is
the image of the support. -/
theorem _root_.Finsupp.support_mapDomain_nnrat {α β : Type*} [DecidableEq β] (g : α → β)
    (v : α →₀ ℚ≥0) : (v.mapDomain g).support = v.support.image g := by
  refine subset_antisymm Finsupp.mapDomain_support ?_
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
  rw [Finsupp.mem_support_iff] at ha ⊢
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 ha) ?_)
  have h := Finset.single_le_sum (f := fun a' => (Finsupp.single (g a') (v a')) (g a))
    (fun _ _ => zero_le) (Finsupp.mem_support_iff.2 ha)
  simpa [Finsupp.sum] using h

/-- **General position in terms of the reduced linearization**: `(f, Λ)` is in general position
iff at every `x ∈ supp(Λ ∘ f)` every operator of `T^R_(f,Λ)(x)` is surjective. -/
theorem isInGeneralPosition_iff_reducedLinearization {f : A.Obj → A.W} {Λ : A.W → ℚ≥0} :
    IsInGeneralPosition A f Λ ↔ ∀ x : A.X.PObj.Level 1, 0 < Λ (f (A.X.PObj.levelVal 1 x)) →
      ∀ (φ : MChart A.Obj) (hφ : A.X.PObj.IsChart φ) (hx : A.X.PObj.levelVal 1 x ∈ φ.source)
        (k : ℕ) (V : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin k → ℝ)).prod V)),
        φ.model.C = T 0 ⁻¹' quadrant k V 0 →
          ∀ L ∈ (reducedLinearization f Λ x hφ hx T).support, Surjective L := by
  classical
  constructor
  · intro h x hx φ hφ hxφ k V T hT L hL
    rw [reducedLinearization, Finsupp.support_mapDomain_nnrat] at hL
    obtain ⟨L', hL', rfl⟩ := Finset.mem_image.1 hL
    exact h x hx L' hL' φ hφ hxφ k V T hT
  · intro h x hx L hL φ hφ hxφ k V T hT
    refine h x hx φ hφ hxφ k V T hT _ ?_
    rw [reducedLinearization, Finsupp.support_mapDomain_nnrat]
    exact Finset.mem_image_of_mem _ hL

/-- **Remark 15.3.6, p. 693, first sentence**: in general position `T(f,Λ)(x)` is onto at every
`x ∈ supp(Λ ∘ f)`: every operator of its support is surjective (`T^R_xX ⊆ T_xX`). -/
theorem IsInGeneralPosition.surjective {f : A.Obj → A.W} {Λ : A.W → ℚ≥0}
    (h : IsInGeneralPosition A f Λ) {x : A.X.PObj.Level 1}
    (hx : 0 < Λ (f (A.X.PObj.levelVal 1 x))) {L} (hL : L ∈ (linearization f Λ x).support) :
    Surjective L := by
  obtain ⟨φ, hφ, hxφ, k, V, T, hT⟩ := exists_chart_presentation (A := A) x
  intro w
  obtain ⟨α, hα⟩ := h x hx L hL φ hφ hxφ k V T hT w
  exact ⟨α, hα⟩

/-! ### `supp(Λ ∘ f) ⊆ X₁` -/

/-- **`supp(Λ ∘ f) ⊆ X₁`**: if `Λ(f(x)) > 0` then `f(x) = sᵢ(x) ∈ W_{0,1}` for a local section
`sᵢ`, so `x ∈ X₁` (`f` is regularizing, the remark after Definition 12.1.1). -/
theorem mem_levelSet_one_of_pos {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) {x : A.Obj} (hx : 0 < Λ (f x)) :
    x ∈ A.X.PObj.levelSet 1 := by
  classical
  obtain ⟨O, k, s, σ, -, hxO, h⟩ := hΛ.exists_isLocalRepOn x
  have hfx : A.P (f x) = x := hf.1.1.1 x
  have hsum := h.2.2.2 (f x) (by rw [hfx]; exact hxO)
  rw [hsum] at hx
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hx)
  have hfi : f x = s i x := by
    by_contra hne
    rw [hfx, if_neg hne] at hi
    exact hi rfl
  have hone : f x ∈ A.B.oneSet := hfi ▸ (h.2.1 i).mem_oneSet hxO
  refine A.E.remark_12_1_1_regularizing_obj hf (m := 0) ?_ ?_
  · rw [MPolyfold.levelSet_zero]; exact mem_univ x
  · exact StrongBundle.oneSet_subset_doubleLevel hone

/-! ### Satisfiability of Definition 15.3.5 -/

/-- **Definition 15.3.5 is satisfiable with nonempty `supp(Λ ∘ f)`**: over the trivial ep-groupoid
of `ℝⁿ` with the bundle `ℝⁿ × ℝ⁰ → ℝⁿ`, the zero section and the trivial multisection `Λ₀` are in
general position, and `supp(Λ₀ ∘ 0)` is all of `ℝⁿ` (the fibres are `0`, so every operator onto
them is surjective). -/
theorem isInGeneralPosition_witness (n : ℕ) :
    IsInGeneralPosition (StrongBundleEquivalenceExamples.epSEP n 0)
      (fiberZero (StrongBundleEquivalenceExamples.epSEP n 0).P)
      (zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)) ∧
    ∀ x, 0 < zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)
      (fiberZero (StrongBundleEquivalenceExamples.epSEP n 0).P x) := by
  classical
  refine ⟨fun x _ L _ φ hφ hx k V T _ w => ?_, fun x => ?_⟩
  · refine ⟨0, Subtype.ext (Prod.ext ?_ (funext fun i => i.elim0))⟩
    have h1 := ((L.domRestrict (reducedTangentFiber hφ hx T)) 0).2
    have h2 := w.2
    exact (h1.trans h2.symm)
  · unfold zeroMultisection
    rw [if_pos]
    · exact one_pos
    · rfl

end SBLocalization

end Polyfold
