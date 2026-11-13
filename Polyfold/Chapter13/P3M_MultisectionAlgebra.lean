import Polyfold.Chapter13.P3M_MultisectionConvolution

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.2, **Definition 13.2.9**, **Definition 13.2.10** and **Lemma 13.2.11** (pp. 611–612;
2017: Definitions 13.9, 13.10, Lemma 13.11), at the level of the functors `Λ : W → ℚ⁺`.

# Sums and scalar multiples of sc⁺-multisections

## The text, paraphrased

(Definition 13.2.9) For decorated sc⁺-multisections `Λ'`, `Λ''`, the sum is
(1) `(Λ' ⊕ Λ'')(w) = ∑_{w' + w'' = w, w', w'' ∈ W_{P(w)}} Λ'(w')·Λ''(w'')`, decorated by (2) the
neighbourhoods `U(x) ∩ U'(x)` and (3) the index sets `I_x × I'_x` with the sections
`s_i + s'_{i'}`.  The sum is associative and commutative.
(Definition 13.2.10) `(0Λ)(w) = 1` for `w = 0` and `0` otherwise; `(aΛ)(w) = Λ(w/a)` for
`a ≠ 0`, decorated by the sections `a·sᵢ`.
(Lemma 13.2.11) For an sc-smooth functor `β : X → ℝ`, `(β ⊙ Λ)(w) = (β(P(w))Λ)(w)` is a
decorated sc⁺-multisection.

## What is formalized (namespace `Polyfold.SBLocalization`)

The decorations need good systems of neighbourhoods (§13.1); here the functors and their local
section structures (the data (2), (3) on one domain) are treated.
* Definition 13.2.9: `multisectionAdd` (formula (1)); `multisectionAdd_eq_conv` (the convolution
  of the pair); `multisectionAdd_eq_sum_of_isLocalRepOn` (the local sections `s_i + s'_{i'}` with
  weights `σ_i σ'_{i'}`, data (3)); **`definition_13_2_9`**: `Λ' ⊕ Λ''` is an
  sc⁺-multisection; `multisectionAdd_comm` (for all functions), `multisectionAdd_assoc` (for
  sc⁺-multisections).
* Definition 13.2.10: `multisectionSmul`; `multisectionSmul_zero` (`0Λ` is the multisection of
  the zero section); `multisectionSmul_eq_sum_of_isLocalRepOn` (the sections `a·sᵢ`);
  **`definition_13_2_10`**: `aΛ` is an sc⁺-multisection.
* Lemma 13.2.11: `multisectionSmulFun`; **`lemma_13_2_11`** (functor level).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle

variable {A : SEP.{u}}

/-! ### Definition 13.2.9 -/

/-- The sum over the fibre `W_x`: `∑_{w' + w'' = w} Λ'(w')·Λ''(w'')`. -/
def addAt (Λ' Λ'' : A.W → ℚ≥0) (x : A.Obj) (w : A.W) : ℚ≥0 :=
  ∑ᶠ p : A.P ⁻¹' {x} × A.P ⁻¹' {x},
    if ((p.1 + p.2 : A.P ⁻¹' {x}) : A.W) = w then Λ' p.1 * Λ'' p.2 else 0

/-- **2021 Definition 13.2.9 (1), p. 611 (2017: Definition 13.9)**: the sum
`(Λ' ⊕ Λ'')(w) = ∑_{(w', w''), w', w'' ∈ W|P(w), w' + w'' = w} Λ'(w')·Λ''(w'')`. -/
def multisectionAdd (Λ' Λ'' : A.W → ℚ≥0) (w : A.W) : ℚ≥0 :=
  addAt Λ' Λ'' (A.P w) w

theorem multisectionAdd_eq_addAt (Λ' Λ'' : A.W → ℚ≥0) {x : A.Obj} {w : A.W} (hw : A.P w = x) :
    multisectionAdd Λ' Λ'' w = addAt Λ' Λ'' x w := by
  unfold multisectionAdd; rw [hw]

theorem addAt_eq_convAt (Λ' Λ'' : A.W → ℚ≥0) (x : A.Obj) (w : A.W) :
    addAt Λ' Λ'' x w = convAt ![Λ', Λ''] x w := by
  unfold addAt convAt
  rw [← finsum_comp_equiv (piFinTwoEquiv fun _ => A.P ⁻¹' {x})]
  refine finsum_congr fun v => ?_
  simp [piFinTwoEquiv, Fin.sum_univ_two, Fin.prod_univ_two]

/-- `Λ' ⊕ Λ''` is the convolution of the pair `(Λ', Λ'')`. -/
theorem multisectionAdd_eq_conv (Λ' Λ'' : A.W → ℚ≥0) :
    multisectionAdd Λ' Λ'' = conv ![Λ', Λ''] :=
  funext fun w => addAt_eq_convAt Λ' Λ'' (A.P w) w

/-- The sum over a fibre from finite descriptions of the two summands. -/
theorem addAt_eq_sum {Λ' Λ'' : A.W → ℚ≥0} {x : A.Obj} {K' K'' : Type*} [Fintype K']
    [Fintype K''] (a' : K' → A.P ⁻¹' {x}) (σ' : K' → ℚ≥0) (a'' : K'' → A.P ⁻¹' {x})
    (σ'' : K'' → ℚ≥0) (hΛ' : ∀ u : A.P ⁻¹' {x}, Λ' u = ∑ k, if u = a' k then σ' k else 0)
    (hΛ'' : ∀ u : A.P ⁻¹' {x}, Λ'' u = ∑ k, if u = a'' k then σ'' k else 0) (w : A.W) :
    addAt Λ' Λ'' x w = ∑ κ : K' × K'',
      if ((a' κ.1 + a'' κ.2 : A.P ⁻¹' {x}) : A.W) = w then σ' κ.1 * σ'' κ.2 else 0 := by
  have hprod : ∀ p : A.P ⁻¹' {x} × A.P ⁻¹' {x}, Λ' p.1 * Λ'' p.2 =
      ∑ κ : K' × K'', if p = (a' κ.1, a'' κ.2) then σ' κ.1 * σ'' κ.2 else 0 := fun p => by
    rw [hΛ', hΛ'', Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k'' _ => ?_
    rw [ite_zero_mul_ite_zero]
    exact if_congr ⟨fun h => Prod.ext h.1 h.2,
      fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩ rfl rfl
  have hterm : ∀ p : A.P ⁻¹' {x} × A.P ⁻¹' {x},
      (if ((p.1 + p.2 : A.P ⁻¹' {x}) : A.W) = w then Λ' p.1 * Λ'' p.2 else 0) =
      ∑ κ : K' × K'', if p = (a' κ.1, a'' κ.2) then
        (if ((a' κ.1 + a'' κ.2 : A.P ⁻¹' {x}) : A.W) = w then σ' κ.1 * σ'' κ.2 else 0)
        else 0 := fun p => by
    rw [hprod p]
    split_ifs with hc
    · refine Finset.sum_congr rfl fun κ _ => ?_
      split_ifs with h1 h2
      · rfl
      · subst h1; exact absurd hc h2
      · rfl
    · refine (Finset.sum_eq_zero fun κ _ => ?_).symm
      split_ifs with h1 h2
      · subst h1; exact absurd h2 hc
      · rfl
      · rfl
  unfold addAt
  simp_rw [hterm]
  rw [finsum_sum_comm]
  · refine Finset.sum_congr rfl fun κ _ => ?_
    rw [finsum_eq_single _ (a' κ.1, a'' κ.2) fun p hp => if_neg hp, if_pos rfl]
  · intro κ _
    refine (finite_singleton (a' κ.1, a'' κ.2)).subset fun p hp => ?_
    by_contra hne
    exact hp (if_neg hne)

/-- **Definition 13.2.9 (3), on one domain**: if `Λ'` and `Λ''` have the local representations
`(s'_i, σ'_i)` and `(s''_j, σ''_j)` on `O` (global sections), then `Λ' ⊕ Λ''` is given on `O` by the
sections `s'_i + s''_j` with the weights `σ'_i σ''_j`. -/
theorem multisectionAdd_eq_sum_of_isLocalRepOn {Λ' Λ'' : A.W → ℚ≥0} {O : Set A.Obj}
    {k' k'' : ℕ} {s' : Fin k' → A.Obj → A.W} {σ' : Fin k' → ℚ≥0}
    {s'' : Fin k'' → A.Obj → A.W} {σ'' : Fin k'' → ℚ≥0} (h' : IsLocalRepOn A Λ' O s' σ')
    (h'' : IsLocalRepOn A Λ'' O s'' σ'') (hs' : ∀ i, IsSection A.P (s' i))
    (hs'' : ∀ j, IsSection A.P (s'' j)) {w : A.W} (hw : A.P w ∈ O) :
    multisectionAdd Λ' Λ'' w = ∑ i, ∑ j,
      if w = Polyfold.sectionAdd A.P (s' i) (s'' j) (A.P w) then σ' i * σ'' j else 0 := by
  rw [multisectionAdd, addAt_eq_sum (fun i => ⟨s' i (A.P w), (h'.2.1 i).1 _ hw⟩) σ'
    (fun j => ⟨s'' j (A.P w), (h''.2.1 j).1 _ hw⟩) σ'' (fun u => h'.apply_fib hw u)
    (fun u => h''.apply_fib hw u) w, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => if_congr ?_ rfl rfl
  rw [sectionAdd_apply (hs' i) (hs'' j)]
  exact eq_comm

/-- **2021 Definition 13.2.9, p. 611 (2017: Definition 13.9), functor level**: the sum
`Λ' ⊕ Λ''` of two sc⁺-multisections is an sc⁺-multisection (its local section structures are
those of `multisectionAdd_eq_sum_of_isLocalRepOn`). -/
theorem definition_13_2_9 {Λ' Λ'' : A.W → ℚ≥0} (h' : IsScPlusMultisection A Λ')
    (h'' : IsScPlusMultisection A Λ'') : IsScPlusMultisection A (multisectionAdd Λ' Λ'') := by
  rw [multisectionAdd_eq_conv]
  exact isScPlusMultisection_conv fun i => by
    fin_cases i
    · exact h'
    · exact h''

/-- **Definition 13.2.9, "commutative"**: `Λ' ⊕ Λ'' = Λ'' ⊕ Λ'` (for all functions). -/
theorem multisectionAdd_comm (Λ' Λ'' : A.W → ℚ≥0) :
    multisectionAdd Λ' Λ'' = multisectionAdd Λ'' Λ' := by
  funext w
  unfold multisectionAdd addAt
  rw [← finsum_comp_equiv (Equiv.prodComm _ _)]
  refine finsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  exact if_congr (by rw [add_comm]) (mul_comm _ _) rfl

/-- An sc⁺-multisection over a point, as a finite sum over the fibre. -/
theorem IsScPlusMultisection.exists_fib_rep {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (x : A.Obj) : ∃ (k : ℕ) (a : Fin k → A.P ⁻¹' {x}) (σ : Fin k → ℚ≥0),
      ∀ u : A.P ⁻¹' {x}, Λ u = ∑ i, if u = a i then σ i else 0 := by
  obtain ⟨O, k, s, σ, -, hx, h⟩ := hΛ.exists_isLocalRepOn x
  exact ⟨k, _, σ, fun u => h.apply_fib hx u⟩

/-- The sum over a fibre, in the form of the fibre descriptions (to iterate `addAt_eq_sum`). -/
theorem multisectionAdd_fib_rep {Λ' Λ'' : A.W → ℚ≥0} {x : A.Obj} {K' K'' : Type*} [Fintype K']
    [Fintype K''] (a' : K' → A.P ⁻¹' {x}) (σ' : K' → ℚ≥0) (a'' : K'' → A.P ⁻¹' {x})
    (σ'' : K'' → ℚ≥0) (hΛ' : ∀ u : A.P ⁻¹' {x}, Λ' u = ∑ k, if u = a' k then σ' k else 0)
    (hΛ'' : ∀ u : A.P ⁻¹' {x}, Λ'' u = ∑ k, if u = a'' k then σ'' k else 0)
    (u : A.P ⁻¹' {x}) :
    multisectionAdd Λ' Λ'' u = ∑ κ : K' × K'',
      if u = a' κ.1 + a'' κ.2 then σ' κ.1 * σ'' κ.2 else 0 := by
  rw [multisectionAdd_eq_addAt _ _ u.2, addAt_eq_sum a' σ' a'' σ'' hΛ' hΛ'']
  refine Finset.sum_congr rfl fun κ _ => if_congr ?_ rfl rfl
  exact ⟨fun e => (Subtype.ext e).symm, fun e => by rw [e]⟩

/-- **Definition 13.2.9, "associative"**: `(Λ₁ ⊕ Λ₂) ⊕ Λ₃ = Λ₁ ⊕ (Λ₂ ⊕ Λ₃)` for
sc⁺-multisections (over each fibre both sides are `∑ [a₁ + a₂ + a₃ = w] σ₁σ₂σ₃`). -/
theorem multisectionAdd_assoc {Λ₁ Λ₂ Λ₃ : A.W → ℚ≥0} (h₁ : IsScPlusMultisection A Λ₁)
    (h₂ : IsScPlusMultisection A Λ₂) (h₃ : IsScPlusMultisection A Λ₃) :
    multisectionAdd (multisectionAdd Λ₁ Λ₂) Λ₃ = multisectionAdd Λ₁ (multisectionAdd Λ₂ Λ₃) := by
  funext w
  set x := A.P w
  obtain ⟨k₁, a₁, σ₁, r₁⟩ := h₁.exists_fib_rep x
  obtain ⟨k₂, a₂, σ₂, r₂⟩ := h₂.exists_fib_rep x
  obtain ⟨k₃, a₃, σ₃, r₃⟩ := h₃.exists_fib_rep x
  have r₁₂ := multisectionAdd_fib_rep a₁ σ₁ a₂ σ₂ r₁ r₂
  have r₂₃ := multisectionAdd_fib_rep a₂ σ₂ a₃ σ₃ r₂ r₃
  rw [multisectionAdd_eq_addAt _ _ rfl, multisectionAdd_eq_addAt _ _ rfl,
    addAt_eq_sum (fun κ : Fin k₁ × Fin k₂ => a₁ κ.1 + a₂ κ.2) (fun κ => σ₁ κ.1 * σ₂ κ.2) a₃ σ₃
      r₁₂ r₃,
    addAt_eq_sum a₁ σ₁ (fun κ : Fin k₂ × Fin k₃ => a₂ κ.1 + a₃ κ.2) (fun κ => σ₂ κ.1 * σ₃ κ.2)
      r₁ r₂₃,
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, add_assoc, mul_assoc]

/-! ### Definition 13.2.10 -/

/-- The scalar multiple over the fibre `W_x`: `(0Λ)(u) = [u = 0]`, `(aΛ)(u) = Λ(u/a)`. -/
def smulAt (a : ℝ) (Λ : A.W → ℚ≥0) (x : A.Obj) (u : A.P ⁻¹' {x}) : ℚ≥0 :=
  if a = 0 then (if u = 0 then 1 else 0) else Λ ((a⁻¹ • u : A.P ⁻¹' {x}) : A.W)

/-- **2021 Definition 13.2.10, p. 611 (2017: Definition 13.10)**: the scalar multiple `aΛ`:
`(0Λ)(w) = 0` for `w ≠ 0`, `(0Λ)(0) = 1`, and `(aΛ)(w) = Λ(w/a)` for `a ≠ 0`. -/
def multisectionSmul (a : ℝ) (Λ : A.W → ℚ≥0) (w : A.W) : ℚ≥0 :=
  smulAt a Λ (A.P w) (toFib w)

theorem multisectionSmul_fib (a : ℝ) (Λ : A.W → ℚ≥0) {x : A.Obj} (u : A.P ⁻¹' {x}) :
    multisectionSmul a Λ u = smulAt a Λ x u :=
  fib_congr (smulAt a Λ) u.2 _ _ rfl

/-- `0Λ` is the multisection of the zero section. -/
theorem multisectionSmul_zero (Λ : A.W → ℚ≥0) : multisectionSmul 0 Λ = zeroMultisection A := by
  funext w
  unfold multisectionSmul smulAt zeroMultisection
  rw [if_pos rfl]
  exact if_congr ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩ rfl rfl

/-- The scalar multiple over a fibre from a finite description of `Λ` (the points `a·bₖ`). -/
theorem smulAt_eq_sum {Λ : A.W → ℚ≥0} {x : A.Obj} {K : Type*} [Fintype K]
    (b : K → A.P ⁻¹' {x}) (σ : K → ℚ≥0) (hsum : ∑ k, σ k = 1)
    (hΛ : ∀ u : A.P ⁻¹' {x}, Λ u = ∑ k, if u = b k then σ k else 0) (a : ℝ)
    (u : A.P ⁻¹' {x}) : smulAt a Λ x u = ∑ k, if u = a • b k then σ k else 0 := by
  unfold smulAt
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl]
    simp only [zero_smul]
    by_cases hu : u = 0
    · simp [hu, hsum]
    · simp [hu]
  · rw [if_neg ha, hΛ]
    refine Finset.sum_congr rfl fun k _ => if_congr ?_ rfl rfl
    exact inv_smul_eq_iff₀ ha

/-- **Definition 13.2.10, the local sections**: if `Λ` has the local representation `(sᵢ, σᵢ)` on
`O` (global sections), then `aΛ` is given on `O` by the sections `a·sᵢ` with the same weights. -/
theorem multisectionSmul_eq_sum_of_isLocalRepOn {Λ : A.W → ℚ≥0} {O : Set A.Obj} {k : ℕ}
    {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (h : IsLocalRepOn A Λ O s σ)
    (hs : ∀ i, IsSection A.P (s i)) (a : ℝ) {w : A.W} (hw : A.P w ∈ O) :
    multisectionSmul a Λ w =
      ∑ i, if w = Polyfold.sectionSmul A.P (fun _ => a) (s i) (A.P w) then σ i else 0 := by
  rw [multisectionSmul, smulAt_eq_sum _ σ h.2.2.1 (fun u => h.apply_fib hw u) a]
  refine Finset.sum_congr rfl fun i _ => if_congr ?_ rfl rfl
  rw [sectionSmul_apply (hs i)]
  exact ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩

theorem smulAt_map (a : ℝ) {Λ : A.W → ℚ≥0} {x y : A.Obj} (e : A.P ⁻¹' {x} ≃ₗ[ℝ] A.P ⁻¹' {y})
    (he : ∀ u : A.P ⁻¹' {x}, Λ (e u) = Λ u) (u : A.P ⁻¹' {x}) :
    smulAt a Λ y (e u) = smulAt a Λ x u := by
  unfold smulAt
  by_cases ha : a = 0
  · rw [if_pos ha, if_pos ha]
    exact if_congr (map_eq_zero_iff e e.injective) rfl rfl
  · rw [if_neg ha, if_neg ha, ← map_smul, he]

/-- The scalar multiple of a functor is a functor. -/
theorem isWFunctor_multisectionSmul (a : ℝ) {Λ : A.W → ℚ≥0} (hΛ : IsWFunctor A Λ) :
    IsWFunctor A (multisectionSmul a Λ) := by
  rintro ⟨⟨φ, w⟩, hq⟩
  have hq' : A.P w = A.X.src φ := hq
  set e := (A.E.fiberMorEquiv φ).toLinearEquiv
  have he : ∀ u : A.P ⁻¹' {A.X.src φ}, Λ (e u) = Λ u := fun u => hΛ ⟨(φ, (u : A.W)), u.2⟩
  have h1 := smulAt_map a e he ⟨w, hq'⟩
  have e1 : multisectionSmul a Λ (A.E.μ ⟨(φ, w), hq⟩) = smulAt a Λ (A.X.tgt φ) (e ⟨w, hq'⟩) :=
    fib_congr (smulAt a Λ) (A.E.P_μ _) _ _ (A.E.μ_congr rfl)
  have e2 : multisectionSmul a Λ w = smulAt a Λ (A.X.src φ) ⟨w, hq'⟩ :=
    fib_congr (smulAt a Λ) hq' _ _ rfl
  change multisectionSmul a Λ (A.E.μ ⟨(φ, w), hq⟩) = multisectionSmul a Λ w
  rw [e1, e2, h1]

/-- **2021 Definition 13.2.10, p. 611, functor level**: `aΛ` is an sc⁺-multisection, with the
local sections `a·sᵢ` (`multisectionSmul_eq_sum_of_isLocalRepOn`). -/
theorem definition_13_2_10 {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (a : ℝ) :
    IsScPlusMultisection A (multisectionSmul a Λ) := by
  refine ⟨isWFunctor_multisectionSmul a hΛ.1, fun x => ?_⟩
  obtain ⟨O, k, s, σ, hO, hx, h⟩ := hΛ.exists_isLocalRepOn x
  have h' := h.extendZero
  have hs : ∀ i, IsSection A.P (extendZero O (s i)) := fun i => isSection_extendZero _ _
  refine hasLocalSectionStructure_of_isLocalRepOn hO hx (s := fun i =>
    Polyfold.sectionSmul A.P (fun _ => a) (extendZero O (s i))) (σ := σ)
    ⟨h.1, fun i => (h'.2.1 i).sectionSmul_const hO (hs i) a, h.2.2.1, fun w hw => ?_⟩
  exact multisectionSmul_eq_sum_of_isLocalRepOn h' hs a hw

/-! ### Lemma 13.2.11 -/

/-- **`β ⊙ Λ`** (Lemma 13.2.11, p. 612): `(β ⊙ Λ)(w) = (β(P(w))Λ)(w)`. -/
def multisectionSmulFun (β : A.Obj → ℝ) (Λ : A.W → ℚ≥0) (w : A.W) : ℚ≥0 :=
  multisectionSmul (β (A.P w)) Λ w

/-- **2021 Lemma 13.2.11, p. 612 (2017: Lemma 13.11), functor level**: for an sc-smooth functor
`β : X → ℝ` (`β(x) = β(x')` along morphisms) and an sc⁺-multisection `Λ`, `β ⊙ Λ` is an
sc⁺-multisection, with the local sections `β·sᵢ`. -/
theorem lemma_13_2_11 {β : A.Obj → ℝ} (hβ : ∀ φ : A.Mor, β (A.X.tgt φ) = β (A.X.src φ))
    (hβs : A.X.PObj.IsScSmoothMap realPolyfold β) {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) : IsScPlusMultisection A (multisectionSmulFun β Λ) := by
  refine ⟨fun q => ?_, fun x => ?_⟩
  · obtain ⟨⟨φ, w⟩, hq⟩ := q
    have hq' : A.P w = A.X.src φ := hq
    change multisectionSmul (β (A.P (A.E.μ ⟨(φ, w), hq⟩))) Λ (A.E.μ ⟨(φ, w), hq⟩) =
      multisectionSmul (β (A.P w)) Λ w
    rw [A.E.P_μ, hβ, ← hq']
    exact isWFunctor_multisectionSmul _ hΛ.1 ⟨(φ, w), hq⟩
  · obtain ⟨O, k, s, σ, hO, hx, h⟩ := hΛ.exists_isLocalRepOn x
    have h' := h.extendZero
    have hs : ∀ i, IsSection A.P (extendZero O (s i)) := fun i => isSection_extendZero _ _
    refine hasLocalSectionStructure_of_isLocalRepOn hO hx (s := fun i =>
      Polyfold.sectionSmul A.P β (extendZero O (s i))) (σ := σ)
      ⟨h.1, fun i => (h'.2.1 i).sectionSmul hO (hs i) hβs, h.2.2.1, fun w hw => ?_⟩
    exact multisectionSmul_eq_sum_of_isLocalRepOn h' hs (β (A.P w)) hw

end SBLocalization

end Polyfold
