import Polyfold.Chapter14.P3W5T9_SumSections
import Polyfold.Chapter14.P3W4GL_NormControl

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.5, pp. 676–678:
the assembly of `Λ'` in the proof of **Theorem 14.1.9** (the ∂-Extension Theorem) (2017: §14.5,
Theorem 14.2).

# The assembly of the extension

## The text, paraphrased

On `V̂_b` the summed structures `s̃ᵇ` define `Λ'_b`, compatible along the `τ̂_{b,b'}`.  Points
`|x| ∉ ⋃ |V̂_b|` get a neighbourhood `V̂_x` with the natural action on which the sections vanish,
`I_x = {1}`, the zero section, and `τ̂_{b,x} = [I_b ← I_b → {1}]`, `τ̂_{x,b}` its reverse,
`τ̂_{x,x'} = [{1} ← {1} → {1}]`.  The resulting global `Λ'` extends `Λ`; it is structurable by
Theorem 14.5.5.  The size control multiplies by a cut-off functor.

## What is formalized (namespace `Polyfold.SBLocalization.AssemblyInput`)

* `mult σ`: the functor `Λ'` (with the cut-off `σ` folded into the sections), computed in any
  chart `V̂_b` (`mult_eq`), a functor (`isWFunctor_mult`).
* `crit`: the data of Theorem 14.5.5 (GL's `CriterionData`), indexed by `A ⊔ X`: the `V̂_b` with
  the `σ·s̃ᵇ`, and for every object `x` the invariant core of `X ∖ C` in a neighbourhood of `x`
  with the zero section and the correspondences of the text.
* `CriterionData.hasLocalSectionStructure_t9`: the criterion's data and a functor give an
  sc⁺-multisection (local structures transported by `t`); hence `isStructurable_mult`.
* `mult_boundary`: `Λ'|∂X = Λ` when `σ = 1` on `dom-supp(Λ)`; `domSupp_mult_subset`.
* `exists_cutoff`: the cut-off `σ` (Urysohn on the normal space `|X|`) with `σ = 1` on
  `dom-supp(Λ)` and `tsupport σ ⊆ Ũ`.
* **`AssemblyInput.extension`**: the conclusion of GL's `theorem_14_1_9_extension_statement` for
  `Λ` with an `AssemblyInput`.
* **`theorem_14_1_9_extension_statement_of_assembly`** and **`theorem_14_1_9_of_assembly`**:
  Theorem 14.1.9 from `AssemblyHyp A` (every structurable `Λ` over `∂X` has the data of
  §§14.3–14.5), with the witness `assemblyHyp_of_boundary_eq_empty`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid EpGroupoid.ZSetup

variable {A : SEP.{u}}

/-! ### Fibre maps -/

theorem fibAct_eq_fiberZero_iff_t9 {ψ : A.Mor} {w : A.W} (hw : A.P w = A.X.src ψ) :
    fibAct ψ w = fiberZero A.P (A.X.tgt ψ) ↔ w = fiberZero A.P (A.X.src ψ) := by
  constructor
  · intro h
    have e := AtomicStructData.fibAct_inv_fibAct hw
    rw [h, fibAct_fiberZero (A.X.src_inv ψ) (A.X.tgt_inv ψ)] at e
    exact e.symm
  · rintro rfl
    exact fibAct_fiberZero rfl rfl

theorem fibAct_comp_inv_t9 {φ ψ : A.Mor} {w : A.W} (hw : A.P w = A.X.src ψ)
    (h : A.X.src φ = A.X.src ψ) :
    fibAct (A.X.comp φ (A.X.inv ψ)) (fibAct ψ w) = fibAct φ w := by
  have hv : A.P (fibAct ψ w) = A.X.src (A.X.inv ψ) := by
    rw [P_fibAct hw, A.X.src_inv]
  rw [AtomicStructData.fibAct_comp hv (by rw [A.X.tgt_inv, h]),
    AtomicStructData.fibAct_inv_fibAct hw]

/-! ### Local structures from the criterion's data -/

/-- **The data of Theorem 14.5.5 and a functor give local section structures**: near `y`, the
structure of a `V_a` transported by a local inverse of `t`. -/
theorem CriterionData.hasLocalSectionStructure_t9 {Λ : A.W → ℚ≥0} (E : CriterionData A Λ)
    (hfun : IsWFunctor A Λ) (hne : ∀ a, Nonempty (E.I a)) (y : A.Obj) :
    HasLocalSectionStructure A Λ y := by
  obtain ⟨a, O, τ, hO, hyO, hτ, h⟩ := E.exists_transport y
  have := hne a
  have hc : (Fintype.card (E.I a) : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hP : ∀ i, ∀ z ∈ O, A.P (E.s a i (A.X.src (τ z))) = A.X.src (τ z) := fun i z hz =>
    (E.isScPlusSectionOn a i).1 _ (h z hz).2
  refine hasLocalSectionStructure_of_isLocalRepOn hO hyO
    (isLocalRepOn_of_fintype (K := E.I a)
      (fun i => transportSection τ fun z => E.s a i (A.X.src (τ z)))
      (fun _ => (Fintype.card (E.I a) : ℚ≥0)⁻¹) (fun _ => inv_pos.2 (pos_iff_ne_zero.2 hc))
      (fun i => ?_) ?_ fun w hw => ?_)
  · obtain ⟨-, G, hG, hGs⟩ := E.isScPlusSectionOn a i
    have hsτ : A.X.PObj.IsScSmoothOn A.X.PObj (A.X.src ∘ τ) O :=
      MPolyfold.IsScSmoothOn.comp A.X.isScSmoothMap_src hτ (mapsTo_univ _ _)
    exact isScPlusSectionOn_transportSection hτ (G := G ∘ (A.X.src ∘ τ))
      (fun z hz => hG _ (h z hz).2) (MPolyfold.IsScSmoothOn.comp hGs hsτ fun z hz => (h z hz).2)
      (fun z hz => hP i z hz) fun z hz => (h z hz).1
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hc]
  · set ψ := τ (A.P w)
    have htψ : A.X.tgt ψ = A.P w := (h _ hw).1
    have hsψ : A.X.src ψ ∈ E.V a := (h _ hw).2
    have hwi : A.P w = A.X.src (A.X.inv ψ) := by rw [A.X.src_inv, htψ]
    have hw' : A.P (fibAct (A.X.inv ψ) w) = A.X.src ψ := by
      rw [P_fibAct hwi, A.X.tgt_inv]
    have hΛ : Λ (fibAct (A.X.inv ψ) w) = Λ w := by
      rw [fibAct_of hwi]; exact hfun ⟨(A.X.inv ψ, w), hwi⟩
    rw [← hΛ, E.rep a _ (by rw [hw']; exact hsψ), hw', Finset.natCast_card_filter,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs : transportSection τ (fun z => E.s a i (A.X.src (τ z))) (A.P w) =
        fibAct ψ (E.s a i (A.X.src ψ)) :=
      AtomicStructData.transportSection_eq_fibAct (hP i _ hw)
    have hiff : E.s a i (A.X.src ψ) = fibAct (A.X.inv ψ) w ↔
        w = transportSection τ (fun z => E.s a i (A.X.src (τ z))) (A.P w) := by
      rw [hs]
      constructor
      · intro e
        rw [e]
        exact (AtomicStructData.fibAct_fibAct_inv (htψ.symm ▸ rfl)).symm
      · intro e
        rw [e]
        exact (AtomicStructData.fibAct_inv_fibAct (hP i _ hw)).symm
    by_cases hi : E.s a i (A.X.src ψ) = fibAct (A.X.inv ψ) w
    · rw [if_pos hi, if_pos (hiff.1 hi), mul_one]
    · rw [if_neg hi, if_neg fun e => hi (hiff.2 e), mul_zero]

namespace AssemblyInput

variable {Λ : A.W → ℚ≥0} (D : AssemblyInput A Λ)

/-! ### The functor `Λ'` -/

/-- **The functor `Λ'`** (the cut-off `σ` included): in a chart `φ : P(w) → t(φ) ∈ V̂_b`, the
count `|I_b|⁻¹·#{j | σ·s̃ᵇⱼ(t φ) = μ(φ, w)}`; trivial where no chart exists. -/
def mult (σ : A.Obj → ℝ) (w : A.W) : ℚ≥0 :=
  if h : ∃ p : D.S.A × A.Mor, A.X.src p.2 = A.P w ∧ A.X.tgt p.2 ∈ D.S.V p.1 then
    (Fintype.card (D.S.I h.choose.1) : ℚ≥0)⁻¹ *
      ((Finset.univ.filter fun j =>
        D.ssec σ h.choose.1 j (A.X.tgt h.choose.2) = fibAct h.choose.2 w).card : ℚ≥0)
  else if w = fiberZero A.P (A.P w) then 1 else 0

variable {σ : A.Obj → ℝ}

/-- **`Λ'` in any chart.** -/
theorem mult_eq (hσt : ∀ φ : A.Mor, σ (A.X.tgt φ) = σ (A.X.src φ)) {b : A.Obj}
    (hb : b ∈ D.S.A) {w : A.W} {φ : A.Mor} (hs : A.X.src φ = A.P w)
    (ht : A.X.tgt φ ∈ D.S.V b) :
    D.mult σ w = (Fintype.card (D.S.I b) : ℚ≥0)⁻¹ *
      ((Finset.univ.filter fun j => D.ssec σ b j (A.X.tgt φ) = fibAct φ w).card : ℚ≥0) := by
  have hex : ∃ p : D.S.A × A.Mor, A.X.src p.2 = A.P w ∧ A.X.tgt p.2 ∈ D.S.V p.1 :=
    ⟨(⟨b, hb⟩, φ), hs, ht⟩
  unfold mult
  rw [dif_pos hex]
  obtain ⟨hs', ht'⟩ := hex.choose_spec
  set b' := hex.choose.1
  set φ' := hex.choose.2
  have hsχ : A.X.src (A.X.comp φ (A.X.inv φ')) = A.X.tgt φ' := by
    rw [A.X.src_comp _ _ (by rw [A.X.tgt_inv, hs, hs']), A.X.src_inv]
  have htχ : A.X.tgt (A.X.comp φ (A.X.inv φ')) = A.X.tgt φ := by
    rw [A.X.tgt_comp _ _ (by rw [A.X.tgt_inv, hs, hs'])]
  have hχ : A.X.comp φ (A.X.inv φ') ∈ A.X.morBetween (D.S.V b') (D.S.V b) := by
    refine ⟨?_, ?_⟩
    · rw [hsχ]; exact ht'
    · rw [htχ]; exact ht
  have hsat := D.ssec_compat hσt b'.2 hb hχ
  rw [hsχ, htχ] at hsat
  have hw' : A.P w = A.X.src φ' := hs'.symm
  have hinj : InjOn (fibAct (A.X.comp φ (A.X.inv φ'))) (A.P ⁻¹' {A.X.tgt φ'}) :=
    fun v hv v' hv' e => by
      have h1 : A.P v = A.X.src (A.X.comp φ (A.X.inv φ')) := by rw [hsχ]; exact hv
      have h2 : A.P v' = A.X.src (A.X.comp φ (A.X.inv φ')) := by rw [hsχ]; exact hv'
      rw [← AtomicStructData.fibAct_inv_fibAct h1, e, AtomicStructData.fibAct_inv_fibAct h2]
  have := IndexCorr.count_eq_of_sat hinj (fun j => D.isSection_ssec σ b' j _) hsat
    (v := fibAct φ' w) (P_fibAct hw')
  rw [fibAct_comp_inv_t9 hw' (hs.trans hs'.symm)] at this
  exact this

theorem P_ssec_ne {b : A.Obj} {j : D.S.I b} {y : A.Obj} : A.P (D.ssec σ b j y) = y :=
  D.isSection_ssec σ b j y

theorem not_mem_C_of_src {φ : A.Mor} (h : A.X.src φ ∉ D.C) : A.X.tgt φ ∉ D.C := fun ht => by
  have := A.X.isSaturated_iff.1 D.isSaturated_C (A.X.inv φ) (by rw [A.X.src_inv]; exact ht)
  rw [A.X.tgt_inv] at this
  exact h this

theorem not_mem_C_of_tgt {φ : A.Mor} (h : A.X.tgt φ ∉ D.C) : A.X.src φ ∉ D.C := fun hs =>
  h (A.X.isSaturated_iff.1 D.isSaturated_C φ hs)

/-- Off `C`, `Λ'` is trivial. -/
theorem mult_of_not_mem_C {w : A.W} (hw : A.P w ∉ D.C) :
    D.mult σ w = if w = fiberZero A.P (A.P w) then 1 else 0 := by
  unfold mult
  split_ifs with h h0 h0
  · obtain ⟨hs, -⟩ := h.choose_spec
    have := D.nonempty_I _ h.choose.1.2
    have hc : (Fintype.card (D.S.I h.choose.1) : ℚ≥0) ≠ 0 :=
      Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have htC : A.X.tgt h.choose.2 ∉ D.C := D.not_mem_C_of_src (by rw [hs]; exact hw)
    rw [Finset.filter_true_of_mem fun j _ => ?_, Finset.card_univ, inv_mul_cancel₀ hc]
    rw [D.ssec_eq_zero_of_not_mem_C σ j htC]
    exact ((fibAct_eq_fiberZero_iff_t9 hs.symm).2 (by rw [hs]; exact h0)).symm
  · obtain ⟨hs, -⟩ := h.choose_spec
    have htC : A.X.tgt h.choose.2 ∉ D.C := D.not_mem_C_of_src (by rw [hs]; exact hw)
    rw [Finset.filter_false_of_mem fun j _ => ?_, Finset.card_empty, Nat.cast_zero, mul_zero]
    rw [D.ssec_eq_zero_of_not_mem_C σ j htC]
    intro e
    exact h0 ((fibAct_eq_fiberZero_iff_t9 hs.symm).1 e.symm |>.trans (by rw [hs]))
  · rfl
  · rfl

theorem isWFunctor_mult (hσt : ∀ φ : A.Mor, σ (A.X.tgt φ) = σ (A.X.src φ)) :
    IsWFunctor A (D.mult σ) := by
  rintro ⟨⟨ψ, w⟩, hq⟩
  have hq' : A.P w = A.X.src ψ := hq
  change D.mult σ (A.E.μ ⟨(ψ, w), hq⟩) = D.mult σ w
  rw [← fibAct_of hq']
  have hPμ : A.P (fibAct ψ w) = A.X.tgt ψ := P_fibAct hq'
  by_cases h : ∃ p : D.S.A × A.Mor, A.X.src p.2 = A.P w ∧ A.X.tgt p.2 ∈ D.S.V p.1
  · obtain ⟨⟨b, φ⟩, hs, ht⟩ := h
    have hc : A.X.src φ = A.X.tgt (A.X.inv ψ) := by rw [A.X.tgt_inv, hs, hq']
    rw [D.mult_eq hσt b.2 hs ht,
      D.mult_eq hσt b.2 (φ := A.X.comp φ (A.X.inv ψ))
        (by rw [A.X.src_comp _ _ hc, A.X.src_inv, hPμ]) (by rw [A.X.tgt_comp _ _ hc]; exact ht),
      A.X.tgt_comp _ _ hc, fibAct_comp_inv_t9 hq' (hs.trans hq')]
  · have h' : ¬ ∃ p : D.S.A × A.Mor,
        A.X.src p.2 = A.P (fibAct ψ w) ∧ A.X.tgt p.2 ∈ D.S.V p.1 := by
      rintro ⟨⟨b, φ⟩, hs, ht⟩
      have hc : A.X.src φ = A.X.tgt ψ := hs.trans hPμ
      exact h ⟨(b, A.X.comp φ ψ), by rw [A.X.src_comp _ _ hc, hq'], by
        rw [A.X.tgt_comp _ _ hc]; exact ht⟩
    unfold mult
    rw [dif_neg h, dif_neg h', hPμ, hq', fibAct_eq_fiberZero_iff_t9 hq']

/-! ### The data of Theorem 14.5.5 -/

/-- A neighbourhood with the natural action, for every object. -/
def Nx (x : A.Obj) : A.X.NatNbhd x :=
  Classical.choose (A.X.exists_natNbhd_isProperSubset x isOpen_univ (mem_univ x))

/-- The points `a ∈ A` and all objects `x`. -/
def pt : D.S.A ⊕ A.Obj → A.Obj
  | .inl a => a.1
  | .inr x => x

/-- `Ũ(a)`, resp. a neighbourhood of `x`. -/
def critN : ∀ i : D.S.A ⊕ A.Obj, A.X.NatNbhd (D.pt i)
  | .inl a => D.S.nbhd a.1
  | .inr x => Nx x

/-- `V̂_a`, resp. the invariant core of `X ∖ C` in the neighbourhood of `x`. -/
def critV : D.S.A ⊕ A.Obj → Set A.Obj
  | .inl a => D.S.V a.1
  | .inr x => (Nx x).invariantCore D.Cᶜ

/-- `I_a`, resp. `{1}`. -/
def critI : D.S.A ⊕ A.Obj → Type u
  | .inl a => D.S.I a.1
  | .inr _ => PUnit.{u + 1}

instance critFintype : ∀ i, Fintype (D.critI i)
  | .inl a => (inferInstance : Fintype (D.S.I a.1))
  | .inr _ => (inferInstance : Fintype PUnit.{u + 1})

instance critMulAction : ∀ i, MulAction (A.X.Isotropy (D.pt i)) (D.critI i)
  | .inl a => (inferInstance : MulAction (A.X.Isotropy a.1) (D.S.I a.1))
  | .inr x => (inferInstance : MulAction (A.X.Isotropy x) PUnit.{u + 1})

/-- `σ·s̃ᵇ`, resp. the zero section. -/
def critS (σ : A.Obj → ℝ) : ∀ i, D.critI i → A.Obj → A.W
  | .inl a => fun j => D.ssec σ a.1 j
  | .inr _ => fun _ => fiberZero A.P

/-- `τ̂_{b,b'}`, `[I_b ← I_b → {1}]`, `[{1} ← I_b → I_b]`, `[{1} ← {1} → {1}]`. -/
def critτ : ∀ i i' : D.S.A ⊕ A.Obj, A.Mor → IndexCorr (D.critI i) (D.critI i')
  | .inl b, .inl b' => D.S.τ b.1 b'.1
  | .inl b, .inr _ => fun _ => haveI := D.nonempty_I b.1 b.2
      (IndexCorr.toUnit (D.S.I b.1)).swap
  | .inr _, .inl b => fun _ => haveI := D.nonempty_I b.1 b.2
      IndexCorr.toUnit (D.S.I b.1)
  | .inr _, .inr _ => fun _ => IndexCorr.ofEquiv (Equiv.refl PUnit.{u + 1})

theorem critV_inr_not_mem {x y : A.Obj} (hy : y ∈ D.critV (.inr x)) : y ∉ D.C :=
  ((Nx x).invariantCore_subset _ hy).2

theorem critV_inr_mem_U {x y : A.Obj} (hy : y ∈ D.critV (.inr x)) : y ∈ (Nx x).U :=
  ((Nx x).invariantCore_subset _ hy).1

/-! #### The correspondences with `{1}` -/

section Unit

variable {β : Type u} [Fintype β] [Nonempty β] {G G' : Type*} [Group G] [Group G']

theorem biact_toUnit_swap_t9 {_ : MulAction G β} {_ : MulAction G' PUnit.{u + 1}} (g' : G')
    (g : G) : IndexCorr.biact g' (IndexCorr.toUnit β).swap g = (IndexCorr.toUnit β).swap :=
  (IndexCorr.mk_eq_mk
    (d := ((IndexDiagram.toUnit β).swap).map (MulAction.toPerm g⁻¹) (MulAction.toPerm g'))
    (d' := (IndexDiagram.toUnit β).swap)).2
    ⟨@MulAction.toPerm G β _ _ g⁻¹, fun _ => ⟨rfl, Subsingleton.elim _ _⟩⟩

theorem biact_toUnit_t9 {_ : MulAction G PUnit.{u + 1}} {_ : MulAction G' β} (g' : G') (g : G) :
    IndexCorr.biact g' (IndexCorr.toUnit β) g = IndexCorr.toUnit β :=
  IndexCorr.example_13_3_3 g' _ g

theorem ofEquiv_refl_eq_ofPerm_t9 {_ : MulAction G PUnit.{u + 1}} (g : G) :
    IndexCorr.ofEquiv (Equiv.refl PUnit.{u + 1}) = IndexCorr.ofPerm g :=
  IndexCorr.mk_eq_mk.2 ⟨Equiv.refl _, fun _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

theorem ofEquiv_refl_eq_biact_t9 {_ : MulAction G PUnit.{u + 1}}
    {_ : MulAction G' PUnit.{u + 1}} (g' : G') (g : G) :
    IndexCorr.ofEquiv (Equiv.refl PUnit.{u + 1}) =
      IndexCorr.biact g' (IndexCorr.ofEquiv (Equiv.refl PUnit.{u + 1})) g :=
  IndexCorr.mk_eq_mk.2 ⟨Equiv.refl _, fun _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

theorem ofEquiv_refl_eq_swap_t9 :
    IndexCorr.ofEquiv (Equiv.refl PUnit.{u + 1}) =
      (IndexCorr.ofEquiv (Equiv.refl PUnit.{u + 1})).swap :=
  IndexCorr.mk_eq_mk.2 ⟨Equiv.refl _, fun _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

end Unit

theorem isOpen_morBetween_t9 {U V : Set A.Obj} (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (A.X.morBetween U V) :=
  (hU.preimage A.X.continuous_src).inter (hV.preimage A.X.continuous_tgt)

theorem isOpen_critV (i : D.S.A ⊕ A.Obj) : IsOpen (D.critV i) := by
  rcases i with a | x
  · exact D.T.isOpen_V a.1 a.2
  · exact (Nx x).isOpen_invariantCore D.isClosed_C.isOpen_compl

/-- **The data (a)–(e) of Theorem 14.5.5 for `Λ'`.** -/
def crit (hσ : A.X.PObj.IsScSmoothMap realPolyfold σ)
    (hσt : ∀ φ : A.Mor, σ (A.X.tgt φ) = σ (A.X.src φ)) : CriterionData A (D.mult σ) where
  ι := D.S.A ⊕ A.Obj
  pt := D.pt
  N := D.critN
  V := D.critV
  isOpen_V := D.isOpen_critV
  V_subset i := by
    rcases i with a | x
    · exact D.S.V_subset a.1 a.2
    · exact fun y hy => D.critV_inr_mem_U hy
  mapsTo_V i g := by
    rcases i with a | x
    · exact D.S.mapsTo_V a.1 a.2 g
    · exact (Nx x).mapsTo_Φ_invariantCore _ g
  cover x := by
    by_cases hx : x ∈ D.C
    · obtain ⟨a, φ, hφ, e⟩ := mem_iUnion.1 hx
      exact ⟨.inl a, A.X.src φ, D.K_subset a.2 hφ, A.X.π_eq_π_iff.2 ⟨φ, rfl, e⟩⟩
    · exact ⟨.inr x, x, (Nx x).mem_invariantCore (V := D.Cᶜ) hx, rfl⟩
  I := D.critI
  fintype := D.critFintype
  mulAction := D.critMulAction
  s := D.critS σ
  isScPlusSectionOn i j := by
    rcases i with a | x
    · exact D.isScPlusSectionOn_ssec hσ a.2 j
    · exact isScPlusSectionOn_fiberZero (D.isOpen_critV (.inr x))
  equivariant i g j y hy := by
    rcases i with a | x
    · exact D.ssec_equivariant hσt a.2 g j hy
    · have hyU := D.critV_inr_mem_U hy
      exact (fibAct_fiberZero ((Nx x).src_Γ g hyU) ((Nx x).tgt_Γ g hyU)).symm
  rep i w hw := by
    rcases i with a | x
    · have e := D.mult_eq hσt a.2 (φ := A.X.unit (A.P w)) (A.X.src_unit _)
        (by rw [A.X.tgt_unit]; exact hw)
      rw [A.X.tgt_unit, AtomicStructData.fibAct_unit rfl] at e
      exact e
    · rw [D.mult_of_not_mem_C (D.critV_inr_not_mem hw)]
      change _ = (Fintype.card PUnit.{u + 1} : ℚ≥0)⁻¹ *
        ((Finset.univ.filter fun _ : PUnit.{u + 1} => fiberZero A.P (A.P w) = w).card : ℚ≥0)
      by_cases h0 : w = fiberZero A.P (A.P w)
      · rw [if_pos h0, Finset.filter_true_of_mem fun _ _ => h0.symm]
        simp
      · rw [if_neg h0, Finset.filter_false_of_mem fun _ _ e => h0 e.symm]
        simp
  τ := D.critτ
  locallyConstant i i' φ hφ := by
    rcases i with b | x <;> rcases i' with b' | x'
    · have h := D.T.locallyConstant b.1 b.2 b'.1 b'.2 φ hφ
      rwa [nhdsWithin_eq_nhds.2 ((isOpen_morBetween_t9 (D.T.isOpen_V b.1 b.2)
        (D.T.isOpen_V b'.1 b'.2)).mem_nhds hφ)] at h
    all_goals exact Eventually.of_forall fun _ => rfl
  finite i i' := by
    rcases i with b | x <;> rcases i' with b' | x'
    · exact D.finite_τ b.1 b.2 b'.1 b'.2
    all_goals exact (finite_singleton _).subset (by rintro _ ⟨_, _, rfl⟩; rfl)
  biact i i' φ hφ g' g := by
    rcases i with b | x <;> rcases i' with b' | x'
    · exact D.biact_τ b.1 b.2 b'.1 b'.2 φ hφ g' g
    · have := D.nonempty_I b.1 b.2
      exact (biact_toUnit_swap_t9 (β := D.S.I b.1) g' g).symm
    · have := D.nonempty_I b'.1 b'.2
      exact (biact_toUnit_t9 (β := D.S.I b'.1) g' g).symm
    · exact ofEquiv_refl_eq_biact_t9 g' g
  compat i i' φ hφ := by
    rcases i with b | x <;> rcases i' with b' | x'
    · exact D.ssec_compat hσt b.2 b'.2 hφ
    · have htC := D.critV_inr_not_mem hφ.2
      refine IndexCorr.sat_of_forall (fun j _ => ?_) _
      change fiberZero A.P (A.X.tgt φ) = fibAct φ (D.ssec σ b.1 j (A.X.src φ))
      rw [D.ssec_eq_zero_of_not_mem_C σ j (D.not_mem_C_of_tgt htC), fibAct_fiberZero rfl rfl]
    · have hsC := D.critV_inr_not_mem hφ.1
      refine IndexCorr.sat_of_forall (fun _ j => ?_) _
      change D.ssec σ b'.1 j (A.X.tgt φ) = fibAct φ (fiberZero A.P (A.X.src φ))
      rw [D.ssec_eq_zero_of_not_mem_C σ j (D.not_mem_C_of_src hsC), fibAct_fiberZero rfl rfl]
    · refine IndexCorr.sat_of_forall (fun _ _ => ?_) _
      exact (fibAct_fiberZero rfl rfl).symm
  diag i g y hy := by
    rcases i with a | x
    · exact D.S.diag a.1 a.2 g y hy
    · exact ofEquiv_refl_eq_ofPerm_t9 g
  swap i i' φ hφ := by
    rcases i with b | x <;> rcases i' with b' | x'
    · exact D.S.swap b.1 b.2 b'.1 b'.2 φ hφ.1 hφ.2
    · exact (IndexCorr.swap_swap _).symm
    · rfl
    · exact ofEquiv_refl_eq_swap_t9

theorem crit_nonempty (hσ : A.X.PObj.IsScSmoothMap realPolyfold σ)
    (hσt : ∀ φ : A.Mor, σ (A.X.tgt φ) = σ (A.X.src φ)) (i : (D.crit hσ hσt).ι) :
    Nonempty ((D.crit hσ hσt).I i) := by
  rcases i with a | x
  · exact D.nonempty_I a.1 a.2
  · exact ⟨PUnit.unit⟩

/-- **`Λ'` is structurable** (Theorem 14.5.5). -/
theorem isStructurable_mult (hpara : A.X.HasParacompactOrbitSpace)
    (hσ : A.X.PObj.IsScSmoothMap realPolyfold σ)
    (hσt : ∀ φ : A.Mor, σ (A.X.tgt φ) = σ (A.X.src φ)) : IsStructurable A (D.mult σ) :=
  theorem_14_5_5 hpara ⟨D.isWFunctor_mult hσt, fun y =>
    (D.crit hσ hσt).hasLocalSectionStructure_t9 (D.isWFunctor_mult hσt)
      (D.crit_nonempty hσ hσt) y⟩ (D.crit hσ hσt)

/-! ### `Λ'` over `∂X` and its domain support -/

/-- On `V̂_b ∩ ∂X` the boundary sections vanish off `dom-supp(Λ)`. -/
theorem s0_eq_zero {b : A.Obj} (hb : b ∈ D.S.A) (j : D.S.I b) {y : A.Obj}
    (hy : y ∈ D.S.V b ∩ A.X.PObj.boundary) (hyd : y ∉ boundaryDomSupp Λ) :
    D.T.s0 b j y = fiberZero A.P y := by
  have hPs0 : A.P (D.T.s0 b j y) = y := by
    rw [← D.T.sh_boundary b hb j y hy]
    exact (D.T.isScPlusSectionOn_sh b hb j).1 y hy.1
  by_contra hne
  apply hyd
  refine subset_closure ⟨hy.2, D.T.s0 b j y, hPs0, hne, ?_⟩
  have := D.nonempty_I b hb
  rw [D.rep b hb _ (by rw [hPs0]; exact hy), hPs0]
  refine mul_pos (inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos)) (Nat.cast_pos.2 ?_)
  exact Finset.card_pos.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩

theorem ssec_boundary (hσ1 : ∀ y ∈ boundaryDomSupp Λ, σ y = 1) {b : A.Obj} (hb : b ∈ D.S.A)
    (j : D.S.I b) {y : A.Obj} (hy : y ∈ D.S.V b ∩ A.X.PObj.boundary) :
    D.ssec σ b j y = D.T.s0 b j y := by
  unfold ssec
  rw [sectionSmul_congr_t9 (D.usec_boundary hb j hy)]
  have hPs0 : A.P (D.T.s0 b j y) = y := by
    rw [← D.T.sh_boundary b hb j y hy]
    exact (D.T.isScPlusSectionOn_sh b hb j).1 y hy.1
  by_cases hyd : y ∈ boundaryDomSupp Λ
  · unfold Polyfold.sectionSmul
    rw [dif_pos hPs0, hσ1 y hyd, one_smul]
  · have h0 := D.s0_eq_zero hb j hy hyd
    unfold Polyfold.sectionSmul
    rw [dif_pos hPs0]
    have e : (⟨D.T.s0 b j y, hPs0⟩ : A.P ⁻¹' {y}) = 0 := Subtype.ext h0
    rw [e, smul_zero, h0]
    rfl

/-- **`Λ'|(W|∂X) = Λ`** (when `σ = 1` on `dom-supp(Λ)`). -/
theorem mult_boundary (hσt : ∀ φ : A.Mor, σ (A.X.tgt φ) = σ (A.X.src φ))
    (hσ1 : ∀ y ∈ boundaryDomSupp Λ, σ y = 1) {w : A.W} (hw : A.P w ∈ A.X.PObj.boundary) :
    D.mult σ w = Λ w := by
  obtain ⟨a, ha, hβ⟩ := exists_ne_zero_of_finsum_mem_ne_zero
    (by rw [D.sum_one _ hw]; exact one_ne_zero : ∑ᶠ a ∈ D.S.A, D.T.β a (A.P w) ≠ 0)
  obtain ⟨φ, hs, ht⟩ := D.suppInSat a ha _ hβ
  have hsb : A.X.src φ ∈ A.X.PObj.boundary := src_mem_boundary_t9 (ht ▸ hw)
  have hwi : A.P w = A.X.src (A.X.inv φ) := by rw [A.X.src_inv, ht]
  rw [D.mult_eq hσt ha (φ := A.X.inv φ) (by rw [A.X.src_inv, ht])
    (by rw [A.X.tgt_inv]; exact hs)]
  have hPw' : A.P (fibAct (A.X.inv φ) w) = A.X.src φ := by rw [P_fibAct hwi, A.X.tgt_inv]
  rw [← D.functor (A.X.inv φ) w hwi (by rw [← hwi]; exact hw),
    D.rep a ha _ (by rw [hPw']; exact ⟨hs, hsb⟩), hPw', A.X.tgt_inv]
  congr 3
  refine Finset.filter_congr fun j _ => ?_
  rw [D.ssec_boundary hσ1 ha j ⟨hs, hsb⟩]

/-- **`dom-supp(Λ') ⊆ tsupport σ`.** -/
theorem domSupp_mult_subset (hσt : ∀ φ : A.Mor, σ (A.X.tgt φ) = σ (A.X.src φ)) :
    domSupp (D.mult σ) ⊆ tsupport σ := by
  refine closure_mono ?_
  rintro x ⟨w, rfl, hw0, hpos⟩
  by_contra hσx
  have hσ0 : σ (A.P w) = 0 := by
    by_contra h
    exact hσx (Function.mem_support.2 h)
  apply (lt_irrefl (0 : ℚ≥0))
  convert hpos using 1
  symm
  by_cases h : ∃ p : D.S.A × A.Mor, A.X.src p.2 = A.P w ∧ A.X.tgt p.2 ∈ D.S.V p.1
  · obtain ⟨⟨b, φ⟩, hs, ht⟩ := h
    rw [D.mult_eq hσt b.2 hs ht, Finset.filter_false_of_mem fun j _ => ?_, Finset.card_empty,
      Nat.cast_zero, mul_zero]
    have hσφ : σ (A.X.tgt φ) = 0 := by rw [hσt, hs]; exact hσ0
    rw [D.ssec_eq_zero_of_σ j hσφ]
    intro e
    exact hw0 ((fibAct_eq_fiberZero_iff_t9 hs.symm).1 e.symm |>.trans (by rw [hs]))
  · unfold mult
    rw [dif_neg h, if_neg hw0]

/-! ### The cut-off -/

include D in
/-- `dom-supp(Λ)` over `∂X` is saturated. -/
theorem isSaturated_boundaryDomSupp : A.X.IsSaturated (boundaryDomSupp Λ) := by
  refine isSaturated_closure_gl (A.X.isSaturated_iff.2 fun φ hφ => ?_)
  obtain ⟨hb, w, hw, hw0, hpos⟩ := hφ
  have hwφ : A.P w = A.X.src φ := hw
  refine ⟨A.X.isSaturated_iff.1 isSaturated_boundary_gl φ hb, fibAct φ w, P_fibAct hwφ,
    fun e => hw0 ?_, ?_⟩
  · exact (fibAct_eq_fiberZero_iff_t9 hwφ).1 e
  · rw [D.functor φ w hwφ hb]; exact hpos

include D in
/-- **The cut-off of the size control**: an sc-smooth functor `σ` with `σ = 1` on
`dom-supp(Λ)` and `tsupport σ ⊆ Ũ` (Urysohn's lemma on `|X|`, Theorem 7.5.7). -/
theorem exists_cutoff (hpara : A.X.HasParacompactOrbitSpace)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity) {Ũ : Set A.Obj} (hUo : IsOpen Ũ)
    (hUs : A.X.IsSaturated Ũ) (hsub : boundaryDomSupp Λ ⊆ Ũ) :
    ∃ σ : A.Obj → ℝ, A.X.PObj.IsScSmoothMap realPolyfold σ ∧
      (∀ φ : A.Mor, σ (A.X.tgt φ) = σ (A.X.src φ)) ∧
      (∀ y ∈ boundaryDomSupp Λ, σ y = 1) ∧ tsupport σ ⊆ Ũ := by
  have : ParacompactSpace A.X.OrbitSpace := hpara
  have hK : IsClosed (A.X.π '' boundaryDomSupp Λ) :=
    A.X.isClosed_π_image_of_isSaturated D.isSaturated_boundaryDomSupp isClosed_closure
  have hU : IsOpen (A.X.π '' Ũ) := A.X.proposition_7_1_8 Ũ hUo
  obtain ⟨u, huo, hKu, hucl⟩ := normal_exists_closure_subset hK hU (image_mono hsub)
  obtain ⟨F, hFs, hF0, hF1, -⟩ := A.X.exists_isScSmoothMap_orbit_urysohn hpara hpu
    huo.isClosed_compl hK (disjoint_compl_left.mono_right hKu)
  refine ⟨F ∘ A.X.π, hFs, fun φ => ?_, fun y hy => hF1 (mem_image_of_mem _ hy), ?_⟩
  · simp only [comp_apply]
    rw [A.X.π_eq_π_iff.2 ⟨φ, rfl, rfl⟩]
  · have hsupp : support (F ∘ A.X.π) ⊆ A.X.π ⁻¹' u := fun y hy => by
      by_contra hyu
      exact hy (hF0 hyu)
    refine (closure_mono hsupp).trans ((A.X.continuous_π.closure_preimage_subset u).trans ?_)
    intro y hy
    have : A.X.π y ∈ A.X.π '' Ũ := hucl hy
    rw [← hUs]
    exact this

include D in
/-- **The extension of Theorem 14.1.9** (GL's `theorem_14_1_9_extension_statement`, conclusion)
for a boundary multisection with the data of §§14.3–14.5. -/
theorem extension (hpara : A.X.HasParacompactOrbitSpace)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity) {Ũ : Set A.Obj} (hUo : IsOpen Ũ)
    (hUs : A.X.IsSaturated Ũ) (hsub : boundaryDomSupp Λ ⊆ Ũ) :
    ∃ Λ'' : A.W → ℚ≥0, IsStructurable A Λ'' ∧ domSupp Λ'' ⊆ Ũ ∧
      ∀ w, A.P w ∈ A.X.PObj.boundary → Λ'' w = Λ w := by
  obtain ⟨σ, hσ, hσt, hσ1, hσU⟩ := D.exists_cutoff hpara hpu hUo hUs hsub
  exact ⟨D.mult σ, D.isStructurable_mult hpara hσ hσt,
    (D.domSupp_mult_subset hσt).trans hσU, fun w hw => D.mult_boundary hσt hσ1 hw⟩

end AssemblyInput

/-! ### Theorem 14.1.9 -/

/-- **The data of §§14.3–14.5 exist** (as a `Prop`): under the hypotheses of Theorem 14.1.9,
every structurable `Λ` over `∂X` has an `AssemblyInput` (Propositions 14.2.3, 14.3.8, 14.4.14 and
Lemma 14.5.1, instantiated). -/
def AssemblyHyp (A : SEP.{u}) : Prop :=
  A.X.IsTame → A.X.HasParacompactOrbitSpace → A.X.PObj.AdmitsScPartitionsOfUnity →
    ∀ Λ : A.W → ℚ≥0, IsBoundaryStructurable A Λ → Nonempty (AssemblyInput A Λ)

/-- **GL's extension statement from the data of §§14.3–14.5.** -/
theorem theorem_14_1_9_extension_statement_of_assembly (h : AssemblyHyp A) :
    theorem_14_1_9_extension_statement A := by
  intro hX hpara hpu Λ hΛ Ũ hUo hUs hsub
  obtain ⟨D⟩ := h hX hpara hpu Λ hΛ
  exact D.extension hpara hpu hUo hUs hsub

/-- **2021 Theorem 14.1.9 (∂-Extension Theorem), p. 646 (2017: Theorem 14.2)**, from the data
of §§14.3–14.5 (`AssemblyHyp`): Proposition 14.5.4 (`proposition_14_5_4`), the sum over `a`,
Theorem 14.5.5 and the size control (GL's `theorem_14_1_9_hyp`). -/
theorem theorem_14_1_9_of_assembly (h : AssemblyHyp A) : theorem_14_1_9_statement A :=
  theorem_14_1_9_hyp (theorem_14_1_9_extension_statement_of_assembly h)

/-! ### Satisfiability of `AssemblyHyp` -/

/-- The setting of §14.4 with `A = ∅`. -/
def emptyZSetup (A : SEP.{u}) : A.X.ZSetup :=
  { ZSetup.trivialSetup A.X with
    A := ∅
    V_subset := fun _ h => absurd h (notMem_empty _)
    mapsTo_V := fun _ h => absurd h (notMem_empty _)
    diag := fun _ h => absurd h (notMem_empty _)
    swap := fun _ h => absurd h (notMem_empty _) }

/-- Transport data over `A = ∅` (`β ≡ 0`, zero sections). -/
def emptyTransportInput (A : SEP.{u}) : TransportInput A (emptyZSetup A) where
  isOpen_V _ h := absurd h (notMem_empty _)
  proper _ h := absurd h (notMem_empty _)
  locallyConstant _ h := absurd h (notMem_empty _)
  β _ _ := 0
  isScSmooth_β _ := isScSmoothMap_real_const 0
  β_tgt _ _ := rfl
  closure_support_β _ h := absurd h (notMem_empty _)
  s0 _ _ := fiberZero A.P
  s0_compat _ h := absurd h (notMem_empty _)
  sh _ _ := fiberZero A.P
  isScPlusSectionOn_sh _ h := absurd h (notMem_empty _)
  sh_equivariant _ h := absurd h (notMem_empty _)
  sh_boundary _ h := absurd h (notMem_empty _)
  sh_zRel _ h := absurd h (notMem_empty _)

/-- The data of §§14.3–14.5 over `A = ∅`, when `∂X = ∅`. -/
def emptyAssemblyInput (hb : A.X.PObj.boundary = ∅) (Λ : A.W → ℚ≥0) : AssemblyInput A Λ where
  S := emptyZSetup A
  T := emptyTransportInput A
  suppInSat _ h := absurd h (notMem_empty _)
  locFin y := ⟨univ, isOpen_univ, mem_univ y, A.X.isSaturated_iff.2 fun _ _ => mem_univ _,
    finite_empty.subset fun _ ha => ha.1⟩
  sum_one y hy := by rw [hb] at hy; exact absurd hy (notMem_empty _)
  nonempty_I _ h := absurd h (notMem_empty _)
  finite_τ _ h := absurd h (notMem_empty _)
  biact_τ _ h := absurd h (notMem_empty _)
  rep _ h := absurd h (notMem_empty _)
  functor _ _ _ h := by rw [hb] at h; exact absurd h (notMem_empty _)

/-- **`AssemblyHyp` is satisfiable**: it holds when `∂X = ∅` (with `A = ∅`). -/
theorem assemblyHyp_of_boundary_eq_empty (hb : A.X.PObj.boundary = ∅) : AssemblyHyp A :=
  fun _ _ _ Λ _ => ⟨emptyAssemblyInput hb Λ⟩

end SBLocalization

end Polyfold
