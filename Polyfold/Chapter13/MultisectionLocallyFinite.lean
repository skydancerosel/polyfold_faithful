import Polyfold.Chapter13.MultisectionAlgebra

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.2, **Definition 13.2.12** and **Lemma 13.2.13** (p. 612; 2017: Definition 13.12,
Lemma 13.13), at the level of the functors `Λ : W → ℚ⁺`.

# Locally finite sums of sc⁺-multisections

## The text, paraphrased

(Definition 13.2.12) A family `(Λ_j)_{j ∈ J}` is locally finite if every `x` has an open
saturated neighbourhood `O(x)` such that only finitely many `Λ_j` take a positive value on some
`w ≠ 0` over `O(x)`; `O(x)` can be taken so that every smaller saturated `O'(x)` gives the same
finite set `J_x`.  On `U(x) = O(x) ∩ ⋂_{j ∈ J_x} U_j(x)` the index set is `∏_{j ∈ J_x} I^j_x` and
the sections are `∑_{j ∈ J_x} s^j_{i_j}`.
(Lemma 13.2.13) The sum `⊕_j Λ_j` of a locally finite family is a well-defined decorated
sc⁺-multisection.

## What is formalized (namespace `Polyfold.SBLocalization`)

* Definition 13.2.12: `nontrivIdx` (the set of `j` with `Λ_j(w) > 0` for some `w ≠ 0` over `O`),
  `IsLocallyFiniteFamily`; `IsLocallyFiniteFamily.exists_stable` (the choice of `O(x)` after the
  definition).
* The sum of a family: `lfSum`, the convolution over the finitely supported families
  `(v_j) ∈ W_x^{(J)}` with `∑ v_j = w`, of `∏ᶠ_j Λ_j(v_j)`; `lfSumAt_eq_convAt`: if the `Λ_j` with
  `j ∉ F` are trivial over `x`, it is the convolution over the finite set `F`;
  `lfSum_eq_conv_of_mem` (on `O(x)` the sum is `⊕_{j ∈ J_x}`), `lfSum_eq_conv` (for a finite `J`
  it is the finite convolution, so for two terms Definition 13.2.9 (1)).
* **`lemma_13_2_13`**: the sum of a locally finite family of sc⁺-multisections is an
  sc⁺-multisection, with the local sections `∑_{j ∈ J_x} s^j_{i_j}` on `U(x)`.
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

/-! ### Reindexing a finite convolution -/

/-- A finite convolution does not depend on the indexing of the family. -/
theorem convAt_comp_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (Λ : ι' → A.W → ℚ≥0) (x : A.Obj) (w : A.W) :
    convAt (fun i => Λ (e i)) x w = convAt Λ x w := by
  unfold convAt
  rw [← finsum_comp_equiv (Equiv.arrowCongr e (Equiv.refl (A.P ⁻¹' {x}))).symm]
  refine finsum_congr fun v => ?_
  have hs : (∑ i, (Equiv.arrowCongr e (Equiv.refl _)).symm v i : A.P ⁻¹' {x}) = ∑ i', v i' :=
    Fintype.sum_equiv e _ _ fun i => by simp [Equiv.arrowCongr]
  have hp : ∏ i, Λ (e i) ((Equiv.arrowCongr e (Equiv.refl _)).symm v i : A.P ⁻¹' {x}) =
      ∏ i', Λ i' (v i') :=
    Fintype.prod_equiv e _ _ fun i => by simp [Equiv.arrowCongr]
  rw [hs, hp]

/-! ### Definition 13.2.12 -/

/-- The indices `j` for which `Λ_j(w) > 0` for some `w ≠ 0` over `O`. -/
def nontrivIdx {J : Type*} (Λ : J → A.W → ℚ≥0) (O : Set A.Obj) : Set J :=
  {j | ∃ w, A.P w ∈ O ∧ w ≠ fiberZero A.P (A.P w) ∧ 0 < Λ j w}

theorem nontrivIdx_mono {J : Type*} (Λ : J → A.W → ℚ≥0) {O O' : Set A.Obj} (h : O' ⊆ O) :
    nontrivIdx Λ O' ⊆ nontrivIdx Λ O := fun _ ⟨w, hw, hw0, hpos⟩ => ⟨w, h hw, hw0, hpos⟩

/-- **2021 Definition 13.2.12, p. 612 (2017: Definition 13.12)**: `(Λ_j)_{j ∈ J}` is locally
finite if every `x` has an open saturated neighbourhood `O(x)` over which only finitely many
`Λ_j` are positive at some `w ≠ 0`. -/
def IsLocallyFiniteFamily {J : Type*} (Λ : J → A.W → ℚ≥0) : Prop :=
  ∀ x, ∃ O : Set A.Obj, IsOpen O ∧ A.X.IsSaturated O ∧ x ∈ O ∧ (nontrivIdx Λ O).Finite

/-- **p. 612, after Definition 13.2.12**: `O(x)` can be taken so that every smaller open saturated
`O'(x)` gives the same set of indices. -/
theorem IsLocallyFiniteFamily.exists_stable {J : Type*} {Λ : J → A.W → ℚ≥0}
    (h : IsLocallyFiniteFamily Λ) (x : A.Obj) :
    ∃ O : Set A.Obj, IsOpen O ∧ A.X.IsSaturated O ∧ x ∈ O ∧ (nontrivIdx Λ O).Finite ∧
      ∀ O' : Set A.Obj, IsOpen O' → A.X.IsSaturated O' → x ∈ O' → O' ⊆ O →
        nontrivIdx Λ O' = nontrivIdx Λ O := by
  obtain ⟨O₀, hO₀, hs₀, hx₀, hf₀⟩ := h x
  have hex : ∃ n, ∃ O : Set A.Obj, IsOpen O ∧ A.X.IsSaturated O ∧ x ∈ O ∧ O ⊆ O₀ ∧
      (nontrivIdx Λ O).ncard = n := ⟨_, O₀, hO₀, hs₀, hx₀, subset_rfl, rfl⟩
  obtain ⟨O, hO, hs, hx, hsub, hcard⟩ := Nat.find_spec hex
  have hfin : (nontrivIdx Λ O).Finite := hf₀.subset (nontrivIdx_mono Λ hsub)
  refine ⟨O, hO, hs, hx, hfin, fun O' hO' hs' hx' hO'O => ?_⟩
  have hle : nontrivIdx Λ O' ⊆ nontrivIdx Λ O := nontrivIdx_mono Λ hO'O
  refine Set.eq_of_subset_of_ncard_le hle ?_ hfin
  rw [hcard]
  exact Nat.find_min' hex ⟨O', hO', hs', hx', hO'O.trans hsub, rfl⟩

/-! ### The sum of a family -/

/-- **The sum `⊕_j Λ_j` over the fibre `W_x`**: the convolution over the finitely supported
families `(v_j) ∈ W_x^{(J)}` with `∑ v_j = w`, of `∏ᶠ_j Λ_j(v_j)`. -/
def lfSumAt {J : Type*} (Λ : J → A.W → ℚ≥0) (x : A.Obj) (w : A.W) : ℚ≥0 :=
  ∑ᶠ v : J →₀ A.P ⁻¹' {x},
    if ((v.sum fun _ u => u : A.P ⁻¹' {x}) : A.W) = w then ∏ᶠ j, Λ j (v j) else 0

/-- **The sum `⊕_{j ∈ J} Λ_j : W → ℚ⁺`** of a family (Lemma 13.2.13). -/
def lfSum {J : Type*} (Λ : J → A.W → ℚ≥0) (w : A.W) : ℚ≥0 := lfSumAt Λ (A.P w) w

theorem lfSum_eq_lfSumAt {J : Type*} (Λ : J → A.W → ℚ≥0) {x : A.Obj} {w : A.W}
    (hw : A.P w = x) : lfSum Λ w = lfSumAt Λ x w := by
  unfold lfSum; rw [hw]

/-- **The sum of a family is a finite convolution over a fibre** where all but finitely many
members are trivial: if `Λ_j(u) = [u = 0]` on `W_x` for `j ∉ F`, then
`(⊕_{j ∈ J} Λ_j)(w) = (⊕_{j ∈ F} Λ_j)(w)` over `x`. -/
theorem lfSumAt_eq_convAt {J : Type*} (Λ : J → A.W → ℚ≥0) {x : A.Obj} (F : Finset J)
    (hF : ∀ j ∉ F, ∀ u : A.P ⁻¹' {x}, Λ j u = if u = 0 then 1 else 0) (w : A.W) :
    lfSumAt Λ x w = convAt (fun j : F => Λ j) x w := by
  set e : (F → A.P ⁻¹' {x}) → (J →₀ A.P ⁻¹' {x}) := fun v =>
    Finsupp.onFinset F (fun j => if h : j ∈ F then v ⟨j, h⟩ else 0) (fun j hj => by
      by_contra hjF; exact hj (dif_neg hjF)) with hedef
  have he : ∀ v j, e v j = if h : j ∈ F then v ⟨j, h⟩ else 0 := fun v j => rfl
  have hinj : Injective e := fun v v' hvv' => funext fun i => by
    have := congrArg (fun f : J →₀ A.P ⁻¹' {x} => f i) hvv'
    simpa [he, i.2] using this
  set f : (J →₀ A.P ⁻¹' {x}) → ℚ≥0 := fun v =>
    if ((v.sum fun _ u => u : A.P ⁻¹' {x}) : A.W) = w then ∏ᶠ j, Λ j (v j) else 0 with hfdef
  have hmul : ∀ v : J →₀ A.P ⁻¹' {x},
      (mulSupport fun j => Λ j (v j)) ⊆ ↑(F ∪ v.support) := fun v j hj => by
    by_contra hjn
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff,
      not_or, not_not] at hjn
    exact hj (by
      show Λ j ((v j : A.P ⁻¹' {x}) : A.W) = 1
      rw [hF j hjn.1, if_pos hjn.2])
  have hsupp : support f ⊆ range e := fun v hv => by
    have hprod : ∏ᶠ j, Λ j (v j) ≠ 0 := fun h0 => hv (by simp only [hfdef, h0, ite_self])
    have hvF : ∀ j ∉ F, v j = 0 := fun j hj => by
      by_contra hne
      exact hprod (finprod_eq_zero _ j (by rw [hF j hj, if_neg hne])
        ((Finset.finite_toSet _).subset (hmul v)))
    refine ⟨fun i => v i, Finsupp.ext fun j => ?_⟩
    simp only [he]
    split_ifs with hj
    · rfl
    · exact (hvF j hj).symm
  have hval : ∀ v : F → A.P ⁻¹' {x}, f (e v) =
      if ((∑ i : F, v i : A.P ⁻¹' {x}) : A.W) = w then ∏ i : F, Λ i (v i) else 0 := fun v => by
    have hs : ((e v).sum fun _ u => u) = ∑ i : F, v i := by
      rw [Finsupp.onFinset_sum _ fun _ => rfl, ← Finset.sum_coe_sort F]
      exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.2]
    have hp : ∏ᶠ j, Λ j (e v j) = ∏ i : F, Λ i (v i) := by
      rw [finprod_eq_prod_of_mulSupport_subset (s := F) _ fun j hj => ?_,
        ← Finset.prod_coe_sort F]
      · exact Finset.prod_congr rfl fun i _ => by simp only [he, dif_pos i.2]
      · by_contra hjF
        exact hj (by
          show Λ j ((e v j : A.P ⁻¹' {x}) : A.W) = 1
          have hjF' : j ∉ F := hjF
          simp only [he, dif_neg hjF']
          rw [hF j hjF', if_pos rfl])
    simp only [hfdef, hs, hp]
  unfold lfSumAt convAt
  change ∑ᶠ v, f v = _
  have h1 : ∑ᶠ v, f v = ∑ᶠ v ∈ range e, f v := by
    rw [finsum_mem_def, Set.indicator_eq_self.2 hsupp]
  rw [h1, finsum_mem_range hinj]
  exact finsum_congr hval

/-- **For a finite index type the sum is the finite convolution** (so for `J = Fin 2` it is the
sum of Definition 13.2.9 (1), `multisectionAdd_eq_conv`). -/
theorem lfSum_eq_conv {J : Type*} [Fintype J] (Λ : J → A.W → ℚ≥0) : lfSum Λ = conv Λ := by
  funext w
  rw [lfSum, conv, lfSumAt_eq_convAt Λ Finset.univ (fun j hj => absurd (Finset.mem_univ j) hj)]
  exact convAt_comp_equiv (Equiv.subtypeUnivEquiv Finset.mem_univ) Λ _ w

/-- A member of a family of sc⁺-multisections whose index is not in `nontrivIdx Λ O` is trivial
over `O`. -/
theorem trivial_of_not_mem_nontrivIdx {J : Type*} {Λ : J → A.W → ℚ≥0}
    (hΛ : ∀ j, IsScPlusMultisection A (Λ j)) {O : Set A.Obj} {x : A.Obj} (hx : x ∈ O) {j : J}
    (hj : j ∉ nontrivIdx Λ O) (u : A.P ⁻¹' {x}) : Λ j u = if u = 0 then 1 else 0 := by
  have hz : ∀ w, A.P w = x → w ≠ fiberZero A.P x → Λ j w = 0 := fun w hw hw0 => by
    by_contra hne
    exact hj ⟨w, by rw [hw]; exact hx, by rw [hw]; exact hw0, pos_iff_ne_zero.2 hne⟩
  split_ifs with hu
  · rw [hu]; exact ((hΛ j).apply_fiberZero_eq_one_iff x).2 hz
  · exact hz u u.2 fun e => hu (Subtype.ext e)

/-- **On `O(x)` the sum of a locally finite family is the finite sum over `J_x`**. -/
theorem lfSum_eq_conv_of_mem {J : Type*} {Λ : J → A.W → ℚ≥0}
    (hΛ : ∀ j, IsScPlusMultisection A (Λ j)) {O : Set A.Obj} (hfin : (nontrivIdx Λ O).Finite)
    {w : A.W} (hw : A.P w ∈ O) : lfSum Λ w = conv (fun j : hfin.toFinset => Λ j) w := by
  rw [lfSum, conv, lfSumAt_eq_convAt Λ hfin.toFinset fun j hj u =>
    trivial_of_not_mem_nontrivIdx hΛ hw (fun h => hj (hfin.mem_toFinset.2 h)) u]

/-- The sum of a locally finite family of functors is a functor (both fibres of a morphism lie in
the same saturated `O(x)`). -/
theorem isWFunctor_lfSum {J : Type*} {Λ : J → A.W → ℚ≥0}
    (hΛ : ∀ j, IsScPlusMultisection A (Λ j)) (hlf : IsLocallyFiniteFamily Λ) :
    IsWFunctor A (lfSum Λ) := by
  rintro ⟨⟨φ, w⟩, hq⟩
  have hq' : A.P w = A.X.src φ := hq
  obtain ⟨O, -, hsat, hxO, hfin⟩ := hlf (A.X.src φ)
  have htO : A.X.tgt φ ∈ O := A.X.isSaturated_iff.1 hsat φ hxO
  have h1 : A.P (A.E.μ ⟨(φ, w), hq⟩) ∈ O := by rw [A.E.P_μ]; exact htO
  have h2 : A.P w ∈ O := by rw [hq']; exact hxO
  change lfSum Λ (A.E.μ ⟨(φ, w), hq⟩) = lfSum Λ w
  rw [lfSum_eq_conv_of_mem hΛ hfin h1, lfSum_eq_conv_of_mem hΛ hfin h2]
  exact isWFunctor_conv (Λ := fun j : hfin.toFinset => Λ j) (fun j => (hΛ j).1) ⟨(φ, w), hq⟩

/-- A local representation transfers along a function which agrees on `O`. -/
theorem IsLocalRepOn.congr_fun {Λ Λ' : A.W → ℚ≥0} {O : Set A.Obj} {k : ℕ}
    {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (h : IsLocalRepOn A Λ O s σ)
    (heq : ∀ w, A.P w ∈ O → Λ' w = Λ w) : IsLocalRepOn A Λ' O s σ :=
  ⟨h.1, h.2.1, h.2.2.1, fun w hw => (heq w hw).trans (h.2.2.2 w hw)⟩

/-- **2021 Lemma 13.2.13, p. 612 (2017: Lemma 13.13), functor level**: the sum `⊕_{j ∈ J} Λ_j` of
a locally finite family of sc⁺-multisections is an sc⁺-multisection.  Around `x` its local
representation lives on `U(x) = O(x) ∩ ⋂_{j ∈ J_x} U_j(x)`, with the index set
`∏_{j ∈ J_x} I^j` and the sections `∑_{j ∈ J_x} s^j_{i_j}` (`isLocalRepOn_conv`). -/
theorem lemma_13_2_13 {J : Type*} {Λ : J → A.W → ℚ≥0}
    (hΛ : ∀ j, IsScPlusMultisection A (Λ j)) (hlf : IsLocallyFiniteFamily Λ) :
    IsScPlusMultisection A (lfSum Λ) := by
  refine ⟨isWFunctor_lfSum hΛ hlf, fun x => ?_⟩
  obtain ⟨O, hO, -, hxO, hfin⟩ := hlf x
  set F := hfin.toFinset
  choose R k s σ h using fun j : F => (hΛ j).2 x
  set U := O ∩ ⋂ j : F, (R j).U
  have hU : IsOpen U := hO.inter (isOpen_iInter_of_finite fun j => (R j).isOpen_U)
  have hxU : x ∈ U := ⟨hxO, mem_iInter.2 fun j => (R j).mem_U⟩
  obtain ⟨N, S, τ, hrep⟩ := isLocalRepOn_conv hU fun j =>
    (h j).mono hU (inter_subset_right.trans (iInter_subset _ j))
  exact hasLocalSectionStructure_of_isLocalRepOn hU hxU
    (hrep.congr_fun fun w hw => lfSum_eq_conv_of_mem hΛ hfin hw.1)

end SBLocalization

end Polyfold
