import Polyfold.Chapter15.P3W4TX_TransversalExtension
import Polyfold.Chapter14.P3W4LX_OpenExtension
import Polyfold.Chapter14.P3W4GL_NormControl

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, p. 698: step (a)
of the proof of **Theorem 15.3.9** (the cut-off functor `h₀`), proved; gap TX-1.

# The cut-off functor `h₀` of Theorem 15.3.9

## The text, paraphrased

At the start of the proof of the Transversal Extension Theorem one picks a continuous functor
`h₀` with `N(Λ) < h₀ < h` on `∂X`, supported in `U`, and applies Theorem 14.1.9 with it.

## What is formalized (namespace `Polyfold.SBLocalization`)

* For `Λ : W|∂X → ℚ⁺` an sc⁺-multisection over `∂X` (Definition 14.1.3):
  `BoundarySymmetricStructure.mem_suppAt_iff_ty` (`supp(Λ)(y) = {sᵢ(y)}` over `U(x)`),
  `IsBoundaryScPlusMultisection.suppAt_subset_oneSet_ty`, `pointwiseNorm_tgt_of_boundary_ty`
  (`N(Λ)` is a functor on `∂X`), `isSaturated_boundaryDomSupp_ty`, and
  **`exists_nhds_pointwiseNorm_lt_ty`**: `N(Λ)` is upper semicontinuous along `∂X` (the face-wise
  sc⁺ sections `sᵢ` extend to sc⁺-sections near `x`, LX's
  `exists_scPlusSectionOn_extension_of_face`, on which `N ∘ s̄ᵢ` is continuous).
* **`lemma_15_3_9_cutoff_hyp`**: TX's `lemma_15_3_9_cutoff_statement A` holds as soon as every
  object lies in a tame strong bundle chart (`hB`, the reading of "strong bundle over a tame
  ep-groupoid" used by LX and Z4).  Proof: on the paracompact Hausdorff orbit space `|X|`, a
  continuous `g` with `N(Λ) < g < h` on `|dom-supp(Λ)|` and `0 ≤ g < h` everywhere (local
  constants and a partition of unity, `exists_continuous_forall_mem_convex_of_local_const`), times
  an Urysohn function `ψ` with `ψ = 1` on `|dom-supp(Λ)|` and support in a closed neighbourhood
  inside `|U|`; `h₀ = (ψ g) ∘ π`.
* **`theorem_15_3_9_of_extension_ty`**: Theorem 15.3.9 from GL's extension statement of §§14.3–14.5
  and TX's relative general position statement (steps (c)–(d)) only.

## Reading

* `hB` is not stated by the text; without tame strong bundle charts Definition 14.1.3 (1) says
  nothing about the `sᵢ`, and `N(Λ)` need not be semicontinuous along `∂X`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold EpGroupoid

variable {A : SEP.{u}}

/-! ### The support over a boundary point -/

/-- Over `U(x)`, `supp(Λ)(y) = {sᵢ(y) | i ∈ I_x}` (Definition 14.1.3 (3)). -/
theorem BoundarySymmetricStructure.mem_suppAt_iff_ty {Λ : A.W → ℚ≥0} {x : A.Obj}
    {V : A.X.NatNbhd x} (S : BoundarySymmetricStructure A Λ V) {y : A.Obj} (hy : y ∈ V.bdry)
    {w : A.W} : w ∈ suppAt Λ y ↔ ∃ i, S.s i y = w := by
  classical
  constructor
  · rintro ⟨hw, hpos⟩
    have hr := S.rep w (by rw [hw]; exact hy)
    rw [hr, hw] at hpos
    by_contra hne
    push Not at hne
    have e : (Finset.univ.filter fun i => S.s i y = w) = ∅ :=
      Finset.filter_false_of_mem fun i _ => hne i
    rw [e] at hpos
    simp at hpos
  · rintro ⟨i, rfl⟩
    have hP := S.P_s i hy
    refine ⟨hP, ?_⟩
    rw [S.rep _ (by rw [hP]; exact hy), hP]
    have hmem : i ∈ Finset.univ.filter fun j => S.s j y = S.s i y := by simp
    have hc : 0 < (Finset.univ.filter fun j => S.s j y = S.s i y).card :=
      Finset.card_pos.2 ⟨i, hmem⟩
    have hI : 0 < Fintype.card S.I := Fintype.card_pos_iff.2 ⟨i⟩
    refine mul_pos (inv_pos.2 ?_) ?_
    · exact_mod_cast hI
    · exact_mod_cast hc

/-- Over `∂X`, the support of an sc⁺-multisection over `∂X` lies in `W_{0,1}`. -/
theorem IsBoundaryScPlusMultisection.suppAt_subset_oneSet_ty {Λ : A.W → ℚ≥0}
    (hΛ : IsBoundaryScPlusMultisection A Λ) {y : A.Obj} (hy : y ∈ A.X.PObj.boundary) :
    suppAt Λ y ⊆ A.B.oneSet := by
  obtain ⟨V, -, ⟨S⟩⟩ := hΛ.2 y hy
  intro w hw
  obtain ⟨i, rfl⟩ := (S.mem_suppAt_iff_ty ⟨V.mem_U, hy⟩).1 hw
  exact ((S.isFaceScPlus i).1 y ⟨V.mem_U, hy⟩).2

/-- `μ(φ, ·)` carries the norms of `supp(Λ)(s(φ))` into those of `supp(Λ)(t(φ))`, `s(φ) ∈ ∂X`. -/
theorem normW_image_suppAt_subset_ty {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N)
    {Λ : A.W → ℚ≥0} (hΛ : IsBoundaryScPlusMultisection A Λ) (φ : A.Mor)
    (hφ : A.X.src φ ∈ A.X.PObj.boundary) :
    normW N '' suppAt Λ (A.X.src φ) ⊆ normW N '' suppAt Λ (A.X.tgt φ) := by
  rintro _ ⟨w, ⟨hw, hpos⟩, rfl⟩
  have hw1 := hΛ.suppAt_subset_oneSet_ty hφ ⟨hw, hpos⟩
  refine ⟨A.E.μ ⟨(φ, w), hw⟩, ⟨A.E.P_μ _, ?_⟩, normW_μ hN hw hw1⟩
  rw [hΛ.1 ⟨(φ, w), hw⟩ hφ]
  exact hpos

/-- **`N(Λ)` is a functor on `∂X`** for an sc⁺-multisection over `∂X`. -/
theorem pointwiseNorm_tgt_of_boundary_ty {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N)
    {Λ : A.W → ℚ≥0} (hΛ : IsBoundaryScPlusMultisection A Λ) (φ : A.Mor)
    (hφ : A.X.src φ ∈ A.X.PObj.boundary) :
    pointwiseNorm N Λ (A.X.tgt φ) = pointwiseNorm N Λ (A.X.src φ) := by
  have hφ' : A.X.src (A.X.inv φ) ∈ A.X.PObj.boundary := by
    rw [A.X.src_inv]
    exact A.X.isSaturated_iff.1 isSaturated_boundary_gl φ hφ
  unfold pointwiseNorm
  congr 1
  refine Subset.antisymm ?_ (normW_image_suppAt_subset_ty hN hΛ φ hφ)
  have := normW_image_suppAt_subset_ty hN hΛ (A.X.inv φ) hφ'
  rwa [A.X.src_inv, A.X.tgt_inv] at this

/-- `dom-supp(Λ)` of an sc⁺-multisection over `∂X` is saturated. -/
theorem isSaturated_boundaryDomSupp_ty {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N)
    {Λ : A.W → ℚ≥0} (hΛ : IsBoundaryScPlusMultisection A Λ) :
    A.X.IsSaturated (boundaryDomSupp Λ) := by
  refine isSaturated_closure_gl (A.X.isSaturated_iff.2 fun φ hφ => ?_)
  obtain ⟨hb, w, hw, hw0, hpos⟩ := hφ
  have hw1 := hΛ.suppAt_subset_oneSet_ty hb ⟨hw, hpos⟩
  refine ⟨A.X.isSaturated_iff.1 isSaturated_boundary_gl φ hb, A.E.μ ⟨(φ, w), hw⟩, A.E.P_μ _,
    fun h0 => hw0 ?_, by rw [hΛ.1 ⟨(φ, w), hw⟩ hb]; exact hpos⟩
  have e := normW_μ hN hw hw1
  rw [h0, normW_fiberZero hN.isAuxNorm] at e
  have := (normW_eq_zero_iff hN.isAuxNorm hw1).1 e.symm
  rwa [hw] at this

theorem boundaryDomSupp_subset_boundary_ty (Λ : A.W → ℚ≥0) :
    boundaryDomSupp Λ ⊆ A.X.PObj.boundary :=
  closure_minimal (fun _ hx => hx.1) A.X.PObj.isClosed_boundary

/-! ### Upper semicontinuity of `N(Λ)` along `∂X` -/

/-- **`N(Λ)` is upper semicontinuous along `∂X`**: for `x ∈ ∂X` and `c > N(Λ)(x)` there is an
open `O ∋ x` with `N(Λ) < c` on `O ∩ ∂X`.  (The `sᵢ` of a structure at `x` extend to
sc⁺-sections `s̄ᵢ` on `V(x)`, LX's `exists_scPlusSectionOn_extension_of_face`; `N ∘ s̄ᵢ` is
continuous and `N(Λ)(y) = maxᵢ N(sᵢ(y))` on `U(x)`.) -/
theorem exists_nhds_pointwiseNorm_lt_ty
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity) {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N)
    {Λ : A.W → ℚ≥0} (hΛ : IsBoundaryScPlusMultisection A Λ) {x : A.Obj}
    (hx : x ∈ A.X.PObj.boundary) {c : ℝ} (hc : pointwiseNorm N Λ x < c) :
    ∃ O : Set A.Obj, IsOpen O ∧ x ∈ O ∧
      ∀ y ∈ O ∩ A.X.PObj.boundary, pointwiseNorm N Λ y < c := by
  obtain ⟨V, -, ⟨S⟩⟩ := hΛ.2 x hx
  have hxV : x ∈ V.bdry := ⟨V.mem_U, hx⟩
  choose σ hσ hσs using fun i =>
    exists_scPlusSectionOn_extension_of_face hB hpu V.isOpen_U (S.isFaceScPlus i)
  set c' := (pointwiseNorm N Λ x + c) / 2 with hc'
  have hP0 := pointwiseNorm_nonneg hN Λ x
  have hle : ∀ y ∈ V.bdry, ∀ i, normW N (S.s i y) ≤ pointwiseNorm N Λ y := by
    intro y hy i
    refine le_csSup ?_ ⟨S.s i y, (S.mem_suppAt_iff_ty hy).2 ⟨i, rfl⟩, rfl⟩
    have hsub : normW N '' suppAt Λ y ⊆ range fun j => normW N (S.s j y) := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨j, rfl⟩ := (S.mem_suppAt_iff_ty hy).1 hw
      exact ⟨j, rfl⟩
    exact ((finite_range _).subset hsub).bddAbove
  have hopen : ∀ i, IsOpen (V.U ∩ (fun y => normW N (σ i y)) ⁻¹' Iio c') := fun i =>
    ((hσ i).continuousOn_normW hN).isOpen_inter_preimage V.isOpen_U isOpen_Iio
  refine ⟨V.U ∩ ⋂ i, (V.U ∩ (fun y => normW N (σ i y)) ⁻¹' Iio c'),
    V.isOpen_U.inter (isOpen_iInter_of_finite hopen),
    ⟨V.mem_U, mem_iInter.2 fun i => ⟨V.mem_U, ?_⟩⟩, ?_⟩
  · change normW N (σ i x) < c'
    rw [hσs i x hxV]
    linarith [hle x hxV i]
  · rintro y ⟨⟨hyU, hyi⟩, hyb⟩
    have hyV : y ∈ V.bdry := ⟨hyU, hyb⟩
    have hle' : pointwiseNorm N Λ y ≤ c' := by
      refine Real.sSup_le ?_ (by linarith)
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨i, rfl⟩ := (S.mem_suppAt_iff_ty hyV).1 hw
      have h2 := (mem_iInter.1 hyi i).2
      simp only [mem_preimage, mem_Iio] at h2
      rw [← hσs i y hyV]
      exact h2.le
    linarith

/-! ### Step (a) of the proof of Theorem 15.3.9 -/

/-- **Step (a) of the proof of Theorem 15.3.9, p. 698** (gap TX-1): TX's
`lemma_15_3_9_cutoff_statement A` holds when every object lies in a tame strong bundle chart.
The functor is `h₀ = (ψ g) ∘ π` on the paracompact Hausdorff orbit space `|X|`: `g` continuous
with `0 ≤ g < h` and `g > N(Λ)` on `|dom-supp(Λ)|` (convex local choices glued by a partition of
unity; `N(Λ)` is upper semicontinuous along `∂X`, `exists_nhds_pointwiseNorm_lt_ty`), and `ψ` an
Urysohn function, `1` on `|dom-supp(Λ)|`, `0` off an open `V` with `cl V ⊆ |U|`. -/
theorem lemma_15_3_9_cutoff_hyp
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source) :
    lemma_15_3_9_cutoff_statement A := by
  intro _ hpara hpu Λ hΛ N hN U hUo hUsat hdomU h hc hfun hpos hNh
  have : ParacompactSpace A.X.OrbitSpace := hpara
  have hN1 : A.B.IsAuxNorm N := hN.isAuxNorm
  set C := boundaryDomSupp Λ with hCdef
  have hCsat : A.X.IsSaturated C := isSaturated_boundaryDomSupp_ty hN hΛ
  have hCcl : IsClosed C := isClosed_closure
  have hCb : C ⊆ A.X.PObj.boundary := boundaryDomSupp_subset_boundary_ty Λ
  have hiso : ∀ x y, A.X.π x = A.X.π y → h x = h y := by
    intro x y hxy
    obtain ⟨φ, hs, ht⟩ := A.X.π_eq_π_iff.1 hxy
    rw [← hs, ← ht, hfun]
  have hNiso : ∀ x y, A.X.π x = A.X.π y → x ∈ A.X.PObj.boundary →
      pointwiseNorm N Λ x = pointwiseNorm N Λ y := by
    intro x y hxy hx
    obtain ⟨φ, hs, ht⟩ := A.X.π_eq_π_iff.1 hxy
    rw [← hs] at hx
    rw [← hs, ← ht]
    exact (pointwiseNorm_tgt_of_boundary_ty hN hΛ φ hx).symm
  -- the convex family `t(q)`
  classical
  let t : A.X.OrbitSpace → Set ℝ := fun q => Ici 0 ∩ ⋂ x ∈ A.X.π ⁻¹' {q},
    Iio (h x) ∩ (if x ∈ C then Ioi (pointwiseNorm N Λ x) else univ)
  have hmem : ∀ q (y : ℝ), y ∈ t q ↔ 0 ≤ y ∧ ∀ x, A.X.π x = q →
      y < h x ∧ (x ∈ C → pointwiseNorm N Λ x < y) := by
    intro q y
    simp only [t, mem_inter_iff, mem_Ici, mem_iInter, mem_preimage, mem_singleton_iff, mem_Iio]
    refine and_congr Iff.rfl (forall_congr' fun x => imp_congr_right fun _ =>
      and_congr Iff.rfl ?_)
    split_ifs with hx
    · exact ⟨fun h' _ => h', fun h' => h' hx⟩
    · exact ⟨fun _ h' => absurd h' hx, fun _ => mem_univ _⟩
  have hconv : ∀ q, Convex ℝ (t q) := fun q =>
    (convex_Ici 0).inter (convex_iInter₂ fun x _ => (convex_Iio _).inter (by
      split_ifs
      exacts [convex_Ioi _, convex_univ]))
  have hloc : ∀ q, ∃ c : ℝ, ∀ᶠ q' in 𝓝 q, c ∈ t q' := by
    intro q
    obtain ⟨x, rfl⟩ := A.X.surjective_π q
    obtain ⟨c, O, hO, hxO, hc0, hcO⟩ : ∃ c : ℝ, ∃ O : Set A.Obj, IsOpen O ∧ x ∈ O ∧ 0 ≤ c ∧
        ∀ y ∈ O, c < h y ∧ (y ∈ C → pointwiseNorm N Λ y < c) := by
      by_cases hxC : x ∈ C
      · have hxb := hCb hxC
        have hlt := hNh x hxb
        obtain ⟨O, hO, hxO, hOb⟩ := exists_nhds_pointwiseNorm_lt_ty hB hpu hN1 hΛ hxb
          (c := (pointwiseNorm N Λ x + h x) / 2) (by linarith)
        refine ⟨(pointwiseNorm N Λ x + h x) / 2, O ∩ {y | (pointwiseNorm N Λ x + h x) / 2 < h y},
          hO.inter (isOpen_lt continuous_const hc), ⟨hxO, ?_⟩, ?_,
          fun y hy => ⟨hy.2, fun hyC => hOb y ⟨hy.1, hCb hyC⟩⟩⟩
        · change (pointwiseNorm N Λ x + h x) / 2 < h x
          linarith
        · linarith [pointwiseNorm_nonneg hN1 Λ x]
      · refine ⟨h x / 2, Cᶜ ∩ {y | h x / 2 < h y},
          hCcl.isOpen_compl.inter (isOpen_lt continuous_const hc), ⟨hxC, ?_⟩, ?_,
          fun y hy => ⟨hy.2, fun hyC => absurd hyC hy.1⟩⟩
        · change h x / 2 < h x
          linarith [hpos x]
        · linarith [hpos x]
    refine ⟨c, Filter.mem_of_superset
      ((A.X.proposition_7_1_8 O hO).mem_nhds (mem_image_of_mem _ hxO)) ?_⟩
    rintro _ ⟨y, hyO, rfl⟩
    change c ∈ t (A.X.π y)
    rw [hmem]
    refine ⟨hc0, fun x' hx' => ?_⟩
    have hh' : h x' = h y := hiso x' y hx'
    refine ⟨hh' ▸ (hcO y hyO).1, fun hx'C => ?_⟩
    have hyC : y ∈ C := by
      have : y ∈ A.X.π ⁻¹' (A.X.π '' C) := ⟨x', hx'C, hx'⟩
      rwa [hCsat] at this
    rw [hNiso x' y hx' (hCb hx'C)]
    exact (hcO y hyO).2 hyC
  obtain ⟨g, hg⟩ := exists_continuous_forall_mem_convex_of_local_const hconv hloc
  have hg' : ∀ q, 0 ≤ g q ∧ ∀ x, A.X.π x = q →
      g q < h x ∧ (x ∈ C → pointwiseNorm N Λ x < g q) := fun q => (hmem q (g q)).1 (hg q)
  -- the Urysohn cut-off `ψ`
  have hπC : IsClosed (A.X.π '' C) := A.X.isClosed_π_image_of_isSaturated hCsat hCcl
  have hπU : IsOpen (A.X.π '' U) := A.X.proposition_7_1_8 U hUo
  obtain ⟨V, hVo, hCV, hVU⟩ := normal_exists_closure_subset hπC hπU (image_mono hdomU)
  obtain ⟨ψ, hψ0, hψ1, hψI⟩ := exists_continuous_zero_one_of_isClosed hVo.isClosed_compl hπC
    (disjoint_compl_left_iff_subset.2 hCV)
  refine ⟨fun x => ψ (A.X.π x) * g (A.X.π x),
    (ψ.continuous.comp A.X.continuous_π).mul (g.continuous.comp A.X.continuous_π),
    fun x => mul_nonneg (hψI _).1 (hg' _).1, fun φ => ?_, ?_, fun x => ?_, fun x hx => ?_⟩
  · simp only
    rw [A.X.π_eq_π_iff.2 ⟨φ, rfl, rfl⟩]
  · have h1 : tsupport (fun q => ψ q * g q) ⊆ closure V := by
      refine (tsupport_mul_subset_left).trans (closure_mono fun q hq => ?_)
      by_contra hqV
      exact hq (hψ0 hqV)
    have h2 := tsupport_comp_subset_preimage (fun q => ψ q * g q) A.X.continuous_π
    intro x hx
    have h3 : x ∈ A.X.π ⁻¹' (A.X.π '' U) := hVU (h1 (h2 hx))
    rwa [hUsat] at h3
  · have := ((hg' (A.X.π x)).2 x rfl).1
    have hle : ψ (A.X.π x) * g (A.X.π x) ≤ g (A.X.π x) :=
      mul_le_of_le_one_left (hg' _).1 (hψI _).2
    exact hle.trans_lt this
  · have h1 : ψ (A.X.π x) = 1 := hψ1 (mem_image_of_mem _ hx)
    simp only [h1, one_mul]
    exact ((hg' (A.X.π x)).2 x rfl).2 hx

/-! ### Theorem 15.3.9 with step (a) proved -/

/-- **Theorem 15.3.9 (Transversal Extension Theorem), p. 694, from the extension of §§14.3–14.5
and steps (c)–(d)**: if every object lies in a tame strong bundle chart (`hB`), GL's
`theorem_14_1_9_extension_statement A` (the output of §§14.3–14.5) and TX's
`theorem_15_3_7_relative_statement A` (the relative general position step) give
`theorem_15_3_9_statement A`.  Step (a) is `lemma_15_3_9_cutoff_hyp`, the size control of
Theorem 14.1.9 is GL's `theorem_14_1_9_hyp`. -/
theorem theorem_15_3_9_of_extension_ty
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source)
    (hext : theorem_14_1_9_extension_statement A) (hrel : theorem_15_3_7_relative_statement A) :
    theorem_15_3_9_statement A :=
  theorem_15_3_9_hyp (theorem_14_1_9_hyp hext) (lemma_15_3_9_cutoff_hyp hB) hrel

end SBLocalization

end Polyfold
