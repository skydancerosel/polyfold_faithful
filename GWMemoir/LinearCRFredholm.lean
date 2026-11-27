import GWMemoir.LinearCRSphere
import Polyfold.Chapter1.FredholmIndex
import Polyfold.Chapter1.CylinderCompactInclusions

/-!
# The linearized Cauchy–Riemann operator on the three-pointed sphere is Fredholm

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Props 4.7, 4.23, 4.25
near the constant maps).  For `D = linCR` at the constant map `u ≡ q` from `sphere3`:

* the two classical inputs are stated as named propositions: **`EllipticEstimate`**,
  `‖ξ‖_{H^{3,δ₀}} ≤ C (‖Dξ‖_{H^{2,δ₀}} + ‖ξ‖_{L²})`, and **`CokernelVanishes`**, the surjectivity
  of `D` (`H^{0,1}(P¹, ℂⁿ) = 0`);
* **`isClosed_range_of_estimate`** (Peetre): an estimate `‖x‖ ≤ C (‖Tx‖ + ‖Kx‖)` with `K`
  compact and `ker T` finite-dimensional gives a closed range; with the compact inclusion
  `H^{3,δ₀} → L²` (`isCompactOperator_inclH`, `0 < δ₀`) this gives
  **`linCR_isClosed_range`** from `EllipticEstimate`;
* **`linCR_ker_equiv`**: `ker D ≃ E` (proved, `GWMemoir.LinearCRSphere`);
* **`linCR_isFredholm`**: `CokernelVanishes` makes `D` Fredholm (Mathlib's `IsFredholm`), and
  **`linCR_index`**: its index is `dim E = 2n`;
* **`linCR_index_uSpace`**: on a closed subspace `E_u` of finite codimension `c`, the restriction
  has index `dim E - c` (`linIndex_comp`); for the three constraints `H = 0` at `e₀, e₁, e₂` its
  kernel is `0` (`linCR_ker_three_points`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology NNReal
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev ContinuousLinearMap

noncomputable section

namespace GWMemoir

/-! ## 1. Peetre's lemma -/

section Peetre

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Peetre's lemma**: if `‖x‖ ≤ C (‖Tx‖ + ‖Kx‖)` with `K` compact and `ker T`
finite-dimensional, then `T` has closed range. -/
theorem isClosed_range_of_estimate {T : E →L[ℝ] F} {K : E →L[ℝ] G} (hK : IsCompactOperator K)
    (hker : FiniteDimensional ℝ T.ker) {C : ℝ} (hC : ∀ x, ‖x‖ ≤ C * (‖T x‖ + ‖K x‖)) :
    IsClosed (T.range : Set F) := by
  obtain ⟨M, hMc, hcompl⟩ :=
    (Submodule.ClosedComplemented.of_finiteDimensional T.ker).exists_isClosed_isCompl
  have : CompleteSpace M := hMc.completeSpace_coe
  set TM : M →L[ℝ] F := T.comp M.subtypeL
  set C' : ℝ≥0 := ⟨2 * max C 0, by positivity⟩
  -- `Ψ = (T, K)` on `M` is antilipschitz
  set Ψ : M →L[ℝ] F × G := TM.prod (K.comp M.subtypeL)
  have hΨ : AntilipschitzWith C' Ψ := by
    refine AddMonoidHomClass.antilipschitz_of_bound Ψ fun x => ?_
    have h1 := hC x
    have h2 : ‖T x‖ ≤ ‖Ψ x‖ := le_max_left _ _
    have h3 : ‖K x‖ ≤ ‖Ψ x‖ := le_max_right _ _
    change ‖(x : E)‖ ≤ 2 * max C 0 * ‖Ψ x‖
    have h4 : C * (‖T x‖ + ‖K x‖) ≤ max C 0 * (‖T x‖ + ‖K x‖) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    nlinarith [le_max_right C 0]
  have hbd : ∃ c > 0, ∀ x : M, c * ‖x‖ ≤ ‖TM x‖ := by
    by_contra hcon
    push Not at hcon
    have hseq : ∀ n : ℕ, ∃ x : M, ‖x‖ = 1 ∧ ‖TM x‖ < 1 / (n + 1) := by
      intro n
      obtain ⟨x, hx⟩ := hcon (1 / (n + 1)) (by positivity)
      have hx0 : x ≠ 0 := by rintro rfl; simp at hx
      have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
      refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
      · rw [map_smul, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul, div_lt_iff₀ hxn]
        linarith
    choose x hx1 hx using hseq
    obtain ⟨S, hS, hSsub⟩ := hK.image_closedBall_subset_compact (f := (K : E →ₗ[ℝ] G)) 1
    have hmem : ∀ n, K (x n) ∈ S := fun n => hSsub ⟨x n, by
      rw [Metric.mem_closedBall, dist_zero_right]; exact (hx1 n).le, rfl⟩
    obtain ⟨y, -, φ, hφ, hlim⟩ := hS.tendsto_subseq hmem
    have hT0 : Tendsto (fun n => TM (x (φ n))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hx (φ n)).le)
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
    have hΨlim : Tendsto (fun n => Ψ (x (φ n))) atTop (𝓝 (0, y)) := hT0.prodMk_nhds hlim
    have hcau : CauchySeq (fun n => x (φ n)) := by
      have h' : CauchySeq (fun n => Ψ (x (φ n))) := hΨlim.cauchySeq
      have h'' := (hΨ.isUniformInducing Ψ.uniformContinuous).cauchy_map_iff
        (F := map (fun n => x (φ n)) atTop)
      rw [Filter.map_map] at h''
      exact h''.1 h'
    obtain ⟨x₀, hx₀⟩ := cauchySeq_tendsto_of_complete hcau
    have hn : ‖x₀‖ = 1 := by
      have := (continuous_norm.tendsto _).comp hx₀
      simp only [Function.comp_def, hx1] at this
      exact (tendsto_nhds_unique tendsto_const_nhds this).symm
    have hT : TM x₀ = 0 := tendsto_nhds_unique ((TM.continuous.tendsto _).comp hx₀) hT0
    have hxk : (x₀ : E) ∈ T.ker := hT
    have : (x₀ : E) = 0 :=
      (Submodule.disjoint_def.1 hcompl.disjoint) _ hxk x₀.2
    rw [show ‖x₀‖ = ‖(x₀ : E)‖ from rfl, this, norm_zero] at hn
    exact zero_ne_one hn
  obtain ⟨c, hc, hcb⟩ := hbd
  have hanti : AntilipschitzWith ⟨c⁻¹, by positivity⟩ TM :=
    AddMonoidHomClass.antilipschitz_of_bound TM fun x => by
      change ‖x‖ ≤ c⁻¹ * ‖TM x‖
      rw [← div_eq_inv_mul, le_div_iff₀ hc, mul_comm]; exact hcb x
  have hrange : (T.range : Set F) = range TM := by
    ext f
    constructor
    · rintro ⟨e, rfl⟩
      obtain ⟨n, hn, m, hm, rfl⟩ := Submodule.mem_sup.1 (hcompl.sup_eq_top ▸ Submodule.mem_top :
        e ∈ T.ker ⊔ M)
      exact ⟨⟨m, hm⟩, by simp [TM, show T n = 0 from hn]⟩
    · rintro ⟨m, rfl⟩; exact ⟨m, rfl⟩
  rw [hrange]
  exact hanti.isClosed_range TM.uniformContinuous

end Peetre

/-! ## 2. The operator on `sphere3`: kernel, the named propositions, Fredholm -/

section Fredholm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q} {A : SectionAtlas (E := E) sphere3 (fun _ => q)}
  (G : GlueData A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

instance sectionSpace_completeSpace : CompleteSpace (sectionSpace A δ h0 hmono) :=
  (isClosed_sectionSpace A δ h0 hmono).completeSpace_coe

/-- `D` on `sphere3`, `J₀ = J(q)`. -/
abbrev linCR3 : sectionSpace A δ h0 hmono →L[ℝ] fibreSpace J A δ h0 hmono :=
  linCR rfl sphere3_chartsOnto (fun _ => rfl) G J

lemma constBlocks_mem_sectionSpace (e : E) :
    constBlocks A δ h0 hmono e ∈ sectionSpace A δ h0 hmono :=
  Submodule.le_topologicalClosure _ (constBlocks_mem A δ h0 hmono e)

lemma constBlocks_add (e e' : E) :
    constBlocks A δ h0 hmono (e + e') = constBlocks A δ h0 hmono e + constBlocks A δ h0 hmono e' :=
  isRep_unique rfl (isRep_constBlocks A (e + e'))
    ((isRep_constBlocks A e).add (isRep_constBlocks A e'))

lemma constBlocks_smul (c : ℝ) (e : E) :
    constBlocks A δ h0 hmono (c • e) = c • constBlocks A δ h0 hmono e :=
  isRep_unique rfl (isRep_constBlocks A (c • e)) ((isRep_constBlocks A e).smul c)

/-- The constant sections, as a linear map into the kernel of `D`. -/
def constKer : E →ₗ[ℝ] (linCR3 J G δ h0 hmono).ker where
  toFun e := ⟨⟨constBlocks A δ h0 hmono e, constBlocks_mem_sectionSpace δ h0 hmono e⟩,
    (linCR_ker_sphere3' J G δ h0 hmono _).2 ⟨e, rfl⟩⟩
  map_add' e e' := by
    apply Subtype.ext; apply Subtype.ext; exact constBlocks_add δ h0 hmono e e'
  map_smul' c e := by
    apply Subtype.ext; apply Subtype.ext; exact constBlocks_smul δ h0 hmono c e

/-- **`ker D ≃ E`**: the kernel of `D` on `H^{3,δ₀}_c(S², u*TQ)` is the constants. -/
def linCR_ker_equiv : E ≃ₗ[ℝ] (linCR3 J G δ h0 hmono).ker :=
  LinearEquiv.ofBijective (constKer J G δ h0 hmono)
    ⟨fun e e' h => constBlocks_injective δ h0 hmono
      (congrArg (fun w : (linCR3 J G δ h0 hmono).ker =>
        ((w : sectionSpace A δ h0 hmono) : (blocks A δ h0 hmono) 0)) h), by
      rintro ⟨w, hw⟩
      obtain ⟨e, he⟩ := (linCR_ker_sphere3' J G δ h0 hmono w).1 hw
      exact ⟨e, Subtype.ext (Subtype.ext he.symm)⟩⟩

theorem finrank_linCR_ker :
    Module.finrank ℝ ((linCR3 J G δ h0 hmono).ker) = Module.finrank ℝ E :=
  (linCR_ker_equiv J G δ h0 hmono).finrank_eq.symm

instance : FiniteDimensional ℝ ((linCR3 J G δ h0 hmono).ker) :=
  LinearEquiv.finiteDimensional (linCR_ker_equiv J G δ h0 hmono)

/-- The `L²` blocks: `H^{3,δ₀} → H^{2,0} → H^{0,0} = L²` on each disc block. -/
def l2Op (hδ : 0 < δ 0) : sectionSpace A δ h0 hmono →L[ℝ]
    (Fin A.nd × Fin (Module.finrank ℝ E) → H 0 (le_refl (0 : ℝ))) :=
  ContinuousLinearMap.pi fun ik =>
    ((inclH (le_refl (0 : ℝ)) (le_refl (0 : ℝ)) (Nat.zero_le 2) le_rfl).comp
      (inclH (m := 2) (le_refl (0 : ℝ)) (Neck.δ_nonneg δ h0 hmono 0) (Nat.le_succ 2) hδ.le)).comp
        ((secProj δ h0 hmono ik).comp (sectionSpace A δ h0 hmono).subtypeL)

lemma isCompactOperator_pi {ι : Type*} [Fintype ι] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {Y : ι → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)]
    {f : ∀ i, X →L[ℝ] Y i} (hf : ∀ i, IsCompactOperator (f i)) :
    IsCompactOperator (ContinuousLinearMap.pi f) := by
  choose K hK hKn using fun i => hf i
  refine ⟨univ.pi K, isCompact_univ_pi hK, ?_⟩
  have : (⇑(ContinuousLinearMap.pi f)) ⁻¹' univ.pi K = ⋂ i, (f i) ⁻¹' K i := by
    ext x; simp
  rw [this]
  exact (Filter.iInter_mem).2 hKn

/-- The `L²` blocks are compact (Rellich, `isCompactOperator_inclH`). -/
theorem isCompactOperator_l2Op (hδ : 0 < δ 0) : IsCompactOperator (l2Op (A := A) δ h0 hmono hδ) :=
  isCompactOperator_pi fun _ => by
    rw [coe_comp, coe_comp]
    exact ((((isCompactOperator_inclH (m := 2) (le_refl (0 : ℝ))
    (Neck.δ_nonneg δ h0 hmono 0) hδ)).clm_comp _).comp_clm _)

/-- **The elliptic estimate** (Memoir §4, at a constant map):
`‖ξ‖_{H^{3,δ₀}} ≤ C (‖Dξ‖_{H^{2,δ₀}} + ‖ξ‖_{L²})`.  Not formalized here. -/
def EllipticEstimate (hδ : 0 < δ 0) : Prop :=
  ∃ C : ℝ, ∀ w : sectionSpace A δ h0 hmono,
    ‖w‖ ≤ C * (‖linCR3 J G δ h0 hmono w‖ + ‖l2Op (A := A) δ h0 hmono hδ w‖)

/-- **The vanishing of the cokernel** (`H^{0,1}(P¹, ℂⁿ) = 0`): `D` is onto the fibre.  Not
formalized here. -/
def CokernelVanishes : Prop := Surjective (linCR3 J G δ h0 hmono)

/-- **`EllipticEstimate` gives a closed range** (Peetre's lemma, with the proved
finite-dimensional kernel and the compact inclusion into `L²`). -/
theorem linCR_isClosed_range (hδ : 0 < δ 0) (h : EllipticEstimate J G δ h0 hmono hδ) :
    IsClosed ((linCR3 J G δ h0 hmono).range : Set (fibreSpace J A δ h0 hmono)) := by
  obtain ⟨C, hC⟩ := h
  exact isClosed_range_of_estimate (isCompactOperator_l2Op (A := A) δ h0 hmono hδ) inferInstance hC

/-- **`D` is Fredholm** given `CokernelVanishes` (Memoir §4; the kernel is proved). -/
theorem linCR_isFredholm (h : CokernelVanishes J G δ h0 hmono) :
    IsFredholm (linCR3 J G δ h0 hmono) := by
  have htop : (linCR3 J G δ h0 hmono).range = ⊤ :=
    LinearMap.range_eq_top.2 (show Surjective (linCR3 J G δ h0 hmono) from h)
  refine isFredholm_of_banach _ inferInstance ?_ ?_
  · rw [htop]; exact isClosed_univ
  · rw [htop]; exact Submodule.CoFG.top

/-- **The index of `D` is `dim E = 2n`.** -/
theorem linCR_index (h : CokernelVanishes J G δ h0 hmono) :
    fredholmIndex (linCR3 J G δ h0 hmono) = Module.finrank ℝ E := by
  have htop : LinearMap.range (linCR3 J G δ h0 hmono).toLinearMap = ⊤ :=
    LinearMap.range_eq_top (f := (linCR3 J G δ h0 hmono).toLinearMap) |>.2 h
  have : Subsingleton (fibreSpace J A δ h0 hmono ⧸
      LinearMap.range (linCR3 J G δ h0 hmono).toLinearMap) := by
    exact Submodule.Quotient.subsingleton_iff.2 htop
  rw [fredholmIndex, linIndex, Module.finrank_zero_of_subsingleton (R := ℝ)
    (M := fibreSpace J A δ h0 hmono ⧸ LinearMap.range (linCR3 J G δ h0 hmono).toLinearMap),
    Nat.cast_zero, sub_zero]
  exact_mod_cast finrank_linCR_ker J G δ h0 hmono

/-- **The index on a closed subspace `M` of finite codimension `c`** (such as `E_u`):
`ind (D|_M) = dim E - c`. -/
theorem linCR_index_restrict (h : CokernelVanishes J G δ h0 hmono)
    (M : Submodule ℝ (sectionSpace A δ h0 hmono))
    [FiniteDimensional ℝ (sectionSpace A δ h0 hmono ⧸ M)] :
    HasFiniteIndex ((linCR3 J G δ h0 hmono).toLinearMap ∘ₗ M.subtype) ∧
      linIndex ((linCR3 J G δ h0 hmono).toLinearMap ∘ₗ M.subtype) =
        Module.finrank ℝ E - Module.finrank ℝ (sectionSpace A δ h0 hmono ⧸ M) := by
  have hD := Polyfold.IsFredholm.hasFiniteIndex (linCR_isFredholm J G δ h0 hmono h)
  have hι : HasFiniteIndex M.subtype := by
    refine ⟨?_, ?_⟩
    · rw [Submodule.ker_subtype]; infer_instance
    · rw [Submodule.range_subtype]; infer_instance
  refine ⟨hι.comp hD, ?_⟩
  rw [linIndex_comp hι hD]
  have hiD : linIndex (linCR3 J G δ h0 hmono).toLinearMap = Module.finrank ℝ E :=
    linCR_index J G δ h0 hmono h
  have hiι : linIndex M.subtype = - Module.finrank ℝ (sectionSpace A δ h0 hmono ⧸ M) := by
    rw [linIndex, Submodule.ker_subtype, Submodule.range_subtype, finrank_bot, Nat.cast_zero,
      zero_sub]
  rw [hiD, hiι]; ring

end Fredholm

end GWMemoir
