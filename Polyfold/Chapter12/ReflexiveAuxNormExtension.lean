import Polyfold.Chapter12.ReflexiveAuxNormEp
import Polyfold.Chapter12.AuxNormExtension
import Polyfold.Chapter12.BumpEp
import Polyfold.Chapter8.NonVacuityBundle
import Polyfold.Chapter5.ReflexiveCompactness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 12,
§12.2, **Theorem 12.2.13** (extension of reflexive auxiliary norms), p. 578.

# Extension of reflexive auxiliary norms from `W|∂X`

## The text, paraphrased

(Theorem 12.2.13) For a strong bundle with reflexive `1`-fibres over a tame ep-groupoid, a
reflexive auxiliary norm `N` for `W_{0,1}|∂X` extends to a reflexive auxiliary norm `Ñ` of
`W_{0,1}`.  (Proof) The local extension of the proof of Theorem 12.2.7 is well behaved under mixed
limits "by inspection"; near interior points reflexive local norms exist; partitions of unity as in
Theorem 12.2.11.

## What is formalized

* `EpStrongBundle.IsReflexiveAuxNormOn A N`: Definition 12.2.10 over a set `A` of objects
  (`EpStrongBundle.IsAuxNormOn` with the `liminf` clause for mixed convergent sequences over `A`).
* `EpStrongBundle.HasReflexiveLocalExtensions X B N`: the local step of the proof, with the lower
  semicontinuity the text checks "by inspection": every `x ∈ ∂X` has an open `V ∋ x` and a local
  auxiliary norm on `V` which is lower semicontinuous along mixed convergent sequences over `V`
  and equals `N` over `V ∩ ∂X`.  It implies the hypothesis `HasLocalExtensions` of
  `theorem_12_2_7_hyp` (`HasReflexiveLocalExtensions.hasLocalExtensions`).
* **`EpStrongBundle.theorem_12_2_13_hyp`**: the theorem with this local step as a hypothesis.  The
  global part of the proof is proved: interior points carry the average of a Part I reflexive
  auxiliary norm (Proposition 5.1.8); averaging, transport and gluing keep the lower
  semicontinuity (`mixedLscAt_avgNorm`, `mixedLscAt_transNorm`, `isReflexiveAuxNorm_glueNorm`).
  Tameness and the paracompactness of `|X|` (which the text uses through Theorem 12.2.7) are
  needed only for the local step, resp. the partition of unity.
* Satisfiability: `hasReflexiveLocalExtensions_of_isReflexiveAuxNorm`,
  `theorem_12_2_13_hyp_witness`; concretely `TrivialBundle.epBundle_reflexive_witness` (the trivial
  bundle `ℝⁿ × ℝᵏ → ℝⁿ` over the trivial ep-groupoid of `ℝⁿ` has reflexive `1`-fibres,
  paracompact `|X|`, a reflexive auxiliary norm, and an `N` satisfying all hypotheses of
  `theorem_12_2_13_hyp`).

## Elsewhere

The local step is `ReflexiveLocalExtension.hasReflexiveLocalExtensions_of_isTame`; Theorem
12.2.13 is `theorem_12_2_13` there.
-/

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

universe u v

section Thm12213

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable (E : EpStrongBundle X B)

/-- **Definition 12.2.10 over a subset `A` of the objects** (Theorem 12.2.13's "reflexive
auxiliary norm for `W_{0,1}|∂X`", `A = ∂X`): an auxiliary norm over `A` (`IsAuxNormOn`) with
`N(w) ≤ liminf N(w_k)` for mixed convergent sequences `w_k →ᵐ w` in `W_{0,1}|A`. -/
structure IsReflexiveAuxNormOn (A : Set Obj) (N : B.One → ℝ) : Prop
    extends E.IsAuxNormOn A N where
  le_liminf : ∀ (w : ℕ → B.One) (y : B.One), (∀ k, P (B.oneVal (w k)) ∈ A) →
    P (B.oneVal y) ∈ A → E.MixedTendsto w y →
      (N y : EReal) ≤ liminf (fun k => (N (w k) : EReal)) atTop

variable {E}

/-- The restriction of a reflexive auxiliary norm is one over every subset. -/
theorem IsReflexiveAuxNorm.isReflexiveAuxNormOn {N : B.One → ℝ} (hN : E.IsReflexiveAuxNorm N)
    (A : Set Obj) : E.IsReflexiveAuxNormOn A N :=
  ⟨hN.toIsAuxNorm.isAuxNormOn A, fun w y _ _ hm => hN.le_liminf w y hm⟩

variable (X B) in
/-- **The local extension step of the proof of Theorem 12.2.13** (the hypothesis of
`theorem_12_2_13_hyp`): every `x ∈ ∂X` has an open neighbourhood `V` and a local auxiliary norm `M`
on `V` which is lower semicontinuous along mixed convergent sequences with limit over `V`, with
`M = N` on `W_{0,1}|(V ∩ ∂X)`. -/
def HasReflexiveLocalExtensions (N : B.One → ℝ) : Prop :=
  ∀ x ∈ X.PObj.boundary, ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧ ∃ M : B.One → ℝ,
    B.IsLocalAuxNorm V M ∧ (∀ y : B.One, P (B.oneVal y) ∈ V → B.MixedLscAt M y) ∧
      ∀ w : B.One, P (B.oneVal w) ∈ V ∩ X.PObj.boundary → M w = N w

/-- The reflexive local step gives the local step of Theorem 12.2.7. -/
theorem HasReflexiveLocalExtensions.hasLocalExtensions {N : B.One → ℝ}
    (h : HasReflexiveLocalExtensions X B N) : HasLocalExtensions X B N := fun x hx => by
  obtain ⟨V, hVo, hxV, M, hM, -, hMN⟩ := h x hx
  exact ⟨V, hVo, hxV, M, hM, hMN⟩

/-- **Theorem 12.2.13 with the local extension step as a hypothesis**, p. 578: for a strong bundle
with reflexive `1`-fibres over an ep-groupoid with paracompact `|X|`, a reflexive auxiliary norm
`N` for `W_{0,1}|∂X` with reflexive local extensions near every boundary point extends to a
reflexive auxiliary norm `Ñ` of `W_{0,1}`.  The text's proof with the local coordinate step
replaced by `HasReflexiveLocalExtensions`; the interior local norms, the averaging, the transport
and the gluing (with the lower semicontinuity) are proved, without tameness. -/
theorem theorem_12_2_13_hyp (h : X.HasParacompactOrbitSpace) (hB : E.HasReflexiveFibers)
    {N : B.One → ℝ} (hN : E.IsReflexiveAuxNormOn X.PObj.boundary N)
    (hloc : HasReflexiveLocalExtensions X B N) :
    ∃ Ñ : B.One → ℝ, E.IsReflexiveAuxNorm Ñ ∧
      ∀ w : B.One, P (B.oneVal w) ∈ X.PObj.boundary → Ñ w = N w := by
  classical
  have := B.paracompactSpace_pullback X.PMor X.src
  have : ParacompactSpace X.OrbitSpace := h
  have := X.theorem_7_3_1_metrizable h
  obtain ⟨N₀, hN₀⟩ := proposition_5_1_8_exists hB
  have hdata : ∀ x : Obj, ∃ (R : X.NaturalRep x) (M : B.One → ℝ), B.IsLocalAuxNorm R.U M ∧
      (∀ y : B.One, P (B.oneVal y) ∈ R.U → B.MixedLscAt M y) ∧
      (x ∈ X.PObj.boundary → ∀ w : B.One, P (B.oneVal w) ∈ R.U ∩ X.PObj.boundary → M w = N w) ∧
      (x ∉ X.PObj.boundary → R.U ⊆ X.PObj.boundaryᶜ) := by
    intro x
    by_cases hx : x ∈ X.PObj.boundary
    · obtain ⟨V, hVo, hxV, M, hM, hMl, hMN⟩ := hloc x hx
      obtain ⟨R, hRV⟩ := X.theorem_7_1_13 x hVo hxV
      exact ⟨R, M, hM.mono hRV, fun y hy => hMl y (hRV hy),
        fun _ w hw => hMN w ⟨hRV hw.1, hw.2⟩, fun h' => absurd hx h'⟩
    · obtain ⟨R, hRV⟩ := X.theorem_7_1_13 x X.isOpen_compl_boundary hx
      exact ⟨R, N₀, hN₀.toIsAuxNorm.isLocalAuxNorm _, fun y _ => hN₀.mixedLscAt y,
        fun h' => absurd h' hx, fun _ => hRV⟩
  choose R M hM hMl hMN hRint using hdata
  have hM' : ∀ x, B.IsLocalAuxNorm (R x).U (E.avgNorm (R x) (M x)) := fun x =>
    E.isLocalAuxNorm_avgNorm (R x) (hM x)
  have hinv : ∀ x g w, P (B.oneVal w) ∈ (R x).U →
      E.avgNorm (R x) (M x) (E.actOne ((R x).Γ g) w) = E.avgNorm (R x) (M x) w :=
    fun x g w hw => E.avgNorm_actOne (R x) (M x) g hw
  have hlscM : ∀ x (y : B.One), P (B.oneVal y) ∈ (R x).U →
      B.MixedLscAt (E.avgNorm (R x) (M x)) y := fun x _ hy =>
    E.mixedLscAt_avgNorm hB (R x) (hMl x) hy
  obtain ⟨β, hβ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun x => X.π '' X.satSet (R x).U)
    (fun x => by rw [EpGroupoid.image_π_satSet]; exact X.proposition_7_1_8 _ (R x).isOpen_U)
    fun z _ => by
      obtain ⟨y, rfl⟩ := X.surjective_π z
      exact mem_iUnion.2 ⟨y, y, EpGroupoid.subset_satSet _ (R y).mem_U, rfl⟩
  set T : Obj → B.One → ℝ := fun x => E.transNorm (R x) (E.avgNorm (R x) (M x)) with hT
  refine ⟨glueNorm β T, isReflexiveAuxNorm_glueNorm (E := E) (U := fun x => X.satSet (R x).U)
    (fun x => EpGroupoid.isOpen_satSet (R x).isOpen_U)
    (fun x => EpGroupoid.isSaturated_satSet _) hβ
    (fun x => isLocalAuxNorm_transNorm (hM' x) (hinv x))
    (fun x h k ψ hk _ hh => transNorm_μ (hinv x) h k ψ hk hh)
    (fun x _ hy => mixedLscAt_transNorm hB (hinv x) (hlscM x) hy), fun w hw => ?_⟩
  -- over `∂X` every nonzero term of the glued norm is `β_x · N` (as in Theorem 12.2.7)
  have key : ∀ x, β x (X.π (P (B.oneVal w))) * T x w = β x (X.π (P (B.oneVal w))) * N w := by
    intro x
    by_cases hβ0 : β x (X.π (P (B.oneVal w))) = 0
    · rw [hβ0, zero_mul, zero_mul]
    have hyU : P (B.oneVal w) ∈ X.satSet (R x).U :=
      EpGroupoid.mem_of_π_mem_image (EpGroupoid.isSaturated_satSet _)
        (hβ x (subset_tsupport _ hβ0))
    have hxb : x ∈ X.PObj.boundary := by
      by_contra hx
      obtain ⟨φ, hφs, hφt⟩ := hyU
      exact hRint x hx hφt ((X.tgt_mem_boundary_iff φ).2 (hφs ▸ hw))
    congr 1
    change E.transNorm (R x) (E.avgNorm (R x) (M x)) w = N w
    rw [transNorm, if_pos hyU]
    have hφs := X.src_selMor (R x).U (P (B.oneVal w))
    set v := E.actOne (X.selMor (R x).U) w with hv
    have hPv : P (B.oneVal v) = X.tgt (X.selMor (R x).U (P (B.oneVal w))) := E.P_actOne hφs
    have hvU : P (B.oneVal v) ∈ (R x).U := hPv ▸ X.tgt_selMor_mem hyU
    have hvb : P (B.oneVal v) ∈ X.PObj.boundary :=
      hPv ▸ (X.tgt_mem_boundary_iff _).2 (hφs.symm ▸ hw)
    have hNv : N v = N w :=
      hN.toIsAuxNormOn.map_μ v w _ hφs.symm hw (E.oneVal_actOne_of_eq hφs.symm)
    have hterm : ∀ g, M x (E.actOne ((R x).Γ g) v) = N w := fun g => by
      have hs := (R x).src_Γ g _ hvU
      have hgb : P (B.oneVal (E.actOne ((R x).Γ g) v)) ∈ X.PObj.boundary := by
        rw [E.P_actOne hs]; exact (X.tgt_mem_boundary_iff _).2 (hs.symm ▸ hvb)
      rw [hMN x hxb _ ⟨E.actOne_Γ_mem (R x) g hvU, hgb⟩,
        hN.toIsAuxNormOn.map_μ _ v _ hs.symm hvb (E.oneVal_actOne_of_eq hs.symm), hNv]
    have := Fintype.ofFinite (X.Isotropy x)
    rw [avgNorm, finsum_congr hterm, finsum_eq_sum_of_fintype, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      inv_mul_cancel_left₀ (card_isotropy_pos X (x := x)).ne']
  rw [glueNorm, finsum_congr key, ← finsum_mul, β.sum_eq_one (mem_univ _), one_mul]

/-- **The hypothesis of `theorem_12_2_13_hyp` holds for restrictions**: the restriction to `∂X` of a
reflexive auxiliary norm of `W` has reflexive local extensions (the norm itself). -/
theorem hasReflexiveLocalExtensions_of_isReflexiveAuxNorm {N : B.One → ℝ}
    (hN : E.IsReflexiveAuxNorm N) : HasReflexiveLocalExtensions X B N := fun _ _ =>
  ⟨univ, isOpen_univ, mem_univ _, N, hN.isAuxNorm.isLocalAuxNorm univ,
    fun y _ => hN.mixedLscAt y, fun _ _ => rfl⟩

/-- **Satisfiability of the hypotheses of `theorem_12_2_13_hyp`**: with reflexive `1`-fibres and
paracompact `|X|` there is a reflexive auxiliary norm `N` for `W_{0,1}|∂X` with reflexive local
extensions (the restriction of one from Theorem 12.2.11). -/
theorem theorem_12_2_13_hyp_witness (h : X.HasParacompactOrbitSpace)
    (hB : E.HasReflexiveFibers) :
    ∃ N : B.One → ℝ, E.IsReflexiveAuxNormOn X.PObj.boundary N ∧
      HasReflexiveLocalExtensions X B N := by
  obtain ⟨N, hN⟩ := E.theorem_12_2_11_exists h hB
  exact ⟨N, hN.isReflexiveAuxNormOn _, hasReflexiveLocalExtensions_of_isReflexiveAuxNorm hN⟩

end EpStrongBundle

end Thm12213

/-! ### Non-vacuity on the trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ` -/

namespace TrivialBundle

/-- **Non-vacuity of Definition 12.2.10 and of the hypotheses of Theorems 12.2.11 and 12.2.13**:
the trivial strong bundle `ℝⁿ × ℝᵏ → ℝⁿ` over the trivial ep-groupoid of `ℝⁿ` has reflexive
`1`-fibres and paracompact orbit space, it has a reflexive auxiliary norm, and some `N` satisfies
all hypotheses of `theorem_12_2_13_hyp`. -/
theorem epBundle_reflexive_witness (n k : ℕ) :
    (epBundle n k).HasReflexiveFibers ∧
      (EpGroupoid.trivial (rnPolyfold n)).HasParacompactOrbitSpace ∧
      (∃ N, (epBundle n k).IsReflexiveAuxNorm N) ∧
      ∃ N, (epBundle n k).IsReflexiveAuxNormOn (rnPolyfold n).boundary N ∧
        EpStrongBundle.HasReflexiveLocalExtensions (EpGroupoid.trivial (rnPolyfold n))
          (bundle n k) N :=
  ⟨hasReflexiveFibers_bundle, (EpGroupoid.admitsBumpFunctionsPointwise_trivial_rn n).2,
    (epBundle n k).theorem_12_2_11_exists (EpGroupoid.admitsBumpFunctionsPointwise_trivial_rn n).2
      hasReflexiveFibers_bundle,
    (epBundle n k).theorem_12_2_13_hyp_witness
      (EpGroupoid.admitsBumpFunctionsPointwise_trivial_rn n).2 hasReflexiveFibers_bundle⟩

end TrivialBundle

end Polyfold
