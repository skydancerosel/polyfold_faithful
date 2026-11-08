import Polyfold.Chapter6.LocalDetBundle
import Polyfold.Chapter6.Propagation
import Polyfold.Chapter3.SolutionLinearization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 6, "Orientations":
the statements that the 2021 edition changes, **Lemma 6.4.4** (p. 247; 2017: Lemma 6.3),
**Proposition 6.4.13** (p. 253; 2017: Proposition 6.6), **Proposition 6.4.15** (p. 257; 2017:
Proposition 6.7; preprint: Proposition 6.15), **Proposition 6.6.3** (p. 263; 2017:
Proposition 6.12; preprint: Proposition 6.28), **Lemma 6.6.5** (p. 265; 2017: Lemma 6.13;
preprint: Lemma 6.30) and **Lemma 6.6.8** (p. 267; 2017: Lemma 6.15, first half; preprint:
Lemma 6.33), and the items new in 2021, **Lemma 6.6.9** (p. 269; 2017: second half of
Lemma 6.15) and **Theorem 6.6.17** (p. 275; 2017: running text after Definition 6.13).

# Chapter 6 in the 2021 edition

## The text, paraphrased

(Lemma 6.4.4, p. 247) For `T₀ : E → F` Fredholm and `P₀ ∈ Π_{T₀}` there is `ε > 0` such that
every `T` and every projection `P` with `‖T − T₀‖ < ε`, `‖P − P₀‖ < ε` have: `T` Fredholm,
`P ∈ Π_T`, and (new in 2021) `ind(P ∘ T) = ind(T) = ind(T₀) = ind(P₀ ∘ T₀)`.

(Proposition 6.4.13, p. 253) For `T` Fredholm and a closed `H ⊆ F` of finite codimension with
`Π_T ∩ 𝒫_H ≠ ∅` (now an explicit hypothesis), and `P, Q ∈ Π_T ∩ 𝒫_H`, there are isomorphisms
`A_T : ker(P T) → ker(Q T)`, `B_T : F/H → F/H` making the diagram of the exact sequences
`E(T, P)`, `E(T, Q)` commute; they depend continuously on `T`.

(Lemma 6.6.8, p. 267) Adding parameters `μ ∈ ℝˡ` that enter `F(t, y, λ)` as dummy variables does
not change the propagation of orientation; (Lemma 6.6.9, p. 269, new) adding sc⁺-sections
`Σ μⱼ s̄ⱼ(y, t)` to a section `F` with property (P) does not change it either.

## What is formalized

* `lemma_6_4_4_2021`: Lemma 6.4.4 with all four index equalities.  The proof is not the text's
  map `Φ_{(P,T)}`: the intertwiner `J(P) = P P₀ + (1 − P)(1 − P₀)` (`projIntertwiner`) is a unit
  near `P₀` with `J P₀ = P J` (`projIntertwiner_mul`), so `P = J P₀ J⁻¹`; then `R(P) = J R(P₀)`
  has finite codimension, and `lemma_6_17` applied to `J⁻¹ T` near `T₀` gives
  `R(P T) = J R(P₀ J⁻¹ T) = J R(P₀) = R(P)`.  The indices: `fredholmIndex_add_of_norm_lt` and
  `IsGoodLeftProj.fredholmIndex_comp`.
* `proposition_6_4_13_2021`: the isomorphisms `A_T`, `B_T` and the commuting diagram of
  Proposition 6.4.13, by the text's construction, with a common algebraic complement `X` of
  `ker(P T)` and `ker(Q T)` (`exists_isCompl_isCompl_of_finrank_eq`: two finite-dimensional
  subspaces of the same dimension have one; `dim ker(P T) = dim ker(Q T)` from the indices).
* `lemma_6_6_8_2021` and `lemma_6_6_9_2021`: Lemmas 6.6.8 and 6.6.9 as instances of the existing
  `IsStabKernels.push_append` (appending zero sections, resp. arbitrary sections `s̄ⱼ`).

## Items already covered, and items not formalized

* Proposition 6.4.15 (hypotheses `T` Fredholm and `T ⊕ φ` onto made explicit; `c̄ᵢ ∈ ℝⁿ`) is the
  existing `proposition_6_15` (`Stabilization.lean`), which already has these hypotheses.
* Proposition 6.6.3 (tame `X`; the sc⁺-sections `s`, `q` valued in `Y × [0, 1]`) is covered by
  the existing `proposition_6_28` (`OrientableNbhd.lean`), which does not assume tameness and
  reads the sections over `[0, 1] × X` as pull-back sections; (1) (contractibility) remains gap
  G.61.
* Lemma 6.6.5 (the solution set near `(t, φ(t), 0)` for points `(t, y, λ)`; 2017: `(t, y, 0)`,
  possible misprint): the manifold statement is gap G.62; the family of kernels used later is
  `exists_subspaceFamily_linKer` (`KernelFamily.lean`), which is not affected by the change.
* Proposition 6.4.13: the last sentence (`A_T`, `B_T` depend continuously on `T` near `T`) is not
  formalized; it needs a closed common complement `X` (here `X` is algebraic) and the topology of
  the kernel bundle of Remark 6.4.5.
* Theorem 6.6.17 (the Hausdorff topology on `O_f`; the text leaves the proof to the reader) is in
  `Chapter6/OrientationSpace.lean` (`theorem_6_6_17_2021`, `existsUnique_orientationTopology_2021`),
  built from the glued local propagations `orPush`/`orLocalTransport`.
* Proposition 6.2.2 (2017: Proposition 6.1; preprint: Proposition 6.2) is unchanged in 2021 and is
  the existing `proposition_6_2` (`Chapter3/IndexAlongPathsDevice.lean`).

## What the text leaves implicit, and the choices made

* `ind(P ∘ T)` is the index of `P ∘ T : E → F` (as in `IsGoodLeftProj.fredholmIndex_comp`); as a
  map onto `R(P)` its index would be `dim ker(P T)`.
* `E`, `F` are taken in `Type` (the universe of `isFredholm_add_of_norm_lt`).
* "Dummy variables" in Lemma 6.6.8 are the sections `s̄ⱼ = 0`; the stabilized kernels of the
  appended data are a hypothesis (`IsStabKernels`), as in `push_append`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

section Lemma644

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The intertwiner `J(P) = P P₀ + (1 − P)(1 − P₀)` of two projections. -/
def projIntertwiner (P₀ P : F →L[ℝ] F) : F →L[ℝ] F := P * P₀ + (1 - P) * (1 - P₀)

omit [CompleteSpace F] in
/-- `J(P₀) = 1` for a projection `P₀`. -/
theorem projIntertwiner_self {P₀ : F →L[ℝ] F} (h₀ : P₀ * P₀ = P₀) : projIntertwiner P₀ P₀ = 1 := by
  unfold projIntertwiner
  have : (1 - P₀) * (1 - P₀) = 1 - P₀ := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, h₀]; abel
  rw [h₀, this]; abel

omit [CompleteSpace F] in
/-- `J(P) P₀ = P J(P)` for projections `P₀`, `P`. -/
theorem projIntertwiner_mul {P₀ P : F →L[ℝ] F} (h₀ : P₀ * P₀ = P₀) (h : P * P = P) :
    projIntertwiner P₀ P * P₀ = P * projIntertwiner P₀ P := by
  unfold projIntertwiner
  have l : (P * P₀ + (1 - P) * (1 - P₀)) * P₀ = P * (P₀ * P₀) + (1 - P) * (P₀ - P₀ * P₀) := by
    noncomm_ring
  have r : P * (P * P₀ + (1 - P) * (1 - P₀)) = (P * P) * P₀ + (P - P * P) * (1 - P₀) := by
    noncomm_ring
  rw [l, r, h₀, h, sub_self, sub_self, mul_zero, zero_mul]

omit [CompleteSpace F] in
/-- `P ↦ J(P)` is continuous. -/
theorem continuous_projIntertwiner (P₀ : F →L[ℝ] F) : Continuous (projIntertwiner P₀) := by
  unfold projIntertwiner
  fun_prop

/-- **2021 Lemma 6.4.4, p. 247** (2017: Lemma 6.3; no preprint counterpart): for `T₀` Fredholm
and `P₀ ∈ Π_{T₀}` there is `ε > 0` such that for every `T` and every projection `P` with
`‖T − T₀‖ < ε` and `‖P − P₀‖ < ε`: `T` is Fredholm, `P ∈ Π_T`, and
`ind(P ∘ T) = ind(T) = ind(T₀) = ind(P₀ ∘ T₀)` (the index equalities are new in 2021). -/
theorem lemma_6_4_4_2021 {T₀ : E →L[ℝ] F} (hT₀ : T₀.IsFredholm) {P₀ : F →L[ℝ] F}
    (hP₀ : IsGoodLeftProj T₀ P₀) :
    ∃ ε > 0, ∀ (T : E →L[ℝ] F) (P : F →L[ℝ] F), P ∘L P = P → ‖T - T₀‖ < ε → ‖P - P₀‖ < ε →
      T.IsFredholm ∧ IsGoodLeftProj T P ∧ fredholmIndex (P ∘L T) = fredholmIndex T ∧
        fredholmIndex T = fredholmIndex T₀ ∧ fredholmIndex T₀ = fredholmIndex (P₀ ∘L T₀) := by
  have h₀ : P₀ * P₀ = P₀ := hP₀.isProj
  -- (a) Fredholm with the same index near `T₀`
  obtain ⟨v, hv⟩ := ContinuousLinearMap.isFredholm_iff_exists_isQuasiInverse.1 hT₀
  have hA : ∀ᶠ q : (F →L[ℝ] F) × (E →L[ℝ] F) in 𝓝 (P₀, T₀),
      q.2.IsFredholm ∧ fredholmIndex q.2 = fredholmIndex T₀ := by
    have hball : ∀ᶠ q : (F →L[ℝ] F) × (E →L[ℝ] F) in 𝓝 (P₀, T₀),
        q.2 ∈ Metric.ball T₀ (1 / (‖v‖ + 1)) :=
      continuous_snd.continuousAt.eventually (Metric.ball_mem_nhds _ (by positivity))
    filter_upwards [hball] with q hq
    rw [Metric.mem_ball, dist_eq_norm] at hq
    have hs : ‖v‖ * ‖q.2 - T₀‖ < 1 := by
      calc ‖v‖ * ‖q.2 - T₀‖ ≤ (‖v‖ + 1) * ‖q.2 - T₀‖ := by gcongr; linarith
        _ < (‖v‖ + 1) * (1 / (‖v‖ + 1)) := by gcongr
        _ = 1 := by field_simp
    have e : T₀ + (q.2 - T₀) = q.2 := add_sub_cancel T₀ q.2
    refine ⟨e ▸ isFredholm_add_of_norm_lt hv hs, ?_⟩
    rw [← e]
    exact (fredholmIndex_add_of_norm_lt hv hs).2
  -- (b) `J(P)` is a unit near `P₀`
  have hJc : ContinuousAt (fun q : (F →L[ℝ] F) × (E →L[ℝ] F) => projIntertwiner P₀ q.1) (P₀, T₀) :=
    ((continuous_projIntertwiner P₀).comp continuous_fst).continuousAt
  have hJ1 : projIntertwiner P₀ P₀ = ((1 : (F →L[ℝ] F)ˣ) : F →L[ℝ] F) := by
    rw [projIntertwiner_self h₀, Units.val_one]
  have hB : ∀ᶠ q : (F →L[ℝ] F) × (E →L[ℝ] F) in 𝓝 (P₀, T₀), IsUnit (projIntertwiner P₀ q.1) := by
    refine hJc.eventually (Units.isOpen.mem_nhds ?_)
    change IsUnit (projIntertwiner P₀ P₀)
    rw [hJ1]; exact Units.isUnit 1
  -- (c) `J(P)⁻¹ T` is close to `T₀`
  obtain ⟨Y, hY⟩ := (hP₀.isFredholm_comp hT₀).closedComplemented_ker.exists_isTopCompl
  obtain ⟨ε₂, hε₂, h617⟩ := lemma_6_17 hP₀ hY
  have hinv0 : ContinuousAt (fun q : (F →L[ℝ] F) × (E →L[ℝ] F) =>
      Ring.inverse (projIntertwiner P₀ q.1)) (P₀, T₀) := by
    refine ContinuousAt.comp (g := Ring.inverse) ?_ hJc
    change ContinuousAt Ring.inverse (projIntertwiner P₀ P₀)
    rw [hJ1]
    exact NormedRing.inverse_continuousAt 1
  have hinvc := hinv0.clm_comp (continuous_snd.continuousAt (x := (P₀, T₀)))
  have hC : ∀ᶠ q : (F →L[ℝ] F) × (E →L[ℝ] F) in 𝓝 (P₀, T₀),
      Ring.inverse (projIntertwiner P₀ q.1) ∘L q.2 ∈ Metric.ball T₀ ε₂ := by
    have hval : Ring.inverse (projIntertwiner P₀ P₀) ∘L T₀ = T₀ := by
      rw [hJ1, Ring.inverse_unit, inv_one, Units.val_one]
      ext x; rfl
    have := hinvc.eventually (Metric.ball_mem_nhds (Ring.inverse (projIntertwiner P₀ P₀) ∘L T₀) hε₂)
    rwa [hval] at this
  obtain ⟨ε, hε, hεq⟩ := Metric.eventually_nhds_iff.1 (hA.and (hB.and hC))
  refine ⟨ε, hε, fun T P hP hT hPd => ?_⟩
  have hdist : dist (P, T) (P₀, T₀) < ε := by
    rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]; exact ⟨hPd, hT⟩
  obtain ⟨⟨hTF, hTi⟩, hJu, hS⟩ := hεq hdist
  simp only at hTF hTi hJu hS
  rw [Metric.mem_ball, dist_eq_norm] at hS
  obtain ⟨hPS, -⟩ := h617 _ hS
  -- conjugation `P = J P₀ J⁻¹`
  set J := projIntertwiner P₀ P with hJdef
  set Ji := Ring.inverse J with hJidef
  have hP' : P * P = P := hP
  have hJJi : J * Ji = 1 := Ring.mul_inverse_cancel J hJu
  have hJiJ : Ji * J = 1 := Ring.inverse_mul_cancel J hJu
  have hconj : P = J * P₀ * Ji := by
    rw [projIntertwiner_mul h₀ hP', mul_assoc, hJJi, mul_one]
  have hJi_surj : LinearMap.range (Ji : F →ₗ[ℝ] F) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun y => ⟨J y, ?_⟩
    change (Ji * J) y = y
    rw [hJiJ]; rfl
  have hrangeP : LinearMap.range (P : F →ₗ[ℝ] F) =
      (LinearMap.range (P₀ : F →ₗ[ℝ] F)).map (J : F →ₗ[ℝ] F) := by
    have : (P : F →ₗ[ℝ] F) = (J : F →ₗ[ℝ] F) ∘ₗ ((P₀ : F →ₗ[ℝ] F) ∘ₗ (Ji : F →ₗ[ℝ] F)) := by
      conv_lhs => rw [hconj]
      rfl
    rw [this, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ hJi_surj]
  have hrangePT : LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) =
      (LinearMap.range (P₀ : F →ₗ[ℝ] F)).map (J : F →ₗ[ℝ] F) := by
    have : ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) =
        (J : F →ₗ[ℝ] F) ∘ₗ ((P₀ ∘L (Ji ∘L T) : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
      conv_lhs => rw [hconj]
      rfl
    rw [this, LinearMap.range_comp, hPS.range_comp]
  have hGood : IsGoodLeftProj T P := by
    refine ⟨hP, ?_, hrangePT.trans hrangeP.symm⟩
    let e : F ≃ₗ[ℝ] F :=
      { toFun := J, invFun := Ji,
        map_add' := J.map_add, map_smul' := J.map_smul,
        left_inv := fun y => by change (Ji * J) y = y; rw [hJiJ]; rfl,
        right_inv := fun y => by change (J * Ji) y = y; rw [hJJi]; rfl }
    have := hP₀.finite_coker
    rw [hrangeP]
    exact (Submodule.Quotient.equiv _ _ e rfl).finiteDimensional
  exact ⟨hTF, hGood, hGood.fredholmIndex_comp hTF, hTi, (hP₀.fredholmIndex_comp hT₀).symm⟩

end Lemma644

section CommonCompl

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Adding a vector `v ∉ K` raises the dimension by one. -/
theorem finrank_sup_span_singleton_of_notMem {K : Submodule ℝ V} [FiniteDimensional ℝ K] {v : V}
    (hv : v ∉ K) : finrank ℝ ↥(K ⊔ ℝ ∙ v) = finrank ℝ K + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ K.zero_mem)
  have hinf : K ⊓ ℝ ∙ v = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxv⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxv
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd ((K.smul_mem_iff hc).1 hxK) hv
  have h := Submodule.finrank_sup_add_finrank_inf_eq K (ℝ ∙ v)
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hv0] at h
  exact h

/-- If `X` complements `K ⊔ ℝ v` and `v ∉ K`, then `X ⊔ ℝ v` complements `K`. -/
theorem isCompl_sup_span_singleton {K X : Submodule ℝ V} {v : V} (hv : v ∉ K)
    (hX : IsCompl X (K ⊔ ℝ ∙ v)) : IsCompl (X ⊔ ℝ ∙ v) K := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxK
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have hyK : y ∈ K ⊔ ℝ ∙ v := by
      have : y = (y + c • v) - c • v := by abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hxK)
        (Submodule.mem_sup_right (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)))
    have hy0 : y = 0 := (Submodule.disjoint_def.1 hX.1) y hy hyK
    subst hy0
    rw [zero_add] at hxK ⊢
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd ((K.smul_mem_iff hc).1 hxK) hv
  · rw [codisjoint_iff, sup_assoc, sup_comm (ℝ ∙ v) K]
    exact codisjoint_iff.1 hX.2

/-- The induction behind `exists_isCompl_isCompl_of_finrank_eq`, on `dim(K₁ + K₂) − dim K₁`. -/
theorem exists_isCompl_isCompl_of_finrank_eq_aux (n : ℕ) :
    ∀ (K₁ K₂ : Submodule ℝ V) [FiniteDimensional ℝ K₁] [FiniteDimensional ℝ K₂],
      finrank ℝ K₁ = finrank ℝ K₂ → finrank ℝ ↥(K₁ ⊔ K₂) = finrank ℝ K₁ + n →
        ∃ X : Submodule ℝ V, IsCompl X K₁ ∧ IsCompl X K₂ := by
  induction n with
  | zero =>
    intro K₁ K₂ _ _ heq hn
    have h1 : K₁ ⊔ K₂ = K₁ :=
      (Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)).symm
    have h2 : K₂ = K₁ :=
      Submodule.eq_of_le_of_finrank_eq (h1 ▸ le_sup_right) heq.symm
    obtain ⟨X, hX⟩ := Submodule.exists_isCompl K₁
    exact ⟨X, hX.symm, h2 ▸ hX.symm⟩
  | succ n ih =>
    intro K₁ K₂ _ _ heq hn
    have hn12 : ¬ K₂ ≤ K₁ := by
      intro h
      rw [sup_eq_left.2 h] at hn
      omega
    have hn21 : ¬ K₁ ≤ K₂ := fun h =>
      hn12 (Submodule.eq_of_le_of_finrank_eq h heq ▸ le_refl _)
    obtain ⟨a, haK₂, haK₁⟩ := SetLike.not_le_iff_exists.1 hn12
    obtain ⟨b, hbK₁, hbK₂⟩ := SetLike.not_le_iff_exists.1 hn21
    have hv₁ : a + b ∉ K₁ := fun h => haK₁ (by simpa using K₁.sub_mem h hbK₁)
    have hv₂ : a + b ∉ K₂ := fun h => hbK₂ (by simpa using K₂.sub_mem h haK₂)
    have hvs : a + b ∈ K₁ ⊔ K₂ :=
      Submodule.add_mem _ (Submodule.mem_sup_right haK₂) (Submodule.mem_sup_left hbK₁)
    have hsup : (K₁ ⊔ ℝ ∙ (a + b)) ⊔ (K₂ ⊔ ℝ ∙ (a + b)) = K₁ ⊔ K₂ := by
      have hspan : ℝ ∙ (a + b) ≤ K₁ ⊔ K₂ := (Submodule.span_singleton_le_iff_mem _ _).2 hvs
      apply le_antisymm
      · exact sup_le (sup_le le_sup_left hspan) (sup_le le_sup_right hspan)
      · exact sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right)
    have hf₁ := finrank_sup_span_singleton_of_notMem hv₁
    have hf₂ := finrank_sup_span_singleton_of_notMem hv₂
    obtain ⟨X, hX₁, hX₂⟩ := ih (K₁ ⊔ ℝ ∙ (a + b)) (K₂ ⊔ ℝ ∙ (a + b)) (by rw [hf₁, hf₂, heq])
      (by rw [hsup, hf₁, hn]; ring)
    exact ⟨X ⊔ ℝ ∙ (a + b), isCompl_sup_span_singleton hv₁ hX₁,
      isCompl_sup_span_singleton hv₂ hX₂⟩

/-- Two finite-dimensional subspaces of the same dimension have a common algebraic complement
(the text's `X` in the proof of Proposition 6.4.13, there taken closed). -/
theorem exists_isCompl_isCompl_of_finrank_eq (K₁ K₂ : Submodule ℝ V) [FiniteDimensional ℝ K₁]
    [FiniteDimensional ℝ K₂] (heq : finrank ℝ K₁ = finrank ℝ K₂) :
    ∃ X : Submodule ℝ V, IsCompl X K₁ ∧ IsCompl X K₂ :=
  exists_isCompl_isCompl_of_finrank_eq_aux (finrank ℝ ↥(K₁ ⊔ K₂) - finrank ℝ K₁) K₁ K₂ heq
    (by have := Submodule.finrank_mono (le_sup_left : K₁ ≤ K₁ ⊔ K₂); omega)

end CommonCompl

section Prop6413

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **2021 Proposition 6.4.13, p. 253** (2017: Proposition 6.6; no preprint counterpart), the
algebraic part: for `T` Fredholm and `P, Q ∈ Π_T ∩ 𝒫_H` (good left-projections with range the
given `H`), there are linear isomorphisms `A_T : ker(P T) → ker(Q T)` and `B_T : F/H → F/H`
(here `F/R(P) → F/R(Q)`) making the diagram of the exact sequences `E(T, P)`, `E(T, Q)`
(`projSeqJ`, `projSeqPhi`, `projSeqPi`) commute: `A_T ∘ j_P = j_Q`, `Φ_Q ∘ A_T = B_T ∘ Φ_P`,
`π_Q ∘ B_T = π_P`.  The construction is the text's: `A_T(e) = e − x(e)` with `x(e) ∈ X` solving
`Q T x = Q T e`, and `B_T(f + H) = f̃ + H` with `T x + f̃ = (1 − P) f`, `f̃ ∈ (1 − Q) F`. -/
theorem proposition_6_4_13_2021 {T : E →L[ℝ] F} (hT : T.IsFredholm) {H : Submodule ℝ F}
    {P Q : F →L[ℝ] F} (hP : IsGoodLeftProj T P) (hQ : IsGoodLeftProj T Q)
    (hPH : LinearMap.range (P : F →ₗ[ℝ] F) = H) (hQH : LinearMap.range (Q : F →ₗ[ℝ] F) = H) :
    ∃ (A : LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) ≃ₗ[ℝ]
        LinearMap.ker ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F))
      (B : (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)) ≃ₗ[ℝ] (F ⧸ LinearMap.range (Q : F →ₗ[ℝ] F))),
      (A : _ →ₗ[ℝ] _) ∘ₗ projSeqJ T P = projSeqJ T Q ∧
      projSeqPhi T Q ∘ₗ (A : _ →ₗ[ℝ] _) = (B : _ →ₗ[ℝ] _) ∘ₗ projSeqPhi T P ∧
      projSeqPi (T := T) hQ.isProj ∘ₗ (B : _ →ₗ[ℝ] _) = projSeqPi (T := T) hP.isProj := by
  set K₁ := LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) with hK₁
  set K₂ := LinearMap.ker ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) with hK₂
  have : FiniteDimensional ℝ K₁ := (hP.isFredholm_comp hT).finite_ker
  have : FiniteDimensional ℝ K₂ := (hQ.isFredholm_comp hT).finite_ker
  have := hP.finite_coker
  have := hQ.finite_coker
  have hPP : ∀ y, P (P y) = P y := fun y => by
    simpa using congrArg (fun A : F →L[ℝ] F => A y) hP.isProj
  have hQQ : ∀ y, Q (Q y) = Q y := fun y => by
    simpa using congrArg (fun A : F →L[ℝ] F => A y) hQ.isProj
  have hrangeQ : LinearMap.range (P : F →ₗ[ℝ] F) = LinearMap.range (Q : F →ₗ[ℝ] F) :=
    hPH.trans hQH.symm
  have hcoker : finrank ℝ (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)) =
      finrank ℝ (F ⧸ LinearMap.range (Q : F →ₗ[ℝ] F)) :=
    (Submodule.quotEquivOfEq _ _ hrangeQ).finrank_eq
  have hrank : finrank ℝ K₁ = finrank ℝ K₂ := by
    have h := (hP.fredholmIndex_comp hT).trans (hQ.fredholmIndex_comp hT).symm
    have hc : finrank ℝ (F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) =
        finrank ℝ (F ⧸ LinearMap.range ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
      (Submodule.quotEquivOfEq _ _ (by rw [hP.range_comp, hQ.range_comp, hrangeQ])).finrank_eq
    unfold fredholmIndex linIndex at h
    rw [hc] at h
    exact_mod_cast sub_left_inj.1 h
  obtain ⟨X, hX₁, hX₂⟩ := exists_isCompl_isCompl_of_finrank_eq K₁ K₂ hrank
  have hK₂mem : ∀ e : E, e ∈ K₂ ↔ Q (T e) = 0 := fun e => Iff.rfl
  have hK₁mem : ∀ e : E, e ∈ K₁ ↔ P (T e) = 0 := fun e => Iff.rfl
  -- `Q T x = Q T e` for the `X`-component `x` of `e`
  have hQTproj : ∀ e : E, Q (T (X.projection K₂ hX₂ e)) = Q (T e) := by
    intro e
    have hsum := Submodule.projection_add_projection_eq_self hX₂ e
    have hk := (hK₂mem _).1 (Submodule.projection_apply_mem hX₂.symm e)
    conv_rhs => rw [← hsum]
    rw [map_add, map_add, hk, add_zero]
  -- `Ψ = Q T|_X : X → R(Q)` is an isomorphism
  let Ψ : X →ₗ[ℝ] LinearMap.range (Q : F →ₗ[ℝ] F) :=
    LinearMap.codRestrict _ (((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) ∘ₗ X.subtype)
      (fun x => ⟨T x, rfl⟩)
  have hΨi : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hx⟩ hΨx
    have h0 : Q (T x) = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hΨx)
    have : x ∈ X ⊓ K₂ := ⟨hx, (hK₂mem x).2 h0⟩
    rw [hX₂.1.eq_bot] at this
    exact (Submodule.mem_bot ℝ).2 (Subtype.ext ((Submodule.mem_bot ℝ).1 this))
  have hΨs : Function.Surjective Ψ := by
    rintro ⟨y, hy⟩
    rw [← hQ.range_comp] at hy
    obtain ⟨e, rfl⟩ := hy
    refine ⟨⟨X.projection K₂ hX₂ e, Submodule.projection_apply_mem hX₂ e⟩, Subtype.ext ?_⟩
    exact hQTproj e
  let ΨE := LinearEquiv.ofBijective Ψ ⟨hΨi, hΨs⟩
  let Qr : F →ₗ[ℝ] LinearMap.range (Q : F →ₗ[ℝ] F) :=
    LinearMap.codRestrict _ (Q : F →ₗ[ℝ] F) (fun g => ⟨g, rfl⟩)
  let ξ : F →ₗ[ℝ] X := ΨE.symm.toLinearMap ∘ₗ Qr
  have hξ : ∀ g, Q (T (ξ g : E)) = Q g := fun g =>
    congrArg Subtype.val (ΨE.apply_symm_apply (Qr g))
  have hξu : ∀ g, ∀ x ∈ X, Q (T x) = Q g → (ξ g : E) = x := by
    intro g x hx hxg
    have : ΨE ⟨x, hx⟩ = Qr g := Subtype.ext hxg
    change ((ΨE.symm (Qr g) : X) : E) = x
    rw [← this, LinearEquiv.symm_apply_apply]
  -- `A(e) = e − x(e)`, the `K₂`-component of `e`
  let A₀ : K₁ →ₗ[ℝ] K₂ := LinearMap.codRestrict K₂ ((K₂.projection X hX₂.symm) ∘ₗ K₁.subtype)
    (fun e => Submodule.projection_apply_mem hX₂.symm _)
  have hA₀i : Function.Injective A₀ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨e, he⟩ hAe
    have h0 : K₂.projection X hX₂.symm e = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hAe)
    rw [Submodule.projection_apply_eq_zero_iff] at h0
    have : e ∈ X ⊓ K₁ := ⟨h0, he⟩
    rw [hX₁.1.eq_bot] at this
    exact (Submodule.mem_bot ℝ).2 (Subtype.ext ((Submodule.mem_bot ℝ).1 this))
  let A := LinearEquiv.ofBijective A₀
    ⟨hA₀i, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hA₀i⟩
  -- `B(f + H) = f̃ + H` with `f̃ = (1 − P) f − T x`, `x ∈ X`, `Q T x = Q (1 − P) f`
  let D : F →ₗ[ℝ] F := LinearMap.id - (P : F →ₗ[ℝ] F)
  let G : F →ₗ[ℝ] F ⧸ LinearMap.range (Q : F →ₗ[ℝ] F) :=
    (LinearMap.range (Q : F →ₗ[ℝ] F)).mkQ ∘ₗ
      (D - (T : E →ₗ[ℝ] F) ∘ₗ X.subtype ∘ₗ ξ ∘ₗ D)
  have hDP : ∀ f, D (P f) = 0 := fun f => by simp [D, hPP]
  let B₀ := (LinearMap.range (P : F →ₗ[ℝ] F)).liftQ G (by
    rintro _ ⟨f, rfl⟩
    simp [G, hDP])
  have hB₀ : ∀ f, B₀ (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (D f - T (ξ (D f) : E)) := fun f => rfl
  have hB₀i : Function.Injective B₀ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro α hα
    induction α using Submodule.Quotient.induction_on with
    | H f =>
    rw [LinearMap.mem_ker, hB₀, Submodule.Quotient.mk_eq_zero] at hα
    obtain ⟨g', hg'⟩ := hα
    have hQg : Q (D f - T (ξ (D f) : E)) = 0 := by
      rw [map_sub, hξ, sub_self]
    have hg0 : D f - T (ξ (D f) : E) = 0 := by
      have hg'' : Q g' = D f - T (ξ (D f) : E) := hg'
      rw [← hg''] at hQg ⊢
      rwa [hQQ] at hQg
    have hPx : P (T (ξ (D f) : E)) = 0 := by
      have : T (ξ (D f) : E) = D f := (sub_eq_zero.1 hg0).symm
      rw [this]
      simp [D, hPP]
    have hx0 : (ξ (D f) : E) = 0 := by
      have : (ξ (D f) : E) ∈ X ⊓ K₁ := ⟨(ξ (D f)).2, (hK₁mem _).2 hPx⟩
      rw [hX₁.1.eq_bot] at this
      exact (Submodule.mem_bot ℝ).1 this
    rw [hx0, map_zero, sub_zero] at hg0
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    refine ⟨f, ?_⟩
    have : f - P f = 0 := hg0
    exact (sub_eq_zero.1 this).symm
  let B := LinearEquiv.ofBijective B₀
    ⟨hB₀i, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hcoker).1 hB₀i⟩
  refine ⟨A, B, ?_, ?_, ?_⟩
  · refine LinearMap.ext fun e => Subtype.ext ?_
    have he : (e : E) ∈ K₂ := (hK₂mem _).2 (by
      have : T e = 0 := e.2
      simp [this])
    exact Submodule.projection_apply_of_mem_left hX₂.symm he
  · refine LinearMap.ext fun e => ?_
    have hPe : P (T e) = 0 := e.2
    have hDe : D (T e) = T e := by simp [D, hPe]
    have hx : (ξ (T e) : E) = X.projection K₂ hX₂ e :=
      hξu _ _ (Submodule.projection_apply_mem hX₂ e) (hQTproj e)
    change Submodule.Quotient.mk (T (K₂.projection X hX₂.symm e)) =
      B₀ (Submodule.Quotient.mk (T e))
    rw [hB₀, hDe, hx]
    congr 1
    have hsum := Submodule.projection_add_projection_eq_self hX₂ (e : E)
    rw [eq_sub_iff_add_eq, ← map_add, add_comm, hsum]
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
    change projSeqPi (T := T) hQ.isProj (B₀ (Submodule.Quotient.mk f)) =
      projSeqPi (T := T) hP.isProj (Submodule.Quotient.mk f)
    rw [hB₀, projSeqPi_mk, projSeqPi_mk, Submodule.Quotient.eq]
    refine ⟨-(ξ (D f) : E), ?_⟩
    rw [map_sub, hξ]
    simp only [map_neg, D, LinearMap.sub_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe]
    abel

end Prop6413

section Lemma668

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {Q : Type*} [TopologicalSpace Q] [SimplyConnectedSpace Q]
  [LocallyPathConnectedSpace Q] [Nonempty Q]
  {c : StrongBundleChart PX P} {hc : B.IsChart c} {y : Q → X} {hy : ∀ q, y q ∈ c.φ.source}
  {S : Q → X → Y} {k : ℕ} {s : Fin k → Q → X → Y}
  {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}

/-- **2021 Lemma 6.6.8, p. 267** (2017: Lemma 6.15, first half; preprint: Lemma 6.33): adding
parameters `μ ∈ ℝᵈ` that enter as dummy variables, i.e. appending the zero sections
`s̄ⱼ = 0`, does not change the push-forward of orientations along the stabilized kernels. -/
theorem lemma_6_6_8_2021 (hΛ : IsStabKernels f c hc y hy S s Λ) {d : ℕ}
    {Λ' : SubspaceFamily Q (c.φ.model.E 0 × (Fin (k + d) → ℝ))}
    (hΛ' : IsStabKernels f c hc y hy S (Fin.append s fun (_ : Fin d) (_ : Q) => fiberZero P) Λ')
    (hf : B.IsScFredholmSection f) (a b : Q) {x₀ x₁ : X} (ha : y a = x₀) (hb : y b = x₁)
    (hx₀ : x₀ ∈ PX.smoothSet) (hx₁ : x₁ ∈ PX.smoothSet)
    (z₀ : c.φ.model.E 1) (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x₀)
    (z₁ : c.φ.model.E 1) (hz₁ : c.φ.model.E.toBase 1 z₁ = c.φ x₁) :
    hΛ'.push hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁ = hΛ.push hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁ :=
  hΛ.push_append hΛ' hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁

/-- **2021 Lemma 6.6.9, p. 269** (new in the 2021 edition; 2017: Lemma 6.15, second half;
preprint: Lemma 6.33): adding sc⁺-sections `Σ μⱼ s̄ⱼ(y, t)` to a section with property (P) does
not change the push-forward of orientations (the existing `IsStabKernels.push_append`). -/
theorem lemma_6_6_9_2021 (hΛ : IsStabKernels f c hc y hy S s Λ) {d : ℕ}
    {sbar : Fin d → Q → X → Y} {Λ' : SubspaceFamily Q (c.φ.model.E 0 × (Fin (k + d) → ℝ))}
    (hΛ' : IsStabKernels f c hc y hy S (Fin.append s sbar) Λ') (hf : B.IsScFredholmSection f)
    (a b : Q) {x₀ x₁ : X} (ha : y a = x₀) (hb : y b = x₁) (hx₀ : x₀ ∈ PX.smoothSet)
    (hx₁ : x₁ ∈ PX.smoothSet) (z₀ : c.φ.model.E 1) (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x₀)
    (z₁ : c.φ.model.E 1) (hz₁ : c.φ.model.E.toBase 1 z₁ = c.φ x₁) :
    hΛ'.push hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁ = hΛ.push hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁ :=
  hΛ.push_append hΛ' hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁

end Lemma668

end Polyfold
