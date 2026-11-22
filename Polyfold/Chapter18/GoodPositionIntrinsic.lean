import Polyfold.Chapter3.GoodPositionGerm
import Polyfold.Chapter18.TangentPartialCone
import Polyfold.Chapter18.ImplicitFunctionTheorem
import Polyfold.Chapter3.GlobalIFTIndexG
import Polyfold.Chapter3.TameGermsAddG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV:
Theorem 18.1.5 (p. 846) with Remark 17.2.18 (p. 784); Part I: Definition 3.1.24 (good position)
and Definition 3.6.6 (p. 136).

# `ker f'(α)` in good position to the partial cone `C_αC`

The hypothesis of Theorem 18.1.5 is that `f'(α) : T_αC → E_α` is onto and that `ker f'(α)` is in
good position to the partial cone `C_αC ⊆ T_αC` (Remark 17.2.18).  `T_αC` carries a topology and a
linear structure, but no preferred norm, so good position is stated here without norms.

* `IsInGoodPositionTop C N` (Definition 3.1.24 on a topological vector space): `N ∩ C` has
  interior in `N`, and `N` has an algebraic complement `P` with a neighbourhood `U` of `0` and a
  bounded set `B` such that `n ∈ C ↔ n + p ∈ C` whenever `p ∈ sU`, `n ∉ sB` (`s > 0`).  We read
  the text's `‖p‖ ≤ ε‖n‖` in this scale-invariant form; on a normed space the two agree
  (`isInGoodPositionTop_iff_norm`), and the notion is transported by continuous linear
  isomorphisms (`isInGoodPositionTop_preimage_iff`).  As in Part I's `IsInGoodPosition`, the
  complement `P` is algebraic and `N` is not required to be finite-dimensional.
* `PolyfoldConstruction.IsInGoodPositionToPartialCone α N`: `N ⊆ T_αC` is in good position to
  `C_αC`.  For every `Ψ ∈ F(α)` it is good position of `S_Ψ(N)` to `C_qO`
  (`isInGoodPositionToPartialCone_iff`), and in a chart Part I's `IsInGoodPositionIn`
  (`MPolyfold.isInGoodPositionTop_tangentPartialCone_iff`).
* `StrongBundle.isGoodPositionGermTame_iff_tangent`: Definition 3.6.6 as printed — for a tame
  sc-Fredholm section, Part I's good position at a zero `x` (in a tame chart) holds iff `f'(x)` is
  onto and `ker f'(x)` is in good position to `C_xX`.
* `StrongPolyfoldBundleConstruction.IsKernelInGoodPosition`: `ker f'(α)` is in good position to
  `C_αC`; `isGoodPositionGermTame_localRep_iff`: with surjectivity of `f'(α)` it is the
  hypothesis of `theorem_18_1_5_model` read through any `Ψ̄ ∈ F̄(α)`.
* **`theorem_18_1_5`**: Theorem 18.1.5 with the text's hypothesis on `f'(α)`, and tame germ data
  (`hft`, the standing reading of tame polyfolds, as in Part III's `theorem_15_3_7_existence`).
* `not_isInGoodPositionToPartialCone_of_le_reducedTangent`: on `∂C`, no non-zero subspace of the
  reduced tangent space `T^R_αC` is in good position to `C_αC`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology
open scoped Pointwise

noncomputable section

namespace Polyfold

section TopVec

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- **Good position on a topological vector space** (Definition 3.1.24, 2021): `N ∩ C` has
non-empty interior in `N`, and `N` has an algebraic complement `P` together with a neighbourhood
`U` of `0` and a von Neumann bounded set `B` such that `n ∈ C ↔ n + p ∈ C` for `n ∈ N`, `p ∈ P`
with `p ∈ sU` and `n ∉ sB` for some `s > 0`.  We read the text's `‖p‖ ≤ ε‖n‖` in this norm-free
form (`isInGoodPositionTop_iff_norm` on a normed space). -/
structure IsInGoodPositionTop (C : Set V) (N : Submodule ℝ V) : Prop where
  interior_nonempty : (interior (Subtype.val ⁻¹' C : Set N)).Nonempty
  exists_goodComplement : ∃ P : Submodule ℝ V, IsCompl N P ∧ ∃ U ∈ 𝓝 (0 : V), ∃ B : Set V,
    Bornology.IsVonNBounded ℝ B ∧ ∀ s : ℝ, 0 < s → ∀ n ∈ N, ∀ p ∈ P, p ∈ s • U → n ∉ s • B →
      (n ∈ C ↔ n + p ∈ C)

end TopVec

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {C : Set V} {N P : Submodule ℝ V}

/-- The good complement condition of `IsInGoodPositionTop` is the text's `‖p‖ ≤ ε‖n‖` on a
normed space (Definition 3.1.24). -/
theorem goodComplement_top_iff_norm :
    (∃ U ∈ 𝓝 (0 : V), ∃ B : Set V, Bornology.IsVonNBounded ℝ B ∧ ∀ s : ℝ, 0 < s →
      ∀ n ∈ N, ∀ p ∈ P, p ∈ s • U → n ∉ s • B → (n ∈ C ↔ n + p ∈ C)) ↔
      ∃ ε > 0, ∀ n ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + p ∈ C) := by
  constructor
  · rintro ⟨U, hU, B, hB, h⟩
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨R, hR⟩ := (NormedSpace.isVonNBounded_iff ℝ).1 hB |>.subset_closedBall 0
    set R' := max R 1 with hR'
    have hR'0 : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
    refine ⟨δ / (4 * R'), by positivity, fun n hn p hp hpn => ?_⟩
    by_cases hn0 : n = 0
    · subst hn0
      have : p = 0 := norm_le_zero_iff.1 (by simpa using hpn)
      subst this
      simp
    have hnpos : 0 < ‖n‖ := norm_pos_iff.2 hn0
    set s := ‖n‖ / (2 * R') with hs
    have hs0 : 0 < s := by positivity
    refine h s hs0 n hn p hp ?_ ?_
    · rw [mem_smul_set_iff_inv_smul_mem₀ hs0.ne']
      apply hδU
      rw [Metric.mem_ball, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hs0, hs]
      rw [inv_div, div_mul_eq_mul_div, div_lt_iff₀ hnpos]
      calc 2 * R' * ‖p‖ ≤ 2 * R' * (δ / (4 * R') * ‖n‖) := by gcongr
        _ = δ * ‖n‖ / 2 := by field_simp; ring
        _ < δ * ‖n‖ := by linarith [mul_pos hδ hnpos]
    · intro hmem
      rw [mem_smul_set_iff_inv_smul_mem₀ hs0.ne'] at hmem
      have h1 := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hs0, hs, inv_div] at h1
      have h2 : 2 * R' / ‖n‖ * ‖n‖ ≤ R := h1
      rw [div_mul_cancel₀ _ hnpos.ne'] at h2
      have : R ≤ R' := le_max_left _ _
      linarith
  · rintro ⟨ε, hε, h⟩
    refine ⟨Metric.closedBall 0 ε, Metric.closedBall_mem_nhds 0 hε, Metric.ball 0 1,
      (NormedSpace.isVonNBounded_iff ℝ).2 Metric.isBounded_ball, fun s hs n hn p hp hps hns => ?_⟩
    rw [mem_smul_set_iff_inv_smul_mem₀ hs.ne', Metric.mem_closedBall, dist_zero_right, norm_smul,
      norm_inv, Real.norm_eq_abs, abs_of_pos hs] at hps
    rw [mem_smul_set_iff_inv_smul_mem₀ hs.ne', Metric.mem_ball, dist_zero_right, norm_smul,
      norm_inv, Real.norm_eq_abs, abs_of_pos hs, not_lt] at hns
    refine h n hn p hp ?_
    have h1 : ‖p‖ ≤ ε * s := by
      rw [inv_mul_le_iff₀ hs] at hps; linarith
    have h2 : s ≤ ‖n‖ := by
      rw [le_inv_mul_iff₀ hs] at hns; linarith
    nlinarith

/-- **On a normed space, `IsInGoodPositionTop` is Definition 3.1.24 as printed**: interior of
`N ∩ C` in `N`, and a complement `P` with `ε > 0` such that `n ∈ C ↔ n + p ∈ C` for
`‖p‖ ≤ ε‖n‖`. -/
theorem isInGoodPositionTop_iff_norm :
    IsInGoodPositionTop C N ↔ (interior (Subtype.val ⁻¹' C : Set N)).Nonempty ∧
      ∃ P : Submodule ℝ V, IsCompl N P ∧
        ∃ ε > 0, ∀ n ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + p ∈ C) := by
  constructor
  · rintro ⟨hi, P, hP, hg⟩
    exact ⟨hi, P, hP, goodComplement_top_iff_norm.1 hg⟩
  · rintro ⟨hi, P, hP, hg⟩
    exact ⟨hi, P, hP, goodComplement_top_iff_norm.2 hg⟩

/-- **A non-zero subspace of the lineality space of a proper convex cone is not in good
position** (Definition 3.1.24): if `C` is closed under sums and positive multiples, `L` is a
subspace with `L ⊆ C` and `C ∩ −C ⊆ L`, `L ≠ V`, then no subspace `0 ≠ N ⊆ L` is in good position
to `C`: a good complement `P` would contain a `p ∉ C` (otherwise `V = N ⊕ P ⊆ L`), and for
`0 ≠ n ∈ N`, `n + tp ∉ C` for every `t > 0` while `n ∈ C`. -/
theorem not_isInGoodPositionTop_of_le_lineality
    (hadd : ∀ v w, v ∈ C → w ∈ C → v + w ∈ C) (hsmul : ∀ t : ℝ, 0 < t → ∀ v ∈ C, t • v ∈ C)
    {L : Submodule ℝ V} (hLC : ∀ v ∈ L, v ∈ C) (hCL : ∀ v, v ∈ C → -v ∈ C → v ∈ L)
    (hL : L ≠ ⊤) (hNL : N ≤ L) (hN0 : N ≠ ⊥) : ¬ IsInGoodPositionTop C N := by
  rw [isInGoodPositionTop_iff_norm]
  rintro ⟨-, P, hP, ε, hε, hg⟩
  obtain ⟨p₀, hp₀, hp₀C⟩ : ∃ p ∈ P, p ∉ C := by
    by_contra h
    push Not at h
    have hPL : P ≤ L := fun p hp => hCL p (h p hp) (h (-p) (P.neg_mem hp))
    apply hL
    rw [eq_top_iff, ← hP.sup_eq_top]
    exact sup_le hNL hPL
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  have hp0 : p₀ ≠ 0 := fun h => hp₀C (h ▸ hLC 0 L.zero_mem)
  have hnpos : 0 < ‖n‖ := norm_pos_iff.2 hn0
  have hppos : 0 < ‖p₀‖ := norm_pos_iff.2 hp0
  set t := ε * ‖n‖ / ‖p₀‖ with ht
  have htpos : 0 < t := by positivity
  have hnC : n ∈ C := hLC n (hNL hn)
  have hnp : n + t • p₀ ∈ C := by
    refine (hg n hn (t • p₀) (P.smul_mem t hp₀) ?_).1 hnC
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, ht, div_mul_cancel₀ _ hppos.ne']
  have htp : t • p₀ ∈ C := by
    have := hadd _ _ hnp (hLC (-n) (L.neg_mem (hNL hn)))
    simpa using this
  apply hp₀C
  have := hsmul t⁻¹ (inv_pos.2 htpos) _ htp
  rwa [smul_smul, inv_mul_cancel₀ htpos.ne', one_smul] at this

end Normed

section Transfer

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] {C : Set V} {N : Submodule ℝ V}

/-- `e⁻¹(w) ∈ N` for `w ∈ e(N)`. -/
theorem symm_mem_of_mem_map (e : V ≃L[ℝ] W) {w : W} (hw : w ∈ N.map (e : V →ₗ[ℝ] W)) :
    e.symm w ∈ N := by
  obtain ⟨n, hn, rfl⟩ := Submodule.mem_map.1 hw
  simpa using hn

/-- The restriction of a topological linear isomorphism to `N → N.map e`. -/
def homeomorphMap (e : V ≃L[ℝ] W) (N : Submodule ℝ V) :
    N ≃ₜ N.map (e : V →ₗ[ℝ] W) where
  toFun n := ⟨e n, n, n.2, rfl⟩
  invFun w := ⟨e.symm w, symm_mem_of_mem_map e w.2⟩
  left_inv n := Subtype.ext (e.symm_apply_apply n)
  right_inv w := Subtype.ext (e.apply_symm_apply w)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- **Good position is carried along a topological linear isomorphism.** -/
theorem IsInGoodPositionTop.map (e : V ≃L[ℝ] W) (h : IsInGoodPositionTop C N) :
    IsInGoodPositionTop (e.symm ⁻¹' C) (N.map (e : V →ₗ[ℝ] W)) := by
  obtain ⟨⟨n₀, hn₀⟩, P, hP, U, hU, B, hB, hg⟩ := h
  set h := homeomorphMap e N
  refine ⟨⟨h n₀, ?_⟩, P.map (e : V →ₗ[ℝ] W), ?_, e.symm ⁻¹' U, ?_, e '' B, ?_, ?_⟩
  · have hpre : (Subtype.val ⁻¹' (e.symm ⁻¹' C) : Set (N.map (e : V →ₗ[ℝ] W))) =
        h.symm ⁻¹' (Subtype.val ⁻¹' C) := by
      ext w; rfl
    rw [hpre, ← h.symm.preimage_interior]
    change h.symm (h n₀) ∈ interior (Subtype.val ⁻¹' C : Set N)
    rw [h.symm_apply_apply]
    exact hn₀
  · exact (Submodule.orderIsoMapComap (e : V ≃ₗ[ℝ] W)).isCompl hP
  · exact e.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hU)
  · exact hB.image (e : V →L[ℝ] W)
  · rintro s hs _ ⟨n, hn, rfl⟩ _ ⟨p, hp, rfl⟩ hps hns
    have hps' : p ∈ s • U := by
      rw [mem_smul_set_iff_inv_smul_mem₀ hs.ne'] at hps ⊢
      simpa using hps
    have hns' : n ∉ s • B := by
      rintro ⟨b, hb, rfl⟩
      exact hns ⟨e b, ⟨b, hb, rfl⟩, by simp⟩
    have := hg s hs n hn p hp hps' hns'
    simpa [mem_preimage] using this

/-- **Good position and topological linear isomorphisms**: `N` is in good position to `e⁻¹(C')`
iff `e(N)` is in good position to `C'`. -/
theorem isInGoodPositionTop_preimage_iff (e : V ≃L[ℝ] W) {C' : Set W} :
    IsInGoodPositionTop (e ⁻¹' C') N ↔ IsInGoodPositionTop C' (N.map (e : V →ₗ[ℝ] W)) := by
  constructor
  · intro h
    have := h.map e
    rwa [← preimage_comp, show (⇑e ∘ ⇑e.symm) = id from funext e.apply_symm_apply,
      preimage_id] at this
  · intro h
    have := h.map e.symm
    convert this using 2
    · ext v; simp
    · ext v
      simp only [Submodule.mem_map]
      constructor
      · intro hv; exact ⟨e v, ⟨v, hv, rfl⟩, by simp⟩
      · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩; simpa using hu

end Transfer

section Subspace

variable {E : ScBanach} {T : Submodule ℝ (E 0)} {C : Set (E 0)}

/-- A point of `N.map T.subtype`, as a point of `T`, lies in `N`. -/
theorem mk_mem_of_mem_map_subtype (N : Submodule ℝ T) {x : E 0} (hx : x ∈ N.map T.subtype) :
    (⟨x, Submodule.map_subtype_le T N hx⟩ : T) ∈ N := by
  obtain ⟨n, hn, rfl⟩ := Submodule.mem_map.1 hx
  exact hn

/-- `N ≅ N.map T.subtype` for a subspace `N` of `T ⊆ E₀`. -/
def homeomorphMapSubtype (N : Submodule ℝ T) : N ≃ₜ N.map T.subtype where
  toFun n := ⟨n.1.1, n.1, n.2, rfl⟩
  invFun w := ⟨⟨w.1, Submodule.map_subtype_le T N w.2⟩, mk_mem_of_mem_map_subtype N w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- **Part I's good position inside a subspace `T ⊆ E₀` (`IsInGoodPositionIn`) is the topological
good position in `T`** for subspaces of `T`. -/
theorem isInGoodPositionIn_map_subtype_iff (N : Submodule ℝ T) :
    IsInGoodPositionIn E T C (N.map T.subtype) ↔
      IsInGoodPositionTop (Subtype.val ⁻¹' C : Set T) N := by
  rw [isInGoodPositionTop_iff_norm]
  set h := homeomorphMapSubtype N
  have hpre : (Subtype.val ⁻¹' C : Set (N.map T.subtype)) =
      h.symm ⁻¹' (Subtype.val ⁻¹' (Subtype.val ⁻¹' C : Set T) : Set N) := by
    ext w; rfl
  have hint : (interior (Subtype.val ⁻¹' C : Set (N.map T.subtype))).Nonempty ↔
      (interior (Subtype.val ⁻¹' (Subtype.val ⁻¹' C : Set T) : Set N)).Nonempty := by
    rw [hpre, ← h.symm.preimage_interior]
    constructor
    · rintro ⟨w, hw⟩; exact ⟨_, hw⟩
    · rintro ⟨n, hn⟩
      refine ⟨h n, ?_⟩
      change h.symm (h n) ∈ interior (Subtype.val ⁻¹' (Subtype.val ⁻¹' C : Set T) : Set N)
      rw [h.symm_apply_apply]; exact hn
  constructor
  · rintro ⟨-, hi, P, hPT, hNP, hsup, ε, hε, hg⟩
    refine ⟨hint.1 hi, P.comap T.subtype, ?_, ε, hε, fun x hx p hp hpx => ?_⟩
    · refine ⟨Submodule.disjoint_def.2 fun x hxN hxP => ?_, codisjoint_iff.2 (eq_top_iff.2
        fun x _ => ?_)⟩
      · have : (x : E 0) ∈ N.map T.subtype ⊓ P := ⟨⟨x, hxN, rfl⟩, hxP⟩
        rw [hNP] at this
        exact Subtype.ext ((Submodule.mem_bot ℝ).1 this)
      · have hx : (x : E 0) ∈ N.map T.subtype ⊔ P := by rw [hsup]; exact x.2
        obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx
        obtain ⟨a', ha', rfl⟩ := Submodule.mem_map.1 ha
        refine Submodule.mem_sup.2 ⟨a', ha', ⟨b, hPT hb⟩, hb, Subtype.ext ?_⟩
        exact hab
    · exact hg x ⟨x, hx, rfl⟩ p hp hpx
  · rintro ⟨hi, P', hP', ε, hε, hg⟩
    refine ⟨Submodule.map_subtype_le T N, hint.2 hi, P'.map T.subtype,
      Submodule.map_subtype_le T P', ?_, ?_, ε, hε, ?_⟩
    · rw [eq_bot_iff]
      rintro x ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
      have hab' : b = a := Subtype.ext hab
      subst hab'
      have := Submodule.disjoint_def.1 hP'.disjoint b ha hb
      rw [this]; exact Submodule.zero_mem _
    · refine le_antisymm (sup_le (Submodule.map_subtype_le T N) (Submodule.map_subtype_le T P'))
        fun x hx => ?_
      have : (⟨x, hx⟩ : T) ∈ N ⊔ P' := by rw [hP'.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 this
      exact Submodule.mem_sup.2 ⟨a, ⟨a, ha, rfl⟩, b, ⟨b, hb, rfl⟩, congrArg Subtype.val hab⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨p, hp, rfl⟩ hpx
      exact hg x hx p hp hpx

end Subspace

section MPolyfoldCone

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **Good position to `C_xX` read in a chart**: a subspace `N ⊆ T_xX` is in good position to the
partial cone `C_xX` (topological good position in `T_xX`) iff `Tφ(N) ⊆ T_{φ(x)}O` is in good
position to `C_{φ(x)}` inside `T_{φ(x)}O` (`IsInGoodPositionIn`, Definition 3.1.24 inside a
subspace), for every chart `φ` around `x` and every presentation `T` of its partial quadrant. -/
theorem MPolyfold.isInGoodPositionTop_tangentPartialCone_iff {φ : MChart X} (hφ : P.IsChart φ)
    {x : P.Level 1} (hx : P.levelVal 1 x ∈ φ.source) {n : ℕ} {W : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) (N : Submodule ℝ (P.tangentFiber x)) :
    IsInGoodPositionTop (P.tangentPartialCone x) N ↔
      IsInGoodPositionIn φ.model.E (MPolyfold.tangentFiberModel hφ hx)
        (partialQuadrantAtWith T (φ (P.levelVal 1 x))) (N.map (MPolyfold.fiberCoord hφ hx)) := by
  rw [MPolyfold.tangentPartialCone_eq hφ hx T hT]
  set e := MPolyfold.tangentFiberContinuousLinearEquiv hφ hx
  have hC : MPolyfold.partialConeFiber hφ hx T =
      e ⁻¹' (Subtype.val ⁻¹' partialQuadrantAtWith T (φ (P.levelVal 1 x))) := rfl
  have hN : N.map (MPolyfold.fiberCoord hφ hx) =
      (N.map (e : P.tangentFiber x →ₗ[ℝ] _)).map (MPolyfold.tangentFiberModel hφ hx).subtype := by
    rw [← Submodule.map_comp]; rfl
  rw [hC, hN, isInGoodPositionIn_map_subtype_iff, isInGoodPositionTop_preimage_iff]

end MPolyfoldCone

section Bundle

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr MPolyfold

omit [T2Space Y] [ParacompactSpace Y] in
/-- In a strong bundle chart, `T_{φ(x)}O = Dr(φ(x))E` for the base retraction `r` of the chart. -/
theorem StrongBundleChart.tangentFiberModel_eq_rangeS (c : StrongBundleChart PX P)
    {x : PX.Level 1} (hx : PX.levelVal 1 x ∈ c.φ.source) :
    tangentFiberModel c.isChart hx =
      rangeS (scDeriv c.U (r c.R) (levelLift c.φ 1 (PX.levelVal 1 x))) := by
  ext v
  rw [mem_tangentFiberModel, ← c.base_retract, retractTangent_eq]
  have h := (c.isRetraction.baseRetraction c.relOpen).mem_tangent_iff_mem_range
    (x := levelLift c.φ 1 (PX.levelVal 1 x)) (h := v)
    (by rw [c.base_retract]; exact levelLift_mem_lvlSet_one c.isChart hx)
  rw [h]
  exact Iff.rfl

omit [T2Space Y] [ParacompactSpace Y] in
/-- The chart coordinates of a tangent vector lie in `Dr(φ(x))E`. -/
theorem StrongBundleChart.fiberCoord_mem_rangeS (c : StrongBundleChart PX P)
    {x : PX.Level 1} (hx : PX.levelVal 1 x ∈ c.φ.source) (α : PX.tangentFiber x) :
    fiberCoord c.isChart hx α ∈
      rangeS (scDeriv c.U (r c.R) (levelLift c.φ 1 (PX.levelVal 1 x))) := by
  rw [← c.tangentFiberModel_eq_rangeS hx]
  exact (tangentFiberEquiv c.isChart hx α).2

/-- `f'(x)` in chart coordinates is the chart linearization `Lin(φ(x))` on `Dr(φ(x))E`. -/
theorem StrongBundle.linAt_fiberCoord (hf : B.IsScSmoothSection f) {x : PX.Level 1}
    (h0 : IsZeroAt P f (PX.levelVal 1 x)) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hx : PX.levelVal 1 x ∈ c.φ.source) (α : PX.tangentFiber x) :
    linAt c.U c.R (c.principal f) (levelLift c.φ 1 (PX.levelVal 1 x))
        ⟨fiberCoord c.isChart hx α, c.fiberCoord_mem_rangeS hx α⟩ =
      c.fiberLin hx (B.linZeroAt hf x h0 α) := by
  rw [B.linZeroAt_eq hf h0 hc hx, StrongBundle.fiberLin_linIntr, StrongBundleChart.linChart_apply,
    linAt_apply]
  rfl

/-- **The kernel of `f'(x)` in a chart**: `Tφ(ker f'(x)) = ker Lin(φ(x))` as subspaces of `E₀`. -/
theorem StrongBundle.map_ker_linZeroAt (hf : B.IsScSmoothSection f) {x : PX.Level 1}
    (h0 : IsZeroAt P f (PX.levelVal 1 x)) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hx : PX.levelVal 1 x ∈ c.φ.source) :
    (LinearMap.ker (B.linZeroAt hf x h0)).map (fiberCoord c.isChart hx) =
      (LinearMap.ker (linAt c.U c.R (c.principal f) (levelLift c.φ 1 (PX.levelVal 1 x)) :
        ↥(rangeS (scDeriv c.U (r c.R) (levelLift c.φ 1 (PX.levelVal 1 x)))) →ₗ[ℝ] c.F 0)).map
        (rangeS (scDeriv c.U (r c.R) (levelLift c.φ 1 (PX.levelVal 1 x)))).subtype := by
  have key : ∀ α, B.linZeroAt hf x h0 α = 0 ↔
      linAt c.U c.R (c.principal f) (levelLift c.φ 1 (PX.levelVal 1 x))
        ⟨fiberCoord c.isChart hx α, c.fiberCoord_mem_rangeS hx α⟩ = 0 := by
    intro α
    rw [B.linAt_fiberCoord hf h0 hc hx α]
    constructor
    · intro h; rw [h, map_zero]
    · intro h; exact c.fiberLin_injective hx (by rw [h, map_zero])
  ext v
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨_, (key α).1 hα, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    have hwT : (w : c.φ.model.E 0) ∈ tangentFiberModel c.isChart hx := by
      rw [c.tangentFiberModel_eq_rangeS hx]; exact w.2
    set α := (tangentFiberEquiv c.isChart hx).symm ⟨w, hwT⟩
    have hα : fiberCoord c.isChart hx α = w := by
      rw [fiberCoord_eq_coe, Equiv.apply_symm_apply]
    refine ⟨α, (key α).2 ?_, hα⟩
    have : (⟨fiberCoord c.isChart hx α, c.fiberCoord_mem_rangeS hx α⟩ :
        ↥(rangeS (scDeriv c.U (r c.R) (levelLift c.φ 1 (PX.levelVal 1 x))))) = w :=
      Subtype.ext hα
    rw [this]; exact hw

/-- **`f'(x)` is onto iff the linearization in a chart is onto the fibre `K_{φ(x)}`.** -/
theorem StrongBundle.surjective_linZeroAt_iff (hf : B.IsScSmoothSection f) {x : PX.Level 1}
    (h0 : IsZeroAt P f (PX.levelVal 1 x)) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hx : PX.levelVal 1 x ∈ c.φ.source) :
    Surjective (B.linZeroAt hf x h0) ↔
      ∀ k, (c.φ (PX.levelVal 1 x), k) ∈ c.K →
        ∃ v, linAt c.U c.R (c.principal f) (levelLift c.φ 1 (PX.levelVal 1 x)) v = k := by
  constructor
  · intro hs k hk
    obtain ⟨w, hw⟩ := c.mem_range_fiberLin hx hk
    obtain ⟨α, rfl⟩ := hs w
    exact ⟨_, (B.linAt_fiberCoord hf h0 hc hx α).trans hw⟩
  · intro hs w
    have hK : (c.φ (PX.levelVal 1 x), c.fiberLin hx w) ∈ c.K := by
      rw [← c.apply_fiberLin hx w, ← c.image_source]; exact ⟨_, c.fiberLin_src hx w, rfl⟩
    obtain ⟨v, hv⟩ := hs _ hK
    have hvT : (v : c.φ.model.E 0) ∈ tangentFiberModel c.isChart hx := by
      rw [c.tangentFiberModel_eq_rangeS hx]; exact v.2
    set α := (tangentFiberEquiv c.isChart hx).symm ⟨v, hvT⟩
    have hα' : fiberCoord c.isChart hx α = v := by
      rw [fiberCoord_eq_coe, Equiv.apply_symm_apply]
    have hα : (⟨fiberCoord c.isChart hx α, c.fiberCoord_mem_rangeS hx α⟩ :
        ↥(rangeS (scDeriv c.U (r c.R) (levelLift c.φ 1 (PX.levelVal 1 x))))) = v :=
      Subtype.ext hα'
    refine ⟨α, c.fiberLin_injective hx ?_⟩
    rw [← B.linAt_fiberCoord hf h0 hc hx α, hα, hv]

/-- **Good position of `ker f'(x)` to `C_xX`, read in a chart**: the topological good position of
`ker f'(x) ⊆ T_xX` to the partial cone `C_xX` is Part I's good position of `ker Lin(φ(x))` to
`C_{φ(x)}` inside `T_{φ(x)}O = Dr(φ(x))E`. -/
theorem StrongBundle.isInGoodPositionTop_ker_linZeroAt_iff (hf : B.IsScSmoothSection f)
    {x : PX.Level 1} (h0 : IsZeroAt P f (PX.levelVal 1 x)) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) (hx : PX.levelVal 1 x ∈ c.φ.source) {n : ℕ} {W : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n W 0) :
    IsInGoodPositionTop (PX.tangentPartialCone x) (LinearMap.ker (B.linZeroAt hf x h0)) ↔
      IsInGoodPositionIn c.φ.model.E
        (rangeS (scDeriv c.U (r c.R) (levelLift c.φ 1 (PX.levelVal 1 x))))
        (partialQuadrantAtWith T (c.φ (PX.levelVal 1 x)))
        ((LinearMap.ker (linAt c.U c.R (c.principal f) (levelLift c.φ 1 (PX.levelVal 1 x)) :
          ↥(rangeS (scDeriv c.U (r c.R) (levelLift c.φ 1 (PX.levelVal 1 x)))) →ₗ[ℝ] c.F 0)).map
          (rangeS (scDeriv c.U (r c.R) (levelLift c.φ 1 (PX.levelVal 1 x)))).subtype) := by
  rw [MPolyfold.isInGoodPositionTop_tangentPartialCone_iff c.isChart hx T hT,
    B.map_ker_linZeroAt hf h0 hc hx, c.tangentFiberModel_eq_rangeS hx]

/-- **Definition 3.6.6 in the text's form** (2021 p. 136): for an sc-Fredholm section with tame
germ data and a zero `x` on level `1`, Part I's good position in a tame chart
(`IsGoodPositionGermTame`) holds iff (1) `f'(x) : T_xX → Y_x` is onto and (2) `ker f'(x)` is in
good position to the partial cone `C_xX ⊆ T_xX` (topological good position,
`IsInGoodPositionTop`).  At an interior point `C_xX = T_xX` and (2) holds for every subspace. -/
theorem StrongBundle.isGoodPositionGermTame_iff_tangent (hf : B.IsScFredholmSectionTame f)
    {x : PX.Level 1} (h0 : IsZeroAt P f (PX.levelVal 1 x)) :
    B.IsGoodPositionGermTame f (PX.levelVal 1 x) ↔
      Surjective (B.linZeroAt hf.isScSmooth x h0) ∧
        IsInGoodPositionTop (PX.tangentPartialCone x)
          (LinearMap.ker (B.linZeroAt hf.isScSmooth x h0)) := by
  have hfs := hf.isScSmooth
  constructor
  · intro hg
    have hlin := hg.isGoodPositionGerm.isLinSurjAt hfs
    obtain ⟨-, c, hct, hyV, hφ0, h0U, g, s, hfill, -, -, -, G, Dg, -, hDg, hgp⟩ := hg
    have hz : c.φ.model.E.toBase 1 (levelLift c.φ 1 (PX.levelVal 1 x)) =
        c.φ (PX.levelVal 1 x) :=
      PX.toBase_levelLift c.isChart hyV (levelVal_mem x)
    refine ⟨(B.surjective_linZeroAt_iff hfs h0 hct.1 hyV).2
      (hlin.linAt_surjective hfs h0 hct.1 hyV hz), ?_⟩
    obtain ⟨n, W, T, hT⟩ := c.φ.model.isPartialQuadrant
    rw [B.isInGoodPositionTop_ker_linZeroAt_iff hfs h0 hct.1 hyV T hT]
    have hz0 : levelLift c.φ 1 (PX.levelVal 1 x) = 0 :=
      c.φ.model.E.toBase_injective 1 (by rw [hz, hφ0, map_zero])
    have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := by
      rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model _ hyV
    obtain ⟨-, hker⟩ := StrongBundle.linAt_eq_germDeriv_chart hfs hct.1 hyV
      (z := 0) (by rw [map_zero, hφ0]) h0U h0O hDg (G.zero_mem 1)
      (by rw [hφ0, ← c.r_image]; exact hfill.eq_on)
    rw [hz0, hker, inf_eq_left.2 hgp.kernel.le, hφ0, partialQuadrantAtWith_zero, ← hT]
    exact hgp.kernel
  · rintro ⟨hsurj, hker⟩
    have hys := hf.toIsScFredholmSection.mem_smoothSet_of_isZeroAt h0
    obtain ⟨c, hcm, hyc⟩ := B.exists_chart_mem (PX.levelVal 1 x)
    have hc := B.isChart_of_mem hcm
    obtain ⟨n, W, T, hT⟩ := c.φ.model.isPartialQuadrant
    have hz := PX.toBase_levelLift c.isChart hyc (levelVal_mem x)
    exact (StrongBundle.isGoodPositionGerm_of_linAt_surj hfs (hf.germ _ hys) h0 hc hyc hz T hT
      ((B.surjective_linZeroAt_iff hfs h0 hc hyc).1 hsurj)
      ((B.isInGoodPositionTop_ker_linZeroAt_iff hfs h0 hc hyc T hT).1 hker)).toTame hfs
      (hf.germTame _ hys) h0

end Bundle

universe u

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} (α : C.Obj) [hα : Fact (S.TangentObj α)]

variable (S) in
/-- **A subspace `N ⊆ T_αC` in good position to the partial cone `C_αC`** (Remark 17.2.18,
2021 p. 784, Definition 3.1.24): topological good position (`IsInGoodPositionTop`) in the
topological vector space `T_αC` (Proposition 17.2.4). -/
def IsInGoodPositionToPartialCone (N : Submodule ℝ (S.TangentSpaceAt α)) : Prop :=
  IsInGoodPositionTop (S.partialCone α) N

/-- **Good position to `C_αC` read through any uniformizer**: for every `Ψ ∈ F(α)` (more
generally every `Ψ` of the construction) and the level-`1` point `q` with `Ψ(q) = α`, `N` is in
good position to `C_αC` iff `S_Ψ(N) ⊆ T_qO` is in good position to the partial cone `C_qO`. -/
theorem isInGoodPositionToPartialCone_iff (Ψ : S.Unif) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) (N : Submodule ℝ (S.TangentSpaceAt α)) :
    S.IsInGoodPositionToPartialCone α N ↔
      IsInGoodPositionTop (Ψ.1.P.tangentPartialCone x)
        (N.map (S.tangentChartCLE α Ψ x hx : S.TangentSpaceAt α →ₗ[ℝ] Ψ.1.P.tangentFiber x)) := by
  rw [IsInGoodPositionToPartialCone, partialCone_eq α Ψ x hx (MPolyfold.isChart_fiberChart _ _)
    (MPolyfold.mem_fiberChart_source _ _) (MPolyfold.fiberChartPresentation _ _)
    (MPolyfold.fiberChartPresentation_spec _)]
  exact isInGoodPositionTop_preimage_iff _

/-- `C_αC` is closed under sums. -/
theorem add_mem_partialCone {e e' : S.TangentSpaceAt α} (he : e ∈ S.partialCone α)
    (he' : e' ∈ S.partialCone α) : e + e' ∈ S.partialCone α := by
  intro i hi
  have h1 := he i hi
  have h2 := he' i hi
  change 0 ≤ ((MPolyfold.fiberChartPresentation _ _) 0 (MPolyfold.fiberCoord _ _
    (S.refChartCLE α (e + e')))).1 i
  rw [map_add, map_add, map_add]
  exact add_nonneg h1 h2

/-- `C_αC` is closed under non-negative multiples. -/
theorem smul_mem_partialCone {t : ℝ} (ht : 0 ≤ t) {e : S.TangentSpaceAt α}
    (he : e ∈ S.partialCone α) : t • e ∈ S.partialCone α := by
  intro i hi
  have h1 := he i hi
  change 0 ≤ ((MPolyfold.fiberChartPresentation _ _) 0 (MPolyfold.fiberCoord _ _
    (S.refChartCLE α (t • e)))).1 i
  rw [map_smul, map_smul, map_smul]
  exact mul_nonneg ht h1

/-- **A non-zero subspace of the reduced tangent space is not in good position to `C_αC` on the
boundary**: for a tame `C`, a smooth `α` with `d_C(α) ≥ 1` and `0 ≠ N ⊆ T^R_αC`, `N` is not in
good position to `C_αC` (`not_isInGoodPositionTop_of_le_lineality` in the Banach space
`T_qO`, `T^R_αC = C_αC ∩ −C_αC`, `C_αC ≠ T_αC`). -/
theorem not_isInGoodPositionToPartialCone_of_le_reducedTangent (htame : S.IsTame)
    (hs : S.IsSmoothObj α) (hb : 1 ≤ S.degIndex α) {N : Submodule ℝ (S.TangentSpaceAt α)}
    (hN : N ≤ S.reducedTangent α) (hN0 : N ≠ ⊥) : ¬ S.IsInGoodPositionToPartialCone α N := by
  set Ψ := S.refUnif hα.out
  set x := S.refPoint hα.out
  set L := (S.refChartCLE α).trans (MPolyfold.tangentFiberContinuousLinearEquiv
    (Ψ.1.P.isChart_fiberChart x) (Ψ.1.P.mem_fiberChart_source x))
  set C' : Set (MPolyfold.tangentFiberModel (Ψ.1.P.isChart_fiberChart x)
      (Ψ.1.P.mem_fiberChart_source x)) :=
    Subtype.val ⁻¹' partialQuadrantAtWith (Ψ.1.P.fiberChartPresentation x)
      ((Ψ.1.P.fiberChart x) (Ψ.1.P.levelVal 1 x))
  have hcone : S.partialCone α = L ⁻¹' C' := rfl
  have hmem : ∀ e, e ∈ S.partialCone α ↔ L e ∈ C' := fun e => by rw [hcone]; rfl
  intro h
  rw [IsInGoodPositionToPartialCone, hcone, isInGoodPositionTop_preimage_iff] at h
  refine not_isInGoodPositionTop_of_le_lineality (C := C') ?_ ?_
    (L := (S.reducedTangent α).map (L : S.TangentSpaceAt α →ₗ[ℝ] _)) ?_ ?_ ?_
    (Submodule.map_mono hN) ?_ h
  · intro v w hv hw i hi
    change 0 ≤ ((Ψ.1.P.fiberChartPresentation x) 0 ((v : _) + (w : _))).1 i
    rw [map_add]
    exact add_nonneg (hv i hi) (hw i hi)
  · intro t ht v hv i hi
    change 0 ≤ ((Ψ.1.P.fiberChartPresentation x) 0 (t • (v : _))).1 i
    rw [map_smul]
    exact mul_nonneg ht.le (hv i hi)
  · rintro _ ⟨e, he, rfl⟩
    exact (hmem e).1 (reducedTangent_subset_partialCone α he)
  · intro v hv hnv
    refine ⟨L.symm v, (mem_reducedTangent_iff_lineality α _).2 ⟨(hmem _).2 ?_, (hmem _).2 ?_⟩,
      by simp⟩
    · simpa using hv
    · simpa using hnv
  · intro htop
    apply partialCone_ne_univ α htame hs hb
    refine eq_univ_of_forall fun e => ?_
    have : L e ∈ (S.reducedTangent α).map (L : S.TangentSpaceAt α →ₗ[ℝ] _) := by
      rw [htop]; exact Submodule.mem_top
    obtain ⟨e', he', hee'⟩ := this
    have : e' = e := L.injective hee'
    exact this ▸ reducedTangent_subset_partialCone α he'
  · intro hbot
    apply hN0
    rw [eq_bot_iff]
    intro e he
    have : L e ∈ N.map (L : S.TangentSpaceAt α →ₗ[ℝ] _) := ⟨e, he, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    exact L.injective (by rw [this, map_zero])

end GCT.PolyfoldConstruction

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open GroupoidalCategory GroupoidalCategory.BanachFunctor StrongBundleUniformizerConstruction
  StrongBundleUniformizerData PolyfoldConstruction

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  (Q : V.StrongPolyfoldBundleConstruction S) {f : V.SectionFunctor}

variable (f) in
/-- **`ker f'(α)` is in good position to the partial cone `C_αC`** (the hypothesis of
Theorem 18.1.5, 2021 p. 846, with Remark 17.2.18): the kernel of the linearization
`f'(α) : T_αC → E_α` (Definition 18.1.3) is in good position to `C_αC ⊆ T_αC`. -/
def IsKernelInGoodPosition (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] (h0 : f.toFun α = V.objMk α 0) (hne : (Q.F α).Nonempty) : Prop :=
  S.IsInGoodPositionToPartialCone α (LinearMap.ker (Q.linearization f hf α h0 hne))

/-- `S_Ψ(ker f'(α)) = ker f'_Ψ̄(q)`. -/
theorem map_ker_sectionLin (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] (h0 : f.toFun α = V.objMk α 0) {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α)
    (x : Ψ.1.base.P.Level 1) (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) :
    (LinearMap.ker (Q.sectionLin hf α h0 hΨ x hx)).map
        (S.tangentChartCLE α (Q.baseUnif Ψ) x hx :
          S.TangentSpaceAt α →ₗ[ℝ] Ψ.1.base.P.tangentFiber x) =
      LinearMap.ker (Ψ.1.B.linZeroAt (hf α Ψ.1 hΨ) x (isZeroAt_localRep h0 hx)) := by
  ext v
  constructor
  · rintro ⟨e, he, rfl⟩
    simpa [sectionLin] using he
  · intro hv
    refine ⟨(S.tangentChartCLE α (Q.baseUnif Ψ) x hx).symm v, ?_, by simp⟩
    simpa [sectionLin] using hv

/-- **The intrinsic hypothesis of Theorem 18.1.5 is Part I's good position in a uniformizer**:
for every `Ψ̄ ∈ F̄(α)` and the level-`1` point `q₀` with `Ψ(q₀) = α`, `f_Ψ̄` is in good position at
`q₀` (Definition 3.6.6 in a tame chart, the reading of `theorem_18_1_5_model`) iff `f'(α)` is onto
and `ker f'(α)` is in good position to the partial cone `C_αC` (Remark 17.2.18). -/
theorem isGoodPositionGermTame_localRep_iff (hf : Q.IsScSmoothSectionFunctor f)
    (hft : Q.IsScFredholmSectionFunctorTame f) (α : C.Obj) [Fact (S.TangentObj α)]
    (h0 : f.toFun α = V.objMk α 0) (hne : (Q.F α).Nonempty) {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α)
    (x : Ψ.1.base.P.Level 1) (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) :
    Ψ.1.B.IsGoodPositionGermTame (Ψ.1.localRep f) (Ψ.1.base.P.levelVal 1 x) ↔
      Surjective (Q.linearization f hf α h0 hne) ∧ Q.IsKernelInGoodPosition f hf α h0 hne := by
  rw [Ψ.1.B.isGoodPositionGermTame_iff_tangent (hft α Ψ.1 hΨ) (isZeroAt_localRep h0 hx),
    Q.surjective_linearization_iff f hf α h0 hne hΨ x hx, IsKernelInGoodPosition,
    isInGoodPositionToPartialCone_iff α (Q.baseUnif Ψ) x hx,
    ← Q.definition_18_1_3 hf α h0 hne hΨ x hx, Q.map_ker_sectionLin hf α h0 hΨ x hx]

/-- **Theorem 18.1.5 (implicit function theorem), 2021 p. 846, with the text's hypothesis**, and
tame germ data (`hft`, the standing reading of tame polyfolds: README, germ data in a tame chart;
as in `theorem_18_1_5_model` and Part III's `theorem_15_3_7_existence`).  Let `f` be an sc-Fredholm
section functor, `α` an object with `f(α) = 0`, `f'(α) : T_αC → E_α` onto and `ker f'(α)` in good
position to the partial cone `C_αC` (Remark 17.2.18).  For every family `Ψ̄` of strong bundle
uniformizers containing some `Ψ̄_λ ∈ F̄(α)`, with `q₀` the level-`1` point over `α`, there is a
natural representation `U(x₀)` of `G_{x₀}` at `x₀ = (λ, q₀)` in the model `X_Ψ` whose image
`U = |Γ|(π(U(x₀)))` is an open neighbourhood of `|α|` in `|C|`, with the conclusions (1), (2) and
the Note of `theorem_18_1_5_model`. -/
theorem theorem_18_1_5 {ι : Type u} (Ψb : ι → Q.Unif)
    (hf : Q.IsScFredholmSectionFunctor f) (hft : Q.IsScFredholmSectionFunctorTame f)
    {α : C.Obj} [Fact (S.TangentObj α)] (h0 : f.toFun α = V.objMk α 0) (hne : (Q.F α).Nonempty)
    (hsurj : Surjective (Q.linearization f hf.isScSmoothSectionFunctor α h0 hne))
    (hker : Q.IsKernelInGoodPosition f hf.isScSmoothSectionFunctor α h0 hne)
    {i : ι} (hΨ : (Ψb i).1 ∈ Q.F α) (x : (Ψb i).1.base.P.Level 1)
    (hx : (Ψb i).1.base.obj ((Ψb i).1.base.P.levelVal 1 x) = α) :
    ∃ R : (Q.modelSEP Ψb).X.NaturalRep ⟨i, (Ψb i).1.base.P.levelVal 1 x⟩,
      IsOpen ((S.modelFunctor (Q.modelBase Ψb)).orbitMap ''
        ((S.modelEP (Q.modelBase Ψb)).X.π '' R.U)) ∧
      C.toGroupoidStr.π α ∈
        (S.modelFunctor (Q.modelBase Ψb)).orbitMap ''
          ((S.modelEP (Q.modelBase Ψb)).X.π '' R.U) ∧
      C.IsOrbifoldTypeBranched f.zeroIndicator ∧
      (∀ y, f.zeroIndicator ((S.modelFunctor (Q.modelBase Ψb)).obj y) =
        (SBLocalization.zeroMultisection (Q.modelSEP Ψb) (Q.modelSection Ψb f y) : ℚ)) ∧
      (∀ y ∈ R.U, (S.modelFunctor (Q.modelBase Ψb)).obj y ∈ f.zeroSet →
        Nonempty ((Q.modelSEP Ψb).X.TameBranchingStructure
          (fun z => f.zeroIndicator ((S.modelFunctor (Q.modelBase Ψb)).obj z)) y)) ∧
      (∀ y ∈ R.U, (S.modelFunctor (Q.modelBase Ψb)).obj y ∈ f.zeroSet →
        SBLocalization.IsGoodPositionAt (A := Q.modelSEP Ψb) (Q.modelSection Ψb f)
          (SBLocalization.zeroMultisection (Q.modelSEP Ψb)) y) ∧
      (Q.modelSEP Ψb).X.PObj.IsSmoothSubmanifold
        {y ∈ R.U | (S.modelFunctor (Q.modelBase Ψb)).obj y ∈ f.zeroSet} ∧
      ∀ g, ∀ y ∈ R.U, (S.modelFunctor (Q.modelBase Ψb)).obj y ∈ f.zeroSet →
        (S.modelFunctor (Q.modelBase Ψb)).obj (R.Φ g y) ∈ f.zeroSet := by
  have hgp := (Q.isGoodPositionGermTame_localRep_iff hf.isScSmoothSectionFunctor hft α h0 hne hΨ
    x hx).2 ⟨hsurj, hker⟩
  have h0' : (S.modelFunctor (Q.modelBase Ψb)).obj ⟨i, (Ψb i).1.base.P.levelVal 1 x⟩ ∈
      f.zeroSet := by
    have e : (S.modelFunctor (Q.modelBase Ψb)).obj ⟨i, (Ψb i).1.base.P.levelVal 1 x⟩ = α := hx
    rw [e]; exact h0
  have hπ : C.toGroupoidStr.π ((S.modelFunctor (Q.modelBase Ψb)).obj
      ⟨i, (Ψb i).1.base.P.levelVal 1 x⟩) = C.toGroupoidStr.π α := by
    change C.toGroupoidStr.π ((Ψb i).1.base.obj ((Ψb i).1.base.P.levelVal 1 x)) = _
    rw [hx]
  obtain ⟨R, h1, h2, h3, h4, h5, h6, h7, h8⟩ := Q.theorem_18_1_5_model hf hft h0' hgp
  exact ⟨R, h1, hπ ▸ h2, h3, h4, h5, h6, h7, h8⟩

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

end Polyfold
