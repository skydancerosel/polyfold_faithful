import Polyfold.Chapter12.AuxNormEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 12,
§12.2, **Theorem 12.2.7** (extension of auxiliary norms), pp. 574–576.

# Extension of auxiliary norms from `W|∂X`

## The text, paraphrased

(Theorem 12.2.7) For a strong bundle `(P : W → X, μ)` over a tame ep-groupoid with paracompact
`|X|`, an auxiliary norm `N : W_{0,1}|∂X → [0, ∞)` (Definition 12.2.1 over `∂X`) extends to an
auxiliary norm `Ñ` on `W_{0,1}`.  (Proof) By the proof of Theorem 12.2.2 it suffices to extend
`N` near each `x ∈ ∂X`.  In a tame local model `K → O`, `O ⊆ C = [0, ∞)ⁿ ⊕ H`, with
`q(t, h) = (t, h) − min(t)·(1, …, 1, 0)` and `R(u, w) = (r(u), A(u)w)`, the map `r ∘ q` retracts a
neighbourhood of `x₀` onto `∂O` (tameness: `d_C(r(x)) = d_C(x)`), and
`N'((t,h), w) = N(rq(t,h), A(rq(t,h))w) + ‖w − A(rq(t,h))w‖_{F₁}` extends `N`.  Averaging over
`G_{x₀}` keeps the extension property, the transport extends it to the saturation, and a
partition of unity over `|X|` (with neighbourhoods of interior points whose closures avoid `∂X`)
gives `Ñ`.

## What is formalized

* `EpStrongBundle.IsAuxNormOn A N`: Definition 12.2.1 over a subset `A` of objects (the text's
  "auxiliary norm for `W|∂X`", `A = ∂X`); `IsAuxNorm.isAuxNormOn` (restriction).
* **`EpStrongBundle.theorem_12_2_7_hyp`**: the theorem with the local extension step of the
  proof as a hypothesis (`HasLocalExtensions X B N`: every `x ∈ ∂X` has an open neighbourhood
  `V` and a local auxiliary norm on `V` (`StrongBundle.IsLocalAuxNorm`) equal to `N` over
  `V ∩ ∂X`; no invariance, no saturation asked).  Everything else of the text's proof is
  proved: the average over `G_x` (it still extends `N`, since `N` is invariant), the transport
  to the saturation, the interior neighbourhoods inside `X ∖ ∂X`, and the gluing; tameness is
  not used there.
* Satisfiability of the added hypothesis: `hasLocalExtensions_of_isAuxNorm` (the restriction of an
  auxiliary norm of `X` has local extensions) and `theorem_12_2_7_hyp_witness` (for every strong
  bundle over an ep-groupoid with paracompact `|X|`, an `N` satisfying all hypotheses exists).

## The local step

The coordinate construction `N'` of the local step is in `AuxNormLocalExtension.lean`
(Part III wave 2): `EpStrongBundle.hasLocalExtensions_of_isTame` discharges the hypothesis of
`theorem_12_2_7_hyp` for tame `X`, and `EpStrongBundle.theorem_12_2_7` is the printed theorem.
The retraction `r ∘ q` is built in a tame chart of the base, and the formula for `N'` is
evaluated in any strong bundle chart of the atlas, so no "tame strong bundle chart" is needed.
-/

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

universe u v

/-! ### Monotonicity of local auxiliary norms -/

section Mono

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

lemma StrongBundle.IsLocalAuxNorm.mono {V V' : Set X} {M : B.One → ℝ}
    (h : B.IsLocalAuxNorm V M) (hV : V' ⊆ V) : B.IsLocalAuxNorm V' M :=
  ⟨h.continuousOn.mono fun _ hw => hV hw, fun y hy => h.seminorm y (hV hy),
    fun w y hy h1 h2 => h.tendsto w y (hV hy) h1 h2⟩

end Mono

/-! ### The boundary of the object space is saturated -/

section Boundary

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

namespace EpGroupoid

/-- `t(φ) ∈ ∂X ⟺ s(φ) ∈ ∂X` (`d_X(t φ) = d_𝐗(φ) = d_X(s φ)`). -/
theorem tgt_mem_boundary_iff (φ : Mor) :
    X.tgt φ ∈ X.PObj.boundary ↔ X.src φ ∈ X.PObj.boundary := by
  change 1 ≤ X.PObj.degIndex (X.tgt φ) ↔ 1 ≤ X.PObj.degIndex (X.src φ)
  rw [← X.degIndex_tgt φ, X.degIndex_src φ]

/-- `X ∖ ∂X` is open (Lemma 2.4.3). -/
theorem isOpen_compl_boundary : IsOpen X.PObj.boundaryᶜ := by
  have h : X.PObj.boundaryᶜ = {x | X.PObj.degIndex x < 1} := by
    ext x; simp [MPolyfold.boundary]
  rw [h]; exact X.PObj.isOpen_setOf_degIndex_lt 1

end EpGroupoid

end Boundary

/-! ### Theorem 12.2.7 -/

section Thm1227

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable (E : EpStrongBundle X B)

/-- **Definition 12.2.1 over a subset `A` of the objects** (Theorem 12.2.7's "auxiliary norm for
`W|∂X`", with `A = ∂X`): `N` is continuous on `W_{0,1}|A`, a complete norm on the fibres over `A`,
`h_k → 0_y` for `h_k ∈ W_{0,1}|A` with `P(h_k) → y ∈ A` and `N(h_k) → 0`, and invariant under the
morphisms starting in `A`. -/
structure IsAuxNormOn (A : Set Obj) (N : B.One → ℝ) : Prop where
  continuousOn : ContinuousOn N {w | P (B.oneVal w) ∈ A}
  fiber : ∀ y ∈ A, B.IsCompleteFiberNorm N y
  tendsto_zeroOne : ∀ (w : ℕ → B.One) (y : Obj), y ∈ A → (∀ k, P (B.oneVal (w k)) ∈ A) →
    Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 y) →
      Tendsto (fun k => N (w k)) atTop (𝓝 0) → Tendsto w atTop (𝓝 (B.zeroOne y))
  map_μ : ∀ (h k : B.One) (φ : Mor) (hk : P (B.oneVal k) = X.src φ), P (B.oneVal k) ∈ A →
    B.oneVal h = E.μ ⟨(φ, B.oneVal k), hk⟩ → N h = N k

variable {E}

/-- The restriction of an auxiliary norm is one over every subset. -/
theorem IsAuxNorm.isAuxNormOn {N : B.One → ℝ} (hN : E.IsAuxNorm N) (A : Set Obj) :
    E.IsAuxNormOn A N :=
  ⟨hN.isAuxNorm.continuous.continuousOn, fun y _ => hN.isAuxNorm.fiber y,
    fun w y _ _ h1 h2 => hN.isAuxNorm.tendsto_zeroOne w y h1 h2,
    fun h k φ hk _ hh => hN.map_μ h k φ hk hh⟩

variable (X B) in
/-- **The local extension step of the proof of Theorem 12.2.7** (the hypothesis of
`theorem_12_2_7_hyp`): every `x ∈ ∂X` has an open neighbourhood `V` and a local auxiliary norm
`M` on `V` (conditions (1)–(2) of Definition 12.2.1 over `V`, `StrongBundle.IsLocalAuxNorm`) with
`M = N` on `W_{0,1}|(V ∩ ∂X)`. -/
def HasLocalExtensions (N : B.One → ℝ) : Prop :=
  ∀ x ∈ X.PObj.boundary, ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧ ∃ M : B.One → ℝ,
    B.IsLocalAuxNorm V M ∧ ∀ w : B.One, P (B.oneVal w) ∈ V ∩ X.PObj.boundary → M w = N w

/-- **Theorem 12.2.7 with the local extension step as a hypothesis**, pp. 574–576: for a strong
bundle over an ep-groupoid with paracompact `|X|`, an auxiliary norm `N` for `W|∂X` which has
local extensions near every boundary point extends to an auxiliary norm `Ñ` of `W`.  The text's
proof with its local coordinate construction replaced by the hypothesis `HasLocalExtensions`;
the averaging, the transport to saturations and the gluing are proved, without tameness. -/
theorem theorem_12_2_7_hyp (h : X.HasParacompactOrbitSpace) {N : B.One → ℝ}
    (hN : E.IsAuxNormOn X.PObj.boundary N) (hloc : HasLocalExtensions X B N) :
    ∃ Ñ : B.One → ℝ, E.IsAuxNorm Ñ ∧
      ∀ w : B.One, P (B.oneVal w) ∈ X.PObj.boundary → Ñ w = N w := by
  classical
  have := B.paracompactSpace_pullback X.PMor X.src
  have : ParacompactSpace X.OrbitSpace := h
  have := X.theorem_7_3_1_metrizable h
  obtain ⟨N₀, hN₀⟩ := proposition_5_1_3_exists (B := B)
  have hdata : ∀ x : Obj, ∃ (R : X.NaturalRep x) (M : B.One → ℝ), B.IsLocalAuxNorm R.U M ∧
      (x ∈ X.PObj.boundary → ∀ w : B.One, P (B.oneVal w) ∈ R.U ∩ X.PObj.boundary → M w = N w) ∧
      (x ∉ X.PObj.boundary → R.U ⊆ X.PObj.boundaryᶜ) := by
    intro x
    by_cases hx : x ∈ X.PObj.boundary
    · obtain ⟨V, hVo, hxV, M, hM, hMN⟩ := hloc x hx
      obtain ⟨R, hRV⟩ := X.theorem_7_1_13 x hVo hxV
      exact ⟨R, M, hM.mono hRV, fun _ w hw => hMN w ⟨hRV hw.1, hw.2⟩, fun h' => absurd hx h'⟩
    · obtain ⟨R, hRV⟩ := X.theorem_7_1_13 x X.isOpen_compl_boundary hx
      exact ⟨R, N₀, hN₀.isLocalAuxNorm _, fun h' => absurd h' hx, fun _ => hRV⟩
  choose R M hM hMN hRint using hdata
  have hM' : ∀ x, B.IsLocalAuxNorm (R x).U (E.avgNorm (R x) (M x)) := fun x =>
    E.isLocalAuxNorm_avgNorm (R x) (hM x)
  have hinv : ∀ x g w, P (B.oneVal w) ∈ (R x).U →
      E.avgNorm (R x) (M x) (E.actOne ((R x).Γ g) w) = E.avgNorm (R x) (M x) w :=
    fun x g w hw => E.avgNorm_actOne (R x) (M x) g hw
  obtain ⟨β, hβ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun x => X.π '' X.satSet (R x).U)
    (fun x => by rw [EpGroupoid.image_π_satSet]; exact X.proposition_7_1_8 _ (R x).isOpen_U)
    fun z _ => by
      obtain ⟨y, rfl⟩ := X.surjective_π z
      exact mem_iUnion.2 ⟨y, y, EpGroupoid.subset_satSet _ (R y).mem_U, rfl⟩
  set T : Obj → B.One → ℝ := fun x => E.transNorm (R x) (E.avgNorm (R x) (M x)) with hT
  refine ⟨glueNorm β T, isAuxNorm_glueNorm (E := E) (U := fun x => X.satSet (R x).U)
    (fun x => EpGroupoid.isOpen_satSet (R x).isOpen_U)
    (fun x => EpGroupoid.isSaturated_satSet _) hβ
    (fun x => isLocalAuxNorm_transNorm (hM' x) (hinv x))
    (fun x h k ψ hk _ hh => transNorm_μ (hinv x) h k ψ hk hh), fun w hw => ?_⟩
  -- over `∂X` every nonzero term of the glued norm is `β_x · N`
  have key : ∀ x, β x (X.π (P (B.oneVal w))) * T x w = β x (X.π (P (B.oneVal w))) * N w := by
    intro x
    by_cases hβ0 : β x (X.π (P (B.oneVal w))) = 0
    · rw [hβ0, zero_mul, zero_mul]
    have hyU : P (B.oneVal w) ∈ X.satSet (R x).U :=
      EpGroupoid.mem_of_π_mem_image (EpGroupoid.isSaturated_satSet _) (hβ x (subset_tsupport _ hβ0))
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
    have hNv : N v = N w := hN.map_μ v w _ hφs.symm hw (E.oneVal_actOne_of_eq hφs.symm)
    have hterm : ∀ g, M x (E.actOne ((R x).Γ g) v) = N w := fun g => by
      have hs := (R x).src_Γ g _ hvU
      have hgb : P (B.oneVal (E.actOne ((R x).Γ g) v)) ∈ X.PObj.boundary := by
        rw [E.P_actOne hs]; exact (X.tgt_mem_boundary_iff _).2 (hs.symm ▸ hvb)
      rw [hMN x hxb _ ⟨E.actOne_Γ_mem (R x) g hvU, hgb⟩,
        hN.map_μ _ v _ hs.symm hvb (E.oneVal_actOne_of_eq hs.symm), hNv]
    have := Fintype.ofFinite (X.Isotropy x)
    rw [avgNorm, finsum_congr hterm, finsum_eq_sum_of_fintype, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      inv_mul_cancel_left₀ (card_isotropy_pos X (x := x)).ne']
  rw [glueNorm, finsum_congr key, ← finsum_mul, β.sum_eq_one (mem_univ _), one_mul]

/-- **The hypothesis of `theorem_12_2_7_hyp` holds for restrictions**: the restriction to `∂X`
of an auxiliary norm of `W` has local extensions (the norm itself). -/
theorem hasLocalExtensions_of_isAuxNorm {N : B.One → ℝ} (hN : E.IsAuxNorm N) :
    HasLocalExtensions X B N := fun _ _ =>
  ⟨univ, isOpen_univ, mem_univ _, N, hN.isAuxNorm.isLocalAuxNorm univ, fun _ _ => rfl⟩

/-- **Satisfiability of the hypotheses of `theorem_12_2_7_hyp`**: over every ep-groupoid with
paracompact `|X|` there is an auxiliary norm `N` for `W|∂X` with local extensions (the restriction
of one from Theorem 12.2.2). -/
theorem theorem_12_2_7_hyp_witness (h : X.HasParacompactOrbitSpace) :
    ∃ N : B.One → ℝ, E.IsAuxNormOn X.PObj.boundary N ∧ HasLocalExtensions X B N := by
  obtain ⟨N, hN⟩ := E.theorem_12_2_2 h
  exact ⟨N, hN.isAuxNormOn _, hasLocalExtensions_of_isAuxNorm hN⟩

end EpStrongBundle

end Thm1227

end Polyfold
