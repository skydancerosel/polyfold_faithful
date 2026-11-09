import Polyfold.Chapter2.TameFaces

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.4,
**Proposition 2.5.16 (preprint 2.44)**, second sentence: the corner germs `F^σ_x` of a tame M-polyfold are germs of
tame sub-M-polyfolds of codimension `#σ`.

# Corner germs of tame M-polyfolds

## The text, paraphrased

(Proposition 2.5.16 (preprint 2.44)) In a tame M-polyfold every point `x` has exactly `d_X(x)` local faces (face
germs `𝓕_x`); for `σ ⊆ 𝓕_x`, the germ `F^σ_x = ⋂_{[F, x] ∈ σ} F` is the germ of a tame
sub-M-polyfold of codimension `#σ`, with `d_{F^σ}(x) = d_X(x) − #σ`.  (No proof in the text; the
exposition argues by induction on `#σ`.)

## What is formalized

* The corner `f_σ = ⋂_{i ∈ σ} f_i` as the model space `ℝ^{n − #σ} ⊕ W`: `cornerIdx`,
  `cornerRemoveL`, `cornerInsertL`, the sc-operators `cornerIncl σ T` (`ι_σ`), `cornerProj σ T`
  (`π_σ`) and `cornerKill T σ = ι_σ ∘ π_σ` (`P_σ`), and
  `degIndexWith_eq_quadrantDeg_cornerProj_add_card` (`d_C = d_{C'} ∘ π_σ + #σ` on `f_σ`).
* `Polyfold.corner_retraction`: for a tame retraction and `σ ⊆ I(o)`, the faces `F_i ∋ o`
  (`i ∈ σ`, pairwise distinct) and an sc-smooth retraction `r ∘ P_σ` near `o` onto
  `O ∩ V ∩ f_σ = O ∩ V ∩ ⋂_{i ∈ σ} F_i`.
* `Polyfold.corner_tameModel`: its image has the tame model `π_σ(…) ⊆ [0,∞)^{n − #σ} ⊕ W`, with
  `d_{C'}(π_σ y) + #σ = d_C(y)`.
* `Polyfold.MPolyfold.proposition_2_5_16_corner` (**Proposition 2.5.16 (preprint 2.44)**, second sentence).

## What the text leaves implicit, and the choices made

* "Face germs at `x`" are the faces `F_i`, `i ∈ I(φ(x))`, of the tame chart `φ : V → O` around `x`
  (Corollary 2.5.13 (preprint 2.41): there are `d_X(x)` of them), and `σ` is a set of indices `i ∈ I(φ(x))`; "the germ
  `F^σ_x` is the germ of `A`" is witnessed by `A = φ⁻¹(B ∩ ⋂_{i ∈ σ} F_i)` itself for an open
  `B ∋ φ(x)`.  "Codimension `#σ`" is the number of quadrant coordinates removed in the tame model
  of `A`, and `d_A + #σ = d_X` holds on all of `A`.
* Instead of the exposition's induction (identifying the germ of `F_1 ∩ F_2` with a face of `F_1`),
  all coordinates of `σ` are removed at once: Lemma 4.C for each `i ∈ σ` shows that `r` maps points
  of `f_σ ∩ C` near `φ(x)` into `f_σ`.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

variable {E : ScBanach}

/-! ### The corner `f_σ = ⋂_{i ∈ σ} f_i ≅ ℝ^{n − #σ} ⊕ W` -/

section CornerModel

variable {n : ℕ} (σ : Finset (Fin n))

/-- The `j`-th coordinate outside `σ`. -/
def cornerIdx (j : Fin σᶜ.card) : Fin n := (σᶜ.equivFin.symm j : Fin n)

lemma cornerIdx_not_mem (j : Fin σᶜ.card) : cornerIdx σ j ∉ σ :=
  Finset.mem_compl.1 (σᶜ.equivFin.symm j).2

lemma cornerIdx_injective : Injective (cornerIdx σ) := fun _ _ h =>
  σᶜ.equivFin.symm.injective (Subtype.ext h)

lemma exists_cornerIdx {l : Fin n} (hl : l ∉ σ) : ∃ j, cornerIdx σ j = l :=
  ⟨σᶜ.equivFin ⟨l, Finset.mem_compl.2 hl⟩, by simp [cornerIdx]⟩

/-- `a ↦ (a_l)_{l ∉ σ}`. -/
def cornerRemoveL : (Fin n → ℝ) →L[ℝ] (Fin σᶜ.card → ℝ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (cornerIdx σ j)

@[simp] lemma cornerRemoveL_apply (a : Fin n → ℝ) (j : Fin σᶜ.card) :
    cornerRemoveL σ a j = a (cornerIdx σ j) := rfl

open scoped Classical in
/-- `b ↦ a` with `a_l = 0` for `l ∈ σ` and `a_{cornerIdx j} = b_j`. -/
def cornerInsertL : (Fin σᶜ.card → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun l =>
    if h : l ∈ σᶜ then ContinuousLinearMap.proj (σᶜ.equivFin ⟨l, h⟩) else 0

lemma cornerInsertL_apply_mem (b : Fin σᶜ.card → ℝ) {l : Fin n} (hl : l ∈ σ) :
    cornerInsertL σ b l = 0 := by
  classical
  simp [cornerInsertL, Finset.mem_compl, hl]

lemma cornerInsertL_apply_idx (b : Fin σᶜ.card → ℝ) (j : Fin σᶜ.card) :
    cornerInsertL σ b (cornerIdx σ j) = b j := by
  classical
  have h : cornerIdx σ j ∈ σᶜ := (σᶜ.equivFin.symm j).2
  simp only [cornerInsertL, ContinuousLinearMap.pi_apply, dif_pos h,
    ContinuousLinearMap.proj_apply]
  congr 1
  apply σᶜ.equivFin.symm.injective
  simp [cornerIdx]

lemma cornerRemoveL_cornerInsertL (b : Fin σᶜ.card → ℝ) :
    cornerRemoveL σ (cornerInsertL σ b) = b :=
  funext fun j => cornerInsertL_apply_idx σ b j

lemma cornerInsertL_cornerRemoveL {a : Fin n → ℝ} (ha : ∀ l ∈ σ, a l = 0) :
    cornerInsertL σ (cornerRemoveL σ a) = a := by
  funext l
  by_cases hl : l ∈ σ
  · rw [cornerInsertL_apply_mem σ _ hl, ha l hl]
  · obtain ⟨j, rfl⟩ := exists_cornerIdx σ hl
    rw [cornerInsertL_apply_idx, cornerRemoveL_apply]

variable {W : ScBanach}

/-- `(b, w) ↦ (cornerInsertL b, w)`. -/
def cornerInsertModel (W : ScBanach) :
    ScOperator ((ScBanach.const (Fin σᶜ.card → ℝ)).prod W)
      ((ScBanach.const (Fin n → ℝ)).prod W) where
  lvl m := (cornerInsertL σ).prodMap (ContinuousLinearMap.id ℝ (W m))
  incl_comm _ _ := rfl

/-- `(a, w) ↦ (cornerRemoveL a, w)`. -/
def cornerRemoveModel (W : ScBanach) :
    ScOperator ((ScBanach.const (Fin n → ℝ)).prod W)
      ((ScBanach.const (Fin σᶜ.card → ℝ)).prod W) where
  lvl m := (cornerRemoveL σ).prodMap (ContinuousLinearMap.id ℝ (W m))
  incl_comm _ _ := rfl

variable (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))

/-- The inclusion `ι_σ : ℝ^{n − #σ} ⊕ W ≅ f_σ ⊆ E`. -/
def cornerIncl : ScOperator ((ScBanach.const (Fin σᶜ.card → ℝ)).prod W) E :=
  T.symm.toScOperator.comp (cornerInsertModel σ W)

/-- The projection `π_σ : E → ℝ^{n − #σ} ⊕ W`. -/
def cornerProj : ScOperator E ((ScBanach.const (Fin σᶜ.card → ℝ)).prod W) :=
  (cornerRemoveModel σ W).comp T.toScOperator

lemma cornerIncl_apply (z : ((ScBanach.const (Fin σᶜ.card → ℝ)).prod W) 0) :
    cornerIncl σ T 0 z = (T 0).symm (cornerInsertL σ z.1, z.2) := rfl

lemma cornerProj_apply (y : E 0) :
    cornerProj σ T 0 y = (cornerRemoveL σ (T 0 y).1, (T 0 y).2) := rfl

lemma coord_cornerIncl_mem (z : ((ScBanach.const (Fin σᶜ.card → ℝ)).prod W) 0) {l : Fin n}
    (hl : l ∈ σ) : (T 0 (cornerIncl σ T 0 z)).1 l = 0 := by
  rw [cornerIncl_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact cornerInsertL_apply_mem σ z.1 hl

lemma coord_cornerIncl_idx (z : ((ScBanach.const (Fin σᶜ.card → ℝ)).prod W) 0)
    (j : Fin σᶜ.card) : (T 0 (cornerIncl σ T 0 z)).1 (cornerIdx σ j) = z.1 j := by
  rw [cornerIncl_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact cornerInsertL_apply_idx σ z.1 j

lemma cornerProj_cornerIncl (z : ((ScBanach.const (Fin σᶜ.card → ℝ)).prod W) 0) :
    cornerProj σ T 0 (cornerIncl σ T 0 z) = z := by
  rw [cornerProj_apply]
  refine Prod.ext (funext fun j => ?_) ?_
  · exact coord_cornerIncl_idx σ T z j
  · change (T 0 ((T 0).symm (cornerInsertL σ z.1, z.2))).2 = z.2
    rw [ContinuousLinearEquiv.apply_symm_apply]

lemma cornerIncl_cornerProj {y : E 0} (hy : ∀ l ∈ σ, (T 0 y).1 l = 0) :
    cornerIncl σ T 0 (cornerProj σ T 0 y) = y := by
  apply (T 0).injective
  rw [cornerIncl_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact Prod.ext (cornerInsertL_cornerRemoveL σ hy) rfl

variable {C : Set (E 0)}

lemma cornerIncl_mem (hT : C = T 0 ⁻¹' quadrant n W 0)
    {z : ((ScBanach.const (Fin σᶜ.card → ℝ)).prod W) 0} (hz : z ∈ quadrant σᶜ.card W 0) :
    cornerIncl σ T 0 z ∈ C := by
  rw [hT]; intro l
  change 0 ≤ (T 0 (cornerIncl σ T 0 z)).1 l
  by_cases hl : l ∈ σ
  · rw [coord_cornerIncl_mem σ T z hl]
  · obtain ⟨j, rfl⟩ := exists_cornerIdx σ hl
    rw [coord_cornerIncl_idx]; exact hz j

lemma cornerProj_mem (hT : C = T 0 ⁻¹' quadrant n W 0) {y : E 0} (hy : y ∈ C) :
    cornerProj σ T 0 y ∈ quadrant σᶜ.card W 0 := fun j => coord_nonneg hT hy (cornerIdx σ j)

/-- On `f_σ`, `d_C(y) = d_{C'}(π_σ y) + #σ`. -/
lemma degIndexWith_eq_quadrantDeg_cornerProj_add_card {y : E 0}
    (hy : ∀ l ∈ σ, (T 0 y).1 l = 0) :
    degIndexWith T y = quadrantDeg (cornerProj σ T 0 y) + σ.card := by
  classical
  unfold degIndexWith quadrantDeg
  have hsplit : (Finset.univ.filter fun l => (T 0 y).1 l = 0) =
      σ ∪ (Finset.univ.filter fun j => (T 0 y).1 (cornerIdx σ j) = 0).map
        ⟨cornerIdx σ, cornerIdx_injective σ⟩ := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hl
      by_cases hlσ : l ∈ σ
      · exact Or.inl hlσ
      · obtain ⟨j, rfl⟩ := exists_cornerIdx σ hlσ
        exact Or.inr ⟨j, hl, rfl⟩
    · rintro (hlσ | ⟨j, hj, rfl⟩)
      · exact hy l hlσ
      · exact hj
  have hdisj : Disjoint σ ((Finset.univ.filter fun j => (T 0 y).1 (cornerIdx σ j) = 0).map
      ⟨cornerIdx σ, cornerIdx_injective σ⟩) := by
    rw [Finset.disjoint_left]
    intro l hl hl'
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hl'
    exact cornerIdx_not_mem σ j hl
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_map, add_comm]
  rfl

end CornerModel

/-! ### The retraction onto a corner and its tame model -/

section CornerRetract

variable {n : ℕ} {W : ScBanach} {C : Set (E 0)} {R : ScRetraction E C}
  {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (σ : Finset (Fin n))

variable (T) in
/-- The sc-projection `P_σ = ι_σ ∘ π_σ` of `E` onto `f_σ` (all coordinates in `σ` set to `0`). -/
def cornerKill : ScOperator E E := (cornerIncl σ T).comp (cornerProj σ T)

lemma cornerKill_apply (y : E 0) : cornerKill T σ 0 y = cornerIncl σ T 0 (cornerProj σ T 0 y) :=
  rfl

lemma cornerKill_eq_self {y : E 0} (hy : ∀ l ∈ σ, (T 0 y).1 l = 0) : cornerKill T σ 0 y = y :=
  cornerIncl_cornerProj σ T hy

lemma cornerKill_coord_mem (y : E 0) {l : Fin n} (hl : l ∈ σ) :
    (T 0 (cornerKill T σ 0 y)).1 l = 0 := coord_cornerIncl_mem σ T _ hl

lemma cornerKill_mem (hT : C = T 0 ⁻¹' quadrant n W 0) {y : E 0} (hy : y ∈ C) :
    cornerKill T σ 0 y ∈ C := cornerIncl_mem σ T hT (cornerProj_mem σ T hT hy)

/-- **The retraction onto a corner** (the germs `F^σ_x` of Proposition 2.5.16 (preprint 2.44)): let `r` be tame and
`o ∈ O` with `σ ⊆ I(o)`.  There are the faces `F_i ∋ o` of `O` (`i ∈ σ`, `F_i ⊆ f_i`), an open
`V ∋ o`, and an sc-smooth retraction `s = r ∘ P_σ` (on `V ∩ C`) onto
`O ∩ V ∩ ⋂_{i ∈ σ} F_i = O ∩ V ∩ f_σ`.  The proof uses Lemma 4.C for every `i ∈ σ`: `r` maps points
of `f_i` near `o` into `f_i`. -/
theorem corner_retraction (hT : C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T) {o : E 0}
    (ho : o ∈ R.retract) (hσ : ∀ i ∈ σ, (T 0 o).1 i = 0) :
    ∃ F : σ → Set (E 0), (∀ i, R.IsRetractFace (F i) ∧ o ∈ F i ∧ F i ⊆ coordHyper T i) ∧
      Injective F ∧
      ∃ V : Set (E 0), IsOpen V ∧ o ∈ V ∧ ∃ S : ScRetraction E C, S.U ⊆ R.U ∧
        EqOn S (R ∘ cornerKill T σ 0) S.U ∧
        S.retract = R.retract ∩ V ∩ {z | ∀ i ∈ σ, (T 0 z).1 i = 0} ∧
        S.retract = R.retract ∩ V ∩ ⋂ i, F i := by
  classical
  -- the local faces `F_i`
  have hF : ∀ i : σ, ∃ F : Set (E 0), (R.IsRetractFace F ∧ o ∈ F ∧ F ⊆ coordHyper T i) ∧
      (∃ p ∈ F, degIndexWith T p = 1) ∧
      ∀ᶠ z in 𝓝 o, z ∈ C → (T 0 z).1 i = 0 → R z ∈ F := by
    intro i
    obtain ⟨ε, hε, p, hpS, hpi, hBU, -, -, -, hcl⟩ := local_face_structure hT hR ho (hσ i i.2)
    have hoF : o ∈ closure (connectedComponentIn R.faceStratum p) := by
      have := hcl o ⟨Metric.mem_ball_self hε, R.retract_subset_C ho⟩ (hσ i i.2)
      rwa [R.apply_eq_self_of_mem_retract ho] at this
    refine ⟨closure (connectedComponentIn R.faceStratum p) ∩ R.retract,
      ⟨⟨p, hpS, rfl⟩, ⟨hoF, ho⟩, fun z hz => (isClosed_coordHyper T i).closure_subset_iff.2
        (connectedComponentIn_faceStratum_subset hT hpi) hz.1⟩,
      ⟨p, ⟨subset_closure (mem_connectedComponentIn hpS), hpS.1⟩,
        faceStratum_degIndexWith hT hpS⟩, ?_⟩
    exact Filter.mem_of_superset (Metric.ball_mem_nhds o hε) fun z hz hzC hzi =>
      ⟨hcl z ⟨hz, hzC⟩ hzi, R.apply_mem_retract (hBU ⟨hz, hzC⟩)⟩
  choose F hFp hFone hFev using hF
  have hFinj : Injective F := by
    intro i j hij
    obtain ⟨p, hpF, hp1⟩ := hFone i
    have hpi : (T 0 p).1 i = 0 := (hFp i).2.2 hpF
    have hpj : (T 0 p).1 j = 0 := (hFp j).2.2 (hij ▸ hpF)
    have h1 := zeroSet_eq_singleton hp1 hpi
    have h2 := zeroSet_eq_singleton hp1 hpj
    exact Subtype.ext (Finset.singleton_injective (h1.symm.trans h2))
  have hevU : ∀ᶠ z in 𝓝 o, z ∈ C → z ∈ R.U := by
    obtain ⟨V₀, hV₀, hUV⟩ := R.relOpen.relOpen
    have hoV : o ∈ V₀ := (hUV ▸ R.retract_subset ho).1
    exact Filter.mem_of_superset (hV₀.mem_nhds hoV) fun z hz hzC => by rw [hUV]; exact ⟨hz, hzC⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (hevU.and (Filter.eventually_all.2 hFev))
  set B := Metric.ball o δ with hB
  obtain ⟨Ws, hWs, hWseq⟩ := continuousOn_iff'.1 R.isSc1.isSc0.continuousOn_base B
    Metric.isOpen_ball
  set P := cornerKill T σ 0 with hP
  have hPc : Continuous P := (cornerKill T σ 0).continuous
  set V := B ∩ P ⁻¹' (B ∩ Ws) with hVdef
  have hV : IsOpen V := Metric.isOpen_ball.inter ((Metric.isOpen_ball.inter hWs).preimage hPc)
  have hWs_of : ∀ y ∈ R.U, R y ∈ B → y ∈ Ws := fun y hy hRy => by
    have : y ∈ R ⁻¹' B ∩ R.U := ⟨hRy, hy⟩
    rw [hWseq] at this; exact this.1
  have hoV : o ∈ V := by
    refine ⟨Metric.mem_ball_self hδ, ?_⟩
    rw [mem_preimage, hP, cornerKill_eq_self σ hσ]
    refine ⟨Metric.mem_ball_self hδ, hWs_of o (R.retract_subset ho) ?_⟩
    rw [R.apply_eq_self_of_mem_retract ho]; exact Metric.mem_ball_self hδ
  set U' := V ∩ C with hU'
  have hU'rel : IsRelOpenInQuadrant E C U' := ⟨R.relOpen.isPartialQuadrant, V, hV, rfl⟩
  have hPzC : ∀ z ∈ U', P z ∈ C := fun z hz => cornerKill_mem σ hT hz.2
  have hPzU : ∀ z ∈ U', P z ∈ R.U := fun z hz => (hball hz.1.2.1).1 (hPzC z hz)
  have hRret : ∀ z ∈ U', R (P z) ∈ R.retract := fun z hz => R.apply_mem_retract (hPzU z hz)
  have hRσ : ∀ z ∈ U', ∀ i ∈ σ, (T 0 (R (P z))).1 i = 0 := fun z hz i hi =>
    (hFp ⟨i, hi⟩).2.2 ((hball hz.1.2.1).2 ⟨i, hi⟩ (hPzC z hz) (cornerKill_coord_mem σ z hi))
  have hRB : ∀ z ∈ U', R (P z) ∈ B := fun z hz => by
    have : P z ∈ Ws ∩ R.U := ⟨hz.1.2.2, hPzU z hz⟩
    rw [← hWseq] at this; exact this.1
  have hRU' : ∀ z ∈ U', R (P z) ∈ U' := fun z hz => by
    refine ⟨⟨hRB z hz, ?_⟩, R.retract_subset_C (hRret z hz)⟩
    rw [mem_preimage, cornerKill_eq_self σ (hRσ z hz)]
    refine ⟨hRB z hz, hWs_of _ (R.retract_subset (hRret z hz)) ?_⟩
    rw [R.apply_eq_self_of_mem_retract (hRret z hz)]; exact hRB z hz
  let S : ScRetraction E C :=
    { U := U'
      toFun := R ∘ P
      relOpen := hU'rel
      mapsTo := hRU'
      isScSmooth := IsScSmooth.comp hU'rel.isScDomain R.isScDomain R.isScSmooth
        ((cornerKill T σ).isScSmooth hU'rel.isScDomain) hPzU
      idem := fun z hz => by
        change R (P (R (P z))) = R (P z)
        rw [cornerKill_eq_self σ (hRσ z hz), R.apply_eq_self_of_mem_retract (hRret z hz)] }
  have hSret : S.retract = R.retract ∩ V ∩ {z | ∀ i ∈ σ, (T 0 z).1 i = 0} := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨⟨hRret z hz, (hRU' z hz).1⟩, hRσ z hz⟩
    · rintro y ⟨⟨hyO, hyV⟩, hyσ⟩
      refine ⟨y, ⟨hyV, R.retract_subset_C hyO⟩, ?_⟩
      change R (P y) = y
      rw [cornerKill_eq_self σ hyσ, R.apply_eq_self_of_mem_retract hyO]
  refine ⟨F, hFp, hFinj, V, hV, hoV, S, fun z hz => (hball hz.1.1).1 hz.2, fun _ _ => rfl, hSret,
    ?_⟩
  rw [hSret]
  ext y
  simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter]
  constructor
  · rintro ⟨⟨hyO, hyV⟩, hyσ⟩
    refine ⟨⟨hyO, hyV⟩, fun i => ?_⟩
    have := (hball hyV.1).2 i (R.retract_subset_C hyO) (hyσ i i.2)
    rwa [R.apply_eq_self_of_mem_retract hyO] at this
  · rintro ⟨⟨hyO, hyV⟩, hyF⟩
    exact ⟨⟨hyO, hyV⟩, fun i hi => (hFp ⟨i, hi⟩).2.2 (hyF ⟨i, hi⟩)⟩

/-- **The tame model of a corner**: for an sc-smooth retraction `s = r ∘ P_σ` (on `S.U ⊆ U`) onto
a subset of `O ∩ f_σ`, the map `r' = π_σ ∘ r ∘ ι_σ` is a tame sc-smooth retraction of
`C' = [0,∞)^{n − #σ} ⊕ W` onto `π_σ(s(U_s))`, and `d_{C'}(π_σ y) + #σ = d_C(y)` there (the proof
of `proposition_2_5_15_tameModel` with `σ` in place of `{i}`). -/
theorem corner_tameModel (hT : C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T)
    (S : ScRetraction E C) (hSσ : ∀ y ∈ S.retract, ∀ l ∈ σ, (T 0 y).1 l = 0)
    (hSO : S.retract ⊆ R.retract) (hSU : S.U ⊆ R.U) (hSeq : EqOn S (R ∘ cornerKill T σ 0) S.U) :
    ∃ R' : ScRetraction ((ScBanach.const (Fin σᶜ.card → ℝ)).prod W) (quadrant σᶜ.card W 0),
      R'.IsTameWith (ScIso.refl _) ∧ R'.retract = cornerProj σ T 0 '' S.retract ∧
      ∀ y ∈ S.retract, degIndex _ (quadrant σᶜ.card W 0) (cornerProj σ T 0 y) + σ.card =
        degIndex E C y := by
  classical
  set F := S.retract with hFdef
  have hFS : F ⊆ S.U := S.retract_subset
  obtain ⟨W₀, hW₀, hSW⟩ := S.relOpen.relOpen
  set E' := (ScBanach.const (Fin σᶜ.card → ℝ)).prod W with hE'
  set ι := cornerIncl σ T with hι
  set π := cornerProj σ T with hπ
  have hT' : quadrant σᶜ.card W 0 = (ScIso.refl E') 0 ⁻¹' quadrant σᶜ.card W 0 := by ext; rfl
  have hιC : ∀ z ∈ quadrant σᶜ.card W 0, ι 0 z ∈ C := fun z hz => cornerIncl_mem σ T hT hz
  have hPι : ∀ z, cornerKill T σ 0 (ι 0 z) = ι 0 z := fun z => by
    rw [cornerKill_apply, cornerProj_cornerIncl]
  set U' : Set (E' 0) := ι 0 ⁻¹' W₀ ∩ quadrant σᶜ.card W 0 with hU'
  have hιU : ∀ z ∈ U', ι 0 z ∈ S.U := fun z hz => by rw [hSW]; exact ⟨hz.1, hιC z hz.2⟩
  have hmapsR : MapsTo (ι 0) U' R.U := fun z hz => hSU (hιU z hz)
  have hRιF : ∀ z ∈ U', R (ι 0 z) ∈ F := fun z hz => by
    have := S.apply_mem_retract (hιU z hz)
    rwa [hSeq (hιU z hz), Function.comp_apply, hPι] at this
  have hιπ : ∀ y ∈ F, ι 0 (π 0 y) = y := fun y hy => cornerIncl_cornerProj σ T (hSσ y hy)
  have hFU' : ∀ y ∈ F, π 0 y ∈ U' := fun y hy => by
    have hyS := hFS hy
    rw [hSW] at hyS
    refine ⟨?_, cornerProj_mem σ T hT hyS.2⟩
    rw [mem_preimage, hιπ y hy]; exact hyS.1
  have hU'rel : IsRelOpenInQuadrant E' (quadrant σᶜ.card W 0) U' :=
    ⟨⟨σᶜ.card, W, ScIso.refl E', hT'⟩, ι 0 ⁻¹' W₀, hW₀.preimage (ι 0).continuous, rfl⟩
  have hsm : IsScSmooth U' (π 0 ∘ (R ∘ ι 0)) :=
    IsScSmooth.comp hU'rel.isScDomain (isScDomain_univ _) (π.isScSmooth (isScDomain_univ _))
      (IsScSmooth.comp hU'rel.isScDomain R.isScDomain R.isScSmooth
        (ι.isScSmooth hU'rel.isScDomain) hmapsR) (mapsTo_univ _ _)
  let R' : ScRetraction E' (quadrant σᶜ.card W 0) :=
    { U := U'
      toFun := fun z => π 0 (R (ι 0 z))
      relOpen := hU'rel
      mapsTo := fun z hz => hFU' _ (hRιF z hz)
      isScSmooth := hsm
      idem := fun z hz => by
        change π 0 (R (ι 0 (π 0 (R (ι 0 z))))) = π 0 (R (ι 0 z))
        rw [hιπ _ (hRιF z hz), R.apply_eq_self_of_mem_retract (hSO (hRιF z hz))] }
  have hR'ret : R'.retract = π 0 '' F := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩; exact ⟨_, hRιF z hz, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨π 0 y, hFU' y hy, ?_⟩
      change π 0 (R (ι 0 (π 0 y))) = π 0 y
      rw [hιπ y hy, R.apply_eq_self_of_mem_retract (hSO hy)]
  have hιret : ∀ w ∈ R'.retract, ι 0 w ∈ F := by
    rw [hR'ret]; rintro _ ⟨y, hy, rfl⟩; rw [hιπ y hy]; exact hy
  refine ⟨R', ⟨fun z hz => ?_, fun x hx hs => ?_⟩, hR'ret, fun y hy => ?_⟩
  · -- tameness (1)
    have hzq : z ∈ quadrant σᶜ.card W 0 := hz.2
    have hz'q : R' z ∈ quadrant σᶜ.card W 0 := (R'.mapsTo hz).2
    rw [degIndex_eq (ScIso.refl E') hT' hz'q, degIndex_eq (ScIso.refl E') hT' hzq]
    change quadrantDeg (π 0 (R (ι 0 z))) = quadrantDeg z
    have h1 := degIndexWith_eq_quadrantDeg_cornerProj_add_card σ T (hSσ _ (hRιF z hz))
    have h2 := degIndexWith_eq_quadrantDeg_cornerProj_add_card σ T
      (fun l hl => coord_cornerIncl_mem σ T z hl)
    rw [cornerProj_cornerIncl] at h2
    have h3 := hR.degIndex_apply _ (hmapsR hz)
    rw [degIndex_eq T hT (R.retract_subset_C (hSO (hRιF z hz))),
      degIndex_eq T hT (hιC z hzq)] at h3
    exact Nat.add_right_cancel (h1.symm.trans (h3.trans h2))
  · -- tameness (2)
    set D := scDeriv R'.U R' x with hD
    have hx1U : x ∈ E'.lvlSet U' 1 := R'.lvlSet_retract_subset 1 hx
    have hy : ι 1 x ∈ E.lvlSet R.retract 1 := by
      rw [ScBanach.mem_lvlSet, ι.toBase_comm]; exact hSO (hιret _ hx)
    have hys : ι 1 x ∈ E.smoothLvl 1 := ι.mapsTo_smoothLvl 1 hs
    have hyU : ι 1 x ∈ E.lvlSet R.U 1 := R.lvlSet_retract_subset 1 hy
    have hDv : ∀ v, D v = π 0 (scDeriv R.U R (ι 1 x) (ι 0 v)) := fun v => by
      have c1 := scDeriv_comp_apply_of_isScDomain hU'rel.isScDomain R.isScDomain
        (ι.isScSmooth hU'rel.isScDomain).isSc1
        (IsScSmooth.comp R.isScDomain (isScDomain_univ _) (π.isScSmooth (isScDomain_univ _))
          R.isScSmooth (mapsTo_univ _ _)).isSc1 hmapsR hx1U v
      have c2 := scDeriv_comp_apply_of_isScDomain R.isScDomain (isScDomain_univ _) R.isSc1
        (π.isScSmooth (isScDomain_univ _)).isSc1 (mapsTo_univ _ _) hyU (ι 0 v)
      rw [ι.scDeriv_eq hU'rel.isScDomain hx1U, ι.levelMap_eq] at c1
      rw [π.scDeriv_eq (isScDomain_univ _) (mem_univ _)] at c2
      change scDeriv U' ((π 0 ∘ R) ∘ ι 0) x v = _
      rw [← c1, ← c2]
    refine ⟨_, R'.isScSplitting_range_scDeriv hx hs, ?_⟩
    rintro _ ⟨v, rfl⟩
    rw [mem_minimalSubspaceWith]
    intro j hj
    change (v - D v).1 j = 0
    have hj' : (T 0 (E.toBase 1 (ι 1 x))).1 (cornerIdx σ j) = 0 := by
      rw [ι.toBase_comm, hι, coord_cornerIncl_idx]; exact hj
    have key := coord_scDeriv_eq hT hR hy hys hj' (ι 0 v)
    rw [hι, coord_cornerIncl_idx] at key
    rw [Prod.fst_sub, Pi.sub_apply, hDv v, hπ, cornerProj_apply]
    change v.1 j -
      (T 0 (scDeriv R.U R (cornerIncl σ T 1 x) (cornerIncl σ T 0 v))).1 (cornerIdx σ j) = 0
    rw [key, sub_self]
  · -- `d_F = d_O − #σ`
    have hyC := R.retract_subset_C (hSO hy)
    rw [degIndex_eq (ScIso.refl E') hT' (cornerProj_mem σ T hT hyC), degIndex_eq T hT hyC,
      degIndexWith_eq_quadrantDeg_cornerProj_add_card σ T (hSσ y hy)]
    rfl

end CornerRetract

/-! ### Proposition 2.5.16 (preprint 2.44): the corner germs are tame sub-M-polyfolds -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **Proposition 2.5.16 (preprint 2.44)**, second sentence: let `X` be tame and `x ∈ X`.  In a tame chart
`φ : V → O` around `x` the faces of `O` through `φ(x)` are the `F_i`, `i ∈ I(φ(x))`
(Corollary 2.5.13 (preprint 2.41)); for every `σ ⊆ I(φ(x))` (a set of `#σ` distinct face germs at `x`) the germ at `x`
of `F^σ = ⋂_{i ∈ σ} φ⁻¹(F_i)` is the germ of a tame sub-M-polyfold `A` of `X` with
`d_A(y) + #σ = d_X(y)` for all `y ∈ A` (in particular `d_A(x) = d_X(x) − #σ`).  Here
`A = {y ∈ V | φ(y) ∈ B, φ(y) ∈ F_i ∀ i ∈ σ}` for an open `B ∋ φ(x)`.

*Proof.* Lemma 4.C for every `i ∈ σ` gives the retraction `r ∘ P_σ` onto `O ∩ B ∩ f_σ =
O ∩ B ∩ ⋂ F_i` near `φ(x)` (`corner_retraction`), whose image has the tame model
`(π_σ(O ∩ B ∩ f_σ), [0,∞)^{n − #σ} ⊕ W, ℝ^{n − #σ} ⊕ W)` (`corner_tameModel`); conclude as for
Theorem 2.5.17 (preprint 2.45) (`isSubMPolyfold_of_local`, `faceChart`).  The text gives no proof; the exposition
argues by induction on `#σ`, identifying the germ of `F_1 ∩ F_2` with a face of `F_1`. -/
theorem proposition_2_5_16_corner (hP : P.IsTame) (x : X) :
    ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧
      ∃ (R : ScRetraction φ.model.E φ.model.C) (n : ℕ) (W : ScBanach)
        (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
        R.retract = φ.model.O ∧ φ.model.C = T 0 ⁻¹' quadrant n W 0 ∧ R.IsTameWith T ∧
        ∀ σ : Finset (Fin n), σ ⊆ zeroSet T (φ x) →
          ∃ F : σ → Set (φ.model.E 0),
            (∀ i, R.IsRetractFace (F i) ∧ φ x ∈ F i ∧ F i ⊆ coordHyper T i) ∧ Injective F ∧
            ∃ B : Set (φ.model.E 0), IsOpen B ∧ φ x ∈ B ∧
              ∃ hA : P.IsSubMPolyfold {y | y ∈ φ.source ∧ φ y ∈ B ∧ ∀ i, φ y ∈ F i},
                haveI := P.paracompactSpace_subtype {y | y ∈ φ.source ∧ φ y ∈ B ∧ ∀ i, φ y ∈ F i}
                (subPolyfold hA).IsTame ∧
                  ∀ a : {y | y ∈ φ.source ∧ φ y ∈ B ∧ ∀ i, φ y ∈ F i},
                    (subPolyfold hA).degIndex a + σ.card = P.degIndex a := by
  classical
  obtain ⟨φ, hφ, hx, R, hRO, hRt⟩ := IsTame.exists_chart P hP x
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hR := hRt n W T hT
  refine ⟨φ, hφ, hx, R, n, W, T, hRO, hT, hR, fun σ hσ => ?_⟩
  have hoO : φ x ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model x hx
  obtain ⟨F, hFp, hFinj, V, hV, hoV, S, hSU, hSeq, hSret1, hSret2⟩ :=
    corner_retraction σ hT hR hoO fun i hi => (mem_zeroSet T).1 (hσ hi)
  refine ⟨F, hFp, hFinj, V, hV, hoV, ?_⟩
  set A := {y | y ∈ φ.source ∧ φ y ∈ V ∧ ∀ i, φ y ∈ F i} with hAdef
  have hSO : S.retract ⊆ R.retract := by rw [hSret1]; exact fun y hy => hy.1.1
  have hSσ : ∀ y ∈ S.retract, ∀ l ∈ σ, (T 0 y).1 l = 0 := by
    rw [hSret1]; exact fun y hy => hy.2
  have hSV : S.retract ⊆ V := by rw [hSret1]; exact fun y hy => hy.1.2
  have himg : φ '' (A ∩ φ.source) = S.retract := by
    rw [hSret2]
    ext z
    constructor
    · rintro ⟨y, ⟨⟨hyV, hyB, hyF⟩, -⟩, rfl⟩
      refine ⟨⟨?_, hyB⟩, mem_iInter.2 hyF⟩
      rw [hRO]; exact φ.mapsTo_model y hyV
    · rintro ⟨⟨hzO, hzB⟩, hzF⟩
      have hzO' : z ∈ φ.model.O := by rw [← hRO]; exact hzO
      refine ⟨φ.symm z, ⟨⟨φ.symm_mapsTo hzO', ?_, ?_⟩, φ.symm_mapsTo hzO'⟩,
        φ.apply_symm_apply hzO'⟩
      · rw [φ.apply_symm_apply hzO']; exact hzB
      · rw [φ.apply_symm_apply hzO']; exact mem_iInter.1 hzF
  have hsub : P.IsSubMPolyfold A := P.isSubMPolyfold_of_local fun a ha =>
    ⟨φ, hφ, ha.1, S, V, hV, ha.2.1, by rw [← hRO]; exact hSO, by rw [himg]⟩
  refine ⟨hsub, ?_⟩
  have : ParacompactSpace A := P.paracompactSpace_subtype A
  obtain ⟨R', hR'tame, hR'ret, hdeg⟩ := corner_tameModel σ hT hR S hSσ hSO hSU hSeq
  have hT' : quadrant σᶜ.card W 0 =
      (ScIso.refl ((ScBanach.const (Fin σᶜ.card → ℝ)).prod W)) 0 ⁻¹' quadrant σᶜ.card W 0 := by
    ext; rfl
  set V₁ := φ.source ∩ φ ⁻¹' V with hV₁def
  have hV₁ : IsOpen V₁ := φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source hV
  have hFV : φ '' (A ∩ V₁) = S.retract := by
    rw [← himg]
    congr 1
    ext y
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h.1.2.1⟩⟩
  set ι := cornerIncl σ T with hι
  set π := cornerProj σ T with hπ
  have hιπ : ∀ y ∈ φ '' (A ∩ V₁), ι 0 (π 0 y) = y := fun y hy => by
    rw [hFV] at hy; exact cornerIncl_cornerProj σ T (hSσ y hy)
  have hπι : ∀ z, π 0 (ι 0 z) = z := cornerProj_cornerIncl σ T
  have hR'O : R'.retract = π 0 '' (φ '' (A ∩ V₁)) := by rw [hR'ret, hFV]
  have hret : IsScRetract _ (quadrant σᶜ.card W 0) (π 0 '' (φ '' (A ∩ V₁))) := ⟨R', hR'O⟩
  suffices key : ∀ a : A, ∃ χ : MChart A, (subPolyfold hsub).IsChart χ ∧ a ∈ χ.source ∧
      IsTameRetract χ.model.E χ.model.C χ.model.O ∧
      (subPolyfold hsub).degIndex a + σ.card = P.degIndex a by
    refine ⟨isTame_of_forall_exists_chart _ fun a => ?_, fun a => (key a).choose_spec.2.2.2⟩
    obtain ⟨χ, h1, h2, h3, -⟩ := key a
    exact ⟨χ, h1, h2, h3⟩
  intro a
  set χ := faceChart a φ V₁ (quadrant σᶜ.card W 0) ι π hV₁ (fun _ h => h.1) hιπ hπι hret with hχ
  have hχQ : (subPolyfold hsub).IsChart χ :=
    isChart_subPolyfold_of_compatible hsub hφ (fun _ hy => hy.1) fun d b₀ =>
      faceChart_compatible_subChart hφ hV₁ (fun _ h => h.1) hιπ hπι hret d b₀
  have haχ : a ∈ χ.source := show (a : X) ∈ V₁ from ⟨a.2.1, a.2.2.1⟩
  refine ⟨χ, hχQ, haχ, ⟨R', hR'O, hR'tame.isTame hT'⟩, ?_⟩
  rw [(subPolyfold hsub).degIndex_eq_chartDegIndex_of_isTameWith hχQ R' hR'O hT' hR'tame haχ,
    P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR a.2.1]
  have haS : φ a ∈ S.retract := by
    rw [← hFV]; exact ⟨a, ⟨a.2, a.2.1, a.2.2.1⟩, rfl⟩
  exact hdeg _ haS

end MPolyfold

end Polyfold
