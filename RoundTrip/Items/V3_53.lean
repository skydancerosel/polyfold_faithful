import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_53

open Set Filter Topology Function

noncomputable section

namespace RoundTrip.V3_53
open Polyfold

/-- The project's statement: `lemma_3_7_3` (abstract form, for a family of sc-operators on a compact
parameter set).  No universe parameters. -/
def A : Prop := type_of% @Polyfold.lemma_3_7_3

theorem A_holds : A := @Polyfold.lemma_3_7_3

/-! ### Glue: the concrete family `L(b) = P_Y ∘ Df(b)|_X` as sc-operators `X → Y`
(as in `RoundTrip.V3_52`, now on every level) -/

/-- A continuous linear lift `S → E_k` of a finite-dimensional smooth subspace `S ⊆ E_∞`. -/
lemma exists_lift (E : ScBanach) (S : Submodule ℝ (E.lvl 0)) [FiniteDimensional ℝ S]
    (hS : S ≤ E.smooth) (k : ℕ) : ∃ ℓ : S →L[ℝ] E.lvl k, ∀ s, E.toBase k (ℓ s) = s := by
  let τ : E.levelSub S k →ₗ[ℝ] S :=
    { toFun := fun x => ⟨E.toBase k x, x.2⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun a x => Subtype.ext (map_smul _ _ _) }
  have hbij : Function.Bijective τ := by
    refine ⟨fun x y hxy => Subtype.ext (E.toBase_injective k (congrArg Subtype.val hxy)),
      fun s => ?_⟩
    obtain ⟨y, hy⟩ := (E.mem_smooth_iff).1 (hS s.2) k
    exact ⟨⟨y, show E.toBase k y ∈ S by rw [hy]; exact s.2⟩, Subtype.ext hy⟩
  let e := LinearEquiv.ofBijective τ hbij
  let ℓl : S →ₗ[ℝ] E.lvl k := (E.levelSub S k).subtype ∘ₗ (e.symm : S →ₗ[ℝ] E.levelSub S k)
  refine ⟨LinearMap.toContinuousLinearMap ℓl, fun s => ?_⟩
  have := congrArg Subtype.val (e.apply_symm_apply s)
  exact this

section Family

variable {E F : ScBanach} {U : Set (E.lvl 0)} {f : E.lvl 0 → F.lvl 0}
  {Bs X : Submodule ℝ (E.lvl 0)} {Ac Y : Submodule ℝ (F.lvl 0)}

open scoped Classical in
/-- The family `L(b) = P_Y ∘ Df(b)|_X : X → Y` (zero where `b ∉ U`). -/
def famL (hf : IsSc1 U f) (hBs : Bs ≤ E.smooth) (hXsc : E.IsScSubspace X)
    (hYA : F.IsScSplitting Y Ac) (ℓ1 : Bs →L[ℝ] E.lvl 1) (hℓ1 : ∀ s, E.toBase 1 (ℓ1 s) = s)
    (b : Bs) : ScOperator (E.ofSubspace hXsc) hYA.left :=
  if hb : (b : E.lvl 0) ∈ U then
    hYA.projOp.comp
      (((hf.isSc1With_scDeriv.scOperator_deriv (x := ℓ1 b)
        (show E.toBase 1 (ℓ1 b) ∈ U by rw [hℓ1]; exact hb)
        (show E.toBase 1 (ℓ1 b) ∈ E.smooth by rw [hℓ1]; exact hBs b.2)).toScOperator).comp
        hXsc.inclOp)
  else ScOperator.zeroOp _ _

/-- The level-`m` map of `L(b)`: `h ↦ P_Y Df(b)h` with the level operator `Df(b) : E_m → F_m`. -/
lemma famL_lvl (hf : IsSc1 U f) (hBs : Bs ≤ E.smooth) (hXsc : E.IsScSubspace X)
    (hYA : F.IsScSplitting Y Ac) (ℓ1 : Bs →L[ℝ] E.lvl 1) (hℓ1 : ∀ s, E.toBase 1 (ℓ1 s) = s)
    {m : ℕ} (ℓm : Bs →L[ℝ] E.lvl (m + 1)) (hℓm : ∀ s, E.toBase (m + 1) (ℓm s) = s)
    {b : Bs} (hb : (b : E.lvl 0) ∈ U) (h : (E.ofSubspace hXsc).lvl m) :
    famL hf hBs hXsc hYA ℓ1 hℓ1 b m h =
      hYA.proj m (levelDeriv (scDeriv U f) m (ℓm b) (hXsc.inclOp m h)) := by
  have hx : ℓm b ∈ E.lvlSet U (m + 1) := show E.toBase (m + 1) (ℓm b) ∈ U by rw [hℓm]; exact hb
  have hsh : E.shift.toBase m (ℓm b) = ℓ1 b :=
    E.toBase_injective 1 (by rw [← E.shift_toBase, hℓm, hℓ1])
  rw [famL, dif_pos hb, ScOperator.comp_apply, ScOperator.comp_apply]
  show hYA.proj m _ = hYA.proj m _
  congr 1
  apply F.toBase_injective m
  rw [ScOperator.toBase_comm, IsScOperator.toScOperator_zero,
    hf.isSc1With_scDeriv.toBase_levelDeriv hx, hsh]

/-- Joint continuity of `(b, h) ↦ L(b)h` on level `m` over a parameter set inside `U`. -/
lemma famL_continuousOn (hf : IsSc1 U f) (hBs : Bs ≤ E.smooth) (hXsc : E.IsScSubspace X)
    (hYA : F.IsScSplitting Y Ac) (ℓ1 : Bs →L[ℝ] E.lvl 1) (hℓ1 : ∀ s, E.toBase 1 (ℓ1 s) = s)
    {m : ℕ} (ℓm : Bs →L[ℝ] E.lvl (m + 1)) (hℓm : ∀ s, E.toBase (m + 1) (ℓm s) = s)
    {K : Set Bs} (hKU : ∀ b ∈ K, (b : E.lvl 0) ∈ U) :
    ContinuousOn (fun p : Bs × (E.ofSubspace hXsc).lvl m =>
      famL hf hBs hXsc hYA ℓ1 hℓ1 p.1 m p.2) (K ×ˢ univ) := by
  have h1 : ContinuousOn (fun p : Bs × (E.ofSubspace hXsc).lvl m =>
      hYA.proj m (levelDeriv (scDeriv U f) m (ℓm p.1) (hXsc.inclOp m p.2))) (K ×ˢ univ) := by
    refine (hYA.proj m).continuous.comp_continuousOn
      ((hf.isSc1With_scDeriv.continuousOn_levelDeriv m).comp
        (f := fun p : Bs × (E.ofSubspace hXsc).lvl m => (ℓm p.1, hXsc.inclOp m p.2))
        ((ℓm.continuous.comp continuous_fst).prodMk
          ((hXsc.inclOp m).continuous.comp continuous_snd)).continuousOn ?_)
    intro p hp
    exact ⟨show E.toBase (m + 1) (ℓm p.1) ∈ U by rw [hℓm]; exact hKU _ hp.1, mem_univ _⟩
  exact h1.congr fun p hp => famL_lvl hf hBs hXsc hYA ℓ1 hℓ1 ℓm hℓm (hKU _ hp.1) p.2

/-- **`FamilyCompactness` on level `m` from the blind compactness property** (`CompactnessProp`,
with its radius `r`), over any parameter set `K ⊆ {b ∈ B ∩ U, |b| < r}`. -/
lemma famL_compactness (hf : IsSc1 U f) (hBs : Bs ≤ E.smooth) (hXsc : E.IsScSubspace X)
    (hYA : F.IsScSplitting Y Ac) (ℓ1 : Bs →L[ℝ] E.lvl 1) (hℓ1 : ∀ s, E.toBase 1 (ℓ1 s) = s)
    {m : ℕ} (ℓm : Bs →L[ℝ] E.lvl (m + 1)) (hℓm : ∀ s, E.toBase (m + 1) (ℓm s) = s)
    (ℓA : Ac →L[ℝ] F.lvl (m + 1)) (hℓA : ∀ s, F.toBase (m + 1) (ℓA s) = s) {r : ℝ}
    (hcpt : ∀ (b : ℕ → E.lvl (m + 1)) (b₀ : E.lvl (m + 1)) (η : ℕ → E.lvl m)
      (y : ℕ → F.lvl m) (z : ℕ → F.lvl (m + 1)),
      (∀ j, E.toBase (m + 1) (b j) ∈ Bs ∧ E.toBase (m + 1) (b j) ∈ U) →
      E.toBase (m + 1) b₀ ∈ Bs → E.toBase (m + 1) b₀ ∈ U → ‖E.toBase (m + 1) b₀‖ < r →
      Tendsto (fun j => E.toBase (m + 1) (b j)) atTop (𝓝 (E.toBase (m + 1) b₀)) →
      (∀ j, E.toBase m (η j) ∈ X) → (∃ M : ℝ, ∀ j, ‖η j‖ ≤ M) →
      (∀ j, levelDeriv (scDeriv U f) m (b j) (η j) = y j + F.incl m (z j)) →
      Tendsto y atTop (𝓝 0) → (∃ M : ℝ, ∀ j, ‖z j‖ ≤ M) →
      ∃ (η₀ : E.lvl m) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (η ∘ φ) atTop (𝓝 η₀))
    {K : Set Bs} (hK : ∀ b ∈ K, (b : E.lvl 0) ∈ U ∧ ‖(b : E.lvl 0)‖ < r) :
    FamilyCompactness K (famL hf hBs hXsc hYA ℓ1 hℓ1) m := by
  intro b b₀ η hbK hb₀K hb hη hL0
  set L := famL hf hBs hXsc hYA ℓ1 hℓ1 with hLdef
  set Φ : Bs → E.lvl m →L[ℝ] F.lvl m := fun b => levelDeriv (scDeriv U f) m (ℓm b) with hΦdef
  have hΦc : ContinuousOn (fun p : Bs × E.lvl m => Φ p.1 p.2) (K ×ˢ univ) := by
    refine (hf.isSc1With_scDeriv.continuousOn_levelDeriv m).comp
      (f := fun p : Bs × E.lvl m => (ℓm p.1, p.2))
      ((ℓm.continuous.comp continuous_fst).prodMk continuous_snd).continuousOn ?_
    intro p hp
    exact ⟨show E.toBase (m + 1) (ℓm p.1) ∈ U by rw [hℓm]; exact (hK _ hp.1).1, mem_univ _⟩
  obtain ⟨M₁, hM₁⟩ := exists_bound_of_continuousOn_clm (Φ := Φ) hΦc hb₀K
  have hbK' : Tendsto b atTop (𝓝[K] b₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hb, Eventually.of_forall hbK⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hbK'.eventually hM₁)
  obtain ⟨M, hM⟩ := hη
  set P' : F.lvl m →L[ℝ] F.lvl m := (F.levelSub Y m).subtypeL.comp (hYA.proj m) with hP'
  set b' : ℕ → E.lvl (m + 1) := fun j => ℓm (b (j + N)) with hb'
  set η' : ℕ → E.lvl m := fun j => hXsc.inclOp m (η (j + N)) with hη'
  set y' : ℕ → F.lvl m := fun j => P' (Φ (b (j + N)) (η' j)) with hy'
  have hamem : ∀ j, F.toBase m (Φ (b (j + N)) (η' j) - y' j) ∈ Ac := fun j => by
    have := hYA.sub_proj_mem m (Φ (b (j + N)) (η' j))
    exact this
  set z' : ℕ → F.lvl (m + 1) := fun j => ℓA ⟨_, hamem j⟩ with hz'
  have hz'b : ∀ j, F.incl m (z' j) = Φ (b (j + N)) (η' j) - y' j := fun j => by
    apply F.toBase_injective m
    rw [← ScScale.toBase_succ, hz', hℓA]
  have hyL : ∀ j, y' j = hYA.1.inclOp m (L (b (j + N)) m (η (j + N))) := fun j => by
    rw [hLdef, famL_lvl hf hBs hXsc hYA ℓ1 hℓ1 ℓm hℓm (hK _ (hbK _)).1]
    rfl
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨η₀, φ, hφ, hlim⟩ := hcpt b' (ℓm b₀) η' y' z'
    (fun j => ⟨by rw [hℓm]; exact (b (j + N)).2, by rw [hℓm]; exact (hK _ (hbK _)).1⟩)
    (by rw [hℓm]; exact b₀.2) (by rw [hℓm]; exact (hK _ hb₀K).1) (by rw [hℓm]; exact (hK _ hb₀K).2)
    (by
      simp only [hb', hℓm]
      exact (continuous_subtype_val.tendsto _).comp (hb.comp (tendsto_add_atTop_nat N)))
    (fun j => (η (j + N)).2) ⟨M, fun j => hM _⟩
    (fun j => by
      rw [hz'b]
      show Φ (b (j + N)) (η' j) = _
      abel)
    (by
      have : Tendsto (fun j => L (b (j + N)) m (η (j + N))) atTop (𝓝 0) :=
        hL0.comp (tendsto_add_atTop_nat N)
      have h2 := ((hYA.1.inclOp m).continuous.tendsto _).comp this
      rw [map_zero] at h2
      exact h2.congr fun j => (hyL j).symm)
    ⟨‖ℓA‖ * (‖F.toBase m‖ * (‖ContinuousLinearMap.id ℝ (F.lvl m) - P'‖ * (|M₁| * M))),
      fun j => by
      have hΦb : ‖Φ (b (j + N)) (η' j)‖ ≤ |M₁| * M := by
        have h1 : ‖Φ (b (j + N)) (η' j)‖ ≤ M₁ * ‖η' j‖ := hN (j + N) (by omega) _
        calc ‖Φ (b (j + N)) (η' j)‖ ≤ M₁ * ‖η' j‖ := h1
          _ ≤ |M₁| * ‖η' j‖ := mul_le_mul_of_nonneg_right (le_abs_self M₁) (norm_nonneg _)
          _ ≤ |M₁| * M := mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
      have ha : ‖Φ (b (j + N)) (η' j) - y' j‖ ≤
          ‖ContinuousLinearMap.id ℝ (F.lvl m) - P'‖ * (|M₁| * M) := by
        have : Φ (b (j + N)) (η' j) - y' j =
            (ContinuousLinearMap.id ℝ (F.lvl m) - P') (Φ (b (j + N)) (η' j)) := rfl
        rw [this]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_left hΦb (norm_nonneg _))
      have hb2 : ‖F.toBase m (Φ (b (j + N)) (η' j) - y' j)‖ ≤
          ‖F.toBase m‖ * (‖ContinuousLinearMap.id ℝ (F.lvl m) - P'‖ * (|M₁| * M)) :=
        (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left ha (by positivity))
      calc ‖z' j‖ ≤ ‖ℓA‖ * ‖(⟨_, hamem j⟩ : Ac)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖ℓA‖ * (‖F.toBase m‖ * (‖ContinuousLinearMap.id ℝ (F.lvl m) - P'‖ * (|M₁| * M))) :=
          mul_le_mul_of_nonneg_left hb2 (by positivity)⟩
  have hXm : η₀ ∈ E.levelSub X m := by
    have hcl := E.isClosed_levelSub hXsc.1 m
    exact hcl.mem_of_tendsto hlim (Eventually.of_forall fun j => (η (φ j + N)).2)
  refine ⟨⟨η₀, hXm⟩, fun j => φ j + N, fun i j hij => by simp only; have := hφ hij; omega, ?_⟩
  exact tendsto_subtype_rng.2 hlim

end Family

/-- A ⇒ B: Lemma 3.60 in the setting of Theorem 3.58.  The neighbourhood `O` and its injectivity
property come from the project's `lemma_3_7_2` (allowed: it is not this item's theorem) applied to
the family `L(b) = P_Y ∘ Df(b)|_X`; for `Õ` with compact closure in `O`, the hypothesis
`lemma_3_7_3` is applied on `K = cl(Õ)` (compact in `B`), level by level: continuity from the sc¹
property, injectivity on level `m` from level `0`, `FamilyCompactness` from `CompactnessProp`;
`P_Y(Df(b)h)` is the `y` of B by uniqueness of the decomposition `F_m = Y_m ⊕ A_m`. -/
theorem A_to_B : A → B := by
  intro hA E F C U f Bs X hS Ac hAfin hAY
  obtain ⟨hU, h0, hf, -, hsplit, hBfin, -, hker, ⟨r, hr, hcpt⟩, -⟩ := hS
  have := hBfin
  have := hAfin
  set Y := imgY E F U f X with hYdef
  have hBs : Bs ≤ E.smooth := (E.proposition_1_1_7_iff Bs).1 hsplit.1
  have hAs : Ac ≤ F.smooth := (F.proposition_1_1_7_iff Ac).1 hAY.1
  have hXsc : E.IsScSubspace X := hsplit.2.1
  have hYA : F.IsScSplitting Y Ac := hAY.symm
  choose ℓ hℓ using fun k => exists_lift E Bs hBs k
  choose ℓA hℓA using fun k => exists_lift F Ac hAs k
  have hf1 : IsSc1 U f := hf.isSc1
  set L := famL hf1 hBs hXsc hYA (ℓ 1) (hℓ 1) with hLdef
  set O : Set Bs := {b | (b : E.lvl 0) ∈ U ∧ ‖(b : E.lvl 0)‖ < r} with hOdef
  have hOU : ∀ b ∈ O, (b : E.lvl 0) ∈ U := fun b hb => hb.1
  have h0O : (0 : Bs) ∈ O := ⟨h0, by simpa using hr⟩
  have hfc : ∀ m, ∀ K ⊆ O, FamilyCompactness K L m := fun m K hKO =>
    famL_compactness hf1 hBs hXsc hYA (ℓ 1) (hℓ 1) (ℓ (m + 1)) (hℓ (m + 1)) (ℓA (m + 1))
      (hℓA (m + 1)) (hcpt m) fun b hb => hKO hb
  have hcont : ∀ m, ∀ K ⊆ O, ContinuousOn (fun p : Bs × (E.ofSubspace hXsc).lvl m => L p.1 m p.2)
      (K ×ˢ univ) := fun m K hKO =>
    famL_continuousOn hf1 hBs hXsc hYA (ℓ 1) (hℓ 1) (ℓ (m + 1)) (hℓ (m + 1))
      fun b hb => (hKO hb).1
  -- `L(0)` is injective on level `0`
  have hinj : Injective (L 0 0) := by
    rw [injective_iff_map_eq_zero]
    intro h hh
    rw [hLdef, famL_lvl hf1 hBs hXsc hYA (ℓ 1) (hℓ 1) (ℓ (0 + 1)) (hℓ (0 + 1))
      (by simpa using h0) h] at hh
    simp only [map_zero, levelDeriv_zero] at hh
    set v := scDeriv U f (0 : E.lvl 1) (hXsc.inclOp 0 h) with hv
    obtain ⟨a, ha, c, hc, hvac⟩ := hYA.exists_add 0 v
    rw [hvac, hYA.proj_add 0 ha hc] at hh
    have ha0 : a = 0 := congrArg Subtype.val hh
    have hvA : v ∈ Ac := by rw [hvac, ha0, zero_add]; exact hc
    have hvY : v ∈ Y := ⟨hXsc.inclOp 0 h, h.2, rfl⟩
    have hv0 : v = 0 := by
      have hc' := hAY.2.2 0
      simp only [ScBanach.levelSub_zero] at hc'
      exact (Submodule.disjoint_def.1 hc'.disjoint) v hvA hvY
    have hhB : hXsc.inclOp 0 h ∈ Bs := hker (by
      show scDeriv U f 0 (hXsc.inclOp 0 h) = 0
      exact hv0)
    have hBX := hsplit.2.2 0
    simp only [ScBanach.levelSub_zero] at hBX
    exact Subtype.ext ((Submodule.disjoint_def.1 hBX.disjoint) _ hhB h.2)
  -- Lemma 3.59 (a project lemma, not this item's) gives the neighbourhood `O`
  obtain ⟨r', hr', hinjO⟩ := Polyfold.lemma_3_7_2 h0O L (hcont 0 O subset_rfl) hinj
    (hfc 0 O subset_rfl)
  obtain ⟨OU, hOUo, hUeq⟩ := hU.relOpen
  set OB : Set (E.lvl 0) := (OU ∩ Metric.ball 0 (min r r')) ∩ ((Bs : Set (E.lvl 0)) ∩ C)
    with hOBdef
  have hOBU : OB ⊆ U := by
    rintro x ⟨⟨hxO, -⟩, -, hxC⟩
    rw [hUeq]; exact ⟨hxO, hxC⟩
  have hOBO : ∀ x ∈ OB, ∃ hxB : x ∈ Bs, (⟨x, hxB⟩ : Bs) ∈ O ∧ ‖(⟨x, hxB⟩ : Bs)‖ < r' := by
    rintro x ⟨⟨hxO, hxr⟩, hxB, hxC⟩
    rw [Metric.mem_ball, dist_zero_right] at hxr
    exact ⟨hxB, ⟨hOBU ⟨⟨hxO, by rw [Metric.mem_ball, dist_zero_right]; exact hxr⟩, hxB, hxC⟩,
      hxr.trans_le (min_le_left _ _)⟩, hxr.trans_le (min_le_right _ _)⟩
  refine ⟨OB, ⟨OU ∩ Metric.ball 0 (min r r'), hOUo.inter Metric.isOpen_ball, rfl⟩, ?_, hOBU,
    ?_, ?_⟩
  · have h0U' := h0
    rw [hUeq] at h0U'
    exact ⟨⟨h0U'.1, by simp [lt_min hr hr']⟩, Bs.zero_mem, h0U'.2⟩
  · -- the injectivity of Lemma 3.59
    intro b₁ hb₁ h hX hA'
    obtain ⟨hxB, hbO, hbr⟩ := hOBO _ hb₁
    set b : Bs := ⟨E.toBase 1 b₁, hxB⟩ with hbdef
    have hℓb : ℓ (0 + 1) b = b₁ := E.toBase_injective 1 (by rw [hℓ (0 + 1)])
    set hh : (E.ofSubspace hXsc).lvl 0 := ⟨h, hX⟩ with hhdef
    have hL : L b 0 hh = 0 := by
      refine (famL_lvl hf1 hBs hXsc hYA (ℓ 1) (hℓ 1) (ℓ (0 + 1)) (hℓ (0 + 1)) (b := b)
        hbO.1 hh).trans ?_
      rw [hℓb, levelDeriv_zero]
      exact hYA.proj_apply_right 0 (show F.toBase 0 (scDeriv U f b₁ h) ∈ Ac from hA')
    have := hinjO b hbO hbr (hL.trans (map_zero _).symm)
    exact congrArg Subtype.val this
  · -- the uniform lower bounds of Lemma 3.60 (the hypothesis)
    intro Ot hOt h0Ot hcpt' hclO m
    set K : Set Bs := Subtype.val ⁻¹' closure Ot with hKdef
    have hKc : IsCompact K := by
      refine Topology.IsInducing.subtypeVal.isCompact_preimage ?_ hcpt'
      rw [Subtype.range_coe]
      exact Bs.closed_of_finiteDimensional
    have hKO : K ⊆ O := fun b hb => (hOBO _ (hclO hb)).2.1
    have hKinj : ∀ b ∈ K, Injective (L b m) := fun b hb =>
      ScOperator.injective_lvl _ (hinjO b (hKO hb) (hOBO _ (hclO hb)).2.2) m
    obtain ⟨c, hc, hcb⟩ := hA hKc L m (hcont m K hKO) hKinj (hfc m K hKO)
    refine ⟨c, hc, fun b' hb' h hX y hyY hyA => ?_⟩
    have hb'B : E.toBase (m + 1) b' ∈ Bs := by
      obtain ⟨O'', -, hOteq⟩ := hOt
      rw [hOteq] at hb'
      exact hb'.2.2
    set b : Bs := ⟨E.toBase (m + 1) b', hb'B⟩ with hbdef
    have hbK : b ∈ K := subset_closure hb'
    have hℓb : ℓ (m + 1) b = b' := E.toBase_injective (m + 1) (by rw [hℓ (m + 1)])
    set hh : (E.ofSubspace hXsc).lvl m := ⟨h, hX⟩ with hhdef
    have hLy : L b m hh = ⟨y, hyY⟩ := by
      refine (famL_lvl hf1 hBs hXsc hYA (ℓ 1) (hℓ 1) (ℓ (m + 1)) (hℓ (m + 1)) (b := b)
        (hKO hbK).1 hh).trans ?_
      rw [hℓb]
      have hdec : levelDeriv (scDeriv U f) m b' (hXsc.inclOp m hh) =
          y + (levelDeriv (scDeriv U f) m b' h - y) := by
        show levelDeriv (scDeriv U f) m b' h = _
        abel
      rw [hdec]
      exact hYA.proj_add m hyY hyA
    have := hcb b hbK hh
    rw [hLy] at this
    exact this

#rt_check RoundTrip.V3_53.A_to_B [Polyfold.lemma_3_7_3]
#rt_overlap RoundTrip.V3_53.A_to_B [Polyfold.lemma_3_7_3]

end RoundTrip.V3_53

end
