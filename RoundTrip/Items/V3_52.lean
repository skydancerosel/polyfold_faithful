import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_52

open Set Filter Topology Function

noncomputable section

namespace RoundTrip.V3_52
open Polyfold

/-- The project's statement: `lemma_3_59` (abstract form, for a family of sc-operators);
`FamilyCompactness` is a definition.  No universe parameters. -/
def A : Prop := type_of% @Polyfold.lemma_3_59

theorem A_holds : A := @Polyfold.lemma_3_59

/-! ### Glue: the concrete family `L(b) = P_Y ∘ Df(b)|_X` as sc-operators `X → Y` -/

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
/-- The family `L(b) = P_Y ∘ Df(b)|_X : X → Y` (zero where `b ∉ U`), `Df(b)` the sc-operator
`IsSc1With.scOperator_deriv` at the smooth point `b`. -/
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

lemma famL_zero (hf : IsSc1 U f) (hBs : Bs ≤ E.smooth) (hXsc : E.IsScSubspace X)
    (hYA : F.IsScSplitting Y Ac) (ℓ1 : Bs →L[ℝ] E.lvl 1) (hℓ1 : ∀ s, E.toBase 1 (ℓ1 s) = s)
    {b : Bs} (hb : (b : E.lvl 0) ∈ U) (h : (E.ofSubspace hXsc).lvl 0) :
    famL hf hBs hXsc hYA ℓ1 hℓ1 b 0 h = hYA.proj 0 (scDeriv U f (ℓ1 b) (hXsc.inclOp 0 h)) := by
  rw [famL, dif_pos hb, ScOperator.comp_apply, ScOperator.comp_apply,
    IsScOperator.toScOperator_zero]
  rfl

end Family

/-- A ⇒ B: Lemma 3.59 in the setting of Theorem 3.58, from the abstract `lemma_3_59` applied to
the family `L(b) = P_Y ∘ Df(b)|_X` over `Bf = B` (finite-dimensional), `O = {b ∈ B ∩ U, |b| < r}`
(`r` from the compactness property): continuity from the sc¹ property, injectivity of `L(0)` from
`ker Df(0) ⊆ B`, `B ∩ X = 0` and `A ∩ Y = 0`, and `FamilyCompactness` from `CompactnessProp`
(the `A`-component of `Df(b_j)h_j` is bounded on level `1` because `A` is a finite-dimensional
smooth subspace and `Df(b)` is uniformly bounded near `b₀`). -/
theorem A_to_B : A → B := by
  intro hA E F C U f Bs X hS Ac hAfin hAY
  obtain ⟨hU, h0, hf, -, hsplit, hBfin, -, hker, ⟨r, hr, hcpt⟩, -⟩ := hS
  have := hBfin
  have := hAfin
  set Y := imgY E F U f X with hYdef
  have hBs : Bs ≤ E.smooth := (E.proposition_1_6_iff Bs).1 hsplit.1
  have hAs : Ac ≤ F.smooth := (F.proposition_1_6_iff Ac).1 hAY.1
  have hXsc : E.IsScSubspace X := hsplit.2.1
  have hYA : F.IsScSplitting Y Ac := hAY.symm
  obtain ⟨ℓ1, hℓ1⟩ := exists_lift E Bs hBs 1
  obtain ⟨ℓA, hℓA⟩ := exists_lift F Ac hAs 1
  have hf1 : IsSc1 U f := hf.isSc1
  have hD := hf1.isSc1With_scDeriv
  set L := famL hf1 hBs hXsc hYA ℓ1 hℓ1 with hLdef
  set O : Set Bs := {b | (b : E.lvl 0) ∈ U ∧ ‖(b : E.lvl 0)‖ < r} with hOdef
  have hOU : ∀ b ∈ O, (b : E.lvl 0) ∈ U := fun b hb => hb.1
  have h0O : (0 : Bs) ∈ O := ⟨h0, by simpa using hr⟩
  -- `(b, h) ↦ Df(b)h` on `O × E₀`
  have hΦc : ContinuousOn (fun p : Bs × E.lvl 0 => scDeriv U f (ℓ1 p.1) p.2) (O ×ˢ univ) := by
    refine hD.continuousOn_deriv.comp (f := fun p : Bs × E.lvl 0 => (ℓ1 p.1, p.2))
      ((ℓ1.continuous.comp continuous_fst).prodMk continuous_snd).continuousOn ?_
    intro p hp
    show E.toBase 1 (ℓ1 p.1) ∈ U
    rw [hℓ1]; exact hOU _ hp.1
  -- continuity of the family on level `0`
  have hcont : ContinuousOn (fun p : Bs × (E.ofSubspace hXsc).lvl 0 => L p.1 0 p.2)
      (O ×ˢ univ) := by
    have h1 : ContinuousOn (fun p : Bs × (E.ofSubspace hXsc).lvl 0 =>
        hYA.proj 0 (scDeriv U f (ℓ1 p.1) (hXsc.inclOp 0 p.2))) (O ×ˢ univ) :=
      (hYA.proj 0).continuous.comp_continuousOn
        (hΦc.comp (f := fun p : Bs × (E.ofSubspace hXsc).lvl 0 => (p.1, hXsc.inclOp 0 p.2))
          (continuous_fst.prodMk ((hXsc.inclOp 0).continuous.comp continuous_snd)).continuousOn
          fun p hp => ⟨hp.1, mem_univ _⟩)
    refine h1.congr fun p hp => ?_
    exact famL_zero hf1 hBs hXsc hYA ℓ1 hℓ1 (hOU _ hp.1) p.2
  -- injectivity of `L(0)`
  have hinj : Injective (L 0 0) := by
    rw [injective_iff_map_eq_zero]
    intro h hh
    rw [hLdef, famL_zero hf1 hBs hXsc hYA ℓ1 hℓ1 (by simpa using h0) h] at hh
    simp only [map_zero] at hh
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
  -- the compactness property of the family on level `0`
  have hfc : FamilyCompactness O L 0 := by
    intro b b₀ η hbO hb₀O hb hη hL0
    set Φ : Bs → E.lvl 0 →L[ℝ] F.lvl 0 := fun b => scDeriv U f (ℓ1 b) with hΦdef
    obtain ⟨M₁, hM₁⟩ := exists_bound_of_continuousOn_clm (Φ := Φ) hΦc hb₀O
    have hbO' : Tendsto b atTop (𝓝[O] b₀) :=
      tendsto_nhdsWithin_iff.2 ⟨hb, Eventually.of_forall hbO⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hbO'.eventually hM₁)
    obtain ⟨M, hM⟩ := hη
    set P' : F.lvl 0 →L[ℝ] F.lvl 0 := (Y : Submodule ℝ (F.lvl 0)).subtypeL.comp (hYA.proj 0)
      with hP'
    -- the tails
    set b' : ℕ → E.lvl 1 := fun j => ℓ1 (b (j + N)) with hb'
    set η' : ℕ → E.lvl 0 := fun j => hXsc.inclOp 0 (η (j + N)) with hη'
    set y' : ℕ → F.lvl 0 := fun j => P' (Φ (b (j + N)) (η' j)) with hy'
    have hamem : ∀ j, Φ (b (j + N)) (η' j) - y' j ∈ Ac := fun j => by
      have := hYA.sub_proj_mem 0 (Φ (b (j + N)) (η' j))
      exact this
    set z' : ℕ → F.lvl 1 := fun j => ℓA ⟨_, hamem j⟩ with hz'
    have hz'b : ∀ j, F.toBase 1 (z' j) = Φ (b (j + N)) (η' j) - y' j := fun j => by
      rw [hz', hℓA]
    have hyL : ∀ j, y' j = hYA.1.inclOp 0 (L (b (j + N)) 0 (η (j + N))) := fun j => by
      rw [hLdef, famL_zero hf1 hBs hXsc hYA ℓ1 hℓ1 (hOU _ (hbO _))]
      rfl
    obtain ⟨η₀, φ, hφ, hlim⟩ := hcpt 0 b' (ℓ1 b₀) η' y' z'
      (fun j => ⟨by rw [hℓ1]; exact (b (j + N)).2, by rw [hℓ1]; exact hOU _ (hbO _)⟩)
      (by rw [hℓ1]; exact b₀.2) (by rw [hℓ1]; exact hOU _ hb₀O) (by rw [hℓ1]; exact hb₀O.2)
      (by
        simp only [hb', hℓ1]
        exact (continuous_subtype_val.tendsto _).comp (hb.comp (tendsto_add_atTop_nat N)))
      (fun j => (η (j + N)).2) ⟨M, fun j => hM _⟩
      (fun j => by
        rw [levelDeriv_zero]
        have h1 : F.incl 0 (z' j) = F.toBase 1 (z' j) := rfl
        rw [h1, hz'b]
        abel)
      (by
        have : Tendsto (fun j => L (b (j + N)) 0 (η (j + N))) atTop (𝓝 0) :=
          hL0.comp (tendsto_add_atTop_nat N)
        have h2 := ((hYA.1.inclOp 0).continuous.tendsto _).comp this
        rw [map_zero] at h2
        refine h2.congr fun j => ?_
        exact (hyL j).symm)
      ⟨‖ℓA‖ * (‖ContinuousLinearMap.id ℝ (F.lvl 0) - P'‖ * (|M₁| * M)), fun j => by
        have hΦb : ‖Φ (b (j + N)) (η' j)‖ ≤ |M₁| * M := by
          have h1 : ‖Φ (b (j + N)) (η' j)‖ ≤ M₁ * ‖η' j‖ := hN (j + N) (by omega) _
          have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
          calc ‖Φ (b (j + N)) (η' j)‖ ≤ M₁ * ‖η' j‖ := h1
            _ ≤ |M₁| * ‖η' j‖ := mul_le_mul_of_nonneg_right (le_abs_self M₁) (norm_nonneg _)
            _ ≤ |M₁| * M := mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
        have ha : ‖Φ (b (j + N)) (η' j) - y' j‖ ≤
            ‖ContinuousLinearMap.id ℝ (F.lvl 0) - P'‖ * (|M₁| * M) := by
          have : Φ (b (j + N)) (η' j) - y' j =
              (ContinuousLinearMap.id ℝ (F.lvl 0) - P') (Φ (b (j + N)) (η' j)) := rfl
          rw [this]
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_left hΦb (norm_nonneg _))
        calc ‖z' j‖ ≤ ‖ℓA‖ * ‖(⟨_, hamem j⟩ : Ac)‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖ℓA‖ * (‖ContinuousLinearMap.id ℝ (F.lvl 0) - P'‖ * (|M₁| * M)) :=
            mul_le_mul_of_nonneg_left ha (by positivity)⟩
    -- the limit lies in `X`
    have hX0 : η₀ ∈ E.levelSub X 0 := by
      have hcl := E.isClosed_levelSub hXsc.1 0
      exact hcl.mem_of_tendsto hlim (Eventually.of_forall fun j => (η (φ j + N)).2)
    refine ⟨⟨η₀, hX0⟩, fun j => φ j + N, fun i j hij => by simp only; have := hφ hij; omega, ?_⟩
    exact tendsto_subtype_rng.2 hlim
  -- Lemma 3.59 (the hypothesis)
  obtain ⟨r', hr', hinjO⟩ := hA h0O L hcont hinj hfc
  obtain ⟨OU, hOUo, hUeq⟩ := hU.relOpen
  refine ⟨(OU ∩ Metric.ball 0 (min r r')) ∩ ((Bs : Set (E.lvl 0)) ∩ C),
    ⟨OU ∩ Metric.ball 0 (min r r'), hOUo.inter Metric.isOpen_ball, rfl⟩, ?_, ?_, ?_⟩
  · have h0U' := h0
    rw [hUeq] at h0U'
    exact ⟨⟨h0U'.1, by simp [lt_min hr hr']⟩, Bs.zero_mem, h0U'.2⟩
  · rintro x ⟨⟨hxO, -⟩, -, hxC⟩
    rw [hUeq]; exact ⟨hxO, hxC⟩
  · rintro b₁ ⟨⟨hxO, hxr⟩, hxB, hxC⟩ h hX hA'
    have hxU : E.toBase 1 b₁ ∈ U := by rw [hUeq]; exact ⟨hxO, hxC⟩
    rw [Metric.mem_ball, dist_zero_right] at hxr
    set b : Bs := ⟨E.toBase 1 b₁, hxB⟩ with hbdef
    have hbO : b ∈ O := ⟨hxU, hxr.trans_le (min_le_left _ _)⟩
    have hbr : ‖b‖ < r' := hxr.trans_le (min_le_right _ _)
    have hℓb : ℓ1 b = b₁ := E.toBase_injective 1 (by rw [hℓ1])
    set hh : (E.ofSubspace hXsc).lvl 0 := ⟨h, hX⟩ with hhdef
    have hL : L b 0 hh = 0 := by
      refine (famL_zero hf1 hBs hXsc hYA ℓ1 hℓ1 (b := b) hxU hh).trans ?_
      show hYA.proj 0 (scDeriv U f (ℓ1 b) h) = 0
      rw [hℓb]
      exact hYA.proj_apply_right 0 (show F.toBase 0 (scDeriv U f b₁ h) ∈ Ac from hA')
    have := hinjO b hbO hbr (hL.trans (map_zero _).symm)
    exact congrArg Subtype.val this

#rt_check RoundTrip.V3_52.A_to_B [Polyfold.lemma_3_59]
#rt_overlap RoundTrip.V3_52.A_to_B [Polyfold.lemma_3_59]

end RoundTrip.V3_52

end
