import Polyfold.Chapter5.GapP1_LindenstraussPair

/-!
# Projectional resolutions of the identity in WCG spaces

A tool for the non-separable case of 2021 Theorem 5.5.16, p. 235 (preprint 5.43).

## The abstract part

`P : Ordinal → (X →L[ℝ] X)` is *continuous at limits* (`PRICont P`) if, at every limit `β`, the
map `γ ↦ P γ x` converges to `P β x` from below. For such `P`:
* `pri_finite`: for every `x` and `η > 0`, only finitely many `α` have
  `‖P (α+1) x − P α x‖ > η`;
* `pri_approx`: if `P μ x = x`, then either `P 0 x = x`, or there is an `α < μ` with
  `P (α+1) x ≠ P α x` and `‖x − P (α+1) x‖ < η`.

## The construction

Fix a weakly compact `K` of dense span in a Banach space `X`, and a map `e` from the ordinals
below `μ` onto a dense set. Let `A α, D α` be the Lindenstrauss closure of `{e β | β < α}`
(`lclA`, `lclD`), and `P α` the projection of the pair (`IsLPair.exists_proj`). Then:
* `‖P α‖ ≤ 1`;
* `P α P β = P β P α = P (min α β)`;
* `P μ = 1`;
* `P` is continuous at limits, because the closure has finite character (`lclA_finite`);
* the range of `P α` has a dense subset of cardinality at most `max(|α|, ℵ₀)` (`card_lcl`).

This is the Amir–Lindenstrauss projectional resolution of the identity.
-/

open Set Function Filter Topology Metric Order
open scoped Cardinal

noncomputable section

namespace Polyfold

universe u v

/-! ### Abstract resolutions -/

section Abstract

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (P : Ordinal.{v} → X →L[ℝ] X)

/-- **Continuity at limits** of a family of operators indexed by ordinals. -/
def PRICont : Prop :=
  ∀ β : Ordinal.{v}, 0 < β → (∀ γ < β, succ γ < β) → ∀ x, ∀ ε > 0,
    ∃ γ < β, ∀ γ', γ ≤ γ' → γ' < β → ‖P γ' x - P β x‖ < ε

variable {P}

/-- **The increments are in `c₀`**: `{α | η < ‖P (α+1) x − P α x‖}` is finite. -/
theorem pri_finite (hP : PRICont P) (x : X) {η : ℝ} (hη : 0 < η) :
    {α | η < ‖P (succ α) x - P α x‖}.Finite := by
  by_contra hinf
  set s := {α | η < ‖P (succ α) x - P α x‖} with hs
  have : Infinite s := (Set.not_finite.1 hinf).to_subtype
  obtain ⟨f, hf | hf⟩ := Infinite.exists_strictMono_or_strictAnti s
  swap
  · exact not_strictAnti_of_wellFoundedLT f hf
  set a : ℕ → Ordinal.{v} := fun n => (f n : Ordinal) with ha_def
  have ha : StrictMono a := fun m n h => hf h
  have hbdd : BddAbove (range a) := Ordinal.bddAbove_of_small
  set β := ⨆ n, a n with hβ
  have hlt : ∀ n, a n < β := fun n => (ha (Nat.lt_succ_self n)).trans_le (le_ciSup hbdd _)
  have h0 : 0 < β := bot_le.trans_lt (hlt 0)
  have hsucc : ∀ γ < β, succ γ < β := fun γ hγ => by
    obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 hγ
    exact (succ_le_of_lt hn).trans_lt (hlt (n + 1) |>.trans_le' (ha.monotone (Nat.le_succ n)))
  obtain ⟨γ, hγ, hγ'⟩ := hP β h0 hsucc x (η / 2) (half_pos hη)
  obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 hγ
  have h1 := hγ' (a n) hn.le (hlt n)
  have h2 := hγ' (succ (a n)) (hn.le.trans (le_succ _)) (hsucc _ (hlt n))
  have h3 : η < ‖P (succ (a n)) x - P (a n) x‖ := (f n).2
  have h4 := norm_sub_le_norm_sub_add_norm_sub (P (succ (a n)) x) (P β x) (P (a n) x)
  rw [norm_sub_rev (P β x)] at h4
  linarith

/-- **Approximation by an increment**: if `P μ x = x`, then `P 0 x = x`, or some `α < μ` has
`P (α+1) x ≠ P α x` and `‖x − P (α+1) x‖ < η`. -/
theorem pri_approx (hP : PRICont P) {x : X} {μ : Ordinal.{v}} (hμ : P μ x = x) {η : ℝ}
    (hη : 0 < η) :
    P 0 x = x ∨ ∃ α < μ, P (succ α) x ≠ P α x ∧ ‖x - P (succ α) x‖ < η := by
  set T := {β | P β x = x} with hT
  have hTne : T.Nonempty := ⟨μ, hμ⟩
  set β₀ := sInf T with hβ₀def
  have hβ₀ : P β₀ x = x := csInf_mem hTne
  have hmin : ∀ β < β₀, P β x ≠ x := fun β hβ h => notMem_of_lt_csInf' hβ h
  have hβμ : β₀ ≤ μ := csInf_le' hμ
  rcases Ordinal.zero_or_succ_or_isSuccLimit β₀ with h | ⟨α, hα⟩ | hlim
  · left; rw [← h]; exact hβ₀
  · right
    have hαs : α < β₀ := hα ▸ lt_succ α
    refine ⟨α, hαs.trans_le hβμ, ?_, ?_⟩
    · rw [hα, hβ₀]; exact (hmin α hαs).symm
    · rw [hα, hβ₀, sub_self, norm_zero]; exact hη
  · right
    have h0 : 0 < β₀ := pos_iff_ne_zero.2 (Ordinal.isSuccLimit_iff.1 hlim).1
    have hs : ∀ γ < β₀, succ γ < β₀ := fun γ hγ => hlim.succ_lt hγ
    obtain ⟨γ, hγ, hγ'⟩ := hP β₀ h0 hs x η hη
    by_contra hno
    have hconst : ∀ α, γ ≤ α → α < β₀ → P (succ α) x = P α x := fun α h1 h2 => by
      by_contra hne
      refine hno ⟨α, h2.trans_le hβμ, hne, ?_⟩
      have h3 := hγ' (succ α) (h1.trans (le_succ α)) (hs α h2)
      rwa [hβ₀, norm_sub_rev] at h3
    have key : ∀ δ, γ ≤ δ → δ ≤ β₀ → P δ x = P γ x := by
      intro δ
      refine WellFoundedLT.induction (motive := fun δ => γ ≤ δ → δ ≤ β₀ → P δ x = P γ x) δ
        fun δ ih h1 h2 => ?_
      rcases eq_or_lt_of_le h1 with h | h1'
      · rw [h]
      rcases Ordinal.zero_or_succ_or_isSuccLimit δ with hd | ⟨α, hα⟩ | hdl
      · exact absurd h1' (by rw [hd]; exact (bot_le (a := γ)).not_gt)
      · have hαδ : α < δ := hα ▸ lt_succ α
        have hγα : γ ≤ α := lt_succ_iff.1 (by rw [hα]; exact h1')
        rw [← hα, hconst α hγα (hαδ.trans_le h2)]
        exact ih α hαδ hγα (hαδ.le.trans h2)
      · refine eq_of_forall_dist_le fun ε hε => ?_
        have hd0 : 0 < δ := pos_iff_ne_zero.2 (Ordinal.isSuccLimit_iff.1 hdl).1
        obtain ⟨γ'', hγ''δ, hγ''⟩ := hP δ hd0 (fun _ h => hdl.succ_lt h) x ε hε
        have hm : max γ γ'' < δ := max_lt h1' hγ''δ
        have h5 := hγ'' (max γ γ'') (le_max_right _ _) hm
        rw [ih (max γ γ'') hm (le_max_left _ _) (hm.le.trans h2)] at h5
        rw [dist_eq_norm, norm_sub_rev]
        exact h5.le
    exact hmin γ hγ ((key β₀ hγ.le le_rfl).symm.trans hβ₀)

end Abstract

/-! ### The construction in a WCG space -/

section Construction

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The initial segment `{e β | β < α, β < μ}`. -/
def segS (e : Ordinal.{u} → X) (μ α : Ordinal.{u}) : Set X := e '' {β | β < α ∧ β < μ}

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma segS_mono (e : Ordinal.{u} → X) (μ : Ordinal.{u}) {α α' : Ordinal.{u}} (h : α ≤ α') :
    segS e μ α ⊆ segS e μ α' :=
  image_mono fun _ hβ => ⟨hβ.1.trans_le h, hβ.2⟩

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma card_segS (e : Ordinal.{u} → X) (μ α : Ordinal.{u}) : #(segS e μ α) ≤ α.card := by
  have h1 := Cardinal.mk_image_le_lift (f := e) (s := {β | β < α ∧ β < μ})
  have h2 : #{β | β < α ∧ β < μ} ≤ #(Iio α) := Cardinal.mk_le_mk_of_subset fun β hβ => hβ.1
  rw [Cardinal.mk_Iio_ordinal] at h2
  have h3 : Cardinal.lift.{u + 1} #(segS e μ α) ≤ Cardinal.lift.{u + 1} α.card := by
    refine h1.trans ?_
    rw [Cardinal.lift_id'.{u, u + 1}]
    exact h2.trans_eq (by simp)
  exact Cardinal.lift_le.1 h3

variable [CompleteSpace X] {K : Set X} (hK : IsCompact (toWeakSpace ℝ X '' K))
  (hspan : closure (Submodule.span ℝ K : Set X) = univ) (e : Ordinal.{u} → X) (μ : Ordinal.{u})

/-- **The projection `P α`** of the Lindenstrauss closure of `{e β | β < α, β < μ}`. -/
def priP (α : Ordinal.{u}) : X →L[ℝ] X :=
  ((isLPair_lcl (K := K) (segS e μ α)).exists_proj hK hspan).choose

lemma priP_spec (α : Ordinal.{u}) :
    (∀ x, priP hK hspan e μ α x ∈ closure (lclA K (segS e μ α))) ∧
      (∀ x, ∀ f ∈ lclD K (segS e μ α), f (priP hK hspan e μ α x) = f x) ∧
        ‖priP hK hspan e μ α‖ ≤ 1 :=
  ((isLPair_lcl (K := K) (segS e μ α)).exists_proj hK hspan).choose_spec

lemma priP_fix {α : Ordinal.{u}} {x : X} (hx : x ∈ closure (lclA K (segS e μ α))) :
    priP hK hspan e μ α x = x :=
  (isLPair_lcl _).eq_of_forall ((priP_spec hK hspan e μ α).1 x) hx
    fun f hf => (priP_spec hK hspan e μ α).2.1 x f hf

lemma priP_comm₁ {α β : Ordinal.{u}} (h : α ≤ β) (x : X) :
    priP hK hspan e μ α (priP hK hspan e μ β x) = priP hK hspan e μ α x :=
  (isLPair_lcl _).eq_of_forall ((priP_spec hK hspan e μ α).1 _) ((priP_spec hK hspan e μ α).1 x)
    fun f hf => by
      rw [(priP_spec hK hspan e μ α).2.1 _ f hf, (priP_spec hK hspan e μ α).2.1 x f hf,
        (priP_spec hK hspan e μ β).2.1 x f (lclD_mono (segS_mono e μ h) hf)]

lemma priP_comm₂ {α β : Ordinal.{u}} (h : α ≤ β) (x : X) :
    priP hK hspan e μ β (priP hK hspan e μ α x) = priP hK hspan e μ α x :=
  priP_fix hK hspan e μ (closure_mono (lclA_mono (segS_mono e μ h))
    ((priP_spec hK hspan e μ α).1 x))

lemma priP_top (hd : Dense (segS e μ μ)) (x : X) : priP hK hspan e μ μ x = x :=
  priP_fix hK hspan e μ (closure_mono (subset_lclA _) (hd.closure_eq ▸ mem_univ x))

/-- **The resolution is continuous at limits** (finite character of the closure). -/
theorem priP_cont : PRICont (priP hK hspan e μ) := by
  classical
  intro β h0 hs x ε hε
  set P := priP hK hspan e μ with hPdef
  obtain ⟨a, haA, hda⟩ := Metric.mem_closure_iff.1 ((priP_spec hK hspan e μ β).1 x) (ε / 2)
    (by positivity)
  obtain ⟨F, hFS, haF⟩ := lclA_finite (K := K) _ haA
  have hord : ∀ y ∈ F, ∃ b, (b < β ∧ b < μ) ∧ e b = y := fun y hy => hFS hy
  choose o ho using hord
  set γ := F.attach.sup fun y => succ (o y.1 y.2) with hγ
  have hγβ : γ < β := by
    rw [hγ, Finset.sup_lt_iff (bot_lt_iff_ne_bot.2 h0.ne')]
    intro y _
    exact hs _ (ho y.1 y.2).1.1
  refine ⟨γ, hγβ, fun γ' h1 h2 => ?_⟩
  have hFγ' : (↑F : Set X) ⊆ segS e μ γ' := fun y hy => by
    refine ⟨o y hy, ⟨?_, (ho y hy).1.2⟩, (ho y hy).2⟩
    have : succ (o y hy) ≤ γ :=
      Finset.le_sup (f := fun y : F => succ (o y.1 y.2)) (Finset.mem_attach F ⟨y, hy⟩)
    exact (lt_succ _).trans_le (this.trans h1)
  have hPa : P γ' a = a :=
    priP_fix hK hspan e μ (subset_closure (lclA_mono hFγ' haF))
  have hcomm : P γ' x = P γ' (P β x) := (priP_comm₁ hK hspan e μ h2.le x).symm
  rw [dist_eq_norm] at hda
  have hnorm : ‖P γ' (P β x - a)‖ ≤ ‖P β x - a‖ :=
    ((P γ').le_opNorm _).trans (by
      have := (priP_spec hK hspan e μ γ').2.2
      nlinarith [norm_nonneg (P β x - a)])
  calc ‖P γ' x - P β x‖ = ‖P γ' (P β x - a) + (a - P β x)‖ := by
        rw [hcomm, map_sub, hPa]; congr 1; abel
    _ ≤ ‖P β x - a‖ + ‖a - P β x‖ := (norm_add_le _ _).trans (by gcongr)
    _ < ε := by rw [norm_sub_rev a]; linarith

end Construction

end Polyfold
