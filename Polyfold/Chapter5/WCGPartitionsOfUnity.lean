import Polyfold.Chapter5.LocallyFiniteBases
import Polyfold.Chapter5.ProjectionalResolution

/-!
# Godefroy–Troyanski–Whitfield–Zizler: 2021 Theorem 5.5.16 for all Banach spaces

**2021 Theorem 5.5.16, p. 235 (preprint 5.43)**: a weakly compactly generated Banach space with a
`C^k`-bump function admits `C^k` partitions of unity (`theorem_5_5_16`).

*Proof*, by strong induction on the cardinality `κ` of a dense subset.
* `κ ≤ ℵ₀`: the separable case, Bonic–Frampton (`admitsContDiffPartitionsOfUnity_of_separable`).
* `κ > ℵ₀`: let `μ = κ.ord`. The Amir–Lindenstrauss projections `P α` (`priP`) are norm-one
  projections. They are continuous at limits and satisfy `P μ = 1`.
  - Each range `P α X` with `α < μ` is again a WCG Banach space with a `C^k` bump. It has a dense
    subset of cardinality `max(|α|, ℵ₀) < κ`, so by induction it admits `C^k` partitions of unity.
  - These give bases relative to `Q = P (α+1)` (`exists_isRelC0Base_of_admits`,
    `IsRelC0Base.comp`).
  - The increments `Δ = P (α+1) − P α` are in `c₀` (`pri_finite`), and every `x ≠ 0` is
    approximated by some `Q x` with `Δ x ≠ 0` (`pri_approx`).
  - The gluing lemma (`isRelC0Base_glue`) gives a base of `X`, hence `C^k` partitions of unity
    (`admitsContDiffPartitionsOfUnity_of_isRelC0Base`, through Toruńczyk's theorem).

The proof follows Deville–Godefroy–Zizler, *Smoothness and Renormings in Banach Spaces*, VI.2 and
VIII.3. Projections are built with an elementary closure argument and weak compactness
(`IsLPair.exists_proj`). Krein's theorem is not needed.
-/

open Set Function Filter Topology Metric Order
open scoped Cardinal

noncomputable section

namespace Polyfold

universe u

section Subspace

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {k : ℕ∞}

/-- A `C^k` bump restricts to a `C^k` bump on every subspace. -/
theorem HasContDiffBump.submodule (hb : HasContDiffBump X k) (M : Submodule ℝ X) :
    HasContDiffBump M k := by
  obtain ⟨ψ, R, hψc, -, hψ1, hψs⟩ := hb.exists_one_on_ball
  refine ⟨fun m => ψ m, hψc.comp M.subtypeL.contDiff, fun h => ?_, ?_⟩
  · have := congrFun h 0
    simp only [Submodule.coe_zero, Pi.zero_apply] at this
    rw [hψ1 0 (mem_ball_self one_pos)] at this
    exact one_ne_zero this
  · refine (Metric.isBounded_ball (x := (0 : M)) (r := R)).subset fun m hm => ?_
    have h := hψs hm
    rw [mem_ball_zero_iff] at h ⊢
    exact h

/-- The range of a bounded projection of a WCG space is WCG. -/
theorem IsWCG.of_proj {K : Set X} (hK : IsCompact (toWeakSpace ℝ X '' K))
    (hspan : closure (Submodule.span ℝ K : Set X) = univ) (M : Submodule ℝ X) (P : X →L[ℝ] X)
    (hPM : ∀ x, P x ∈ M) (hPfix : ∀ x ∈ M, P x = x) : IsWCG M := by
  set L : X →L[ℝ] M := P.codRestrict M hPM with hL
  refine ⟨L '' K, ?_, ?_⟩
  · have : toWeakSpace ℝ M '' (L '' K) = WeakSpace.map L '' (toWeakSpace ℝ X '' K) := by
      rw [image_image, image_image]; rfl
    rw [this]
    exact hK.image (WeakSpace.map L).continuous
  · refine eq_univ_of_forall fun m => ?_
    have hLm : L m = m := Subtype.ext (hPfix m m.2)
    have h1 : (m : X) ∈ closure (Submodule.span ℝ K : Set X) := hspan ▸ mem_univ _
    have h2 := image_closure_subset_closure_image L.continuous ⟨_, h1, rfl⟩
    rw [hLm] at h2
    refine closure_mono ?_ h2
    rintro _ ⟨y, hy, rfl⟩
    have : (L : X →ₗ[ℝ] M) y ∈ (Submodule.span ℝ K).map (L : X →ₗ[ℝ] M) :=
      Submodule.mem_map_of_mem hy
    rw [← Submodule.span_image] at this
    exact this

/-- The closure of `A`, as a subspace, has a dense subset of cardinality `#A`. -/
theorem exists_dense_card_le (A : Set X) (M : Submodule ℝ X) (hM : (M : Set X) = closure A) :
    ∃ s : Set M, Dense s ∧ #s ≤ #A := by
  refine ⟨Subtype.val ⁻¹' A, Metric.dense_iff.2 fun m r hr => ?_,
    Cardinal.mk_preimage_of_injective _ _ Subtype.val_injective⟩
  have hm : (m : X) ∈ closure A := hM ▸ m.2
  obtain ⟨a, ha, hma⟩ := Metric.mem_closure_iff.1 hm r hr
  have haM : a ∈ M := by rw [← SetLike.mem_coe, hM]; exact subset_closure ha
  exact ⟨⟨a, haM⟩, by rw [mem_ball, dist_comm]; exact hma, ha⟩

end Subspace

/-! ### The induction on the density -/

section Induction

/-- **2021 Theorem 5.5.16, p. 235 (preprint 5.43), by induction on the density**: every WCG Banach
space with a `C^k` bump and a dense subset of cardinality at most `κ` admits `C^k` partitions of
unity. -/
theorem admitsContDiffPartitionsOfUnity_of_wcg_card (k : ℕ∞) (κ : Cardinal.{u}) :
    ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X], IsWCG X →
      HasContDiffBump X k → (∃ s : Set X, Dense s ∧ #s ≤ κ) →
        AdmitsContDiffPartitionsOfUnity X k := by
  classical
  refine WellFoundedLT.induction (motive := fun κ : Cardinal.{u} => ∀ (X : Type u)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X], IsWCG X →
      HasContDiffBump X k → (∃ s : Set X, Dense s ∧ #s ≤ κ) →
        AdmitsContDiffPartitionsOfUnity X k) κ fun κ ih => ?_
  intro X _ _ _ hW hb ⟨s, hsd, hsκ⟩
  by_cases hκ : κ ≤ ℵ₀
  · -- the separable case
    have hsc : s.Countable := Set.countable_coe_iff.1 (Cardinal.mk_le_aleph0_iff.1 (hsκ.trans hκ))
    have : TopologicalSpace.SeparableSpace X := ⟨⟨s, hsc, hsd⟩⟩
    exact admitsContDiffPartitionsOfUnity_of_separable hb
  rw [not_le] at hκ
  obtain ⟨K, hK, hspan⟩ := hW
  set μ := κ.ord with hμ
  have hμlim : IsSuccLimit μ := Cardinal.isSuccLimit_ord hκ.le
  -- enumerate the dense set by the ordinals below `μ`
  have hsne : s.Nonempty := hsd.nonempty
  have : Nonempty s := hsne.to_subtype
  have hemb : Nonempty (s ↪ Iio μ) := by
    refine Cardinal.lift_mk_le'.1 ?_
    rw [Cardinal.mk_Iio_ordinal, hμ, Cardinal.card_ord, Cardinal.lift_id'.{u, u + 1}]
    exact Cardinal.lift_le.2 hsκ
  obtain ⟨j⟩ := hemb
  set g : s → Ordinal.{u} := fun y => (j y : Ordinal) with hg
  have hginj : Injective g := fun y y' h => j.injective (Subtype.ext h)
  set e : Ordinal.{u} → X := fun β => (invFun g β : s) with he
  have hd : Dense (segS e μ μ) := hsd.mono fun y hy => by
    refine ⟨g ⟨y, hy⟩, ⟨(j ⟨y, hy⟩).2, (j ⟨y, hy⟩).2⟩, ?_⟩
    simp only [he, leftInverse_invFun hginj ⟨y, hy⟩]
  set P := priP hK hspan e μ with hP
  have hPc : PRICont P := priP_cont hK hspan e μ
  -- the index set
  set ord : Shrink.{u} (Iio μ) → Ordinal.{u} := fun t => ((equivShrink (Iio μ)).symm t).1
    with hord
  have hordlt : ∀ t, ord t < μ := fun t => ((equivShrink (Iio μ)).symm t).2
  have hordinj : Injective ord := fun t t' h =>
    (equivShrink (Iio μ)).symm.injective (Subtype.ext h)
  set lev : Option (Shrink.{u} (Iio μ)) → Ordinal.{u} := fun i => i.elim 0 fun t => succ (ord t)
    with hlev
  have hlevlt : ∀ i, lev i < μ := by
    rintro (_ | t)
    · exact hμlim.bot_lt
    · exact hμlim.succ_lt (hordlt t)
  set Δ : Option (Shrink.{u} (Iio μ)) → X →L[ℝ] X :=
    fun i => i.elim (P 0) fun t => P (succ (ord t)) - P (ord t) with hΔ
  set Q : Option (Shrink.{u} (Iio μ)) → X →L[ℝ] X := fun i => P (lev i) with hQ
  have hPn : ∀ α, ‖P α‖ ≤ 1 := fun α => (priP_spec hK hspan e μ α).2.2
  have hC : ∀ i, ‖Δ i‖ ≤ 2 := by
    rintro (_ | t)
    · exact (hPn 0).trans one_le_two
    · exact (norm_sub_le _ _).trans (by linarith [hPn (succ (ord t)), hPn (ord t)])
  have hP1 : ∀ x, ∀ η > 0, {i | η < ‖Δ i x‖}.Finite := by
    intro x η hη
    have hfin := ((pri_finite hPc x hη).preimage hordinj.injOn).image some
    refine (hfin.insert none).subset ?_
    rintro (_ | t) ht
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ ⟨t, ht, rfl⟩
  have hP2 : ∀ x ≠ 0, ∀ η > 0, ∃ i, Δ i x ≠ 0 ∧ ‖x - Q i x‖ < η := by
    intro x hx η hη
    rcases pri_approx hPc (priP_top hK hspan e μ hd x) hη with h0 | ⟨α, hα, hne, hlt⟩
    · refine ⟨none, ?_, ?_⟩
      · change P 0 x ≠ 0; rw [h0]; exact hx
      · change ‖x - P 0 x‖ < η; rw [h0, sub_self, norm_zero]; exact hη
    · refine ⟨some (equivShrink (Iio μ) ⟨α, hα⟩), ?_, ?_⟩
      · have : ord (equivShrink (Iio μ) ⟨α, hα⟩) = α := by simp [hord]
        change (P (succ (ord _)) - P (ord _)) x ≠ 0
        rw [this]
        exact sub_ne_zero.2 hne
      · have : ord (equivShrink (Iio μ) ⟨α, hα⟩) = α := by simp [hord]
        change ‖x - P (succ (ord _)) x‖ < η
        rw [this]; exact hlt
  -- the bases on the pieces, by the induction hypothesis
  have hbase : ∀ i, ∃ (J : Type u) (g : J → X → ℝ), IsRelC0Base k (fun x => Q i x) g := by
    intro i
    have hp := isLPair_lcl (K := K) (segS e μ (lev i))
    set M := hp.sub with hM
    have hMset : (M : Set X) = closure (lclA K (segS e μ (lev i))) := rfl
    have hPM : ∀ x, Q i x ∈ M := fun x => (priP_spec hK hspan e μ (lev i)).1 x
    have hPfix : ∀ x ∈ M, Q i x = x := fun x hx => priP_fix hK hspan e μ hx
    have : CompleteSpace M := (isClosed_closure (s := lclA K (segS e μ (lev i)))).isComplete
      |>.completeSpace_coe
    set lam := max (lev i).card ℵ₀ with hlam
    have hlam : lam < κ := max_lt (Cardinal.lt_ord.1 (hlevlt i)) hκ
    have hcard : #(lclA K (segS e μ (lev i))) ≤ lam :=
      (card_lcl (le_max_right _ _) ((card_segS e μ (lev i)).trans (le_max_left _ _))).1
    obtain ⟨s', hs'd, hs'c⟩ := exists_dense_card_le _ M hMset
    have hPOU := ih lam hlam M (IsWCG.of_proj hK hspan M (Q i) hPM hPfix) (hb.submodule M)
      ⟨s', hs'd, hs'c.trans hcard⟩
    obtain ⟨J, g, hg⟩ := exists_isRelC0Base_of_admits hPOU
    refine ⟨J, _, (hg.comp ((Q i).codRestrict M hPM)).of_dist_eq fun x y => ?_⟩
    rfl
  choose J g hg using hbase
  obtain ⟨f, hf⟩ := isRelC0Base_glue hb Δ Q hC hP1 hP2 g hg
  exact admitsContDiffPartitionsOfUnity_of_isRelC0Base hf

/-- **2021 Theorem 5.5.16, p. 235 (preprint 5.43)** (Godefroy, Troyanski, Whitfield, Zizler): if
the Banach space `V` is weakly compactly generated and admits a `C^k`-bump function, then it admits
`C^k` partitions of unity. -/
theorem theorem_5_5_16 (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (k : ℕ∞) : GodefroyTroyanskiWhitfieldZizlerStatement V k := fun hW hb =>
  admitsContDiffPartitionsOfUnity_of_wcg_card k #V V hW hb ⟨univ, dense_univ, Cardinal.mk_univ.le⟩

end Induction

end Polyfold
