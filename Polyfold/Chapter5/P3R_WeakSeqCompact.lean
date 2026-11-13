import Polyfold.Chapter5.PartitionsOfUnity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.1–§5.2 (pp. 207–216):
the functional analysis behind reflexive `(0, 1)`-fibres (Definition 5.1.4) and mixed convergence
(Lemma 5.1.5, Definition 5.1.6, Proposition 5.2.7).

# Weak sequential compactness in reflexive Banach spaces

The text uses, without comment, that a bounded sequence in a reflexive Banach space has a weakly
convergent subsequence (proof of Proposition 5.2.7: "we may assume after perhaps taking a
subsequence that `h_k` is mixed convergent"), and that a weakly convergent sequence is mapped by
the compact inclusion `F₁ → F₀` to a norm convergent one (proof of Lemma 5.1.5: "`h_k ⇀ h` in `F₁`
implies `h_k → h` in `F₀`").  Mathlib has the sequential Banach–Alaoglu theorem only for the dual
of a separable space; this file proves what the text needs.

## What is formalized

* `Polyfold.IsReflexive F` (the existing definition of `PartitionsOfUnity.lean`, §5.5): the
  canonical map `F → F**` is onto.  `isReflexive_of_finiteDimensional`: finite-dimensional spaces
  are reflexive (Hilbert spaces: the existing `isReflexive_of_hilbert`).
* `Polyfold.WeakTendsto u h`: `g(u_k) → g(h)` for every `g ∈ F*`, with `WeakTendsto.unique`,
  `WeakTendsto.map`, `WeakTendsto.comp_strictMono`, `weakTendsto_iff_shift`,
  `WeakTendsto.congr_eventually`, `Tendsto.weakTendsto`.
* `WeakTendsto.exists_bound` (uniform boundedness: weakly convergent sequences are bounded).
* `WeakTendsto.eventually_norm_gt` (weak lower semicontinuity of the norm:
  `‖h‖ - ε < ‖u_k‖` eventually).
* **`exists_subseq_weakTendsto`** (the infrastructure item (b′) of the Part III plan): in a
  reflexive `F` every bounded sequence has a weakly convergent subsequence.  Proof: the closed
  span `M` of the sequence is separable; countably many norm-one functionals `g_d` norm the
  points of `M`; a diagonal subsequence (a compact metrizable cube `∏_d [-C, C]`) makes every
  `g_d(u_k)` converge; the images in the bidual lie in a weak*-compact ball (Banach–Alaoglu);
  every weak* cluster point is `J(p)` with `p ∈ M` (reflexivity and Hahn–Banach), and the `g_d`
  determine it; a sequence in a compact set with one cluster point converges.
  `exists_subseq_weakTendsto_of_eventually`: the same with a bound that holds eventually.
* `WeakTendsto.tendsto_of_isCompactOperator`: a compact operator maps weakly convergent sequences
  to norm convergent ones.
* `weakTendsto_of_bounded_of_tendsto`: in a reflexive `F`, a bounded sequence whose image under an
  injective bounded operator converges to the image of `h` converges weakly to `h`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

section WeakSeq

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Weak convergence** of a sequence: `g(u_k) → g(h)` for every bounded linear functional `g`
(the text's `h_k ⇀ h`). -/
def WeakTendsto (u : ℕ → F) (h : F) : Prop :=
  ∀ g : StrongDual ℝ F, Tendsto (fun k => g (u k)) atTop (𝓝 (g h))

/-- Norm convergence implies weak convergence. -/
lemma _root_.Filter.Tendsto.weakTendsto {u : ℕ → F} {h : F} (hu : Tendsto u atTop (𝓝 h)) :
    WeakTendsto u h := fun g => (g.continuous.tendsto h).comp hu

lemma weakTendsto_const (h : F) : WeakTendsto (fun _ => h) h := fun _ => tendsto_const_nhds

/-- Weak limits are unique (Hahn–Banach). -/
lemma WeakTendsto.unique {u : ℕ → F} {h h' : F} (hh : WeakTendsto u h) (hh' : WeakTendsto u h') :
    h = h' :=
  (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun g => tendsto_nhds_unique (hh g) (hh' g)

/-- Bounded operators preserve weak convergence. -/
lemma WeakTendsto.map {u : ℕ → F} {h : F} (hu : WeakTendsto u h) (A : F →L[ℝ] G) :
    WeakTendsto (fun k => A (u k)) (A h) := fun g => hu (g.comp A)

lemma WeakTendsto.comp_strictMono {u : ℕ → F} {h : F} (hu : WeakTendsto u h) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) : WeakTendsto (u ∘ φ) h := fun g => (hu g).comp hφ.tendsto_atTop

lemma WeakTendsto.congr_eventually {u v : ℕ → F} {h : F} (hu : WeakTendsto u h)
    (huv : ∀ᶠ k in atTop, u k = v k) : WeakTendsto v h := fun g =>
  (hu g).congr' (huv.mono fun k hk => by rw [hk])

lemma weakTendsto_iff_shift {u : ℕ → F} {h : F} (n : ℕ) :
    WeakTendsto (fun k => u (k + n)) h ↔ WeakTendsto u h := by
  refine forall_congr' fun g => ?_
  exact tendsto_add_atTop_iff_nat (f := fun k => g (u k)) n

/-- **Weakly convergent sequences are bounded** (uniform boundedness for the maps
`J(u_k) ∈ F**` on the Banach space `F*`). -/
theorem WeakTendsto.exists_bound {u : ℕ → F} {h : F} (hu : WeakTendsto u h) :
    ∃ C, 0 ≤ C ∧ ∀ k, ‖u k‖ ≤ C := by
  set J := NormedSpace.inclusionInDoubleDual ℝ F
  have hpt : ∀ g : StrongDual ℝ F, ∃ C, ∀ k, ‖J (u k) g‖ ≤ C := by
    intro g
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ (hu g))
    exact ⟨C, fun k => by rw [NormedSpace.dual_def]; exact hC _ ⟨k, rfl⟩⟩
  obtain ⟨C', hC'⟩ := banach_steinhaus hpt
  refine ⟨max C' 0, le_max_right _ _, fun k => ?_⟩
  refine NormedSpace.norm_le_dual_bound ℝ (u k) (le_max_right _ _) fun g => ?_
  calc ‖g (u k)‖ = ‖J (u k) g‖ := by rw [NormedSpace.dual_def]
    _ ≤ ‖J (u k)‖ * ‖g‖ := (J (u k)).le_opNorm g
    _ ≤ max C' 0 * ‖g‖ :=
        mul_le_mul_of_nonneg_right ((hC' k).trans (le_max_left _ _)) (norm_nonneg _)

/-- **Weak lower semicontinuity of the norm**: `‖h‖ - ε < ‖u_k‖` for all large `k`. -/
theorem WeakTendsto.eventually_norm_gt {u : ℕ → F} {h : F} (hu : WeakTendsto u h) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ k in atTop, ‖h‖ - ε < ‖u k‖ := by
  obtain ⟨g, hg1, hgh⟩ := exists_dual_vector'' ℝ h
  have hgh' : g h = ‖h‖ := by simpa using hgh
  have hlim := hu g
  rw [hgh'] at hlim
  filter_upwards [(tendsto_order.1 hlim).1 _ (sub_lt_self ‖h‖ hε)] with k hk
  calc (‖h‖ - ε : ℝ) < g (u k) := hk
    _ ≤ ‖g (u k)‖ := Real.le_norm_self _
    _ ≤ ‖g‖ * ‖u k‖ := g.le_opNorm _
    _ ≤ 1 * ‖u k‖ := mul_le_mul_of_nonneg_right hg1 (norm_nonneg _)
    _ = ‖u k‖ := one_mul _

/-- A cluster point of a constant sequence is that constant (in a Hausdorff space). -/
private lemma mapClusterPt_const_eq {α : Type*} [TopologicalSpace α] [T2Space α] {a b : α}
    (h : MapClusterPt b atTop (fun _ : ℕ => a)) : b = a := by
  exact eq_of_nhds_neBot (ClusterPt.mono h (tendsto_const_nhds (x := a) (f := (atTop : Filter ℕ))))

/-- A cluster point of a sequence with a limit is the limit. -/
private lemma mapClusterPt_eq_of_tendsto {α : Type*} [TopologicalSpace α] [T2Space α]
    {v : ℕ → α} {a b : α} (h : MapClusterPt b atTop v) (hv : Tendsto v atTop (𝓝 a)) : b = a :=
  eq_of_nhds_neBot (ClusterPt.mono h hv)

/-- **Bounded sequences in a reflexive space have weakly convergent subsequences** (the
infrastructure item (b′) of the Part III plan; used in the proofs of Lemma 5.1.5 and Proposition
5.2.7 of the 2021 text). -/
theorem exists_subseq_weakTendsto (hF : IsReflexive F) {u : ℕ → F} {C : ℝ}
    (hu : ∀ k, ‖u k‖ ≤ C) : ∃ h : F, ∃ φ : ℕ → ℕ, StrictMono φ ∧ WeakTendsto (u ∘ φ) h := by
  classical
  -- the closed span `M` of the sequence and a countable set `D` dense in it
  set M : Submodule ℝ F := (Submodule.span ℝ (range u)).topologicalClosure with hMdef
  have hMc : IsClosed (M : Set F) := Submodule.isClosed_topologicalClosure _
  have huM : ∀ k, u k ∈ M := fun k =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨k, rfl⟩)
  have hsep : TopologicalSpace.IsSeparable (M : Set F) := by
    have h1 : TopologicalSpace.IsSeparable (Submodule.span ℝ (range u) : Set F) :=
      (TopologicalSpace.IsSeparable.span (countable_range u).isSeparable)
    have h2 := h1.closure
    change TopologicalSpace.IsSeparable
      ((Submodule.span ℝ (range u)).topologicalClosure : Set F)
    rw [Submodule.topologicalClosure_coe]; exact h2
  obtain ⟨D, hDc, hMD⟩ := hsep
  -- norm-one functionals attaining the norm at the points of `D`
  have hg : ∀ d : D, ∃ g : StrongDual ℝ F, ‖g‖ ≤ 1 ∧ g d = ‖(d : F)‖ := fun d =>
    exists_dual_vector'' ℝ (d : F)
  choose g hg1 hgd using hg
  have : Countable D := hDc.to_subtype
  -- a diagonal subsequence along which every `g_d(u_k)` converges
  set v : ℕ → (D → ℝ) := fun k d => g d (u k) with hvdef
  have hvK : ∀ k, v k ∈ univ.pi fun _ : D => Metric.closedBall (0 : ℝ) C := by
    intro k d _
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖g d (u k)‖ ≤ ‖g d‖ * ‖u k‖ := (g d).le_opNorm _
      _ ≤ 1 * C := mul_le_mul (hg1 d) (hu k) (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  obtain ⟨L, -, φ, hφ, hvL⟩ :=
    (isCompact_univ_pi fun _ : D => isCompact_closedBall (0 : ℝ) C).tendsto_subseq hvK
  have hgL : ∀ d : D, Tendsto (fun k => g d (u (φ k))) atTop (𝓝 (L d)) := fun d =>
    tendsto_pi_nhds.1 hvL d
  -- the images in the weak-* bidual lie in a compact ball
  set J := NormedSpace.inclusionInDoubleDual ℝ F with hJ
  set W : ℕ → WeakDual ℝ (StrongDual ℝ F) := fun k => StrongDual.toWeakDual (J (u (φ k)))
    with hWdef
  set S : Set (WeakDual ℝ (StrongDual ℝ F)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ (StrongDual ℝ F)) C with hS
  have hSc : IsCompact S := WeakDual.isCompact_closedBall 0 C
  have hWS : ∀ k, W k ∈ S := fun k => by
    change J (u (φ k)) ∈ Metric.closedBall 0 C
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (NormedSpace.double_dual_bound ℝ F _).trans (hu _)
  have hWapp : ∀ k (f : StrongDual ℝ F), W k f = f (u (φ k)) := fun k f => rfl
  -- every cluster point is `J p` with `p ∈ M`, and is determined by the values `L d`
  have hclus : ∀ Φ : WeakDual ℝ (StrongDual ℝ F), MapClusterPt Φ atTop W →
      ∃ p ∈ M, WeakDual.toStrongDual Φ = J p ∧ ∀ d : D, g d p = L d := by
    intro Φ hΦ
    obtain ⟨p, hp⟩ := hF (WeakDual.toStrongDual Φ)
    have hev : ∀ f : StrongDual ℝ F, MapClusterPt (f p) atTop (fun k => f (u (φ k))) := by
      intro f
      have h1 := hΦ.continuousAt_comp (WeakDual.eval_continuous f).continuousAt
      have e : (Φ : WeakDual ℝ (StrongDual ℝ F)) f = f p := by
        change WeakDual.toStrongDual Φ f = f p
        rw [← hp]; rfl
      rw [e] at h1
      exact h1
    refine ⟨p, ?_, hp.symm, fun d => mapClusterPt_eq_of_tendsto (hev (g d)) (hgL d)⟩
    by_contra hpM
    obtain ⟨f, r, hfM, hrf⟩ :=
      geometric_hahn_banach_closed_point (M.convex) hMc hpM
    have hf0 : ∀ a ∈ M, f a = 0 := by
      intro a ha
      by_contra hne
      have := hfM (((r + 1) / f a) • a) (M.smul_mem _ ha)
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
      linarith
    have h1 : MapClusterPt (f p) atTop (fun k => f (u (φ k))) := hev f
    have h2 : (fun k => f (u (φ k))) = fun _ => (0 : ℝ) := funext fun k => hf0 _ (huM _)
    rw [h2] at h1
    have h3 := mapClusterPt_const_eq h1
    have h4 := hfM 0 M.zero_mem
    rw [map_zero] at h4
    linarith
  -- a cluster point exists
  obtain ⟨Φ₀, -, hΦ₀⟩ := hSc.exists_mapClusterPt (f := atTop) (u := W)
    (tendsto_principal.2 (Eventually.of_forall hWS))
  obtain ⟨p₀, hp₀M, hp₀, hp₀L⟩ := hclus Φ₀ hΦ₀
  -- it is the only one
  have huniq : ∀ Φ ∈ S, MapClusterPt Φ atTop W → Φ = Φ₀ := by
    intro Φ _ hΦ
    obtain ⟨p, hpM, hp, hpL⟩ := hclus Φ hΦ
    have hz : p - p₀ = 0 := by
      have hzM : p - p₀ ∈ M := M.sub_mem hpM hp₀M
      have hgz : ∀ d : D, g d (p - p₀) = 0 := fun d => by rw [map_sub, hpL, hp₀L, sub_self]
      refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
      obtain ⟨d, hdD, hdist⟩ := Metric.mem_closure_iff.1 (hMD hzM) (ε / 2) (half_pos hε)
      set d' : D := ⟨d, hdD⟩
      have hkey : ‖(d : F)‖ = g d' (d - (p - p₀)) := by
        rw [map_sub, hgz d', sub_zero]; exact (hgd d').symm
      have hle : ‖(d : F)‖ ≤ ‖d - (p - p₀)‖ := by
        rw [hkey]
        calc g d' (d - (p - p₀)) ≤ ‖g d' (d - (p - p₀))‖ := Real.le_norm_self _
          _ ≤ ‖g d'‖ * ‖d - (p - p₀)‖ := (g d').le_opNorm _
          _ ≤ 1 * ‖d - (p - p₀)‖ := mul_le_mul_of_nonneg_right (hg1 d') (norm_nonneg _)
          _ = _ := one_mul _
      have hd2 : ‖d - (p - p₀)‖ < ε / 2 := by rw [norm_sub_rev, ← dist_eq_norm]; exact hdist
      calc ‖p - p₀‖ ≤ ‖(p - p₀) - d‖ + ‖(d : F)‖ := by
            have := norm_add_le ((p - p₀) - d) (d : F)
            rwa [sub_add_cancel] at this
        _ ≤ ‖d - (p - p₀)‖ + ‖d - (p - p₀)‖ := by rw [norm_sub_rev]; exact add_le_add le_rfl hle
        _ ≤ 0 + ε := by linarith
    have hpp : p = p₀ := sub_eq_zero.1 hz
    apply WeakDual.toStrongDual.injective
    rw [hp, hp₀, hpp]
  have hlim : Tendsto W atTop (𝓝 Φ₀) :=
    hSc.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall hWS) huniq
  refine ⟨p₀, φ, hφ, fun f => ?_⟩
  have h1 := ((WeakDual.eval_continuous f).tendsto Φ₀).comp hlim
  have e : (Φ₀ : WeakDual ℝ (StrongDual ℝ F)) f = f p₀ := by
    change WeakDual.toStrongDual Φ₀ f = f p₀
    rw [hp₀]; rfl
  rw [e] at h1
  exact h1

/-- (b′) with a bound that holds eventually. -/
theorem exists_subseq_weakTendsto_of_eventually (hF : IsReflexive F) {u : ℕ → F} {C : ℝ}
    (hu : ∀ᶠ k in atTop, ‖u k‖ ≤ C) :
    ∃ h : F, ∃ φ : ℕ → ℕ, StrictMono φ ∧ WeakTendsto (u ∘ φ) h := by
  obtain ⟨n, hn⟩ := eventually_atTop.1 hu
  obtain ⟨h, φ, hφ, hw⟩ :=
    exists_subseq_weakTendsto hF (u := fun k => u (k + n)) (C := C) fun k => hn _ (by omega)
  exact ⟨h, fun k => φ k + n, fun a b hab => by simpa using hφ hab, hw⟩

/-- **A compact operator maps weakly convergent sequences to norm convergent ones** (the step
"`h_k ⇀ h` in `F₁` implies `h_k → h` in `F₀`" of the proof of Lemma 5.1.5). -/
theorem WeakTendsto.tendsto_of_isCompactOperator {u : ℕ → F} {h : F} (hu : WeakTendsto u h)
    {T : F →L[ℝ] G} (hT : IsCompactOperator T) :
    Tendsto (fun k => T (u k)) atTop (𝓝 (T h)) := by
  obtain ⟨C, hC0, hC⟩ := hu.exists_bound
  obtain ⟨K, hK, hKsub⟩ := hT.image_closedBall_subset_compact C
  have hmem : ∀ k, T (u k) ∈ K := fun k =>
    hKsub ⟨u k, by rw [Metric.mem_closedBall, dist_zero_right]; exact hC k, rfl⟩
  refine hK.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall hmem) fun y _ hy => ?_
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun g => ?_
  have h1 := hy.continuousAt_comp g.continuous.continuousAt
  exact mapClusterPt_eq_of_tendsto h1 ((hu.map T) g)

/-- **Bounded sequences in a reflexive space with a convergent image under an injective bounded
operator converge weakly** (the last step of the proof of Lemma 5.1.5: "the boundedness of `(h'_k)`
in `F'₁` and the convergence on level 0 implies the weak convergence `h'_k ⇀ h'` in `F'₁`"). -/
theorem weakTendsto_of_bounded_of_tendsto (hF : IsReflexive F) {ι : F →L[ℝ] G}
    (hι : Injective ι) {u : ℕ → F} {C : ℝ} (hu : ∀ᶠ k in atTop, ‖u k‖ ≤ C) {h : F}
    (hlim : Tendsto (fun k => ι (u k)) atTop (𝓝 (ι h))) : WeakTendsto u h := by
  intro g
  by_contra hng
  obtain ⟨s, hs, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.1 hng
  obtain ⟨ψ, hψ, hψs⟩ := extraction_of_frequently_atTop hfreq
  have hbd : ∀ᶠ k in atTop, ‖(u ∘ ψ) k‖ ≤ C := hψ.tendsto_atTop.eventually hu
  obtain ⟨h', φ, hφ, hw⟩ := exists_subseq_weakTendsto_of_eventually hF hbd
  have h1 : WeakTendsto (fun k => ι ((u ∘ ψ ∘ φ) k)) (ι h) :=
    (hlim.comp (hψ.comp hφ).tendsto_atTop).weakTendsto
  have h2 := hw.map ι
  have hh : h' = h := hι (h2.unique h1)
  rw [hh] at hw
  have h3 := (hw g).eventually (isOpen_iff_mem_nhds.1 (isOpen_interior) _
    (mem_interior_iff_mem_nhds.2 hs))
  obtain ⟨k, hk⟩ := h3.exists
  exact hψs (φ k) (interior_subset hk)

/-- **Finite-dimensional spaces are reflexive.** -/
theorem isReflexive_of_finiteDimensional [FiniteDimensional ℝ F] : IsReflexive F := by
  set J := NormedSpace.inclusionInDoubleDual ℝ F
  have hinj : Injective J := (NormedSpace.inclusionInDoubleDualLi (E := F) ℝ).injective
  have hd : Module.finrank ℝ F = Module.finrank ℝ (StrongDual ℝ (StrongDual ℝ F)) := by
    have e1 : Module.finrank ℝ (StrongDual ℝ F) = Module.finrank ℝ F := by
      rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := F) (F' := ℝ)).finrank_eq]
      exact Subspace.dual_finrank_eq
    have e2 : Module.finrank ℝ (StrongDual ℝ (StrongDual ℝ F)) =
        Module.finrank ℝ (StrongDual ℝ F) := by
      rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := StrongDual ℝ F)
        (F' := ℝ)).finrank_eq]
      exact Subspace.dual_finrank_eq
    rw [e2, e1]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd (f := J.toLinearMap)).1 hinj

end WeakSeq

end Polyfold
