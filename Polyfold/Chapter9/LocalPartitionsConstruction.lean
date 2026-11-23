import Polyfold.Chapter9.LocalPartitionsExtension

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Remark 9.5.19, 2021 p. 451** (2017: Remark 9.8), point G.153.
Numbers and pages are the 2021 text's.

# Partitions of unity near a compact branched ep⁺-subgroupoid: the construction

## The text, paraphrased

Remark 9.5.19: in Theorems 9.5.17 and 9.5.18 it suffices to have partitions of unity on `supp Θ`,
and `supp Θ` is compact in the orbit space.

## What is formalized

* `LocalPart.exists_cutoff`: for a compact `Θ` and a saturated open `W ⊇ supp Θ`, a continuous
  function, constant on orbits, equal to `1` near `supp Θ` and with support in `W`.
* `EP.hasLocalPartitions`: every ep-groupoid has partitions of unity near its compact branched
  ep⁺-subgroupoids (`EP.HasLocalPartitions`), with no hypothesis on sc-smooth partitions of unity
  or bump functions of `X`.

## Reading

For `p ∈ supp Θ` and the open `N(p) ∋ p`, `LocalPart.exists_orbit_bump` gives `F_p ≥ 0`, constant
on orbits, with `F_p(p) = 1`, vanishing off a closed subset of `N(p)^*` and sc-smooth on a
saturated open `W_p ⊇ supp Θ`.  Finitely many `p_k` have `|supp Θ| ⊆ ⋃ π{F_{p_k} > 0}`; then
`W = ⋂ W_{p_k} ∩ {∑ F_{p_k} > 0}` and `β_k = F_{p_k} / ∑_j F_{p_j}`.  The cut-off is
`χ = θ ∘ ∑ c_k` for finitely many continuous orbit-constant `c_k ≥ 0` vanishing off `W` with
`∑ c_k > 1/2` on `supp Θ` and `θ(s) = max(0, min(1, 4s − 1))`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

open MPolyfold EpGroupoid

namespace LocalPart

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

/-- A function with equal values at the source and target of every morphism is constant on the
orbits. -/
theorem eq_of_π_eq {c : Obj → ℝ} (hc : ∀ φ : Mor, c (X.src φ) = c (X.tgt φ)) {y z : Obj}
    (h : X.π y = X.π z) : c y = c z := by
  obtain ⟨φ, hs, ht⟩ := (X.π_eq_π_iff).1 h
  rw [← hs, ← ht]
  exact hc φ

/-- **The continuous cut-off** (Remark 9.5.19, 2021 p. 451): for a functor `Θ` with `|supp Θ|`
compact and a saturated open `W ⊇ supp Θ` there is a continuous function `χ`, constant on the
orbits, with `χ = 1` near `supp Θ` and `supp χ ⊆ W`. -/
theorem exists_cutoff (hcpt : X.IsCompactBranched Θ) {W : Set Obj} (hW : IsOpen W)
    (hWs : X.IsSaturated W) (hΘW : supp Θ ⊆ W) :
    ∃ χ : Obj → ℝ, Continuous χ ∧ (∀ φ : Mor, χ (X.src φ) = χ (X.tgt φ)) ∧
      (∀ y ∈ supp Θ, ∀ᶠ z in 𝓝 y, χ z = 1) ∧ tsupport χ ⊆ W := by
  classical
  choose c hc hcinv hc0 hcp hcs using fun p : supp Θ => exists_orbit_cutoff X p.1 hW (hΘW p.2)
  have hcW : ∀ p, support (c p) ⊆ W := fun p => (hcs p).trans (le_of_eq hWs)
  have hUo : ∀ p, IsOpen {y | (1 / 2 : ℝ) < c p y} := fun p =>
    isOpen_lt continuous_const (hc p)
  obtain ⟨t, ht⟩ := (hcpt : IsCompact (X.orbitSupp Θ)).elim_finite_subcover
    (fun p => X.π '' {y | (1 / 2 : ℝ) < c p y}) (fun p => X.proposition_7_1_8 _ (hUo p)) (by
      rintro _ ⟨y, hy, rfl⟩
      refine mem_iUnion.2 ⟨⟨y, hy⟩, y, ?_, rfl⟩
      change (1 / 2 : ℝ) < c ⟨y, hy⟩ y
      rw [hcp]; norm_num)
  set s : Obj → ℝ := fun y => ∑ p ∈ t, c p y with hs
  have hsc : Continuous s := continuous_finsetSum _ fun p _ => hc p
  have hs0 : ∀ y, 0 ≤ s y := fun y => Finset.sum_nonneg fun p _ => hc0 p y
  refine ⟨fun y => max 0 (min 1 (4 * s y - 1)),
    continuous_const.max (continuous_const.min ((continuous_const.mul hsc).sub continuous_const)),
    fun φ => ?_, fun y hy => ?_, ?_⟩
  · have : s (X.src φ) = s (X.tgt φ) := Finset.sum_congr rfl fun p _ => hcinv p φ
    simp only [this]
  · obtain ⟨p, hpt, z, hz, hzy⟩ := mem_iUnion₂.1 (ht ⟨y, hy, rfl⟩)
    have hz' : (1 / 2 : ℝ) < c p z := hz
    have hy1 : (1 / 2 : ℝ) < s y := by
      rw [eq_of_π_eq (hcinv p) hzy] at hz'
      exact lt_of_lt_of_le hz' (Finset.single_le_sum (fun q _ => hc0 q y) hpt)
    filter_upwards [(isOpen_lt continuous_const hsc).mem_nhds hy1] with z' hz'
    have h1 : (1 / 2 : ℝ) < s z' := hz'
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  · have hcl : IsClosed {y | (1 / 4 : ℝ) ≤ s y} := isClosed_le continuous_const hsc
    refine (closure_minimal (fun y hy => ?_) hcl).trans fun y hy => ?_
    · change (1 / 4 : ℝ) ≤ s y
      by_contra h
      have h' : 4 * s y - 1 < 0 := by linarith [not_le.1 h]
      exact hy (by
        change max 0 (min 1 (4 * s y - 1)) = 0
        rw [max_eq_left ((min_le_right _ _).trans h'.le)])
    · have hy' : (1 / 4 : ℝ) ≤ s y := hy
      by_contra hyW
      have : s y = 0 := Finset.sum_eq_zero fun p _ => by
        by_contra hne
        exact hyW (hcW p hne)
      linarith

end LocalPart

namespace EP

open LocalPart

/-- **Partitions of unity near the compact branched ep⁺-subgroupoids exist** (Remark 9.5.19,
2021 p. 451): for every ep-groupoid `X`, every compact branched ep⁺-subgroupoid `Θ` and all open
neighbourhoods `N(x)` of the points `x ∈ supp Θ` there are a saturated open `W ⊇ supp Θ`,
finitely many functions `β_k`, sc-smooth on `W` and constant on orbits, with supports in
`N(x_k)^*` and `∑ β_k = 1` on `W`, and a continuous orbit-constant cut-off `χ` with `χ = 1` near
`supp Θ` and `supp χ ⊆ W`.  No sc-smooth partitions of unity or bump functions of `X` are
assumed. -/
theorem hasLocalPartitions (A : EP.{u}) : A.HasLocalPartitions := by
  intro Θ hΘ hcpt N hN
  classical
  choose F Wp C hWo hWs hΘW hsc hinv h0 h1 hC hFC hCN using fun x : supp Θ =>
    exists_orbit_bump hΘ x.2 (hN x.1 x.2).1 (hN x.1 x.2).2
  have hUo : ∀ x, IsOpen (Wp x ∩ F x ⁻¹' Ioi 0) := fun x =>
    (hsc x).continuousOn.isOpen_inter_preimage (hWo x) isOpen_Ioi
  obtain ⟨t, ht⟩ := (hcpt : IsCompact (A.X.orbitSupp Θ)).elim_finite_subcover
    (fun x => A.X.π '' (Wp x ∩ F x ⁻¹' Ioi 0)) (fun x => A.X.proposition_7_1_8 _ (hUo x)) (by
      rintro _ ⟨y, hy, rfl⟩
      refine mem_iUnion.2 ⟨⟨y, hy⟩, y, ⟨hΘW _ hy, ?_⟩, rfl⟩
      change 0 < F ⟨y, hy⟩ y
      rw [h1]; exact one_pos)
  set W0 : Set A.Obj := ⋂ k : t, Wp k.1 with hW0
  have hW0o : IsOpen W0 := isOpen_iInter_of_finite fun k => hWo k.1
  set S : A.Obj → ℝ := fun y => ∑ k : t, F k.1 y with hS
  have hSsc0 : A.X.PObj.IsScSmoothOn realPolyfold S W0 :=
    real_finsetSum Finset.univ hW0o fun k _ => (hsc k.1).mono hW0o (iInter_subset _ k)
  have hWopen : IsOpen (W0 ∩ S ⁻¹' Ioi 0) :=
    hSsc0.continuousOn.isOpen_inter_preimage hW0o isOpen_Ioi
  have hSsc : A.X.PObj.IsScSmoothOn realPolyfold S (W0 ∩ S ⁻¹' Ioi 0) :=
    hSsc0.mono hWopen inter_subset_left
  have hSinv : ∀ φ : A.Mor, S (A.X.src φ) = S (A.X.tgt φ) := fun φ =>
    Finset.sum_congr rfl fun k _ => hinv k.1 φ
  have hΘWW : supp Θ ⊆ W0 ∩ S ⁻¹' Ioi 0 := fun y hy => by
    refine ⟨mem_iInter.2 fun k => hΘW k.1 hy, ?_⟩
    obtain ⟨x, hxt, z, hz, hzy⟩ := mem_iUnion₂.1 (ht ⟨y, hy, rfl⟩)
    have hz' : 0 < F x z := hz.2
    rw [eq_of_π_eq (hinv x) hzy] at hz'
    exact lt_of_lt_of_le hz' (Finset.single_le_sum (f := fun k : t => F k.1 y)
      (fun k _ => h0 k.1 y) (Finset.mem_univ ⟨x, hxt⟩))
  have hWsat : A.X.IsSaturated (W0 ∩ S ⁻¹' Ioi 0) := A.X.isSaturated_iff.2 fun φ hφ =>
    ⟨mem_iInter.2 fun k => A.X.isSaturated_iff.1 (hWs k.1) φ (mem_iInter.1 hφ.1 k), by
      change 0 < S (A.X.tgt φ)
      rw [← hSinv φ]; exact hφ.2⟩
  obtain ⟨χ, hχc, hχinv, hχ1, hχW⟩ := exists_cutoff hcpt hWopen hWsat hΘWW
  exact ⟨{
    W := W0 ∩ S ⁻¹' Ioi 0
    isOpen_W := hWopen
    isSaturated_W := hWsat
    supp_subset_W := hΘWW
    κ := t
    pt := fun k => k.1.1
    pt_mem := fun k => k.1.2
    β := fun k y => F k.1 y * (S y)⁻¹
    isScSmoothOn_β := fun k => real_mul ((hsc k.1).mono hWopen fun y hy =>
      mem_iInter.1 hy.1 k) (real_inv hSsc fun y hy => hy.2)
    β_src_eq_tgt := fun k φ _ => by rw [hinv k.1 φ, hSinv φ]
    closure_subset := fun k y hy => hCN k.1 (closure_minimal (fun z hz => hFC k.1 fun h0' =>
      hz.2 (by rw [h0', zero_mul])) (hC k.1) hy.2)
    sum_β := fun y hy => by
      have hpos : 0 < S y := hy.2
      rw [← Finset.sum_mul]
      exact mul_inv_cancel₀ hpos.ne'
    χ := χ
    continuous_χ := hχc
    χ_src_eq_tgt := hχinv
    χ_eventually_eq_one := hχ1
    tsupport_χ_subset := hχW }⟩

end EP

end Polyfold
