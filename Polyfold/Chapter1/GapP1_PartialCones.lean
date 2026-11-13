import Polyfold.Chapter1.ChainRule

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §1.1, Remark 1.1.17,
pp. 10–11 (preprint Remark 1.15).

# Partial cones in place of partial quadrants

## The text, paraphrased

Instead of a partial quadrant one may take a closed convex partial cone `P ⊆ E` (`λP ⊆ P` for
`λ ≥ 0`) with nonempty interior; for `U` open in `P`, sc¹ is defined as in Definition 1.1.15, the
tangent map lives on `TP = P¹ ⊕ E`, again a closed cone with nonempty interior.  Many results
should carry over.

## What is formalized

The library states §§1.2–1.3 for *sc-domains* (`IsScDomain`, row V1.27: every level `U_m` is
open-in-convex with unique derivatives), and the definition of sc¹ (`IsSc1`) is made for any
`U ⊆ E₀`.  So the content of the remark is that relatively open subsets of partial cones are
sc-domains, and that `T` preserves partial cones:

* `IsPartialCone E P`: closed, convex, `λP ⊆ P` for `λ ≥ 0`, nonempty interior.
* `IsPartialCone.isScDomain`: `U = O ∩ P` with `O` open is an sc-domain.  (Closedness and the cone
  property are not needed: convexity and nonempty interior suffice.)
* `IsPartialCone.tangentSet`: `TP = P₁ × E₀` is a partial cone in `TE`.
* `IsPartialQuadrant.isPartialCone`: partial quadrants are partial cones.
* `remark_1_1_17_chainRule`: the chain rule (Theorem 1.3.1) for relatively open subsets of
  partial cones, as an example of a result that carries over; every theorem of §§1.2–1.3 stated
  for sc-domains applies in the same way.
-/

open Set Topology

namespace Polyfold

variable {E : ScBanach}

/-- A **closed convex partial cone with nonempty interior** (Remark 1.1.17). -/
structure IsPartialCone (E : ScBanach) (P : Set (E 0)) : Prop where
  isClosed : IsClosed P
  convex : Convex ℝ P
  smul_mem : ∀ c : ℝ, 0 ≤ c → ∀ x ∈ P, c • x ∈ P
  interior_nonempty : (interior P).Nonempty

/-- An open nonempty subset of `E₀` meets the image of every level `E_m`. -/
lemma exists_toBase_mem_of_isOpen {B : Set (E 0)} (hB : IsOpen B) (hne : B.Nonempty) (m : ℕ) :
    ∃ y : E m, E.toBase m y ∈ B := by
  obtain ⟨x, hxB, hxs⟩ := (E.dense_smooth 0).inter_open_nonempty B hB hne
  obtain ⟨y, hy⟩ := E.mem_smooth_iff.1 hxs m
  exact ⟨y, hy ▸ hxB⟩

/-- A subset of `E₀` with nonempty interior has level sets with nonempty interior. -/
lemma interior_lvlSet_nonempty_of_interior {P : Set (E 0)} (hP : (interior P).Nonempty) (m : ℕ) :
    (interior (E.lvlSet P m)).Nonempty := by
  obtain ⟨y, hy⟩ := exists_toBase_mem_of_isOpen isOpen_interior hP m
  refine ⟨y, ?_⟩
  have hopen : IsOpen (E.toBase m ⁻¹' interior P) :=
    isOpen_interior.preimage (E.toBase m).continuous
  exact interior_maximal (s := E.lvlSet P m) (fun z hz => interior_subset (s := P) hz) hopen hy

namespace IsPartialCone

variable {P : Set (E 0)}

/-- **Remark 1.1.17**: a relatively open subset `U = O ∩ P` of a convex set `P` with nonempty
interior (in particular of a partial cone) is an sc-domain. -/
theorem isScDomain_of_convex (hc : Convex ℝ P) (hint : (interior P).Nonempty) {O : Set (E 0)}
    (hO : IsOpen O) : IsScDomain E (O ∩ P) where
  relOpenConvex m := ⟨E.lvlSet O m, E.lvlSet P m, E.isOpen_lvlSet hO m,
    hc.linear_preimage (E.toBase m : E m →ₗ[ℝ] E 0), E.lvlSet_inter O P m⟩
  uniqueDiffWithinAt m x hx := by
    rw [E.lvlSet_inter] at hx ⊢
    have hcm : Convex ℝ (E.lvlSet P m) := hc.linear_preimage (E.toBase m : E m →ₗ[ℝ] E 0)
    have hu := uniqueDiffOn_convex hcm (interior_lvlSet_nonempty_of_interior hint m) x hx.2
    rw [inter_comm]
    exact hu.inter ((E.isOpen_lvlSet hO m).mem_nhds hx.1)

/-- **Remark 1.1.17**: a relatively open subset of a partial cone is an sc-domain (the property
of the text's tuples used in §§1.2–1.3, row V1.27). -/
theorem isScDomain (hP : IsPartialCone E P) {O : Set (E 0)} (hO : IsOpen O) :
    IsScDomain E (O ∩ P) :=
  isScDomain_of_convex hP.convex hP.interior_nonempty hO

/-- **Remark 1.1.17**: `TP = P₁ ⊕ E₀` is a closed convex partial cone with nonempty interior in
`TE`. -/
theorem tangentSet (hP : IsPartialCone E P) : IsPartialCone E.tangent (E.tangentSet P) := by
  have heq : E.tangentSet P = (E.lvlSet P 1 : Set (E 1)) ×ˢ (univ : Set (E 0)) := by
    ext p; exact ⟨fun h => ⟨h, mem_univ _⟩, fun h => h.1⟩
  have hc1 : Convex ℝ (E.lvlSet P 1) := hP.convex.linear_preimage (E.toBase 1 : E 1 →ₗ[ℝ] E 0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]
    exact (hP.isClosed.preimage (E.toBase 1).continuous).prod isClosed_univ
  · rw [heq]; exact hc1.prod convex_univ
  · intro c hc p hp
    change E.toBase 1 (c • p).1 ∈ P
    rw [Prod.smul_fst, map_smul]
    exact hP.smul_mem c hc _ hp
  · rw [heq, interior_prod_eq, interior_univ]
    obtain ⟨y, hy⟩ := interior_lvlSet_nonempty_of_interior hP.interior_nonempty 1
    exact ⟨(y, 0), hy, mem_univ _⟩

end IsPartialCone

/-- Partial quadrants are partial cones. -/
theorem IsPartialQuadrant.isPartialCone {C : Set (E 0)} (hC : IsPartialQuadrant E C) :
    IsPartialCone E C := by
  obtain ⟨n, W, T, rfl⟩ := hC
  have hcont : ∀ i, Continuous fun x : E 0 => (T 0 x).1 i := fun i =>
    (continuous_apply i).comp (continuous_fst.comp (T 0).continuous)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : T 0 ⁻¹' quadrant n W 0 = ⋂ i, {x | 0 ≤ (T 0 x).1 i} := by ext; simp [quadrant]
    rw [this]
    exact isClosed_iInter fun i => isClosed_le continuous_const (hcont i)
  · exact (quadrant_convex n W 0).linear_preimage (T 0 : E 0 →ₗ[ℝ] _)
  · intro c hc x hx i
    simp only [map_smul, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hc (hx i)
  · refine ⟨(T 0).symm (fun _ => 1, 0), ?_⟩
    have hopen : IsOpen (⋂ i, {x : E 0 | 0 < (T 0 x).1 i}) :=
      isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (hcont i)
    refine interior_maximal (fun x hx i => (mem_iInter.1 hx i).le) hopen ?_
    exact mem_iInter.2 fun i => by simp

/-- **Remark 1.1.17, the chain rule for partial cones** (Theorem 1.3.1 with partial cones in place
of partial quadrants): for `U ⊆ P`, `V ⊆ Q` relatively open in partial cones and sc¹ maps
`f : U → V`, `g : V → G`, the composite `g ∘ f` is sc¹ and `T(g ∘ f) = Tg ∘ Tf` on `TU`. -/
theorem remark_1_1_17_chainRule {F G : ScBanach} {P : Set (E 0)} {Q : Set (F 0)}
    (hP : IsPartialCone E P) (hQ : IsPartialCone F Q) {O : Set (E 0)} {O' : Set (F 0)}
    (hO : IsOpen O) (hO' : IsOpen O') {f : E 0 → F 0} {g : F 0 → G 0}
    (hf : IsSc1 (O ∩ P) f) (hg : IsSc1 (O' ∩ Q) g) (hfV : MapsTo f (O ∩ P) (O' ∩ Q)) :
    IsSc1 (O ∩ P) (g ∘ f) ∧
      EqOn (tangentMap (O ∩ P) (g ∘ f)) (tangentMap (O' ∩ Q) g ∘ tangentMap (O ∩ P) f)
        (E.tangentSet (O ∩ P)) :=
  theorem_1_3_1' (hP.isScDomain hO) (hQ.isScDomain hO') hf hg hfV

end Polyfold
