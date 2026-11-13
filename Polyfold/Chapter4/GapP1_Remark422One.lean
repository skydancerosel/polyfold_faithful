import Polyfold.Chapter4.GapP1_Remark422
import Polyfold.Chapter9.BoundaryPositionConverse

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.2,
**Remark 4.2.2** (p. 184; preprint Remark 4.14), the sentence on the points with `d_A(a) = 1`.

# Near the points with `d_A = 1` a smooth submanifold is a manifold with boundary

## The text

"Near points with `d_A(a) = 1` it [`A`] has a natural structure as a smooth manifold with
boundary."  No proof is given.

## What is formalized

* `MPolyfold.hasCornerStructure_of_degIndex_le_one`: an M-polyfold `X` with `X₀ = X_∞`,
  `1₀¹ : X → X¹` sc-smooth and `d_X ≤ 1` everywhere has a corner structure (Definition 4.1.1).
  No tameness.
* `MPolyfold.IsSmoothSubmanifold.hasCornerStructure_of_degIndex_le_one`: the same for the induced
  structure of a smooth finite-dimensional submanifold `A` with `d_A ≤ 1`.
* `MPolyfold.remark_4_2_2_dA_one`: the open piece `{d_A ≤ 1}` of a smooth finite-dimensional
  submanifold `A` is a smooth submanifold of `A` whose induced structure has a corner structure
  with degeneracy index `≤ 1`: a smooth manifold with boundary.  `remark_4_2_2_dA_one_near`: the
  same near one point with `d_A(a) ≤ 1` (in particular `d_A(a) = 1`).

## The proof

By Theorem 4.1.2 (`hasCornerStructure_of_centred`) it suffices to find, at every `x`, a chart
centred at `x` whose tangent space `N = T₀O` is in good position to the partial quadrant.  Take a
chart `φ` realizing `d_X(x)` and re-centre it at `e = φ(x)` (`MChart.recentre`); the new partial
quadrant is `C_e`, cut out by the `d_X(x) ≤ 1` coordinates vanishing at `e`.
* `d_X(x) = 0`: `C_e = E`, and every subspace is in good position (`isInGoodPosition_univ`).
* `d_X(x) = 1`, `C_e = {λ ≥ 0}`: if `λ` does not vanish on `N`, then `N` is in good position
  with a complement inside `ker λ` (`isInGoodPosition_halfSpace`).  If `λ` vanishes on `N`, then
  `T₀O ⊆ E_0` and the model `O` is near `0` the graph over an open subset of `N`, a chart without
  boundary, so `d_X(x) = 0` (`degIndex_eq_zero_of_isReducedTangentAt`, the proof of 2021
  Lemma 9.2.13), a contradiction.
-/

open Set Filter Topology Function

universe u

namespace Polyfold

section HalfSpace

variable {E : ScBanach}

/-- **A subspace on which a functional `ℓ` does not vanish is in good position to the half-space
`{ℓ ≥ 0}`** (Definition 3.1.24): the interior of `N ∩ {ℓ ≥ 0}` in `N` contains `{ℓ > 0} ∩ N`,
and a complement `P ⊆ ker ℓ` of `N` is good with every `ε`, since `ℓ(x + p) = ℓ(x)`. -/
theorem isInGoodPosition_halfSpace (ℓ : E 0 →L[ℝ] ℝ) (N : Submodule ℝ (E 0)) {v₀ : E 0}
    (hv₀ : v₀ ∈ N) (hℓ : ℓ v₀ ≠ 0) : IsInGoodPosition E {v | 0 ≤ ℓ v} N := by
  set n₁ : E 0 := (ℓ v₀)⁻¹ • v₀ with hn₁
  have hn₁N : n₁ ∈ N := N.smul_mem _ hv₀
  have hℓn₁ : ℓ n₁ = 1 := by rw [hn₁, map_smul, smul_eq_mul, inv_mul_cancel₀ hℓ]
  refine ⟨⟨⟨n₁, hn₁N⟩, ?_⟩, ?_⟩
  · refine interior_maximal (t := {n : N | 0 < ℓ n}) (fun n (hn : 0 < ℓ n) => le_of_lt hn)
      (isOpen_lt continuous_const (ℓ.continuous.comp continuous_subtype_val)) ?_
    change (0 : ℝ) < ℓ n₁
    rw [hℓn₁]; exact one_pos
  · set K : Submodule ℝ (E 0) := LinearMap.ker (ℓ : E 0 →ₗ[ℝ] ℝ) with hK
    obtain ⟨P₀, hP₀⟩ := Submodule.exists_isCompl (N.comap K.subtype)
    refine ⟨P₀.map K.subtype, ⟨⟨Submodule.disjoint_def.2 ?_, codisjoint_iff.2 ?_⟩, 1, one_pos,
      fun x _ p hp _ => ?_⟩⟩
    · rintro x hxN ⟨k, hk, rfl⟩
      have hkN : k ∈ N.comap K.subtype := hxN
      have := Submodule.disjoint_def.1 hP₀.disjoint k hkN hk
      simp [this]
    · rw [Submodule.eq_top_iff']
      intro x
      have hk : x - ℓ x • n₁ ∈ K := by
        rw [hK, LinearMap.mem_ker]
        simp [map_sub, map_smul, hℓn₁]
      have hmem : (⟨_, hk⟩ : K) ∈ N.comap K.subtype ⊔ P₀ := by
        rw [hP₀.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem
      refine Submodule.mem_sup.2 ⟨ℓ x • n₁ + a, N.add_mem (N.smul_mem _ hn₁N) ha, b,
        ⟨b, hb, rfl⟩, ?_⟩
      have h := congrArg Subtype.val hab
      simp only [Submodule.coe_add] at h
      change ℓ x • n₁ + (a : E 0) + (b : E 0) = x
      rw [add_assoc, h]; abel
    · obtain ⟨k, -, rfl⟩ := hp
      have hk0 : ℓ k = 0 := k.2
      simp [map_add, hk0]

end HalfSpace

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **An M-polyfold with `X₀ = X_∞`, `1₀¹ : X → X¹` sc-smooth and `d_X ≤ 1` has a corner
structure** (Definition 4.1.1; Theorem 4.1.2 (2) ⇒ (1), 2021 p. 182, with good position
supplied): in a chart realizing `d_X(x)`, re-centred at `x`, the tangent space `T₀O` is in good
position to `C_e`, unless `C_e = {λ ≥ 0}` and `λ` vanishes on `T₀O`, which forces `d_X(x) = 0`
(`degIndex_eq_zero_of_isReducedTangentAt`).  No tameness. -/
theorem hasCornerStructure_of_degIndex_le_one (x₀ : P.Level 1) (hsm : ∀ x, x ∈ P.smoothSet)
    (hmap : P.IsScSmoothMap P.shift (P.toLevelOne x₀)) (hd : ∀ x, P.degIndex x ≤ 1) :
    P.HasCornerStructure := by
  classical
  have hplus := (isScSmoothMap_toLevelOne_iff x₀).1 ⟨hsm, hmap⟩
  refine hasCornerStructure_of_centred x₀ hsm hmap fun x => ?_
  obtain ⟨φ, hφ, hxφ, hdx⟩ := P.exists_isChart_degIndex_eq x
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have he : φ x ∈ φ.model.E.smooth := (MPolyfold.mem_smoothSet_iff hφ hxφ).1 (hsm x)
  set ψ := φ.recentre T hT (φ x) he with hψdef
  have hψ : P.IsChart ψ := φ.recentre_isChart T hT (φ x) he hφ
  have hxψ : x ∈ ψ.source := φ.mem_recentre_source T hT (φ x) he hxφ rfl
  have hψ0 : ψ x = 0 := φ.recentre_apply_self T hT (φ x) he rfl
  obtain ⟨t, ht, htp⟩ := hplus ψ hψ
  have h01 : (0 : ψ.model.E 1) ∈ ψ.model.E.lvlSet t.retract 1 := by
    rw [ScBanach.mem_lvlSet, ht, map_zero, ← hψ0]; exact ψ.mapsTo_model x hxψ
  have hNt : ((rangeS (scDeriv t.U t 0)) : Set (ψ.model.E 0)) =
      tangentSpace ψ.model.E ψ.model.C ψ.model.O 0 := by
    rw [← ht]; exact (tangentSpace_eq_coe_submodule t h01).symm
  refine ⟨ψ, hψ, hxψ, hψ0, rangeS (scDeriv t.U t 0), hNt, lemma_4_1_7_ii htp h01, ?_⟩
  set N := rangeS (scDeriv t.U t 0) with hNdef
  have hcard : P.degIndex x = (zeroSet T (φ x)).card := by
    rw [hdx, chartDegIndex, degIndex_eq T hT (φ.apply_mem_C hxφ), degIndexWith_eq_card_zeroSet]
  have hC : ψ.model.C = partialQuadrantAtWith T (φ x) := rfl
  have hle := hd x
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hcard ▸ hle) with h0 | h1
  · -- `d_X(x) = 0`: `C_e = E`
    have hU : partialQuadrantAtWith T (φ x) = univ := by
      ext v
      simp only [partialQuadrantAtWith, mem_ofPred_eq, mem_univ, iff_true]
      intro i hi
      have : i ∈ zeroSet T (φ x) := (mem_zeroSet T).2 hi
      rw [Finset.card_eq_zero.1 h0] at this
      exact absurd this (Finset.notMem_empty i)
    rw [hC, hU]
    exact isInGoodPosition_univ N
  · -- `d_X(x) = 1`: `C_e = {λ_i ≥ 0}`
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h1
    have hzi : ∀ j, (T 0 (φ x)).1 j = 0 ↔ j = i := fun j => by
      rw [← mem_zeroSet T, hi, Finset.mem_singleton]
    have hH : partialQuadrantAtWith T (φ x) = {v | 0 ≤ coordL T i v} := by
      ext v
      simp only [partialQuadrantAtWith, mem_ofPred_eq, coordL_apply]
      constructor
      · intro h; exact h i ((hzi i).2 rfl)
      · intro h j hj; rw [(hzi j).1 hj]; exact h
    by_cases hN : ∃ v ∈ N, coordL T i v ≠ 0
    · obtain ⟨v, hv, hne⟩ := hN
      rw [hC, hH]
      exact isInGoodPosition_halfSpace (coordL T i) N hv hne
    · exfalso
      push Not at hN
      have hred : IsReducedTangentAt ψ.model.E ψ.model.C ψ.model.O
          (recentreIso T (φ x)) 0 := by
        intro v hv
        rw [← hNt] at hv
        have hmin : minimalSubspaceWith (recentreIso T (φ x)) (φ x - φ x) =
            minimalSubspaceWith T (φ x) :=
          minimalSubspaceWith_recentreIso (mem_recentreNbhd hT (φ.apply_mem_C hxφ))
        change v ∈ (minimalSubspaceWith (recentreIso T (φ x)) (φ.model.E.toBase 1 0) :
          Set (φ.model.E 0))
        rw [map_zero, ← sub_self (φ x), hmin]
        refine (mem_minimalSubspaceWith T).2 fun j hj => ?_
        rw [(hzi j).1 hj]
        exact hN v hv
      have hx0 := degIndex_eq_zero_of_isReducedTangentAt hψ hxψ ⟨t, ht, htp⟩
        (recentreIso T (φ x)) (partialQuadrantAtWith_eq_preimage T (φ x)) (z := 0)
        (by rw [map_zero, hψ0]) hred
      omega

/-- **A smooth finite-dimensional submanifold with `d_A ≤ 1` is a manifold with boundary**
(Definition 4.1.1 for its induced structure): `hasCornerStructure_of_degIndex_le_one`, with
Proposition 4.2.3 (4) (`A = A_∞`, `1₀¹ : A → A¹` sc-smooth).  No tameness, no good position. -/
theorem IsSmoothSubmanifold.hasCornerStructure_of_degIndex_le_one {A : Set X}
    (hA : P.IsSmoothSubmanifold A) [ParacompactSpace A]
    (hd : ∀ a, (subPolyfold hA.isSubMPolyfold).degIndex a ≤ 1) :
    (subPolyfold hA.isSubMPolyfold).HasCornerStructure := by
  by_cases hne : Nonempty A
  · obtain ⟨a₀⟩ := hne
    have h1 : a₀ ∈ (subPolyfold hA.isSubMPolyfold).levelSet 1 :=
      (hA.mem_levelSet_subPolyfold_iff a₀ 1).2 (hA.mem_levelSet_one a₀.2)
    set x₀ := (subPolyfold hA.isSubMPolyfold).levelMk 1 a₀ h1
    obtain ⟨hsm, hmap⟩ := hA.proposition_4_2_3_four x₀
    exact _root_.Polyfold.MPolyfold.hasCornerStructure_of_degIndex_le_one x₀ hsm hmap hd
  · rw [hasCornerStructure_iff]
    intro x
    exact (hne ⟨x⟩).elim

/-- The set `{d ≤ k}` is open (Lemma 2.4.3, upper semicontinuity). -/
theorem isOpen_degIndex_le (Q : MPolyfold X) (k : ℕ) : IsOpen {x | Q.degIndex x ≤ k} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  exact Filter.mem_of_superset (lemma_2_4_3 Q x) fun y (hy : Q.degIndex y ≤ Q.degIndex x) =>
    show Q.degIndex y ≤ k from hy.trans hx

/-- **2021 Remark 4.2.2, p. 184, near the points with `d_A ≤ 1`** (preprint: Remark 4.14): for a
smooth finite-dimensional submanifold `A` of an M-polyfold `X`, with its induced M-polyfold
structure, the open piece `{d_A ≤ 1}` of `A` is a smooth finite-dimensional submanifold of `A`
whose induced structure has a corner structure (Definition 4.1.1) with degeneracy index `≤ 1` at
every point: a smooth manifold with boundary.  No tameness of `X` or `A`. -/
theorem remark_4_2_2_dA_one {A : Set X} (hA : P.IsSmoothSubmanifold A) [ParacompactSpace A] :
    ∃ hS : (subPolyfold hA.isSubMPolyfold).IsSmoothSubmanifold
        (univ ∩ {b | (subPolyfold hA.isSubMPolyfold).degIndex b ≤ 1}),
      haveI := (subPolyfold hA.isSubMPolyfold).paracompactSpace_subtype
        (univ ∩ {b | (subPolyfold hA.isSubMPolyfold).degIndex b ≤ 1})
      (subPolyfold hS.isSubMPolyfold).HasCornerStructure ∧
        ∀ b, (subPolyfold hS.isSubMPolyfold).degIndex b ≤ 1 := by
  have hS := hA.isSmoothSubmanifold_univ_subPolyfold.inter_isOpen
    (isOpen_degIndex_le (subPolyfold hA.isSubMPolyfold) 1)
  have := (subPolyfold hA.isSubMPolyfold).paracompactSpace_subtype
    (univ ∩ {b | (subPolyfold hA.isSubMPolyfold).degIndex b ≤ 1})
  have hd : ∀ b, (subPolyfold hS.isSubMPolyfold).degIndex b ≤ 1 := fun b =>
    (lemma_2_4_6 hS.isSubMPolyfold b).trans b.2.2
  exact ⟨hS, hS.hasCornerStructure_of_degIndex_le_one hd, hd⟩

/-- **2021 Remark 4.2.2, p. 184, near a point with `d_A(a) = 1`**: every `a ∈ A` with
`d_A(a) ≤ 1` has an open neighbourhood `U` in `A` which is a smooth finite-dimensional
submanifold of `A` whose induced structure is a smooth manifold with boundary (a corner structure
with `d_U ≤ 1`); `U = {d_A ≤ 1}`. -/
theorem remark_4_2_2_dA_one_near {A : Set X} (hA : P.IsSmoothSubmanifold A) [ParacompactSpace A]
    {a : A} (h1 : (subPolyfold hA.isSubMPolyfold).degIndex a ≤ 1) :
    ∃ U : Set A, IsOpen U ∧ a ∈ U ∧ ∃ hU : (subPolyfold hA.isSubMPolyfold).IsSmoothSubmanifold U,
      haveI := (subPolyfold hA.isSubMPolyfold).paracompactSpace_subtype U
      (subPolyfold hU.isSubMPolyfold).HasCornerStructure ∧
        ∀ b, (subPolyfold hU.isSubMPolyfold).degIndex b ≤ 1 := by
  obtain ⟨hS, hC, hd⟩ := remark_4_2_2_dA_one hA
  exact ⟨_, isOpen_univ.inter (isOpen_degIndex_le (subPolyfold hA.isSubMPolyfold) 1),
    ⟨mem_univ a, h1⟩, hS, hC, hd⟩

end MPolyfold

end Polyfold
