import Polyfold.Chapter6.IntervalSliceFrames

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
**Remark 6.6.19** (preprint Remark 6.42, p. 230) and the proof of Theorem 6.7.1 (p. 278): the
orientation `e ∧ o` of `ker G'(t, x)` for a section `G` over `[0, 1] × X`, in terms of frames,
for both orientations of the slice.

# Signed frames of `ker G'(t, x)` with the `t`-direction first

## The text, paraphrased

`ker G'(t, x) = ℝ·ν ⊕ ker g'(x)`, `g = G(t, ·)`, with `ν` of `t`-component `1`, and the
orientation `e ∧ o` puts the `ℝ`-factor first.  If the kernel of `g'(x)` is `0` (index `0`), the
point `x` carries a sign, and `ker G'(t, x) = ℝ·ν` is oriented by `ν` if the sign is `+` and by
`−ν` if it is `−`.

## What is formalized

* `pullOr_neg`: the orientation pulled back from the opposite ray is the opposite orientation.
* `wedge_cons_neg`: `(−ν) ∧ a₁ ∧ … ∧ a_k = −(ν ∧ a₁ ∧ … ∧ a_k)`.
* `ray_cons_of_coordinates`, `exists_timeFirst_coordinates_signed`: the linear algebra, for
  both signs.
* **`ChartPoint.exists_timeFirst_wedge_signed_of_slice`**: in the situation of
  `ChartPoint.exists_timeFirst_wedge_of_slice`, for any basis `a₁, …, a_k` of `ker g'(x)`: there
  are `ν, ν' ∈ ker G'(t, x)` whose `t`-components are the directions of increasing and of
  decreasing `t` such that `ν ∧ (0, a₁) ∧ … ∧ (0, a_k)` spans the orientation given by `e ∧ o`
  if `a₁ ∧ … ∧ a_k` spans the orientation given by `o`, and `ν' ∧ (0, a₁) ∧ … ∧ (0, a_k)` spans
  it otherwise.
* `exists_timeFirst_wedge_signed_ivOrLift`: the same for the chart point of the product chart
  with a given level-one lift of the base point.
-/

open Set Filter Topology Manifold Module
open scoped ContDiff

noncomputable section

namespace Polyfold

open StrongRetr UnitCube

universe u v

/-! ### Opposite rays and orientations -/

section Neg

variable {E N : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup N] [Module ℝ N] {k : ℕ} (hk : finrank ℝ E = k)

/-- **The orientation pulled back from the opposite ray is the opposite orientation.** -/
theorem pullOr_neg (L : E ≃ₗ[ℝ] N) (r : Module.Ray ℝ (maxPow N)) :
    pullOr hk L (-r) = -pullOr hk L r := by
  classical
  have := L.finiteDimensional
  have hρ := Module.Ray.ne_neg_self (rayOfNeZero ℝ _ (wedge_equiv_ne_zero hk L (pullBasis hk)))
  unfold pullOr
  rcases ray_eq_or_eq_neg_of_finrank_eq_one finrank_maxPow
    (wedge_equiv_ne_zero hk L (pullBasis hk)) r with h | h
  · rw [if_pos h, h, if_neg (fun h' => hρ h'.symm)]
  · rw [h, neg_neg, if_pos rfl, if_neg (fun h' => hρ h'.symm), neg_neg]

omit [FiniteDimensional ℝ E] in
/-- `(−ν) ∧ a₁ ∧ … ∧ a_k = −(ν ∧ a₁ ∧ … ∧ a_k)`. -/
theorem wedge_cons_neg {n : ℕ} (ν : E) (a : Fin n → E) (h : n + 1 = finrank ℝ E) :
    wedge (Fin.cons (-ν) a : Fin (n + 1) → E) h = -wedge (Fin.cons ν a : Fin (n + 1) → E) h := by
  classical
  refine Subtype.ext ?_
  change ExteriorAlgebra.ιMulti ℝ (n + 1) (Fin.cons (-ν) a) =
    -ExteriorAlgebra.ιMulti ℝ (n + 1) (Fin.cons ν a)
  have e : (Fin.cons (-ν) a : Fin (n + 1) → E) =
      Function.update (Fin.cons ν a : Fin (n + 1) → E) 0 (-ν) := by
    rw [Fin.update_cons_zero]
  rw [e, AlternatingMap.map_update_neg, Fin.update_cons_zero]

/-- **The two cases of an orientation read in coordinates with the `ℝ`-direction first**: let
`ι`, `ι'` be coordinates of `N`, `N'` such that the ray of `a₁ ∧ … ∧ a_k` gives the standard
orientation in `ι` and a ray giving the standard orientation in `ι'` is that of
`ν ∧ a'₁ ∧ … ∧ a'_k`.  If rays `r` of `λ(N)` and `r'` of `λ(N')` give the standard orientations
together, then `r'` is the ray of `ν ∧ a'` if `r` is that of `a`, and the ray of `(−ν) ∧ a'` if
not. -/
theorem ray_cons_of_coordinates {N' : Type*} [AddCommGroup N'] [Module ℝ N']
    [FiniteDimensional ℝ N] [FiniteDimensional ℝ N'] {n : ℕ}
    (hn : finrank ℝ N = n) (hn' : finrank ℝ N' = n + 1)
    (ι : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] N) (ι' : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] N')
    (a : Fin n → N) (hna : wedge a hn.symm ≠ 0) (ν : N') (a' : Fin n → N')
    (hna' : wedge (Fin.cons ν a' : Fin (n + 1) → N') hn'.symm ≠ 0)
    (hstd : ∀ r : Module.Ray ℝ (maxPow N), r = rayOfNeZero ℝ _ hna →
      pullOr finrank_euclideanSpace_fin ι r = stdOrientation n)
    (hray : ∀ r' : Module.Ray ℝ (maxPow N'),
      pullOr finrank_euclideanSpace_fin ι' r' = stdOrientation (n + 1) →
        r' = rayOfNeZero ℝ _ hna')
    (r : Module.Ray ℝ (maxPow N)) (r' : Module.Ray ℝ (maxPow N'))
    (hiff : pullOr finrank_euclideanSpace_fin ι' r' = stdOrientation (n + 1) ↔
      pullOr finrank_euclideanSpace_fin ι r = stdOrientation n) :
    ∃ hna'' : wedge (Fin.cons (-ν) a' : Fin (n + 1) → N') hn'.symm ≠ 0,
      (r = rayOfNeZero ℝ _ hna → r' = rayOfNeZero ℝ _ hna') ∧
      (r ≠ rayOfNeZero ℝ _ hna → r' = rayOfNeZero ℝ _ hna'') := by
  have hneg : wedge (Fin.cons (-ν) a' : Fin (n + 1) → N') hn'.symm =
      -wedge (Fin.cons ν a' : Fin (n + 1) → N') hn'.symm := wedge_cons_neg ν a' _
  have hna'' : wedge (Fin.cons (-ν) a' : Fin (n + 1) → N') hn'.symm ≠ 0 := by
    rw [hneg]; exact neg_ne_zero.2 hna'
  refine ⟨hna'', fun ha => hray _ (hiff.2 (hstd _ ha)), fun ha => ?_⟩
  have h1 : pullOr finrank_euclideanSpace_fin ι r ≠ stdOrientation n := fun h => by
    rcases ray_eq_or_eq_neg_of_finrank_eq_one finrank_maxPow hna r with h' | h'
    · exact ha h'
    · rw [h', pullOr_neg, hstd _ rfl] at h
      exact Module.Ray.ne_neg_self _ h.symm
  have h2 : pullOr finrank_euclideanSpace_fin ι' r' ≠ stdOrientation (n + 1) :=
    fun h => h1 (hiff.1 h)
  have h3 : pullOr finrank_euclideanSpace_fin ι' (-r') = stdOrientation (n + 1) := by
    rw [pullOr_neg]
    rcases Orientation.eq_or_eq_neg (stdOrientation (n + 1))
      (pullOr finrank_euclideanSpace_fin ι' r')
      (by rw [Fintype.card_fin, finrank_euclideanSpace_fin]) with h | h
    · exact absurd h.symm h2
    · exact h.symm
  have h4 := hray _ h3
  rw [neg_eq_iff_eq_neg, neg_rayOfNeZero] at h4
  exact h4.trans (rayOfNeZero_congr hneg.symm _ _)

end Neg

/-! ### Signed coordinates with the `ℝ`-direction first -/

section SignedCoordinates

variable {E₀ : Type*} [AddCommGroup E₀] [Module ℝ E₀]

/-- **Coordinates with the `ℝ`-direction first, both signs.**  In the situation of
`exists_timeFirst_coordinates` there are `ν, ν' ∈ N'` with `ℝ`-components `s`, `−s` and
coordinates `ι`, `ι'` (`ι'(0, w) = (0, ι w)`, `ι'(1, 0)` of `ℝ`-component `s`) such that, for rays
`r` of `λ(N)` and `r'` of `λ(N')` giving the standard orientations in `ι`, `ι'` together, `r'` is
the ray of `ν ∧ (0, a)` if `r` is that of `a₁ ∧ … ∧ a_k`, and the ray of `ν' ∧ (0, a)` if not. -/
theorem exists_timeFirst_coordinates_signed {N : Submodule ℝ E₀}
    {N' : Submodule ℝ ((Fin 1 → ℝ) × E₀)} [FiniteDimensional ℝ N] [FiniteDimensional ℝ N']
    {k : ℕ} (hk : finrank ℝ N = k) (hk' : finrank ℝ N' = k + 1)
    (hiff : ∀ w : (Fin 1 → ℝ) × E₀, w.1 = 0 → (w ∈ N' ↔ w.2 ∈ N)) {s : ℝ} (hs : s ≠ 0)
    (a : Fin k → N) (hna : wedge a hk.symm ≠ 0) :
    ∃ (ν ν' : N') (a' : Fin k → N')
      (hna' : wedge (Fin.cons ν a' : Fin (k + 1) → N') hk'.symm ≠ 0)
      (hna'' : wedge (Fin.cons ν' a' : Fin (k + 1) → N') hk'.symm ≠ 0)
      (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] N) (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N'),
      ((ν : (Fin 1 → ℝ) × E₀).1 = fun _ => s) ∧ ((ν' : (Fin 1 → ℝ) × E₀).1 = fun _ => -s) ∧
      (∀ l, ((a' l : N') : (Fin 1 → ℝ) × E₀) = (0, (a l : E₀))) ∧
      (∀ w, ((ι' (consE 0 w) : N') : (Fin 1 → ℝ) × E₀) = (0, (ι w : E₀))) ∧
      (((ι' (consE 1 0) : N') : (Fin 1 → ℝ) × E₀).1 = fun _ => s) ∧
      ∀ (r : Module.Ray ℝ (maxPow N)) (r' : Module.Ray ℝ (maxPow N')),
        (pullOr finrank_euclideanSpace_fin ι' r' = stdOrientation (k + 1) ↔
          pullOr finrank_euclideanSpace_fin ι r = stdOrientation k) →
        (r = rayOfNeZero ℝ _ hna → r' = rayOfNeZero ℝ _ hna') ∧
        (r ≠ rayOfNeZero ℝ _ hna → r' = rayOfNeZero ℝ _ hna'') := by
  obtain ⟨ν, a', hna', ι, ι', hν1, ha', hι₀, hι₁, hstd, hray⟩ :=
    exists_timeFirst_coordinates hk hk' hiff hs a hna
  obtain ⟨hna'', -⟩ := ray_cons_of_coordinates hk hk' ι ι' a hna ν a' hna' hstd hray
    (rayOfNeZero ℝ _ hna) (rayOfNeZero ℝ _ hna')
    (iff_of_true ((Orientation.eq_or_eq_neg _ _ (by
      rw [Fintype.card_fin, finrank_euclideanSpace_fin])).elim id fun h => by
        have h3 : pullOr finrank_euclideanSpace_fin ι' (-rayOfNeZero ℝ _ hna') =
            stdOrientation (k + 1) := by rw [pullOr_neg, h, neg_neg]
        exact absurd (hray _ h3) (fun h' => Module.Ray.ne_neg_self _ h'.symm)) (hstd _ rfl))
  refine ⟨ν, -ν, a', hna', hna'', ι, ι', hν1, ?_, ha', hι₀, hι₁, fun r r' h => ?_⟩
  · change (-(ν : (Fin 1 → ℝ) × E₀)).1 = fun _ => -s
    rw [Prod.fst_neg, hν1]
    rfl
  · obtain ⟨_, h₁, h₂⟩ := ray_cons_of_coordinates hk hk' ι ι' a hna ν a' hna' hstd hray r r' h
    exact ⟨h₁, h₂⟩

end SignedCoordinates

section IvFrames

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) (b : Fin 1 → Bool) {t : Fin 1 → unitInterval}
  (ht : t ∈ (chart b).source)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))

set_option maxHeartbeats 3200000 in
-- the model of the product chart is identified with `ℝ × E`
/-- **Signed frames of `ker G'(t, x)` with the `t`-direction first** (2021 Remark 6.6.19,
p. 276, and the proof of Theorem 6.7.1, p. 278): let `(t, x)` be a zero of a section `G` over
`[0, 1] × X` with `G'(t, x)` onto and in `Lin(f̃, (t, x))`, such that the slice `g = G(t, ·)` has
`g'(x)` onto and in `Lin(f, x)`; let `dim ker g'(x) = k`, `dim ker G'(t, x) = k + 1`, and let
`a₁, …, a_k` be a basis of `ker g'(x)`.  Then there are `ν, ν' ∈ ker G'(t, x)` with
`t`-components the directions of increasing and of decreasing `t` such that the orientation of
`ker G'(t, x)` given by `e ∧ o` is spanned by `ν ∧ (0, a₁) ∧ … ∧ (0, a_k)` if `a₁ ∧ … ∧ a_k`
spans the orientation of `ker g'(x)` given by `o`, and by `ν' ∧ (0, a₁) ∧ … ∧ (0, a_k)` if not.
For `k = 0`: the line `ker G'(t, x)` is oriented by `ν` at a positive point `x` and by `ν'` at a
negative one. -/
theorem exists_timeFirst_wedge_signed_of_slice (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hxs : x ∈ PX.smoothSet) (hne : (p.linSet f).Nonempty) (o : p.Or f hf)
    {G : (Fin 1 → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hG : (ivBundle B).IsScFredholmSection G) (hg : B.IsScFredholmSection (prodSlice G t))
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) G (t, x)) (hx0 : IsZeroAt P (prodSlice G t) x)
    (hgL : B.IsLinSurjAt (prodSlice G t) x) (hGL : (ivBundle B).IsLinSurjAt G (t, x))
    (hmem : p.linZero hg hx0 ∈ p.linSet f)
    (hmem' : (p.ivPt b ht q₀).linZero hG hz0 ∈
      (p.ivPt b ht q₀).linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    {k : ℕ} (hk : finrank ℝ (p.c.linKer (prodSlice G t) p.z) = k)
    (hk' : finrank ℝ ((p.ivPt b ht q₀).c.linKer G (p.ivPt b ht q₀).z) = k + 1)
    (a : Fin k → p.c.linKer (prodSlice G t) p.z) (hna : wedge a hk.symm ≠ 0) :
    ∃ (ν ν' : (p.ivPt b ht q₀).c.linKer G (p.ivPt b ht q₀).z)
      (a' : Fin k → (p.ivPt b ht q₀).c.linKer G (p.ivPt b ht q₀).z)
      (hna' : wedge (Fin.cons ν a' : Fin (k + 1) →
        (p.ivPt b ht q₀).c.linKer G (p.ivPt b ht q₀).z) hk'.symm ≠ 0)
      (hna'' : wedge (Fin.cons ν' a' : Fin (k + 1) →
        (p.ivPt b ht q₀).c.linKer G (p.ivPt b ht q₀).z) hk'.symm ≠ 0),
      ((ν.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = fun _ => ivSign b) ∧
      ((ν'.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = fun _ => -ivSign b) ∧
      (∀ l, ((a' l).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) = (0, (a l : p.c.φ.model.E 0))) ∧
      (p.tangentOrOf hf hg hx0 hgL hmem o = rayOfNeZero ℝ _ hna →
        (p.ivPt b ht q₀).tangentOrOf hfc hG hz0 hGL hmem'
          (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o) = rayOfNeZero ℝ _ hna') ∧
      (p.tangentOrOf hf hg hx0 hgL hmem o ≠ rayOfNeZero ℝ _ hna →
        (p.ivPt b ht q₀).tangentOrOf hfc hG hz0 hGL hmem'
          (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o) = rayOfNeZero ℝ _ hna'') := by
  have hfdN : FiniteDimensional ℝ (p.c.linKer (prodSlice G t) p.z) := by
    have := (p.isFredholm_of_mem_linSet hf _ hmem).finite_ker
    exact (kerEquivOfMap (p.linZero hg hx0) p.T.subtypeL Subtype.val_injective
      (p.map_ker_linZero hg hx0)).finiteDimensional
  have hfdN' : FiniteDimensional ℝ ((p.ivPt b ht q₀).c.linKer G (p.ivPt b ht q₀).z) :=
    Module.finite_of_finrank_pos (by rw [hk']; exact Nat.succ_pos k)
  have aux := fun (N' : Submodule ℝ ((Fin 1 → ℝ) × p.c.φ.model.E 0))
      (hfd : FiniteDimensional ℝ N') (hk' : finrank ℝ N' = k + 1)
      (hiff : ∀ w : (Fin 1 → ℝ) × p.c.φ.model.E 0, w.1 = 0 →
        (w ∈ N' ↔ w.2 ∈ p.c.linKer (prodSlice G t) p.z)) =>
    exists_timeFirst_coordinates_signed (E₀ := p.c.φ.model.E 0)
      (N := p.c.linKer (prodSlice G t) p.z) (N' := N') hk hk' hiff (ivSign_ne_zero b) a hna
  obtain ⟨ν, ν', a', hna', hna'', ι, ι', hν1, hν1', ha', hι₀, hι₁, hboth⟩ :=
    aux ((p.ivPt b ht q₀).c.linKer G (p.ivPt b ht q₀).z) hfdN' hk'
      (p.mem_linKer_ivPt_iff_of_fst_eq_zero b ht q₀ hG hg hz0 hx0)
  exact ⟨ν, ν', a', hna', hna'', hν1, hν1', ha', hboth _ _
    (p.pullOr_tangentOrOf_ivOrFirst₀_iff_of_slice b ht q₀ hf hfc hxs hne o hG hg hz0 hx0 hgL hGL
      hmem hmem' ι ι' hι₀ hι₁)⟩

end ChartPoint

/-- **Signed frames of `ker G'(t, x)` with the `t`-direction first, in the chart point of the
product chart with a given lift** `z' = (χ_b(t), z)` of the base point: the statement of
`ChartPoint.exists_timeFirst_wedge_signed_of_slice` for the orientation `ivOrLift`. -/
theorem exists_timeFirst_wedge_signed_ivOrLift (b : Fin 1 → Bool) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source) (z : c.φ.model.E 1)
    (hz : c.φ.model.E.toBase 1 z = c.φ x) {t : Fin 1 → unitInterval}
    (ht : t ∈ (chart b).source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hxc : ((t, x) : (Fin 1 → unitInterval) × X) ∈ (ivChart b c q₀).φ.source)
    (z' : (ivChart b c q₀).φ.model.E 1)
    (hz' : (ivChart b c q₀).φ.model.E.toBase 1 z' = (ivChart b c q₀).φ (t, x))
    (hzz : z' = ((chart b t : Fin 1 → ℝ), z)) (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hxs : x ∈ PX.smoothSet) (hne : ((chartPt c hc hx z hz).linSet f).Nonempty)
    (o : (chartPt c hc hx z hz).Or f hf)
    {G : (Fin 1 → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hG : (ivBundle B).IsScFredholmSection G) {g : X → Y} (hgs : prodSlice G t = g)
    (hg : B.IsScFredholmSection g)
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) G (t, x)) (hx0 : IsZeroAt P g x)
    (hgL : B.IsLinSurjAt g x) (hGL : (ivBundle B).IsLinSurjAt G (t, x))
    (hmem : (chartPt c hc hx z hz).linZero hg hx0 ∈ (chartPt c hc hx z hz).linSet f)
    (hmem' : (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
        hz').linZero hG hz0 ∈
      (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z' hz').linSet
        (cubeLift (n := 1) f hf.isScSmooth.1))
    {k : ℕ} (hk : finrank ℝ (c.linKer g z) = k)
    (hk' : finrank ℝ ((ivChart b c q₀).linKer G z') = k + 1)
    (a : Fin k → c.linKer g z) (hna : wedge a hk.symm ≠ 0) :
    ∃ (ν ν' : (ivChart b c q₀).linKer G z') (a' : Fin k → (ivChart b c q₀).linKer G z')
      (hna' : wedge (Fin.cons ν a' : Fin (k + 1) → (ivChart b c q₀).linKer G z') hk'.symm ≠ 0)
      (hna'' : wedge (Fin.cons ν' a' : Fin (k + 1) → (ivChart b c q₀).linKer G z')
        hk'.symm ≠ 0),
      ((ν.1 : (Fin 1 → ℝ) × c.φ.model.E 0).1 = fun _ => ivSign b) ∧
      ((ν'.1 : (Fin 1 → ℝ) × c.φ.model.E 0).1 = fun _ => -ivSign b) ∧
      (∀ l, ((a' l).1 : (Fin 1 → ℝ) × c.φ.model.E 0) = (0, (a l : c.φ.model.E 0))) ∧
      ((chartPt c hc hx z hz).tangentOrOf hf hg hx0 hgL hmem o = rayOfNeZero ℝ _ hna →
        (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
            hz').tangentOrOf hfc hG hz0 hGL hmem'
            (ivOrLift b hc hx z hz ht q₀ hxc z' hz' hzz hf hfc hxs hne o) =
          rayOfNeZero ℝ _ hna') ∧
      ((chartPt c hc hx z hz).tangentOrOf hf hg hx0 hgL hmem o ≠ rayOfNeZero ℝ _ hna →
        (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
            hz').tangentOrOf hfc hG hz0 hGL hmem'
            (ivOrLift b hc hx z hz ht q₀ hxc z' hz' hzz hf hfc hxs hne o) =
          rayOfNeZero ℝ _ hna'') := by
  subst hzz
  subst hgs
  exact (chartPt c hc hx z hz).exists_timeFirst_wedge_signed_of_slice b ht q₀ hf hfc hxs hne o hG
    hg hz0 hx0 hgL hGL hmem hmem' hk hk' a hna

end IvFrames

end Polyfold
