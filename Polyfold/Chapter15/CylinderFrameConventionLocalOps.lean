import Polyfold.Chapter6.IntervalSliceFrames
import Polyfold.Chapter15.OrientedLinearizations

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
**Remark 6.6.19**, and the proof of Theorem 6.7.1 (p. 278), in the form used on p. 703 for
Corollary 15.4.4.

# Frames of a kernel over `[0, 1] × X` with the `t`-direction first: operators

## What is formalized

`ChartPoint.exists_timeFirst_wedge_of_slice` (Chapter 6) relates the orientation `e ∧ o` of
`ker G'(t, x)` and the orientation of `ker G(t, ·)'(x)` for a section `G` over `[0, 1] × X`.
Here the same statement is made for operators:

* **`ChartPoint.exists_timeFirst_wedge_of_ops`**: let `L ∈ Lin(f, x)` be onto, and let
  `T₁ ∈ Lin(f̃, (t, x))` be onto with `T₁ (0, v) = L v` (in the product chart `χ_b × φ`).  For
  vectors `a₁, …, a_k` of `ker L` whose wedge spans the orientation of `ker L` given by `o`
  there is `ν ∈ ker T₁` with `t`-component the direction of increasing `t` such that
  `ν ∧ (0, a₁) ∧ … ∧ (0, a_k)` spans the orientation of `ker T₁` given by `e ∧ o`.

* `exists_timeFirst_wedge_of_ops_lift`: the same for the chart point of the product chart with
  a given level-one lift of the base point.

No section with linearization `T₁` enters, so the statement applies to the linearizations of
`f̃ − s̃` for an sc⁺-section `s̃` given near `(t, x)` only.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Manifold Module
open scoped ContDiff

noncomputable section

namespace Polyfold

open StrongRetr UnitCube

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) (b : Fin 1 → Bool) {t : Fin 1 → unitInterval}
  (ht : t ∈ (chart b).source)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))

/-- **`(0, v) ∈ ker T₁` iff `v ∈ ker L`**, for an operator `T₁` on `ℝ × T_xX` which is `L` on the
vectors `(0, v)`. -/
theorem mem_map_ker_ivPt_iff_of_fst_eq_zero {L : ↥p.T →L[ℝ] ↥p.K}
    {T₁ : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p.ivPt b ht q₀).K}
    (hE : ∀ w : ↥(p.ivPt b ht q₀).T, (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = 0 →
      T₁ w = p.ivLin b ht q₀ L w)
    {N₀ : Submodule ℝ (p.c.φ.model.E 0)}
    (hN₀ : (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = N₀)
    {N' : Submodule ℝ ((Fin 1 → ℝ) × p.c.φ.model.E 0)}
    (hN' : (LinearMap.ker (T₁ : ↥(p.ivPt b ht q₀).T →ₗ[ℝ] ↥(p.ivPt b ht q₀).K)).map
      (p.ivIncl b ht q₀ : ↥(p.ivPt b ht q₀).T →ₗ[ℝ] (Fin 1 → ℝ) × p.c.φ.model.E 0) = N')
    (w : (Fin 1 → ℝ) × p.c.φ.model.E 0) (hw : w.1 = 0) : w ∈ N' ↔ w.2 ∈ N₀ := by
  rw [← hN', ← hN₀]
  constructor
  · rintro ⟨u, hu, huw⟩
    have huw' : (u.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) = w := huw
    have hu1 : (u.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = 0 := by rw [huw']; exact hw
    have h0 : T₁ u = 0 := LinearMap.mem_ker.1 hu
    rw [hE u hu1] at h0
    have h1 := p.coe_ivLin_apply b ht q₀ L u
    rw [h0] at h1
    refine ⟨(p.ivT b ht q₀ u).1, LinearMap.mem_ker.2 (Subtype.ext h1.symm), ?_⟩
    change ((p.ivT b ht q₀ u).1 : p.c.φ.model.E 0) = w.2
    rw [coe_ivT_fst, huw']
  · rintro ⟨v, hv, hvw⟩
    have hvw' : (v : p.c.φ.model.E 0) = w.2 := hvw
    have hwT : w ∈ (p.ivPt b ht q₀).T := (p.mem_ivPt_T_iff b ht q₀ w).2 (hvw' ▸ v.2)
    have hT : (p.ivT b ht q₀ ⟨w, hwT⟩).1 = v := Subtype.ext hvw'.symm
    refine ⟨⟨w, hwT⟩, LinearMap.mem_ker.2 ?_, rfl⟩
    change T₁ ⟨w, hwT⟩ = 0
    rw [hE ⟨w, hwT⟩ hw]
    refine Subtype.ext ?_
    rw [p.coe_ivLin_apply b ht q₀ L ⟨w, hwT⟩, hT]
    have h0 : L v = 0 := LinearMap.mem_ker.1 hv
    rw [h0]
    rfl

set_option maxHeartbeats 1600000 in
-- the model of the product chart is identified with `ℝ × E`
/-- **Frames of `ker T₁` with the `t`-direction first, for operators** (2021 Remark 6.6.19,
p. 276, and the proof of Theorem 6.7.1, p. 278): let `L ∈ Lin(f, x)` and
`T₁ ∈ Lin(f̃, (t, x))` be onto with `T₁ (0, v) = L v`; let `dim ker L = k`,
`dim ker T₁ = k + 1`, and let `a₁, …, a_k` be vectors of `ker L` whose wedge spans the
orientation of `ker L` given by `o`.  Then there is `ν ∈ ker T₁` with `t`-component the
direction of increasing `t` (`± 1` in the chart `χ_b × φ`, the sign that of `χ_b`) such that
`ν ∧ (0, a₁) ∧ … ∧ (0, a_k)` spans the orientation of `ker T₁` given by `e ∧ o`. -/
theorem exists_timeFirst_wedge_of_ops (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hxs : x ∈ PX.smoothSet) (hne : (p.linSet f).Nonempty) (o : p.Or f hf)
    {L : ↥p.T →L[ℝ] ↥p.K} (hmem : L ∈ p.linSet f) (hLs : Function.Surjective L)
    {T₁ : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p.ivPt b ht q₀).K}
    (hT₁m : T₁ ∈ (p.ivPt b ht q₀).linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    (hT₁s : Function.Surjective T₁)
    (hE : ∀ w : ↥(p.ivPt b ht q₀).T, (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = 0 →
      T₁ w = p.ivLin b ht q₀ L w)
    {N₀ : Submodule ℝ (p.c.φ.model.E 0)}
    (hN₀ : (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = N₀)
    {N' : Submodule ℝ ((p.ivPt b ht q₀).c.φ.model.E 0)}
    (hN' : (LinearMap.ker (T₁ : ↥(p.ivPt b ht q₀).T →ₗ[ℝ] ↥(p.ivPt b ht q₀).K)).map
      ((p.ivPt b ht q₀).T.subtypeL :
        ↥(p.ivPt b ht q₀).T →ₗ[ℝ] (p.ivPt b ht q₀).c.φ.model.E 0) = N')
    {k : ℕ} (hk : finrank ℝ N₀ = k) (hk' : finrank ℝ N' = k + 1)
    (a : Fin k → N₀) (hna : wedge a hk.symm ≠ 0)
    (ha : p.orKer o hmem hLs hN₀ = rayOfNeZero ℝ _ hna) :
    ∃ (ν : N') (a' : Fin k → N')
      (hna' : wedge (Fin.cons ν a' : Fin (k + 1) → N') hk'.symm ≠ 0),
      ((ν.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = fun _ => ivSign b) ∧
      (∀ l, ((a' l).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) = (0, (a l : p.c.φ.model.E 0))) ∧
      (p.ivPt b ht q₀).orKer (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o) hT₁m hT₁s hN' =
        rayOfNeZero ℝ _ hna' := by
  have hfdN : FiniteDimensional ℝ N₀ := p.finiteDimensional_of_mem_linSet hf hmem hN₀
  have hfdN' : FiniteDimensional ℝ N' :=
    Module.finite_of_finrank_pos (by rw [hk']; exact Nat.succ_pos k)
  have aux := fun (N' : Submodule ℝ ((Fin 1 → ℝ) × p.c.φ.model.E 0))
      (hfd : FiniteDimensional ℝ N') (hk' : finrank ℝ N' = k + 1)
      (hiff : ∀ w : (Fin 1 → ℝ) × p.c.φ.model.E 0, w.1 = 0 → (w ∈ N' ↔ w.2 ∈ N₀)) =>
    exists_timeFirst_coordinates (E₀ := p.c.φ.model.E 0) (N := N₀) (N' := N') hk hk' hiff
      (ivSign_ne_zero b) a hna
  have hiff := p.mem_map_ker_ivPt_iff_of_fst_eq_zero b ht q₀ hE hN₀ hN'
  have h2 := aux N' hfdN' hk' hiff
  obtain ⟨ν, a', hna', ι, ι', hν1, ha', hι₀, hι₁, hrest⟩ := h2
  refine ⟨ν, a', hna', hν1, ha', hrest.2 _ ?_⟩
  -- the shear between `T₁` and `L̂`
  have aux2 : ∀ (N' : Submodule ℝ ((Fin 1 → ℝ) × p.c.φ.model.E 0))
      (hN' : (LinearMap.ker ((T₁ : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p.ivPt b ht q₀).K) :
        ↥(p.ivPt b ht q₀).T →ₗ[ℝ] ↥(p.ivPt b ht q₀).K)).map
          (p.ivIncl b ht q₀ : ↥(p.ivPt b ht q₀).T →ₗ[ℝ] (Fin 1 → ℝ) × p.c.φ.model.E 0) = N')
      (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N')
      (_ : ∀ w, ((ι' (consE 0 w) : N') : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
        (0, (ι w : p.c.φ.model.E 0)))
      (_ : ((ι' (consE 1 (0 : EuclideanSpace ℝ (Fin k))) : N') :
        (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = fun _ => ivSign b),
      (pullOr finrank_euclideanSpace_fin ι'
          (surjRay hT₁s (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hN'
            ((p.ivPt b ht q₀).orEquivRay hfc hT₁m (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o))) =
          stdOrientation (k + 1) ↔
        pullOr finrank_euclideanSpace_fin ι
          (surjRay hLs p.T.subtypeL Subtype.val_injective hN₀ (p.orEquivRay hf hmem o)) =
            stdOrientation k) := by
    intro N' hN' ι' hι₀' hι₁'
    have hsurj := (kerEquivOfMap T₁ (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀)
      hN').surjective (ι' (consE 1 (0 : EuclideanSpace ℝ (Fin k))))
    obtain ⟨ν', hν'1⟩ := hsurj
    have hνker : T₁ ν'.1 = 0 := LinearMap.mem_ker.1 ν'.2
    have hνeq : ((ν'.1 : ↥(p.ivPt b ht q₀).T).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
        ((ι' (consE 1 (0 : EuclideanSpace ℝ (Fin k))) : N') :
          (Fin 1 → ℝ) × p.c.φ.model.E 0) :=
      (coe_kerEquivOfMap T₁ (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hN' ν').symm.trans
        (congrArg Subtype.val hν'1)
    have hν1' : ((ν'.1 : ↥(p.ivPt b ht q₀).T).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 =
        fun _ => ivSign b := (congrArg Prod.fst hνeq).trans hι₁'
    have hsh := p.exists_shear_of_eq_on_slice b ht q₀ L T₁ hE ν'.1 hνker hν1'
    obtain ⟨N, hNN, hT, hNform⟩ := hsh
    exact p.pullOr_surjRay_ivOrFirst₀_iff_of_shear b ht q₀ hf hfc hxs hne o hmem hLs
      hN₀ hT₁m hT₁s N hNN hT _ hNform hN' rfl ι ι' hι₀'
      (Prod.ext hι₁' (congrArg Prod.snd hνeq).symm)
  exact (aux2 _ hN' ι' hι₀ hι₁).2 (hrest.1 _ ha)

end ChartPoint

/-- **Frames of `ker T₁` with the `t`-direction first, in the chart point of the product chart
with a given lift** `z' = (χ_b(t), z)` of the base point: the statement of
`ChartPoint.exists_timeFirst_wedge_of_ops` for the orientation `ivOrLift`, with the relation
`T₁ (0, v) = L v` read in the model spaces. -/
theorem exists_timeFirst_wedge_of_ops_lift (b : Fin 1 → Bool) {c : StrongBundleChart PX P}
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
    {L : ↥(chartPt c hc hx z hz).T →L[ℝ] ↥(chartPt c hc hx z hz).K}
    (hmem : L ∈ (chartPt c hc hx z hz).linSet f) (hLs : Function.Surjective L)
    {T₁ : ↥(chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
        hz').T →L[ℝ]
      ↥(chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z' hz').K}
    (hT₁m : T₁ ∈ (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
      hz').linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    (hT₁s : Function.Surjective T₁)
    (hE : ∀ (w : ↥(chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
        hz').T) (v : ↥(chartPt c hc hx z hz).T),
      (w.1 : (Fin 1 → ℝ) × c.φ.model.E 0) = (0, (v.1 : c.φ.model.E 0)) →
        ((T₁ w).1 : c.F 0) = ((L v).1 : c.F 0))
    {N₀ : Submodule ℝ (c.φ.model.E 0)}
    (hN₀ : (LinearMap.ker (L : ↥(chartPt c hc hx z hz).T →ₗ[ℝ] ↥(chartPt c hc hx z hz).K)).map
      ((chartPt c hc hx z hz).T.subtypeL :
        ↥(chartPt c hc hx z hz).T →ₗ[ℝ] c.φ.model.E 0) = N₀)
    {N' : Submodule ℝ ((ivChart b c q₀).φ.model.E 0)}
    (hN' : (LinearMap.ker (T₁ :
        ↥(chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
          hz').T →ₗ[ℝ]
        ↥(chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
          hz').K)).map
      ((chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
        hz').T.subtypeL :
        ↥(chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
          hz').T →ₗ[ℝ] (ivChart b c q₀).φ.model.E 0) = N')
    {k : ℕ} (hk : finrank ℝ N₀ = k) (hk' : finrank ℝ N' = k + 1)
    (a : Fin k → N₀) (hna : wedge a hk.symm ≠ 0)
    (ha : (chartPt c hc hx z hz).orKer o hmem hLs hN₀ = rayOfNeZero ℝ _ hna) :
    ∃ (ν : N') (a' : Fin k → N')
      (hna' : wedge (Fin.cons ν a' : Fin (k + 1) → N') hk'.symm ≠ 0),
      ((ν.1 : (Fin 1 → ℝ) × c.φ.model.E 0).1 = fun _ => ivSign b) ∧
      (∀ l, ((a' l).1 : (Fin 1 → ℝ) × c.φ.model.E 0) = (0, (a l : c.φ.model.E 0))) ∧
      (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
          hz').orKer (ivOrLift b hc hx z hz ht q₀ hxc z' hz' hzz hf hfc hxs hne o) hT₁m hT₁s
          hN' = rayOfNeZero ℝ _ hna' := by
  subst hzz
  have hE' : ∀ w : ↥((chartPt c hc hx z hz).ivPt b ht q₀).T,
      (w.1 : (Fin 1 → ℝ) × c.φ.model.E 0).1 = 0 →
        T₁ w = (chartPt c hc hx z hz).ivLin b ht q₀ L w := fun w hw =>
    Subtype.ext ((hE w ((chartPt c hc hx z hz).ivT b ht q₀ w).1 (Prod.ext hw rfl)).trans
      ((chartPt c hc hx z hz).coe_ivLin_apply b ht q₀ L w).symm)
  exact (chartPt c hc hx z hz).exists_timeFirst_wedge_of_ops b ht q₀ hf hfc hxs hne o hmem hLs
    hT₁m hT₁s hE' hN₀ hN' hk hk' a hna ha

end Polyfold
