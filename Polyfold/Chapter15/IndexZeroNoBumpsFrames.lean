import Polyfold.Chapter15.CylinderFrameConventionLocal
import Polyfold.Chapter6.IntervalSliceSignedFrames

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703: the proof
of **Corollary 15.4.4** (2017: Corollary 15.2) for Fredholm index `0`, with **Remark 6.6.19**
(p. 276).

# Signed frames of the kernels on the ends of the cylinder, from the local sc⁺-sections

## The text, paraphrased

On `[0, 1] × X` the section `f̃` is oriented by "`[0, 1]` first, then `o`".  Near `(q, y)` a sheet
of the cobordism is `M̃ = {f̃ = s̃}`, with `T_{(q, y)}M̃ = ℝ·ν ⊕ T_yM`, `M = {f = s̃(q, ·)}`,
`dt(ν) = 1`.  If the Fredholm index is `0`, `M` is a point with a sign and `M̃` a curve, oriented
by `ν` at a positive point and by `−ν` at a negative one.

## What is formalized

The statements of `Polyfold/Chapter15/CylinderPointFrames.lean`, proved with the local
sc⁺-sections `sᵢ`, `s̃ⱼ` of the sheets themselves (no sc-smooth bump functions on `X`):

* `ChartPoint.exists_timeFirst_wedge_signed_of_ops`, `exists_timeFirst_wedge_signed_of_ops_lift`:
  the operator form of `ChartPoint.exists_timeFirst_wedge_signed_of_slice`: for onto
  `L ∈ Lin(f, x)`, `T₁ ∈ Lin(f̃, (t, x))` with `T₁ (0, v) = L v` and any basis `a` of `ker L`,
  there are `ν, ν' ∈ ker T₁` with `t`-components the directions of increasing and of decreasing
  `t` such that `ν ∧ (0, a)` spans the orientation of `ker T₁` given by `e ∧ o` if `a` spans the
  one of `ker L` given by `o`, and `ν' ∧ (0, a)` spans it otherwise.
* **`exists_signed_frame_cubeOrientation_loc`**: `exists_signed_frame_cubeOrientation` without
  bump functions (sheets of any dimension, `0` included).
* **`exists_signed_generator_cubeOrientation_loc`**: the case `dim Mᵢ = 0`: the tangent line of
  the curve `M̃ⱼ` at `(q, y)` has a positive generator `w` with `dt(w) = 1` if the point `y` is
  positive, and with `dt(w) = −1` if not.

## Proof

As in `exists_timeFirst_frame_cubeOrientation_loc`
(`Polyfold/Chapter15/CylinderFrameConventionLocal.lean`), with the two signs of
`exists_timeFirst_coordinates_signed`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Manifold Module
open scoped ContDiff

noncomputable section

namespace Polyfold

open StrongRetr UnitCube

universe u v

section Ops

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) (b : Fin 1 → Bool) {t : Fin 1 → unitInterval}
  (ht : t ∈ (chart b).source)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))

set_option maxHeartbeats 1600000 in
-- the model of the product chart is identified with `ℝ × E`
/-- **Signed frames of `ker T₁` with the `t`-direction first, for operators** (2021 Remark
6.6.19, p. 276, and the proof of Theorem 6.7.1, p. 278): let `L ∈ Lin(f, x)` and
`T₁ ∈ Lin(f̃, (t, x))` be onto with `T₁ (0, v) = L v`; let `dim ker L = k`,
`dim ker T₁ = k + 1`, and let `a₁, …, a_k` be a basis of `ker L`.  Then there are
`ν, ν' ∈ ker T₁` with `t`-components the directions of increasing and of decreasing `t` such
that the orientation of `ker T₁` given by `e ∧ o` is spanned by `ν ∧ (0, a₁) ∧ … ∧ (0, a_k)` if
`a₁ ∧ … ∧ a_k` spans the orientation of `ker L` given by `o`, and by
`ν' ∧ (0, a₁) ∧ … ∧ (0, a_k)` if not. -/
theorem exists_timeFirst_wedge_signed_of_ops (hf : B.IsScFredholmSection f)
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
    (a : Fin k → N₀) (hna : wedge a hk.symm ≠ 0) :
    ∃ (ν ν' : N') (a' : Fin k → N')
      (hna' : wedge (Fin.cons ν a' : Fin (k + 1) → N') hk'.symm ≠ 0)
      (hna'' : wedge (Fin.cons ν' a' : Fin (k + 1) → N') hk'.symm ≠ 0),
      ((ν.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = fun _ => ivSign b) ∧
      ((ν'.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = fun _ => -ivSign b) ∧
      (∀ l, ((a' l).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) = (0, (a l : p.c.φ.model.E 0))) ∧
      (p.orKer o hmem hLs hN₀ = rayOfNeZero ℝ _ hna →
        (p.ivPt b ht q₀).orKer (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o) hT₁m hT₁s hN' =
          rayOfNeZero ℝ _ hna') ∧
      (p.orKer o hmem hLs hN₀ ≠ rayOfNeZero ℝ _ hna →
        (p.ivPt b ht q₀).orKer (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o) hT₁m hT₁s hN' =
          rayOfNeZero ℝ _ hna'') := by
  have hfdN : FiniteDimensional ℝ N₀ := p.finiteDimensional_of_mem_linSet hf hmem hN₀
  have hfdN' : FiniteDimensional ℝ N' :=
    Module.finite_of_finrank_pos (by rw [hk']; exact Nat.succ_pos k)
  have aux := fun (N' : Submodule ℝ ((Fin 1 → ℝ) × p.c.φ.model.E 0))
      (hfd : FiniteDimensional ℝ N') (hk' : finrank ℝ N' = k + 1)
      (hiff : ∀ w : (Fin 1 → ℝ) × p.c.φ.model.E 0, w.1 = 0 → (w ∈ N' ↔ w.2 ∈ N₀)) =>
    exists_timeFirst_coordinates_signed (E₀ := p.c.φ.model.E 0) (N := N₀) (N' := N') hk hk' hiff
      (ivSign_ne_zero b) a hna
  have hiff := p.mem_map_ker_ivPt_iff_of_fst_eq_zero b ht q₀ hE hN₀ hN'
  have h2 := aux N' hfdN' hk' hiff
  obtain ⟨ν, ν', a', hna', hna'', ι, ι', hν1, hν1', ha', hι₀, hι₁, hboth⟩ := h2
  refine ⟨ν, ν', a', hna', hna'', hν1, hν1', ha', hboth _ _ ?_⟩
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
  exact aux2 _ hN' ι' hι₀ hι₁

end ChartPoint

/-- **Signed frames of `ker T₁` with the `t`-direction first, in the chart point of the product
chart with a given lift** `z' = (χ_b(t), z)` of the base point: the statement of
`ChartPoint.exists_timeFirst_wedge_signed_of_ops` for the orientation `ivOrLift`, with the
relation `T₁ (0, v) = L v` read in the model spaces. -/
theorem exists_timeFirst_wedge_signed_of_ops_lift (b : Fin 1 → Bool) {c : StrongBundleChart PX P}
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
    (a : Fin k → N₀) (hna : wedge a hk.symm ≠ 0) :
    ∃ (ν ν' : N') (a' : Fin k → N')
      (hna' : wedge (Fin.cons ν a' : Fin (k + 1) → N') hk'.symm ≠ 0)
      (hna'' : wedge (Fin.cons ν' a' : Fin (k + 1) → N') hk'.symm ≠ 0),
      ((ν.1 : (Fin 1 → ℝ) × c.φ.model.E 0).1 = fun _ => ivSign b) ∧
      ((ν'.1 : (Fin 1 → ℝ) × c.φ.model.E 0).1 = fun _ => -ivSign b) ∧
      (∀ l, ((a' l).1 : (Fin 1 → ℝ) × c.φ.model.E 0) = (0, (a l : c.φ.model.E 0))) ∧
      ((chartPt c hc hx z hz).orKer o hmem hLs hN₀ = rayOfNeZero ℝ _ hna →
        (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
          hz').orKer (ivOrLift b hc hx z hz ht q₀ hxc z' hz' hzz hf hfc hxs hne o) hT₁m hT₁s
          hN' = rayOfNeZero ℝ _ hna') ∧
      ((chartPt c hc hx z hz).orKer o hmem hLs hN₀ ≠ rayOfNeZero ℝ _ hna →
        (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
          hz').orKer (ivOrLift b hc hx z hz ht q₀ hxc z' hz' hzz hf hfc hxs hne o) hT₁m hT₁s
          hN' = rayOfNeZero ℝ _ hna'') := by
  subst hzz
  have hE' : ∀ w : ↥((chartPt c hc hx z hz).ivPt b ht q₀).T,
      (w.1 : (Fin 1 → ℝ) × c.φ.model.E 0).1 = 0 →
        T₁ w = (chartPt c hc hx z hz).ivLin b ht q₀ L w := fun w hw =>
    Subtype.ext ((hE w ((chartPt c hc hx z hz).ivT b ht q₀ w).1 (Prod.ext hw rfl)).trans
      ((chartPt c hc hx z hz).coe_ivLin_apply b ht q₀ L w).symm)
  exact (chartPt c hc hx z hz).exists_timeFirst_wedge_signed_of_ops b ht q₀ hf hfc hxs hne o
    hmem hLs hT₁m hT₁s hE' hN₀ hN' hk hk' a hna

end Ops

namespace SBLocalization

open StrongBundle MPolyfold Linearization15 EpGroupoid SEP

universe w

variable {A : SEP.{w}} {f : A.Obj → A.W}

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid and the product chart point are unfolded in several places
/-- **Signed frames of the kernels for `õ = e ∧ o`, at a pair of sheets** (2021 p. 703, Remark
6.6.19 and the proof of Theorem 6.7.1), from the local sc⁺-sections of the sheets.  Let `K` be a
local branching structure of `(f, Λ)` at `x` described by kernels, `K̃` one of `(f̃, Λ̃)` at
`(q, x)`, and let the sheets `Mᵢ = {f = sᵢ}` of `K` and `M̃ⱼ = {f̃ = s̃ⱼ}` of `K̃` satisfy
`s̃ⱼ(q, ·) = sᵢ` and `dim M̃ⱼ = dim Mᵢ + 1`.  For `y ∈ Mᵢ` with `(q, y) ∈ M̃ⱼ` there are a
basis `α` of `T_yMᵢ = ker (f − sᵢ)'(y)`, a sign `s = ±1` and a vector
`w ∈ T_{(q, y)}M̃ⱼ = ker (f̃ − s̃ⱼ)'(q, y)` with `dt(w) = s` such that `(w, Tι_q α)` is positive
for `(e ∧ o)_{(q, y)}`, where `s = 1` if `α` is positive for `o_y` and `s = −1` if not.  No
sc-smooth bump functions on `X` are used. -/
theorem exists_signed_frame_cubeOrientation_loc
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy) (q : Fin 1 → unitInterval)
    {Λ : A.W → ℚ≥0} {Λ' : (A.cubeSEP 1).W → ℚ≥0} {x : A.Obj} (K : KernelBranching A f Λ x)
    (K' : KernelBranching (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1) Λ' (q, x)) (i : K.ι)
    (j : K'.ι) (hd : K'.dim j = K.dim i + 1)
    (hs : ∀ y ∈ K.O, (q, y) ∈ K'.O → cubeVal (K'.s j (q, y)) = ((q, y), K.s i y))
    {y : A.Obj} (hy : y ∈ K.M i) (hy' : ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.M j) :
    ∃ α : Fin (K.dim i) → A.X.PObj.TangentSpace,
      (∀ l, α l ∈ A.X.PObj.submanifoldTangent (K.M i) y) ∧
      ∃ (s : ℝ) (w : (A.cubeSEP 1).X.PObj.TangentSpace),
        ((s = 1 ∧ α ∈ K.frames hf.2 hsec o i y) ∨ (s = -1 ∧ α ∉ K.frames hf.2 hsec o i y)) ∧
        w ∈ (A.cubeSEP 1).X.PObj.submanifoldTangent (K'.M j) (q, y) ∧
        cylTimeComponent A q w = s ∧
          (fun k => (Fin.cons w (fun l => (cubeFaceIncl A q).tangent.obj (α l)) :
            Fin (K.dim i + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) (Fin.cast hd k)) ∈
            K'.frames (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
              (cubeOrientation hf hft hsec o) j (q, y) := by
  classical
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj)
    (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)
  have hf₀ : A.B.IsScFredholmSection f := hf.2
  have hfc : (ivBundle A.B).IsScFredholmSection (cubeLift (n := 1) f hf₀.isScSmooth.1) :=
    (hft.paramCube (n := 1)).toIsScFredholmSection
  have hys := K.smooth i y hy
  have hzs := K'.smooth j (q, y) hy'
  -- the charts
  obtain ⟨c, hc, hyc⟩ : ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c ∧ y ∈ c.φ.source :=
    ⟨orChart A.B y, isChart_orChart y, mem_orChart y⟩
  have hb := mem_chart_corner q
  obtain ⟨q₀⟩ : Nonempty (pullbackSpace A.P (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)) :=
    ⟨cubeLiftEp (n := 1) f hf.1.1.1 (q, y)⟩
  have hc' : (A.cubeSEP 1).B.IsChart (ivChart (corner q) c q₀) := isChart_ivChart (corner q) hc q₀
  have hzc' : ((q, y) : (Fin 1 → unitInterval) × A.Obj) ∈ (ivChart (corner q) c q₀).φ.source :=
    mem_ivChart_source q₀ hyc hb
  have hzz := ivChart_lift_eq (corner q) _ (exists_lift_of_smooth c hyc hys).choose_spec q q₀ _
    (exists_lift_of_smooth (ivChart (corner q) c q₀) hzc' hzs).choose_spec
  -- the operators `(f − sᵢ)'(y)` and `(f̃ − s̃ⱼ)'(q, y)`
  have hLex := K.exists_op_frames_pt hf₀ hsec o hy (chartPtOf c hc hyc hys)
  obtain ⟨L, hLm, hLs, hnL, hLcoe, hLker, hLfr⟩ := hLex
  have hTex := K'.exists_op_frames_pt (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2
    hsec' (cubeOrientation hf hft hsec o) hy'
    (chartPtOf (B := ivBundle A.B) (ivChart (corner q) c q₀)
      (isChart_ivChart (corner q) hc q₀) hzc' hzs)
  obtain ⟨T₁, hTm, hTs, hnT, hTcoe, hTker, hTfr⟩ := hTex
  have hne := ChartPoint.linSet_nonempty (chartPtOf c hc hyc hys) hf₀ hys hsec
  -- the orientation `e ∧ o` in the product chart
  have hor : toChartOr hfc hzs (ivChart (corner q) c q₀) (isChart_ivChart (corner q) hc q₀) hzc'
      (cubeOrientation hf hft hsec o (q, y) hzs) =
      ivOrOf (corner q) hc hyc hys hb q₀ hf₀ hfc hne (toChartOr hf₀ hys c hc hyc (o y hys)) := by
    have h := toChartOr_ivFirstFun hf₀ hfc hsec o (q, y) hzs (corner q) hb hc hyc q₀
      (isChart_ivChart (corner q) hc q₀) hzc' hne
    exact h.trans (DFunLike.congr_fun (ChartPoint.orTransfer_self _ hfc hzs) _)
  -- `(f̃ − s̃ⱼ)'(q, y) (0, v) = (f − sᵢ)'(y) v`
  have hE : ∀ (w : ↥(chartPtOf (B := ivBundle A.B) (ivChart (corner q) c q₀)
        (isChart_ivChart (corner q) hc q₀) hzc' hzs).T) (v : ↥(chartPtOf c hc hyc hys).T),
      (w.1 : (Fin 1 → ℝ) × c.φ.model.E 0) = (0, (v.1 : c.φ.model.E 0)) →
        ((T₁ w).1 : c.F 0) = ((L v).1 : c.F 0) := fun w v hwv => by
    have h1 := hTcoe w
    have h2 := hLcoe v
    have h3 := subDeriv_ivChart_restrictInter_slice hf₀.isScSmooth
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2.isScSmooth K.isOpen_O
      (K.isScPlus i) K'.isOpen_O (K'.isScPlus j) q hs (chartPtOf c hc hyc hys) (K.mem_O hy)
      (K'.mem_O hy') (corner q) hb q₀ v.1
    have h4 := congrArg₂ (fun (z' : (ivChart (corner q) c q₀).φ.model.E 1)
        (u : (Fin 1 → ℝ) × c.φ.model.E 0) =>
      subDeriv (A := A.cubeSEP 1) ((ivChart (corner q) c q₀).restrictInter K'.isOpen_O)
        (cubeLiftEp (n := 1) f hf.1.1.1) (K'.s j) z' u) hzz hwv
    exact h1.trans (h4.trans (h3.trans h2.symm))
  -- a basis of `ker (f − sᵢ)'(y)`
  have : FiniteDimensional ℝ ↥((LinearMap.ker (L : ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ]
      ↥(chartPtOf c hc hyc hys).K)).map ((chartPtOf c hc hyc hys).T.subtypeL :
        ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ] (chartPtOf c hc hyc hys).c.φ.model.E 0)) :=
    (chartPtOf c hc hyc hys).finiteDimensional_of_mem_linSet hf₀ hLm rfl
  obtain ⟨bA⟩ : Nonempty (Basis (Fin (K.dim i)) ℝ
      ↥((LinearMap.ker (L : ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ]
        ↥(chartPtOf c hc hyc hys).K)).map ((chartPtOf c hc hyc hys).T.subtypeL :
          ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ] (chartPtOf c hc hyc hys).c.φ.model.E 0))) :=
    ⟨Module.finBasisOfFinrankEq ℝ _ hnL⟩
  have hna : wedge (fun l => bA l) hnL.symm ≠ 0 := wedge_basis_ne_zero' bA hnL.symm
  -- the two generators of the complement in `ker (f̃ − s̃ⱼ)'(q, y)`
  have hex := exists_timeFirst_wedge_signed_of_ops_lift (corner q) hc hyc _
    (exists_lift_of_smooth c hyc hys).choose_spec hb q₀ hzc' _
    (exists_lift_of_smooth (ivChart (corner q) c q₀) hzc' hzs).choose_spec hzz hf₀ hfc hys hne
    (toChartOr hf₀ hys c hc hyc (o y hys)) hLm hLs hTm hTs hE rfl rfl hnL (hnT.trans hd)
    (fun l => bA l) hna
  obtain ⟨ν₀, ν₀', a', hna', hna'', hν1, hν1', ha', hpos, hneg⟩ := hex
  -- tangent vectors of `Mᵢ` with chart vectors `a`
  have hαex : ∀ l, ∃ α ∈ A.X.PObj.submanifoldTangent (K.M i) y,
      chartVec (chartPtOf c hc hyc hys).c.isChart α = (bA l).1 := fun l =>
    (hLker (bA l).1).1 (bA l).2
  choose α hαT hαv using hαex
  have hαm : ∀ l, chartVec (chartPtOf c hc hyc hys).c.isChart (α l) ∈
      (LinearMap.ker (L : ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ]
        ↥(chartPtOf c hc hyc hys).K)).map ((chartPtOf c hc hyc hys).T.subtypeL :
          ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ] (chartPtOf c hc hyc hys).c.φ.model.E 0) := fun l =>
    mem_submodule_of_eq_of_mem (hαv l) (bA l).2
  have hαw : wedge (fun l => (⟨chartVec (chartPtOf c hc hyc hys).c.isChart (α l), hαm l⟩ :
      ↥((LinearMap.ker (L : ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ]
        ↥(chartPtOf c hc hyc hys).K)).map ((chartPtOf c hc hyc hys).T.subtypeL :
          ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ] (chartPtOf c hc hyc hys).c.φ.model.E 0)))) hnL.symm =
      wedge (fun l => bA l) hnL.symm := by
    congr 1
    exact funext fun l => Subtype.ext (hαv l)
  have htO : α ∈ K.frames hf₀ hsec o i y ↔
      (chartPtOf c hc hyc hys).orKer (toChartOr hf₀ hys c hc hyc (o y hys)) hLm hLs rfl =
        rayOfNeZero ℝ _ hna := by
    constructor
    · intro hF
      obtain ⟨-, hm', hne', hr'⟩ := (hLfr α).1 hF
      exact hr'.trans (rayOfNeZero_congr hαw _ _)
    · intro hr
      exact (hLfr α).2 ⟨hαT, hαm, by rw [hαw]; exact hna,
        hr.trans (rayOfNeZero_congr hαw.symm _ _)⟩
  -- the generator for the sign of `α`
  obtain ⟨ν, hna₁, s, hsF, hν₁, hray'⟩ : ∃ ν, ∃ hna₁ : wedge (Fin.cons ν a' :
      Fin (K.dim i + 1) → _) (hnT.trans hd).symm ≠ 0, ∃ s : ℝ,
      ((s = 1 ∧ α ∈ K.frames hf₀ hsec o i y) ∨ (s = -1 ∧ α ∉ K.frames hf₀ hsec o i y)) ∧
      ((ν.1 : (Fin 1 → ℝ) × c.φ.model.E 0).1 = fun _ => s * ivSign (corner q)) ∧
      (chartPtOf (B := ivBundle A.B) (ivChart (corner q) c q₀)
        (isChart_ivChart (corner q) hc q₀) hzc' hzs).orKer
        (ivOrOf (corner q) hc hyc hys hb q₀ hf₀ hfc hne (toChartOr hf₀ hys c hc hyc (o y hys)))
        hTm hTs rfl = rayOfNeZero ℝ _ hna₁ := by
    by_cases hF : α ∈ K.frames hf₀ hsec o i y
    · exact ⟨ν₀, hna', 1, Or.inl ⟨rfl, hF⟩, by rw [one_mul]; exact hν1, hpos (htO.1 hF)⟩
    · exact ⟨ν₀', hna'', -1, Or.inr ⟨rfl, hF⟩, by rw [neg_one_mul]; exact hν1',
        hneg fun h => hF (htO.2 h)⟩
  -- tangent vectors of `M̃ⱼ`
  have hwex := (hTker ν.1).1 ν.2
  obtain ⟨w, hwT, hwv⟩ := hwex
  have hβb : ∀ l, (A.cubeSEP 1).X.PObj.levelVal 1 ((A.cubeSEP 1).X.PObj.tangentProj
      ((cubeFaceIncl A q).tangent.obj (α l))) = (q, y) := fun l => by
    have h := levelVal_tangentProj_tangentMap (isScSmoothMap_cubeFace A q) (α l)
    rw [(hαT l).1] at h
    exact h
  have hβv : ∀ l, chartVec (ivChart (corner q) c q₀).isChart
      ((cubeFaceIncl A q).tangent.obj (α l)) = (a' l).1 := fun l => by
    have hαb : A.X.PObj.levelVal 1 (A.X.PObj.tangentProj (α l)) ∈ c.φ.source := by
      rw [(hαT l).1]
      exact hyc
    have h := chartVec_tangentMap_prodMk (P := A.X.PObj) (P₀ := cubePolyfold 1)
      (isScSmoothMap_cubeFace A q) (isChart_chart (corner q)) hb c.isChart (α := α l) hαb
    exact h.trans ((congrArg (Prod.mk (0 : Fin 1 → ℝ)) (hαv l)).trans (ha' l).symm)
  have hβT : ∀ l, (cubeFaceIncl A q).tangent.obj (α l) ∈
      (A.cubeSEP 1).X.PObj.submanifoldTangent (K'.M j) (q, y) := fun l => by
    have hγex := (hTker (a' l).1).1 (a' l).2
    obtain ⟨γ, hγ, hγv⟩ := hγex
    have he : γ = (cubeFaceIncl A q).tangent.obj (α l) :=
      chartVec_injOn (ivChart (corner q) c q₀).isChart hzc' hγ.1 (hβb l)
        (hγv.trans (hβv l).symm)
    rw [← he]
    exact hγ
  -- the `t`-component of `w`
  have hτ : cylTimeComponent A q w = s := by
    have hbase : ((cubePolyfold 1).prod A.X.PObj).levelVal 1
        (((cubePolyfold 1).prod A.X.PObj).tangentProj w) = (q, y) := hwT.1
    have h := chartVec_prod_fst (P := A.X.PObj) (isChart_chart (corner q)) c.isChart (w := w)
      (by rw [hbase]; exact ⟨hb, hyc⟩)
    have h2 : (chartVec ((isChart_chart (corner q)).prod c.isChart) w).1 =
        fun _ => s * ivSign (corner q) := (congrArg Prod.fst hwv).trans hν₁
    change cubeTimeSign q * (chartVec (isChart_chart (corner q))
      (MPolyfold.tangentMap (isScSmoothMap_fst (cubePolyfold 1) A.X.PObj) w) : Fin 1 → ℝ) 0 = s
    rw [← h, h2, cubeTimeSign_eq_ivSign]
    change ivSign (corner q) * (s * ivSign (corner q)) = s
    rw [mul_comm s, ← mul_assoc, ivSign_mul_self, one_mul]
  refine ⟨α, hαT, s, w, hsF, hwT, hτ, ?_⟩
  -- the frame `(w, Tι_q α)`
  have hval : ∀ m : Fin (K.dim i + 1), chartVec (ivChart (corner q) c q₀).isChart
      ((Fin.cons w (fun l => (cubeFaceIncl A q).tangent.obj (α l)) :
        Fin (K.dim i + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) m) =
      ((Fin.cons ν a' : Fin (K.dim i + 1) → _) m).1 := fun m => by
    refine Fin.cases ?_ (fun l => ?_) m
    · exact hwv
    · exact hβv l
  have hTan : ∀ m : Fin (K.dim i + 1), (Fin.cons w (fun l => (cubeFaceIncl A q).tangent.obj (α l)) :
      Fin (K.dim i + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) m ∈
      (A.cubeSEP 1).X.PObj.submanifoldTangent (K'.M j) (q, y) := fun m => by
    refine Fin.cases ?_ (fun l => ?_) m
    · exact hwT
    · exact hβT l
  have hr₁ := (congrArg (fun o' => (chartPtOf (B := ivBundle A.B) (ivChart (corner q) c q₀)
    (isChart_ivChart (corner q) hc q₀) hzc' hzs).orKer o' hTm hTs rfl) hor).trans hray'
  have hw' := fun hm => wedge_mk_comp_finCast hd (Fin.cons ν a' : Fin (K.dim i + 1) → _)
    (fun k : Fin (K'.dim j) => chartVec (ivChart (corner q) c q₀).isChart
      ((Fin.cons w (fun l => (cubeFaceIncl A q).tangent.obj (α l)) :
        Fin (K.dim i + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) (Fin.cast hd k)))
    (fun k => hval (Fin.cast hd k)) hm (hnT.trans hd).symm hnT.symm
  have hm := fun k : Fin (K'.dim j) => mem_submodule_of_eq_of_mem (hval (Fin.cast hd k))
    ((Fin.cons ν a' : Fin (K.dim i + 1) → _) (Fin.cast hd k)).2
  exact (hTfr _).2 ⟨fun k => hTan _, hm, fun h0 => hna₁ ((hw' hm).symm.trans h0),
    hr₁.trans (rayOfNeZero_congr (hw' hm).symm _ _)⟩


/-- **The tangent line of a curve of the cobordism over a signed point** (Corollary 15.4.4 for
Fredholm index `0`, p. 703; Remark 6.6.19), from the local sc⁺-sections of the sheets.  In the
situation of `exists_signed_frame_cubeOrientation_loc` with `dim Mᵢ = 0`: there is
`w ∈ T_{(q, y)}M̃ⱼ` positive for `(e ∧ o)_{(q, y)}` with `dt(w) = 1` if the point `y` of `Mᵢ` is
positive (the orientation `o_{i,y}` induced by `o` has a frame), and with `dt(w) = −1` if it is
negative. -/
theorem exists_signed_generator_cubeOrientation_loc
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy) (q : Fin 1 → unitInterval)
    {Λ : A.W → ℚ≥0} {Λ' : (A.cubeSEP 1).W → ℚ≥0} {x : A.Obj} (K : KernelBranching A f Λ x)
    (K' : KernelBranching (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1) Λ' (q, x)) (i : K.ι)
    (j : K'.ι) (h0 : K.dim i = 0) (h1 : K'.dim j = 1)
    (hs : ∀ y ∈ K.O, (q, y) ∈ K'.O → cubeVal (K'.s j (q, y)) = ((q, y), K.s i y))
    {y : A.Obj} (hy : y ∈ K.M i) (hy' : ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.M j) :
    ∃ (s : ℝ) (w : (A.cubeSEP 1).X.PObj.TangentSpace),
      ((s = 1 ∧ (K.frames hf.2 hsec o i y).Nonempty) ∨
        (s = -1 ∧ ¬ (K.frames hf.2 hsec o i y).Nonempty)) ∧
      w ∈ (A.cubeSEP 1).X.PObj.submanifoldTangent (K'.M j) (q, y) ∧
      cylTimeComponent A q w = s ∧
      (fun _ => w) ∈ K'.frames (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
        (cubeOrientation hf hft hsec o) j (q, y) := by
  have hd : K'.dim j = K.dim i + 1 := by rw [h0, h1]
  obtain ⟨α, -, s, w, hsF, hwT, hτ, hfr⟩ :=
    exists_signed_frame_cubeOrientation_loc hf hft hsec hsec' o q K K' i j hd hs hy hy'
  have huniq : ∀ β : Fin (K.dim i) → A.X.PObj.TangentSpace, β = α := fun β =>
    funext fun l => (by have := l.2; omega : False).elim
  refine ⟨s, w, hsF.imp (fun h => ⟨h.1, α, h.2⟩)
    (fun h => ⟨h.1, fun ⟨β, hβ⟩ => h.2 (huniq β ▸ hβ)⟩), hwT, hτ, ?_⟩
  have he : (fun _ : Fin (K'.dim j) => w) =
      fun k => (Fin.cons w (fun l => (cubeFaceIncl A q).tangent.obj (α l)) :
        Fin (K.dim i + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) (Fin.cast hd k) := by
    funext k
    have hk0 : Fin.cast hd k = 0 := Fin.ext (by
      have := k.2
      change (k : ℕ) = 0
      omega)
    rw [hk0, Fin.cons_zero]
  rw [he]
  exact hfr

end SBLocalization

end Polyfold
