import Polyfold.Chapter15.CanonicalLiftContinuityLocalFrames
import Polyfold.Chapter15.CylinderFrameConventionLocalRestr

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–703 (**Theorem 15.4.1** and the proof of **Corollary 15.4.4**).

# The frames `o_{i,y}` of a sheet read in any chart point

## The text, paraphrased

(pp. 701–702) Near a point of `supp(Λ ∘ f)` the sheets are `Mᵢ = {f = sᵢ}` for the local
sc⁺-sections `sᵢ` of a local sc⁺-section structure, and `o_y` orients `ker (f − sᵢ)'(y)`.

## What is formalized (namespace `Polyfold.SBLocalization`)

Let `K` be a local branching structure described by kernels, with local sc⁺-sections `sᵢ` on the
open set `O`, and let `p` be any chart point at `z ∈ Mᵢ` (the domain of its chart need not lie in
`O`).

* **`KernelBranching.exists_op_frames_pt`**: there is an onto operator `T₁ ∈ Lin(f, z)`, read
  in `p`, which is `D((f̂ − ŝᵢ) ∘ r)(z)` computed in the chart of `p` restricted to `O`; the chart
  vectors of `T_zMᵢ` are `ker T₁`, of dimension `dᵢ`; and a frame of `T_zMᵢ` is in `o_{i,z}` iff
  the wedge of its chart vectors spans the orientation of `ker T₁` induced by `o_z`
  (`ChartPoint.orKer`).

No sc⁺-section over all of the base enters.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}} {f : A.Obj → A.W} {Λ : A.W → ℚ≥0} {x : A.Obj}

namespace KernelBranching

variable (K : KernelBranching A f Λ x)

set_option maxHeartbeats 1600000 in
-- the chart point and its restriction to `O` have the same model spaces after unfolding
/-- **The frames `o_{i,z}` read in any chart point `p` at `z ∈ Mᵢ`** (2021 pp. 701–702): there
is an onto member `T₁` of `Lin(f, z)`, read in `p`, with `T₁ v = D((f̂ − ŝᵢ) ∘ r)(z) v` (the
derivative in the chart of `p` restricted to the domain `O` of `sᵢ`), such that the chart vectors
of `T_zMᵢ` are the kernel of `T₁`, of dimension `dᵢ`, and a frame `v` of `T_zMᵢ` is in `o_{i,z}`
iff the wedge of its chart vectors spans the orientation of `ker T₁` induced by `o_z` read in
`p`. -/
theorem exists_op_frames_pt (hf : A.B.IsScFredholmSection f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy) {i : K.ι} {z : A.Obj}
    (hz : z ∈ K.M i) (p : ChartPoint A.B z) :
    ∃ (T₁ : ↥p.T →L[ℝ] ↥p.K) (hT₁ : T₁ ∈ p.linSet f) (hT₁s : Surjective T₁)
      (hn : finrank ℝ ↥((LinearMap.ker (T₁ : ↥p.T →ₗ[ℝ] ↥p.K)).map
        (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)) = K.dim i),
      (∀ v : ↥p.T, ((T₁ v).1 : p.c.F 0) =
        subDeriv (p.c.restrictInter K.isOpen_O) f (K.s i) p.z v.1) ∧
      (∀ u : p.c.φ.model.E 0,
        u ∈ (LinearMap.ker (T₁ : ↥p.T →ₗ[ℝ] ↥p.K)).map
            (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) ↔
          ∃ α ∈ A.X.PObj.submanifoldTangent (K.M i) z, chartVec p.c.isChart α = u) ∧
      ∀ v : Fin (K.dim i) → A.X.PObj.TangentSpace,
        v ∈ K.frames hf hsec o i z ↔
          (∀ j, v j ∈ A.X.PObj.submanifoldTangent (K.M i) z) ∧
          ∃ (hmem : ∀ j, chartVec p.c.isChart (v j) ∈
              (LinearMap.ker (T₁ : ↥p.T →ₗ[ℝ] ↥p.K)).map
                (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0))
            (hne : wedge (fun j => (⟨chartVec p.c.isChart (v j), hmem j⟩ :
              ↥((LinearMap.ker (T₁ : ↥p.T →ₗ[ℝ] ↥p.K)).map
                (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)))) hn.symm ≠ 0),
            p.orKer ((orxPt A.B z (K.smooth i z hz)).orTransfer p hf (K.smooth i z hz)
                (o z (K.smooth i z hz))) hT₁ hT₁s rfl = rayOfNeZero ℝ _ hne := by
  classical
  have hzs := K.smooth i z hz
  have hfs : f z = K.s i z := K.eq_of_mem hz
  let pr : ChartPoint A.B z := p.restr K.isOpen_O (K.mem_O hz)
  have hsub : pr.c.φ.source ⊆ K.O := p.restr_source_subset K.isOpen_O (K.mem_O hz)
  let S : ↥pr.T →L[ℝ] ↥pr.K := subOp hf.isScSmooth (K.isScPlus i) pr hsub hfs
  have hS : S ∈ pr.linSet f :=
    subOp_mem_linSet hf K.isOpen_O (K.isScPlus i) pr hsub hfs hzs hsec
  have hSs : Surjective S := K.surj_pt hf hz pr hsub
  let AT : ↥pr.T ≃L[ℝ] ↥p.T := pr.transferT p
  let AK : ↥pr.K ≃L[ℝ] ↥p.K := pr.transferK p
  let T₁ : ↥p.T →L[ℝ] ↥p.K :=
    (AK : ↥pr.K →L[ℝ] ↥p.K) ∘L S ∘L (p.transferT pr : ↥p.T →L[ℝ] ↥pr.T)
  have hT₁ : T₁ ∈ p.linSet f := pr.conj_mem_linSet p hf hzs hS
  have hconj : ∀ v, T₁ (AT v) = AK (S v) := pr.transfer_conj_apply p S
  have hT₁s : Surjective T₁ := fun k => by
    have hex := hSs (AK.symm k)
    obtain ⟨v, hv⟩ := hex
    exact ⟨AT v, by rw [hconj, hv, AK.apply_symm_apply]⟩
  have hn₀ := K.finrank_ker_pt hf hz pr hsub
  have hAT : ∀ v : ↥pr.T, ((AT v : ↥p.T) : p.c.φ.model.E 0) = _root_.id (v : pr.c.φ.model.E 0) :=
    fun v => p.coe_transferT_restr K.isOpen_O (K.mem_O hz) v
  let κ := conjKerEquivOfMap AT AK hconj pr.T.subtypeL Subtype.val_injective rfl p.T.subtypeL
    Subtype.val_injective rfl
  have hκ := ChartPoint.coe_conjKerEquivOfMap_eq pr p AT AK _root_.id hAT hconj rfl rfl
  have hn : finrank ℝ ↥((LinearMap.ker (T₁ : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)) = K.dim i :=
    κ.symm.finrank_eq.trans hn₀
  -- the two kernels are the same subset of the model
  have hNN : ∀ u : p.c.φ.model.E 0,
      u ∈ (LinearMap.ker (T₁ : ↥p.T →ₗ[ℝ] ↥p.K)).map
          (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) ↔
        u ∈ (LinearMap.ker (S : ↥pr.T →ₗ[ℝ] ↥pr.K)).map
          (pr.T.subtypeL : ↥pr.T →ₗ[ℝ] pr.c.φ.model.E 0) := fun u => by
    constructor
    · intro hu
      have h1 := hκ (κ.symm ⟨u, hu⟩)
      rw [κ.apply_symm_apply] at h1
      have h2 : u = ((κ.symm ⟨u, hu⟩).1 : pr.c.φ.model.E 0) := h1
      rw [h2]
      exact (κ.symm ⟨u, hu⟩).2
    · intro hu
      have h1 : ((κ ⟨u, hu⟩).1 : p.c.φ.model.E 0) = u := hκ ⟨u, hu⟩
      rw [← h1]
      exact (κ ⟨u, hu⟩).2
  -- chart vectors
  have hkr := (K.ker_eq_pt hz pr hsub).trans
    (kerSet_eq_coe_map_ker hf.isScSmooth (K.isScPlus i) pr hsub hfs)
  have hcvr : ∀ α ∈ A.X.PObj.submanifoldTangent (K.M i) z, chartVec pr.c.isChart α ∈
      (LinearMap.ker (S : ↥pr.T →ₗ[ℝ] ↥pr.K)).map
        (pr.T.subtypeL : ↥pr.T →ₗ[ℝ] pr.c.φ.model.E 0) := fun α hα =>
    (Set.ext_iff.1 hkr _).1 (mem_image_of_mem _ hα)
  have hzl : levelLift pr.c.φ 1 z = pr.z :=
    pr.c.φ.model.E.toBase_injective 1 ((A.X.PObj.toBase_levelLift pr.c.isChart pr.mem_source
      (smoothSet_subset_levelSet 1 hzs)).trans pr.toBase_z.symm)
  have hcv : ∀ α ∈ A.X.PObj.submanifoldTangent (K.M i) z,
      chartVec p.c.isChart α = chartVec pr.c.isChart α := fun α hα => by
    have h := chartVec_eq_scDeriv_transition pr.c.isChart p.c.isChart (pr.baseRet_retract p)
      pr.mem_source p.mem_source hα.1
    rw [hzl] at h
    have hmem := hcvr α hα
    obtain ⟨w, -, hw⟩ := hmem
    have hw' : (w : pr.c.φ.model.E 0) = chartVec pr.c.isChart α := hw
    have h3 := p.coe_transferT_restr K.isOpen_O (K.mem_O hz) w
    have h4 : pr.baseDeriv p (w : pr.c.φ.model.E 0) = (w : pr.c.φ.model.E 0) := h3
    rw [hw'] at h4
    exact h.trans h4
  have hor : (orxPt A.B z hzs).orTransfer p hf hzs (o z hzs) =
      ((orxPt A.B z hzs).orTransfer pr hf hzs (o z hzs)).conj
        (hC' := p.isFredholm_of_mem_linSet hf) AT AK (pr.transfer_mem_linSet p hf hzs) :=
    (DFunLike.congr_fun (ChartPoint.orTransfer_trans (orxPt A.B z hzs) pr p hf hzs)
      (o z hzs)).symm
  refine ⟨T₁, hT₁, hT₁s, hn, fun v => ?_, fun u => ?_, fun v => ?_⟩
  · have h1 := p.coe_transferK_restr K.isOpen_O (K.mem_O hz) (S (p.transferT pr v))
    have h2 := p.coe_transferT_to_restr K.isOpen_O (K.mem_O hz) v
    refine h1.trans ?_
    change subDeriv pr.c f (K.s i) pr.z ((p.transferT pr v : ↥pr.T).1 : pr.c.φ.model.E 0) = _
    exact congrArg (subDeriv pr.c f (K.s i) pr.z) h2
  · refine (hNN u).trans ?_
    constructor
    · intro hu
      have h1 := (Set.ext_iff.1 hkr u).2 hu
      obtain ⟨α, hα, hαu⟩ := h1
      exact ⟨α, hα, (hcv α hα).trans hαu⟩
    · rintro ⟨α, hα, rfl⟩
      rw [hcv α hα]
      exact hcvr α hα
  · have hfr := K.frames_eq_pt hf hsec o hz pr hsub
    have step1 := mem_kerFrames_iff hf K.isOpen_O (K.isScPlus i) pr hsub hfs hzs hsec hSs
      ((orxPt A.B z hzs).orTransfer pr hf hzs (o z hzs))
      (A.X.PObj.submanifoldTangent (K.M i) z) hn₀ rfl hS hSs rfl hn₀ v
    refine (Set.ext_iff.1 hfr v).trans (step1.trans (and_congr_right fun hvL => ?_))
    have step2 := pr.exists_ray_orKer_conj_iff p hf hf AT AK _root_.id injective_id hAT
      (pr.transfer_mem_linSet p hf hzs) ((orxPt A.B z hzs).orTransfer pr hf hzs (o z hzs))
      hS hT₁ hconj hSs hT₁s rfl rfl hn₀.symm hn.symm
      (fun j => chartVec pr.c.isChart (v j)) (fun j => chartVec p.c.isChart (v j))
      (fun j => hcv _ (hvL j))
    have key : ∀ o' : p.Or f hf, o' = ((orxPt A.B z hzs).orTransfer pr hf hzs (o z hzs)).conj
          (hC' := p.isFredholm_of_mem_linSet hf) AT AK (pr.transfer_mem_linSet p hf hzs) →
        ((∃ (hm : ∀ j, chartVec pr.c.isChart (v j) ∈
              (LinearMap.ker (S : ↥pr.T →ₗ[ℝ] ↥pr.K)).map
                (pr.T.subtypeL : ↥pr.T →ₗ[ℝ] pr.c.φ.model.E 0))
            (hne : wedge (fun j => (⟨chartVec pr.c.isChart (v j), hm j⟩ :
              ↥((LinearMap.ker (S : ↥pr.T →ₗ[ℝ] ↥pr.K)).map
                (pr.T.subtypeL : ↥pr.T →ₗ[ℝ] pr.c.φ.model.E 0)))) hn₀.symm ≠ 0),
            pr.orKer ((orxPt A.B z hzs).orTransfer pr hf hzs (o z hzs)) hS hSs rfl =
              rayOfNeZero ℝ _ hne) ↔
          ∃ (hm : ∀ j, chartVec p.c.isChart (v j) ∈
              (LinearMap.ker (T₁ : ↥p.T →ₗ[ℝ] ↥p.K)).map
                (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0))
            (hne : wedge (fun j => (⟨chartVec p.c.isChart (v j), hm j⟩ :
              ↥((LinearMap.ker (T₁ : ↥p.T →ₗ[ℝ] ↥p.K)).map
                (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)))) hn.symm ≠ 0),
            p.orKer o' hT₁ hT₁s rfl = rayOfNeZero ℝ _ hne) := by
      rintro _ rfl
      exact step2.symm
    exact key _ hor

end KernelBranching

end SBLocalization

end Polyfold
