import Polyfold.Chapter15.KernelFramesPerturbed
import Polyfold.Chapter15.CanonicalLiftNaturality
import Polyfold.Chapter15.KernelBranchingIndex
import Polyfold.Chapter6.TangentOrientationFamily
import Polyfold.Chapter6.SolutionSetOpen
import Polyfold.Chapter9.ManifoldBridge

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702: **Theorem 15.4.1** and **Definition 15.4.2** (2017: Theorem 15.6, Definition 15.7),
the continuity of the canonical lift `T̂_((f, o), Λ)` along the sheets.

# The canonical lift is continuous along the sheets

## The text, paraphrased

(Theorem 15.4.1) For an oriented sc-Fredholm section functor `(f, o)` and an sc⁺-multisection
`Λ` in good position, `T_Θ`, `Θ = Λ ∘ f`, has a canonical lift
`T̂(y) = ∑_{i : f(y) = sᵢ(y)} σᵢ · (ker (f − sᵢ)'(y), o_{i,y})` to `Ĝr(X)`, with `o_{i,y}` the
orientation of `ker (f − sᵢ)'(y) = T_yMᵢ` induced by `o_y`.  (Definition 15.4.2) It is the
canonical orientation of `Θ`; in particular the sheets `Mᵢ` are oriented by `y ↦ o_{i,y}`
(Definition 9.3.2).

## What is formalized

* `MPolyfold.exists_basis_incFrame_mem_of_isOrientedAt`,
  `MPolyfold.continuousOn_modelDeriv_levelLift`,
  `MPolyfold.exists_continuousOn_frame_of_eventually`: for an `n`-dimensional submanifold `N`
  with a corner structure, a family `F y` of orientations of the spaces `T_yN` is continuous in
  the sense of Definition 9.3.2 near `x` as soon as the sign of the frame field
  `(Tι(b₁), …, Tι(bₙ))` of corner coordinates is locally constant at `x`.
* **`KernelBranching.eventually_incFrame_mem_frames`**: for an orientation `o` of `f`
  (Part I's Definition 6.6.16) the sign of such a frame field of a sheet `Mᵢ` for `o_{i,y}` is
  locally constant.  Near `x₀ ∈ Mᵢ` the local section `sᵢ` is replaced by a global sc⁺-section
  `ŝ` (bump functions); `Mᵢ` is then the solution set of `g = f + (−ŝ)`, `o` is an orientation of
  `g` (`isSectionOrientation_sectionAdd`), `o_{i,y}` is Part I's tangent orientation of `g`
  (`KernelBranching.mem_frames_iff_tangentOr`), and along segments in corner coordinates of
  `Mᵢ` both the tangent orientations and the frame field are orientations of the line bundle of
  the kernels (`isLineOrientation_tangentOr_of_family_of_isSectionOrientation`).
* **`KernelBranching.framesContinuous`**, **`canonContinuous`**: `CanonContinuous` for an
  orientation `o` of `f`, on a tame `X` with sc-smooth bump functions.
* **`theorem_15_4_1_of_isSectionOrientation`**: Theorem 15.4.1 in `Ĝr(X)` for an orientation `o`
  of `f` invariant under the morphisms, `(f, Λ)` in good position and `f` of index `n` on
  `supp(Λ ∘ f)`, with the independence of Theorem 9.2.1 as a hypothesis.

## Reading

"`(f, o)` oriented" is read as: `o` is an orientation of `f` in the sense of Part I
(`IsSectionOrientation`, Definition 6.6.16) and is invariant under the morphisms
(`IsOrInvariant`, Definition 12.5.4).  The continuity statement uses the first property only.
The family of the kernels along a path in `Mᵢ` is given by the frame field of the corner
coordinates, so only the surjectivity of `(f − sᵢ)'(y)` is used and the points of `∂X` are
included (the sheets are in good position there, not in general position).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Module Manifold

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {N : Set X} [ParacompactSpace N] {n : ℕ} {hY : P.IsSubMPolyfold N}
  {hcs : (subPolyfold hY).HasCornerStructureOfDim n}

/-- **Some basis of `ℝⁿ` has a positive frame**, for a set of frames `F` orienting `T_yN`
(`exists_basis_incFrame_mem_frames` for one oriented tangent space). -/
theorem exists_basis_incFrame_mem_of_isOrientedAt (hn : 0 < n) (hN : P.IsSubmanifoldOfDim N n)
    {y : N} {F : Set (Fin n → P.TangentSpace)}
    (hF : P.IsOrientedAt y.1 ⟨n, P.submanifoldTangent N y.1, F⟩)
    (κ : CornerCoords (subPolyfold hY) n) (hy : y ∈ κ.s) :
    ∃ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      (fun i => incFrame hcs κ hy (b i)) ∈ F := by
  classical
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y.1
  set d := (hN.1.data y.2).toSubData
  have hyσ : y ∈ (subChart d hφ y).source :=
    d.mem_shrink φ y.2 (hN.1.mem_data_V y.2) hyφ
  have hyχ : y ∈ κ.χ.source := κ.s_subset hy
  have hz : κ.χ.model.E.toBase 1 (levelLift κ.χ 1 y) = κ.χ y :=
    (subPolyfold hY).toBase_levelLift κ.isChart hyχ (levelVal_mem (hcs.levelOne y))
  set m := modelDeriv κ hφ d y (levelLift κ.χ 1 y) with hm
  have hinj : Function.Injective m := modelDeriv_injective κ hφ d y hy hyσ hz
  have hcv : ∀ v, chartVec hφ (incFrame hcs κ hy v) = m v := fun v =>
    chartVec_incFrame κ hy v hφ d y hyσ
  have hli : ∀ c : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      LinearIndependent ℝ fun i => chartVec hφ (incFrame hcs κ hy (c i)) := fun c => by
    have h := c.linearIndependent.map' (m : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] φ.model.E 0)
      (LinearMap.ker_eq_bot.2 hinj)
    have e : (fun i => chartVec hφ (incFrame hcs κ hy (c i))) =
        (m : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] φ.model.E 0) ∘ c := funext fun i => hcv (c i)
    rw [e]; exact h
  set b₀ : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  by_cases h0 : (fun i => incFrame hcs κ hy (b₀ i)) ∈ F
  · exact ⟨b₀, h0⟩
  set w : Fin n → ℝˣ := Function.update (fun _ => 1) ⟨0, hn⟩ (-1) with hw
  refine ⟨b₀.unitsSMul w, ?_⟩
  have hdet : b₀.det (b₀.unitsSMul w) = -1 := by
    rw [Basis.det_unitsSMul_self]
    have hwi : ∀ i, ((w i : ℝˣ) : ℝ) =
        Function.update (fun _ => (1 : ℝ)) (⟨0, hn⟩ : Fin n) (-1) i := fun i => by
      rw [hw]
      by_cases h : i = ⟨0, hn⟩
      · subst h; simp
      · simp [Function.update_of_ne h]
    simp only [hwi]
    rw [Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  have key : ((fun i => incFrame hcs κ hy (b₀.unitsSMul w i)) ∈ F ↔
      (fun i => incFrame hcs κ hy (b₀ i)) ∈ F) ↔ 0 < b₀.det (b₀.unitsSMul w) := by
    rw [Basis.det_apply]
    refine IsOrientedAt.frames_iff_frames_iff_det_pos hN y.2 hF hφ hyφ
      (fun i => incFrame_mem hN.1 κ hy _) (fun i => incFrame_mem hN.1 κ hy _) (hli b₀)
      (hli (b₀.unitsSMul w)) (b₀.toMatrix (b₀.unitsSMul w)) fun j => ?_
    rw [hcv]
    conv_lhs => rw [← b₀.sum_repr (b₀.unitsSMul w j)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hcv, Basis.toMatrix_apply]
  rw [hdet] at key
  by_contra h1
  exact absurd (key.1 ⟨fun h => (h1 h).elim, fun h => (h0 h).elim⟩) (by norm_num)

/-- **The tangent map of the inclusion, read in corner coordinates and a chart of `X`, depends
continuously on the point**: `y ↦ modelDeriv(y) v` is continuous on the overlap of the corner
coordinates `κ` with the induced chart. -/
theorem continuousOn_modelDeriv_levelLift (hcs : (subPolyfold hY).HasCornerStructureOfDim n)
    (κ : CornerCoords (subPolyfold hY) n) {φ : MChart X} (hφ : P.IsChart φ) (d : P.SubData N)
    (a₀ : N) (v : EuclideanSpace ℝ (Fin n)) :
    ContinuousOn (fun y : N => modelDeriv κ hφ d a₀ (levelLift κ.χ 1 y) v)
      (κ.s ∩ (subChart d hφ a₀).source) := by
  have hfin := κ.isCornerChart.finiteDimensional
  set σ := subChart d hφ a₀ with hσdef
  have hσ : (subPolyfold hY).IsChart σ := subPolyfold_isChart hY d hφ a₀
  set R := overlapRet κ.isCornerChart σ
  have hf : IsScSmooth R.U (κ.χ.transition σ ∘ R) :=
    (MPolyfold.IsChart.compatible (subPolyfold hY) κ.isChart hσ).1.comp_isScSmooth R
      (overlapRet_retract κ.isCornerChart σ)
  have hD := hf.isSc1.isSc1With_scDeriv.continuousOn_deriv
  have hz : ∀ y ∈ κ.s ∩ σ.source, κ.χ.model.E.toBase 1 (levelLift κ.χ 1 y) = κ.χ y :=
    fun y hy => (subPolyfold hY).toBase_levelLift κ.isChart (κ.s_subset hy.1)
      (levelVal_mem (hcs.levelOne y))
  have hl : ContinuousOn (fun y : N => levelLift κ.χ 1 y) (κ.s ∩ σ.source) := by
    have h1 : ContinuousOn (fun y : N => (κ.χ.model.E.scIsoConst 1).symm (κ.χ y))
        (κ.s ∩ σ.source) :=
      (κ.χ.model.E.scIsoConst 1).symm.continuous.comp_continuousOn
        (κ.χ.continuousOn_toFun.mono fun y hy => κ.s_subset hy.1)
    refine h1.congr fun y hy => ?_
    apply κ.χ.model.E.toBase_injective 1
    rw [hz y hy]
    exact ((κ.χ.model.E.scIsoConst 1).apply_symm_apply (κ.χ y)).symm
  exact hD.comp (hl.prodMk (continuousOn_const (c := κ.Ψ.symm (ofLpCLM n v))))
    (fun y hy => R.lvlSet_retract_subset 1
      (mem_lvlSet_overlapRet κ.isCornerChart (κ.s_subset hy.1) hy.2 (hz y hy)))

/-- **A frame field from corner coordinates**: if near `x ∈ N` the frames
`(Tι(b₁), …, Tι(bₙ))` of `T_yN`, read in the corner coordinates `κ`, lie in the sets `F y`, there
are a chart `φ` of `X`, an open `V ∋ x` in its domain and a field `e` of frames with `e z ∈ F z`
on `N ∩ V` whose chart vectors are continuous on `N ∩ V` (the continuity of Definition 9.3.2). -/
theorem exists_continuousOn_frame_of_eventually (hN : P.IsSubmanifoldOfDim N n)
    (F : X → Set (Fin n → P.TangentSpace)) (κ : CornerCoords (subPolyfold hY) n) {x : N}
    (hx : x ∈ κ.s) (b : Fin n → EuclideanSpace ℝ (Fin n))
    (hev : ∀ᶠ y in 𝓝 x, ∃ hy : y ∈ κ.s, (fun i => incFrame hcs κ hy (b i)) ∈ F y.1) :
    ∃ (φ : MChart X) (hφ : P.IsChart φ) (V : Set X), IsOpen V ∧ x.1 ∈ V ∧ V ⊆ φ.source ∧
      ∃ e : X → Fin n → P.TangentSpace, (∀ z ∈ N ∩ V, e z ∈ F z) ∧
        ContinuousOn (fun z j => chartVec hφ (e z j)) (N ∩ V) := by
  classical
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x.1
  set d := (hN.1.data x.2).toSubData
  set σ := subChart d hφ x with hσdef
  have hσ : (subPolyfold hY).IsChart σ := subPolyfold_isChart hY d hφ x
  have hxσ : x ∈ σ.source := d.mem_shrink φ x.2 (hN.1.mem_data_V x.2) hxφ
  obtain ⟨G₀, hG₀sub, hG₀o, hxG₀⟩ := mem_nhds_iff.1
    (hev.and ((κ.isOpen_s.inter σ.isOpen_source).mem_nhds ⟨hx, hxσ⟩))
  obtain ⟨V₀, hV₀o, hV₀⟩ := isOpen_induced_iff.1 hG₀o
  have hmemG : ∀ z (hz : z ∈ N), z ∈ V₀ → (⟨z, hz⟩ : N) ∈ G₀ := fun z hz hzV => by
    rw [← hV₀]; exact hzV
  let m : N → EuclideanSpace ℝ (Fin n) →L[ℝ] φ.model.E 0 := fun y =>
    modelDeriv κ hφ d x (levelLift κ.χ 1 y)
  let e : X → Fin n → P.TangentSpace := fun z =>
    if h : ∃ hz : z ∈ N, (⟨z, hz⟩ : N) ∈ κ.s then fun j => incFrame hcs κ h.choose_spec (b j)
    else fun j => incFrame hcs κ hx (b j)
  have he : ∀ z (hz : z ∈ N) (hzκ : (⟨z, hz⟩ : N) ∈ κ.s),
      e z = fun j => incFrame hcs κ hzκ (b j) := fun z hz hzκ => dif_pos ⟨hz, hzκ⟩
  refine ⟨φ, hφ, V₀ ∩ φ.source, hV₀o.inter φ.isOpen_source, ⟨by rw [← hV₀] at hxG₀; exact hxG₀,
    hxφ⟩, inter_subset_right, e, fun z hz => ?_, ?_⟩
  · obtain ⟨⟨hzκ, hzF⟩, -⟩ := hG₀sub (hmemG z hz.1 hz.2.1)
    rw [he z hz.1 hzκ]
    exact hzF
  have hmc : ContinuousOn (fun y : N => fun j => m y (b j)) G₀ :=
    continuousOn_pi.2 fun j => (continuousOn_modelDeriv_levelLift hcs κ hφ d x (b j)).mono
      fun y hy => (hG₀sub hy).2
  rw [continuousOn_iff_continuous_domRestrict]
  have hres : (N ∩ (V₀ ∩ φ.source)).domRestrict (fun z j => chartVec hφ (e z j)) =
      (fun y : N => fun j => m y (b j)) ∘
        fun z : ↥(N ∩ (V₀ ∩ φ.source)) => (⟨z.1, z.2.1⟩ : N) := funext fun z => by
    have hzG := hmemG z.1 z.2.1 z.2.2.1
    funext j
    change chartVec hφ (e z.1 j) = m ⟨z.1, z.2.1⟩ (b j)
    rw [he z.1 z.2.1 (hG₀sub hzG).2.1]
    exact chartVec_incFrame κ (hG₀sub hzG).2.1 (b j) hφ d x (hG₀sub hzG).2.2
  rw [hres]
  exact hmc.comp_continuous (continuous_subtype_val.subtype_mk _)
    fun z => hmemG z.1 z.2.1 z.2.2.1

end MPolyfold

/-- A ray of `λ(N)` through the wedge of a tuple, for two equal tuples. -/
theorem exists_ray_wedge_congr {E : Type*} [AddCommGroup E] [Module ℝ E] {N : Submodule ℝ E}
    {n : ℕ} (hn : n = finrank ℝ N) {w w' : Fin n → E} (h : w = w')
    (r : Module.Ray ℝ (maxPow N)) :
    (∃ (hmem : ∀ i, w i ∈ N) (hne : wedge (fun i => (⟨w i, hmem i⟩ : N)) hn ≠ 0),
        r = rayOfNeZero ℝ _ hne) ↔
      ∃ (hmem : ∀ i, w' i ∈ N) (hne : wedge (fun i => (⟨w' i, hmem i⟩ : N)) hn ≠ 0),
        r = rayOfNeZero ℝ _ hne := by
  subst h; rfl

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}} {f : A.Obj → A.W} {Λ : A.W → ℚ≥0} {x : A.Obj}

namespace KernelBranching

/-- **The sign of a frame field in corner coordinates is locally constant along a sheet**: for
an orientation `o` of `f` (Definition 6.6.16), a sheet `Mᵢ` of positive dimension, corner
coordinates `κ` of `Mᵢ` and a basis `b` of `ℝⁿ`, if the frame `(Tι(b₁), …, Tι(bₙ))` of
`T_{x₀}Mᵢ` is positive for `o_{i,x₀}`, the frames `(Tι(b₁), …, Tι(bₙ))` of `T_yMᵢ` are positive
for `o_{i,y}` at all `y ∈ Mᵢ` near `x₀`. -/
theorem eventually_incFrame_mem_frames (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hft.toIsScFredholmSection y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hft.toIsScFredholmSection o)
    (K : KernelBranching A f Λ x) (i : K.ι) (hn : 0 < K.dim i) [ParacompactSpace (K.M i)]
    {hY : A.X.PObj.IsSubMPolyfold (K.M i)}
    {hcs : (subPolyfold hY).HasCornerStructureOfDim (K.dim i)}
    (κ : CornerCoords (subPolyfold hY) (K.dim i)) {x₀ : K.M i} (hx₀ : x₀ ∈ κ.s)
    (b : Basis (Fin (K.dim i)) ℝ (EuclideanSpace ℝ (Fin (K.dim i))))
    (hb : (fun j => incFrame hcs κ hx₀ (b j)) ∈
      K.frames hft.toIsScFredholmSection hsec o i x₀.1) :
    ∀ᶠ y in 𝓝 x₀, ∃ hy : y ∈ κ.s,
      (fun j => incFrame hcs κ hy (b j)) ∈ K.frames hft.toIsScFredholmSection hsec o i y.1 := by
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  have := paracompactSpace_rn_rn_prod A.X.PObj
  have := paracompactSpace_rn_rn_pullback A.B
  have hf : A.B.IsScFredholmSection f := hft.toIsScFredholmSection
  have hs₀ := K.smooth i x₀.1 x₀.2
  have hNd := K.isSubmanifoldOfDim i
  -- the global sc⁺-section equal to `sᵢ` near `x₀`
  obtain ⟨ŝ, hŝ, N₁, hN₁, hx₀N₁, hN₁O, heq'⟩ := exists_isScPlusSection_eqOn_nhds hbump
    K.isOpen_O (K.isScPlus i).extendZero (isSection_extendZero K.O (K.s i)) (K.mem_O x₀.2)
  have heq : EqOn ŝ (K.s i) N₁ := fun y hy =>
    (heq' hy).trans (extendZero_eqOn (K.isScPlus i).1 (hN₁O hy)).symm
  have ht := isScPlusSection_minusSection hŝ
  have hgt := theorem_3_1_18_tame hft ht
  have hg := theorem_3_1_18_preprint hf ht
  have ho' := isSectionOrientation_sectionAdd hf ht ho
  obtain ⟨c, hc, U, V, hN⟩ := exists_isOrientableNbhd hX hbump hgt hs₀
  have hVc : ∀ {y : A.Obj}, y ∈ V → y ∈ c.φ.source := fun hy =>
    hN.hasLocalPropagation.subset (hN.subset hy)
  set d := hY.data x₀.2 with hd
  have hxσ₀ : x₀ ∈ (subChart d c.isChart x₀).source :=
    d.mem_shrink c.φ x₀.2 (hY.mem_data_V x₀.2) (hVc hN.mem)
  have hG : IsOpen ((subChart d c.isChart x₀).source ∩ Subtype.val ⁻¹' (V ∩ N₁)) :=
    (subChart _ c.isChart x₀).isOpen_source.inter
      ((hN.isOpen_V.inter hN₁).preimage continuous_subtype_val)
  -- the pointwise description of the frames
  have hpt := fun (w : K.M i) (hwV : w.1 ∈ V) (hwN : w.1 ∈ N₁) =>
    K.mem_frames_iff_tangentOr hf hsec o hŝ hN₁O heq hN₁ w.2 hwN hc (hVc hwV)
  choose hZ hLs hnk hA hiff using hpt
  filter_upwards [eventually_exists_segPath κ hx₀ hG ⟨hxσ₀, hN.mem, hx₀N₁⟩] with y hy
  obtain ⟨hyκ, γ, hγs, hγ0', hγ1', hγG, hγχ⟩ := hy
  refine ⟨hyκ, ?_⟩
  have hγsX : (rnPolyfold 1).IsScSmoothMap A.X.PObj (Subtype.val ∘ γ) :=
    (subPolyfold_inclusion_isScSmooth hY).comp hγs
  have hγV : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, (Subtype.val ∘ γ) q ∈ V := fun q _ => (hγG q).2.2.1
  have hγZ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, IsZeroAt A.P
      (Polyfold.sectionAdd A.P f (minusSection ŝ)) ((Subtype.val ∘ γ) q) := fun q _ =>
    hZ (γ q) (hγG q).2.2.1 (hγG q).2.2.2
  have hγL : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, A.B.IsLinSurjAt
      (Polyfold.sectionAdd A.P f (minusSection ŝ)) ((Subtype.val ∘ γ) q) := fun q _ =>
    hLs (γ q) (hγG q).2.2.1 (hγG q).2.2.2
  -- the frame of the kernels along the path
  let m : K.M i → EuclideanSpace ℝ (Fin (K.dim i)) →L[ℝ] c.φ.model.E 0 := fun w =>
    modelDeriv κ c.isChart d x₀ (levelLift κ.χ 1 w)
  have hcv : ∀ (w : K.M i) (hw : w ∈ κ.s), w ∈ (subChart d c.isChart x₀).source →
      ∀ v, chartVec c.isChart (incFrame hcs κ hw v) = m w v := fun w hw hwσ v =>
    chartVec_incFrame κ hw v c.isChart d x₀ hwσ
  have hmem : ∀ (q : (Fin 1 → ℝ)) (hq : q ∈ Icc (0 : Fin 1 → ℝ) 1) v, m (γ q) v ∈ c.linKer
      (Polyfold.sectionAdd A.P f (minusSection ŝ)) (chartPtOf c hc (hVc (hγV q hq))
        (hg.mem_smoothSet_of_isZeroAt (hγZ q hq))).z := fun q hq v => by
    rw [← SetLike.mem_coe]
    refine (hA (γ q) (hγG q).2.2.1 (hγG q).2.2.2) ▸ ?_
    exact ⟨_, incFrame_mem hNd.1 κ (hγG q).1 v, hcv (γ q) (hγG q).1 (hγG q).2.1 v⟩
  have hli : ∀ q : (Fin 1 → ℝ), LinearIndependent ℝ fun j => m (γ q) (b j) := fun q =>
    b.linearIndependent.map' (m (γ q)).toLinearMap (LinearMap.ker_eq_bot.2
      (modelDeriv_injective κ c.isChart d x₀ (hγG q).1 (hγG q).2.1
        ((subPolyfold hY).toBase_levelLift κ.isChart (κ.s_subset (hγG q).1)
          (levelVal_mem (hcs.levelOne (γ q))))))
  have hγc : Continuous γ := continuousOn_univ.1 hγs.continuousOn
  have hcont : ∀ v, Continuous fun q : Icc (0 : Fin 1 → ℝ) 1 => m (γ q) v := fun v =>
    (continuousOn_modelDeriv_levelLift hcs κ c.isChart d x₀ v).comp_continuous
      (hγc.comp continuous_subtype_val) fun q => ⟨(hγG q).1, (hγG q).2.1⟩
  let Λ₁ : SubspaceFamily (Icc (0 : Fin 1 → ℝ) 1) (c.φ.model.E 0) :=
    { L := fun q => c.linKer (Polyfold.sectionAdd A.P f (minusSection ŝ))
        (chartPtOf c hc (hVc (hγV q q.2)) (hg.mem_smoothSet_of_isZeroAt (hγZ q q.2))).z
      n := K.dim i
      finiteDimensional := fun q => Module.finite_of_finrank_pos
        (lt_of_lt_of_eq hn (hnk (γ q) (hγG q).2.2.1 (hγG q).2.2.2).symm)
      finrank_eq := fun q => hnk (γ q) (hγG q).2.2.1 (hγG q).2.2.2
      exists_frame := fun _ => ⟨univ, isOpen_univ, mem_univ _, fun j q => m (γ q) (b j),
        fun j => (hcont (b j)).continuousOn, fun q _ => ⟨fun j => hmem q q.2 (b j), hli q⟩⟩ }
  have hT := isLineOrientation_tangentOr_of_family_of_isSectionOrientation hg ho' hs₀ hN hγsX
    hγV hγZ hγL Λ₁ (fun q => rfl)
  let ε : (Λ₁.congrL _ (fun q => rfl)).Frame :=
    { U := univ
      isOpen := isOpen_univ
      e := fun j q => m (γ q) (b j)
      continuousOn := fun j => (hcont (b j)).continuousOn
      mem := fun q _ j => hmem q q.2 (b j)
      linearIndependent := fun q _ => hli q }
  have hL := ε.isLineOrientation rfl
  have : PreconnectedSpace (Icc (0 : Fin 1 → ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.1 (convex_Icc 0 1).isPreconnected
  have hiff01 := IsLineOrientation.eq_iff_eq hT hL ⟨1, right_mem_Icc.2 fun _ => zero_le_one⟩
    ⟨0, left_mem_Icc.2 fun _ => zero_le_one⟩
  -- the frames of `o_{i,γ(q)}` and the two orientations of the line bundle
  have hkey : ∀ q : Icc (0 : Fin 1 → ℝ) 1,
      (fun j => incFrame hcs κ (hγG q).1 (b j)) ∈ K.frames hf hsec o i (γ q).1 ↔
        tangentOrAt (Polyfold.sectionAdd A.P f (minusSection ŝ)) hg c hc
            (hN.hasLocalPropagation.subset (hN.subset (hγV q q.2)))
            (hg.mem_smoothSet_of_isZeroAt (hγZ q q.2)) (hγZ q q.2) (hγL q q.2)
            (restrictOr (fun y hy => (chartPtOf (orChart A.B y) (isChart_orChart y)
              (mem_orChart y) hy).orSectionAdd hf ht (o y hy)) hN ((Subtype.val ∘ γ) q)
              (hγV q q.2) (hg.mem_smoothSet_of_isZeroAt (hγZ q q.2))) =
          rayOfNeZero ℝ (ε.wedgeAt q) (ε.wedgeAt_ne_zero (mem_univ q)) := fun q => by
    have hw : (fun j => chartVec c.isChart (incFrame hcs κ (hγG q).1 (b j))) =
        fun j => m (γ q) (b j) := funext fun j => hcv (γ q) (hγG q).1 (hγG q).2.1 (b j)
    have hwe := ε.wedgeAt_of_mem (mem_univ q)
    have hstep := congrArg (tangentOrAt (Polyfold.sectionAdd A.P f (minusSection ŝ)) hg c hc
      (hN.hasLocalPropagation.subset (hN.subset (hγV q q.2)))
      (hg.mem_smoothSet_of_isZeroAt (hγZ q q.2)) (hγZ q q.2) (hγL q q.2))
      (toChartOr_orSectionAdd hf ht (hg.mem_smoothSet_of_isZeroAt (hγZ q q.2))
        (o (γ q).1 (hg.mem_smoothSet_of_isZeroAt (hγZ q q.2))) c hc
        (hN.hasLocalPropagation.subset (hN.subset (hγV q q.2))))
    refine (hiff (γ q) (hγG q).2.2.1 (hγG q).2.2.2 _).trans ?_
    refine (and_iff_right fun j => incFrame_mem hNd.1 κ (hγG q).1 (b j)).trans ?_
    refine (exists_ray_wedge_congr _ hw _).trans ?_
    constructor
    · rintro ⟨_, hne, he⟩
      exact hstep.trans (he.trans (rayOfNeZero_congr hwe.symm _ _))
    · intro he
      exact ⟨fun j => hmem q q.2 (b j), hwe ▸ ε.wedgeAt_ne_zero (mem_univ q),
        hstep.symm.trans (he.trans (rayOfNeZero_congr hwe _ _))⟩
  have htr : ∀ (w w' : K.M i) (_ : w = w') (hw : w ∈ κ.s) (hw' : w' ∈ κ.s),
      ((fun j => incFrame hcs κ hw (b j)) ∈ K.frames hf hsec o i w.1 ↔
        (fun j => incFrame hcs κ hw' (b j)) ∈ K.frames hf hsec o i w'.1) := by
    intro w w' h hw hw'
    subst h
    rfl
  exact (htr _ _ hγ1' (hγG 1).1 hyκ).1 ((hkey ⟨1, right_mem_Icc.2 fun _ => zero_le_one⟩).2
    (hiff01.2 ((hkey ⟨0, left_mem_Icc.2 fun _ => zero_le_one⟩).1
      ((htr _ _ hγ0'.symm hx₀ (hγG 0).1).1 hb))))

/-- **Continuity of `y ↦ o_{i,y}` along the sheets** (Theorem 15.4.1; Definition 9.3.2): for an
orientation `o` of `f` (Definition 6.6.16) on a tame `X` with sc-smooth bump functions, every
local branching structure described by kernels has continuous frames: near every point of a
sheet `Mᵢ` of positive dimension, the frame field `(Tι(b₁), …, Tι(bₙ))` of corner coordinates of
`Mᵢ`, for a basis `b` positive at the point, is positive for `o_{i,y}` and continuous. -/
theorem framesContinuous (hX : A.X.PObj.IsTame) (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hft : A.B.IsScFredholmSectionTame f) (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hft.toIsScFredholmSection y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hft.toIsScFredholmSection o)
    (K : KernelBranching A f Λ x) : K.FramesContinuous hft.toIsScFredholmSection hsec o := by
  intro i hn y hy
  let _ := A.X.PObj.paracompactSpace_subtype (K.M i)
  have hNd := K.isSubmanifoldOfDim i
  have hcs := hNd.hasCornerStructureOfDim_of_hasTameInducedStructure
    (K.hasTameInducedStructure i)
  obtain ⟨κ, hκ⟩ := hcs.exists_cornerCoords ⟨y, hy⟩
  obtain ⟨b, hb⟩ := exists_basis_incFrame_mem_of_isOrientedAt (hcs := hcs) hn hNd
    (K.isOrientedAt hft.toIsScFredholmSection hsec o hy) κ hκ
  exact exists_continuousOn_frame_of_eventually (hcs := hcs) hNd
    (K.frames hft.toIsScFredholmSection hsec o i) κ hκ b
    (K.eventually_incFrame_mem_frames hX hbump hft hsec o ho i hn κ hκ b hb)

end KernelBranching

/-! ### Theorem 15.4.1 -/

/-- **Theorem 15.4.1 (2021 p. 702; 2017: Theorem 15.6), continuity of the canonical lift**: let
`X` be tame with sc-smooth bump functions, `f` an sc-Fredholm section with tame germ data and
`o` an orientation of `f` (Definition 6.6.16: `y ↦ o_y ∈ Or_y^f` is a continuous orientation over
every orientable neighbourhood).  Then for every local branching structure of `Θ = Λ ∘ f`
described by kernels, `y ↦ o_{i,y}` is continuous along the sheets `Mᵢ` (`CanonContinuous`).
Boundary points are included. -/
theorem canonContinuous (Λ : A.W → ℚ≥0) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hft.toIsScFredholmSection y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hft.toIsScFredholmSection o) :
    CanonContinuous Λ hft.toIsScFredholmSection hsec o :=
  fun _ K => K.framesContinuous hX hbump hft hsec o ho

/-- **Theorem 15.4.1 (2021 p. 702; 2017: Theorem 15.6) in `Ĝr(X)`, for an oriented sc-Fredholm
section functor**: let `X` be tame with sc-smooth bump functions, `f` an sc-Fredholm section
functor with tame germ data, `o` an orientation of `f` (Definition 6.6.16) invariant under the
morphisms (Definition 12.5.4), and `Λ` an sc⁺-multisection such that `(f, Λ)` is in good position
(Definition 15.2.4) and `f` has index `n` at every point of `supp(Λ ∘ f)`.  Then, with the
independence of Theorem 9.2.1 (`hTS`), `canonicalOrientation` is an orientation of `Θ = Λ ∘ f`
(Definition 9.3.2), and it is the canonical one (`IsCanonicalFor`): naturality is
`canonNatural`, continuity is `canonContinuous`, the dimension is
`exists_kernelBranching_dim`. -/
theorem theorem_15_4_1_of_isSectionOrientation (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hF : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hΛ : IsScPlusMultisection A Λ)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hinv : A.E.IsOrInvariant hF hsec o)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hF.2 o) {n : ℕ}
    (hgp : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), IsGoodPositionAt f Λ x)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x n)
    (hTS : A.X.HasIndependentTangentSums (fun z => (Λ (f z) : ℚ))) :
    IsCanonicalFor Λ hF.2 hsec o n (canonicalOrientation Λ hF.2 hsec o) :=
  theorem_15_4_1_of_natural_continuous hF hft hΛ
    (fun x hx => exists_kernelBranching_dim hF hft hsec (hgp x hx) (hidx x hx)) hTS
    (canonNatural Λ hF hΛ hsec o hinv) (canonContinuous Λ hX hbump hft hsec o ho)

end SBLocalization

end Polyfold
