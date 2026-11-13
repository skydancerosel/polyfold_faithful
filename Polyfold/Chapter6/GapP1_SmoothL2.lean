import Polyfold.Chapter6.SubspaceBundle
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, the bundle `L` of
Lemma 6.6.5 (p. 265; preprint Lemma 6.30, p. 222), gap G.62: smooth families of subspaces and the
smooth vector bundles they define.

# Smooth families of finite-dimensional subspaces

## What is formalized

* `Polyfold.SmoothSubspaceFamily IB B W`: over a manifold `B` (model `IB`), a family
  `b ↦ L b` of `n`-dimensional subspaces of a normed space `W`, spanned near every point by a
  `C^∞` frame (`ContMDiffOn IB 𝓘(ℝ, W) ∞`).  `toSubspaceFamily`: the underlying continuous
  family (`SubspaceFamily`, `Chapter6/SubspaceBundle.lean`).
* **`SmoothSubspaceFamily.prebundle`, `contMDiffVectorBundle`**: the subspaces `L b` themselves
  are the fibres of a Mathlib `C^∞` vector bundle with model fibre `ℝⁿ`
  (`FiberBundle`, `VectorBundle`, `ContMDiffVectorBundle ∞ (Fin n → ℝ) (fun b => L b) IB`).  The
  trivializations are the frames (`Frame.pretriv`, coordinates in the basis of the frame), and
  the coordinate changes are `C^∞` (`Frame.contMDiffOn_change`): near `b₀` the change from `e` to
  `e'` is `N(b)⁻¹ M(b)`, where `M(b)`, `N(b)` are the matrices `ξₗ(eₖ(b))`, `ξₗ(e'ₖ(b))` for
  continuous functionals `ξ` dual to `e'(b₀)` (Hahn–Banach), and inversion is `C^∞` at units.
* **`SmoothSubspaceFamily.infKer`** (the text's `L_t = T S ∩ {dt = 0}`, Lemma 6.6.5): cutting
  a smooth family by the kernel of a fixed `ℓ : W → ℝᵐ` that maps every `L b` onto `ℝᵐ` gives a
  smooth family.  Near `b₀` the frame of the kernel is `κⱼ − R (A(b) R)⁻¹ A(b) κⱼ` in the
  coordinates of a frame, for the matrices `A(b) = ℓ ∘ e(b)`, a basis `κ` of `ker A(b₀)` and a
  right inverse `R` of `A(b₀)` (`exists_smooth_kerFrame`).
-/

open Module Bundle Topology Set Filter
open scoped Manifold ContDiff

noncomputable section

namespace Polyfold

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] (IB : ModelWithCorners ℝ EB HB) (B : Type*) [TopologicalSpace B]
  [ChartedSpace HB B] (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **A smooth family of `n`-dimensional subspaces** `L b ⊆ W` over a manifold `B`: near every
point it is spanned by a `C^∞` frame. -/
structure SmoothSubspaceFamily where
  /-- The subspaces. -/
  L : B → Submodule ℝ W
  /-- Their dimension. -/
  n : ℕ
  finiteDimensional : ∀ b, FiniteDimensional ℝ (L b)
  finrank_eq : ∀ b, finrank ℝ (L b) = n
  exists_frame : ∀ b₀, ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧ ∃ e : Fin n → B → W,
    (∀ i, ContMDiffOn IB 𝓘(ℝ, W) ∞ (e i) U) ∧
      ∀ b ∈ U, (∀ i, e i b ∈ L b) ∧ LinearIndependent ℝ fun i => e i b

namespace SmoothSubspaceFamily

variable {IB B W} (Λ : SmoothSubspaceFamily IB B W)

instance (b : B) : FiniteDimensional ℝ (Λ.L b) := Λ.finiteDimensional b

/-- The underlying continuous family. -/
def toSubspaceFamily : SubspaceFamily B W where
  L := Λ.L
  n := Λ.n
  finiteDimensional := Λ.finiteDimensional
  finrank_eq := Λ.finrank_eq
  exists_frame b₀ := by
    obtain ⟨U, hU, hb₀, e, he, h⟩ := Λ.exists_frame b₀
    exact ⟨U, hU, hb₀, e, fun i => (he i).continuousOn, h⟩

/-- The fibre `L b`, as a type. -/
abbrev Fiber (b : B) : Type _ := Λ.L b

/-- A smooth local frame of the family. -/
structure Frame where
  /-- The domain. -/
  U : Set B
  isOpen : IsOpen U
  /-- The frame vectors. -/
  e : Fin Λ.n → B → W
  contMDiffOn : ∀ i, ContMDiffOn IB 𝓘(ℝ, W) ∞ (e i) U
  mem : ∀ b ∈ U, ∀ i, e i b ∈ Λ.L b
  linearIndependent : ∀ b ∈ U, LinearIndependent ℝ fun i => e i b

namespace Frame

variable {Λ} (ε : Λ.Frame)

/-- The frame at `b ∈ U`, as vectors of `L b`. -/
def vec {b : B} (hb : b ∈ ε.U) : Fin Λ.n → Λ.L b := fun i => ⟨ε.e i b, ε.mem b hb i⟩

theorem linearIndependent_vec {b : B} (hb : b ∈ ε.U) : LinearIndependent ℝ (ε.vec hb) :=
  LinearIndependent.of_comp (Λ.L b).subtype (ε.linearIndependent b hb)

/-- The basis of `L b`, `b ∈ U`, given by the frame. -/
def basis {b : B} (hb : b ∈ ε.U) : Basis (Fin Λ.n) ℝ (Λ.L b) :=
  basisOfLinearIndependentOfCardEqFinrank' (ε.vec hb) (ε.linearIndependent_vec hb)
    (by rw [Fintype.card_fin, Λ.finrank_eq b])

theorem coe_basis {b : B} (hb : b ∈ ε.U) : ⇑(ε.basis hb) = ε.vec hb :=
  coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _

open scoped Classical in
/-- The coordinates in the frame (`0` off `U`). -/
def coordL (b : B) : Λ.L b →ₗ[ℝ] (Fin Λ.n → ℝ) :=
  if hb : b ∈ ε.U then (ε.basis hb).equivFun.toLinearMap else 0

open scoped Classical in
/-- The vector with given coordinates in the frame (`0` off `U`). -/
def ofCoordL (b : B) : (Fin Λ.n → ℝ) →ₗ[ℝ] Λ.L b :=
  if hb : b ∈ ε.U then (ε.basis hb).equivFun.symm.toLinearMap else 0

theorem coordL_of_mem {b : B} (hb : b ∈ ε.U) (v : Λ.L b) :
    ε.coordL b v = (ε.basis hb).equivFun v := by
  rw [coordL, dif_pos hb]; rfl

theorem ofCoordL_of_mem {b : B} (hb : b ∈ ε.U) (c : Fin Λ.n → ℝ) :
    ε.ofCoordL b c = (ε.basis hb).equivFun.symm c := by
  rw [ofCoordL, dif_pos hb]; rfl

theorem coordL_ofCoordL {b : B} (hb : b ∈ ε.U) (c : Fin Λ.n → ℝ) :
    ε.coordL b (ε.ofCoordL b c) = c := by
  rw [ε.coordL_of_mem hb, ε.ofCoordL_of_mem hb, LinearEquiv.apply_symm_apply]

theorem ofCoordL_coordL {b : B} (hb : b ∈ ε.U) (v : Λ.L b) :
    ε.ofCoordL b (ε.coordL b v) = v := by
  rw [ε.coordL_of_mem hb, ε.ofCoordL_of_mem hb, LinearEquiv.symm_apply_apply]

/-- In `W`, the vector with coordinates `c` is `∑ cᵢ eᵢ(b)`. -/
theorem coe_ofCoordL {b : B} (hb : b ∈ ε.U) (c : Fin Λ.n → ℝ) :
    (ε.ofCoordL b c : W) = ∑ i, c i • ε.e i b := by
  rw [ε.ofCoordL_of_mem hb, Basis.equivFun_symm_apply, ε.coe_basis hb]
  simp [vec]

/-- **The trivialization of `L` by a frame**: `(b, v) ↦ (b, coordinates of v)` over `U`. -/
def pretriv : Pretrivialization (Fin Λ.n → ℝ) (π (Fin Λ.n → ℝ) Λ.Fiber) where
  toFun x := (x.1, ε.coordL x.1 x.2)
  invFun p := ⟨p.1, ε.ofCoordL p.1 p.2⟩
  source := TotalSpace.proj ⁻¹' ε.U
  target := ε.U ×ˢ univ
  map_source' _ hx := ⟨hx, mem_univ _⟩
  map_target' _ hp := hp.1
  left_inv' x hx := by
    obtain ⟨b, v⟩ := x
    exact congrArg (TotalSpace.mk b) (ε.ofCoordL_coordL hx v)
  right_inv' p hp := Prod.ext rfl (ε.coordL_ofCoordL hp.1 p.2)
  open_target := ε.isOpen.prod isOpen_univ
  baseSet := ε.U
  open_baseSet := ε.isOpen
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- The frame as a continuous linear map `ℝⁿ → W`, `c ↦ ∑ cᵢ eᵢ(b)`. -/
def frameCLM (b : B) : (Fin Λ.n → ℝ) →L[ℝ] W :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin Λ.n → ℝ) →L[ℝ] ℝ).smulRight (ε.e i b)

theorem frameCLM_apply (b : B) (c : Fin Λ.n → ℝ) : ε.frameCLM b c = ∑ i, c i • ε.e i b := by
  simp [frameCLM]

theorem contMDiffOn_frameCLM :
    ContMDiffOn IB 𝓘(ℝ, (Fin Λ.n → ℝ) →L[ℝ] W) ∞ ε.frameCLM ε.U := by
  have h : ∀ i, ContMDiffOn IB 𝓘(ℝ, (Fin Λ.n → ℝ) →L[ℝ] W) ∞
      (fun b => (ContinuousLinearMap.proj i : (Fin Λ.n → ℝ) →L[ℝ] ℝ).smulRight (ε.e i b)) ε.U :=
    fun i => (ContinuousLinearMap.smulRightL ℝ (Fin Λ.n → ℝ) W
      (ContinuousLinearMap.proj i)).contMDiff.comp_contMDiffOn (ε.contMDiffOn i)
  have := contMDiffOn_finsetSum (t := Finset.univ) (fun i _ => h i)
  refine this.congr fun b _ => ?_
  simp [frameCLM]

/-- Continuous functionals dual, at one point, to a frame: `ξᵢ(eⱼ(b₀)) = δᵢⱼ` (Hahn–Banach). -/
theorem exists_dual_functionals {b₀ : B} (hb₀ : b₀ ∈ ε.U) :
    ∃ ξ : Fin Λ.n → W →L[ℝ] ℝ, ∀ i j, ξ i (ε.e j b₀) = if j = i then 1 else 0 := by
  have h : ∀ i, ∃ g : W →L[ℝ] ℝ, ∀ x : Λ.L b₀, g x = (ε.basis hb₀).coord i x := fun i => by
    obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (Λ.L b₀)
      (LinearMap.toContinuousLinearMap ((ε.basis hb₀).coord i))
    exact ⟨g, fun x => by rw [hg x, LinearMap.coe_toContinuousLinearMap']⟩
  choose ξ hξ using h
  refine ⟨ξ, fun i j => ?_⟩
  have h2 : (ε.basis hb₀).coord i (ε.vec hb₀ j) = if j = i then 1 else 0 := by
    rw [← ε.coe_basis hb₀, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  exact (hξ i (ε.vec hb₀ j)).trans h2

/-- The change of frame `ε → ε'` at `b`, as a continuous linear map of `ℝⁿ`. -/
def change (ε' : Λ.Frame) (b : B) : (Fin Λ.n → ℝ) →L[ℝ] (Fin Λ.n → ℝ) :=
  LinearMap.toContinuousLinearMap ((ε'.coordL b).comp (ε.ofCoordL b))

theorem change_apply (ε' : Λ.Frame) (b : B) (c : Fin Λ.n → ℝ) :
    ε.change ε' b c = ε'.coordL b (ε.ofCoordL b c) := by
  simp [change]

/-- `ξ(∑ cₖ e'ₖ(b)) = N(b) c`, so `N(b) ∘ change = M(b)`. -/
theorem comp_change (ε' : Λ.Frame) (Ξ : W →L[ℝ] (Fin Λ.n → ℝ)) {b : B} (hb : b ∈ ε.U)
    (hb' : b ∈ ε'.U) : (Ξ.comp (ε'.frameCLM b)).comp (ε.change ε' b) = Ξ.comp (ε.frameCLM b) := by
  ext1 c
  simp only [ContinuousLinearMap.comp_apply]
  rw [ε.change_apply, frameCLM_apply, ← ε'.coe_ofCoordL hb', ε'.ofCoordL_coordL hb',
    ε.coe_ofCoordL hb, frameCLM_apply]

/-- **The coordinate changes are `C^∞`**: on `U ∩ U'` the change of frame is `C^∞` into
`L(ℝⁿ, ℝⁿ)`; near `b₀` it is `N(b)⁻¹ M(b)` for functionals dual to `e'(b₀)`. -/
theorem contMDiffOn_change (ε' : Λ.Frame) :
    ContMDiffOn IB 𝓘(ℝ, (Fin Λ.n → ℝ) →L[ℝ] (Fin Λ.n → ℝ)) ∞ (ε.change ε') (ε.U ∩ ε'.U) := by
  intro b₀ hb₀
  obtain ⟨ξ, hξ⟩ := ε'.exists_dual_functionals hb₀.2
  set Ξ : W →L[ℝ] (Fin Λ.n → ℝ) := ContinuousLinearMap.pi ξ with hΞ
  set N : B → (Fin Λ.n → ℝ) →L[ℝ] (Fin Λ.n → ℝ) := fun b => Ξ.comp (ε'.frameCLM b) with hN
  set M : B → (Fin Λ.n → ℝ) →L[ℝ] (Fin Λ.n → ℝ) := fun b => Ξ.comp (ε.frameCLM b) with hM
  have hN₀ : N b₀ = 1 := by
    ext1 c
    funext l
    simp only [hN, ContinuousLinearMap.comp_apply, frameCLM_apply, hΞ,
      ContinuousLinearMap.pi_apply, map_sum, map_smul, hξ, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, one_apply_eq_self]
  have hNs : ContMDiffAt IB 𝓘(ℝ, (Fin Λ.n → ℝ) →L[ℝ] (Fin Λ.n → ℝ)) ∞ N b₀ :=
    contMDiffAt_const.clm_comp ((ε'.contMDiffOn_frameCLM).contMDiffAt
      (ε'.isOpen.mem_nhds hb₀.2))
  have hMs : ContMDiffAt IB 𝓘(ℝ, (Fin Λ.n → ℝ) →L[ℝ] (Fin Λ.n → ℝ)) ∞ M b₀ :=
    contMDiffAt_const.clm_comp ((ε.contMDiffOn_frameCLM).contMDiffAt (ε.isOpen.mem_nhds hb₀.1))
  have hinv : ContMDiffAt IB 𝓘(ℝ, (Fin Λ.n → ℝ) →L[ℝ] (Fin Λ.n → ℝ)) ∞
      (fun b => Ring.inverse (N b)) b₀ := by
    have h1 : ContDiffAt ℝ ∞ Ring.inverse (N b₀) := by
      rw [hN₀]
      exact contDiffAt_ringInverse ℝ (1 : ((Fin Λ.n → ℝ) →L[ℝ] (Fin Λ.n → ℝ))ˣ)
    exact h1.comp_contMDiffAt hNs
  have hunit : ∀ᶠ b in 𝓝 b₀, IsUnit (N b) := by
    exact hNs.continuousAt.preimage_mem_nhds
      (Units.isOpen.mem_nhds (by rw [hN₀]; exact isUnit_one))
  have hev : ∀ᶠ b in 𝓝 b₀, (Ring.inverse (N b)).comp (M b) = ε.change ε' b := by
    filter_upwards [hunit, ε.isOpen.mem_nhds hb₀.1, ε'.isOpen.mem_nhds hb₀.2] with b hu hb hb'
    have h := ε.comp_change ε' Ξ hb hb'
    have h' : M b = N b * ε.change ε' b := h.symm
    change Ring.inverse (N b) * M b = ε.change ε' b
    rw [h']
    exact Ring.inverse_mul_cancel_left _ _ hu
  have hsm := (hinv.clm_comp hMs).congr_of_eventuallyEq (hev.mono fun b hb => hb.symm)
  exact hsm.contMDiffWithinAt

end Frame

/-- A frame around `b`. -/
theorem exists_frame_mem (b : B) : ∃ ε : Λ.Frame, b ∈ ε.U := by
  obtain ⟨U, hU, hb, e, he, h⟩ := Λ.exists_frame b
  exact ⟨⟨U, hU, e, he, fun b hb => (h b hb).1, fun b hb => (h b hb).2⟩, hb⟩

/-- The chosen frame around `b`. -/
def frameAt (b : B) : Λ.Frame := (Λ.exists_frame_mem b).choose

theorem mem_frameAt (b : B) : b ∈ (Λ.frameAt b).U := (Λ.exists_frame_mem b).choose_spec

/-- **`L` as a vector prebundle**: the atlas of all frame trivializations. -/
def prebundle : VectorPrebundle ℝ (Fin Λ.n → ℝ) Λ.Fiber where
  pretrivializationAtlas := range fun ε : Λ.Frame => ε.pretriv
  pretrivialization_linear' := by
    rintro _ ⟨ε, rfl⟩
    exact ⟨fun b _ => (ε.coordL b).isLinear⟩
  pretrivializationAt b := (Λ.frameAt b).pretriv
  mem_base_pretrivializationAt b := Λ.mem_frameAt b
  pretrivialization_mem_atlas b := ⟨_, rfl⟩
  exists_coordChange := by
    rintro _ ⟨ε, rfl⟩ _ ⟨ε', rfl⟩
    refine ⟨ε.change ε', (ε.contMDiffOn_change ε').continuousOn, fun b hb v => ?_⟩
    rw [ε.pretriv.mk_symm hb.1 v]
    exact ε.change_apply ε' b v
  totalSpaceMk_isInducing b := by
    have hb := Λ.mem_frameAt b
    set ε := Λ.frameAt b
    have hemb : IsInducing (ε.coordL b) := by
      have he : ⇑(ε.coordL b) = ⇑((ε.basis hb).equivFun.toContinuousLinearEquiv) := by
        funext v; rw [ε.coordL_of_mem hb]; rfl
      rw [he]
      exact (ε.basis hb).equivFun.toContinuousLinearEquiv.toHomeomorph.isInducing
    exact Topology.isInducing_const_prod.2 hemb

/-- **The coordinate changes of the prebundle are `C^∞`.** -/
instance isContMDiff : Λ.prebundle.IsContMDiff IB ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨ε, rfl⟩ _ ⟨ε', rfl⟩
    refine ⟨ε.change ε', ε.contMDiffOn_change ε', fun b hb v => ?_⟩
    rw [ε.pretriv.mk_symm hb.1 v]
    exact ε.change_apply ε' b v

instance : TopologicalSpace (TotalSpace (Fin Λ.n → ℝ) Λ.Fiber) := Λ.prebundle.totalSpaceTopology

instance : FiberBundle (Fin Λ.n → ℝ) Λ.Fiber := Λ.prebundle.toFiberBundle

instance : VectorBundle ℝ (Fin Λ.n → ℝ) Λ.Fiber := Λ.prebundle.toVectorBundle

/-- **A smooth family of subspaces is a `C^∞` vector bundle** (Mathlib's
`ContMDiffVectorBundle`), with fibres the subspaces `L b` and model fibre `ℝⁿ`. -/
instance contMDiffVectorBundle : ContMDiffVectorBundle ∞ (Fin Λ.n → ℝ) Λ.Fiber IB :=
  Λ.prebundle.contMDiffVectorBundle IB

/-! ### Cutting by the kernel of a fixed map onto `ℝᵐ` -/

/-- **A smooth frame of the kernels of a smooth family of surjections** `A b : ℝᵈ → ℝᵐ`: near a
point `b₀` where `A b₀` is onto, `κⱼ(b) = κⱼ − R (A(b) R)⁻¹ A(b) κⱼ` for a basis `κ` of
`ker A(b₀)` and a right inverse `R` of `A(b₀)`. -/
theorem exists_smooth_kerFrame {d m : ℕ}
    {A : B → (Fin d → ℝ) →L[ℝ] (Fin m → ℝ)} {U : Set B} (hU : IsOpen U)
    (hA : ContMDiffOn IB 𝓘(ℝ, (Fin d → ℝ) →L[ℝ] (Fin m → ℝ)) ∞ A U) {b₀ : B} (hb₀ : b₀ ∈ U)
    (hs : Function.Surjective (A b₀)) :
    ∃ U' : Set B, U' ⊆ U ∧ IsOpen U' ∧ b₀ ∈ U' ∧ ∃ κ : Fin (d - m) → B → (Fin d → ℝ),
      (∀ j, ContMDiffOn IB 𝓘(ℝ, Fin d → ℝ) ∞ (κ j) U') ∧
        ∀ b ∈ U', (∀ j, A b (κ j b) = 0) ∧ LinearIndependent ℝ fun j => κ j b := by
  obtain ⟨R, hR⟩ := (A b₀).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hs)
  have hk : finrank ℝ (LinearMap.ker (A b₀ : (Fin d → ℝ) →ₗ[ℝ] Fin m → ℝ)) = d - m := by
    have h := LinearMap.finrank_range_add_finrank_ker (A b₀ : (Fin d → ℝ) →ₗ[ℝ] Fin m → ℝ)
    rw [LinearMap.range_eq_top.2 hs, finrank_top, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at h
    omega
  let κ₀ : Basis (Fin (d - m)) ℝ (LinearMap.ker (A b₀ : (Fin d → ℝ) →ₗ[ℝ] Fin m → ℝ)) :=
    Module.finBasisOfFinrankEq ℝ _ hk
  set P : B → (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) := fun b => (A b).comp R with hP
  have hP₀ : P b₀ = 1 := hR
  have hPs : ContMDiffOn IB 𝓘(ℝ, (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) ∞ P U :=
    hA.clm_comp contMDiffOn_const
  set U'' := U ∩ P ⁻¹' {x | IsUnit x} with hU''
  have hU''o : IsOpen U'' := hPs.continuousOn.isOpen_inter_preimage hU Units.isOpen
  have hb₀'' : b₀ ∈ U'' := ⟨hb₀, by rw [mem_preimage, hP₀]; exact isUnit_one⟩
  let κ : Fin (d - m) → B → (Fin d → ℝ) := fun j b =>
    (κ₀ j : Fin d → ℝ) - (R.comp ((Ring.inverse (P b)).comp (A b))) (κ₀ j)
  have hκdef : ∀ j b, κ j b =
      (κ₀ j : Fin d → ℝ) - R (Ring.inverse (P b) (A b (κ₀ j))) := fun _ _ => rfl
  have hinv : ContMDiffOn IB 𝓘(ℝ, (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) ∞
      (fun b => Ring.inverse (P b)) U'' := by
    intro b hb
    have h1 : ContDiffAt ℝ ∞ Ring.inverse (P b) := by
      have := contDiffAt_ringInverse ℝ (n := ∞) hb.2.unit
      rwa [IsUnit.unit_spec] at this
    exact (h1.comp_contMDiffAt ((hPs.mono inter_subset_left).contMDiffAt
      (hU''o.mem_nhds hb))).contMDiffWithinAt
  have hκs : ∀ j, ContMDiffOn IB 𝓘(ℝ, Fin d → ℝ) ∞ (κ j) U'' := fun j => by
    have h1 : ContMDiffOn IB 𝓘(ℝ, Fin d → ℝ) ∞
        (fun b => (R.comp ((Ring.inverse (P b)).comp (A b))) (κ₀ j)) U'' :=
      (contMDiffOn_const.clm_comp (hinv.clm_comp (hA.mono inter_subset_left))).clm_apply
        contMDiffOn_const
    have h2 : ContDiff ℝ ∞ fun v : Fin d → ℝ => (κ₀ j : Fin d → ℝ) - v :=
      contDiff_const.sub contDiff_id
    exact h2.contMDiff.comp_contMDiffOn h1
  have hκA : ∀ b ∈ U'', ∀ j, A b (κ j b) = 0 := by
    intro b hb j
    have h1 : A b (R (Ring.inverse (P b) (A b (κ₀ j)))) =
        (P b * Ring.inverse (P b)) (A b (κ₀ j)) := rfl
    rw [hκdef, map_sub, h1, Ring.mul_inverse_cancel _ hb.2, one_apply_eq_self, sub_self]
  have hκ₀ : (fun j => κ j b₀) = fun j => (κ₀ j : Fin d → ℝ) := by
    funext j
    have h0 : A b₀ (κ₀ j) = 0 := (κ₀ j).2
    rw [hκdef, h0, map_zero, map_zero, sub_zero]
  have hli₀' : LinearIndependent ℝ
      ((LinearMap.ker (A b₀ : (Fin d → ℝ) →ₗ[ℝ] Fin m → ℝ)).subtype ∘ κ₀) :=
    κ₀.linearIndependent.map' _ (Submodule.ker_subtype _)
  have hli₀ : LinearIndependent ℝ fun j => κ j b₀ := by
    rw [hκ₀]; exact hli₀'
  have hev : ∀ᶠ b in 𝓝 b₀, LinearIndependent ℝ fun j => κ j b := by
    have hca : ContinuousAt (fun b j => κ j b) b₀ := continuousAt_pi.2 fun j =>
      ((hκs j).contMDiffAt (hU''o.mem_nhds hb₀'')).continuousAt
    exact hca.tendsto.eventually hli₀.eventually
  obtain ⟨U₁, hU₁, hU₁o, hb₀U₁⟩ := eventually_nhds_iff.1 hev
  exact ⟨U'' ∩ U₁, inter_subset_left.trans inter_subset_left, hU''o.inter hU₁o, ⟨hb₀'', hb₀U₁⟩,
    κ, fun j => (hκs j).mono inter_subset_left, fun b hb => ⟨hκA b hb.1, hU₁ b hb.2⟩⟩

/-- **Cutting a smooth family by the kernel of a fixed map onto `ℝᵐ`**, onto on every member: the
text's `L_t = T S ∩ {dt = 0}` (Lemma 6.6.5). -/
def infKer {m : ℕ} (ℓ : W →L[ℝ] (Fin m → ℝ))
    (hℓ : ∀ b, (Λ.L b).map (ℓ : W →ₗ[ℝ] Fin m → ℝ) = ⊤) : SmoothSubspaceFamily IB B W where
  L b := Λ.L b ⊓ LinearMap.ker (ℓ : W →ₗ[ℝ] Fin m → ℝ)
  n := Λ.n - m
  finiteDimensional b := inferInstance
  finrank_eq b := by
    have h := LinearMap.finrank_range_add_finrank_ker
      ((ℓ : W →ₗ[ℝ] Fin m → ℝ).domRestrict (Λ.L b))
    rw [LinearMap.range_domRestrict, hℓ b, finrank_top, Module.finrank_fin_fun,
      LinearMap.ker_domRestrict, Λ.finrank_eq b] at h
    rw [← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
    omega
  exists_frame b₀ := by
    set ε := Λ.frameAt b₀
    have hb₀ := Λ.mem_frameAt b₀
    set A : B → (Fin Λ.n → ℝ) →L[ℝ] (Fin m → ℝ) := fun b => ℓ.comp (ε.frameCLM b) with hAdef
    have hA : ContMDiffOn IB 𝓘(ℝ, (Fin Λ.n → ℝ) →L[ℝ] (Fin m → ℝ)) ∞ A ε.U :=
      contMDiffOn_const.clm_comp ε.contMDiffOn_frameCLM
    have hs : Function.Surjective (A b₀) := by
      intro y
      have hy : y ∈ (Λ.L b₀).map (ℓ : W →ₗ[ℝ] Fin m → ℝ) := (hℓ b₀).symm ▸ Submodule.mem_top
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨ε.coordL b₀ ⟨x, hx⟩, ?_⟩
      change ℓ (ε.frameCLM b₀ _) = ℓ x
      rw [ε.frameCLM_apply, ← ε.coe_ofCoordL hb₀, ε.ofCoordL_coordL hb₀]
    obtain ⟨U', hU'U, hU'o, hb₀', κ, hκ, hκA⟩ := exists_smooth_kerFrame ε.isOpen hA hb₀ hs
    refine ⟨U', hU'o, hb₀', fun j b => ε.frameCLM b (κ j b), fun j =>
      (ε.contMDiffOn_frameCLM.mono hU'U).clm_apply (hκ j), fun b hb => ⟨fun j => ⟨?_, ?_⟩, ?_⟩⟩
    · change ε.frameCLM b (κ j b) ∈ Λ.L b
      rw [ε.frameCLM_apply]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ε.mem b (hU'U hb) i)
    · exact (hκA b hb).1 j
    · have hinj : LinearMap.ker (ε.frameCLM b : (Fin Λ.n → ℝ) →ₗ[ℝ] W) = ⊥ :=
        LinearMap.ker_eq_bot'.2 fun c hc => funext (Fintype.linearIndependent_iff.1
          (ε.linearIndependent b (hU'U hb)) c (by rw [← ε.frameCLM_apply]; exact hc))
      exact (hκA b hb).2.map' _ hinj

theorem infKer_L {m : ℕ} (ℓ : W →L[ℝ] (Fin m → ℝ))
    (hℓ : ∀ b, (Λ.L b).map (ℓ : W →ₗ[ℝ] Fin m → ℝ) = ⊤) (b : B) :
    (Λ.infKer ℓ hℓ).L b = Λ.L b ⊓ LinearMap.ker (ℓ : W →ₗ[ℝ] Fin m → ℝ) := rfl

end SmoothSubspaceFamily

end Polyfold
