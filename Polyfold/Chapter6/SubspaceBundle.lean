import Polyfold.Chapter6.LineBundleOrientation
import Polyfold.Chapter6.DetLine
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 222–227: the bundle `L = ⋃_t {t} × L_t` of kernels along a path, its line bundle
`λ(L) = ⋃_t {t} × λ(L_t)`, and "an orientation of the lines `λ(L_t)` determines by continuation an
orientation of all the other lines" (before (96)); the two-parameter bundles `L̃` of Lemmas 6.33,
6.34 and of the proof of Theorem 6.35 *(book 2017: §6.4; see `BookConcordance.md`)*.

# Continuous families of finite-dimensional subspaces and their determinant lines

## The text, paraphrased

Along a path, the kernels `L_t = ker F_t'(φ(t), 0)` form a vector bundle `L` over `[0, 1]`, and
`λ(L) = ⋃ {t} × λ(L_t)` is a line bundle; an orientation of `λ(L_0)` determines by continuation an
orientation of `λ(L_1)`.  Over `[0, 1] × [0, 1]` the same holds for the bundles `L̃`.

## What is formalized

* `Polyfold.SubspaceFamily B W`: a family `b ↦ L b` of `n`-dimensional subspaces of a normed space
  `W` over a topological space `B`, spanned near every point by a continuous frame.
* `SubspaceFamily.det Λ b = λ(L b)`, with the line-bundle structure (`FiberBundle`,
  `VectorBundle`, model fibre `ℝ`) whose trivializations are the frames: the pretrivialization of a
  frame `e` is `x ↦ (b, (e₁(b) ∧ … ∧ eₙ(b))*(x))` (`Frame.pretriv`); the coordinate changes are
  continuous and nowhere zero (`Frame.coordChange_continuousOn`).
* `SubspaceFamily.comp`: the restriction of a family along a continuous map, and
  `LineOrientation.comp`: orientations restrict.
* `SubspaceFamily.transport`: over `[0, 1]` (`unitInterval`), the continuation `λ(L_0) → λ(L_1)` of
  orientations; `transport_eq`: it is the value at `1` of any orientation through the given ray at
  `0`; `transport_injective`; and `transport_comp`: over a simply connected, locally
  path-connected base, the continuation along a path depends only on its end points (this is
  what the two-parameter families of Lemmas 6.33–6.34 and Theorem 6.35 are used for).

## Reading

"Vector bundle" is read as a family of subspaces of one normed space `W` with continuous local
frames; in Lemmas 6.30–6.34 `W` is the model space `E₀ × ℝᵏ` (or `ℝ² × E₀ × ℝᵏ`) of one
chart.  The continuation is by the orientations of `LineBundleOrientation.lean` over `[0, 1]` or
`[0, 1]²`, which are convex.
-/

open Module Bundle Topology Set

noncomputable section

namespace Polyfold

variable {B : Type*} [TopologicalSpace B] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

variable (B W) in
/-- **A continuous family of `n`-dimensional subspaces** `L b ⊆ W` over `B`: near every point it
is spanned by a continuous frame. -/
structure SubspaceFamily where
  /-- The subspaces. -/
  L : B → Submodule ℝ W
  /-- Their dimension. -/
  n : ℕ
  finiteDimensional : ∀ b, FiniteDimensional ℝ (L b)
  finrank_eq : ∀ b, finrank ℝ (L b) = n
  exists_frame : ∀ b₀, ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧ ∃ e : Fin n → B → W,
    (∀ i, ContinuousOn (e i) U) ∧ ∀ b ∈ U, (∀ i, e i b ∈ L b) ∧ LinearIndependent ℝ fun i => e i b

namespace SubspaceFamily

variable (Λ : SubspaceFamily B W)

instance (b : B) : FiniteDimensional ℝ (Λ.L b) := Λ.finiteDimensional b

/-- The line `λ(L b)`. -/
def det (b : B) : Type _ := maxPow (Λ.L b)

instance (b : B) : AddCommMonoid (Λ.det b) := inferInstanceAs (AddCommMonoid (maxPow (Λ.L b)))

instance (b : B) : Module ℝ (Λ.det b) := inferInstanceAs (Module ℝ (maxPow (Λ.L b)))

/-- `λ(L b)` carries the topology of a finite-dimensional real vector space. -/
instance (b : B) : TopologicalSpace (Λ.det b) := moduleTopology ℝ _

instance (b : B) : IsModuleTopology ℝ (Λ.det b) := ⟨rfl⟩

theorem finrank_det (b : B) : finrank ℝ (Λ.det b) = 1 := finrank_maxPow

/-- A local frame of the family: an open set `U` and a continuous frame `e` of `L` over `U`. -/
structure Frame where
  /-- The domain. -/
  U : Set B
  isOpen : IsOpen U
  /-- The frame vectors. -/
  e : Fin Λ.n → B → W
  continuousOn : ∀ i, ContinuousOn (e i) U
  mem : ∀ b ∈ U, ∀ i, e i b ∈ Λ.L b
  linearIndependent : ∀ b ∈ U, LinearIndependent ℝ fun i => e i b

namespace Frame

variable {Λ} (ε : Λ.Frame)

/-- The frame at `b ∈ U`, as vectors of `L b`. -/
def vec {b : B} (hb : b ∈ ε.U) : Fin Λ.n → Λ.L b := fun i => ⟨ε.e i b, ε.mem b hb i⟩

open scoped Classical in
/-- The wedge `e₁(b) ∧ … ∧ eₙ(b) ∈ λ(L b)` (and `0` off `U`). -/
def wedgeAt (b : B) : Λ.det b :=
  if hb : b ∈ ε.U then wedge (ε.vec hb) (Λ.finrank_eq b).symm else 0

/-- The frame at `b ∈ U` is linearly independent in `L b`. -/
theorem linearIndependent_vec {b : B} (hb : b ∈ ε.U) : LinearIndependent ℝ (ε.vec hb) :=
  LinearIndependent.of_comp (Λ.L b).subtype (ε.linearIndependent b hb)

/-- On `U`, `wedgeAt` is the wedge of the frame. -/
theorem wedgeAt_of_mem {b : B} (hb : b ∈ ε.U) :
    ε.wedgeAt b = wedge (ε.vec hb) (Λ.finrank_eq b).symm :=
  dif_pos hb

theorem wedgeAt_ne_zero {b : B} (hb : b ∈ ε.U) : ε.wedgeAt b ≠ 0 := by
  rw [ε.wedgeAt_of_mem hb]
  exact (wedge_ne_zero_iff _).2 (ε.linearIndependent_vec hb)

/-- The coordinate `λ(L b) → ℝ` of the frame: `x ↦ (e₁(b) ∧ … ∧ eₙ(b))*(x)`. -/
def coord (b : B) : Λ.det b →ₗ[ℝ] ℝ :=
  (dualVec (ε.wedgeAt b : maxPow (Λ.L b)) : Module.Dual ℝ (maxPow (Λ.L b)))

/-- `(e₁ ∧ … ∧ eₙ)*(e₁ ∧ … ∧ eₙ) = 1` on `U`. -/
theorem coord_wedgeAt {b : B} (hb : b ∈ ε.U) : ε.coord b (ε.wedgeAt b) = 1 :=
  dualVec_self (L := maxPow (Λ.L b)) finrank_maxPow (ε.wedgeAt_ne_zero hb)

/-- On `U`, every `x ∈ λ(L b)` is `(e₁ ∧ … ∧ eₙ)*(x) · e₁ ∧ … ∧ eₙ`. -/
theorem coord_smul_wedgeAt {b : B} (hb : b ∈ ε.U) (x : Λ.det b) :
    ε.coord b x • ε.wedgeAt b = x :=
  dualVec_apply_smul (L := maxPow (Λ.L b)) finrank_maxPow (ε.wedgeAt_ne_zero hb) x

/-- Change of frame: `ε'*(x) = ε*(x) · ε'*(e₁ ∧ … ∧ eₙ)` on `U`. -/
theorem coord_eq_mul (ε' : Λ.Frame) {b : B} (hb : b ∈ ε.U) (x : Λ.det b) :
    ε'.coord b x = ε.coord b x * ε'.coord b (ε.wedgeAt b) := by
  conv_lhs => rw [← ε.coord_smul_wedgeAt hb x]
  rw [map_smul, smul_eq_mul]

/-- On `U`, the coordinate of a nonzero vector is nonzero. -/
theorem coord_ne_zero {b : B} (hb : b ∈ ε.U) {x : Λ.det b} (hx : x ≠ 0) : ε.coord b x ≠ 0 := by
  intro h
  apply hx
  rw [← ε.coord_smul_wedgeAt hb x, h, zero_smul]

/-- **The trivialization of `λ(L)` by a frame**: `(b, x) ↦ (b, (e₁(b) ∧ … ∧ eₙ(b))*(x))` over
`U`. -/
def pretriv : Pretrivialization ℝ (π ℝ Λ.det) where
  toFun x := (x.1, ε.coord x.1 x.2)
  invFun p := ⟨p.1, p.2 • ε.wedgeAt p.1⟩
  source := TotalSpace.proj ⁻¹' ε.U
  target := ε.U ×ˢ univ
  map_source' _ hx := ⟨hx, mem_univ _⟩
  map_target' _ hp := hp.1
  left_inv' x hx := by
    obtain ⟨b, v⟩ := x
    exact congrArg (TotalSpace.mk b) (ε.coord_smul_wedgeAt hx v)
  right_inv' p hp := by
    refine Prod.ext rfl ?_
    change ε.coord p.1 (p.2 • ε.wedgeAt p.1) = p.2
    rw [map_smul, ε.coord_wedgeAt hp.1, smul_eq_mul, mul_one]
  open_target := ε.isOpen.prod isOpen_univ
  baseSet := ε.U
  open_baseSet := ε.isOpen
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- The basis of `L b`, `b ∈ U`, given by a frame. -/
def basis {b : B} (hb : b ∈ ε.U) : Basis (Fin Λ.n) ℝ (Λ.L b) :=
  basisOfLinearIndependentOfCardEqFinrank' (ε.vec hb) (ε.linearIndependent_vec hb)
    (by rw [Fintype.card_fin, Λ.finrank_eq b])

/-- The vectors of `ε.basis hb` are those of the frame. -/
theorem coe_basis {b : B} (hb : b ∈ ε.U) : ⇑(ε.basis hb) = ε.vec hb :=
  coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _

/-- The coordinate change is the determinant of the change of frame:
`ε'*(e₁ ∧ … ∧ eₙ) = det_{e'}(e)`. -/
theorem coord_wedgeAt_eq_det (ε' : Λ.Frame) {b : B} (hb : b ∈ ε.U) (hb' : b ∈ ε'.U) :
    ε'.coord b (ε.wedgeAt b) = (ε'.basis hb').det (ε.vec hb) := by
  have h : ε.wedgeAt b = (ε'.basis hb').det (ε.vec hb) • ε'.wedgeAt b := by
    rw [ε.wedgeAt_of_mem hb, ε'.wedgeAt_of_mem hb', wedge_eq_det_smul' (ε'.basis hb'),
      ε'.coe_basis hb']
    rfl
  rw [h, map_smul, ε'.coord_wedgeAt hb', smul_eq_mul, mul_one]

/-- Under a linear map `f : M → ℝⁿ`, the determinant `det(f(vⱼ)ᵢ)` changes by `det_β(v)`. -/
theorem _root_.Polyfold.det_linearMap_eq_mul {M : Type*} [AddCommGroup M] [Module ℝ M] {n : ℕ}
    (f : M →ₗ[ℝ] Fin n → ℝ) (β : Basis (Fin n) ℝ M) (v : Fin n → M) :
    Matrix.det (Matrix.of fun j i => f (v j) i) =
      Matrix.det (Matrix.of fun j i => f (β j) i) * β.det v := by
  have h := congrArg (fun A : M [⋀^Fin n]→ₗ[ℝ] ℝ => A v)
    (AlternatingMap.eq_smul_basis_det β (Matrix.detRowAlternating.compLinearMap f))
  simp only [AlternatingMap.smul_apply, smul_eq_mul] at h
  exact h

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

/-- The coordinate change is continuous at every point of `U ∩ U'`: near `b₀` it is the quotient
`det(ξᵢ(eⱼ(b))) / det(ξᵢ(e'ⱼ(b)))` for functionals `ξ` dual to `e'(b₀)`. -/
theorem coordChange_continuousAt (ε' : Λ.Frame) {b₀ : B} (hb₀ : b₀ ∈ ε.U ∩ ε'.U) :
    ContinuousAt (fun b => ε'.coord b (ε.wedgeAt b)) b₀ := by
  obtain ⟨ξ, hξ⟩ := ε'.exists_dual_functionals hb₀.2
  let F : W →ₗ[ℝ] Fin Λ.n → ℝ := LinearMap.pi fun i => (ξ i : W →ₗ[ℝ] ℝ)
  let G : Λ.Frame → B → ℝ := fun ε₁ b => Matrix.det (Matrix.of fun j i => ξ i (ε₁.e j b))
  have hG : ∀ ε₁ : Λ.Frame, b₀ ∈ ε₁.U → ContinuousAt (G ε₁) b₀ := fun ε₁ h₁ =>
    (continuous_id.matrix_det).continuousAt.comp (continuousAt_pi.2 fun j => continuousAt_pi.2
      fun i => (ξ i).continuous.continuousAt.comp
        ((ε₁.continuousOn j).continuousAt (ε₁.isOpen.mem_nhds h₁)))
  have hG₀ : G ε' b₀ ≠ 0 := by
    have : (Matrix.of fun j i => ξ i (ε'.e j b₀)) = 1 := by
      ext j i
      rw [Matrix.of_apply, hξ, Matrix.one_apply]
    simp only [G, this, Matrix.det_one]
    exact one_ne_zero
  have hrel : ∀ b (hb : b ∈ ε.U) (hb' : b ∈ ε'.U),
      G ε b = G ε' b * ε'.coord b (ε.wedgeAt b) := by
    intro b hb hb'
    rw [ε.coord_wedgeAt_eq_det ε' hb hb']
    have := det_linearMap_eq_mul (F ∘ₗ (Λ.L b).subtype) (ε'.basis hb') (ε.vec hb)
    rw [ε'.coe_basis hb'] at this
    exact this
  refine ((hG ε hb₀.1).div (hG ε' hb₀.2) hG₀).congr ?_
  filter_upwards [ε.isOpen.mem_nhds hb₀.1, ε'.isOpen.mem_nhds hb₀.2,
    (hG ε' hb₀.2).eventually_ne hG₀] with b hb hb' hg
  rw [Pi.div_apply, hrel b hb hb', mul_div_cancel_left₀ _ hg]

/-- **The coordinate changes are continuous and nowhere zero**: for two frames, `b ↦ ε'*(ε(b))`
(the determinant of the change of frame) is continuous and nowhere zero on `U ∩ U'`. -/
theorem coordChange_continuousOn (ε' : Λ.Frame) :
    ContinuousOn (fun b => ε'.coord b (ε.wedgeAt b)) (ε.U ∩ ε'.U) ∧
      ∀ b ∈ ε.U ∩ ε'.U, ε'.coord b (ε.wedgeAt b) ≠ 0 :=
  ⟨fun _ hb => (ε.coordChange_continuousAt ε' hb).continuousWithinAt,
    fun _ hb => ε'.coord_ne_zero hb.2 (ε.wedgeAt_ne_zero hb.1)⟩

end Frame

/-- A frame around `b`. -/
theorem exists_frame_mem (b : B) : ∃ ε : Λ.Frame, b ∈ ε.U := by
  obtain ⟨U, hU, hb, e, he, h⟩ := Λ.exists_frame b
  exact ⟨⟨U, hU, e, he, fun b hb => (h b hb).1, fun b hb => (h b hb).2⟩, hb⟩

/-- The chosen frame around `b`. -/
def frameAt (b : B) : Λ.Frame := (Λ.exists_frame_mem b).choose

theorem mem_frameAt (b : B) : b ∈ (Λ.frameAt b).U := (Λ.exists_frame_mem b).choose_spec

/-- **`λ(L)` as a vector prebundle**: the atlas of all frame trivializations. -/
def prebundle : VectorPrebundle ℝ ℝ Λ.det where
  pretrivializationAtlas := range fun ε : Λ.Frame => ε.pretriv
  pretrivialization_linear' := by
    rintro _ ⟨ε, rfl⟩
    exact ⟨fun b _ => (ε.coord b).isLinear⟩
  pretrivializationAt b := (Λ.frameAt b).pretriv
  mem_base_pretrivializationAt b := Λ.mem_frameAt b
  pretrivialization_mem_atlas b := ⟨_, rfl⟩
  exists_coordChange := by
    rintro _ ⟨ε, rfl⟩ _ ⟨ε', rfl⟩
    refine ⟨fun b => ε'.coord b (ε.wedgeAt b) • ContinuousLinearMap.id ℝ ℝ,
      (ε.coordChange_continuousOn ε').1.smul continuousOn_const, fun b hb v => ?_⟩
    rw [ε.pretriv.mk_symm hb.1 v]
    change ε'.coord b (ε.wedgeAt b) * v = ε'.coord b (v • ε.wedgeAt b)
    rw [map_smul, smul_eq_mul, mul_comm]
  totalSpaceMk_isInducing b := by
    have hb := Λ.mem_frameAt b
    have := IsModuleTopology.toContinuousAdd ℝ (Λ.det b)
    have hemb : IsEmbedding ((Λ.frameAt b).coord b) :=
      Function.LeftInverse.isEmbedding (f := fun t : ℝ => t • (Λ.frameAt b).wedgeAt b)
        (fun x => (Λ.frameAt b).coord_smul_wedgeAt hb x) (continuous_id.smul continuous_const)
        (IsModuleTopology.continuous_of_linearMap _)
    exact Topology.isInducing_const_prod.2 hemb.isInducing

instance : TopologicalSpace (TotalSpace ℝ Λ.det) := Λ.prebundle.totalSpaceTopology

instance : FiberBundle ℝ Λ.det := Λ.prebundle.toFiberBundle

instance : VectorBundle ℝ ℝ Λ.det := Λ.prebundle.toVectorBundle

/-- **Continuity of sections in frames**: a section `σ` of `λ(L)` is continuous within `s` at a
point `b₀` of the domain of a frame `ε` iff its coordinate `b ↦ ε*(σ b)` is. -/
theorem continuousWithinAt_section_iff {σ : ∀ b, Λ.det b} {s : Set B} {b₀ : B} (ε : Λ.Frame)
    (hb₀ : b₀ ∈ ε.U) :
    ContinuousWithinAt (fun b => TotalSpace.mk' ℝ b (σ b)) s b₀ ↔
      ContinuousWithinAt (fun b => ε.coord b (σ b)) s b₀ := by
  have key : ∀ ε₁ ε₂ : Λ.Frame, b₀ ∈ ε₁.U → b₀ ∈ ε₂.U →
      ContinuousWithinAt (fun b => ε₁.coord b (σ b)) s b₀ →
        ContinuousWithinAt (fun b => ε₂.coord b (σ b)) s b₀ := by
    intro ε₁ ε₂ h₁ h₂ hc
    have hcc : ContinuousAt (fun b => ε₂.coord b (ε₁.wedgeAt b)) b₀ :=
      ε₁.coordChange_continuousAt ε₂ ⟨h₁, h₂⟩
    refine (hc.mul hcc.continuousWithinAt).congr_of_eventuallyEq ?_
      (ε₁.coord_eq_mul ε₂ h₁ (σ b₀))
    exact eventually_nhdsWithin_of_eventually_nhds
      (Filter.eventually_of_mem (ε₁.isOpen.mem_nhds h₁) fun b hb => ε₁.coord_eq_mul ε₂ hb (σ b))
  rw [FiberBundle.continuousWithinAt_section]
  exact ⟨key _ _ (Λ.mem_frameAt b₀) hb₀, key _ _ hb₀ (Λ.mem_frameAt b₀)⟩

/-- **A frame gives a continuous section**: `b ↦ e₁(b) ∧ … ∧ eₙ(b)` is continuous on `U`. -/
theorem Frame.continuousOn_wedgeAt (ε : Λ.Frame) :
    ContinuousOn (fun b => TotalSpace.mk' ℝ b (ε.wedgeAt b)) ε.U := fun b₀ hb₀ =>
  (Λ.continuousWithinAt_section_iff ε hb₀).2
    ((continuousOn_const (c := (1 : ℝ))).congr (fun _ hb => ε.coord_wedgeAt hb) b₀ hb₀)

/-- The restriction of the family along a continuous map `g : B' → B`. -/
def comp {B' : Type*} [TopologicalSpace B'] (g : C(B', B)) : SubspaceFamily B' W where
  L b := Λ.L (g b)
  n := Λ.n
  finiteDimensional b := Λ.finiteDimensional (g b)
  finrank_eq b := Λ.finrank_eq (g b)
  exists_frame b₀ := by
    obtain ⟨U, hU, hb₀, e, he, h⟩ := Λ.exists_frame (g b₀)
    exact ⟨g ⁻¹' U, hU.preimage g.continuous, hb₀, fun i b => e i (g b),
      fun i => (he i).comp g.continuous.continuousOn (mapsTo_preimage g U),
      fun b hb => h (g b) hb⟩

variable {Λ} in
/-- The pull-back of a frame along `g`. -/
def Frame.comp {B' : Type*} [TopologicalSpace B'] (ε : Λ.Frame) (g : C(B', B)) :
    (Λ.comp g).Frame where
  U := g ⁻¹' ε.U
  isOpen := ε.isOpen.preimage g.continuous
  e i b := ε.e i (g b)
  continuousOn i := (ε.continuousOn i).comp g.continuous.continuousOn (mapsTo_preimage g ε.U)
  mem b hb i := ε.mem (g b) hb i
  linearIndependent b hb := ε.linearIndependent (g b) hb

variable {Λ} in
/-- The coordinate of a pulled-back frame at `b` is that of the frame at `g b`. -/
theorem Frame.coord_comp {B' : Type*} [TopologicalSpace B'] (ε : Λ.Frame) (g : C(B', B))
    (b : B') (x : (Λ.comp g).det b) : (ε.comp g).coord b x = ε.coord (g b) x :=
  rfl

/-- **Orientations restrict** along continuous maps (the fibres of `Λ.comp g` are those of `Λ`). -/
def _root_.Polyfold.LineOrientation.comp {Λ : SubspaceFamily B W} (o : LineOrientation Λ.det)
    {B' : Type*} [TopologicalSpace B'] (g : C(B', B)) : LineOrientation (Λ.comp g).det :=
  ⟨fun b => o (g b), fun b₀ => by
    obtain ⟨U, hU, σ, hσ, hσo⟩ := o.2 (g b₀)
    refine ⟨g ⁻¹' U, g.continuous.continuousAt.preimage_mem_nhds hU, fun b => σ (g b), ?_,
      fun b hb => hσo (g b) hb⟩
    intro b hb
    have hb' := Λ.mem_frameAt (g b)
    refine ((Λ.comp g).continuousWithinAt_section_iff ((Λ.frameAt (g b)).comp g) hb').2 ?_
    exact ((Λ.continuousWithinAt_section_iff (Λ.frameAt (g b)) hb').1 (hσ (g b) hb)).comp
      g.continuous.continuousWithinAt (mapsTo_preimage g U)⟩

@[simp] theorem _root_.Polyfold.LineOrientation.comp_apply {Λ : SubspaceFamily B W}
    (o : LineOrientation Λ.det) {B' : Type*} [TopologicalSpace B'] (g : C(B', B)) (b : B') :
    o.comp g b = o (g b) := rfl

/-! ### Continuation over `[0, 1]` -/

open unitInterval

/-- **The continuation of orientations along `[0, 1]`**: the value at `1` of the orientation of
`λ(L)` through the ray `r` of `λ(L_0)`. -/
def transport (Λ : SubspaceFamily I W) (r : Module.Ray ℝ (Λ.det 0)) : Module.Ray ℝ (Λ.det 1) :=
  haveI := (convex_Icc (0 : ℝ) 1).contractibleSpace (nonempty_Icc.2 zero_le_one)
  haveI := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  (exists_lineOrientation_apply_eq (L := Λ.det) 0 r).choose 1

/-- The continuation is the value at `1` of **any** orientation through `r` at `0`. -/
theorem transport_eq (Λ : SubspaceFamily I W) (o : LineOrientation Λ.det) :
    Λ.transport (o 0) = o 1 := by
  have := (convex_Icc (0 : ℝ) 1).contractibleSpace (nonempty_Icc.2 zero_le_one)
  have := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  have h := LineOrientation.eq_of_apply_eq 0
    (exists_lineOrientation_apply_eq (L := Λ.det) 0 (o 0)).choose_spec
  exact congrArg (fun o : LineOrientation Λ.det => o 1) h

/-- The continuation is injective (so a bijection between the two orientations of `λ(L_0)` and
those of `λ(L_1)`). -/
theorem transport_injective (Λ : SubspaceFamily I W) : Function.Injective Λ.transport := by
  have := (convex_Icc (0 : ℝ) 1).contractibleSpace (nonempty_Icc.2 zero_le_one)
  have := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  intro r r' h
  obtain ⟨o, rfl⟩ := exists_lineOrientation_apply_eq (L := Λ.det) 0 r
  obtain ⟨o', rfl⟩ := exists_lineOrientation_apply_eq (L := Λ.det) 0 r'
  rw [transport_eq, transport_eq] at h
  rw [LineOrientation.eq_of_apply_eq 1 h]

/-- **The continuation along a path is the value of a global orientation**: for an orientation `o`
of `λ(L)` over `B` (one exists through every ray when `B` is simply connected and locally
path-connected, `exists_lineOrientation_apply_eq`), continuing `o(γ(0))` along `γ` gives
`o(γ(1))`. -/
theorem transport_comp (o : LineOrientation Λ.det) (γ : C(I, B)) :
    (Λ.comp γ).transport (o (γ 0)) = o (γ 1) :=
  (Λ.comp γ).transport_eq (o.comp γ)

end SubspaceFamily

end Polyfold
