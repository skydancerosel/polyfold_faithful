import Polyfold.Chapter6.SubspaceBundle
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.5, **Lemma 6.5.3**
(p. 260; preprint Lemma 6.19, p. 216).  Gap G.59, row V6.22.

# Determinant line bundles of vector bundles

## The text, paraphrased

(Lemma 6.5.3) For finite-dimensional topological vector bundles `E`, `F` over `X`, the bundles
`λ(E)`, `λ*(F)`, `E ⊕ F` and `E ⊗ F` have, in a natural way, the structure of topological vector
bundles (a standard lemma; the proof is left to the reader).

## What is formalized

`E` is a Mathlib topological vector bundle (`FiberBundle`, `VectorBundle`) with a
finite-dimensional normed model fibre `F₀`, over a topological space `B` (as in the text).

* `DetBundle.Lam F₀ E`, the fibres `λ(E_b) = Λ^max E_b` (`maxPow`), and
  `DetBundle.LamDual F₀ E`, the fibres `λ*(E_b) = λ(E_b)*` (`maxPowDual`), with **the structure of
  topological line bundles** (`FiberBundle`, `VectorBundle`, model fibre `ℝ`) from the vector
  prebundles `lamPrebundle`, `lamDualPrebundle`.
* "In a natural way": the trivializations are those **induced by the trivializations of `E`**: a
  trivialization `e` of the atlas of `E` gives the frame `b ↦ e⁻¹(b)(f₁), …, e⁻¹(b)(fₙ)` (`f` a
  fixed basis of `F₀`), whose wedge `wedgeAt e` is a continuous nowhere-zero section of `λ(E)` over
  the base set of `e` (`continuousOn_wedgeAt`, `wedgeAt_ne_zero`), and the trivialization
  `x ↦ (e₁ ∧ … ∧ eₙ)*(x)` (`lamPretriv`).  The coordinate changes are the determinants of
  those of `E` (`coord_wedgeAt_eq_det`).  For `λ*(E)`: `ξ ↦ ξ(e₁ ∧ … ∧ eₙ)` (`lamDualPretriv`),
  with the inverse determinants.
* `lemma_6_5_3` collects the four statements.
* `lemma_6_5_3_prod`: `E ⊕ F` is Mathlib's fibrewise product `E ×ᵇ F` with its
  `VectorBundle` instance (`Bundle.Prod.vectorBundle`).
* `DetBundle.Ten F₀ F₁ E E₁`, the fibres `E_b ⊗ F_b`, with the structure of a topological vector
  bundle (`tenPrebundle`, model fibre `F₁ⁿ ≅ F₀ ⊗ F₁`, `n = dim F₀`), again with the
  trivializations induced by pairs of trivializations `e`, `e₁` of `E`, `F`:
  `u ⊗ w ↦ (i ↦ (e u)ᵢ • e₁ w)` (`tenMap`, inverse `tenInv`), and the coordinate changes are the
  matrices of `A ⊗ C` for the coordinate changes `A`, `C` of `E`, `F` (`tenMap_tenInv_eq`).

## Reading

The text gives no construction.  We read "in a natural way" as: the trivializations of the new
bundles are induced by those of `E` and `F`, so that local frames of `E`, `F` give local frames
of `λ(E)`, `λ*(E)`, `E ⊗ F`.  The fibres carry their module topology (the unique Hausdorff
vector-space topology of a finite-dimensional space).  The model fibre of `E ⊗ F` is `F₁ⁿ`
rather than `F₀ ⊗ F₁`, which has no norm in Mathlib.
-/

open Module Bundle Topology Set
open scoped TensorProduct

noncomputable section

namespace Polyfold

namespace DetBundle

variable {B : Type*} [TopologicalSpace B]

/-- `λ(E_b) = Λ^max E_b`, the top exterior power of the fibre (`F₀` is the model fibre, which
fixes the bundle structure). -/
def Lam (_F₀ : Type*) (E : B → Type*) [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)] (b : B) :
    Type _ :=
  maxPow (E b)

/-- `λ*(E_b) = λ(E_b)*`. -/
def LamDual (_F₀ : Type*) (E : B → Type*) [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    (b : B) : Type _ :=
  maxPowDual (E b)

/-- `E_b ⊗ F_b`, the fibrewise tensor product (`F₀`, `F₁` are the model fibres). -/
def Ten (_F₀ _F₁ : Type*) (E E₁ : B → Type*) [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [∀ b, AddCommGroup (E₁ b)] [∀ b, Module ℝ (E₁ b)] (b : B) : Type _ :=
  E b ⊗[ℝ] E₁ b

section Fibres

variable {F₀ : Type*} {E : B → Type*} [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)] (b : B)

instance : AddCommGroup (Lam F₀ E b) := inferInstanceAs (AddCommGroup (maxPow (E b)))
instance : Module ℝ (Lam F₀ E b) := inferInstanceAs (Module ℝ (maxPow (E b)))
instance : TopologicalSpace (Lam F₀ E b) := moduleTopology ℝ _
instance : IsModuleTopology ℝ (Lam F₀ E b) := ⟨rfl⟩

instance : AddCommGroup (LamDual F₀ E b) := inferInstanceAs (AddCommGroup (maxPowDual (E b)))
instance : Module ℝ (LamDual F₀ E b) := inferInstanceAs (Module ℝ (maxPowDual (E b)))
instance : TopologicalSpace (LamDual F₀ E b) := moduleTopology ℝ _
instance : IsModuleTopology ℝ (LamDual F₀ E b) := ⟨rfl⟩

variable {F₁ : Type*} {E₁ : B → Type*} [∀ b, AddCommGroup (E₁ b)] [∀ b, Module ℝ (E₁ b)]

instance : AddCommGroup (Ten F₀ F₁ E E₁ b) := inferInstanceAs (AddCommGroup (E b ⊗[ℝ] E₁ b))
instance : Module ℝ (Ten F₀ F₁ E E₁ b) := inferInstanceAs (Module ℝ (E b ⊗[ℝ] E₁ b))
instance : TopologicalSpace (Ten F₀ F₁ E E₁ b) := moduleTopology ℝ _
instance : IsModuleTopology ℝ (Ten F₀ F₁ E E₁ b) := ⟨rfl⟩

end Fibres

variable {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [FiniteDimensional ℝ F₀]
  {E : B → Type*} [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [TopologicalSpace (TotalSpace F₀ E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F₀ E] [VectorBundle ℝ F₀ E]

variable (F₀ E) in
/-- The fibre `E_b` is linearly equivalent to the model fibre. -/
def fiberEquiv (b : B) : E b ≃ₗ[ℝ] F₀ :=
  (trivializationAt F₀ E b).linearEquivAt ℝ b (FiberBundle.mem_baseSet_trivializationAt F₀ E b)

omit [FiniteDimensional ℝ F₀] in
variable (F₀) in
theorem finrank_fiber (b : B) : finrank ℝ (E b) = finrank ℝ F₀ :=
  (fiberEquiv F₀ E b).finrank_eq

theorem finrank_lam (b : B) : finrank ℝ (Lam F₀ E b) = 1 :=
  haveI := (fiberEquiv F₀ E b).symm.finiteDimensional
  finrank_maxPow

theorem finrank_lamDual (b : B) : finrank ℝ (LamDual F₀ E b) = 1 :=
  haveI := (fiberEquiv F₀ E b).symm.finiteDimensional
  finrank_maxPowDual

/-! ### The frame of a trivialization and its wedge -/

section Frame

variable (e : Trivialization F₀ (π F₀ E)) [MemTrivializationAtlas e]

/-- The frame `e⁻¹(b)(f₁), …, e⁻¹(b)(fₙ)` of `E_b`, `f` the basis `Module.finBasis` of `F₀`. -/
def frame (b : B) : Fin (finrank ℝ F₀) → E b := fun i => e.symm b (Module.finBasis ℝ F₀ i)

/-- On the base set of `e` the frame is a basis of `E_b`. -/
def basisAt {b : B} (hb : b ∈ e.baseSet) : Basis (Fin (finrank ℝ F₀)) ℝ (E b) :=
  (Module.finBasis ℝ F₀).map (e.linearEquivAt ℝ b hb).symm

theorem coe_basisAt {b : B} (hb : b ∈ e.baseSet) : ⇑(basisAt e hb) = frame e b := by
  funext i
  simp [basisAt, frame]

/-- The wedge `e₁(b) ∧ … ∧ eₙ(b) ∈ λ(E_b)` of the frame. -/
def wedgeAt (b : B) : Lam F₀ E b := wedge (frame e b) (finrank_fiber F₀ b).symm

theorem wedgeAt_ne_zero {b : B} (hb : b ∈ e.baseSet) : wedgeAt e b ≠ 0 := by
  have := (fiberEquiv F₀ E b).symm.finiteDimensional
  have := wedge_basis_ne_zero' (basisAt e hb) (finrank_fiber F₀ b).symm
  rwa [coe_basisAt] at this

/-- The coordinate `λ(E_b) → ℝ` of the frame: `x ↦ (e₁ ∧ … ∧ eₙ)*(x)`. -/
def coord (b : B) : Lam F₀ E b →ₗ[ℝ] ℝ := (dualVec (wedgeAt e b : maxPow (E b)) :
  Module.Dual ℝ (maxPow (E b)))

theorem coord_wedgeAt {b : B} (hb : b ∈ e.baseSet) : coord e b (wedgeAt e b) = 1 :=
  dualVec_self (L := maxPow (E b)) (finrank_lam b) (wedgeAt_ne_zero e hb)

theorem coord_smul_wedgeAt {b : B} (hb : b ∈ e.baseSet) (x : Lam F₀ E b) :
    coord e b x • wedgeAt e b = x :=
  dualVec_apply_smul (L := maxPow (E b)) (finrank_lam b) (wedgeAt_ne_zero e hb) x

variable (e' : Trivialization F₀ (π F₀ E)) [MemTrivializationAtlas e']

/-- **The change of frame is the determinant of the coordinate change of `E`**:
`e₁ ∧ … ∧ eₙ = det(e' ∘ e⁻¹)(b) · e'₁ ∧ … ∧ e'ₙ` on the common base set. -/
theorem wedgeAt_eq_det_smul {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    wedgeAt e b = (Trivialization.coordChangeL ℝ e e' b : F₀ →L[ℝ] F₀).det • wedgeAt e' b := by
  have h1 := wedge_eq_det_smul' (basisAt e' hb.2) (frame e b) (finrank_fiber F₀ b).symm
  rw [coe_basisAt] at h1
  refine h1.trans (congrArg (· • wedgeAt e' b) ?_)
  rw [basisAt, Basis.det_map, LinearEquiv.symm_symm]
  have hcomp : (⇑(e'.linearEquivAt ℝ b hb.2) ∘ frame e b) =
      ((Trivialization.coordChangeL ℝ e e' b : F₀ →L[ℝ] F₀) : F₀ →ₗ[ℝ] F₀) ∘
        Module.finBasis ℝ F₀ := by
    funext j
    simp [frame, Trivialization.coordChangeL_apply e e' hb]
  rw [hcomp, Basis.det_comp, Basis.det_self, mul_one]

/-- The coordinate change of `λ(E)`: `e'*(e₁ ∧ … ∧ eₙ) = det(e' ∘ e⁻¹)(b)`. -/
theorem coord_wedgeAt_eq_det {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    coord e' b (wedgeAt e b) = (Trivialization.coordChangeL ℝ e e' b : F₀ →L[ℝ] F₀).det := by
  rw [wedgeAt_eq_det_smul e e' hb, map_smul, coord_wedgeAt e' hb.2, smul_eq_mul, mul_one]

omit [FiniteDimensional ℝ F₀] in
/-- The coordinate changes `b ↦ det(e' ∘ e⁻¹)(b)` are continuous on the common base set. -/
theorem continuousOn_det_coordChange :
    ContinuousOn (fun b => (Trivialization.coordChangeL ℝ e e' b : F₀ →L[ℝ] F₀).det)
      (e.baseSet ∩ e'.baseSet) :=
  (ContinuousLinearMap.continuous_det (𝕜 := ℝ) (E := F₀)).comp_continuousOn
    (continuousOn_coordChange ℝ e e')

/-- The coordinate changes are nowhere zero. -/
theorem det_coordChange_ne_zero {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (Trivialization.coordChangeL ℝ e e' b : F₀ →L[ℝ] F₀).det ≠ 0 := by
  intro h
  apply wedgeAt_ne_zero e hb.1
  rw [wedgeAt_eq_det_smul e e' hb, h, zero_smul]

end Frame

/-! ### `λ(E)` as a topological line bundle -/

section Lam

variable (e : Trivialization F₀ (π F₀ E)) [MemTrivializationAtlas e]

/-- **The trivialization of `λ(E)` induced by a trivialization `e` of `E`**:
`(b, x) ↦ (b, (e₁(b) ∧ … ∧ eₙ(b))*(x))` over the base set of `e`. -/
def lamPretriv : Pretrivialization ℝ (π ℝ (Lam F₀ E)) where
  toFun x := (x.1, coord e x.1 x.2)
  invFun p := ⟨p.1, p.2 • wedgeAt e p.1⟩
  source := TotalSpace.proj ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ hx := ⟨hx, mem_univ _⟩
  map_target' _ hp := hp.1
  left_inv' x hx := by
    obtain ⟨b, v⟩ := x
    exact congrArg (TotalSpace.mk b) (coord_smul_wedgeAt e hx v)
  right_inv' p hp := by
    refine Prod.ext rfl ?_
    change coord e p.1 (p.2 • wedgeAt e p.1) = p.2
    rw [map_smul, coord_wedgeAt e hp.1, smul_eq_mul, mul_one]
  open_target := e.open_baseSet.prod isOpen_univ
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- The atlas of `λ(E)`: one trivialization for each trivialization of the atlas of `E`. -/
def lamAtlas : Set (Pretrivialization ℝ (π ℝ (Lam F₀ E))) :=
  range fun e : FiberBundle.trivializationAtlas F₀ E =>
    haveI : MemTrivializationAtlas e.1 := ⟨e.2⟩
    lamPretriv e.1

theorem lamPretriv_mem_lamAtlas : lamPretriv e ∈ lamAtlas (F₀ := F₀) (E := E) :=
  ⟨⟨e, MemTrivializationAtlas.out⟩, rfl⟩

theorem isInducing_coord {b : B} (hb : b ∈ e.baseSet) : IsInducing (coord e b) := by
  have := IsModuleTopology.toContinuousAdd ℝ (Lam F₀ E b)
  exact (Function.LeftInverse.isEmbedding (f := fun t : ℝ => t • wedgeAt e b)
    (fun x => coord_smul_wedgeAt e hb x) (continuous_id.smul continuous_const)
    (IsModuleTopology.continuous_of_linearMap _)).isInducing

variable (F₀ E) in
/-- **`λ(E)` as a vector prebundle** (Lemma 6.5.3 for `λ(E)`): the trivializations induced by
those of `E`; the coordinate changes are the determinants of those of `E`. -/
def lamPrebundle : VectorPrebundle ℝ ℝ (Lam F₀ E) where
  pretrivializationAtlas := lamAtlas
  pretrivialization_linear' := by
    rintro _ ⟨e, rfl⟩
    have : MemTrivializationAtlas e.1 := ⟨e.2⟩
    exact ⟨fun b _ => (coord e.1 b).isLinear⟩
  pretrivializationAt b := lamPretriv (trivializationAt F₀ E b)
  mem_base_pretrivializationAt b := FiberBundle.mem_baseSet_trivializationAt F₀ E b
  pretrivialization_mem_atlas b := lamPretriv_mem_lamAtlas _
  exists_coordChange := by
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    have : MemTrivializationAtlas e.1 := ⟨e.2⟩
    have : MemTrivializationAtlas e'.1 := ⟨e'.2⟩
    refine ⟨fun b => (Trivialization.coordChangeL ℝ e.1 e'.1 b : F₀ →L[ℝ] F₀).det •
      ContinuousLinearMap.id ℝ ℝ, (continuousOn_det_coordChange e.1 e'.1).smul continuousOn_const,
      fun b hb v => ?_⟩
    rw [(lamPretriv e.1).mk_symm hb.1 v]
    change (Trivialization.coordChangeL ℝ e.1 e'.1 b : F₀ →L[ℝ] F₀).det * v =
      coord e'.1 b (v • wedgeAt e.1 b)
    rw [map_smul, coord_wedgeAt_eq_det e.1 e'.1 hb, smul_eq_mul, mul_comm]
  totalSpaceMk_isInducing b :=
    Topology.isInducing_const_prod.2
      (isInducing_coord _ (FiberBundle.mem_baseSet_trivializationAt F₀ E b))

instance : TopologicalSpace (TotalSpace ℝ (Lam F₀ E)) := (lamPrebundle F₀ E).totalSpaceTopology

/-- **Lemma 6.5.3 for `λ(E)`**: `λ(E)` is a topological fibre bundle with fibre `ℝ`. -/
instance : FiberBundle ℝ (Lam F₀ E) := (lamPrebundle F₀ E).toFiberBundle

/-- **Lemma 6.5.3 for `λ(E)`**: `λ(E)` is a topological line bundle. -/
instance : VectorBundle ℝ ℝ (Lam F₀ E) := (lamPrebundle F₀ E).toVectorBundle

/-- **Naturality**: the wedge of the frame of a trivialization of `E` is a continuous section of
`λ(E)` over its base set (it has constant coordinate `1` in the induced trivialization). -/
theorem continuousOn_wedgeAt :
    ContinuousOn (fun b => TotalSpace.mk' ℝ b (wedgeAt e b)) e.baseSet := by
  intro b₀ hb₀
  rw [FiberBundle.continuousWithinAt_section]
  set e₀ := trivializationAt F₀ E b₀
  have h₀ : b₀ ∈ e₀.baseSet := FiberBundle.mem_baseSet_trivializationAt F₀ E b₀
  have hnhds : e.baseSet ∩ e₀.baseSet ∈ 𝓝 b₀ :=
    (e.open_baseSet.inter e₀.open_baseSet).mem_nhds ⟨hb₀, h₀⟩
  have hc : ContinuousAt (fun b => (Trivialization.coordChangeL ℝ e e₀ b : F₀ →L[ℝ] F₀).det) b₀ :=
    (continuousOn_det_coordChange e e₀).continuousAt hnhds
  refine (hc.congr ?_).continuousWithinAt
  filter_upwards [hnhds] with b hb
  exact (coord_wedgeAt_eq_det e e₀ hb).symm

end Lam

/-! ### `λ*(E)` as a topological line bundle -/

section LamDual

variable (e : Trivialization F₀ (π F₀ E)) [MemTrivializationAtlas e]

/-- The vector `(e₁(b) ∧ … ∧ eₙ(b))*` of `λ*(E_b)`. -/
def dualWedgeAt (b : B) : LamDual F₀ E b := dualVec (wedgeAt e b : maxPow (E b))

/-- The evaluation `ξ ↦ ξ(e₁(b) ∧ … ∧ eₙ(b))` on `λ*(E_b)`. -/
def evalWedge (b : B) : LamDual F₀ E b →ₗ[ℝ] ℝ :=
  Module.Dual.eval ℝ (maxPow (E b)) (wedgeAt e b : maxPow (E b))

theorem evalWedge_dualWedgeAt {b : B} (hb : b ∈ e.baseSet) :
    evalWedge e b (dualWedgeAt e b) = 1 :=
  coord_wedgeAt e hb

omit [MemTrivializationAtlas e] in
/-- `(e₁ ∧ … ∧ eₙ)*` evaluated at another frame's wedge is the coordinate change of `λ(E)`. -/
theorem evalWedge_dualWedgeAt' (e' : Trivialization F₀ (π F₀ E)) [MemTrivializationAtlas e']
    (b : B) : evalWedge e' b (dualWedgeAt e b) = coord e b (wedgeAt e' b) :=
  rfl

/-- Every `ξ ∈ λ*(E_b)` is `ξ(e₁ ∧ … ∧ eₙ) · (e₁ ∧ … ∧ eₙ)*` on the base set. -/
theorem evalWedge_smul_dualWedgeAt {b : B} (hb : b ∈ e.baseSet) (ξ : LamDual F₀ E b) :
    evalWedge e b ξ • dualWedgeAt e b = ξ := by
  refine dual_ext_of_ne_zero (L := maxPow (E b)) (finrank_lam (F₀ := F₀) b) (wedgeAt_ne_zero e hb)
    (φ := (evalWedge e b ξ • dualWedgeAt e b : LamDual F₀ E b)) (ψ := ξ) ?_
  change evalWedge e b (evalWedge e b ξ • dualWedgeAt e b) = evalWedge e b ξ
  rw [map_smul, evalWedge_dualWedgeAt e hb, smul_eq_mul, mul_one]

/-- **The trivialization of `λ*(E)` induced by a trivialization `e` of `E`**:
`(b, ξ) ↦ (b, ξ(e₁(b) ∧ … ∧ eₙ(b)))` over the base set of `e`. -/
def lamDualPretriv : Pretrivialization ℝ (π ℝ (LamDual F₀ E)) where
  toFun x := (x.1, evalWedge e x.1 x.2)
  invFun p := ⟨p.1, p.2 • dualWedgeAt e p.1⟩
  source := TotalSpace.proj ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ hx := ⟨hx, mem_univ _⟩
  map_target' _ hp := hp.1
  left_inv' x hx := by
    obtain ⟨b, ξ⟩ := x
    exact congrArg (TotalSpace.mk b) (evalWedge_smul_dualWedgeAt e hx ξ)
  right_inv' p hp := by
    refine Prod.ext rfl ?_
    change evalWedge e p.1 (p.2 • dualWedgeAt e p.1) = p.2
    rw [map_smul, evalWedge_dualWedgeAt e hp.1, smul_eq_mul, mul_one]
  open_target := e.open_baseSet.prod isOpen_univ
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- The atlas of `λ*(E)`: one trivialization for each trivialization of the atlas of `E`. -/
def lamDualAtlas : Set (Pretrivialization ℝ (π ℝ (LamDual F₀ E))) :=
  range fun e : FiberBundle.trivializationAtlas F₀ E =>
    haveI : MemTrivializationAtlas e.1 := ⟨e.2⟩
    lamDualPretriv e.1

theorem lamDualPretriv_mem_lamDualAtlas :
    lamDualPretriv e ∈ lamDualAtlas (F₀ := F₀) (E := E) :=
  ⟨⟨e, MemTrivializationAtlas.out⟩, rfl⟩

theorem isInducing_evalWedge {b : B} (hb : b ∈ e.baseSet) : IsInducing (evalWedge e b) := by
  have := IsModuleTopology.toContinuousAdd ℝ (LamDual F₀ E b)
  exact (Function.LeftInverse.isEmbedding (f := fun t : ℝ => t • dualWedgeAt e b)
    (fun ξ => evalWedge_smul_dualWedgeAt e hb ξ) (continuous_id.smul continuous_const)
    (IsModuleTopology.continuous_of_linearMap _)).isInducing

variable (F₀ E) in
/-- **`λ*(E)` as a vector prebundle** (Lemma 6.5.3 for `λ*(E)`): the trivializations induced by
those of `E`; the coordinate changes are the inverse determinants of those of `E`. -/
def lamDualPrebundle : VectorPrebundle ℝ ℝ (LamDual F₀ E) where
  pretrivializationAtlas := lamDualAtlas
  pretrivialization_linear' := by
    rintro _ ⟨e, rfl⟩
    have : MemTrivializationAtlas e.1 := ⟨e.2⟩
    exact ⟨fun b _ => (evalWedge e.1 b).isLinear⟩
  pretrivializationAt b := lamDualPretriv (trivializationAt F₀ E b)
  mem_base_pretrivializationAt b := FiberBundle.mem_baseSet_trivializationAt F₀ E b
  pretrivialization_mem_atlas b := lamDualPretriv_mem_lamDualAtlas _
  exists_coordChange := by
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    have : MemTrivializationAtlas e.1 := ⟨e.2⟩
    have : MemTrivializationAtlas e'.1 := ⟨e'.2⟩
    refine ⟨fun b => (Trivialization.coordChangeL ℝ e'.1 e.1 b : F₀ →L[ℝ] F₀).det •
      ContinuousLinearMap.id ℝ ℝ,
      ((continuousOn_det_coordChange e'.1 e.1).mono fun b hb => ⟨hb.2, hb.1⟩).smul
        continuousOn_const, fun b hb v => ?_⟩
    rw [(lamDualPretriv e.1).mk_symm hb.1 v]
    change (Trivialization.coordChangeL ℝ e'.1 e.1 b : F₀ →L[ℝ] F₀).det * v =
      evalWedge e'.1 b (v • dualWedgeAt e.1 b)
    rw [map_smul, evalWedge_dualWedgeAt', coord_wedgeAt_eq_det e'.1 e.1 ⟨hb.2, hb.1⟩,
      smul_eq_mul, mul_comm]
  totalSpaceMk_isInducing b :=
    Topology.isInducing_const_prod.2
      (isInducing_evalWedge _ (FiberBundle.mem_baseSet_trivializationAt F₀ E b))

instance : TopologicalSpace (TotalSpace ℝ (LamDual F₀ E)) :=
  (lamDualPrebundle F₀ E).totalSpaceTopology

/-- **Lemma 6.5.3 for `λ*(E)`**: `λ*(E)` is a topological fibre bundle with fibre `ℝ`. -/
instance : FiberBundle ℝ (LamDual F₀ E) := (lamDualPrebundle F₀ E).toFiberBundle

/-- **Lemma 6.5.3 for `λ*(E)`**: `λ*(E)` is a topological line bundle. -/
instance : VectorBundle ℝ ℝ (LamDual F₀ E) := (lamDualPrebundle F₀ E).toVectorBundle

/-- **Naturality**: `(e₁ ∧ … ∧ eₙ)*` is a continuous section of `λ*(E)` over the base set of
`e`. -/
theorem continuousOn_dualWedgeAt :
    ContinuousOn (fun b => TotalSpace.mk' ℝ b (dualWedgeAt e b)) e.baseSet := by
  intro b₀ hb₀
  rw [FiberBundle.continuousWithinAt_section]
  set e₀ := trivializationAt F₀ E b₀
  have h₀ : b₀ ∈ e₀.baseSet := FiberBundle.mem_baseSet_trivializationAt F₀ E b₀
  have hnhds : e₀.baseSet ∩ e.baseSet ∈ 𝓝 b₀ :=
    (e₀.open_baseSet.inter e.open_baseSet).mem_nhds ⟨h₀, hb₀⟩
  have hc : ContinuousAt (fun b => (Trivialization.coordChangeL ℝ e₀ e b : F₀ →L[ℝ] F₀).det) b₀ :=
    (continuousOn_det_coordChange e₀ e).continuousAt hnhds
  refine (hc.congr ?_).continuousWithinAt
  filter_upwards [hnhds] with b hb
  exact (coord_wedgeAt_eq_det e₀ e hb).symm

end LamDual

/-! ### `E ⊕ F` -/

section Sum

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {E₁ : B → Type*} [∀ b, AddCommGroup (E₁ b)] [∀ b, Module ℝ (E₁ b)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ b, TopologicalSpace (E₁ b)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]

omit [FiniteDimensional ℝ F₀] in
/-- **Lemma 6.5.3 for `E ⊕ F`**: the fibrewise direct sum `E ×ᵇ F` is a topological vector bundle
with fibre `F₀ × F₁` (Mathlib's `Bundle.Prod.vectorBundle`, with the product trivializations). -/
theorem lemma_6_5_3_prod : VectorBundle ℝ (F₀ × F₁) (E ×ᵇ E₁) := inferInstance

end Sum

/-! ### `E ⊗ F` as a topological vector bundle -/

section Tensor

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {E₁ : B → Type*} [∀ b, AddCommGroup (E₁ b)] [∀ b, Module ℝ (E₁ b)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ b, TopologicalSpace (E₁ b)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  (e : Trivialization F₀ (π F₀ E)) [MemTrivializationAtlas e]
  (e₁ : Trivialization F₁ (π F₁ E₁)) [MemTrivializationAtlas e₁]

/-- `(u, w) ↦ (i ↦ (e u)ᵢ • e₁ w)`, `(·)ᵢ` the coordinates in the basis `Module.finBasis` of
`F₀`. -/
def tenBilin (b : B) : E b →ₗ[ℝ] E₁ b →ₗ[ℝ] (Fin (finrank ℝ F₀) → F₁) :=
  LinearMap.mk₂ ℝ (fun u w i =>
      (Module.finBasis ℝ F₀).repr (e.linearMapAt ℝ b u) i • e₁.linearMapAt ℝ b w)
    (fun _ _ _ => by funext i; simp [add_smul])
    (fun _ _ _ => by funext i; simp [mul_smul])
    (fun _ _ _ => by funext i; simp)
    (fun _ _ _ => by funext i; simp only [map_smul, Pi.smul_apply]; exact smul_comm _ _ _)

/-- The fibre map `E_b ⊗ F_b → F₁ⁿ` of the trivialization induced by `e`, `e₁`:
`u ⊗ w ↦ (i ↦ (e u)ᵢ • e₁ w)`. -/
def tenMap (b : B) : E b ⊗[ℝ] E₁ b →ₗ[ℝ] (Fin (finrank ℝ F₀) → F₁) :=
  TensorProduct.lift (tenBilin e e₁ b)

omit [FiniteDimensional ℝ F₁] in
theorem tenMap_tmul (b : B) (u : E b) (w : E₁ b) :
    tenMap e e₁ b (u ⊗ₜ w) = fun i =>
      (Module.finBasis ℝ F₀).repr (e.linearMapAt ℝ b u) i • e₁.linearMapAt ℝ b w :=
  rfl

/-- Its inverse `v ↦ ∑ᵢ e⁻¹(fᵢ) ⊗ e₁⁻¹(vᵢ)`. -/
def tenInv (b : B) : (Fin (finrank ℝ F₀) → F₁) →ₗ[ℝ] E b ⊗[ℝ] E₁ b :=
  ∑ i, (TensorProduct.mk ℝ (E b) (E₁ b) (e.symmₗ ℝ b (Module.finBasis ℝ F₀ i))) ∘ₗ
    e₁.symmₗ ℝ b ∘ₗ LinearMap.proj i

omit [FiniteDimensional ℝ F₁] in
theorem tenInv_apply (b : B) (v : Fin (finrank ℝ F₀) → F₁) :
    tenInv e e₁ b v = ∑ i, e.symmₗ ℝ b (Module.finBasis ℝ F₀ i) ⊗ₜ e₁.symmₗ ℝ b (v i) := by
  simp [tenInv]

omit [FiniteDimensional ℝ F₁] in
theorem tenInv_tenMap {b : B} (hb : b ∈ e.baseSet ∩ e₁.baseSet) (x : E b ⊗[ℝ] E₁ b) :
    tenInv e e₁ b (tenMap e e₁ b x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u w =>
    have hu : ∑ i, (Module.finBasis ℝ F₀).repr (e.linearMapAt ℝ b u) i •
        e.symmₗ ℝ b (Module.finBasis ℝ F₀ i) = u := by
      conv_rhs => rw [← e.symmₗ_linearMapAt (R := ℝ) hb.1 u,
        ← (Module.finBasis ℝ F₀).sum_repr (e.linearMapAt ℝ b u)]
      simp_rw [map_sum, map_smul]
    rw [tenMap_tmul, tenInv_apply]
    simp only [map_smul, e₁.symmₗ_linearMapAt (R := ℝ) hb.2, ← TensorProduct.smul_tmul,
      ← TensorProduct.sum_tmul, hu]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [FiniteDimensional ℝ F₁] in
theorem tenMap_tenInv {b : B} (hb : b ∈ e.baseSet ∩ e₁.baseSet) (v : Fin (finrank ℝ F₀) → F₁) :
    tenMap e e₁ b (tenInv e e₁ b v) = v := by
  rw [tenInv_apply, map_sum]
  funext j
  simp [tenMap_tmul, e.linearMapAt_symmₗ (R := ℝ) hb.1, e₁.linearMapAt_symmₗ (R := ℝ) hb.2,
    Finsupp.single_apply]

/-- `tenMap` on the fibre `Ten F₀ F₁ E E₁ b` (with its module topology). -/
def tenMapT (b : B) : Ten F₀ F₁ E E₁ b →ₗ[ℝ] (Fin (finrank ℝ F₀) → F₁) := tenMap e e₁ b

/-- `tenInv` into the fibre `Ten F₀ F₁ E E₁ b`. -/
def tenInvT (b : B) : (Fin (finrank ℝ F₀) → F₁) →ₗ[ℝ] Ten F₀ F₁ E E₁ b := tenInv e e₁ b

theorem isInducing_tenMapT {b : B} (hb : b ∈ e.baseSet ∩ e₁.baseSet) :
    IsInducing (tenMapT e e₁ b) := by
  have := IsModuleTopology.topologicalAddGroup ℝ (Ten F₀ F₁ E E₁ b)
  exact (Function.LeftInverse.isEmbedding (f := tenInvT e e₁ b)
    (fun x => tenInv_tenMap e e₁ hb x) (LinearMap.continuous_of_finiteDimensional _)
    (IsModuleTopology.continuous_of_linearMap (R := ℝ) (A := Ten F₀ F₁ E E₁ b)
      (tenMapT e e₁ b))).isInducing

/-- **The trivialization of `E ⊗ F` induced by trivializations `e`, `e₁` of `E`, `F`**:
`(b, u ⊗ w) ↦ (b, i ↦ (e u)ᵢ • e₁ w)` over the common base set. -/
def tenPretriv :
    Pretrivialization (Fin (finrank ℝ F₀) → F₁) (π (Fin (finrank ℝ F₀) → F₁) (Ten F₀ F₁ E E₁)) where
  toFun x := (x.1, tenMap e e₁ x.1 x.2)
  invFun p := ⟨p.1, tenInv e e₁ p.1 p.2⟩
  source := TotalSpace.proj ⁻¹' (e.baseSet ∩ e₁.baseSet)
  target := (e.baseSet ∩ e₁.baseSet) ×ˢ univ
  map_source' _ hx := ⟨hx, mem_univ _⟩
  map_target' _ hp := hp.1
  left_inv' x hx := by
    obtain ⟨b, v⟩ := x
    exact congrArg (TotalSpace.mk b) (tenInv_tenMap e e₁ hx v)
  right_inv' p hp := Prod.ext rfl (tenMap_tenInv e e₁ hp.1 p.2)
  open_target := (e.open_baseSet.inter e₁.open_baseSet).prod isOpen_univ
  baseSet := e.baseSet ∩ e₁.baseSet
  open_baseSet := e.open_baseSet.inter e₁.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable (F₀ F₁ E E₁) in
/-- The atlas of `E ⊗ F`: one trivialization for each pair of trivializations of the atlases of
`E` and `F`. -/
def tenAtlas : Set (Pretrivialization (Fin (finrank ℝ F₀) → F₁)
    (π (Fin (finrank ℝ F₀) → F₁) (Ten F₀ F₁ E E₁))) :=
  range fun ee : FiberBundle.trivializationAtlas F₀ E × FiberBundle.trivializationAtlas F₁ E₁ =>
    haveI : MemTrivializationAtlas ee.1.1 := ⟨ee.1.2⟩
    haveI : MemTrivializationAtlas ee.2.1 := ⟨ee.2.2⟩
    tenPretriv ee.1.1 ee.2.1

omit [FiniteDimensional ℝ F₁] in
theorem tenPretriv_mem_tenAtlas : tenPretriv e e₁ ∈ tenAtlas F₀ E F₁ E₁ :=
  ⟨⟨⟨e, MemTrivializationAtlas.out⟩, ⟨e₁, MemTrivializationAtlas.out⟩⟩, rfl⟩

variable (e' : Trivialization F₀ (π F₀ E)) [MemTrivializationAtlas e']
  (e₁' : Trivialization F₁ (π F₁ E₁)) [MemTrivializationAtlas e₁']

/-- The coordinate change of `E ⊗ F`: `v ↦ (j ↦ ∑ᵢ (A fᵢ)ⱼ • C vᵢ)`, the matrix of `A ⊗ C` for
the coordinate changes `A = e' ∘ e⁻¹` of `E` and `C = e₁' ∘ e₁⁻¹` of `F`. -/
def tenCoordChange (b : B) : (Fin (finrank ℝ F₀) → F₁) →L[ℝ] (Fin (finrank ℝ F₀) → F₁) :=
  LinearMap.toContinuousLinearMap (LinearMap.pi fun j => ∑ i,
    (Module.finBasis ℝ F₀).repr (Trivialization.coordChangeL ℝ e e' b (Module.finBasis ℝ F₀ i)) j •
      ((Trivialization.coordChangeL ℝ e₁ e₁' b : F₁ →L[ℝ] F₁) : F₁ →ₗ[ℝ] F₁) ∘ₗ LinearMap.proj i)

theorem tenCoordChange_apply (b : B) (v : Fin (finrank ℝ F₀) → F₁) (j : Fin (finrank ℝ F₀)) :
    tenCoordChange e e₁ e' e₁' b v j = ∑ i,
      (Module.finBasis ℝ F₀).repr (Trivialization.coordChangeL ℝ e e' b
        (Module.finBasis ℝ F₀ i)) j • Trivialization.coordChangeL ℝ e₁ e₁' b (v i) := by
  simp [tenCoordChange]

/-- The coordinate changes of `E ⊗ F` are continuous. -/
theorem continuousOn_tenCoordChange :
    ContinuousOn (tenCoordChange e e₁ e' e₁')
      ((e.baseSet ∩ e₁.baseSet) ∩ (e'.baseSet ∩ e₁'.baseSet)) := by
  have hA := (continuousOn_coordChange ℝ e e').mono fun b (hb : b ∈ (e.baseSet ∩ e₁.baseSet) ∩
    (e'.baseSet ∩ e₁'.baseSet)) => (⟨hb.1.1, hb.2.1⟩ : b ∈ e.baseSet ∩ e'.baseSet)
  have hC := (continuousOn_coordChange ℝ e₁ e₁').mono fun b (hb : b ∈ (e.baseSet ∩ e₁.baseSet) ∩
    (e'.baseSet ∩ e₁'.baseSet)) => (⟨hb.1.2, hb.2.2⟩ : b ∈ e₁.baseSet ∩ e₁'.baseSet)
  refine continuousOn_clm_apply.2 fun v => continuousOn_pi.2 fun j => ?_
  simp_rw [tenCoordChange_apply]
  refine continuousOn_finsetSum _ fun i _ => ContinuousOn.smul ?_ (hC.clm_apply continuousOn_const)
  exact (LinearMap.continuous_of_finiteDimensional
    ((Module.finBasis ℝ F₀).coord j)).comp_continuousOn (hA.clm_apply continuousOn_const)

/-- **The coordinate changes of `E ⊗ F` are those of `E` tensor those of `F`**:
`(e' ⊗ e₁') ∘ (e ⊗ e₁)⁻¹ = A ⊗ C` in the coordinates `F₁ⁿ`. -/
theorem tenMap_tenInv_eq {b : B}
    (hb : b ∈ (e.baseSet ∩ e₁.baseSet) ∩ (e'.baseSet ∩ e₁'.baseSet))
    (v : Fin (finrank ℝ F₀) → F₁) :
    tenMap e' e₁' b (tenInv e e₁ b v) = tenCoordChange e e₁ e' e₁' b v := by
  rw [tenInv_apply, map_sum]
  funext j
  simp only [Finset.sum_apply, tenMap_tmul, tenCoordChange_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [e.symmₗ_apply hb.1.1, e₁.symmₗ_apply hb.1.2, e'.coe_linearMapAt_of_mem hb.2.1,
    e₁'.coe_linearMapAt_of_mem hb.2.2, e.coordChangeL_apply e' ⟨hb.1.1, hb.2.1⟩,
    e₁.coordChangeL_apply e₁' ⟨hb.1.2, hb.2.2⟩]

variable (F₀ F₁ E E₁) in
/-- **`E ⊗ F` as a vector prebundle** (Lemma 6.5.3 for `E ⊗ F`): the trivializations induced by
pairs of trivializations of `E` and `F`; the coordinate changes are the tensor products of
theirs. -/
def tenPrebundle : VectorPrebundle ℝ (Fin (finrank ℝ F₀) → F₁) (Ten F₀ F₁ E E₁) where
  pretrivializationAtlas := tenAtlas F₀ E F₁ E₁
  pretrivialization_linear' := by
    rintro _ ⟨⟨e, e₁⟩, rfl⟩
    have : MemTrivializationAtlas e.1 := ⟨e.2⟩
    have : MemTrivializationAtlas e₁.1 := ⟨e₁.2⟩
    exact ⟨fun b _ => (tenMapT e.1 e₁.1 b).isLinear⟩
  pretrivializationAt b := tenPretriv (trivializationAt F₀ E b) (trivializationAt F₁ E₁ b)
  mem_base_pretrivializationAt b :=
    ⟨FiberBundle.mem_baseSet_trivializationAt F₀ E b,
      FiberBundle.mem_baseSet_trivializationAt F₁ E₁ b⟩
  pretrivialization_mem_atlas b := tenPretriv_mem_tenAtlas _ _
  exists_coordChange := by
    rintro _ ⟨⟨e, e₁⟩, rfl⟩ _ ⟨⟨e', e₁'⟩, rfl⟩
    have : MemTrivializationAtlas e.1 := ⟨e.2⟩
    have : MemTrivializationAtlas e₁.1 := ⟨e₁.2⟩
    have : MemTrivializationAtlas e'.1 := ⟨e'.2⟩
    have : MemTrivializationAtlas e₁'.1 := ⟨e₁'.2⟩
    refine ⟨tenCoordChange e.1 e₁.1 e'.1 e₁'.1, continuousOn_tenCoordChange _ _ _ _,
      fun b hb v => ?_⟩
    rw [(tenPretriv e.1 e₁.1).mk_symm hb.1 v]
    exact (tenMap_tenInv_eq e.1 e₁.1 e'.1 e₁'.1 hb v).symm
  totalSpaceMk_isInducing b :=
    Topology.isInducing_const_prod.2 (isInducing_tenMapT _ _
      ⟨FiberBundle.mem_baseSet_trivializationAt F₀ E b,
        FiberBundle.mem_baseSet_trivializationAt F₁ E₁ b⟩)

instance : TopologicalSpace (TotalSpace (Fin (finrank ℝ F₀) → F₁) (Ten F₀ F₁ E E₁)) :=
  (tenPrebundle F₀ E F₁ E₁).totalSpaceTopology

/-- **Lemma 6.5.3 for `E ⊗ F`**: `E ⊗ F` is a topological fibre bundle with fibre `F₁ⁿ`. -/
instance : FiberBundle (Fin (finrank ℝ F₀) → F₁) (Ten F₀ F₁ E E₁) :=
  (tenPrebundle F₀ E F₁ E₁).toFiberBundle

/-- **Lemma 6.5.3 for `E ⊗ F`**: `E ⊗ F` is a topological vector bundle with fibre
`F₁ⁿ ≅ F₀ ⊗ F₁`. -/
instance : VectorBundle ℝ (Fin (finrank ℝ F₀) → F₁) (Ten F₀ F₁ E E₁) :=
  (tenPrebundle F₀ E F₁ E₁).toVectorBundle

/-- **Lemma 6.5.3** (2021 p. 260; preprint Lemma 6.19): for finite-dimensional topological
vector bundles `E`, `F` over `B`, the bundles `λ(E)`, `λ*(F)`, `E ⊕ F` and `E ⊗ F` are
topological vector bundles, with the trivializations induced by those of `E` and `F`. -/
theorem lemma_6_5_3 :
    VectorBundle ℝ ℝ (Lam F₀ E) ∧ VectorBundle ℝ ℝ (LamDual F₁ E₁) ∧
      VectorBundle ℝ (F₀ × F₁) (E ×ᵇ E₁) ∧
      VectorBundle ℝ (Fin (finrank ℝ F₀) → F₁) (Ten F₀ F₁ E E₁) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end Tensor

end DetBundle

end Polyfold
