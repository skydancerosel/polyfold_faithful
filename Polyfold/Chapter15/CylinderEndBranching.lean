import Polyfold.Chapter15.FaceSliceSubmanifolds
import Polyfold.Chapter15.GeneralPositionBoundaryWeight
import Polyfold.Chapter15.KernelBranching

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, p. 700 (proof of
Corollary 15.3.10 (3)) and §15.4, p. 703 (proof of **Corollary 15.4.4**; 2017: Corollary 15.2),
with Definitions 9.1.2, 9.3.6 and Remark 9.2.14.

# Matching local branching structures on an end of the cylinder

## The text, paraphrased

Near a point `(i, x)` of an end of the cylinder `[0, 1] × X`, with `x ∈ supp Θᵢ`, take a local
sc⁺-section structure `(s̃ⱼ, σⱼ)` of `Λ̃`.  The sheets of `Θ̃ = Λ̃ ∘ f̃` are `M̃ⱼ = {f̃ = s̃ⱼ}`.  As
`(f̃, Λ̃)` is in general position on the boundary, every point of `M̃ⱼ` in the face `{i} × X` is a
boundary point of `M̃ⱼ`; the other points of `M̃ⱼ` near `(i, x)` are interior points of the
cylinder.  So `∂M̃ⱼ = M̃ⱼ ∩ ({i} × X) = {i} × Mⱼ`, and as `Θ̃(i, y) = Θᵢ(y)`, the `Mⱼ` with the
weights `σⱼ` are a local branching structure of `Θᵢ` near `x`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `KernelBranching.restrictRep`: a local branching structure described by kernels, restricted to
  a natural representation on a smaller neighbourhood.
* `KernelBranching.mem_submanifoldBoundary`: on a tame `X`, a point of `Mⱼ ∩ ∂X` at which
  `(f, Λ)` is in general position lies in `∂Mⱼ`.
* **`KernelBranching.boundaryStratum_cyl`**: for the cylinder over `X` with `d_X ≡ 0` and the
  face condition of Theorem 15.3.9, `∂₁M̃ⱼ = M̃ⱼ ∩ ∂([0, 1] × X)` for every sheet of a local
  branching structure of `Θ̃` described by kernels.
* **`exists_slice_branching`**: for such a structure `K̃` at `(i, x)`, `i ∈ {0, 1}`, with a product
  neighbourhood `Ũ = I × U`, the slices `Mⱼ = {y | (i, y) ∈ M̃ⱼ}` with the weights of `K̃` are a
  tame local branching structure of `Θᵢ` on `U`, `∂₁M̃ⱼ = {i} × Mⱼ` and `dim Mⱼ = dim M̃ⱼ − 1`.
* **`exists_matched_branching_of_class`**, **`exists_matched_branching`**: for `i ∈ {0, 1}` and
  `x ∈ supp Θᵢ` there are a local branching structure `K̃` of `Θ̃` at `(i, x)` described by
  kernels and a tame local branching structure `B` of `Θᵢ` at `x`, with the same index set and
  weights, such that `Ũ ∩ ({i} × X) = {i} × U`, `Mⱼ = {y | (i, y) ∈ M̃ⱼ}`, `∂₁M̃ⱼ = {i} × Mⱼ`
  and `dim Mⱼ = dim M̃ⱼ − 1`; the sheets `Mⱼ` can be taken in a class of sets that contains
  every submanifold locally and is closed under intersections with open sets.
* `SliceKernelStatement`: the sheets of `B` are the solution sets `{f = sⱼ}` of the sc⁺-sections
  `sⱼ = s̃ⱼ(i, ·)` of `W → X`, with `T_yMⱼ = ker (f − sⱼ)'(y)` (a structure of `Θᵢ` described by
  kernels).  It is not proved here: the sheets of `B` are given as slices of the sheets of `K̃`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

/-! ### Restriction to a smaller natural representation -/

namespace KernelBranching

variable {f : A.Obj → A.W} {Λ : A.W → ℚ≥0} {x : A.Obj}

/-- **A local branching structure described by kernels, restricted to a natural representation
`R` on a smaller neighbourhood** `R.U ⊆ U(x)`: the sheets `Mᵢ ∩ R.U = {z ∈ R.U | f(z) = sᵢ(z)}`
with the same sections and weights. -/
def restrictRep (K : KernelBranching A f Λ x) (R : A.X.NaturalRep x) (hR : R.U ⊆ K.U) :
    KernelBranching A f Λ x where
  toLocalBranchingStructure := K.toLocalBranchingStructure.restrict R.isOpen_U R.mem_U hR
  rep := R
  U_eq := rfl
  hasPropernessProperty := K.hasPropernessProperty.mono R.isOpen_U hR
  hasTameInducedStructure i := MPolyfold.HasTameInducedStructure.inter_isOpen
    (K.isSmoothSubmanifold i) (K.hasTameInducedStructure i) R.isOpen_U
  dim := K.dim
  isSubmanifoldOfDim i := (K.isSubmanifoldOfDim i).inter_isOpen R.isOpen_U
  O := K.O
  isOpen_O := K.isOpen_O
  U_subset := hR.trans K.U_subset
  k := K.k
  sAll := K.sAll
  σAll := K.σAll
  isLocalRep := K.isLocalRep
  idx := K.idx
  idx_injective := K.idx_injective
  σ_eq := K.σ_eq
  mem_range j z hz h := K.mem_range j z (hR hz) h
  M_eq i := by
    change K.M i ∩ R.U = _
    rw [K.M_eq i]
    ext z
    constructor
    · rintro ⟨⟨-, h⟩, hz⟩; exact ⟨hz, h⟩
    · rintro ⟨hz, h⟩; exact ⟨⟨hR hz, h⟩, hz⟩
  smooth i y hy := K.smooth i y hy.1
  tangent_eq i y hy c hc hsub hyc z hz := by
    change chartVec c.isChart '' A.X.PObj.submanifoldTangent (K.M i ∩ R.U) y = _
    rw [submanifoldTangent_inter_isOpen R.isOpen_U hy.2]
    exact K.tangent_eq i y hy.1 c hc hsub hyc z hz
  onto i y hy := K.onto i y hy.1

@[simp] theorem restrictRep_U (K : KernelBranching A f Λ x) (R : A.X.NaturalRep x)
    (hR : R.U ⊆ K.U) : (K.restrictRep R hR).U = R.U := rfl

theorem restrictRep_M (K : KernelBranching A f Λ x) (R : A.X.NaturalRep x)
    (hR : R.U ⊆ K.U) (i : K.ι) : (K.restrictRep R hR).M i = K.M i ∩ R.U := rfl

/-! ### Boundary points of the sheets in general position -/

/-- **A point of `Mⱼ ∩ ∂X` in general position lies in `∂Mⱼ`** (Remark 9.2.14 with Definition
15.3.5), for the sheets of a local branching structure described by kernels on a tame `X`. -/
theorem mem_submanifoldBoundary (hX : A.X.IsTame) (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (K : KernelBranching A f Λ x) (j : K.ι) {y : A.Obj}
    (hy : y ∈ K.M j) (hb : y ∈ A.X.PObj.boundary) (hgp : IsInGeneralPositionAt f Λ y) :
    y ∈ A.X.PObj.submanifoldBoundary (K.M j) := by
  obtain ⟨hy1, hred⟩ := hgp
  have hyU : y ∈ K.U := K.subset_U j hy
  have hyM := hy
  rw [K.M_eq j] at hyM
  obtain ⟨V, d, hVo, hyV, -, hdim, hbd⟩ :=
    exists_branch_mem_submanifoldBoundary hX hf hft (x := A.X.PObj.levelMk 1 y hy1) hred hb
      K.isOpen_O K.isLocalRep (K.U_subset hyU) (i := K.idx j) hyM.2.symm
  have e : K.M j ∩ V = {z ∈ V | f z = K.sAll (K.idx j) z} ∩ K.U := by
    rw [K.M_eq j]
    ext z
    constructor
    · rintro ⟨⟨hz, h⟩, hzV⟩; exact ⟨⟨hzV, h⟩, hz⟩
    · rintro ⟨⟨hzV, h⟩, hz⟩; exact ⟨⟨hz, h⟩, hzV⟩
  have h1 : y ∈ A.X.PObj.submanifoldBoundary
      ({z ∈ V | f z = K.sAll (K.idx j) z} ∩ K.U) :=
    (MPolyfold.mem_submanifoldBoundary_inter_isOpen_iff hdim.1 K.isOpen_U hyU).2 hbd
  rw [← e] at h1
  exact (MPolyfold.mem_submanifoldBoundary_inter_isOpen_iff (K.isSmoothSubmanifold j) hVo
    hyV).1 h1

/-- **`∂₁M̃ⱼ = M̃ⱼ ∩ ∂([0, 1] × X)`** (proof of Corollary 15.3.10 (3), p. 700, and of Corollary
15.4.4, p. 703): `d_X ≡ 0`, `f` sc-Fredholm with tame germ data, `Λ̃` an sc⁺-multisection with
`Λ̃ = Λⁱ` over `t = i`, the face condition of Theorem 15.3.9 for the glued data.  Then for every
sheet of a local branching structure of `Θ̃` described by kernels, the boundary stratum is the
part of the sheet in `{0, 1} × X`. -/
theorem boundaryStratum_cyl (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁))
    {z : (A.cubeSEP 1).Obj}
    (K : KernelBranching (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1) Λ' z) (j : K.ι) :
    (A.cubeSEP 1).X.PObj.boundaryStratum (K.M j) =
      {p | p ∈ K.M j ∧ p ∈ (A.cubeSEP 1).X.PObj.boundary} := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hbd : ∀ w : (A.cubeSEP 1).W, (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary →
      Λ' w = cubeGlue Λ₀ Λ₁ w := fun w hw => by
    rcases (mem_boundary_cubeSEP_iff hX hd _).1 hw with h | h
    · exact (h0 w h).trans (cubeGlue_of_zero h).symm
    · exact (h1 w h).trans (cubeGlue_of_one h).symm
  have hfC := isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  have hS := K.isSmoothSubmanifold j
  have ht := K.hasTameInducedStructure j
  ext p
  constructor
  · intro hp
    have hpM : p ∈ K.M j := hp.1
    have h := (MPolyfold.mem_boundaryStratum_iff_subDegIndex hS ht hpM).1 hp
    exact ⟨hpM, MPolyfold.submanifoldBoundary_subset_boundary _ ⟨hS, hpM, h.ge⟩⟩
  · rintro ⟨hpM, hpb⟩
    have hpos : 0 < Λ' (cubeLiftEp (n := 1) f hf.1.1.1 p) := by
      have h := (K.toLocalBranchingStructure.mem_supp_iff (K.subset_U j hpM)).2 ⟨j, hpM⟩
      have h' : (0 : ℚ) < (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 p) : ℚ) := h
      exact_mod_cast h'
    have hgp := isInGeneralPositionAt_of_isBoundaryFaceOnto hfC hftC hΛ' hbd honto hpb hpos
    have hmem := K.mem_submanifoldBoundary hXC hfC hftC j hpM hpb hgp
    have h1' := (MPolyfold.mem_submanifoldBoundary_iff_subDegIndex hS hpM).1 hmem
    have h2 := MPolyfold.subDegIndex_le hS.isSubMPolyfold ⟨p, hpM⟩
    have h3 : (A.cubeSEP 1).X.PObj.degIndex p ≤ 1 := by
      have h := A.X.degIndex_cubeProd_one_of_degIndex_eq_zero hX hd p.1 p.2
      change (A.X.cubeProd 1).PObj.degIndex (p.1, p.2) ≤ 1
      rw [h]
      split_ifs <;> norm_num
    exact (MPolyfold.mem_boundaryStratum_iff_subDegIndex hS ht hpM).2
      (le_antisymm (h2.trans h3) h1')

end KernelBranching

/-! ### The slice structure -/

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
open Classical in
/-- **The slice of a local branching structure of the cylinder with a product neighbourhood**
(proof of Corollary 15.4.4, p. 703).  Let `d_X ≡ 0`, `f` sc-Fredholm with tame germ data, `Λ̃` an
sc⁺-multisection with `Λ̃ = Λⁱ` over `t = i`, the face condition of Theorem 15.3.9 for the glued
data, `i ∈ {0, 1}` and `Θ̃(i, y) = Θ(y)`.  Let `K̃` be a local branching structure of `Θ̃` at
`(i, x)` described by kernels with `Ũ = I × U`, `U` the domain of a natural representation at
`x` with the properness property and `I ∩ {0, 1} = {i}`.  Then the slices
`Mⱼ = {y | (i, y) ∈ M̃ⱼ}` with the weights of `K̃` are a tame local branching structure of
`Θ = Λ ∘ f` on `U`, `∂₁M̃ⱼ = {i} × Mⱼ`, and `dim Mⱼ = dim M̃ⱼ − 1`. -/
theorem exists_slice_branching (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁))
    {q : Fin 1 → unitInterval} (hi : (q 0 : ℝ) = 0 ∨ (q 0 : ℝ) = 1) {Λ : A.W → ℚ≥0}
    (hΘ : ∀ y : A.Obj, Λ' (cubeLiftEp (n := 1) f hf.1.1.1 (q, y)) = Λ (f y)) {x : A.Obj}
    (K' : KernelBranching (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1) Λ' (q, x))
    (R : A.X.NaturalRep x) (hR : A.X.HasPropernessProperty R.U)
    {I : Set (Fin 1 → unitInterval)} (hqI : q ∈ I)
    (hIq : ∀ t ∈ I, (t 0 : ℝ) = 0 ∨ (t 0 : ℝ) = 1 → t = q)
    (hKU : K'.U = I ×ˢ R.U) :
    ∃ (B : A.X.TameBranchingStructure (fun z => (Λ (f z) : ℚ)) x) (e : K'.ι ≃ B.ι),
      B.U = R.U ∧ (∀ j, K'.σ j = B.σ (e j)) ∧
      (∀ j, B.M (e j) = {y | ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.M j}) ∧
      (∀ j, (A.cubeSEP 1).X.PObj.boundaryStratum (K'.M j) =
        (cubeFaceIncl A q).obj '' B.M (e j)) ∧
      (∀ j, A.X.PObj.IsSubmanifoldOfDim (B.M (e j)) (K'.dim j - 1)) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hmemU : ∀ p : (A.cubeSEP 1).Obj, p ∈ K'.U ↔ p.1 ∈ I ∧ p.2 ∈ R.U := fun p =>
    iff_of_eq (congrArg (fun S : Set (A.cubeSEP 1).Obj => p ∈ S) hKU)
  have hKb : ∀ p ∈ K'.U, p ∈ (A.cubeSEP 1).X.PObj.boundary → p.1 = q := fun p hp hb =>
    hIq p.1 ((hmemU p).1 hp).1 ((mem_boundary_cubeSEP_iff hX hd p).1 hb)
  have hstr : ∀ j : K'.ι, (A.cubeSEP 1).X.PObj.boundaryStratum (K'.M j) =
      {p | p ∈ K'.M j ∧ p.1 = q} := fun j => by
    rw [K'.boundaryStratum_cyl hd hf hft hΛ' h0 h1 honto j]
    ext p
    constructor
    · rintro ⟨hp, hb⟩; exact ⟨hp, hKb p (K'.subset_U j hp) hb⟩
    · rintro ⟨hp, hpq⟩
      refine ⟨hp, (mem_boundary_cubeSEP_iff hX hd p).2 ?_⟩
      rw [hpq]; exact hi
  have hslice : ∀ j : K'.ι,
      {y : A.Obj | ((q, y) : (A.cubeSEP 1).Obj) ∈ (A.cubeSEP 1).X.PObj.boundaryStratum (K'.M j)} =
        {y : A.Obj | ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.M j} := fun j => by
    rw [hstr j]
    ext y
    exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩
  have hdim : ∀ j : K'.ι, A.X.PObj.IsSubmanifoldOfDim
      {y : A.Obj | ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.M j} (K'.dim j - 1) := fun j => by
    have hN := MPolyfold.isSubmanifoldOfDim_boundaryStratum (K'.isSubmanifoldOfDim j)
      (K'.hasTameInducedStructure j)
    have h := MPolyfold.IsSubmanifoldOfDim.slice (isScSmoothMap_cubeFace A q) hN
      (fun p hp => by rw [hstr j] at hp; exact hp.2)
    exact (congrArg (fun S => A.X.PObj.IsSubmanifoldOfDim S (K'.dim j - 1)) (hslice j)).mp h
  have hMU : ∀ j : K'.ι, {y : A.Obj | ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.M j} ⊆ R.U :=
    fun j y hy => ((hmemU _).1 (K'.subset_U j hy)).2
  have hcont : Continuous fun y : R.U =>
      (⟨(q, y.1), (hmemU _).2 ⟨hqI, y.2⟩⟩ : K'.U) :=
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _
  let B₀ : A.X.LocalBranchingStructure (fun z => (Λ (f z) : ℚ)) x :=
    { U := R.U
      isOpen_U := R.isOpen_U
      mem_U := R.mem_U
      ι := K'.ι
      fintype := K'.fintype
      M := fun j => {y : A.Obj | ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.M j}
      subset_U := hMU
      isSmoothSubmanifold := fun j => (hdim j).1
      mem_M := fun j => K'.mem_M j
      isProperMap := fun j => (isProperMap_inclusion_iff _).2
        ((K'.toLocalBranchingStructure.isClosed_M j).preimage hcont)
      σ := K'.σ
      σ_pos := K'.σ_pos
      eq_sum := fun y hy => by
        have h := K'.eq_sum (q, y) ((hmemU _).2 ⟨hqI, hy⟩)
        rw [hΘ y] at h
        exact h }
  let B : A.X.TameBranchingStructure (fun z => (Λ (f z) : ℚ)) x :=
    { toLocalBranchingStructure := B₀
      rep := R
      U_eq := rfl
      hasPropernessProperty := hR
      hasTameInducedStructure := fun j =>
        MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero (hdim j).1 fun a _ => hd a }
  refine ⟨B, Equiv.refl _, rfl, fun _ => rfl, fun _ => rfl, fun j => ?_, hdim⟩
  rw [hstr j]
  ext p
  constructor
  · rintro ⟨hp, hpq⟩
    refine ⟨p.2, ?_, Prod.ext hpq.symm rfl⟩
    have : p = (q, p.2) := Prod.ext hpq rfl
    change ((q, p.2) : (A.cubeSEP 1).Obj) ∈ K'.M j
    rw [← this]; exact hp
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, rfl⟩

/-! ### The matched structures on an end -/

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
open Classical in
/-- **Matching local branching structures at a point of an end of the cylinder, with sheets in a
given class** (proofs of Corollary 15.3.10 (3), p. 700, and of Corollary 15.4.4, p. 703).  Let
`d_X ≡ 0`, `f` sc-Fredholm with tame germ data, `Λ̃` an sc⁺-multisection on `[0, 1] × X` with
`Λ̃ = Λⁱ` over `t = i`, and the face condition of Theorem 15.3.9 for the glued data.  Let
`i ∈ {0, 1}`, `Λ̃ = Λ` over `t = i`, and `x ∈ supp(Λ ∘ f)`.  Let `S d` be classes of subsets of
`X` such that every `d`-dimensional submanifold through `x` is in `S d` near `x`, closed under
intersections with open sets.  Then there are a local branching structure `K̃` of
`Θ̃ = Λ̃ ∘ f̃` at `(i, x)` described by kernels and a tame local branching structure `B` of
`Θ = Λ ∘ f` at `x` with the index set and the weights of `K̃` such that

* `Ũ ∩ ({i} × X) = {i} × U`, and `Ũ ∩ ∂([0, 1] × X) ⊆ {i} × X`;
* `Mⱼ = {y | (i, y) ∈ M̃ⱼ}`;
* `∂₁M̃ⱼ = {i} × Mⱼ`;
* `Mⱼ` is a submanifold of dimension `dim M̃ⱼ − 1`, in the class `S (dim M̃ⱼ − 1)`. -/
theorem exists_matched_branching_of_class (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁))
    {i : unitInterval} (hi : (i : ℝ) = 0 ∨ (i : ℝ) = 1) {Λ : A.W → ℚ≥0}
    (hΛi : ∀ w, ((cubeVal w).1.1 0 : ℝ) = i → Λ' w = Λ (cubeVal w).2)
    {x : A.Obj} (hx : 0 < Λ (f x)) (S : ℕ → Set (Set A.Obj))
    (hS₁ : ∀ d N, A.X.PObj.IsSubmanifoldOfDim N d → x ∈ N →
      ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧ N ∩ V ∈ S d)
    (hS₂ : ∀ d N V, N ∈ S d → IsOpen V → N ∩ V ∈ S d) :
    ∃ (K' : KernelBranching (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1) Λ' ((fun _ => i), x))
      (B : A.X.TameBranchingStructure (fun z => (Λ (f z) : ℚ)) x) (e : K'.ι ≃ B.ι),
      (∀ j, K'.σ j = B.σ (e j)) ∧
      (∀ y, y ∈ B.U ↔ (((fun _ => i), y) : (A.cubeSEP 1).Obj) ∈ K'.U) ∧
      (∀ p ∈ K'.U, p ∈ (A.cubeSEP 1).X.PObj.boundary → p.1 = fun _ => i) ∧
      (∀ j, B.M (e j) = {y | (((fun _ => i), y) : (A.cubeSEP 1).Obj) ∈ K'.M j}) ∧
      (∀ j, (A.cubeSEP 1).X.PObj.boundaryStratum (K'.M j) =
        (cubeFaceIncl A (fun _ => i)).obj '' B.M (e j)) ∧
      (∀ j, A.X.PObj.IsSubmanifoldOfDim (B.M (e j)) (K'.dim j - 1)) ∧
      (∀ j, B.M (e j) ∈ S (K'.dim j - 1)) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  set q : Fin 1 → unitInterval := fun _ => i with hq
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hbd : ∀ w : (A.cubeSEP 1).W, (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary →
      Λ' w = cubeGlue Λ₀ Λ₁ w := fun w hw => by
    rcases (mem_boundary_cubeSEP_iff hX hd _).1 hw with h | h
    · exact (h0 w h).trans (cubeGlue_of_zero h).symm
    · exact (h1 w h).trans (cubeGlue_of_one h).symm
  have hfC := isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  have hΘ : ∀ y : A.Obj, Λ' (cubeLiftEp (n := 1) f hf.1.1.1 (q, y)) = Λ (f y) := fun y =>
    hΛi _ rfl
  have hbz : ((q, x) : (A.cubeSEP 1).Obj) ∈ (A.cubeSEP 1).X.PObj.boundary :=
    (mem_boundary_cubeSEP_iff hX hd _).2 hi
  have hpos' : 0 < Λ' (cubeLiftEp (n := 1) f hf.1.1.1 (q, x)) := by rw [hΘ x]; exact hx
  have hgpz := isInGeneralPositionAt_of_isBoundaryFaceOnto hfC hftC hΛ' hbd honto hbz hpos'
  obtain ⟨K₀⟩ := exists_kernelBranching hfC hftC
    (isGoodPositionAt_of_isInGeneralPositionAt hfC hftC hΛ' hpos' hgpz)
  -- a product neighbourhood `I × V` of `(i, x)` in `Ũ₀`, with `I = {|t − i| < δ}`, `δ ≤ 1`
  obtain ⟨I₀, V, hI₀, hV, hqI₀, hxV, hsub⟩ := isOpen_prod_iff.1 K₀.isOpen_U q x K₀.mem_U
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hI₀ q hqI₀
  set δ : ℝ := min ε 1 with hδdef
  have hδ : 0 < δ := lt_min hε one_pos
  set I : Set (Fin 1 → unitInterval) := {t | |(t 0 : ℝ) - i| < δ} with hIdef
  have hIo : IsOpen I :=
    isOpen_lt (continuous_abs.comp
      ((continuous_subtype_val.comp (continuous_apply 0)).sub continuous_const))
      continuous_const
  have hIc : IsConnected I := isConnected_cubeNhd i hδ
  have hqI : q ∈ I := by
    change |(i : ℝ) - i| < δ
    rw [sub_self, abs_zero]; exact hδ
  have hII₀ : I ⊆ I₀ := fun t ht => hball (by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro a
    rw [Subsingleton.elim a 0, Subtype.dist_eq, Real.dist_eq]
    exact lt_of_lt_of_le ht (min_le_left _ _))
  have hIq : ∀ t ∈ I, (t 0 : ℝ) = 0 ∨ (t 0 : ℝ) = 1 → t = q := fun t ht h01 => by
    have ht' := abs_lt.1 (lt_of_lt_of_le (show |(t 0 : ℝ) - i| < δ from ht) (min_le_right _ _))
    refine funext fun a => Subtype.ext ?_
    rw [Subsingleton.elim a 0]
    change (t 0 : ℝ) = i
    rcases h01 with h | h <;> rcases hi with h' | h' <;> rw [h, h'] at ht' ⊢ <;>
      first | rfl | (exfalso; linarith [ht'.1, ht'.2])
  -- first the neighbourhoods `U₁ ⊆ V` of `x` and `I × U₁` of `(i, x)`
  obtain ⟨Q, hxQ, hQ⟩ := A.X.exists_hasPropernessProperty x
  obtain ⟨R₁, hRW⟩ := A.X.theorem_7_1_13 x (hV.inter hQ.1) ⟨hxV, hxQ⟩
  let R₁' : (A.cubeSEP 1).X.NaturalRep ((q, x) : (A.cubeSEP 1).Obj) :=
    EpGroupoid.NaturalRep.cubeProd (X := A.X) (n := 1) R₁ hIo hIc hqI
  have hR₁K : R₁'.U ⊆ K₀.U := fun p hp => hsub ⟨hII₀ hp.1, (hRW hp.2).1⟩
  set K₁ := K₀.restrictRep R₁' hR₁K with hK₁
  have hR₁Q : A.X.HasPropernessProperty R₁.U := hQ.mono R₁.isOpen_U fun y hy => (hRW hy).2
  obtain ⟨B₁, e₁, -, -, hM₁, -, hd₁⟩ := exists_slice_branching hd hf hft hΛ' h0 h1 honto
    (q := q) hi hΘ K₁ R₁ hR₁Q hqI hIq rfl
  -- then a smaller `U ⊆ U₁` in which the slices are in the class
  have hV₂ : ∀ j : K₁.ι, ∃ V₂ : Set A.Obj, IsOpen V₂ ∧ x ∈ V₂ ∧
      {y : A.Obj | ((q, y) : (A.cubeSEP 1).Obj) ∈ K₁.M j} ∩ V₂ ∈ S (K₁.dim j - 1) := fun j => by
    have h := hd₁ j
    rw [hM₁ j] at h
    exact hS₁ _ _ h (K₁.mem_M j)
  choose V₂ hV₂o hxV₂ hV₂S using hV₂
  have : Fintype K₁.ι := K₁.fintype
  obtain ⟨R, hRW₂⟩ := A.X.theorem_7_1_13 x (R₁.isOpen_U.inter (isOpen_iInter_of_finite hV₂o))
    ⟨R₁.mem_U, mem_iInter.2 hxV₂⟩
  let R' : (A.cubeSEP 1).X.NaturalRep ((q, x) : (A.cubeSEP 1).Obj) :=
    EpGroupoid.NaturalRep.cubeProd (X := A.X) (n := 1) R hIo hIc hqI
  have hR'K : R'.U ⊆ K₁.U := fun p hp => ⟨hp.1, (hRW₂ hp.2).1⟩
  set K' := K₁.restrictRep R' hR'K with hK'
  have hRQ : A.X.HasPropernessProperty R.U := hR₁Q.mono R.isOpen_U fun y hy => (hRW₂ hy).1
  obtain ⟨B, e, hBU, hσ, hM, hstr, hdim⟩ := exists_slice_branching hd hf hft hΛ' h0 h1 honto
    (q := q) hi hΘ K' R hRQ hqI hIq rfl
  refine ⟨K', B, e, hσ, fun y => ?_, fun p hp hb => ?_, hM, hstr, hdim, fun j => ?_⟩
  · rw [hBU]
    exact ⟨fun h => ⟨hqI, h⟩, fun h => h.2⟩
  · exact hIq p.1 hp.1 ((mem_boundary_cubeSEP_iff hX hd p).1 hb)
  · rw [hM j]
    have e2 : {y : A.Obj | ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.M j} =
        ({y : A.Obj | ((q, y) : (A.cubeSEP 1).Obj) ∈ K₁.M j} ∩ V₂ j) ∩ R.U := by
      ext y
      constructor
      · rintro ⟨h, hy⟩; exact ⟨⟨h, mem_iInter.1 (hRW₂ hy.2).2 j⟩, hy.2⟩
      · rintro ⟨⟨h, -⟩, hy⟩; exact ⟨h, hqI, hy⟩
    rw [e2]
    exact hS₂ _ _ _ (hV₂S j) R.isOpen_U

/-- **Matching local branching structures at a point of an end of the cylinder**
(`exists_matched_branching_of_class` without a class of sheets). -/
theorem exists_matched_branching (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁))
    {i : unitInterval} (hi : (i : ℝ) = 0 ∨ (i : ℝ) = 1) {Λ : A.W → ℚ≥0}
    (hΛi : ∀ w, ((cubeVal w).1.1 0 : ℝ) = i → Λ' w = Λ (cubeVal w).2)
    {x : A.Obj} (hx : 0 < Λ (f x)) :
    ∃ (K' : KernelBranching (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1) Λ' ((fun _ => i), x))
      (B : A.X.TameBranchingStructure (fun z => (Λ (f z) : ℚ)) x) (e : K'.ι ≃ B.ι),
      (∀ j, K'.σ j = B.σ (e j)) ∧
      (∀ y, y ∈ B.U ↔ (((fun _ => i), y) : (A.cubeSEP 1).Obj) ∈ K'.U) ∧
      (∀ p ∈ K'.U, p ∈ (A.cubeSEP 1).X.PObj.boundary → p.1 = fun _ => i) ∧
      (∀ j, B.M (e j) = {y | (((fun _ => i), y) : (A.cubeSEP 1).Obj) ∈ K'.M j}) ∧
      (∀ j, (A.cubeSEP 1).X.PObj.boundaryStratum (K'.M j) =
        (cubeFaceIncl A (fun _ => i)).obj '' B.M (e j)) ∧
      (∀ j, A.X.PObj.IsSubmanifoldOfDim (B.M (e j)) (K'.dim j - 1)) := by
  obtain ⟨K', B, e, h1', h2, h3, h4, h5, h6, -⟩ := exists_matched_branching_of_class hd hf hft
    hΛ' h0 h1 honto hi hΛi hx (fun _ => univ)
    (fun _ _ _ _ => ⟨univ, isOpen_univ, mem_univ _, mem_univ _⟩) (fun _ _ _ _ _ => mem_univ _)
  exact ⟨K', B, e, h1', h2, h3, h4, h5, h6⟩

/-! ### The slices as solution sets -/

/-- **The slice structure is described by kernels** (p. 703: `Mⱼ = {f = s̃ⱼ(i, ·)}`): for a
local branching structure `K̃` of `Θ̃` at `(q, x)` described by kernels and a tame local branching
structure `B` of `Θ = Λ ∘ f` at `x` with a bijection `e` of the index sets, there is a local
branching structure `K` of `Θ` at `x` described by kernels, on the neighbourhood of `B` and with
the sheets of `B`, whose weights are those of `K̃`, whose sections are the restrictions
`s̃ⱼ(q, ·)` of the sections of `K̃` to the slice, and with `dim M̃ⱼ = dim Mⱼ + 1`. -/
def SliceKernelStatement {f : A.Obj → A.W} (hsec : IsSection A.P f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ : A.W → ℚ≥0} (q : Fin 1 → unitInterval) {x : A.Obj}
    (K' : KernelBranching (A.cubeSEP 1) (cubeLiftEp (n := 1) f hsec) Λ' (q, x))
    (B : A.X.TameBranchingStructure (fun z => (Λ (f z) : ℚ)) x) (e : K'.ι ≃ B.ι) : Prop :=
  ∃ (K : KernelBranching A f Λ x) (g : K'.ι ≃ K.ι), K.U = B.U ∧
    (∀ j, K.M (g j) = B.M (e j)) ∧ (∀ j, K.σ (g j) = K'.σ j) ∧
    (∀ j, K'.dim j = K.dim (g j) + 1) ∧
    ∀ j, ∀ y ∈ K.O, ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.O →
      cubeVal (K'.s j (q, y)) = ((q, y), K.s (g j) y)

end SBLocalization

end Polyfold
