import Polyfold.Chapter15.CylinderSliceKernels
import Polyfold.Chapter15.CylinderEndEffectiveMatching
import Polyfold.Chapter15.CanonicalLiftIndependence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, pp. 701–703:
**Theorem 15.4.1**, **Definition 15.4.2** and the proof of **Corollary 15.4.4** (2017: Theorem
15.6, Definition 15.7, Corollary 15.2), with Remark 6.6.19.

# The end identities of the cylinder from the canonical orientations

## The text, paraphrased

(pp. 701–702) Near a point of `supp(Λ ∘ f)` the canonical orientation of `Θ = Λ ∘ f` for an
oriented `(f, o)` is `T̂(y) = ∑_{y ∈ Mᵢ} σᵢ · (T_yMᵢ, o_{i,y})` in any local sc⁺-section structure,
`Mᵢ = {f = sᵢ}`, `T_yMᵢ = ker (f − sᵢ)'(y)` oriented by `o_y`.  (p. 703) On the cylinder
`[0, 1] × X` the section `f̃` is oriented by "`[0, 1]` first, then `o`", and with the canonical
orientations `∂Θ̃ = Θ₁ ⊔ −Θ₀`: near `(i, x)` the sheets of `Θ̃` are `M̃ⱼ = {f̃ = s̃ⱼ}`, their
boundaries are `{i} × Mⱼ` with `Mⱼ = {f = s̃ⱼ(i, ·)}`, and the orientations compare by the frame
with the `t`-direction first.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `KernelBranching.dim_eq_of_represents`: if `T(x)` is the formula of Theorem 15.4.1 in a
  structure `K` described by kernels at `x`, and `T` is described near `x` by an oriented tame
  structure of dimension `n`, every sheet of `K` has dimension `n`.
* `IsKernelCanonical Λ hf hsec o T`: `T` is given by the formula of Theorem 15.4.1 in every
  local branching structure described by kernels, with `o_{i,y}` continuous along the sheets;
  `isKernelCanonical_canonicalOrientation`: this holds for `canonicalOrientation` if the formula
  does not depend on the structure and is continuous (`CanonIndependent`, `CanonContinuous`).
* **`exists_areMatchedAt_of_kernelCanonical`**: if the orientation of `P` and `T̃` are given by
  the formula of Theorem 15.4.1 for `(f, o)` and `(f̃, õ)` and the frame convention
  `CylinderKernelFrameConvention` holds on the end `i`, every `x ∈ supp Θ` has oriented tame
  structures of `Θ` at `x` and of `Θ̃` at `(i, x)` matched with sign `(−1)^{i+1}`.  The structures
  are those of `exists_matched_kernel_branching_of_class`.
* `CylinderKernelCanonicalStatement`: Theorem 15.4.1 for the cobordism `Θ̃`.
* **`cylinderLocalEndsStatement_of_kernelCanonical`**,
  **`corollary_15_4_4_of_kernelCanonical`**, and the effective forms
  `cylinderLocalEndsEffStatement_of_kernelCanonical`,
  **`corollary_15_4_4_eff_of_kernelCanonical`**: Corollary 15.4.4 from Theorem 15.4.1 on `X` and
  on the cylinder and the frame convention.

* `IsCanonicalFor.isKernelCanonical`, `cylinderKernelCanonicalStatement_of_isCanonicalFor`,
  **`corollary_15_4_4_of_canonical`**, **`corollary_15_4_4_eff_of_canonical`**: the same with the
  predicate "the orientation of `P` is the canonical one for `(f, o)`" of Definition 15.4.2
  (`IsCanonicalPerturbation`).

## Reading

Step (c) of the proof of Corollary 15.4.4 is here reduced to three statements, none of which
mentions the local structures of the end: Theorem 15.4.1 for `(f, o)` on `X` (`hcan`),
Theorem 15.4.1 for `(f̃, õ)` on `[0, 1] × X` (`CylinderKernelCanonicalStatement`), and the
relation of `õ` to `o` on the kernels (`CylinderKernelFrameConvention`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

/-! ### The dimension of the sheets of a structure described by kernels -/

/-- **The sheets of a structure described by kernels have the dimension of the orientation**:
if `T(x)` is the sum `∑ σᵢ · (T_xMᵢ, o_{i,x})` of `K` and `T` is described near `x` by an
oriented tame structure of dimension `n` (Definition 9.3.6), then `dim Mᵢ = n` for every sheet
of `K` (every sheet of `K` contains `x`). -/
theorem KernelBranching.dim_eq_of_represents {f : A.Obj → A.W} {Λ : A.W → ℚ≥0} {x : A.Obj}
    (K : KernelBranching A f Λ x) (hf : A.B.IsScFredholmSection f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy) {n : ℕ}
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} (hT : T x = K.canonSum hf hsec o x)
    (C : A.X.OrientedTameStructure n (fun z => (Λ (f z) : ℚ)) x) (hC : C.Represents T)
    (hxs : x ∈ A.X.PObj.smoothSet) (i : K.ι) : K.dim i = n := by
  classical
  have hxM := K.mem_M i
  have h1 : (K.canonSum hf hsec o x) (K.orTangent hf hsec o i x) ≠ 0 := by
    rw [K.canonSum_apply]
    have hle : (if K.orTangent hf hsec o i x = K.orTangent hf hsec o i x then K.σ i else 0) ≤
        ∑ j with x ∈ K.M j,
          if K.orTangent hf hsec o j x = K.orTangent hf hsec o i x then K.σ j else 0 :=
      Finset.single_le_sum
        (f := fun j => if K.orTangent hf hsec o j x = K.orTangent hf hsec o i x then K.σ j else 0)
        (fun j _ => by split_ifs; exacts [(K.σ_pos j).le, le_rfl])
        (Finset.mem_filter.2 ⟨Finset.mem_univ i, hxM⟩)
    rw [if_pos rfl] at hle
    exact (lt_of_lt_of_le (K.σ_pos i) hle).ne'
  rw [← hT, hC x C.mem_U hxs, C.orientedSum_eq_sum_ite, Finsupp.finsetSum_apply] at h1
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  by_cases hxj : x ∈ C.M j
  · rw [if_pos hxj, Finsupp.single_apply] at hj
    by_cases heq : (C.orient j).tangent x = K.orTangent hf hsec o i x
    · exact (congrArg MPolyfold.OrTangent.dim heq).symm
    · rw [if_neg heq] at hj
      exact absurd rfl hj
  · rw [if_neg hxj] at hj
    exact absurd rfl hj

/-! ### Orientations given by the formula of Theorem 15.4.1 -/

section Canonical

variable {f : A.Obj → A.W} (Λ : A.W → ℚ≥0) (hf : A.B.IsScFredholmSection f)
  (hsec : A.B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy)

/-- **`T` is given by the formula of Theorem 15.4.1 in every local structure** (Definition
15.4.2): for every local branching structure `K` of `Θ = Λ ∘ f` described by kernels, the
orientations `o_{i,y}` of the kernels induced by `o` are continuous along the sheets, and
`T(y) = ∑_{y ∈ Mᵢ} σᵢ · (T_yMᵢ, o_{i,y})` at the smooth points `y` of `U`. -/
def IsKernelCanonical (T : A.Obj → A.X.PObj.OrTangent →₀ ℚ) : Prop :=
  CanonContinuous Λ hf hsec o ∧
    ∀ (x : A.Obj) (K : KernelBranching A f Λ x), ∀ y ∈ K.U, y ∈ A.X.PObj.smoothSet →
      T y = K.canonSum hf hsec o y

variable {Λ hf hsec o}

/-- **The canonical lift of Definition 15.4.2 is given by the formula in every local
structure**, if the formula does not depend on the structure and the orientations of the kernels
are continuous along the sheets. -/
theorem isKernelCanonical_canonicalOrientation (hind : CanonIndependent Λ hf hsec o)
    (hcont : CanonContinuous Λ hf hsec o) :
    IsKernelCanonical Λ hf hsec o (canonicalOrientation Λ hf hsec o) :=
  ⟨hcont, fun _ K _ hy hys => canonicalOrientation_eq hind K hy hys⟩

/-- **A canonical orientation (Definition 15.4.2) is given by the formula of Theorem 15.4.1 in
every local structure described by kernels**, if the orientations of the kernels are continuous
along the sheets: the formula does not depend on the structure (`canonIndependent`), and off the
support both sides vanish. -/
theorem IsCanonicalFor.isKernelCanonical {n : ℕ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}
    (h : IsCanonicalFor Λ hf hsec o n T) (hcont : CanonContinuous Λ hf hsec o) :
    IsKernelCanonical Λ hf hsec o T := by
  refine ⟨hcont, fun x K y hy hys => ?_⟩
  by_cases hsupp : y ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ))
  · obtain ⟨K₀, hc, hn, hR⟩ := h.2 y hsupp
    rw [hR y K₀.mem_U hys, K₀.orientedSum_toOrientedTame]
    exact canonIndependent Λ hf hsec o y x K₀ K y K₀.mem_U hy hys
  · rw [h.1.eq_zero_of_not_mem hys hsupp, K.canonSum_eq_zero hf hsec o hy hsupp]

end Canonical

/-! ### Matched oriented structures from the canonical orientations -/

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
/-- **Matched oriented structures at the points of `supp Θᵢ`, for the canonical orientations**
(proof of Corollary 15.4.4, p. 703).  Let `d_X ≡ 0`, `f` sc-Fredholm with tame germ data, `P`
an oriented regular perturbation of `f`, `Λ̃` an sc⁺-multisection on `[0, 1] × X` with
`Λ̃ = Λⁱ` over `t = i`, `Λ̃ = Λ_P` over the end `i ∈ {0, 1}`, the face condition of Theorem
15.3.9 for the glued data, and `ε = (−1)^{i+1}`.  Let the orientation of `P` be given by the
formula of Theorem 15.4.1 for `(f, o)`, and `T̃` by that formula for `(f̃, õ)`, in every local
structure described by kernels, and let the frame convention of the canonical orientations hold
on the end `i`.  Then every `x ∈ supp Θ` has oriented tame structures `C` of `Θ` at `x`, with
sheets in the class of the integration and describing `T_P`, and `C̃` of `Θ̃` at `(i, x)`
describing `T̃`, matched with sign `ε`. -/
theorem exists_areMatchedAt_of_kernelCanonical (hd : ∀ x, A.X.PObj.degIndex x = 0)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {m : ℕ} (P : OrientedRegularPerturbation A f m)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁))
    {i : unitInterval} {ε : ℝ} (hi : ((i : ℝ) = 0 ∧ ε = -1) ∨ ((i : ℝ) = 1 ∧ ε = 1))
    (hΛi : ∀ w, ((cubeVal w).1.1 0 : ℝ) = i → Λ' w = P.Λ (cubeVal w).2)
    {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
      (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)))
    {hsec : A.B.HasScPlusSectionsThrough}
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy}
    {hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough}
    {o' : ∀ z (hz : z ∈ (A.cubeSEP 1).X.PObj.smoothSet),
      Orx (cubeLiftEp (n := 1) f hf.1.1.1)
        (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 z hz}
    (hP : IsKernelCanonical P.Λ hf.2 hsec o P.T)
    (hT' : IsKernelCanonical Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2
      hsec' o' T')
    (hconv : CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o' (fun _ => i)) :
    ∀ x ∈ EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)),
      ∃ (C : A.X.OrientedTameStructure (m + 1) (fun z => (P.Λ (f z) : ℚ)) x)
        (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1)
          (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ((fun _ => i), x))
        (hCT' : C'.Represents T') (hS : ∀ j, C.M j ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets),
        C.Represents P.T ∧ AreMatchedAt (fun _ => i) C C' hΘ' hCT' hS ε := by
  classical
  intro x hx
  have hpos : 0 < P.Λ (f x) := by
    have h : (0 : ℚ) < (P.Λ (f x) : ℚ) := hx
    exact_mod_cast h
  have hi' : (i : ℝ) = 0 ∨ (i : ℝ) = 1 := hi.imp (fun h => h.1) (fun h => h.1)
  -- the class of sheets: in dimension `m + 1`, the class of the integration
  let S : ℕ → Set (Set A.Obj) := fun d =>
    {N | d = m + 1 → N ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets}
  have hS₁ : ∀ d N, A.X.PObj.IsSubmanifoldOfDim N d → x ∈ N →
      ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧ N ∩ V ∈ S d := fun d N hN hxN => by
    by_cases hdm : d = m + 1
    · subst hdm
      obtain ⟨V, hV, hxV, hNV⟩ :=
        EpGroupoid.FormEval.exists_mem_sheets (F := A.baseEP.epFormsInftyEval (m + 1)) hN hxN
      exact ⟨V, hV, hxV, fun _ => hNV⟩
    · exact ⟨univ, isOpen_univ, mem_univ _, fun h => absurd h hdm⟩
  have hS₂ : ∀ d N V, N ∈ S d → IsOpen V → N ∩ V ∈ S d := fun d N V hN hV hdm =>
    EpGroupoid.FormEval.inter_mem_sheets (hN hdm) hV
  obtain ⟨K', K, e, hσ, hU, -, hM, hstr, hKd, hKs, hcls⟩ :=
    exists_matched_kernel_branching_of_class hd hf hft hΛ' h0 h1 honto hi' hΛi hpos S hS₁ hS₂
  obtain ⟨C₀, hC₀⟩ := P.loc x hx
  have hn : ∀ j, K.dim j = m + 1 := fun j => by
    have hxs : x ∈ A.X.PObj.smoothSet := K.smooth j x (K.mem_M j)
    exact K.dim_eq_of_represents hf.2 hsec o (hP.2 x K x K.mem_U hxs) C₀ hC₀ hxs j
  have hn' : ∀ j, K'.dim j = m + 1 + 1 := fun j => by rw [hKd j, hn]
  have hc := hP.1 x K
  have hc' := hT'.1 _ K'
  have hCT' : (K'.toOrientedTame hc' hn').Represents T' :=
    K'.represents_toOrientedTame hc' hn' (hT'.2 _ K')
  have hCT : (K.toOrientedTame hc hn).Represents P.T :=
    K.represents_toOrientedTame hc hn (hP.2 x K)
  have hSh : ∀ j, (K.toOrientedTame hc hn).M j ∈
      (A.baseEP.epFormsInftyEval (m + 1)).sheets := fun j => by
    obtain ⟨j', rfl⟩ := e.surjective j
    exact hcls j' (hn (e j'))
  refine ⟨K.toOrientedTame hc hn, K'.toOrientedTame hc' hn', hCT', hSh, hCT, ?_⟩
  exact areMatchedAt_of_equiv_timeFirst _ _ hΘ' hCT' hSh
    (hi.imp (fun h => ⟨h.1, h.2⟩) (fun h => ⟨h.1, h.2⟩)) e hσ hstr
    (fun y hy => (hU y).1 hy)
    (K.hasTimeFirstFrames_of_convention hconv K' hc hc' hn hn' (fun j => j) e hKs
      fun j y hy => by
        have h := hy
        rw [hM j] at h
        exact h)

/-! ### Corollary 15.4.4 from Theorem 15.4.1 and the frame convention -/

section Statement

variable {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
  (hft : A.B.IsScFredholmSectionTame f)
  (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
  (o' : ∀ z (hz : z ∈ (A.cubeSEP 1).X.PObj.smoothSet),
    Orx (cubeLiftEp (n := 1) f hf.1.1.1)
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 z hz)

/-- **Theorem 15.4.1 for the cobordism** (step (c) of the proof of Corollary 15.4.4 as a
statement about `Θ̃` only): every regular perturbation `Λ̃` of `f̃` on `[0, 1] × X` with
`Λ̃ = Λᵢ` over `t = i` carries an orientation `T̃` of `Θ̃ = Λ̃ ∘ f̃`, described by oriented tame
structures of dimension `m + 2`, which is given by the formula of Theorem 15.4.1 for `(f̃, õ)`
in every local branching structure described by kernels. -/
def CylinderKernelCanonicalStatement {m : ℕ} (P₀ P₁ : OrientedRegularPerturbation A f m) :
    Prop :=
  ∀ Λ' : (A.cubeSEP 1).W → ℚ≥0,
    IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
      (interpAuxNorm A P₀.N P₁.N) (interpSet A P₀.U P₁.U) Λ' →
    (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = P₀.Λ (cubeVal w).2) →
    (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = P₁.Λ (cubeVal w).2) →
    (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) →
    (A.cubeSEP 1).X.IsCompactBranched (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) →
    ∃ T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ,
      (A.cubeSEP 1).X.IsOrientation (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) T' ∧
      (∀ x ∈ EpGroupoid.supp (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)),
        ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1)
          (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) x, C.Represents T') ∧
      IsKernelCanonical Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o' T'

variable {hf hft hsec' o'}

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
/-- **The local end identities from the canonical orientations** (proof of Corollary 15.4.4,
p. 703): for `d_X ≡ 0`, `f` sc-Fredholm with tame germ data and the face condition of Theorem
15.3.9 for the glued data, if the orientations of `P₀`, `P₁` are given by the formula of Theorem
15.4.1 for `(f, o)`, Theorem 15.4.1 holds for the cobordism with `(f̃, õ)`, and the frame
convention of the canonical orientations holds on both ends, then `CylinderLocalEndsStatement`
holds. -/
theorem cylinderLocalEndsStatement_of_kernelCanonical (hd : ∀ x, A.X.PObj.degIndex x = 0)
    {m : ℕ} {P₀ P₁ : OrientedRegularPerturbation A f m}
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    {hsec : A.B.HasScPlusSectionsThrough}
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy}
    (hP₀ : IsKernelCanonical P₀.Λ hf.2 hsec o P₀.T)
    (hP₁ : IsKernelCanonical P₁.Λ hf.2 hsec o P₁.T)
    (hconv₀ : CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o' (fun _ => 0))
    (hconv₁ : CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o' (fun _ => 1))
    (h : CylinderKernelCanonicalStatement hf hft hsec' o' P₀ P₁) :
    CylinderLocalEndsStatement hf.1.1.1 P₀ P₁ := by
  intro Λ' hreg e0 e1 hΘ' hcpt'
  obtain ⟨T', hT', hloc', hcan'⟩ := h Λ' hreg e0 e1 hΘ' hcpt'
  have hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ' := hreg.2.1.1
  have z0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  have z1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  refine ⟨T', hT', hloc', fun p => cylEndMap_mem_orbitSupp_zero hd hf.1.1.1 e0 e1 p,
    fun p => cylEndMap_mem_orbitSupp_one hd hf.1.1.1 e0 e1 p, ?_, ?_⟩
  · exact isLocalEndIdentity_of_matched P₀ hΘ' hcpt' hT' hloc' (i := 0) _
      (exists_areMatchedAt_of_kernelCanonical hd hf hft P₀ hΛ' e0 e1 honto (i := 0)
        (Or.inl ⟨z0, rfl⟩) e0 hΘ' hP₀ hcan' hconv₀)
  · exact isLocalEndIdentity_of_matched P₁ hΘ' hcpt' hT' hloc' (i := 1) _
      (exists_areMatchedAt_of_kernelCanonical hd hf hft P₁ hΛ' e0 e1 honto (i := 1)
        (Or.inr ⟨z1, rfl⟩) e1 hΘ' hP₁ hcan' hconv₁)

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
/-- **The effective local end identities from the canonical orientations**: the effective form
of `cylinderLocalEndsStatement_of_kernelCanonical`. -/
theorem cylinderLocalEndsEffStatement_of_kernelCanonical (hd : ∀ x, A.X.PObj.degIndex x = 0)
    {m : ℕ} (hLUC : A.X.IsLUC) (hLUCC : (A.cubeSEP 1).X.IsLUC)
    {P₀ P₁ : OrientedRegularPerturbation A f m}
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    {hsec : A.B.HasScPlusSectionsThrough}
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy}
    (hP₀ : IsKernelCanonical P₀.Λ hf.2 hsec o P₀.T)
    (hP₁ : IsKernelCanonical P₁.Λ hf.2 hsec o P₁.T)
    (hconv₀ : CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o' (fun _ => 0))
    (hconv₁ : CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o' (fun _ => 1))
    (h : CylinderKernelCanonicalStatement hf hft hsec' o' P₀ P₁) :
    CylinderLocalEndsEffStatement hf.1.1.1 hLUC hLUCC P₀ P₁ := by
  intro Λ' hreg e0 e1 hΘ' hcpt'
  obtain ⟨T', hT', hloc', hcan'⟩ := h Λ' hreg e0 e1 hΘ' hcpt'
  have hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ' := hreg.2.1.1
  have z0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  have z1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  refine ⟨T', hT', hloc', fun p => cylEndMap_mem_orbitSupp_zero hd hf.1.1.1 e0 e1 p,
    fun p => cylEndMap_mem_orbitSupp_one hd hf.1.1.1 e0 e1 p, ?_, ?_⟩
  · exact isLocalEndIdentityEff_of_matched hLUC hLUCC P₀ hΘ' hcpt' hT' hloc' (i := 0) _
      (exists_areMatchedAt_of_kernelCanonical hd hf hft P₀ hΛ' e0 e1 honto (i := 0)
        (Or.inl ⟨z0, rfl⟩) e0 hΘ' hP₀ hcan' hconv₀)
  · exact isLocalEndIdentityEff_of_matched hLUC hLUCC P₁ hΘ' hcpt' hT' hloc' (i := 1) _
      (exists_areMatchedAt_of_kernelCanonical hd hf hft P₁ hΛ' e0 e1 honto (i := 1)
        (Or.inr ⟨z1, rfl⟩) e1 hΘ' hP₁ hcan' hconv₁)

/-- **Corollary 15.4.4 (2017: Corollary 15.2), p. 703, from Theorem 15.4.1 and the frame
convention**: `corollary_15_4_4_of_local_ends` with step (c) reduced to: the orientations of the
perturbations in `Can` are given by the formula of Theorem 15.4.1 for `(f, o)` (`hcan`),
Theorem 15.4.1 for the cobordism with `(f̃, õ)` (`hor`), and the frame convention of the
canonical orientations on the two ends (`hconv₀`, `hconv₁`). -/
theorem corollary_15_4_4_of_kernelCanonical
    (hrelC : theorem_15_3_7_relative_statement (A.cubeSEP 1))
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity)
    (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    (Can : OrientedRegularPerturbation A f m → Prop)
    (hglue : ∀ P₀ P₁, Can P₀ → Can P₁ →
      IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue P₀.Λ P₁.Λ) ∧
        IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    {hsec : A.B.HasScPlusSectionsThrough}
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy}
    (hcan : ∀ P, Can P → IsKernelCanonical P.Λ hf.2 hsec o P.T)
    (hconv₀ : CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o' (fun _ => 0))
    (hconv₁ : CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o' (fun _ => 1))
    (hor : ∀ P₀ P₁, Can P₀ → Can P₁ → CylinderKernelCanonicalStatement hf hft hsec' o' P₀ P₁) :
    corollary_15_4_4_statement A f m Can :=
  corollary_15_4_4_of_local_ends hrelC hd hpara hPU hPUC hf hft hS Can hglue fun P₀ P₁ h₀ h₁ =>
    cylinderLocalEndsStatement_of_kernelCanonical hd (hglue P₀ P₁ h₀ h₁).2 (hcan P₀ h₀)
      (hcan P₁ h₁) hconv₀ hconv₁ (hor P₀ P₁ h₀ h₁)

/-- **Corollary 15.4.4, effective version (p. 703), from Theorem 15.4.1 and the frame
convention**: the effective form of `corollary_15_4_4_of_kernelCanonical`. -/
theorem corollary_15_4_4_eff_of_kernelCanonical
    (hrelC : theorem_15_3_7_relative_statement (A.cubeSEP 1))
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hLUC : A.X.IsLUC)
    (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity) (hLUCC : (A.cubeSEP 1).X.IsLUC)
    (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    (Can : OrientedRegularPerturbation A f m → Prop)
    (hglue : ∀ P₀ P₁, Can P₀ → Can P₁ →
      IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue P₀.Λ P₁.Λ) ∧
        IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    {hsec : A.B.HasScPlusSectionsThrough}
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy}
    (hcan : ∀ P, Can P → IsKernelCanonical P.Λ hf.2 hsec o P.T)
    (hconv₀ : CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o' (fun _ => 0))
    (hconv₁ : CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o' (fun _ => 1))
    (hor : ∀ P₀ P₁, Can P₀ → Can P₁ → CylinderKernelCanonicalStatement hf hft hsec' o' P₀ P₁) :
    corollary_15_4_4_eff_statement A f m hLUC Can :=
  corollary_15_4_4_eff_of_local_ends hrelC hd hpara hPU hLUC hPUC hLUCC hf hft hS Can hglue
    fun P₀ P₁ h₀ h₁ => cylinderLocalEndsEffStatement_of_kernelCanonical hd hLUC hLUCC
      (hglue P₀ P₁ h₀ h₁).2 (hcan P₀ h₀) (hcan P₁ h₁) hconv₀ hconv₁ (hor P₀ P₁ h₀ h₁)

/-! ### The same with Definition 15.4.2 -/

/-- **Theorem 15.4.1 for the cobordism, from Definition 15.4.2**: if every regular perturbation
`Λ̃` of `f̃` restricting to `Λᵢ` on the ends has a canonical orientation for `(f̃, õ)` of dimension
`m + 2` (`IsCanonicalFor`) and the orientations of the kernels are continuous along the sheets,
`CylinderKernelCanonicalStatement` holds. -/
theorem cylinderKernelCanonicalStatement_of_isCanonicalFor {m : ℕ}
    {P₀ P₁ : OrientedRegularPerturbation A f m}
    (hcont' : ∀ Λ' : (A.cubeSEP 1).W → ℚ≥0, CanonContinuous Λ'
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o')
    (h : ∀ Λ' : (A.cubeSEP 1).W → ℚ≥0,
      IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
        (interpAuxNorm A P₀.N P₁.N) (interpSet A P₀.U P₁.U) Λ' →
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = P₀.Λ (cubeVal w).2) →
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = P₁.Λ (cubeVal w).2) →
      ∃ T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ,
        IsCanonicalFor Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o'
          (m + 1 + 1) T') :
    CylinderKernelCanonicalStatement hf hft hsec' o' P₀ P₁ := by
  intro Λ' hreg e0 e1 _ _
  obtain ⟨T', hT'⟩ := h Λ' hreg e0 e1
  exact ⟨T', hT'.1, hT'.loc, hT'.isKernelCanonical (hcont' Λ')⟩

/-- **Corollary 15.4.4 (2017: Corollary 15.2), p. 703, for the canonical orientations of
Definition 15.4.2**: the predicate `Can` is "the orientation of `P` is the canonical one for
`(f, o)`" (`IsCanonicalPerturbation`).  Hypotheses beyond those of
`corollary_15_4_4_of_local_ends`: the orientations of the kernels are continuous along the
sheets on `X` and on `[0, 1] × X` (`hcont`, `hcont'`; Theorem 15.4.1), the cobordism has a
canonical orientation for `(f̃, õ)` (`hcyl`; Theorem 15.4.1 on the cylinder), and the frame
convention relating `õ` to `o` on the two ends (`hconv₀`, `hconv₁`; Remark 6.6.19). -/
theorem corollary_15_4_4_of_canonical
    (hrelC : theorem_15_3_7_relative_statement (A.cubeSEP 1))
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity)
    (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    {hsec : A.B.HasScPlusSectionsThrough}
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy}
    (hglue : ∀ P₀ P₁ : OrientedRegularPerturbation A f m,
      IsCanonicalPerturbation hf.2 hsec o P₀ → IsCanonicalPerturbation hf.2 hsec o P₁ →
      IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue P₀.Λ P₁.Λ) ∧
        IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    (hcont : ∀ Λ : A.W → ℚ≥0, CanonContinuous Λ hf.2 hsec o)
    (hcont' : ∀ Λ' : (A.cubeSEP 1).W → ℚ≥0, CanonContinuous Λ'
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o')
    (hcyl : ∀ P₀ P₁ : OrientedRegularPerturbation A f m,
      IsCanonicalPerturbation hf.2 hsec o P₀ → IsCanonicalPerturbation hf.2 hsec o P₁ →
      ∀ Λ' : (A.cubeSEP 1).W → ℚ≥0,
        IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
          (interpAuxNorm A P₀.N P₁.N) (interpSet A P₀.U P₁.U) Λ' →
        (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = P₀.Λ (cubeVal w).2) →
        (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = P₁.Λ (cubeVal w).2) →
        ∃ T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ,
          IsCanonicalFor Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o'
            (m + 1 + 1) T')
    (hconv₀ : CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o' (fun _ => 0))
    (hconv₁ : CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o' (fun _ => 1)) :
    corollary_15_4_4_statement A f m (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_of_kernelCanonical (hf := hf) (hft := hft) hrelC hd hpara hPU hPUC hS _ hglue
    (fun P hP => IsCanonicalFor.isKernelCanonical hP (hcont P.Λ)) hconv₀ hconv₁
    fun P₀ P₁ h₀ h₁ => cylinderKernelCanonicalStatement_of_isCanonicalFor hcont'
      (hcyl P₀ P₁ h₀ h₁)

/-- **Corollary 15.4.4, effective version (p. 703), for the canonical orientations of
Definition 15.4.2**: the effective form of `corollary_15_4_4_of_canonical`. -/
theorem corollary_15_4_4_eff_of_canonical
    (hrelC : theorem_15_3_7_relative_statement (A.cubeSEP 1))
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hLUC : A.X.IsLUC)
    (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity) (hLUCC : (A.cubeSEP 1).X.IsLUC)
    (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    {hsec : A.B.HasScPlusSectionsThrough}
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy}
    (hglue : ∀ P₀ P₁ : OrientedRegularPerturbation A f m,
      IsCanonicalPerturbation hf.2 hsec o P₀ → IsCanonicalPerturbation hf.2 hsec o P₁ →
      IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue P₀.Λ P₁.Λ) ∧
        IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    (hcont : ∀ Λ : A.W → ℚ≥0, CanonContinuous Λ hf.2 hsec o)
    (hcont' : ∀ Λ' : (A.cubeSEP 1).W → ℚ≥0, CanonContinuous Λ'
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o')
    (hcyl : ∀ P₀ P₁ : OrientedRegularPerturbation A f m,
      IsCanonicalPerturbation hf.2 hsec o P₀ → IsCanonicalPerturbation hf.2 hsec o P₁ →
      ∀ Λ' : (A.cubeSEP 1).W → ℚ≥0,
        IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
          (interpAuxNorm A P₀.N P₁.N) (interpSet A P₀.U P₁.U) Λ' →
        (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = P₀.Λ (cubeVal w).2) →
        (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = P₁.Λ (cubeVal w).2) →
        ∃ T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ,
          IsCanonicalFor Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o'
            (m + 1 + 1) T')
    (hconv₀ : CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o' (fun _ => 0))
    (hconv₁ : CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o' (fun _ => 1)) :
    corollary_15_4_4_eff_statement A f m hLUC (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_eff_of_kernelCanonical (hf := hf) (hft := hft) hrelC hd hpara hPU hLUC hPUC
    hLUCC hS _ hglue
    (fun P hP => IsCanonicalFor.isKernelCanonical hP (hcont P.Λ)) hconv₀ hconv₁
    fun P₀ P₁ h₀ h₁ => cylinderKernelCanonicalStatement_of_isCanonicalFor hcont'
      (hcyl P₀ P₁ h₀ h₁)

end Statement

end SBLocalization

end Polyfold
