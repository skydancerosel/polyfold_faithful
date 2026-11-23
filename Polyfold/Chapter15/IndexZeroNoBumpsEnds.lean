import Polyfold.Chapter15.CylinderPointEnds
import Polyfold.Chapter15.IndexZeroNoBumpsFrames

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2) for Fredholm index `0`, with Remark 6.6.19.

# The ends of a `1`-dimensional cobordism between weighted signed points, without bump functions

## The text, paraphrased

For index `0` the perturbed solution sets `Θᵢ = Λᵢ ∘ f` are finite sets of weighted points with
signs, and `Θ̃ = Λ̃ ∘ f̃` on `[0, 1] × X` is a `1`-dimensional compact oriented cobordism with
`∂Θ̃ = Θ₁ ⊔ −Θ₀`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`exists_arePointMatchedAt_of_kernelCanonical_loc`**: the statement of
  `exists_arePointMatchedAt_of_kernelCanonical` (`Polyfold/Chapter15/CylinderPointEnds.lean`)
  with no sc-smooth bump functions on `X`: for `d_X ≡ 0`, `T` and `T̃` given by the formula of
  Theorem 15.4.1 for `(f, o)` and `(f̃, e ∧ o)`, every point of `supp Θ` has structures matched
  with sign `(−1)^{i+1}` on the end `i`.  The signed generator of the curve through `(i, x)` is
  `exists_signed_generator_cubeOrientation_loc`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u v

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP UnitCube

variable {A : SEP.{u}}

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
/-- **Matched structures with point sheets at the points of `supp Θᵢ`, for the canonical
orientations** (proof of Corollary 15.4.4 for Fredholm index `0`, p. 703; Remark 6.6.19).  Let
`d_X ≡ 0`, `f` sc-Fredholm with tame germ data, `Λ` an
sc⁺-multisection such that `Θ = Λ ∘ f` has an orientation `T` described by oriented tame
structures of dimension `0`, `Λ̃` an sc⁺-multisection on `[0, 1] × X` with `Λ̃ = Λⁱ` over `t = i`,
`Λ̃ = Λ` over the end `i ∈ {0, 1}`, the face condition of Theorem 15.3.9 for the glued data, and
`ε = (−1)^{i+1}`.  If `T` is given by the formula of Theorem 15.4.1 for `(f, o)` and `T̃` by that
formula for `(f̃, e ∧ o)`, in every local structure described by kernels, then every
`x ∈ supp Θ` has oriented tame structures `C` of `Θ` at `x`, with point sheets and describing
`T`, and `C̃` of `Θ̃` at `(i, x)` of dimension `1` describing `T̃`, matched with sign `ε`: the
curve `M̃ⱼ` through `(i, x)` is oriented by a vector `w` with `dt(w)` the sign of the point `x`
(`exists_signed_generator_cubeOrientation_loc`), and `w` points out of `[0, 1] × X` iff
`ε · dt(w) = 1` (`frameSign_boundaryOrient_of_generator`).  No sc-smooth bump functions on `X`
are used. -/
theorem exists_arePointMatchedAt_of_kernelCanonical_loc
    (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ : A.W → ℚ≥0} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}
    (hloc : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
      ∃ C : A.X.OrientedTameStructure 0 (fun z => (Λ (f z) : ℚ)) x, C.Represents T)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁))
    {i : unitInterval} {ε : ℝ} (hi : ((i : ℝ) = 0 ∧ ε = -1) ∨ ((i : ℝ) = 1 ∧ ε = 1))
    (hΛi : ∀ w, ((cubeVal w).1.1 0 : ℝ) = i → Λ' w = Λ (cubeVal w).2)
    {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
      (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)))
    {hsec : A.B.HasScPlusSectionsThrough}
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy}
    {hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough}
    (hP : IsKernelCanonical Λ hf.2 hsec o T)
    (hT' : IsKernelCanonical Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2
      hsec' (cubeOrientation hf hft hsec o) T') :
    ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
      ∃ (C : A.X.OrientedTameStructure 0 (fun z => (Λ (f z) : ℚ)) x)
        (C' : (A.cubeSEP 1).X.OrientedTameStructure (0 + 1)
          (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ((fun _ => i), x))
        (hCT' : C'.Represents T'),
        (∀ j, C.M j ∈ EpGroupoid.pointSheets A.X) ∧ C.Represents T ∧
          ArePointMatchedAt (fun _ => i) C C' hΘ' hCT' ε := by
  classical
  intro x hx
  have hpos : 0 < Λ (f x) := by
    have h : (0 : ℚ) < (Λ (f x) : ℚ) := hx
    exact_mod_cast h
  have hi' : (i : ℝ) = 0 ∨ (i : ℝ) = 1 := hi.imp (fun h => h.1) (fun h => h.1)
  -- the class of sheets: in dimension `0`, the smooth points
  let S : ℕ → Set (Set A.Obj) := fun d => {N | d = 0 → N ∈ EpGroupoid.pointSheets A.X}
  have hS₁ : ∀ d N, A.X.PObj.IsSubmanifoldOfDim N d → x ∈ N →
      ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧ N ∩ V ∈ S d := fun d N hN hxN => by
    by_cases hd0 : d = 0
    · subst hd0
      obtain ⟨V, hV, hxV, hNV⟩ := MPolyfold.exists_isOpen_inter_subset_singleton_of_dim_zero hN
        (MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero hN.1 fun a _ => hd a) hxN
      exact ⟨V, hV, hxV, fun _ => Or.inr ⟨x, hN.1.subset_smoothSet hxN,
        Subset.antisymm hNV (singleton_subset_iff.2 ⟨hxN, hxV⟩)⟩⟩
    · exact ⟨univ, isOpen_univ, mem_univ _, fun h => absurd h hd0⟩
  have hS₂ : ∀ d N V, N ∈ S d → IsOpen V → N ∩ V ∈ S d := fun d N V hN _ hd0 => by
    rcases hN hd0 with rfl | ⟨p, hp, rfl⟩
    · exact Or.inl (empty_inter V)
    · by_cases hpV : p ∈ V
      · exact Or.inr ⟨p, hp, inter_eq_left.2 (singleton_subset_iff.2 hpV)⟩
      · exact Or.inl (singleton_inter_eq_empty.2 hpV)
  obtain ⟨K', K, e, hσ, hU, -, hM, hstr, hKd, hKs, hcls⟩ :=
    exists_matched_kernel_branching_of_class hd hf hft hΛ' h0 h1 honto hi' hΛi hpos S hS₁ hS₂
  obtain ⟨C₀, hC₀⟩ := hloc x hx
  have hn : ∀ j, K.dim j = 0 := fun j => by
    have hxs : x ∈ A.X.PObj.smoothSet := K.smooth j x (K.mem_M j)
    exact K.dim_eq_of_represents hf.2 hsec o (hP.2 x K x K.mem_U hxs) C₀ hC₀ hxs j
  have hn' : ∀ j, K'.dim j = 0 + 1 := fun j => by rw [hKd j, hn]
  have hc := hP.1 x K
  have hc' := hT'.1 _ K'
  have hCT' : (K'.toOrientedTame hc' hn').Represents T' :=
    K'.represents_toOrientedTame hc' hn' (hT'.2 _ K')
  have hCT : (K.toOrientedTame hc hn).Represents T :=
    K.represents_toOrientedTame hc hn (hP.2 x K)
  have hSh : ∀ j, (K.toOrientedTame hc hn).M j ∈ EpGroupoid.pointSheets A.X := fun j => by
    obtain ⟨j', rfl⟩ := e.surjective j
    exact hcls j' (hn (e j'))
  have hbs : ∀ j, (K'.toOrientedTame hc' hn').boundarySheet j =
      (cubeFaceIncl A (fun _ => i)).obj '' K.M (e j) := hstr
  refine ⟨K.toOrientedTame hc hn, K'.toOrientedTame hc' hn', hCT', hSh, hCT,
    fun j => e j.1, fun a b h => Subtype.ext (e.injective h), fun i' hi' => ?_,
    fun j => hσ j.1, fun j => hbs j.1, fun y hy => (hU y).1 hy, fun j y hy => ?_⟩
  · refine absurd ⟨⟨e.symm i', ?_⟩, e.apply_symm_apply i'⟩ hi'
    exact Eq.mpr (congrArg Set.Nonempty (hbs (e.symm i'))) ⟨_, x, K.mem_M _, rfl⟩
  · have hyK : y ∈ K.M (e j.1) := hy
    have hy' : (((fun _ => i), y) : (A.cubeSEP 1).Obj) ∈ K'.M j.1 := by
      have h := hyK
      rw [hM j.1] at h
      exact h
    obtain ⟨s, w, hsF, hwT, hτ, hfr⟩ := exists_signed_generator_cubeOrientation_loc hf hft
      hsec hsec' o (fun _ => i) K K' (e j.1) j.1 (hn _) (hn' _) (hKs j.1) hyK hy'
    have hzB : (((fun _ => i), y) : (A.cubeSEP 1).Obj) ∈
        (K'.toOrientedTame hc' hn').boundarySheet j.1 :=
      (Set.ext_iff.1 (hbs j.1) _).2 ⟨y, hyK, rfl⟩
    have hfr' : (fun _ : Fin (0 + 1) => w) ∈
        ((K'.toOrientedTame hc' hn').orient j.1).frames ((fun _ => i), y) :=
      (mem_frames_cast_iff (A := A.cubeSEP 1) (hn' j.1) (K'.orient hc' j.1) ((fun _ => i), y)
        _).2 hfr
    have hfs : EpGroupoid.frameSign (X := A.X)
        (((K.toOrientedTame hc hn).orient (e j.1)).tangent y) = s := by
      change EpGroupoid.frameSign (X := A.X) ((hn (e j.1) ▸ K.orient hc (e j.1)).tangent y) = s
      rw [KernelBranching.tangent_cast_aux]
      unfold EpGroupoid.frameSign
      rcases hsF with ⟨rfl, hne⟩ | ⟨rfl, hne⟩
      · exact if_pos hne
      · exact if_neg hne
    rw [hfs]
    exact frameSign_boundaryOrient_of_generator (K'.toOrientedTame hc' hn') j.1 hzB hwT hfr' hi
      (hsF.imp And.left And.left) hτ

end SBLocalization

end Polyfold
