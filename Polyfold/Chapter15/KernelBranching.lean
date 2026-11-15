import Polyfold.Chapter15.BranchKernelTangent
import Polyfold.Chapter15.TameBranched

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702, **Theorem 15.4.1** and **Definition 15.4.2** (2017: Theorem 15.6, Definition 15.7):
the local branching structures of `Θ = Λ ∘ f` whose sheets `Mᵢ = {f = sᵢ}` have the kernels of
`(f − sᵢ)'(y)` as tangent spaces.

# Local branching structures described by kernels

## The text, paraphrased

(pp. 701–702) Near a point of `supp(Λ ∘ f)`, in a local sc⁺-section structure `(sᵢ, σᵢ)`, the
solution sets `Mᵢ = {f = sᵢ}` are finite-dimensional submanifolds, `Θ = ∑ σᵢ · 1_{Mᵢ}`, and
`T_yMᵢ = ker (f − sᵢ)'(y)`; the orientation of `f` orients these kernels.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `KernelBranching f Λ x`: a tame local branching structure of `Θ = Λ ∘ f` at `x`
  (Definition 9.3.6) with sheets `Mᵢ = {z ∈ U(x) | f(z) = sᵢ(z)}` for sc⁺-sections `sᵢ` on an open
  `O ⊇ U(x)`, of dimensions `dᵢ`, consisting of smooth points, such that in every strong bundle
  chart with domain in `O` the chart vectors of `T_yMᵢ` are the kernel of `(f − sᵢ)'(y)` on `T_zO`
  and `(f − sᵢ)'(y)` is onto.
* **`exists_kernelBranching`**: at a point where `(f, Λ)` is in good position
  (Definition 15.2.4), such a structure exists (Theorem 15.2.5 with `T_yMᵢ = ker (f − sᵢ)'(y)`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}}

/-! ### One branch -/

/-- **One branch with its kernel description**: at a point `x` where the branch `(f − s)|O` is in
good position (`IsBranchGoodPosition`), there are an open `V ∋ x` in `O` and `d` such that
`M = {y ∈ V | f(y) = s(y)}` is a `d`-dimensional submanifold of `X` with tame induced structure,
its points are smooth, and in every strong bundle chart `c` with domain in `O` around `y ∈ M` the
chart vectors of `T_yM` are the kernel of `(f − s)'(y)` on `T_zO`, and `(f − s)'(y)` is onto. -/
theorem exists_branch_kernel {f : A.Obj → A.W} (hft : A.B.IsScFredholmSectionTame f)
    {s : A.Obj → A.W} {O : Set A.Obj} (hO : IsOpen O) (hs : IsScPlusSectionOn A s O) {x : A.Obj}
    (hxO : x ∈ O) (hfs : f x = s x) (hgp : IsBranchGoodPosition f s hO x hxO) :
    ∃ (V : Set A.Obj) (d : ℕ), IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
      A.X.PObj.IsSubmanifoldOfDim {y ∈ V | f y = s y} d ∧
      A.X.PObj.HasTameInducedStructure {y ∈ V | f y = s y} ∧
      ∀ y ∈ V, f y = s y → y ∈ A.X.PObj.smoothSet ∧
        ∀ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c → c.φ.source ⊆ O →
          y ∈ c.φ.source → ∀ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ y →
            chartVec c.isChart '' A.X.PObj.submanifoldTangent {y ∈ V | f y = s y} y =
                kerSet c f s z ∧
              ChartOnto c (subDeriv c f s z) z := by
  obtain ⟨Vt, hVto, hxVt, hVtO, hSt, hTt⟩ :=
    exists_tame_solutionSet_of_isBranchGoodPosition hft hO hs hxO hfs hgp
  have : Nonempty O := ⟨⟨x, hxO⟩⟩
  have := A.X.PObj.paracompactSpace_subtype O
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
    (A.X.PObj.restrictOpen hO) A.B
  obtain ⟨_, hg⟩ := hgp
  have hgO := isScFredholmSectionTame_subRestrict hO hft hs
  obtain ⟨Vm, d, hVmo, hxVm, hVmO, hdim, hall⟩ := exists_branch_tangent_eq_ker hO hft hs hxO hfs hg
  have e1 : {y ∈ Vm ∩ Vt | f y = s y} = {y ∈ Vm | f y = s y} ∩ Vt := by
    ext y; simp only [mem_ofPred_eq, mem_inter_iff]; tauto
  have e2 : {y ∈ Vm ∩ Vt | f y = s y} = {y ∈ Vt | f y = s y} ∩ Vm := by
    ext y; simp only [mem_ofPred_eq, mem_inter_iff]; tauto
  refine ⟨Vm ∩ Vt, d, hVmo.inter hVto, ⟨hxVm, hxVt⟩, inter_subset_left.trans hVmO, ?_, ?_, ?_⟩
  · rw [e1]; exact hdim.inter_isOpen hVto
  · rw [e2]; exact hTt.inter_isOpen hSt hVmo
  · intro y hy hfy
    obtain ⟨hys, hgood, htan⟩ := hall y hy.1 hfy
    refine ⟨hys, fun c hc hsub hyc z hz => ⟨?_, ?_⟩⟩
    · rw [e1, submanifoldTangent_inter_isOpen hVto hy.2]
      exact htan c hc hsub hyc z hz
    · exact chartOnto_of_isLinSurjAt_subRestrict hO hft hs hc hsub hyc hfy
        ((hgood (hsub hyc)).isGoodPositionGerm.isLinSurjAt hgO.isScSmooth) hz

/-! ### The structure -/

variable (A) in
/-- **A tame local branching structure of `Θ = Λ ∘ f` at `x` described by kernels** (Theorem
15.2.5 with the tangent spaces of 2021 pp. 701–702): sheets `Mᵢ = {z ∈ U(x) | f(z) = sᵢ(z)}` for
sc⁺-sections `sᵢ` on an open `O ⊇ U(x)`, of dimension `dᵢ`, consisting of smooth points, with
`T_yMᵢ = ker (f − sᵢ)'(y)` and `(f − sᵢ)'(y)` onto, read in every strong bundle chart with domain
in `O`. -/
structure KernelBranching (f : A.Obj → A.W) (Λ : A.W → ℚ≥0) (x : A.Obj) extends
    A.X.TameBranchingStructure (fun z => (Λ (f z) : ℚ)) x where
  /-- The dimensions `dᵢ = dim Mᵢ`. -/
  dim : ι → ℕ
  isSubmanifoldOfDim : ∀ i, A.X.PObj.IsSubmanifoldOfDim (M i) (dim i)
  /-- The domain of the local sc⁺-sections. -/
  O : Set A.Obj
  isOpen_O : IsOpen O
  U_subset : U ⊆ O
  /-- The number of local sections of the local sc⁺-section structure of `Λ` on `O`. -/
  k : ℕ
  /-- The local sc⁺-sections of the structure. -/
  sAll : Fin k → A.Obj → A.W
  /-- The weights of the structure. -/
  σAll : Fin k → ℚ≥0
  isLocalRep : IsLocalRepOn A Λ O sAll σAll
  /-- The sheet `Mᵢ` is the solution set of `f = s_{idx i}`. -/
  idx : ι → Fin k
  idx_injective : Function.Injective idx
  σ_eq : ∀ i, σ i = (σAll (idx i) : ℚ)
  mem_range : ∀ j, ∀ z ∈ U, f z = sAll j z → j ∈ Set.range idx
  M_eq : ∀ i, M i = {z ∈ U | f z = sAll (idx i) z}
  smooth : ∀ i, ∀ y ∈ M i, y ∈ A.X.PObj.smoothSet
  tangent_eq : ∀ i, ∀ y ∈ M i, ∀ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c →
    c.φ.source ⊆ O → y ∈ c.φ.source → ∀ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ y →
      chartVec c.isChart '' A.X.PObj.submanifoldTangent (M i) y = kerSet c f (sAll (idx i)) z
  onto : ∀ i, ∀ y ∈ M i, ∀ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c →
    c.φ.source ⊆ O → y ∈ c.φ.source → ∀ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ y →
      ChartOnto c (subDeriv c f (sAll (idx i)) z) z

namespace KernelBranching

variable {f : A.Obj → A.W} {Λ : A.W → ℚ≥0} {x : A.Obj} (K : KernelBranching A f Λ x)

/-- The local sc⁺-section `sᵢ` of the sheet `Mᵢ`. -/
abbrev s (i : K.ι) : A.Obj → A.W := K.sAll (K.idx i)

theorem isScPlus (i : K.ι) : IsScPlusSectionOn A (K.s i) K.O := K.isLocalRep.2.1 (K.idx i)

end KernelBranching

open Classical in
/-- **Theorem 15.2.5 with `T_yMᵢ = ker (f − sᵢ)'(y)`** (2021 pp. 690, 701–702), with the inherited
tame-germ hypothesis `hft`: if `(f, Λ)` is in good position at `x` (Definition 15.2.4), `Θ = Λ ∘ f`
has a tame local branching structure at `x` described by kernels. -/
theorem exists_kernelBranching {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ : A.W → ℚ≥0} {x : A.Obj}
    (hgp : IsGoodPositionAt f Λ x) : Nonempty (KernelBranching A f Λ x) := by
  obtain ⟨-, -, O, hO, hxO, k, s, σ, hrep, hbr⟩ := hgp
  have hsec : IsSection A.P f := hf.1.1.1
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  have hV : ∀ i, ∃ (V : Set A.Obj) (d : ℕ), IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
      (s i x = f x → A.X.PObj.IsSubmanifoldOfDim {y ∈ V | f y = s i y} d ∧
        A.X.PObj.HasTameInducedStructure {y ∈ V | f y = s i y} ∧
        ∀ y ∈ V, f y = s i y → y ∈ A.X.PObj.smoothSet ∧
          ∀ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c → c.φ.source ⊆ O →
            y ∈ c.φ.source → ∀ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ y →
              chartVec c.isChart '' A.X.PObj.submanifoldTangent {y ∈ V | f y = s i y} y =
                  kerSet c f (s i) z ∧
                ChartOnto c (subDeriv c f (s i) z) z) ∧
      (s i x ≠ f x → ∀ y ∈ V, f y ≠ s i y) := by
    intro i
    by_cases h : s i x = f x
    · obtain ⟨V, d, hVo, hxV, hVO, h1, h2, h3⟩ :=
        exists_branch_kernel hft hO (hrep.2.1 i) hxO h.symm (hbr i h)
      exact ⟨V, d, hVo, hxV, hVO, fun _ => ⟨h1, h2, h3⟩, fun h' => absurd h h'⟩
    · exact ⟨{y ∈ O | f y ≠ s i y}, 0, isOpen_sep_ne hfc hO (hrep.2.1 i).continuousOn,
        ⟨hxO, fun e => h e.symm⟩, sep_subset _ _, fun h' => absurd h' h, fun _ y hy => hy.2⟩
  choose V d hVo hxV hVO hVt hVn using hV
  obtain ⟨Q, hxQ, hQ⟩ := A.X.exists_hasPropernessProperty x
  have hWo : IsOpen (Q ∩ O ∩ ⋂ i, V i) :=
    (hQ.1.inter hO).inter (isOpen_iInter_of_finite hVo)
  obtain ⟨R, hRW⟩ := A.X.theorem_7_1_13 x hWo ⟨⟨hxQ, hxO⟩, mem_iInter.2 hxV⟩
  have hRQ : R.U ⊆ Q := fun y hy => (hRW hy).1.1
  have hRV : ∀ i, R.U ⊆ V i := fun i y hy => mem_iInter.1 (hRW hy).2 i
  have hRO : R.U ⊆ O := fun y hy => (hRW hy).1.2
  have hcount : ∀ z ∈ R.U, Λ (f z) = ∑ i with f z = s i z, σ i := fun z hz => by
    have h := hrep.2.2.2 (f z) (by rw [hsec z]; exact hRO hz)
    rw [hsec z] at h
    rw [h, Finset.sum_filter]
  have hI : ∀ i, ∀ z ∈ R.U, f z = s i z → s i x = f x := fun i z hz hfz => by
    by_contra h
    exact hVn i h z (hRV i hz) hfz
  have eM : ∀ i, {z ∈ R.U | f z = s i z} = {z ∈ V i | f z = s i z} ∩ R.U := fun i => by
    ext z
    constructor
    · rintro ⟨hz, he⟩; exact ⟨⟨hRV i hz, he⟩, hz⟩
    · rintro ⟨⟨-, he⟩, hz⟩; exact ⟨hz, he⟩
  have hS : ∀ j : ULift.{u} {i : Fin k // s i x = f x},
      A.X.PObj.IsSmoothSubmanifold {z ∈ R.U | f z = s j.down.1 z} := fun j => by
    rw [eM]; exact (hVt j.down.1 j.down.2).1.1.inter_isOpen R.isOpen_U
  have hT : ∀ j : ULift.{u} {i : Fin k // s i x = f x},
      A.X.PObj.HasTameInducedStructure {z ∈ R.U | f z = s j.down.1 z} := fun j => by
    rw [eM]
    exact (hVt j.down.1 j.down.2).2.1.inter_isOpen (hVt j.down.1 j.down.2).1.1 R.isOpen_U
  have hP : ∀ j : ULift.{u} {i : Fin k // s i x = f x},
      IsProperMap (inclusion (sep_subset R.U fun z => f z = s j.down.1 z)) := fun j => by
    rw [isProperMap_inclusion_iff]
    have hcs : ContinuousOn (s j.down.1) R.U := (hrep.2.1 j.down.1).continuousOn.mono hRO
    have h1 : Continuous fun p : R.U => f p := hfc.comp continuous_subtype_val
    have h2 : Continuous fun p : R.U => s j.down.1 p :=
      hcs.comp_continuous continuous_subtype_val fun p => p.2
    convert isClosed_eq h1 h2 using 1
    ext p
    simp
  let B : A.X.LocalBranchingStructure (fun z => (Λ (f z) : ℚ)) x :=
    EpGroupoid.LocalBranchingStructure.mk R.U R.isOpen_U R.mem_U
      (ULift.{u} {i : Fin k // s i x = f x}) (fun j => {z ∈ R.U | f z = s j.down.1 z})
      (fun j => sep_subset _ _) hS (fun j => ⟨R.mem_U, j.down.2.symm⟩) hP
      (fun j => (σ j.down.1 : ℚ)) (fun j => by exact_mod_cast hrep.1 j.down.1) (by
        intro z hz
        have e0 : ((Λ (f z) : ℚ≥0) : ℚ) = ∑ i, if f z = s i z then (σ i : ℚ) else 0 := by
          rw [hcount z hz, Finset.sum_filter]
          refine (map_sum NNRat.coeHom _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
          split_ifs <;> rfl
        have e1 : (∑ i, if f z = s i z then (σ i : ℚ) else 0) =
            ∑ i with s i x = f x, (if f z = s i z then (σ i : ℚ) else 0) :=
          (Finset.sum_filter_of_ne fun i _ hne => hI i z hz (by
            by_contra h
            exact hne (if_neg h))).symm
        have e2 : (∑ i with s i x = f x, (if f z = s i z then (σ i : ℚ) else 0)) =
            ∑ a : {i // s i x = f x}, (if f z = s a.1 z then (σ a.1 : ℚ) else 0) :=
          Finset.sum_subtype _ (fun i => by simp) _
        have e3 : (∑ a : {i // s i x = f x}, (if f z = s a.1 z then (σ a.1 : ℚ) else 0)) =
            ∑ j : ULift.{u} {i // s i x = f x},
              (if f z = s j.down.1 z then (σ j.down.1 : ℚ) else 0) :=
          (Fintype.sum_equiv Equiv.ulift _ _ fun _ => rfl).symm
        refine e0.trans (e1.trans (e2.trans (e3.trans ?_)))
        simp only [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with h1 h2 h2 <;> first | rfl | exact absurd ⟨hz, h1⟩ h2 | exact absurd h2.2 h1)
  exact ⟨{ toLocalBranchingStructure := B
           rep := R
           U_eq := rfl
           hasPropernessProperty :=
             ⟨R.isOpen_U, hQ.2.of_subset (closure_mono hRQ) isClosed_closure⟩
           hasTameInducedStructure := hT
           dim := fun j => d j.down.1
           isSubmanifoldOfDim := fun j => by
             change A.X.PObj.IsSubmanifoldOfDim {z ∈ R.U | f z = s j.down.1 z} _
             rw [eM]; exact (hVt j.down.1 j.down.2).1.inter_isOpen R.isOpen_U
           O := O
           isOpen_O := hO
           U_subset := hRO
           k := k
           sAll := s
           σAll := σ
           isLocalRep := hrep
           idx := fun j => j.down.1
           idx_injective := fun a b h => ULift.ext _ _ (Subtype.ext h)
           σ_eq := fun _ => rfl
           mem_range := fun j z hz h => ⟨⟨⟨j, hI j z hz h⟩⟩, rfl⟩
           M_eq := fun _ => rfl
           smooth := fun j y hy =>
             ((hVt j.down.1 j.down.2).2.2 y (hRV j.down.1 hy.1) hy.2).1
           tangent_eq := fun j y hy c hc hsub hyc z hz => by
             change chartVec c.isChart ''
               A.X.PObj.submanifoldTangent {z ∈ R.U | f z = s j.down.1 z} y = _
             rw [eM, submanifoldTangent_inter_isOpen R.isOpen_U hy.1]
             exact (((hVt j.down.1 j.down.2).2.2 y (hRV j.down.1 hy.1) hy.2).2
               c hc hsub hyc z hz).1
           onto := fun j y hy c hc hsub hyc z hz =>
             (((hVt j.down.1 j.down.2).2.2 y (hRV j.down.1 hy.1) hy.2).2
               c hc hsub hyc z hz).2 }⟩

end SBLocalization

end Polyfold
