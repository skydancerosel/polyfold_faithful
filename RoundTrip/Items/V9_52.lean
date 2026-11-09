import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_52

/-!
Round trip for V9_52 (Definition 9.5.14, 2021 p. 448, with the paragraph before it; 2017:
Definition 9.17, p. 327): measure zero in `∂S` and `L(∂S)`.

`A` (universes at `0`) is the conjunction of the types of `isMeasureZeroBoundaryAll_of` (the
"well-defined notion": a choice of tame structures with null boundary preimages gives null
boundary preimages for every structure, **given `HasIndependentTangentSums Θ`** (Theorem 9.2.1's
independence of `TΘ`, through which `∂Θ` is defined), for an abstract `SheetNullSets` on the
boundaries) and `orbitSupp_boundaryTheta_subset` (`∂S ⊆ S`); the definitions are vocabulary.

* `A ⇒ B` is not proved.  `B`'s (a) (the preimage of `K ⊆ |∂M_U|` in `M_U` lies in `⋃ ∂Mᵢ`) is
  not a statement of `A`; `B`'s (b) is `isMeasureZeroBoundaryAll_of` for B's concrete notion
  (locally `(n-1)`-dimensional Hausdorff-null), but `A` needs `HasIndependentTangentSums Θ`, which
  `B`'s hypotheses (branched, tame, `n`-dimensional) do not give in the project (Theorem 9.2.1 is
  formalized only under further hypotheses or for `ℝᵐ`), and an abstract null-set system, which
  for B's notion needs the good-sheet property of V9_50 on the boundaries.  With both as
  hypotheses, `A ⇒ B` holds (`A_to_B_of_hyp`): (a) from `HasIndependentTangentSums` through the
  non-item lemmas `boundaryTheta_eq` and `isFunctorial_boundaryTheta` (if `|y| = |w|` with
  `w ∈ ∂Mₖ` then `∂Θ(y) = ∂Θ(w) > 0`, so `y ∈ ∂Mᵢ` for some `i`); (b) from A's
  `isMeasureZeroBoundaryAll_of` with B's suitable structures as project `TameBranchingStructure`s.
* `B ⇒ A` (`B_to_A`) is **vacuous**: `A`'s first conjunct is for an arbitrary `SheetNullSets`
  (under its own hypothesis `HasIndependentTangentSums`), which `B` does not mention, and
  `∂S ⊆ S` is not a statement of `B`; both are re-proved outright (section `ReProof`).
-/

namespace RoundTrip.V9_52
open Polyfold Set MeasureTheory

/-- The project's statements, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.isMeasureZeroBoundaryAll_of.{0} ∧
  type_of% @Polyfold.EpGroupoid.orbitSupp_boundaryTheta_subset.{0}

theorem A_holds : A :=
  ⟨@EpGroupoid.isMeasureZeroBoundaryAll_of, @EpGroupoid.orbitSupp_boundaryTheta_subset⟩

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `Φ(1) = id` on `V` for B's natural action. -/
theorem Φ_one_of {X : EpGroupoid Obj Mor} {x : Obj} {V : Set Obj} {Φ : X.Isotropy x → Obj → Obj}
    {Γ : X.Isotropy x → Obj → Mor} (h : IsNatAction X x V Φ Γ) {y : Obj} (hy : y ∈ V) :
    Φ 1 y = y := by
  obtain ⟨ψ, hψ⟩ := h.diffeo 1
  have hz : ψ y ∈ V := hψ.mapsTo_inv hy
  have h1 : Φ 1 (ψ y) = y := hψ.right_inv y hy
  calc Φ 1 y = Φ 1 (Φ 1 (ψ y)) := by rw [h1]
    _ = Φ (1 * 1) (ψ y) := (h.hom 1 1 _ hz).symm
    _ = y := by rw [mul_one, h1]

/-- B's natural action on a **connected** `V` is a project `NaturalRep` (as in V7_66). -/
def toNaturalRep {X : EpGroupoid Obj Mor} {x : Obj} {V : Set Obj}
    {Φ : X.Isotropy x → Obj → Obj} {Γ : X.Isotropy x → Obj → Mor} (h : IsNatAction X x V Φ Γ)
    (hc : IsConnected V) : X.NaturalRep x where
  U := V
  isOpen_U := h.isOpen
  isConnected_U := hc
  mem_U := h.mem
  Φ := Φ
  Γ := Γ
  isScDiffeoOn_Φ g :=
    { isScSmoothOn := (h.diffeo g).choose_spec.isScSmoothOn
      isScSmoothOn_inv := (h.diffeo g⁻¹).choose_spec.isScSmoothOn
      mapsTo := (h.diffeo g).choose_spec.mapsTo
      mapsTo_inv := (h.diffeo g⁻¹).choose_spec.mapsTo
      left_inv := fun y hy => by rw [← h.hom g⁻¹ g y hy, inv_mul_cancel, Φ_one_of h hy]
      right_inv := fun y hy => by rw [← h.hom g g⁻¹ y hy, mul_inv_cancel, Φ_one_of h hy] }
  Φ_mul := h.hom
  isScSmoothOn_Γ := h.smooth
  Γ_self := h.Γ_x
  src_Γ g y hy := (h.src_tgt g y hy).1
  tgt_Γ g y hy := (h.src_tgt g y hy).2
  existsUnique_Γ := h.unique

theorem isLocNullB_mono {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    {P : MPolyfold Z} {d : ℕ} {C C' : Set Z} (h : IsLocNullB P d C') (hC : C ⊆ C') :
    IsLocNullB P d C := by
  intro z hz
  obtain ⟨V, hV, hzV, hnull⟩ := h z (hC hz)
  exact ⟨V, hV, hzV, fun φ hφ => measure_mono_null
    (image_mono (inter_subset_inter_left _ (inter_subset_inter_left _ hC))) (hnull φ hφ)⟩

/-- The sets on which B's `d`-dimensional null sets behave as a `SheetNullSets` asks (V9_50). -/
def GoodSheets (X : EpGroupoid Obj Mor) (d : ℕ) : Set (Set Obj) :=
  {N | (∀ C : ℕ → Set Obj, (∀ k, IsLocNullB X.PObj d (C k ∩ N)) →
      IsLocNullB X.PObj d ((⋃ k, C k) ∩ N)) ∧ (N.Nonempty → ¬ IsLocNullB X.PObj d N)}

/-- B's `d`-dimensional null sets as a `SheetNullSets` on the good sets (V9_50). -/
def hausdorffNull (X : EpGroupoid Obj Mor) (d : ℕ) : SheetNullSets (GoodSheets X d) where
  IsNull N C := N ∈ GoodSheets X d → IsLocNullB X.PObj d (C ∩ N)
  isNull_empty N _ := fun z hz => (notMem_empty z hz.1).elim
  isNull_mono h hC hN := isLocNullB_mono (h hN) (inter_subset_inter_left _ hC)
  isNull_iUnion h hN := hN.1 _ fun k => h k hN
  isNull_of_local N hN C h _ := by
    intro z hz
    obtain ⟨V, hVo, hzV, hV⟩ := h z hz.1
    obtain ⟨V', hV'o, hzV', hV'⟩ := hV hN z ⟨⟨hz.1, hzV⟩, hz.2⟩
    refine ⟨V ∩ V', hVo.inter hV'o, ⟨hzV, hzV'⟩, fun φ hφ => measure_mono_null
      (image_mono ?_) (hV' φ hφ)⟩
    rintro w ⟨⟨⟨hwC, hwN⟩, hwV, hwV'⟩, hws⟩
    exact ⟨⟨⟨⟨hwC, hwV⟩, hwN⟩, hwV'⟩, hws⟩
  isNull_transfer N hN N' _ C hC h _ := by
    have h1 : C ∩ N' = C := inter_eq_left.2 fun w hw => (hC hw).2
    have h2 : C ∩ N = C := inter_eq_left.2 fun w hw => (hC hw).1
    have h3 := h hN
    rw [h2] at h3
    rw [h1]
    exact h3
  not_isNull_self N hN hne h := hN.2 hne (isLocNullB_mono (h hN) fun w hw => ⟨hw, hw⟩)

end

/-- **`A ⇒ B` under two hypotheses**: Theorem 9.2.1's independence of `TΘ`
(`HasIndependentTangentSums`) and the good-sheet property of the boundaries `∂Mᵢ` of suitable
structures for the `(n-1)`-dimensional null sets. -/
theorem A_to_B_of_hyp (hA : A)
    (hind : ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (n : ℕ),
      X.IsBranchedEpSubgroupoid Θ → IsTameB X Θ → X.IsNDimensional Θ n →
      X.HasIndependentTangentSums Θ)
    (hgood : ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (n : ℕ),
      X.IsBranchedEpSubgroupoid Θ → IsTameB X Θ → X.IsNDimensional Θ n →
      ∀ x ∈ EpGroupoid.supp (X.boundaryTheta Θ), ∀ B : X.LocalBranchingStructure Θ x,
        IsSuitableB X B → ∀ i, X.PObj.submanifoldBoundary (B.M i) ∈ GoodSheets X (n - 1)) :
    B := by
  classical
  intro Obj Mor _ _ _ _ _ _ X Θ n hΘ hT hD
  have hi := hind Obj Mor X Θ n hΘ hT hD
  have hg := hgood Obj Mor X Θ n hΘ hT hD
  refine ⟨fun x _ Bx _ K hK y hy hyK => ?_, fun K _ hK x' hx' B' hB' j => ?_⟩
  · -- (a): the preimages lie in the `∂Mᵢ`
    obtain ⟨w, hw, hwy⟩ := hK hyK
    obtain ⟨k, hk⟩ := mem_iUnion.1 hw
    have hwM : w ∈ Bx.M k := by
      obtain ⟨-, h, -⟩ := hk
      exact h
    have hwU : w ∈ Bx.U := Bx.subset_U k hwM
    obtain ⟨i0, hyi0⟩ := mem_iUnion.1 hy
    have hyU : y ∈ Bx.U := Bx.subset_U i0 hyi0
    have hwpos : 0 < X.boundaryTheta Θ w := by
      rw [X.boundaryTheta_eq hi Bx hwU]
      exact Finset.sum_pos' (fun i _ => (Bx.σ_pos i).le) ⟨k, by simp [hk], Bx.σ_pos k⟩
    have hF := X.isFunctorial_boundaryTheta hΘ hi
    have hyw : X.boundaryTheta Θ y = X.boundaryTheta Θ w := by
      obtain ⟨φ, hs, ht⟩ := (X.π_eq_π_iff).1 hwy
      have h1 := hF φ
      rw [hs, ht] at h1
      exact h1.symm
    have hypos : 0 < X.boundaryTheta Θ y := hyw ▸ hwpos
    rw [X.boundaryTheta_eq hi Bx hyU] at hypos
    exact EpGroupoid.exists_mem_of_sum_pos hypos
  · -- (b): through A's `isMeasureZeroBoundaryAll_of`
    have hmz : X.IsMeasureZeroBoundary (hausdorffNull X (n - 1)) Θ K := fun x hx => by
      obtain ⟨Bx, hBx, hnull⟩ := hK x hx
      have hBx' := hBx
      obtain ⟨⟨Φ, Γ, hN⟩, hc, hp, ht⟩ := hBx'
      let TB : X.TameBranchingStructure Θ x :=
        { toLocalBranchingStructure := Bx
          rep := toNaturalRep hN hc
          U_eq := rfl
          hasPropernessProperty := hp
          hasTameInducedStructure := ht }
      exact ⟨TB, hg x hx Bx hBx, fun i _ => isLocNullB_mono (hnull i) inter_subset_left⟩
    have hall := hA.1 (hausdorffNull X (n - 1)) hi hmz
    exact isLocNullB_mono (hall x' hx' B' (hg x' hx' B' hB') j (hg x' hx' B' hB' j))
      fun w hw => ⟨hw, hw.1⟩

/-! ### `B ⇒ A`, vacuous: `A` re-proved outright -/

namespace ReProof
open EpGroupoid

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {S' : Set (Set Obj)} (G' : SheetNullSets S')

theorem all_of' (hind : X.HasIndependentTangentSums Θ) {K : Set X.OrbitSpace}
    (h : X.IsMeasureZeroBoundary G' Θ K) : X.IsMeasureZeroBoundaryAll G' Θ K := by
  classical
  intro x' _ B' hB'S j
  have hpos : ∀ {w}, w ∈ X.PObj.submanifoldBoundary (B'.M j) → w ∈ supp (X.boundaryTheta Θ) :=
    fun {w} hw => by
      have hwM : w ∈ B'.M j := by obtain ⟨-, hw', -⟩ := hw; exact hw'
      change 0 < X.boundaryTheta Θ w
      rw [X.boundaryTheta_eq hind B' (B'.subset_U j hwM)]
      exact Finset.sum_pos' (fun i _ => (B'.σ_pos i).le) ⟨j, by simp [hw], B'.σ_pos j⟩
  refine G'.isNull_of_cover (hB'S j) inter_subset_left fun z hz => ?_
  obtain ⟨B, hBS, hBnull⟩ := h z (hpos hz.1)
  refine ⟨B.U, B.isOpen_U, B.mem_U, B.ι, inferInstance,
    fun i => X.PObj.submanifoldBoundary (B.M i), hBS, fun w hw => ?_,
    fun i => G'.isNull_mono (hBnull i) fun w hw => ⟨hw.2, hw.1.2⟩⟩
  have h1 := hpos hw.1.1
  change 0 < X.boundaryTheta Θ w at h1
  rw [X.boundaryTheta_eq hind B.toLocalBranchingStructure hw.2] at h1
  exact mem_iUnion.2 (exists_mem_of_sum_pos h1)

end

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

theorem subset' : X.orbitSupp (X.boundaryTheta Θ) ⊆ X.orbitSupp Θ := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  by_contra h
  exact lt_irrefl (0 : ℚ) (by
    have := X.boundaryTheta_eq_zero_of_not_mem_supp (Θ := Θ) h
    change 0 < X.boundaryTheta Θ y at hy
    rwa [this] at hy)

end

end ReProof

/-- `B ⇒ A`, vacuous: `A` re-proved outright. -/
theorem B_to_A : B → A := fun _ => ⟨@ReProof.all_of', @ReProof.subset'⟩

#rt_check RoundTrip.V9_52.B_to_A [Polyfold.EpGroupoid.isMeasureZeroBoundaryAll_of,
  Polyfold.EpGroupoid.orbitSupp_boundaryTheta_subset]
#rt_overlap RoundTrip.V9_52.B_to_A [Polyfold.EpGroupoid.isMeasureZeroBoundaryAll_of,
  Polyfold.EpGroupoid.orbitSupp_boundaryTheta_subset]
#print axioms RoundTrip.V9_52.B_to_A

#rt_check RoundTrip.V9_52.A_to_B_of_hyp [Polyfold.EpGroupoid.isMeasureZeroBoundaryAll_of,
  Polyfold.EpGroupoid.orbitSupp_boundaryTheta_subset]
#rt_overlap RoundTrip.V9_52.A_to_B_of_hyp [Polyfold.EpGroupoid.isMeasureZeroBoundaryAll_of,
  Polyfold.EpGroupoid.orbitSupp_boundaryTheta_subset]
#print axioms RoundTrip.V9_52.A_to_B_of_hyp

end RoundTrip.V9_52
