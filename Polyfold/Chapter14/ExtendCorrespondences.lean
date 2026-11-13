import Polyfold.Chapter14.GoodStructured

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.3, pp. 649–653:
**Lemma 14.3.1**, **Definition 14.3.2**, **Lemma 14.3.3**, **Proposition 14.3.4**,
**Remark 14.3.5** (2017: Lemma 14.2, the text before Lemma 14.3, Lemma 14.3,
Proposition 14.3, Remark 14.4).

# Extension of the correspondences `τ⁰` off the boundary

## The text, paraphrased

Fix a representative `(Λ, 𝒰⁰, S⁰, τ⁰)` of a structured lift with (P1)–(P4) (Proposition 14.2.3)
and open neighbourhoods `Ũ'(x) ⊆ X`, `x ∈ ∂X`, with (P5): (i) the natural `G_x`-action and the
properness property, (ii) `Ũ'(x) ∩ ∂X = U⁰(x)`.  Write `Ũ'(x, x')` for the morphisms from
`Ũ'(x)` to `Ũ'(x')` and `U⁰(x, x') = Ũ'(x, x') ∩ ∂X`.
(Lemma 14.3.1) There are open `Õ_{x,x',[d]} ⊇ τ⁰⁻¹([d])` with (1) `Õ_{x,x',[d]} ⊆ Ũ'(x, x')`,
(2) disjoint closures for `[d] ≠ [d']`, (3) `h ∗ Õ_{[d]} ∗ g = Õ_{h∗[d]∗g}`, (4) the union
`Õ_{x,x'}` meets `∂X` in `U⁰(x, x')`; also `Õ_{[d]} ∩ ∂X = τ⁰⁻¹([d])` (14.20).
(Definition 14.3.2) `Ô_{x,x'}` is the union of the components of `Õ_{x,x'}` meeting `∂X`; for
`φ ∈ Ô_{x,x'}` put `[d]_φ = τ⁰(ψ)` for `ψ` in the component of `φ` and in `∂X`.
(Lemma 14.3.3) `[d]_φ` is well defined.
(Proposition 14.3.4) `Ô_{x,x'}` is open, (1) `U⁰(x, x') ⊆ Ô ⊆ Ũ'(x, x')` and
`Ô ∩ ∂X = U⁰(x, x')`, (2) `Ô` is invariant under the bi-action, (3) `τ⁰` has a unique locally
constant extension `τ̂ : Ô → J(x, x')`, equivariant under the bi-action, with
`τ̂_{x,x}(Γ(g, y)) = τ⁰_{x,x}(Γ(g, z))`; `Ô = ⋃ Ô_{[d]}` with `Ô_{[d]} ∩ ∂X = τ⁰⁻¹([d])`.
(Remark 14.3.5) `Ô` is not of the form `Ũ(x, x')`: a comment.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `boundaryMor A`: the morphisms of `∂X` (source and target in `∂X`).
* `P5Nbhds T`: the neighbourhoods `Ũ'(x)` of (P5), with the natural action of `𝒰⁰` (same
  representation `rep`); the witness `P5Nbhds.ofGood` (the `V(x)` of the good system itself).
* `CorrExtension T P`: open sets `Õ_{x,x',[d]}` for all `x, x' ∈ ∂X` and `[d] ∈ J(x, x')` with
  the properties of Lemma 14.3.1, plus the symmetry `φ ∈ Õ_{x,x',[d]} ↔ φ⁻¹ ∈ Õ_{x',x,[d]♯}`
  (not in the text; it gives the property (a) of Definition 14.1.7 for `τ̂`, which §14.4 uses).
* **Lemma 14.3.1**: `lemma_14_3_1` (a `CorrExtension` exists, given (P4)) and the printed form
  `lemma_14_3_1_book`.
* **Definition 14.3.2**: `CorrExtension.Ot` (`Õ_{x,x'}`), `CorrExtension.Ohat` (`Ô_{x,x'}`),
  `CorrExtension.tauHat` (`τ̂`, `φ ↦ [d]_φ`), `CorrExtension.OhatD` (`Ô_{x,x',[d]}`).
* **Lemma 14.3.3**: `lemma_14_3_3` and `tauHat_eq_tau_of_mem_component` (`τ̂(φ) = τ⁰(ψ)` for every
  `ψ ∈ ∂X` in the component of `φ`: `τ̂` is the text's `[d]_φ`).
* **Proposition 14.3.4**: `proposition_14_3_4` (the printed statement), with the API lemmas
  `isOpen_Ohat`, `mor_subset_Ohat`, `Ohat_subset_mor`, `Ohat_inter_boundaryMor`,
  `biact_mem_Ohat`, `tauHat_locallyConstant`, `tauHat_eq_tau`, `tauHat_unique`, `tauHat_biact`,
  `tauHat_Γ`, `OhatD_inter_boundaryMor`; extras `finite_tauHat`, `inv_mem_Ohat`, `tauHat_inv`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

/-! ### General topology -/

namespace P3W4S3

/-- In a normal space, finitely many pairwise disjoint closed sets have open neighbourhoods with
pairwise disjoint closures (the sets outside the finite index set `F` are empty). -/
theorem exists_open_disjoint_closure {α ι : Type*} [TopologicalSpace α] [NormalSpace α]
    {F : Set ι} (hF : F.Finite) {C : ι → Set α} (hC : ∀ i, IsClosed (C i))
    (hd : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (hCF : ∀ i ∉ F, C i = ∅) :
    ∃ W : ι → Set α, (∀ i, IsOpen (W i)) ∧ (∀ i, C i ⊆ W i) ∧
      ∀ i j, i ≠ j → Disjoint (closure (W i)) (closure (W j)) := by
  classical
  have key : ∀ i j, ∃ P Q : Set α, IsOpen P ∧ IsOpen Q ∧ C i ⊆ P ∧ C j ⊆ Q ∧
      (i ≠ j → Disjoint (closure P) (closure Q)) := by
    intro i j
    by_cases hij : i = j
    · exact ⟨univ, univ, isOpen_univ, isOpen_univ, subset_univ _, subset_univ _,
        fun h => (h hij).elim⟩
    obtain ⟨P, hPo, hCP, hPcl⟩ := normal_exists_closure_subset (hC i) (hC j).isOpen_compl
      (hd i j hij).le_compl_right
    obtain ⟨Q, hQo, hCQ, hQcl⟩ := normal_exists_closure_subset (hC j) isClosed_closure.isOpen_compl
      (subset_compl_iff_disjoint_right.1 hPcl).symm.le_compl_right
    exact ⟨P, Q, hPo, hQo, hCP, hCQ, fun _ => (subset_compl_iff_disjoint_right.1 hQcl).symm⟩
  choose P Q hPo hQo hCP hCQ hPQ using key
  refine ⟨fun i => if i ∈ F then ⋂ j ∈ F, (P i j ∩ Q j i) else ∅, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs
    · exact hF.isOpen_biInter fun j _ => (hPo i j).inter (hQo j i)
    · exact isOpen_empty
  · intro i
    dsimp only
    split_ifs with hi
    · exact subset_iInter₂ fun j _ => subset_inter (hCP i j) (hCQ j i)
    · rw [hCF i hi]
  · intro i j hij
    dsimp only
    split_ifs with hi hj hj
    · refine (hPQ i j hij).mono (closure_mono ?_) (closure_mono ?_)
      · exact (biInter_subset_of_mem hj).trans inter_subset_left
      · exact (biInter_subset_of_mem hi).trans inter_subset_right
    all_goals simp

/-- A function that is locally constant at every point of `S` is constant on the connected
components of `S`. -/
theorem eq_of_mem_connectedComponentIn {α β : Type*} [TopologicalSpace α] {S : Set α}
    {f : α → β} (hf : ∀ φ ∈ S, ∀ᶠ ψ in 𝓝 φ, f ψ = f φ) {φ ψ : α}
    (hψ : ψ ∈ connectedComponentIn S φ) : f ψ = f φ := by
  let _ : TopologicalSpace β := ⊥
  have : DiscreteTopology β := ⟨rfl⟩
  have hφS : φ ∈ S := by
    by_contra h
    rw [connectedComponentIn_eq_empty h] at hψ
    exact hψ
  have hc : ContinuousOn f S := fun χ hχ =>
    (continuousAt_const.congr
      (by filter_upwards [hf χ hχ] with ξ h; exact h.symm)).continuousWithinAt
  exact isPreconnected_connectedComponentIn.constant
    (hc.mono (connectedComponentIn_subset _ _)) hψ (mem_connectedComponentIn hφS)

/-- The component of a point of `O i` in a union of pairwise disjoint open sets `O j` lies in
`O i`. -/
theorem connectedComponentIn_iUnion_subset {α ι : Type*} [TopologicalSpace α] {O : ι → Set α}
    (hO : ∀ i, IsOpen (O i)) (hd : ∀ i j, i ≠ j → Disjoint (O i) (O j)) {i : ι} {φ : α}
    (hφ : φ ∈ O i) : connectedComponentIn (⋃ j, O j) φ ⊆ O i := by
  have hφU : φ ∈ ⋃ j, O j := mem_iUnion.2 ⟨i, hφ⟩
  refine isPreconnected_connectedComponentIn.subset_left_of_subset_union (hO i)
    (isOpen_iUnion fun j => isOpen_iUnion fun _ => hO j)
    (disjoint_iUnion₂_right.2 fun j hj => hd i j (Ne.symm hj)) ?_
    ⟨φ, mem_connectedComponentIn hφU, hφ⟩
  intro ψ hψ
  obtain ⟨j, hj⟩ := mem_iUnion.1 (connectedComponentIn_subset _ _ hψ)
  by_cases hji : j = i
  · exact Or.inl (hji ▸ hj)
  · exact Or.inr (mem_iUnion₂.2 ⟨j, hji, hj⟩)

end P3W4S3

open P3W4S3

/-! ### Two identities for the bi-actions -/

namespace SBLocalization.IndexCorr

/-- `(g' ∗ [d] ∗ g)♯ = g⁻¹ ∗ [d]♯ ∗ g'⁻¹`. -/
theorem swap_biact_p3w4 {α β : Type u} {G G' : Type*} [Group G] [Group G'] [MulAction G α]
    [MulAction G' β] (g' : G') (τ : IndexCorr α β) (g : G) :
    (biact g' τ g).swap = biact g⁻¹ τ.swap g'⁻¹ := by
  refine ind (fun d => mk_eq_mk.2 ⟨_root_.Equiv.refl _, fun k => ⟨?_, ?_⟩⟩) τ
  · change g'⁻¹⁻¹ • d.b k = g' • d.b k
    rw [inv_inv]
  · rfl

end SBLocalization.IndexCorr

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- `(g' ∗ φ ∗ g)⁻¹ = g⁻¹ ∗ φ⁻¹ ∗ g'⁻¹` (Definition 13.1.5). -/
theorem inv_biact_p3w4 {x x' : Obj} {N : X.NatNbhd x} {N' : X.NatNbhd x'} {φ : Mor}
    (hφ : φ ∈ X.morBetween N.U N'.U) (h : X.Isotropy x') (g : X.Isotropy x) :
    X.inv (biact N N' h φ g) = biact N' N g⁻¹ (X.inv φ) h⁻¹ := by
  have hy : N.rep.Φ g⁻¹ (X.src φ) ∈ N.U := N.Φ_mem g⁻¹ hφ.1
  have hc1 : X.src φ = X.tgt (N.rep.Γ g (N.rep.Φ g⁻¹ (X.src φ))) := by
    rw [N.tgt_Γ g hy, N.Φ_Φ_inv g hφ.1]
  have hc2 : X.src (N'.rep.Γ h (X.tgt φ)) =
      X.tgt (X.comp φ (N.rep.Γ g (N.rep.Φ g⁻¹ (X.src φ)))) := by
    rw [N'.src_Γ h hφ.2, X.tgt_comp _ _ hc1]
  have hinvb : X.inv (N.rep.Γ g (N.rep.Φ g⁻¹ (X.src φ))) = N.rep.Γ g⁻¹ (X.src φ) := by
    rw [← N.Γ_inv g hy, N.Φ_Φ_inv g hφ.1]
  have hinva : X.inv (N'.rep.Γ h (X.tgt φ)) = N'.rep.Γ h⁻¹ (N'.rep.Φ h (X.tgt φ)) :=
    (N'.Γ_inv h hφ.2).symm
  have hd1 : X.src (N.rep.Γ g⁻¹ (X.src φ)) = X.tgt (X.inv φ) := by
    rw [N.src_Γ g⁻¹ hφ.1, X.tgt_inv]
  have hd2 : X.src (X.inv φ) = X.tgt (N'.rep.Γ h⁻¹ (N'.rep.Φ h (X.tgt φ))) := by
    rw [X.src_inv, N'.tgt_Γ h⁻¹ (N'.Φ_mem h hφ.2), N'.Φ_inv_Φ h hφ.2]
  have hL : X.inv (biact N N' h φ g) = X.comp (X.comp (N.rep.Γ g⁻¹ (X.src φ)) (X.inv φ))
      (N'.rep.Γ h⁻¹ (N'.rep.Φ h (X.tgt φ))) := by
    rw [biact, GroupoidStr.inv_comp_rev (G := X.toGroupoidStr) hc2,
      GroupoidStr.inv_comp_rev (G := X.toGroupoidStr) hc1]
    rw [hinvb, hinva]
  rw [hL, X.comp_assoc _ _ _ hd1 hd2, biact, X.tgt_inv, X.src_inv, inv_inv]

/-- On `𝒰(x, x')` the natural bi-action depends only on the representations. -/
theorem biact_congr_rep_p3w4 {x x' : Obj} {N₁ N₂ : X.NatNbhd x} {N₁' N₂' : X.NatNbhd x'}
    (h : N₁.rep = N₂.rep) (h' : N₁'.rep = N₂'.rep) (g' : X.Isotropy x') (φ : Mor)
    (g : X.Isotropy x) : biact N₁ N₁' g' φ g = biact N₂ N₂' g' φ g := by
  simp only [biact, h, h']

/-! ### Sheets of the natural representation -/

/-- **The sheet `Γ(g, ·)` is open**: if `φ₀ = Γ(g, s(φ₀))`, then `φ = Γ(g, s(φ))` for all `φ`
near `φ₀` (`s` is a local homeomorphism). -/
theorem eventually_Γ_src_eq_p3w4 {x : Obj} (R : X.NaturalRep x) (g : X.Isotropy x) {φ₀ : Mor}
    (hs : X.src φ₀ ∈ R.U) (h0 : R.Γ g (X.src φ₀) = φ₀) : ∀ᶠ φ in 𝓝 φ₀, R.Γ g (X.src φ) = φ := by
  obtain ⟨W, hWo, hφW, hinj⟩ := X.isLocalScDiffeo_src.isLocallyInjective φ₀
  have hk : ContinuousAt (fun φ => R.Γ g (X.src φ)) φ₀ :=
    ((R.continuousOn_Γ g).continuousAt (R.isOpen_U.mem_nhds hs)).comp
      X.continuous_src.continuousAt
  have hkW : (fun φ => R.Γ g (X.src φ)) ⁻¹' W ∈ 𝓝 φ₀ :=
    hk.preimage_mem_nhds (by rw [h0]; exact hWo.mem_nhds hφW)
  filter_upwards [hWo.mem_nhds hφW, hkW,
    X.continuous_src.continuousAt.preimage_mem_nhds (R.isOpen_U.mem_nhds hs)]
    with φ hφ hk' hsU
  exact hinj hk' hφ (R.src_Γ g _ hsU)

open scoped Classical in
/-- The label `g` of the sheet `Γ(g, ·)` through a morphism between points of `R.U`. -/
def sheetLabel_p3w4 {x : Obj} (R : X.NaturalRep x) (φ : Mor) : X.Isotropy x :=
  if h : ∃ g, R.Γ g (X.src φ) = φ then h.choose else 1

theorem Γ_sheetLabel_p3w4 {x : Obj} (R : X.NaturalRep x) {φ : Mor}
    (hφ : φ ∈ X.morBetween R.U R.U) : R.Γ (sheetLabel_p3w4 R φ) (X.src φ) = φ := by
  have h : ∃ g, R.Γ g (X.src φ) = φ := (R.existsUnique_Γ φ hφ.1 hφ.2).exists
  rw [sheetLabel_p3w4, dif_pos h]
  exact h.choose_spec

theorem sheetLabel_eq_p3w4 {x : Obj} (R : X.NaturalRep x) {φ : Mor}
    (hφ : φ ∈ X.morBetween R.U R.U) {g : X.Isotropy x} (hg : R.Γ g (X.src φ) = φ) :
    sheetLabel_p3w4 R φ = g :=
  (R.Γ_inj hφ.1).1 ((Γ_sheetLabel_p3w4 R hφ).trans hg.symm)

/-- The sheet label is locally constant on the morphisms between points of `R.U`. -/
theorem sheetLabel_locallyConstant_p3w4 {x : Obj} (R : X.NaturalRep x) {φ : Mor}
    (hφ : φ ∈ X.morBetween R.U R.U) :
    ∀ᶠ ψ in 𝓝 φ, sheetLabel_p3w4 R ψ = sheetLabel_p3w4 R φ := by
  filter_upwards [eventually_Γ_src_eq_p3w4 R _ hφ.1 (Γ_sheetLabel_p3w4 R hφ),
    (isOpen_morBetween R.isOpen_U R.isOpen_U).mem_nhds hφ] with ψ hψ hψM
  exact sheetLabel_eq_p3w4 R hψM hψ

end EpGroupoid

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-! ### Boundary morphisms and the neighbourhoods of (P5) -/

/-- The morphisms of `∂X`: source and target in `∂X`. -/
def boundaryMor (A : SEP.{u}) : Set A.Mor :=
  A.X.morBetween A.X.PObj.boundary A.X.PObj.boundary

theorem _root_.Polyfold.EpGroupoid.BoundaryGoodSystem.mor_subset_boundaryMor_p3w4
    (𝒰 : A.X.BoundaryGoodSystem)
    (x x' : A.X.PObj.boundary) : 𝒰.mor x x' ⊆ boundaryMor A := fun _ hφ =>
  ⟨𝒰.U_subset_boundary x hφ.1, 𝒰.U_subset_boundary x' hφ.2⟩

/-- **(P5)**, p. 649: open neighbourhoods `Ũ'(x)` of the `x ∈ ∂X` in `X` with (i) the natural
`G_x`-action (that of the good system `𝒰⁰`: the same representation) and the properness property
(`t : s⁻¹(cl_X Ũ'(x)) → X` proper), (ii) `Ũ'(x) ∩ ∂X = U⁰(x)`. -/
structure P5Nbhds (T : BoundaryStructuredTuple A) where
  /-- `Ũ'(x)` with its natural action. -/
  nbhd : ∀ x : A.X.PObj.boundary, A.X.NatNbhd x
  rep_eq : ∀ x, (nbhd x).rep = (T.dec.𝒰.nbhd x).rep
  /-- (ii) -/
  inter_boundary : ∀ x, (nbhd x).U ∩ A.X.PObj.boundary = T.dec.𝒰.U x
  /-- (i) -/
  isProperSubset_closure : ∀ x, A.X.IsProperSubset (closure (nbhd x).U)

namespace P5Nbhds

variable {T : BoundaryStructuredTuple A} (P : P5Nbhds T)

/-- **(P5) is satisfiable**: the open sets `V(x)` of the good system, with `V(x) ∩ ∂X = U⁰(x)`. -/
def ofGood (T : BoundaryStructuredTuple A) : P5Nbhds T :=
  ⟨T.dec.𝒰.nbhd, fun _ => rfl, fun _ => rfl, fun x => (T.dec.𝒰.isGood x).isProperSubset_closure⟩

/-- `Ũ'(x, x')` (14.19). -/
def mor (x x' : A.X.PObj.boundary) : Set A.Mor := A.X.morBetween (P.nbhd x).U (P.nbhd x').U

theorem isOpen_mor (x x' : A.X.PObj.boundary) : IsOpen (P.mor x x') :=
  isOpen_morBetween (P.nbhd x).isOpen_U (P.nbhd x').isOpen_U

/-- The natural bi-action on `Ũ'(x, x')` (Definition 13.1.5). -/
def biact (x x' : A.X.PObj.boundary) (h : A.X.Isotropy x') (φ : A.Mor) (g : A.X.Isotropy x) :
    A.Mor :=
  EpGroupoid.biact (P.nbhd x) (P.nbhd x') h φ g

theorem biact_eq (x x' : A.X.PObj.boundary) (h : A.X.Isotropy x') (φ : A.Mor)
    (g : A.X.Isotropy x) :
    P.biact x x' h φ g = EpGroupoid.biact (T.dec.𝒰.nbhd x) (T.dec.𝒰.nbhd x') h φ g :=
  biact_congr_rep_p3w4 (P.rep_eq x) (P.rep_eq x') h φ g

theorem biact_mem {x x' : A.X.PObj.boundary} {φ : A.Mor} (hφ : φ ∈ P.mor x x')
    (h : A.X.Isotropy x') (g : A.X.Isotropy x) : P.biact x x' h φ g ∈ P.mor x x' :=
  EpGroupoid.biact_mem hφ h g

/-- `Ũ'(x, x') ∩ ∂X = U⁰(x, x')`. -/
theorem mor_inter_boundaryMor (x x' : A.X.PObj.boundary) :
    P.mor x x' ∩ boundaryMor A = T.dec.𝒰.mor x x' := by
  rw [show T.dec.𝒰.mor x x' = A.X.morBetween (T.dec.𝒰.U x) (T.dec.𝒰.U x') from rfl,
    ← P.inter_boundary x, ← P.inter_boundary x']
  ext φ
  simp only [mem_inter_iff, mor, boundaryMor, EpGroupoid.morBetween, mem_ofPred_eq]
  tauto

theorem mor_subset (x x' : A.X.PObj.boundary) : T.dec.𝒰.mor x x' ⊆ P.mor x x' := by
  rw [← P.mor_inter_boundaryMor]
  exact inter_subset_left

end P5Nbhds

/-- The bi-action of `𝒰⁰` preserves `U⁰(x, x')`. -/
theorem _root_.Polyfold.EpGroupoid.BoundaryGoodSystem.biact_mem_mor_p3w4
    (𝒰 : A.X.BoundaryGoodSystem)
    {x x' : A.X.PObj.boundary} {φ : A.Mor} (hφ : φ ∈ 𝒰.mor x x') (h : A.X.Isotropy x')
    (g : A.X.Isotropy x) : EpGroupoid.biact (𝒰.nbhd x) (𝒰.nbhd x') h φ g ∈ 𝒰.mor x x' := by
  have hφ' := 𝒰.mor_subset x x' hφ
  refine ⟨?_, ?_⟩
  · rw [EpGroupoid.src_biact hφ']
    exact NatNbhd.mapsTo_Φ_bdry _ g⁻¹ hφ.1
  · rw [EpGroupoid.tgt_biact hφ']
    exact NatNbhd.mapsTo_Φ_bdry _ h hφ.2

/-- Inversion maps `U⁰(x, x')` to `U⁰(x', x)`. -/
theorem _root_.Polyfold.EpGroupoid.BoundaryGoodSystem.inv_mem_mor_p3w4
    (𝒰 : A.X.BoundaryGoodSystem)
    {x x' : A.X.PObj.boundary} {φ : A.Mor} (hφ : φ ∈ 𝒰.mor x x') : A.X.inv φ ∈ 𝒰.mor x' x :=
  ⟨by rw [A.X.src_inv]; exact hφ.2, by rw [A.X.tgt_inv]; exact hφ.1⟩

/-! ### Lemma 14.3.1 -/

/-- Open neighbourhoods `Õ'_{x,x',[d]} ⊇ τ⁰⁻¹([d])` inside `Ũ'(x, x')` with pairwise disjoint
closures (the first step of the proof of Lemma 14.3.1). -/
structure CorrPre (T : BoundaryStructuredTuple A) (P : P5Nbhds T) where
  /-- The sets `Õ_{x,x',[d]}`. -/
  O : ∀ x x' : A.X.PObj.boundary, IndexCorr (T.dec.S x).I (T.dec.S x').I → Set A.Mor
  isOpen : ∀ x x' d, IsOpen (O x x' d)
  fiber_subset : ∀ x x' d, T.tau.τ x x' ⁻¹' {d} ∩ T.dec.𝒰.mor x x' ⊆ O x x' d
  /-- (1) -/
  subset_mor : ∀ x x' d, O x x' d ⊆ P.mor x x'
  /-- (2) -/
  disjoint_closure : ∀ x x' d d', d ≠ d' → Disjoint (closure (O x x' d)) (closure (O x x' d'))

/-- **The data of Lemma 14.3.1**: open `Õ_{x,x',[d]} ⊇ τ⁰⁻¹([d])` with (1) `Õ ⊆ Ũ'(x, x')`,
(2) pairwise disjoint closures, (3) `h ∗ Õ_{[d]} ∗ g = Õ_{h∗[d]∗g}` (in the form
`h ∗ φ ∗ g ∈ Õ_{h∗[d]∗g} ↔ φ ∈ Õ_{[d]}` on `Ũ'(x, x')`), and, not in the text, the symmetry
`φ⁻¹ ∈ Õ_{x',x,[d]♯} ↔ φ ∈ Õ_{x,x',[d]}`.  (4) and (14.20) are `iUnion_inter_boundaryMor` and
`inter_boundaryMor`. -/
structure CorrExtension (T : BoundaryStructuredTuple A) (P : P5Nbhds T) extends CorrPre T P where
  /-- (3) -/
  biact_mem_iff : ∀ (x x' : A.X.PObj.boundary) d (h : A.X.Isotropy x') (g : A.X.Isotropy x),
    ∀ φ ∈ P.mor x x',
    P.biact x x' h φ g ∈ O x x' (IndexCorr.biact h d g) ↔ φ ∈ O x x' d
  /-- the symmetry (not in the text) -/
  inv_mem_iff : ∀ (x x' : A.X.PObj.boundary) d φ, A.X.inv φ ∈ O x' x d.swap ↔ φ ∈ O x x' d

namespace CorrPre

variable {T : BoundaryStructuredTuple A} {P : P5Nbhds T}

/-- Step 1 of the proof of Lemma 14.3.1: the sets `τ⁰⁻¹([d])` have pairwise disjoint closures
(P4), finitely many are nonempty, so they have open neighbourhoods with disjoint closures. -/
theorem exists_of_hasP4 (hT : T.HasP4) (P : P5Nbhds T) : Nonempty (CorrPre T P) := by
  classical
  have hW : ∀ x x' : A.X.PObj.boundary, ∃ W : IndexCorr (T.dec.S x).I (T.dec.S x').I → Set A.Mor,
      (∀ d, IsOpen (W d)) ∧ (∀ d, closure (T.tau.τ x x' ⁻¹' {d} ∩ T.dec.𝒰.mor x x') ⊆ W d) ∧
      ∀ d d', d ≠ d' → Disjoint (closure (W d)) (closure (W d')) := by
    intro x x'
    refine exists_open_disjoint_closure (T.tau.finite x x') (fun _ => isClosed_closure)
      (fun d d' hd => disjoint_iff_inter_eq_empty.2 (hT x x' d d' hd)) fun d hd => ?_
    rw [closure_empty_iff, eq_empty_iff_forall_notMem]
    rintro φ ⟨hφ, hφU⟩
    exact hd ⟨φ, hφU, hφ⟩
  choose W hWo hCW hWd using hW
  exact ⟨{
    O := fun x x' d => W x x' d ∩ P.mor x x'
    isOpen := fun x x' d => (hWo x x' d).inter (P.isOpen_mor x x')
    fiber_subset := fun x x' d φ hφ => ⟨hCW x x' d (subset_closure hφ), P.mor_subset x x' hφ.2⟩
    subset_mor := fun _ _ _ => inter_subset_right
    disjoint_closure := fun x x' d d' hd =>
      (hWd x x' d d' hd).mono (closure_mono inter_subset_left) (closure_mono inter_subset_left) }⟩

variable (E : CorrPre T P)

/-- Step 2 (the intersection over the bi-action): `⋂_{h,g} (h ∗ · ∗ g)⁻¹(Õ'_{h∗[d]∗g})`. -/
def biInv : CorrPre T P where
  O x x' d := ⋂ (h : A.X.Isotropy x') (g : A.X.Isotropy x),
    P.mor x x' ∩ (fun φ => P.biact x x' h φ g) ⁻¹' E.O x x' (IndexCorr.biact h d g)
  isOpen x x' d := by
    have := A.X.proposition_7_1_12 (x : A.Obj)
    have := A.X.proposition_7_1_12 (x' : A.Obj)
    exact isOpen_iInter_of_finite fun h => isOpen_iInter_of_finite fun g =>
      (continuousOn_biact h g).isOpen_inter_preimage (P.isOpen_mor x x') (E.isOpen _ _ _)
  fiber_subset x x' d φ hφ := by
    refine mem_iInter₂.2 fun h g => ⟨P.mor_subset x x' hφ.2, ?_⟩
    change P.biact x x' h φ g ∈ E.O x x' (IndexCorr.biact h d g)
    rw [P.biact_eq]
    refine E.fiber_subset x x' _ ⟨?_, T.dec.𝒰.biact_mem_mor_p3w4 hφ.2 h g⟩
    rw [mem_preimage, T.tau.biact x x' φ hφ.2 h g, mem_singleton_iff.1 hφ.1]
    rfl
  subset_mor x x' d φ hφ := (mem_iInter₂.1 hφ 1 1).1
  disjoint_closure x x' d d' hd := by
    refine (E.disjoint_closure x x' d d' hd).mono (closure_mono ?_) (closure_mono ?_) <;>
    · intro φ hφ
      have h1 := mem_iInter₂.1 hφ 1 1
      have h2 := h1.2
      rwa [mem_preimage, P5Nbhds.biact, biact_one_one h1.1, IndexCorr.biact_one_one] at h2

theorem biInv_biact_mem_iff (x x' : A.X.PObj.boundary) (d) (h : A.X.Isotropy x')
    (g : A.X.Isotropy x) {φ : A.Mor} (hφ : φ ∈ P.mor x x') :
    P.biact x x' h φ g ∈ E.biInv.O x x' (IndexCorr.biact h d g) ↔ φ ∈ E.biInv.O x x' d := by
  have hbb : ∀ h₁ g₁, P.biact x x' h₁ (P.biact x x' h φ g) g₁ = P.biact x x' (h₁ * h) φ (g * g₁) :=
    fun h₁ g₁ => biact_biact hφ h₁ h g g₁
  simp only [biInv, mem_iInter₂, mem_inter_iff, mem_preimage]
  constructor
  · intro H h₂ g₂
    have := (H (h₂ * h⁻¹) (g⁻¹ * g₂)).2
    rw [hbb, IndexCorr.biact_biact, inv_mul_cancel_right, mul_inv_cancel_left] at this
    exact ⟨hφ, this⟩
  · intro H h₁ g₁
    refine ⟨P.biact_mem hφ h g, ?_⟩
    rw [hbb, IndexCorr.biact_biact]
    exact (H (h₁ * h) (g * g₁)).2

/-- Step 3 (not in the text): symmetrization under inversion,
`Õ_{x,x',[d]} ∩ ι⁻¹(Õ_{x',x,[d]♯})`. -/
def symm : CorrPre T P where
  O x x' d := E.O x x' d ∩ A.X.inv ⁻¹' E.O x' x d.swap
  isOpen x x' d := (E.isOpen x x' d).inter ((E.isOpen x' x _).preimage A.X.continuous_inv)
  fiber_subset x x' d φ hφ := by
    refine ⟨E.fiber_subset x x' d hφ, E.fiber_subset x' x _ ⟨?_, T.dec.𝒰.inv_mem_mor_p3w4 hφ.2⟩⟩
    rw [mem_preimage, T.tau.swap x x' φ hφ.2, mem_singleton_iff.1 hφ.1]
    rfl
  subset_mor x x' d := inter_subset_left.trans (E.subset_mor x x' d)
  disjoint_closure x x' d d' hd :=
    (E.disjoint_closure x x' d d' hd).mono (closure_mono inter_subset_left)
      (closure_mono inter_subset_left)

theorem symm_inv_mem_iff (x x' d) (φ : A.Mor) :
    A.X.inv φ ∈ E.symm.O x' x d.swap ↔ φ ∈ E.symm.O x x' d := by
  simp only [symm, mem_inter_iff, mem_preimage, GroupoidStr.inv_inv, IndexCorr.swap_swap]
  exact and_comm

theorem symm_biact_mem_iff
    (hE : ∀ (x x' : A.X.PObj.boundary) d (h : A.X.Isotropy x') (g : A.X.Isotropy x),
      ∀ φ ∈ P.mor x x',
      P.biact x x' h φ g ∈ E.O x x' (IndexCorr.biact h d g) ↔ φ ∈ E.O x x' d)
    (x x' : A.X.PObj.boundary) (d) (h : A.X.Isotropy x') (g : A.X.Isotropy x) {φ : A.Mor}
    (hφ : φ ∈ P.mor x x') :
    P.biact x x' h φ g ∈ E.symm.O x x' (IndexCorr.biact h d g) ↔ φ ∈ E.symm.O x x' d := by
  have hφi : A.X.inv φ ∈ P.mor x' x :=
    ⟨by rw [A.X.src_inv]; exact hφ.2, by rw [A.X.tgt_inv]; exact hφ.1⟩
  simp only [symm, mem_inter_iff, mem_preimage]
  rw [hE x x' d h g φ hφ, P5Nbhds.biact, inv_biact_p3w4 hφ, IndexCorr.swap_biact_p3w4]
  exact and_congr_right fun _ => hE x' x d.swap g⁻¹ h⁻¹ _ hφi

end CorrPre

/-- **2021 Lemma 14.3.1, p. 650 (2017: Lemma 14.2)**: for a representative
`(Λ, 𝒰⁰, S⁰, τ⁰)` with (P4) and neighbourhoods `Ũ'(x)` with (P5) there are open sets
`Õ_{x,x',[d]} ⊇ τ⁰⁻¹([d])` with (1)–(3) (and the symmetry under inversion), the fields of
`CorrExtension`; (4) is `CorrExtension.iUnion_inter_boundaryMor`.  The proof is the text's:
separate the closures (P4), then intersect over the bi-action; a last intersection with the
inverted sets gives the symmetry. -/
theorem lemma_14_3_1 {T : BoundaryStructuredTuple A} (hT : T.HasP4) (P : P5Nbhds T) :
    Nonempty (CorrExtension T P) := by
  obtain ⟨E⟩ := CorrPre.exists_of_hasP4 hT P
  exact ⟨{ E.biInv.symm with
    biact_mem_iff := fun x x' d h g φ hφ =>
      E.biInv.symm_biact_mem_iff (fun x x' d h g φ hφ => E.biInv_biact_mem_iff x x' d h g hφ)
        x x' d h g hφ
    inv_mem_iff := E.biInv.symm_inv_mem_iff }⟩

namespace CorrExtension

variable {T : BoundaryStructuredTuple A} {P : P5Nbhds T} (E : CorrExtension T P)

theorem disjoint {x x' : A.X.PObj.boundary} {d d' : IndexCorr (T.dec.S x).I (T.dec.S x').I}
    (hd : d ≠ d') : Disjoint (E.O x x' d) (E.O x x' d') :=
  (E.disjoint_closure x x' d d' hd).mono subset_closure subset_closure

theorem eq_of_mem {x x' : A.X.PObj.boundary} {d d' : IndexCorr (T.dec.S x).I (T.dec.S x').I}
    {φ : A.Mor} (h : φ ∈ E.O x x' d) (h' : φ ∈ E.O x x' d') : d = d' := by
  by_contra hd
  exact disjoint_left.1 (E.disjoint hd) h h'

/-- **(14.20)**: `Õ_{x,x',[d]} ∩ ∂X = τ⁰⁻¹([d])`. -/
theorem inter_boundaryMor (x x' : A.X.PObj.boundary) (d) :
    E.O x x' d ∩ boundaryMor A = T.tau.τ x x' ⁻¹' {d} ∩ T.dec.𝒰.mor x x' := by
  refine Subset.antisymm (fun φ hφ => ?_) fun φ hφ =>
    ⟨E.fiber_subset x x' d hφ, T.dec.𝒰.mor_subset_boundaryMor_p3w4 x x' hφ.2⟩
  have hφU : φ ∈ T.dec.𝒰.mor x x' := by
    rw [← P.mor_inter_boundaryMor]
    exact ⟨E.subset_mor x x' d hφ.1, hφ.2⟩
  have h' := E.fiber_subset x x' _ ⟨rfl, hφU⟩
  exact ⟨(E.eq_of_mem hφ.1 h').symm, hφU⟩

/-- **(3) of Lemma 14.3.1 as printed**: `h ∗ Õ_{x,x',[d]} ∗ g = Õ_{x,x',h∗[d]∗g}`. -/
theorem image_biact (x x' : A.X.PObj.boundary) (d) (h : A.X.Isotropy x') (g : A.X.Isotropy x) :
    (fun φ => P.biact x x' h φ g) '' E.O x x' d = E.O x x' (IndexCorr.biact h d g) := by
  refine Subset.antisymm ?_ fun ψ hψ => ?_
  · rintro _ ⟨φ, hφ, rfl⟩
    exact (E.biact_mem_iff x x' d h g φ (E.subset_mor x x' d hφ)).2 hφ
  · have hψM := E.subset_mor x x' _ hψ
    have hφM := P.biact_mem hψM h⁻¹ g⁻¹
    have hback : P.biact x x' h (P.biact x x' h⁻¹ ψ g⁻¹) g = ψ := by
      rw [P5Nbhds.biact, P5Nbhds.biact, biact_biact hψM, mul_inv_cancel, inv_mul_cancel,
        biact_one_one hψM]
    refine ⟨P.biact x x' h⁻¹ ψ g⁻¹, (E.biact_mem_iff x x' d h g _ hφM).1 ?_, hback⟩
    rwa [hback]

/-! ### Definition 14.3.2 -/

/-- `Õ_{x,x'} = ⋃_{[d]} Õ_{x,x',[d]}` (14.22). -/
def Ot (x x' : A.X.PObj.boundary) : Set A.Mor := ⋃ d, E.O x x' d

/-- **2021 Definition 14.3.2, p. 651 (2017: the text before Lemma 14.3)**: `Ô_{x,x'}`, the
union of the connected components of `Õ_{x,x'}` meeting `∂X`. -/
def Ohat (x x' : A.X.PObj.boundary) : Set A.Mor :=
  {φ | φ ∈ E.Ot x x' ∧ ∃ ψ ∈ connectedComponentIn (E.Ot x x') φ, ψ ∈ boundaryMor A}

open scoped Classical in
/-- **`φ ↦ [d]_φ`** (p. 651) and the extension `τ̂_{x,x'}` (14.25): the class `[d]` with
`φ ∈ Õ_{x,x',[d]}` (unique, `tauHat_eq`); off `Õ_{x,x'}`, the value of `τ⁰` (irrelevant).  By
`tauHat_eq_tau_of_mem_component` it is `τ⁰(ψ)` for every `ψ ∈ ∂X` in the component of `φ`, the
text's definition. -/
def tauHat (x x' : A.X.PObj.boundary) (φ : A.Mor) : IndexCorr (T.dec.S x).I (T.dec.S x').I :=
  if h : ∃ d, φ ∈ E.O x x' d then h.choose else T.tau.τ x x' φ

/-- `Ô_{x,x',[d]} = {φ ∈ Ô_{x,x'} | [d]_φ = [d]}` (p. 652). -/
def OhatD (x x' : A.X.PObj.boundary) (d : IndexCorr (T.dec.S x).I (T.dec.S x').I) : Set A.Mor :=
  {φ | φ ∈ E.Ohat x x' ∧ E.tauHat x x' φ = d}

variable {E}

theorem tauHat_eq {x x' : A.X.PObj.boundary} {d} {φ : A.Mor} (hφ : φ ∈ E.O x x' d) :
    E.tauHat x x' φ = d := by
  have h : ∃ d, φ ∈ E.O x x' d := ⟨d, hφ⟩
  rw [tauHat, dif_pos h]
  exact E.eq_of_mem h.choose_spec hφ

theorem mem_O_tauHat {x x' : A.X.PObj.boundary} {φ : A.Mor} (hφ : φ ∈ E.Ot x x') :
    φ ∈ E.O x x' (E.tauHat x x' φ) := by
  obtain ⟨d, hd⟩ := mem_iUnion.1 hφ
  rwa [tauHat_eq hd]

variable (E)

theorem isOpen_Ot (x x' : A.X.PObj.boundary) : IsOpen (E.Ot x x') :=
  isOpen_iUnion fun d => E.isOpen x x' d

theorem Ot_subset_mor (x x' : A.X.PObj.boundary) : E.Ot x x' ⊆ P.mor x x' :=
  iUnion_subset fun d => E.subset_mor x x' d

theorem mor_subset_Ot (x x' : A.X.PObj.boundary) : T.dec.𝒰.mor x x' ⊆ E.Ot x x' := fun _ hφ =>
  mem_iUnion.2 ⟨_, E.fiber_subset x x' _ ⟨rfl, hφ⟩⟩

/-- **(4) of Lemma 14.3.1**: `Õ_{x,x'} ∩ ∂X = U⁰(x, x')`. -/
theorem iUnion_inter_boundaryMor (x x' : A.X.PObj.boundary) :
    E.Ot x x' ∩ boundaryMor A = T.dec.𝒰.mor x x' := by
  refine Subset.antisymm ?_ fun φ hφ =>
    ⟨E.mor_subset_Ot x x' hφ, T.dec.𝒰.mor_subset_boundaryMor_p3w4 x x' hφ⟩
  rw [← P.mor_inter_boundaryMor]
  exact inter_subset_inter_left _ (E.Ot_subset_mor x x')

/-- The component in `Õ_{x,x'}` of a point of `Õ_{x,x',[d]}` lies in `Õ_{x,x',[d]}`. -/
theorem component_subset {x x' : A.X.PObj.boundary} {d} {φ : A.Mor} (hφ : φ ∈ E.O x x' d) :
    connectedComponentIn (E.Ot x x') φ ⊆ E.O x x' d :=
  connectedComponentIn_iUnion_subset (E.isOpen x x') (fun _ _ hd => E.disjoint hd) hφ

/-- `τ̂` is constant on the components of `Õ_{x,x'}`. -/
theorem tauHat_eq_of_mem_component {x x' : A.X.PObj.boundary} {φ ψ : A.Mor}
    (hφ : φ ∈ E.Ot x x') (hψ : ψ ∈ connectedComponentIn (E.Ot x x') φ) :
    E.tauHat x x' ψ = E.tauHat x x' φ :=
  tauHat_eq (E.component_subset (mem_O_tauHat hφ) hψ)

/-- **`τ̂(φ) = τ⁰(ψ)`** for every `ψ ∈ ∂X` in the component of `φ` in `Õ_{x,x'}`. -/
theorem tauHat_eq_tau_of_mem_component_Ot {x x' : A.X.PObj.boundary} {φ ψ : A.Mor}
    (hφ : φ ∈ E.Ot x x') (hψ : ψ ∈ connectedComponentIn (E.Ot x x') φ)
    (hψb : ψ ∈ boundaryMor A) : E.tauHat x x' φ = T.tau.τ x x' ψ := by
  have h := E.component_subset (mem_O_tauHat hφ) hψ
  have h' : ψ ∈ E.O x x' (E.tauHat x x' φ) ∩ boundaryMor A := ⟨h, hψb⟩
  rw [E.inter_boundaryMor] at h'
  exact (mem_singleton_iff.1 h'.1).symm

theorem Ohat_subset_Ot (x x' : A.X.PObj.boundary) : E.Ohat x x' ⊆ E.Ot x x' := fun _ h => h.1

/-- **(14.23)** `U⁰(x, x') ⊆ Ô_{x,x'}`. -/
theorem mor_subset_Ohat (x x' : A.X.PObj.boundary) : T.dec.𝒰.mor x x' ⊆ E.Ohat x x' :=
  fun φ hφ => ⟨E.mor_subset_Ot x x' hφ, φ, mem_connectedComponentIn (E.mor_subset_Ot x x' hφ),
    T.dec.𝒰.mor_subset_boundaryMor_p3w4 x x' hφ⟩

/-- **(14.23)** `Ô_{x,x'} ⊆ Õ_{x,x'} ⊆ Ũ'(x, x')`. -/
theorem Ohat_subset_mor (x x' : A.X.PObj.boundary) : E.Ohat x x' ⊆ P.mor x x' :=
  (E.Ohat_subset_Ot x x').trans (E.Ot_subset_mor x x')

/-- **(14.23)** `Ô_{x,x'} ∩ ∂X = U⁰(x, x')`. -/
theorem Ohat_inter_boundaryMor (x x' : A.X.PObj.boundary) :
    E.Ohat x x' ∩ boundaryMor A = T.dec.𝒰.mor x x' := by
  refine Subset.antisymm ?_ fun φ hφ =>
    ⟨E.mor_subset_Ohat x x' hφ, T.dec.𝒰.mor_subset_boundaryMor_p3w4 x x' hφ⟩
  rw [← E.iUnion_inter_boundaryMor]
  exact inter_subset_inter_left _ (E.Ohat_subset_Ot x x')

/-- The component in `Õ_{x,x'}` of a point of `Ô_{x,x'}` lies in `Ô_{x,x'}`. -/
theorem component_subset_Ohat {x x' : A.X.PObj.boundary} {φ : A.Mor} (hφ : φ ∈ E.Ohat x x') :
    connectedComponentIn (E.Ot x x') φ ⊆ E.Ohat x x' := by
  intro χ hχ
  obtain ⟨-, ψ, hψ, hψb⟩ := hφ
  refine ⟨connectedComponentIn_subset _ _ hχ, ψ, ?_, hψb⟩
  rwa [← connectedComponentIn_eq hχ]

/-- `Ô_{x,x'}` is open (a union of components of the open set `Õ_{x,x'}`). -/
theorem isOpen_Ohat (x x' : A.X.PObj.boundary) : IsOpen (E.Ohat x x') :=
  isOpen_iff_forall_mem_open.2 fun φ hφ =>
    ⟨_, E.component_subset_Ohat hφ,
      EpGroupoid.isOpen_connectedComponentIn_mor A.X (E.isOpen_Ot x x') φ,
      mem_connectedComponentIn hφ.1⟩

/-! ### Lemma 14.3.3 -/

/-- **2021 Lemma 14.3.3, p. 651 (2017: Lemma 14.3)**: `φ ↦ [d]_φ` is well defined: two
morphisms of `∂X` in the same component of `Ô_{x,x'}` have the same `τ⁰`. -/
theorem lemma_14_3_3 {x x' : A.X.PObj.boundary} {φ ψ ψ' : A.Mor}
    (hψ : ψ ∈ connectedComponentIn (E.Ohat x x') φ)
    (hψ' : ψ' ∈ connectedComponentIn (E.Ohat x x') φ)
    (hψb : ψ ∈ boundaryMor A) (hψ'b : ψ' ∈ boundaryMor A) :
    T.tau.τ x x' ψ = T.tau.τ x x' ψ' := by
  have hφ : φ ∈ E.Ohat x x' := by
    by_contra h
    rw [connectedComponentIn_eq_empty h] at hψ
    exact hψ
  have hmono := connectedComponentIn_mono φ (E.Ohat_subset_Ot x x')
  rw [← E.tauHat_eq_tau_of_mem_component_Ot hφ.1 (hmono hψ) hψb,
    E.tauHat_eq_tau_of_mem_component_Ot hφ.1 (hmono hψ') hψ'b]

/-- **The definition of `[d]_φ` (p. 651)**: for `φ ∈ Ô_{x,x'}` and `ψ ∈ ∂X` in the component of
`φ` in `Ô_{x,x'}`, `τ̂(φ) = τ⁰(ψ)`. -/
theorem tauHat_eq_tau_of_mem_component {x x' : A.X.PObj.boundary} {φ ψ : A.Mor}
    (hφ : φ ∈ E.Ohat x x') (hψ : ψ ∈ connectedComponentIn (E.Ohat x x') φ)
    (hψb : ψ ∈ boundaryMor A) : E.tauHat x x' φ = T.tau.τ x x' ψ :=
  E.tauHat_eq_tau_of_mem_component_Ot hφ.1 (connectedComponentIn_mono φ (E.Ohat_subset_Ot x x') hψ)
    hψb

/-- Every component of `Ô_{x,x'}` meets `∂X`, in the component in `Õ_{x,x'}`. -/
theorem exists_boundary_mem_component {x x' : A.X.PObj.boundary} {φ : A.Mor}
    (hφ : φ ∈ E.Ohat x x') : ∃ ψ ∈ connectedComponentIn (E.Ot x x') φ, ψ ∈ T.dec.𝒰.mor x x' := by
  obtain ⟨-, ψ, hψ, hψb⟩ := hφ
  refine ⟨ψ, hψ, ?_⟩
  rw [← E.iUnion_inter_boundaryMor]
  exact ⟨connectedComponentIn_subset _ _ hψ, hψb⟩

/-! ### Proposition 14.3.4 -/

/-- **`τ̂` extends `τ⁰`**: `τ̂ = τ⁰` on `U⁰(x, x')`. -/
theorem tauHat_eq_tau {x x' : A.X.PObj.boundary} {φ : A.Mor} (hφ : φ ∈ T.dec.𝒰.mor x x') :
    E.tauHat x x' φ = T.tau.τ x x' φ :=
  tauHat_eq (E.fiber_subset x x' _ ⟨rfl, hφ⟩)

/-- **`τ̂` is locally constant** on `Õ_{x,x'}` (so on `Ô_{x,x'}`). -/
theorem tauHat_locallyConstant {x x' : A.X.PObj.boundary} {φ : A.Mor} (hφ : φ ∈ E.Ot x x') :
    ∀ᶠ ψ in 𝓝 φ, E.tauHat x x' ψ = E.tauHat x x' φ := by
  filter_upwards [(E.isOpen x x' _).mem_nhds (mem_O_tauHat hφ)] with ψ hψ
  exact tauHat_eq hψ

/-- **Uniqueness of the extension**: a locally constant `f` on `Ô_{x,x'}` with `f = τ⁰` on
`U⁰(x, x')` is `τ̂` (every component of `Ô_{x,x'}` meets `∂X`). -/
theorem tauHat_unique {x x' : A.X.PObj.boundary} {β : Type*} {f : A.Mor → β}
    {e : IndexCorr (T.dec.S x).I (T.dec.S x').I → β}
    (hf : ∀ φ ∈ E.Ohat x x', ∀ᶠ ψ in 𝓝[E.Ohat x x'] φ, f ψ = f φ)
    (hfτ : ∀ φ ∈ T.dec.𝒰.mor x x', f φ = e (T.tau.τ x x' φ)) {φ : A.Mor}
    (hφ : φ ∈ E.Ohat x x') : f φ = e (E.tauHat x x' φ) := by
  have hf' : ∀ φ ∈ E.Ohat x x', ∀ᶠ ψ in 𝓝 φ, f ψ = f φ := fun φ hφ => by
    rw [← (E.isOpen_Ohat x x').nhdsWithin_eq hφ]
    exact hf φ hφ
  have hg : ∀ φ ∈ E.Ohat x x', ∀ᶠ ψ in 𝓝 φ, e (E.tauHat x x' ψ) = e (E.tauHat x x' φ) :=
    fun φ hφ => (E.tauHat_locallyConstant hφ.1).mono fun ψ h => by rw [h]
  -- a boundary morphism in the component of `φ` in `Ô_{x,x'}`
  obtain ⟨ψ, hψ, hψU⟩ := E.exists_boundary_mem_component hφ
  have hψ' : ψ ∈ connectedComponentIn (E.Ohat x x') φ :=
    (isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hφ.1) (E.component_subset_Ohat hφ)) hψ
  rw [← eq_of_mem_connectedComponentIn hf' hψ', ← eq_of_mem_connectedComponentIn hg hψ',
    hfτ ψ hψU, E.tauHat_eq_tau hψU]

/-- The finitely many values of `τ̂` on `Ô_{x,x'}` are values of `τ⁰` (not stated in the
text; "taking the same values as `τ⁰`"). -/
theorem tauHat_image_subset (x x' : A.X.PObj.boundary) :
    E.tauHat x x' '' E.Ohat x x' ⊆ T.tau.τ x x' '' T.dec.𝒰.mor x x' := by
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨ψ, hψ, hψU⟩ := E.exists_boundary_mem_component hφ
  exact ⟨ψ, hψU, (E.tauHat_eq_tau_of_mem_component_Ot hφ.1 hψ
    (T.dec.𝒰.mor_subset_boundaryMor_p3w4 x x' hψU)).symm⟩

theorem finite_tauHat (x x' : A.X.PObj.boundary) : (E.tauHat x x' '' E.Ohat x x').Finite :=
  (T.tau.finite x x').subset (E.tauHat_image_subset x x')

/-- **Equivariance of `τ̂`**: `τ̂(h ∗ φ ∗ g) = h ∗ τ̂(φ) ∗ g`. -/
theorem tauHat_biact {x x' : A.X.PObj.boundary} {φ : A.Mor} (hφ : φ ∈ E.Ot x x')
    (h : A.X.Isotropy x') (g : A.X.Isotropy x) :
    E.tauHat x x' (P.biact x x' h φ g) = IndexCorr.biact h (E.tauHat x x' φ) g :=
  tauHat_eq ((E.biact_mem_iff x x' _ h g φ (E.Ot_subset_mor x x' hφ)).2 (mem_O_tauHat hφ))

/-- The bi-action maps the component of `φ` in `Õ_{x,x'}` into that of `h ∗ φ ∗ g`. -/
theorem biact_mem_Ot {x x' : A.X.PObj.boundary} {φ : A.Mor} (hφ : φ ∈ E.Ot x x')
    (h : A.X.Isotropy x') (g : A.X.Isotropy x) : P.biact x x' h φ g ∈ E.Ot x x' :=
  mem_iUnion.2 ⟨_, (E.biact_mem_iff x x' _ h g φ (E.Ot_subset_mor x x' hφ)).2 (mem_O_tauHat hφ)⟩

/-- **(2) of Proposition 14.3.4**: `Ô_{x,x'}` is invariant under the bi-action of
`(G_{x'}, G_x)`. -/
theorem biact_mem_Ohat {x x' : A.X.PObj.boundary} {φ : A.Mor} (hφ : φ ∈ E.Ohat x x')
    (h : A.X.Isotropy x') (g : A.X.Isotropy x) : P.biact x x' h φ g ∈ E.Ohat x x' := by
  obtain ⟨hφO, ψ, hψ, hψb⟩ := hφ
  have hmaps : MapsTo (fun χ => P.biact x x' h χ g) (E.Ot x x') (E.Ot x x') :=
    fun χ hχ => E.biact_mem_Ot hχ h g
  have hcont : ContinuousOn (fun χ => P.biact x x' h χ g) (E.Ot x x') :=
    (continuousOn_biact h g).mono (E.Ot_subset_mor x x')
  have himg : (fun χ => P.biact x x' h χ g) '' connectedComponentIn (E.Ot x x') φ ⊆
      connectedComponentIn (E.Ot x x') (P.biact x x' h φ g) :=
    (isPreconnected_connectedComponentIn.image _
      (hcont.mono (connectedComponentIn_subset _ _))).subset_connectedComponentIn
      ⟨φ, mem_connectedComponentIn hφO, rfl⟩
      ((image_mono (connectedComponentIn_subset _ _)).trans (mapsTo_iff_image_subset.1 hmaps))
  have hψU : ψ ∈ T.dec.𝒰.mor x x' := by
    rw [← E.iUnion_inter_boundaryMor]
    exact ⟨connectedComponentIn_subset _ _ hψ, hψb⟩
  refine ⟨hmaps hφO, _, himg ⟨ψ, hψ, rfl⟩, ?_⟩
  change P.biact x x' h ψ g ∈ boundaryMor A
  rw [P.biact_eq]
  exact T.dec.𝒰.mor_subset_boundaryMor_p3w4 x x' (T.dec.𝒰.biact_mem_mor_p3w4 hψU h g)

/-- **The diagonal property of `τ̂` (Proposition 14.3.4 (3), second display)**: for
`y ∈ Ũ'(x)` with `Γ(g, y) ∈ Ô_{x,x}`, `τ̂_{x,x}(Γ(g, y)) = [I_x ←Id I_x →g I_x]`
(`= τ⁰_{x,x}(Γ(g, z))` for `z ∈ U⁰(x)`, Definition 14.1.7 (b)).  The component of `Γ(g, y)` in
`Õ_{x,x}` stays in the sheet `Γ(g, ·)` and meets `∂X`. -/
theorem tauHat_Γ {x : A.X.PObj.boundary} (g : A.X.Isotropy x) {y : A.Obj}
    (hy : y ∈ (P.nbhd x).U) (hΓ : (P.nbhd x).rep.Γ g y ∈ E.Ohat x x) :
    E.tauHat x x ((P.nbhd x).rep.Γ g y) = IndexCorr.ofPerm g := by
  set R := (P.nbhd x).rep
  obtain ⟨ψ, hψ, hψU⟩ := E.exists_boundary_mem_component hΓ
  have hMR : ∀ χ ∈ E.Ot x x, χ ∈ A.X.morBetween R.U R.U := fun χ hχ =>
    morBetween_mono (P.nbhd x).U_subset (P.nbhd x).U_subset (E.Ot_subset_mor x x hχ)
  have hlab := eq_of_mem_connectedComponentIn
    (fun χ hχ => sheetLabel_locallyConstant_p3w4 R (hMR χ hχ)) hψ
  have hΓlab : sheetLabel_p3w4 R (R.Γ g y) = g :=
    sheetLabel_eq_p3w4 R (hMR _ hΓ.1) (by rw [(P.nbhd x).src_Γ g hy])
  have hψΓ : R.Γ g (A.X.src ψ) = ψ := by
    rw [← hΓlab, ← hlab]
    exact Γ_sheetLabel_p3w4 R (hMR ψ (connectedComponentIn_subset _ _ hψ))
  rw [E.tauHat_eq_tau_of_mem_component_Ot hΓ.1 hψ
    (T.dec.𝒰.mor_subset_boundaryMor_p3w4 x x hψU), ← hψΓ]
  have hd := T.tau.diag x g (A.X.src ψ) hψU.1
  rwa [← P.rep_eq x] at hd

/-- **Inversion**: `φ ∈ Ô_{x,x'}` iff `φ⁻¹ ∈ Ô_{x',x}` (not in the text). -/
theorem inv_mem_Ohat {x x' : A.X.PObj.boundary} {φ : A.Mor} (hφ : φ ∈ E.Ohat x x') :
    A.X.inv φ ∈ E.Ohat x' x := by
  obtain ⟨hφO, ψ, hψ, hψb⟩ := hφ
  have hmaps : MapsTo A.X.inv (E.Ot x x') (E.Ot x' x) := fun χ hχ =>
    mem_iUnion.2 ⟨_, (E.inv_mem_iff x x' _ χ).2 (mem_O_tauHat hχ)⟩
  have himg : A.X.inv '' connectedComponentIn (E.Ot x x') φ ⊆
      connectedComponentIn (E.Ot x' x) (A.X.inv φ) :=
    (isPreconnected_connectedComponentIn.image _
      A.X.continuous_inv.continuousOn).subset_connectedComponentIn
      ⟨φ, mem_connectedComponentIn hφO, rfl⟩
      ((image_mono (connectedComponentIn_subset _ _)).trans (mapsTo_iff_image_subset.1 hmaps))
  refine ⟨hmaps hφO, _, himg ⟨ψ, hψ, rfl⟩, ?_⟩
  exact ⟨by rw [A.X.src_inv]; exact hψb.2, by rw [A.X.tgt_inv]; exact hψb.1⟩

/-- **`τ̂_{x',x}(φ⁻¹) = τ̂_{x,x'}(φ)♯`** (Definition 14.1.7 (a) for `τ̂`; not in the text). -/
theorem tauHat_inv {x x' : A.X.PObj.boundary} {φ : A.Mor} (hφ : φ ∈ E.Ot x x') :
    E.tauHat x' x (A.X.inv φ) = (E.tauHat x x' φ).swap :=
  tauHat_eq ((E.inv_mem_iff x x' _ φ).2 (mem_O_tauHat hφ))

/-- `Ô_{x,x',[d]} = Ô_{x,x'} ∩ Õ_{x,x',[d]}`. -/
theorem OhatD_eq (x x' : A.X.PObj.boundary) (d) :
    E.OhatD x x' d = E.Ohat x x' ∩ E.O x x' d := by
  ext φ
  refine ⟨fun h => ⟨h.1, h.2 ▸ mem_O_tauHat h.1.1⟩, fun h => ⟨h.1, tauHat_eq h.2⟩⟩

/-- **The decomposition (14.24)**: `Ô_{x,x',[d]} ∩ ∂X = τ⁰⁻¹([d])`. -/
theorem OhatD_inter_boundaryMor (x x' : A.X.PObj.boundary) (d) :
    E.OhatD x x' d ∩ boundaryMor A = T.tau.τ x x' ⁻¹' {d} ∩ T.dec.𝒰.mor x x' := by
  rw [OhatD_eq]
  refine Subset.antisymm (fun φ hφ => ?_) fun φ hφ =>
    ⟨⟨E.mor_subset_Ohat x x' hφ.2, E.fiber_subset x x' d hφ⟩,
      T.dec.𝒰.mor_subset_boundaryMor_p3w4 x x' hφ.2⟩
  rw [← E.inter_boundaryMor]
  exact ⟨hφ.1.2, hφ.2⟩

end CorrExtension

/-- **2021 Lemma 14.3.1, p. 650, as printed**: for every `[d] ∈ J(x, x')` an open
`Õ_{x,x',[d]} ⊇ τ⁰⁻¹([d])` with (1) `Õ_{x,x',[d]} ⊆ Ũ'(x, x')`, (2) disjoint closures for
`[d] ≠ [d']`, (3) `h ∗ Õ_{x,x',[d]} ∗ g = Õ_{x,x',h∗[d]∗g}`, (4) `Õ_{x,x'} ∩ ∂X = U⁰(x, x')`. -/
theorem lemma_14_3_1_book {T : BoundaryStructuredTuple A} (hT : T.HasP4) (P : P5Nbhds T) :
    ∃ O : ∀ x x' : A.X.PObj.boundary, IndexCorr (T.dec.S x).I (T.dec.S x').I → Set A.Mor,
      (∀ (x x' : A.X.PObj.boundary) d,
        IsOpen (O x x' d) ∧ T.tau.τ x x' ⁻¹' {d} ∩ T.dec.𝒰.mor x x' ⊆ O x x' d) ∧
      (∀ (x x' : A.X.PObj.boundary) d, O x x' d ⊆ P.mor x x') ∧
      (∀ (x x' : A.X.PObj.boundary) d d', d ≠ d' →
        Disjoint (closure (O x x' d)) (closure (O x x' d'))) ∧
      (∀ (x x' : A.X.PObj.boundary) d (h : A.X.Isotropy x') (g : A.X.Isotropy x),
        (fun φ => P.biact x x' h φ g) '' O x x' d = O x x' (IndexCorr.biact h d g)) ∧
      (∀ x x' : A.X.PObj.boundary, (⋃ d, O x x' d) ∩ boundaryMor A = T.dec.𝒰.mor x x') := by
  obtain ⟨E⟩ := lemma_14_3_1 hT P
  exact ⟨E.O, fun x x' d => ⟨E.isOpen x x' d, E.fiber_subset x x' d⟩, E.subset_mor,
    E.disjoint_closure, E.image_biact, E.iUnion_inter_boundaryMor⟩

/-- **2021 Proposition 14.3.4, p. 652 (2017: Proposition 14.3)**: for a representative with
(P1)–(P4) and neighbourhoods `Ũ'(x)` with (P5) there are open `Ô_{x,x'} ⊆ 𝐗` with
(1) `U⁰(x, x') ⊆ Ô_{x,x'} ⊆ Ũ'(x, x')` and `Ô_{x,x'} ∩ ∂X = U⁰(x, x')`,
(2) `Ô_{x,x'}` invariant under the bi-action of `(G_{x'}, G_x)`,
(3) a locally constant extension `τ̂_{x,x'}` of `τ⁰_{x,x'}` to `Ô_{x,x'}`, unique among locally
constant extensions, with `τ̂(g' ∗ φ ∗ g) = g' ∗ τ̂(φ) ∗ g` and
`τ̂_{x,x}(Γ(g, y)) = τ⁰_{x,x}(Γ(g, z))` (`z ∈ U⁰(x)`, `y ∈ Ũ'(x)`, `Γ(g, y) ∈ Ô_{x,x}`), and
`Ô_{x,x',[d]} ∩ ∂X = τ⁰⁻¹([d])` for `Ô_{x,x',[d]} = {φ ∈ Ô_{x,x'} | τ̂(φ) = [d]}` (so
`τ⁰⁻¹([d']) ∩ Ô_{x,x',[d]} = ∅` for `[d'] ≠ [d]`).  Proof: Lemma 14.3.1 and Definition 14.3.2. -/
theorem proposition_14_3_4 {T : BoundaryStructuredTuple A} (hT : T.HasP4) (P : P5Nbhds T) :
    ∃ (Oh : A.X.PObj.boundary → A.X.PObj.boundary → Set A.Mor)
      (τh : ∀ x x' : A.X.PObj.boundary, A.Mor → IndexCorr (T.dec.S x).I (T.dec.S x').I),
      (∀ x x', IsOpen (Oh x x')) ∧
      (∀ x x', T.dec.𝒰.mor x x' ⊆ Oh x x' ∧ Oh x x' ⊆ P.mor x x' ∧
        Oh x x' ∩ boundaryMor A = T.dec.𝒰.mor x x') ∧
      (∀ (x x' : A.X.PObj.boundary) (h : A.X.Isotropy x') (g : A.X.Isotropy x),
        ∀ φ ∈ Oh x x', P.biact x x' h φ g ∈ Oh x x') ∧
      (∀ x x', ∀ φ ∈ Oh x x', ∀ᶠ ψ in 𝓝 φ, τh x x' ψ = τh x x' φ) ∧
      (∀ x x', ∀ φ ∈ T.dec.𝒰.mor x x', τh x x' φ = T.tau.τ x x' φ) ∧
      (∀ (x x' : A.X.PObj.boundary) (f : A.Mor → IndexCorr (T.dec.S x).I (T.dec.S x').I),
        (∀ φ ∈ Oh x x', ∀ᶠ ψ in 𝓝[Oh x x'] φ, f ψ = f φ) →
        (∀ φ ∈ T.dec.𝒰.mor x x', f φ = T.tau.τ x x' φ) → ∀ φ ∈ Oh x x', f φ = τh x x' φ) ∧
      (∀ (x x' : A.X.PObj.boundary) (h : A.X.Isotropy x') (g : A.X.Isotropy x),
        ∀ φ ∈ Oh x x', τh x x' (P.biact x x' h φ g) = IndexCorr.biact h (τh x x' φ) g) ∧
      (∀ (x : A.X.PObj.boundary) (g : A.X.Isotropy x), ∀ z ∈ T.dec.𝒰.U x, ∀ y ∈ (P.nbhd x).U,
        (P.nbhd x).rep.Γ g y ∈ Oh x x →
          τh x x ((P.nbhd x).rep.Γ g y) = T.tau.τ x x ((T.dec.𝒰.nbhd x).rep.Γ g z)) ∧
      (∀ (x x' : A.X.PObj.boundary) d, {φ | φ ∈ Oh x x' ∧ τh x x' φ = d} ∩ boundaryMor A =
        T.tau.τ x x' ⁻¹' {d} ∩ T.dec.𝒰.mor x x') := by
  obtain ⟨E⟩ := lemma_14_3_1 hT P
  refine ⟨E.Ohat, E.tauHat, E.isOpen_Ohat, fun x x' => ⟨E.mor_subset_Ohat x x',
    E.Ohat_subset_mor x x', E.Ohat_inter_boundaryMor x x'⟩,
    fun x x' h g φ hφ => E.biact_mem_Ohat hφ h g, fun x x' φ hφ => E.tauHat_locallyConstant hφ.1,
    fun x x' φ hφ => E.tauHat_eq_tau hφ,
    fun x x' f hf hfτ φ hφ => E.tauHat_unique (e := id) hf hfτ hφ,
    fun x x' h g φ hφ => E.tauHat_biact hφ.1 h g, fun x g z hz y hy hΓ => ?_,
    E.OhatD_inter_boundaryMor⟩
  rw [E.tauHat_Γ g hy hΓ, T.tau.diag x g z hz]

end SBLocalization

end Polyfold
