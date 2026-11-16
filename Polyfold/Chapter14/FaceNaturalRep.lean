import Polyfold.Chapter14.FaceGoodSystem
import Polyfold.Chapter2.LocConnected

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.6, p. 680, with
Theorem 7.1.13 and Proposition 11.1.6.  Numbers and pages are the 2021 text's.

# The natural representation of a face ep-groupoid

For a face `F = X_θ` of a tame face-structured ep-groupoid, the neighbourhoods `U_F(x)` of a
structured sc⁺-multisection on `W|F` are to form a good system for the ep-groupoid `F`
(Proposition 11.1.6).  Condition (2) of Definition 13.1.4 asks for the natural `G_x`-action of
`F` on `U_F(x)`.  Here the natural representation of `X` at `x ∈ F` is restricted to `F`: its
domain is the connected component of `x` in `U(x) ∩ F`, the isotropy groups of `F` and of `X`
at `x` agree, and the action and the morphisms `Γ` are those of `X`.

## What is formalized

Namespace `Polyfold.EpGroupoid`, for an ep-subgroupoid `A ⊆ X` (`subEpGroupoid hA`):
* `subIsotropyEquiv`: `(G_A)_a ≃* G_a`.
* **`NaturalRep.sub`**: a natural representation of `X` at `a ∈ A` restricts to a natural
  representation of the ep-subgroupoid `A` at `a` (Theorem 7.1.13 for `A`), on the connected
  component `subU` of `a` in `U ∩ A`; `sub_Φ_val`, `sub_Γ_val`: the action and `Γ` are those
  of `X`.
* `NatNbhd.sub`: a neighbourhood `U ∋ a` with the natural action of `X`, `U ∩ A` inside the
  component, is one of `A`.

Namespace `Polyfold.SBLocalization`:
* `FaceStructuredTuple.exists_equiv_faceGoodSystem` and on classes
  **`FaceStructuredMultisection.exists_rep_faceGoodSystem`**: every structured
  sc⁺-multisection on `W|F` has a representative and a good system `𝒢` of the ep-groupoid `F`
  (`faceEpGroupoid hX hθ`, Definition 13.1.4: all three conditions, (2) in the strict sense)
  with `U_𝒢(x) = U_F(x) = U(x) ∩ F` and the natural action of `𝒢` that of the representative,
  restricted to `F`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

open scoped EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {A : Set Obj} (hA : X.IsEpSubgroupoid A) [ParacompactSpace A]

/-! ### Isotropy of an ep-subgroupoid -/

/-- **The isotropy groups of `A` and `X` at `a ∈ A` agree** (`A` is a full subcategory). -/
def subIsotropyEquiv (a : A) : (subEpGroupoid hA).Isotropy a ≃* X.Isotropy a where
  toFun g := ⟨g.val.val, congrArg Subtype.val g.src_val, congrArg Subtype.val g.tgt_val⟩
  invFun g := ⟨⟨g.val, by rw [g.src_val]; exact a.2, by rw [g.tgt_val]; exact a.2⟩,
    Subtype.ext g.src_val, Subtype.ext g.tgt_val⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' g h := GroupoidStr.Isotropy.ext
    (subEpGroupoid_comp_val hA (g.src_val.trans h.tgt_val.symm))

@[simp] theorem subIsotropyEquiv_val (a : A) (g : (subEpGroupoid hA).Isotropy a) :
    (subIsotropyEquiv hA a g).val = g.val.val := rfl

@[simp] theorem subIsotropyEquiv_symm_val (a : A) (g : X.Isotropy a) :
    ((subIsotropyEquiv hA a).symm g).val.val = g.val := rfl

/-! ### Restriction of a natural representation -/

namespace NaturalRep

variable {a : A} (R : X.NaturalRep (a : Obj))

/-- The domain of the restricted representation: the connected component of `a` in `U ∩ A`. -/
def subU : Set A := connectedComponentIn ((↑) ⁻¹' R.U) a

include hA in
theorem isOpen_subU : IsOpen (R.subU) := by
  have := (subObjPolyfold hA).locallyConnectedSpace
  exact (R.isOpen_U.preimage continuous_subtype_val).connectedComponentIn

omit [ParacompactSpace A] in
theorem mem_subU : a ∈ R.subU := mem_connectedComponentIn R.mem_U

omit [ParacompactSpace A] in
theorem isConnected_subU : IsConnected R.subU :=
  isConnected_connectedComponentIn_iff.2 (show a ∈ ((↑) ⁻¹' R.U : Set A) from R.mem_U)

omit [ParacompactSpace A] in
theorem subU_subset : R.subU ⊆ (↑) ⁻¹' R.U := connectedComponentIn_subset _ _

omit [ParacompactSpace A] in
include hA in
theorem Γ_mem_morOn_sub (g : X.Isotropy (a : Obj)) {y : A} (hy : (y : Obj) ∈ R.U) :
    R.Γ g y ∈ X.morOn A :=
  ⟨by rw [R.src_Γ g y hy]; exact y.2,
    X.isSaturated_iff.1 hA.isSaturated _ (by rw [R.src_Γ g y hy]; exact y.2)⟩

omit [ParacompactSpace A] in
include hA in
theorem Φ_mem_sub (g : X.Isotropy (a : Obj)) {y : A} (hy : (y : Obj) ∈ R.U) : R.Φ g y ∈ A := by
  rw [← R.tgt_Γ g y hy]; exact (R.Γ_mem_morOn_sub hA g hy).2

open scoped Classical in
/-- The action on `A`. -/
def subΦ (g : (subEpGroupoid hA).Isotropy a) (y : A) : A :=
  if h : R.Φ (subIsotropyEquiv hA a g) y ∈ A then ⟨_, h⟩ else y

open scoped Classical in
/-- The morphisms `Γ` of `A`. -/
def subΓ (g : (subEpGroupoid hA).Isotropy a) (y : A) : X.morOn A :=
  if h : R.Γ (subIsotropyEquiv hA a g) y ∈ X.morOn A then ⟨_, h⟩ else (subEpGroupoid hA).unit y

theorem subΦ_val (g : (subEpGroupoid hA).Isotropy a) {y : A} (hy : (y : Obj) ∈ R.U) :
    (R.subΦ hA g y : Obj) = R.Φ (subIsotropyEquiv hA a g) y := by
  classical
  rw [subΦ, dif_pos (R.Φ_mem_sub hA _ hy)]

theorem subΓ_val (g : (subEpGroupoid hA).Isotropy a) {y : A} (hy : (y : Obj) ∈ R.U) :
    (R.subΓ hA g y : Mor) = R.Γ (subIsotropyEquiv hA a g) y := by
  classical
  rw [subΓ, dif_pos (R.Γ_mem_morOn_sub hA _ hy)]

theorem continuousOn_subΦ (g : (subEpGroupoid hA).Isotropy a) :
    ContinuousOn (R.subΦ hA g) (R.subU) := by
  rw [IsInducing.subtypeVal.continuousOn_iff]
  refine (((R.isScDiffeoOn_Φ (subIsotropyEquiv hA a g)).isScSmoothOn.continuousOn.comp
    continuous_subtype_val.continuousOn fun _ hy => R.subU_subset hy)).congr fun y hy => ?_
  exact R.subΦ_val hA g (R.subU_subset hy)

theorem mapsTo_subΦ (g : (subEpGroupoid hA).Isotropy a) :
    MapsTo (R.subΦ hA g) (R.subU) (R.subU) := by
  have hpc : IsPreconnected (R.subΦ hA g '' R.subU) :=
    (R.isConnected_subU.isPreconnected).image _
      (R.continuousOn_subΦ hA g)
  have ha : a ∈ R.subΦ hA g '' R.subU :=
    ⟨a, R.mem_subU, Subtype.ext ((R.subΦ_val hA g R.mem_U).trans (R.Φ_self _))⟩
  have hsub : R.subΦ hA g '' R.subU ⊆ (↑) ⁻¹' R.U := by
    rintro _ ⟨y, hy, rfl⟩
    change (R.subΦ hA g y : Obj) ∈ R.U
    rw [R.subΦ_val hA g (R.subU_subset hy)]
    exact R.mapsTo_Φ _ (R.subU_subset hy)
  exact fun y hy => hpc.subset_connectedComponentIn ha hsub ⟨y, hy, rfl⟩

theorem isScSmoothOn_subΦ (g : (subEpGroupoid hA).Isotropy a) :
    (subObjPolyfold hA).IsScSmoothOn (subObjPolyfold hA) (R.subΦ hA g) (R.subU) := by
  refine MPolyfold.isScSmoothOn_sub_of_val hA.isSubMPolyfold ?_
  refine (((R.isScDiffeoOn_Φ (subIsotropyEquiv hA a g)).isScSmoothOn.comp
    ((MPolyfold.subPolyfold_inclusion_isScSmooth hA.isSubMPolyfold).mono (R.isOpen_subU hA)
      (subset_univ _)) fun _ hy => R.subU_subset hy)).congr fun y hy => ?_
  exact (R.subΦ_val hA g (R.subU_subset hy)).symm

/-- **The restriction of a natural representation of `X` at `a ∈ A` to the ep-subgroupoid
`A`** (Theorem 7.1.13 for `A`): the domain is the connected component of `a` in `U ∩ A`, the
action and the morphisms `Γ` are those of `X`. -/
def sub : (subEpGroupoid hA).NaturalRep a where
  U := R.subU
  isOpen_U := R.isOpen_subU hA
  isConnected_U := R.isConnected_subU
  mem_U := R.mem_subU
  Φ := R.subΦ hA
  Γ := R.subΓ hA
  isScDiffeoOn_Φ g :=
    { isScSmoothOn := R.isScSmoothOn_subΦ hA g
      isScSmoothOn_inv := R.isScSmoothOn_subΦ hA g⁻¹
      mapsTo := R.mapsTo_subΦ hA g
      mapsTo_inv := R.mapsTo_subΦ hA g⁻¹
      left_inv := fun y hy => Subtype.ext <| by
        have hy' := R.subU_subset hy
        rw [R.subΦ_val hA _ (R.subU_subset (R.mapsTo_subΦ hA g hy)), R.subΦ_val hA _ hy',
          map_inv, ← R.Φ_mul _ _ _ hy', inv_mul_cancel, R.Φ_one _ hy']
      right_inv := fun y hy => Subtype.ext <| by
        have hy' := R.subU_subset hy
        rw [R.subΦ_val hA _ (R.subU_subset (R.mapsTo_subΦ hA g⁻¹ hy)), R.subΦ_val hA _ hy',
          map_inv, ← R.Φ_mul _ _ _ hy', mul_inv_cancel, R.Φ_one _ hy'] }
  Φ_mul g h y hy := Subtype.ext <| by
    have hy' := R.subU_subset hy
    rw [R.subΦ_val hA _ hy', R.subΦ_val hA _ (R.subU_subset (R.mapsTo_subΦ hA h hy)),
      R.subΦ_val hA _ hy', map_mul, R.Φ_mul _ _ _ hy']
  isScSmoothOn_Γ g := by
    refine MPolyfold.isScSmoothOn_sub_of_val (X.isSubMPolyfold_morOn hA) ?_
    refine ((R.isScSmoothOn_Γ (subIsotropyEquiv hA a g)).comp
      ((MPolyfold.subPolyfold_inclusion_isScSmooth hA.isSubMPolyfold).mono (R.isOpen_subU hA)
        (subset_univ _)) fun _ hy => R.subU_subset hy).congr fun y hy => ?_
    exact (R.subΓ_val hA g (R.subU_subset hy)).symm
  Γ_self g := Subtype.ext <| (R.subΓ_val hA g R.mem_U).trans (R.Γ_self _)
  src_Γ g y hy := Subtype.ext <| by
    change X.src (R.subΓ hA g y : Mor) = y
    rw [R.subΓ_val hA g (R.subU_subset hy), R.src_Γ _ _ (R.subU_subset hy)]
  tgt_Γ g y hy := Subtype.ext <| by
    change X.tgt (R.subΓ hA g y : Mor) = (R.subΦ hA g y : Obj)
    rw [R.subΓ_val hA g (R.subU_subset hy), R.tgt_Γ _ _ (R.subU_subset hy),
      R.subΦ_val hA g (R.subU_subset hy)]
  existsUnique_Γ h hs ht := by
    have hs' : X.src (h : Mor) ∈ R.U := R.subU_subset hs
    have ht' : X.tgt (h : Mor) ∈ R.U := R.subU_subset ht
    obtain ⟨g₀, hg₀, huniq⟩ := R.existsUnique_Γ h hs' ht'
    refine ⟨(subIsotropyEquiv hA a).symm g₀, Subtype.ext ?_, fun g' hg' => ?_⟩
    · change (R.subΓ hA _ ⟨X.src (h : Mor), h.2.1⟩ : Mor) = h
      rw [R.subΓ_val hA _ hs', MulEquiv.apply_symm_apply]
      exact hg₀
    · have e : R.Γ (subIsotropyEquiv hA a g') (X.src (h : Mor)) = h := by
        rw [← R.subΓ_val hA g' (y := ⟨X.src (h : Mor), h.2.1⟩) hs']
        exact congrArg Subtype.val hg'
      rw [← huniq _ e, MulEquiv.symm_apply_apply]

@[simp] theorem sub_U : (R.sub hA).U = R.subU := rfl

theorem sub_Φ_val (g : (subEpGroupoid hA).Isotropy a) {y : A} (hy : (y : Obj) ∈ R.U) :
    ((R.sub hA).Φ g y : Obj) = R.Φ (subIsotropyEquiv hA a g) y :=
  R.subΦ_val hA g hy

theorem sub_Γ_val (g : (subEpGroupoid hA).Isotropy a) {y : A} (hy : (y : Obj) ∈ R.U) :
    ((R.sub hA).Γ g y : Mor) = R.Γ (subIsotropyEquiv hA a g) y :=
  R.subΓ_val hA g hy

include hA in
/-- The domain of the restriction is `val⁻¹(O)` for an open `O ∋ a` of `X`. -/
theorem exists_isOpen_preimage_eq_subU :
    ∃ O : Set Obj, IsOpen O ∧ (a : Obj) ∈ O ∧ (↑) ⁻¹' O = R.subU := by
  obtain ⟨O, hO, e⟩ := isOpen_induced_iff.1 (R.isOpen_subU hA)
  exact ⟨O, hO, by
    have : a ∈ (↑) ⁻¹' O := e.symm ▸ R.mem_subU
    exact this, e⟩

end NaturalRep

namespace NatNbhd

variable {a : A}

/-- **A neighbourhood with the natural action of `X` is one of `A`**, when `U ∩ A` lies in the
connected component of `a` in `U(rep) ∩ A`. -/
def sub (N : X.NatNbhd (a : Obj)) (hN : (↑) ⁻¹' N.U ⊆ N.rep.subU) :
    (subEpGroupoid hA).NatNbhd a where
  rep := N.rep.sub hA
  U := (↑) ⁻¹' N.U
  isOpen_U := N.isOpen_U.preimage continuous_subtype_val
  mem_U := show a ∈ ((↑) ⁻¹' N.U : Set A) from N.mem_U
  U_subset := hN
  mapsTo_Φ g y hy := by
    change ((N.rep.sub hA).Φ g y : Obj) ∈ N.U
    rw [N.rep.sub_Φ_val hA g (N.U_subset hy)]
    exact N.mapsTo_Φ _ hy

@[simp] theorem sub_U (N : X.NatNbhd (a : Obj)) (hN : (↑) ⁻¹' N.U ⊆ N.rep.subU) :
    (N.sub hA hN).U = (↑) ⁻¹' N.U := rfl

@[simp] theorem sub_rep (N : X.NatNbhd (a : Obj)) (hN : (↑) ⁻¹' N.U ⊆ N.rep.subU) :
    (N.sub hA hN).rep = N.rep.sub hA := rfl

end NatNbhd

end EpGroupoid

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}} {ι : IndexFamily A}

namespace FaceStructuredTuple

/-- **The neighbourhoods `U_F(x)` form a good system for the ep-groupoid `F`, up to
equivalence, condition (2) in the strict sense** (§14.6, p. 680): for a face `F = X_θ` of a tame
face-structured `X` with paracompact `|X|`, every face tuple is equivalent to one (same `Λ`,
sections and `τ`) for which there is a good system `𝒢` of the ep-groupoid `F` with
`U_𝒢(x) = U_F(x)` and whose natural representations are those of the tuple restricted to `F`. -/
theorem exists_equiv_faceGoodSystem (hX : A.X.IsEpFaceStructured)
    (hpara : A.X.HasParacompactOrbitSpace) {θ : Set A.X.OrbitSpace}
    (hθ : A.X.IsOrbitFace θ) (T : FaceStructuredTuple A (A.X.faceObj θ) ι) :
    ∃ T' : FaceStructuredTuple A (A.X.faceObj θ) ι, T.toRelTuple.Equiv T'.toRelTuple ∧
      T'.Λ = T.Λ ∧ T'.s = T.s ∧ T'.τ = T.τ ∧
      ∃ 𝒢 : (faceEpGroupoid hX hθ).GoodSystem, ∀ x : A.X.faceObj θ,
        (𝒢.nbhd x).U = (↑) ⁻¹' (T'.nbhd x).U ∧
        (𝒢.nbhd x).rep = (T'.nbhd x).rep.sub (isEpSubgroupoid_faceObj hX hθ) := by
  set hF := isEpSubgroupoid_faceObj hX hθ
  obtain ⟨𝒢₀, -⟩ := A.X.theorem_13_1_8 hpara (fun _ => univ) (fun _ => isOpen_univ)
    (fun _ => mem_univ _)
  choose O hO hxO hOe using fun x : A.X.faceObj θ =>
    (T.nbhd x).rep.exists_isOpen_preimage_eq_subU hF (a := x)
  classical
  let W : A.Obj → Set A.Obj := fun y =>
    if h : y ∈ A.X.faceObj θ then 𝒢₀.U y ∩ O ⟨y, h⟩ else 𝒢₀.U y
  have hW : ∀ y, IsOpen (W y) := fun y => by
    by_cases h : y ∈ A.X.faceObj θ
    · simp only [W, dif_pos h]; exact (𝒢₀.nbhd y).isOpen_U.inter (hO _)
    · simp only [W, dif_neg h]; exact (𝒢₀.nbhd y).isOpen_U
  have hxW : ∀ y, y ∈ W y := fun y => by
    by_cases h : y ∈ A.X.faceObj θ
    · simp only [W, dif_pos h]; exact ⟨(𝒢₀.nbhd y).mem_U, hxO _⟩
    · simp only [W, dif_neg h]; exact (𝒢₀.nbhd y).mem_U
  have hWx : ∀ x : A.X.faceObj θ, W x = 𝒢₀.U x ∩ O x := fun x => by
    simp only [W, dif_pos x.2]
  set T' := T.shrink W hW hxW
  have hsub : ∀ x : A.X.faceObj θ, (T'.nbhd x).U ⊆ (T.nbhd x).U ∩ (𝒢₀.U x ∩ O x) :=
    fun x => hWx x ▸ T.toRelTuple.shrink_nbhd_U_subset W hW hxW x
  have hrep : ∀ x : A.X.faceObj θ, (T'.nbhd x).rep = (T.nbhd x).rep := fun _ => rfl
  have hN : ∀ x : A.X.faceObj θ, (↑) ⁻¹' (T'.nbhd x).U ⊆ (T'.nbhd x).rep.subU := fun x y hy => by
    rw [hrep, ← hOe x]
    exact (hsub x hy).2.2
  refine ⟨T', T.toRelTuple.equiv_shrink _ hW hxW, rfl, rfl, rfl,
    ⟨fun x => (T'.nbhd x).sub hF (hN x), fun x => ?_, fun x x' φ hφ => ?_⟩,
    fun x => ⟨rfl, rfl⟩⟩
  · exact EpGroupoid.isProperSubset_face hX hθ (T'.isProper x)
  · refine EpGroupoid.isDiffeoComponent_face hX hθ (NatNbhd.isOpen_U _) (NatNbhd.isOpen_U _)
      (fun ψ hψ => ?_) φ hφ
    exact 𝒢₀.isDiffeoComponent_of_subset (x := x) (x' := x') (NatNbhd.isOpen_U _)
      (NatNbhd.isOpen_U _) (fun _ hy => (hsub x hy).2.1) (fun _ hy => (hsub x' hy).2.1) hψ

end FaceStructuredTuple

/-- **On classes** (§14.6, p. 680): every structured sc⁺-multisection on `W|F`, `F = X_θ`, has a
representative and a good system `𝒢` of the ep-groupoid `F` (Definition 13.1.4, conditions
(1)–(3)) with `U_𝒢(x) = U_F(x) = U(x) ∩ F`; the natural representation of `𝒢` at `x` is that of
the representative restricted to `F` (`NaturalRep.sub`: its action and `Γ` are those of `X`). -/
theorem FaceStructuredMultisection.exists_rep_faceGoodSystem (hX : A.X.IsEpFaceStructured)
    (hpara : A.X.HasParacompactOrbitSpace) {θ : Set A.X.OrbitSpace} (hθ : A.X.IsOrbitFace θ)
    (L : FaceStructuredMultisection A (A.X.faceObj θ)) :
    ∃ T : Σ ι : IndexFamily A, FaceStructuredTuple A (A.X.faceObj θ) ι, ⟦T⟧ = L ∧
      ∃ 𝒢 : (faceEpGroupoid hX hθ).GoodSystem, ∀ x : A.X.faceObj θ,
        (𝒢.nbhd x).U = (↑) ⁻¹' (T.2.nbhd x).U ∧
        (𝒢.nbhd x).rep = (T.2.nbhd x).rep.sub (isEpSubgroupoid_faceObj hX hθ) := by
  obtain ⟨⟨ι, T₀⟩, rfl⟩ := Quotient.exists_rep L
  obtain ⟨T', hT', -, -, -, h𝒢⟩ := T₀.exists_equiv_faceGoodSystem hX hpara hθ
  exact ⟨⟨ι, T'⟩, Quotient.sound (s := FaceStructuredTuple.setoid A _) hT'.symm, h𝒢⟩

end SBLocalization

end Polyfold
