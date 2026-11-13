import Polyfold.Chapter14.FaceStructured

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.6, p. 682:
**Theorem 14.6.3** (2017: Theorem 14.4): compatible structured sc⁺-multisections on the faces
define a structured sc⁺-multisection over `∂X`, which extends by Theorem 14.1.9.

# Assembling face-wise structured multisections

## The text, paraphrased

(Theorem 14.6.3) Let `P : W → X` be a strong bundle over a tame face-structured ep-groupoid and
`F ↦ Λ̃_F` a compatible assignment.  Then the data define a structured `Λ̃ : W|∂X → ℚ⁺`; the
underlying `Λ` extends to `W`, with size restrictions (Theorem 14.1.9).  *Proof*: `Λ(w) := Λ_F(w)`
for `P(w) ∈ F` is a well-defined functor.  Fix representatives `(Λ_F, 𝒰_F, S_F, τ_F)`; for
`x ∈ ∂X` take a good `V(x)` with `U(x) ∩ F ⊆ U_F(x)` for the faces `F ∋ x`; since
`sˣ_{F,i} = sˣ_{F',i}` on `U(x) ∩ F ∩ F'`, `sˣᵢ(y) := sˣ_{F,i}(y)` for `y ∈ F ∩ U(x)` is a
symmetric sc⁺-structure on `U(x)`.  For `φ` with `s(φ) ∈ F ∩ U(x)`, `t(φ) ∈ F ∩ U(x')`, put
`τ_{x,x'}(φ) := τ_{F,x,x'}(φ)`, well defined since `τ_F = τ_{F'}` on `F ∩ F'`; it is locally
constant and relates the structures.  Apply Theorem 14.1.9.

## What is formalized

* `CompatibleFaceData A`: the input of the text's proof, the **chosen representatives**: one
  index family `I_x` (the text's "`I_x := I^F_x`"), for every face `F` a
  `FaceStructuredTuple A F ι`, with `Λ_F = Λ_{F'}`, `sˣ_{F,i} = sˣ_{F',i}` and
  `τ_{F,x,x'} = τ_{F',x,x'}` on `F ∩ F'` (on `U_F ∩ U_{F'}`).
  `CompatibleFaceData.isCompatibleAssignment`: such data is a compatible assignment in the sense
  of Definition 14.6.2.
* `CompatibleFaceData.Λg`, `.sg`, `.τg`: the glued functor, sections and correspondences;
  `CompatibleFaceData.exists_adapted` (the good system for `∂X` with `U(x) ∩ F ⊆ U_F(x)` and the
  natural actions of the faces), `CompatibleFaceData.glue` (the structured `Λ̃` over `∂X`, a
  `BoundaryStructuredTuple`).
* **Theorem 14.6.3**: `theorem_14_6_3_hyp` (`Λ` is structurable over `∂X` and restricts to the
  `Λ_F`; the structure restricts to the given ones: `glue_U_inter_subset`, `glue_s`, `glue_τ`)
  and `theorem_14_6_3_extension_hyp` (the extension with the size control of Theorem 14.1.9,
  from `theorem_14_1_9_statement`).
* Nonvacuity: `CompatibleFaceData.zero` (the zero multisection on every face, one index family
  `I_x = {∗}`), with `CompatibleFaceData.zero_Λg` (the glued `Λ` is the zero multisection over
  `∂X`).

## Hypotheses and readings

* The text says "it follows from the compatibility condition that `sˣ_{F,i} = sˣ_{F',i}` on
  `U_F(x) ∩ U_{F'}(x)`".  The equivalence of structured multisections (Definition 13.3.8 and its
  analogue here, `RelTuple.Equiv`) compares `Λ`, the index sets and the correspondences, not the
  sections, so we take the agreement of the chosen representatives (sections and
  correspondences, on one index family) as the hypothesis `CompatibleFaceData`; it implies the
  compatibility of Definition 14.6.2 (`CompatibleFaceData.isCompatibleAssignment`).
* `|X|` paracompact (the chapter's standing assumption) is used for the good system for `∂X`
  (Theorem 14.1.6, `theorem_14_1_6_hyp`).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- A face `X_θ` is saturated: `s(φ) ∈ F ↔ t(φ) ∈ F`. -/
theorem IsEpFace.tgt_mem_iff {F : Set Obj} (hF : X.IsEpFace F) (φ : Mor) :
    X.tgt φ ∈ F ↔ X.src φ ∈ F := by
  obtain ⟨θ, -, rfl⟩ := hF
  change X.π (X.tgt φ) ∈ θ ↔ X.π (X.src φ) ∈ θ
  rw [X.π_src_eq_π_tgt φ]

theorem IsEpFace.tgt_mem {F : Set Obj} (hF : X.IsEpFace F) {φ : Mor} (h : X.src φ ∈ F) :
    X.tgt φ ∈ F := (hF.tgt_mem_iff φ).2 h

theorem IsEpFace.Φ_mem {F : Set Obj} (hF : X.IsEpFace F) {x : Obj} (N : X.NatNbhd x)
    (g : X.Isotropy x) {y : Obj} (hy : y ∈ N.U) (hyF : y ∈ F) : N.rep.Φ g y ∈ F := by
  rw [← N.tgt_Γ g hy]
  exact hF.tgt_mem (by rw [N.src_Γ g hy]; exact hyF)

end EpGroupoid

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-- **The chosen representatives of a compatible assignment** (the input of the proof of
Theorem 14.6.3): one index family, a representative `(Λ_F, 𝒰_F, S_F, τ_F)` on every face, and the
agreement of `Λ`, the sections and the correspondences on the intersections of faces. -/
structure CompatibleFaceData (A : SEP.{u}) where
  /-- The index sets `I_x` (the text's `I_x := I^F_x`). -/
  ι : IndexFamily A
  /-- The representatives `(Λ_F, 𝒰_F, S_F, τ_F)`. -/
  T : ∀ F, A.X.IsEpFace F → FaceStructuredTuple A F ι
  Λ_eq : ∀ F hF F' hF' w, A.P w ∈ F ∩ F' → (T F hF).Λ w = (T F' hF').Λ w
  s_eq : ∀ F hF F' hF' (x : A.Obj) (hx : x ∈ F) (hx' : x ∈ F') i,
    ∀ y ∈ (T F hF).U ⟨x, hx⟩ ∩ (T F' hF').U ⟨x, hx'⟩, (T F hF).s x i y = (T F' hF').s x i y
  τ_eq : ∀ F hF F' hF' (x : A.Obj) (hx : x ∈ F) (hx' : x ∈ F') (x' : A.Obj) (hx₂ : x' ∈ F)
    (hx₂' : x' ∈ F'), ∀ φ ∈ A.X.morBetween ((T F hF).U ⟨x, hx⟩ ∩ (T F' hF').U ⟨x, hx'⟩)
      ((T F hF).U ⟨x', hx₂⟩ ∩ (T F' hF').U ⟨x', hx₂'⟩), (T F hF).τ x x' φ = (T F' hF').τ x x' φ

namespace CompatibleFaceData

variable (D : CompatibleFaceData A)

/-- **The chosen representatives form a compatible assignment** (Definition 14.6.2). -/
theorem isCompatibleAssignment :
    IsCompatibleAssignment fun F hF =>
      Quotient.mk (FaceStructuredTuple.setoid A F) ⟨D.ι, D.T F hF⟩ := by
  intro F hF F' hF'
  refine Quotient.sound ⟨fun w hw => D.Λ_eq F hF F' hF' w hw,
    fun x => ((D.T F hF).nbhd ⟨x, x.2.1⟩).U ∩ ((D.T F' hF').nbhd ⟨x, x.2.2⟩).U,
    fun x => ((D.T F hF).nbhd _).isOpen_U.inter ((D.T F' hF').nbhd _).isOpen_U,
    fun x => ⟨((D.T F hF).nbhd _).mem_U, ((D.T F' hF').nbhd _).mem_U⟩,
    fun x y hy => ⟨⟨hy.1.1, hy.2⟩, ⟨hy.1.2, hy.2⟩⟩, fun _ => rfl, fun x x' φ hφ => ?_⟩
  change (D.T F' hF').τ x x' φ = ((D.T F hF).τ x x' φ).map _ _
  rw [IndexCorr.map_cast_rfl]
  exact (D.τ_eq F hF F' hF' x x.2.1 x.2.2 x' x'.2.1 x'.2.2 φ
    ⟨⟨⟨hφ.1.1.1, hφ.1.2.1⟩, ⟨hφ.1.1.2, hφ.1.2.2⟩⟩,
      ⟨⟨hφ.2.1.1, hφ.2.2.1⟩, ⟨hφ.2.1.2, hφ.2.2.2⟩⟩⟩).symm

/-! ### The glued functor, sections and correspondences -/

/-- **`Λ(w) := Λ_F(w)` for `P(w) ∈ F`** (`0` off `∂X`). -/
def Λg (w : A.W) : ℚ≥0 :=
  if h : ∃ F, A.X.IsEpFace F ∧ A.P w ∈ F then (D.T h.choose h.choose_spec.1).Λ w else 0

theorem Λg_eq {F : Set A.Obj} (hF : A.X.IsEpFace F) {w : A.W} (hw : A.P w ∈ F) :
    D.Λg w = (D.T F hF).Λ w := by
  have h : ∃ F, A.X.IsEpFace F ∧ A.P w ∈ F := ⟨F, hF, hw⟩
  rw [Λg, dif_pos h]
  exact D.Λ_eq _ _ _ _ w ⟨h.choose_spec.2, hw⟩

variable (hX : A.X.IsEpFaceStructured)

/-- A face through `y`, `x` and `x'` if there is one, else a face through `x ∈ ∂X`. -/
def faceSel (x : A.X.PObj.boundary) (y x' : A.Obj) : {F // A.X.IsEpFace F} :=
  if h : ∃ F, A.X.IsEpFace F ∧ y ∈ F ∧ (x : A.Obj) ∈ F ∧ x' ∈ F then ⟨h.choose, h.choose_spec.1⟩
  else ⟨(exists_isEpFace_mem hX x.2).choose, (exists_isEpFace_mem hX x.2).choose_spec.1⟩

theorem faceSel_spec {x : A.X.PObj.boundary} {y x' : A.Obj}
    (h : ∃ F, A.X.IsEpFace F ∧ y ∈ F ∧ (x : A.Obj) ∈ F ∧ x' ∈ F) :
    y ∈ (faceSel hX x y x').1 ∧ (x : A.Obj) ∈ (faceSel hX x y x').1 ∧
      x' ∈ (faceSel hX x y x').1 := by
  rw [faceSel, dif_pos h]
  exact h.choose_spec.2

/-- **`sˣᵢ(y) := sˣ_{F,i}(y)` for `y ∈ F`.** -/
def sg (x : A.X.PObj.boundary) (i : D.ι.I x) (y : A.Obj) : A.W :=
  (D.T (faceSel hX x y x).1 (faceSel hX x y x).2).s x i y

/-- **`τ_{x,x'}(φ) := τ_{F,x,x'}(φ)` for `s(φ) ∈ F`.** -/
def τg (x x' : A.X.PObj.boundary) (φ : A.Mor) : IndexCorr (D.ι.I x) (D.ι.I x') :=
  (D.T (faceSel hX x (A.X.src φ) x').1 (faceSel hX x (A.X.src φ) x').2).τ x x' φ

/-- **A good system for `∂X` adapted to the faces**: near `x`, every face through a point of
`V(x)` contains `x`, `V(x) ⊆ V_F(x)` for the faces `F ∋ x`, and the natural action on `V(x)` is
that of every `V_F(x)`. -/
def Adapted (𝒲 : A.X.BoundaryGoodSystem) : Prop :=
  ∀ x : A.X.PObj.boundary, ∀ y ∈ (𝒲.nbhd x).U, (∀ F, A.X.IsEpFace F → y ∈ F → (x : A.Obj) ∈ F) ∧
    ∀ F (hF : A.X.IsEpFace F) (hxF : (x : A.Obj) ∈ F), y ∈ ((D.T F hF).nbhd ⟨x, hxF⟩).U ∧
      ∀ g, (𝒲.nbhd x).rep.Γ g y = ((D.T F hF).nbhd ⟨x, hxF⟩).rep.Γ g y

/-- **Adapted good systems exist** (the text's choice of `V(x)` with `U(x) ∩ F ⊆ U_F(x)`): a good
system for `∂X` (Theorem 14.1.6), shrunk inside the common refinement of the `V_F(x)`, `F ∋ x`
(finitely many faces; `NatNbhd.exists_le_of_finite`) and inside the neighbourhood of `x` where
every face through a point contains `x` (`eventually_mem_of_isEpFace`). -/
theorem exists_adapted (hX : A.X.IsEpFaceStructured) (hpara : A.X.HasParacompactOrbitSpace) :
    ∃ 𝒲 : A.X.BoundaryGoodSystem, D.Adapted 𝒲 := by
  obtain ⟨𝒰₀, -⟩ := A.X.theorem_14_1_6_hyp hX.1 hpara (fun _ => univ) (fun _ => isOpen_univ)
    (fun _ => mem_univ _)
  have hO : ∀ x : A.X.PObj.boundary, ∃ O : Set A.Obj, IsOpen O ∧ (x : A.Obj) ∈ O ∧
      ∀ y ∈ O, ∀ F, A.X.IsEpFace F → y ∈ F → (x : A.Obj) ∈ F := fun x => by
    obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.1 (eventually_mem_of_isEpFace hX (x : A.Obj))
    exact ⟨t, hto, hxt, fun y hy => ht hy⟩
  choose O hOo hxO hOF using hO
  have hM : ∀ x : A.X.PObj.boundary, ∃ M : A.X.NatNbhd x, M.U ⊆ O x ∧ M.Le (𝒰₀.nbhd x) ∧
      ∀ F (hF : A.X.IsEpFace F) (hxF : (x : A.Obj) ∈ F), M.Le ((D.T F hF).nbhd ⟨x, hxF⟩) := by
    intro x
    have : Finite {F // A.X.IsEpFace F ∧ (x : A.Obj) ∈ F} :=
      (finite_isEpFace_mem hX (x : A.Obj)).to_subtype
    obtain ⟨M, -, hMO, hM₀, hMF⟩ := NatNbhd.exists_le_of_finite (𝒰₀.nbhd x)
      (fun F : {F // A.X.IsEpFace F ∧ (x : A.Obj) ∈ F} => (D.T F.1 F.2.1).nbhd ⟨x, F.2.2⟩)
      (hOo x) (hxO x)
    exact ⟨M, hMO, hM₀, fun F hF hxF => hMF ⟨F, hF, hxF⟩⟩
  choose M hMO hM₀ hMF using hM
  obtain ⟨𝒲, h𝒲₀, h𝒲M⟩ := 𝒰₀.exists_refinement hX.1 (fun x => (M x).U)
    (fun x => (M x).isOpen_U) (fun x => (M x).mem_U)
  refine ⟨𝒲, fun x y hy => ⟨hOF x y (hMO x (h𝒲M x hy)), fun F hF hxF => ⟨?_, fun g => ?_⟩⟩⟩
  · exact (hMF x F hF hxF).subset (h𝒲M x hy)
  · rw [(h𝒲₀ x).Γ_eq g y hy, ← (hM₀ x).Γ_eq g y (h𝒲M x hy),
      (hMF x F hF hxF).Γ_eq g y (h𝒲M x hy)]

/-! ### The glued data agree with the face data -/

section Adapted

variable {D hX} {𝒲 : A.X.BoundaryGoodSystem} (h𝒲 : D.Adapted 𝒲)
include h𝒲

/-- On `U(x) ∩ F`, `sˣᵢ = sˣ_{F,i}`. -/
theorem sg_eq {x : A.X.PObj.boundary} {y : A.Obj} (hy : y ∈ (𝒲.nbhd x).U) {F : Set A.Obj}
    (hF : A.X.IsEpFace F) (hyF : y ∈ F) (i : D.ι.I x) :
    D.sg hX x i y = (D.T F hF).s x i y := by
  have hxF := (h𝒲 x y hy).1 F hF hyF
  have hex : ∃ G, A.X.IsEpFace G ∧ y ∈ G ∧ (x : A.Obj) ∈ G ∧ (x : A.Obj) ∈ G :=
    ⟨F, hF, hyF, hxF, hxF⟩
  obtain ⟨hyG, hxG, -⟩ := faceSel_spec hX hex
  set G := faceSel hX x y x with hG
  exact D.s_eq G.1 G.2 F hF x hxG hxF i y
    ⟨⟨((h𝒲 x y hy).2 G.1 G.2 hxG).1, hyG⟩, ⟨((h𝒲 x y hy).2 F hF hxF).1, hyF⟩⟩

/-- A morphism of `𝒰(x, x')` with source on `F` is a morphism of `𝒰_F(x, x')`. -/
theorem mem_mor_face {x x' : A.X.PObj.boundary} {φ : A.Mor}
    (hφ : φ ∈ A.X.morBetween (𝒲.nbhd x).U (𝒲.nbhd x').U) {F : Set A.Obj}
    (hF : A.X.IsEpFace F) (hsF : A.X.src φ ∈ F) :
    ∃ (hxF : (x : A.Obj) ∈ F) (hx'F : (x' : A.Obj) ∈ F),
      φ ∈ A.X.morBetween ((D.T F hF).U ⟨x, hxF⟩) ((D.T F hF).U ⟨x', hx'F⟩) := by
  have htF := hF.tgt_mem hsF
  have hxF := (h𝒲 x _ hφ.1).1 F hF hsF
  have hx'F := (h𝒲 x' _ hφ.2).1 F hF htF
  exact ⟨hxF, hx'F, ⟨((h𝒲 x _ hφ.1).2 F hF hxF).1, hsF⟩,
    ⟨((h𝒲 x' _ hφ.2).2 F hF hx'F).1, htF⟩⟩

/-- On `𝒰(x, x')`, `τ_{x,x'} = τ_{F,x,x'}` for every face `F` through `s(φ)`. -/
theorem τg_eq {x x' : A.X.PObj.boundary} {φ : A.Mor}
    (hφ : φ ∈ A.X.morBetween (𝒲.nbhd x).U (𝒲.nbhd x').U) {F : Set A.Obj}
    (hF : A.X.IsEpFace F) (hsF : A.X.src φ ∈ F) :
    D.τg hX x x' φ = (D.T F hF).τ x x' φ := by
  obtain ⟨hxF, hx'F, hφF⟩ := D.mem_mor_face h𝒲 hφ hF hsF
  have hex : ∃ G, A.X.IsEpFace G ∧ A.X.src φ ∈ G ∧ (x : A.Obj) ∈ G ∧ (x' : A.Obj) ∈ G :=
    ⟨F, hF, hsF, hxF, hx'F⟩
  obtain ⟨hsG, hxG, hx'G⟩ := faceSel_spec hX hex
  set G := faceSel hX x (A.X.src φ) x' with hG
  obtain ⟨hxG', hx'G', hφG⟩ := D.mem_mor_face h𝒲 hφ G.2 hsG
  exact D.τ_eq G.1 G.2 F hF x hxG' hxF x' hx'G' hx'F φ ⟨⟨hφG.1, hφF.1⟩, ⟨hφG.2, hφF.2⟩⟩

/-- The natural actions on `V(x)` and `V_F(x)` agree on `V(x)`. -/
theorem Φ_eq {x : A.X.PObj.boundary} {y : A.Obj} (hy : y ∈ (𝒲.nbhd x).U) {F : Set A.Obj}
    (hF : A.X.IsEpFace F) (hxF : (x : A.Obj) ∈ F) (g : A.X.Isotropy x) :
    (𝒲.nbhd x).rep.Φ g y = ((D.T F hF).nbhd ⟨x, hxF⟩).rep.Φ g y := by
  rw [← (𝒲.nbhd x).tgt_Γ g hy, ((h𝒲 x y hy).2 F hF hxF).2 g,
    ((D.T F hF).nbhd ⟨x, hxF⟩).tgt_Γ g ((h𝒲 x y hy).2 F hF hxF).1]

end Adapted

/-! ### The structure over `∂X` -/

section Glue

variable {D hX} {𝒲 : A.X.BoundaryGoodSystem} (h𝒲 : D.Adapted 𝒲)

variable (D hX) in
/-- **The symmetric sc⁺-section structure `sˣ = (sˣᵢ)_{i ∈ I_x}` on `U(x)`** (proof of
Theorem 14.6.3): `sˣᵢ(y) := sˣ_{F,i}(y)` for `y ∈ F ∩ U(x)`. -/
def S (x : A.X.PObj.boundary) : BoundarySymmetricStructure A D.Λg (𝒲.nbhd x) where
  I := D.ι.I x
  s := D.sg hX x
  isFaceScPlus i := by
    refine isFaceScPlusSectionOn_of_local (fun y hy => ?_) fun y hy F hF hyF => ?_
    · obtain ⟨F, hF, hyF⟩ := exists_isEpFace_mem hX hy.2
      have hxF := (h𝒲 x y hy.1).1 F hF hyF
      rw [D.sg_eq h𝒲 hy.1 hF hyF]
      exact ((D.T F hF).isFaceRelScPlus ⟨x, hxF⟩ i).1 y ⟨((h𝒲 x y hy.1).2 F hF hxF).1, hyF⟩
    · have hxF := (h𝒲 x y hy.1).1 F hF hyF
      refine ⟨(D.T F hF).s x i, (𝒲.nbhd x).U, (𝒲.nbhd x).isOpen_U, hy.1,
        ((D.T F hF).isFaceRelScPlus ⟨x, hxF⟩ i).mono ?_, fun z hz => D.sg_eq h𝒲 hz.2 hF hz.1 i⟩
      intro z hz
      rw [mem_singleton_iff.1 hz]
      exact ⟨((h𝒲 x y hy.1).2 F hF hxF).1, hyF⟩
  equivariant g i y hy := by
    obtain ⟨F, hF, hyF⟩ := exists_isEpFace_mem hX hy.2
    have hxF := (h𝒲 x y hy.1).1 F hF hyF
    have hyU := ((h𝒲 x y hy.1).2 F hF hxF).1
    have hΦF : (𝒲.nbhd x).rep.Φ g y ∈ F := hF.Φ_mem (𝒲.nbhd x) g hy.1 hyF
    rw [D.sg_eq h𝒲 ((𝒲.nbhd x).Φ_mem g hy.1) hF hΦF, D.sg_eq h𝒲 hy.1 hF hyF,
      D.Φ_eq h𝒲 hy.1 hF hxF g, ((h𝒲 x y hy.1).2 F hF hxF).2 g]
    exact (D.T F hF).equivariant ⟨x, hxF⟩ g i y ⟨hyU, hyF⟩
  rep w hw := by
    obtain ⟨F, hF, hwF⟩ := exists_isEpFace_mem hX hw.2
    have hxF := (h𝒲 x _ hw.1).1 F hF hwF
    rw [D.Λg_eq hF hwF, (D.T F hF).rep ⟨x, hxF⟩ w ⟨((h𝒲 x _ hw.1).2 F hF hxF).1, hwF⟩]
    congr 3
    exact Finset.filter_congr fun i _ => by rw [D.sg_eq h𝒲 hw.1 hF hwF]

variable (D hX) in
/-- The decoration `(𝒰, S)` over `∂X`. -/
def dec : BoundaryDecoration A D.Λg := ⟨𝒲, S D hX h𝒲⟩

variable (D hX) in
/-- **The correspondences `τ_{x,x'}(φ) := τ_{F,x,x'}(φ)`** for `s(φ) ∈ F` (proof of
Theorem 14.6.3), with (2), (a)–(c) and (4) of Definition 14.1.7. -/
def tau : (dec D hX h𝒲).Tau where
  τ := D.τg hX
  locallyConstant x x' φ hφ := by
    have hφ' := 𝒲.mor_subset x x' hφ
    have h1 : ∀ᶠ ψ in 𝓝 φ, ∀ F, A.X.IsEpFace F → A.X.src ψ ∈ F → A.X.src φ ∈ F :=
      (A.X.continuous_src.tendsto φ).eventually (eventually_mem_of_isEpFace hX (A.X.src φ))
    have h2 : ∀ F ∈ {F | A.X.IsEpFace F ∧ A.X.src φ ∈ F}, ∀ᶠ ψ in 𝓝 φ,
        ∀ hF : A.X.IsEpFace F, ψ ∈ 𝒲.mor x x' → A.X.src ψ ∈ F →
          (D.T F hF).τ x x' ψ = (D.T F hF).τ x x' φ := by
      rintro F ⟨hF, hsF⟩
      obtain ⟨hxF, hx'F, hφF⟩ := D.mem_mor_face h𝒲 hφ' hF hsF
      filter_upwards [eventually_nhdsWithin_iff.1
        ((D.T F hF).locallyConstant ⟨x, hxF⟩ ⟨x', hx'F⟩ φ hφF)] with ψ hψ _ hψ𝒲 hsψ
      obtain ⟨hxF', hx'F', hψF⟩ := D.mem_mor_face h𝒲 (𝒲.mor_subset x x' hψ𝒲) hF hsψ
      exact hψ hψF
    have h3 := ((finite_isEpFace_mem hX (A.X.src φ)).eventually_all).2 h2
    rw [eventually_nhdsWithin_iff]
    filter_upwards [h1, h3] with ψ hψ1 hψ3 hψ
    obtain ⟨G, hG, hsG⟩ := exists_isEpFace_mem hX hψ.1.2
    have hsφG := hψ1 G hG hsG
    change D.τg hX x x' ψ = D.τg hX x x' φ
    rw [D.τg_eq h𝒲 (𝒲.mor_subset x x' hψ) hG hsG, D.τg_eq h𝒲 hφ' hG hsφG]
    exact hψ3 G ⟨hG, hsφG⟩ hG hψ hsG
  finite x x' := by
    have : Finite {F // A.X.IsEpFace F ∧ (x : A.Obj) ∈ F ∧ (x' : A.Obj) ∈ F} :=
      ((finite_isEpFace_mem hX (x : A.Obj)).subset fun F hF => ⟨hF.1, hF.2.1⟩).to_subtype
    refine (finite_iUnion fun F : {F // A.X.IsEpFace F ∧ (x : A.Obj) ∈ F ∧ (x' : A.Obj) ∈ F} =>
      (D.T F.1 F.2.1).finite ⟨x, F.2.2.1⟩ ⟨x', F.2.2.2⟩).subset ?_
    rintro _ ⟨ψ, hψ, rfl⟩
    obtain ⟨G, hG, hsG⟩ := exists_isEpFace_mem hX hψ.1.2
    have hψ' := 𝒲.mor_subset x x' hψ
    obtain ⟨hxG, hx'G, hψG⟩ := D.mem_mor_face h𝒲 hψ' hG hsG
    exact mem_iUnion.2 ⟨⟨G, hG, hxG, hx'G⟩, ψ, hψG, (D.τg_eq h𝒲 hψ' hG hsG).symm⟩
  swap x x' φ hφ := by
    have hφ' := 𝒲.mor_subset x x' hφ
    obtain ⟨F, hF, hsF⟩ := exists_isEpFace_mem hX hφ.1.2
    have hinv : A.X.inv φ ∈ A.X.morBetween (𝒲.nbhd x').U (𝒲.nbhd x).U :=
      ⟨by rw [A.X.src_inv]; exact hφ'.2, by rw [A.X.tgt_inv]; exact hφ'.1⟩
    have hsF' : A.X.src (A.X.inv φ) ∈ F := by rw [A.X.src_inv]; exact hF.tgt_mem hsF
    obtain ⟨hxF, hx'F, hφF⟩ := D.mem_mor_face h𝒲 hφ' hF hsF
    change D.τg hX x' x (A.X.inv φ) = (D.τg hX x x' φ).swap
    rw [D.τg_eq h𝒲 hinv hF hsF', D.τg_eq h𝒲 hφ' hF hsF]
    exact (D.T F hF).swap ⟨x, hxF⟩ ⟨x', hx'F⟩ φ hφF
  diag x g z hz := by
    obtain ⟨F, hF, hzF⟩ := exists_isEpFace_mem hX hz.2
    have hxF := (h𝒲 x z hz.1).1 F hF hzF
    have hzUF := ((h𝒲 x z hz.1).2 F hF hxF).1
    have hΓ : (𝒲.nbhd x).rep.Γ g z ∈ A.X.morBetween (𝒲.nbhd x).U (𝒲.nbhd x).U :=
      ⟨by rw [(𝒲.nbhd x).src_Γ g hz.1]; exact hz.1,
        by rw [(𝒲.nbhd x).tgt_Γ g hz.1]; exact (𝒲.nbhd x).Φ_mem g hz.1⟩
    have hsF : A.X.src ((𝒲.nbhd x).rep.Γ g z) ∈ F := by
      rw [(𝒲.nbhd x).src_Γ g hz.1]; exact hzF
    change D.τg hX x x ((𝒲.nbhd x).rep.Γ g z) = IndexCorr.ofPerm (α := D.ι.I x) g
    rw [D.τg_eq h𝒲 hΓ hF hsF, ((h𝒲 x z hz.1).2 F hF hxF).2 g]
    exact (D.T F hF).diag ⟨x, hxF⟩ g z ⟨hzUF, hzF⟩
  biact x x' φ hφ g' g := by
    have hφ' := 𝒲.mor_subset x x' hφ
    obtain ⟨F, hF, hsF⟩ := exists_isEpFace_mem hX hφ.1.2
    obtain ⟨hxF, hx'F, hφF⟩ := D.mem_mor_face h𝒲 hφ' hF hsF
    have hb := EpGroupoid.biact_mem hφ' g' g
    have hsb : A.X.src (EpGroupoid.biact (𝒲.nbhd x) (𝒲.nbhd x') g' φ g) ∈ F := by
      rw [EpGroupoid.src_biact hφ' g' g]; exact hF.Φ_mem _ g⁻¹ hφ'.1 hsF
    have hy : (𝒲.nbhd x).rep.Φ g⁻¹ (A.X.src φ) ∈ (𝒲.nbhd x).U := (𝒲.nbhd x).Φ_mem g⁻¹ hφ'.1
    have heq : EpGroupoid.biact (𝒲.nbhd x) (𝒲.nbhd x') g' φ g =
        EpGroupoid.biact ((D.T F hF).nbhd ⟨x, hxF⟩) ((D.T F hF).nbhd ⟨x', hx'F⟩) g' φ g := by
      simp only [EpGroupoid.biact]
      rw [((h𝒲 x' _ hφ'.2).2 F hF hx'F).2 g', ((h𝒲 x _ hy).2 F hF hxF).2 g,
        D.Φ_eq h𝒲 hφ'.1 hF hxF g⁻¹]
    change D.τg hX x x' (EpGroupoid.biact (𝒲.nbhd x) (𝒲.nbhd x') g' φ g) =
      IndexCorr.biact g' (D.τg hX x x' φ) g
    rw [D.τg_eq h𝒲 hb hF hsb, D.τg_eq h𝒲 hφ' hF hsF, heq]
    exact (D.T F hF).biact ⟨x, hxF⟩ ⟨x', hx'F⟩ φ hφF g' g
  compat x x' φ hφ := by
    have hφ' := 𝒲.mor_subset x x' hφ
    obtain ⟨F, hF, hsF⟩ := exists_isEpFace_mem hX hφ.1.2
    obtain ⟨hxF, hx'F, hφF⟩ := D.mem_mor_face h𝒲 hφ' hF hsF
    change (D.τg hX x x' φ).Sat fun i j =>
      D.sg hX x' j (A.X.tgt φ) = fibAct φ (D.sg hX x i (A.X.src φ))
    rw [D.τg_eq h𝒲 hφ' hF hsF]
    refine IndexCorr.sat_mono (fun i j h => ?_) ((D.T F hF).compat ⟨x, hxF⟩ ⟨x', hx'F⟩ φ hφF)
    rw [D.sg_eq h𝒲 hφ'.2 hF (hF.tgt_mem hsF), D.sg_eq h𝒲 hφ'.1 hF hsF]
    exact h

end Glue

/-! ### Theorem 14.6.3 -/

section Theorem

variable (hpara : A.X.HasParacompactOrbitSpace)
include hX hpara

/-- **The glued `Λ : W|∂X → ℚ⁺` is an sc⁺-multisection over `∂X`** (Definition 14.1.3): a
functor (as every `Λ_F` is, and `∂X` is the union of the faces), with the structures `S` of the
adapted good system. -/
theorem isBoundaryScPlusMultisection : IsBoundaryScPlusMultisection A D.Λg := by
  obtain ⟨𝒲, h𝒲⟩ := D.exists_adapted hX hpara
  refine ⟨fun q hq => ?_, fun x hx => ⟨𝒲.nbhd ⟨x, hx⟩, 𝒲.isGood _, ⟨S D hX h𝒲 ⟨x, hx⟩⟩⟩⟩
  obtain ⟨F, hF, hsF⟩ := exists_isEpFace_mem hX hq
  have h2 : A.P (q : A.Mor × A.W).2 = A.X.src (q : A.Mor × A.W).1 := q.2
  have h1 : A.P (A.E.μ q) ∈ F := by rw [A.E.P_μ q]; exact hF.tgt_mem hsF
  rw [D.Λg_eq hF h1, D.Λg_eq hF (h2 ▸ hsF)]
  exact (D.T F hF).isFunctor q hsF

/-- **The structured sc⁺-multisection `Λ̃ = [Λ, 𝒰, S, τ]` over `∂X`** defined by compatible face
data (proof of Theorem 14.6.3). -/
def glue : BoundaryStructuredTuple A where
  Λ := D.Λg
  isBoundaryScPlusMultisection := D.isBoundaryScPlusMultisection hX hpara
  dec := dec D hX (D.exists_adapted hX hpara).choose_spec
  tau := tau D hX (D.exists_adapted hX hpara).choose_spec

theorem glue_Λ : (D.glue hX hpara).Λ = D.Λg := rfl

/-- `U(x) ∩ F ⊆ U_F(x)` for the faces `F ∋ x`. -/
theorem glue_U_inter_subset (x : A.X.PObj.boundary) {F : Set A.Obj} (hF : A.X.IsEpFace F)
    (hxF : (x : A.Obj) ∈ F) :
    ((D.glue hX hpara).dec.𝒰.nbhd x).U ∩ F ⊆ (D.T F hF).U ⟨x, hxF⟩ :=
  fun y hy => ⟨(((D.exists_adapted hX hpara).choose_spec x y hy.1).2 F hF hxF).1, hy.2⟩

/-- `sˣᵢ = sˣ_{F,i}` on `U(x) ∩ F`. -/
theorem glue_s (x : A.X.PObj.boundary) {F : Set A.Obj} (hF : A.X.IsEpFace F) (i : D.ι.I x)
    {y : A.Obj} (hy : y ∈ ((D.glue hX hpara).dec.𝒰.nbhd x).U) (hyF : y ∈ F) :
    ((D.glue hX hpara).dec.S x).s i y = (D.T F hF).s x i y :=
  D.sg_eq (D.exists_adapted hX hpara).choose_spec hy hF hyF i

/-- `τ_{x,x'} = τ_{F,x,x'}` on the morphisms of `𝒰(x, x')` with source on `F`. -/
theorem glue_τ (x x' : A.X.PObj.boundary) {φ : A.Mor} (hφ : φ ∈ (D.glue hX hpara).dec.𝒰.mor x x')
    {F : Set A.Obj} (hF : A.X.IsEpFace F) (hsF : A.X.src φ ∈ F) :
    (D.glue hX hpara).tau.τ x x' φ = (D.T F hF).τ x x' φ :=
  D.τg_eq (D.exists_adapted hX hpara).choose_spec
    (BoundaryGoodSystem.mor_subset _ x x' hφ) hF hsF

/-- **2021 Theorem 14.6.3, p. 682 (2017: Theorem 14.4)**, the structure part, for compatible
chosen representatives (`CompatibleFaceData`, which is a compatible assignment by
`isCompatibleAssignment`): over a tame face-structured ep-groupoid with paracompact orbit space,
`Λ(w) := Λ_F(w)` (`P(w) ∈ F`) is a structurable sc⁺-multisection over `∂X` (Definition 14.1.7);
its structure `glue` restricts to the given ones on the faces (`glue_U_inter_subset`, `glue_s`,
`glue_τ`). -/
theorem theorem_14_6_3_hyp :
    IsBoundaryStructurable A D.Λg ∧
      ∀ F (hF : A.X.IsEpFace F) w, A.P w ∈ F → D.Λg w = (D.T F hF).Λ w :=
  ⟨⟨D.isBoundaryScPlusMultisection hX hpara, _, ⟨(D.glue hX hpara).tau⟩⟩,
    fun _ hF _ hw => D.Λg_eq hF hw⟩

/-- **2021 Theorem 14.6.3, p. 682 (2017: Theorem 14.4)**, the extension part: given the
∂-Extension Theorem 14.1.9 (`theorem_14_1_9_statement`), the glued `Λ` extends to a structurable
sc⁺-multisection functor `Λ'` on `W` with `N(Λ') ≤ f`, `dom-supp(Λ') ⊆ Ũ`, and `Λ' = Λ_F` over
every face `F`. -/
theorem theorem_14_6_3_extension_hyp (h1419 : theorem_14_1_9_statement A)
    (hpart : A.X.PObj.AdmitsScPartitionsOfUnity) (N : A.B.One → ℝ) (hN : A.E.IsAuxNorm N)
    (Ũ : Set A.Obj) (hŨ : IsOpen Ũ) (hŨs : A.X.IsSaturated Ũ) (hdom : boundaryDomSupp D.Λg ⊆ Ũ)
    (f : A.Obj → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hff : ∀ φ, f (A.X.tgt φ) = f (A.X.src φ)) (hfU : tsupport f ⊆ Ũ)
    (hfN : ∀ x ∈ boundaryDomSupp D.Λg, pointwiseNorm N D.Λg x < f x) :
    ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧ (∀ x, pointwiseNorm N Λ' x ≤ f x) ∧
      domSupp Λ' ⊆ Ũ ∧ ∀ F (hF : A.X.IsEpFace F) w, A.P w ∈ F → Λ' w = (D.T F hF).Λ w := by
  obtain ⟨Λ', h1, h2, h3, h4⟩ := h1419 hX.1 hpara hpart D.Λg (D.theorem_14_6_3_hyp hX hpara).1
    N hN Ũ hŨ hŨs hdom f hf hf0 hff hfU hfN
  exact ⟨Λ', h1, h2, h3, fun F hF w hw =>
    (h4 w (IsEpFace.subset_boundary hF hw)).trans (D.Λg_eq hF hw)⟩

end Theorem

/-! ### Nonvacuity -/

/-- **`CompatibleFaceData` is satisfiable**: the zero multisection on every face, on one index
family `I_x = {∗}`. -/
def zero (A : SEP.{u}) : CompatibleFaceData A where
  ι := IndexFamily.unit A
  T _ hF := FaceStructuredTuple.zero (IsEpFace.subset_boundary hF)
    (fun x => (A.X.exists_natNbhd_isProperSubset (x : A.Obj) isOpen_univ (mem_univ _)).choose)
    (fun x => (A.X.exists_natNbhd_isProperSubset (x : A.Obj) isOpen_univ (mem_univ _)).choose_spec.2)
  Λ_eq _ _ _ _ _ _ := rfl
  s_eq _ _ _ _ _ _ _ _ _ _ := rfl
  τ_eq _ _ _ _ _ _ _ _ _ _ _ _ := rfl

/-- With the zero face data, the glued `Λ` is the zero multisection over `∂X`. -/
theorem zero_Λg (hX : A.X.IsEpFaceStructured) {w : A.W} (hw : A.P w ∈ A.X.PObj.boundary) :
    (zero A).Λg w = zeroMultisection A w := by
  obtain ⟨F, hF, hwF⟩ := exists_isEpFace_mem hX hw
  exact (zero A).Λg_eq hF hwF

end CompatibleFaceData

end SBLocalization

end Polyfold
