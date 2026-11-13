import Polyfold.Chapter14.P3W5F6_Theorem1463
import Polyfold.Chapter13.P3E_GoodSystemRelative

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.6, p. 680 (2017:
§14.6): **the neighbourhoods `U_F(x)` of a structured sc⁺-multisection on `W|F` form a good
system for the ep-groupoid `F`** (gap F6-3 of wave 5).  Numbers and pages are the 2021 text's.

## The text, paraphrased

For a face `F` of a tame face-structured ep-groupoid, a structured sc⁺-multisection on `W|F`
uses good neighbourhoods `U_F(x) ⊆ F`, `x ∈ F`, for the ep-groupoid `F` (Proposition 11.1.6),
i.e. the conditions of Definition 13.1.2 / 13.1.4 hold inside `F`.

## What is formalized

Namespace `Polyfold.EpGroupoid`, for a face `X_θ` with its ep-groupoid `faceEpGroupoid hX hθ`:
* `isProperSubset_face`: if `t : s⁻¹(cl(U ∩ X_θ)) → X` is proper in `X`, then
  `t : s⁻¹(cl_{X_θ} U_F) → X_θ` is proper in the ep-groupoid `X_θ` (condition (1) inside `F`).
* `isDiffeoComponent_face`: if the components of `{φ | s φ ∈ U, t φ ∈ U'}` satisfy condition (3)
  in `X`, the components of the corresponding morphism set of `X_θ` satisfy it in `X_θ`
  (a component in `X_θ` lies in a component in `X`; `s, t` stay injective).
* `GoodSystem.isProperSubset_face`, `GoodSystem.isDiffeoComponent_face`: every good system of
  `X` restricts to neighbourhoods of `X_θ` with (1) and (3).

Namespace `Polyfold.SBLocalization`:
* `NatNbhd`-shrinking of the tuples: `RelTuple.shrink` (same `Λ`, `s`, `τ`, the neighbourhoods
  replaced by their invariant cores inside given opens), `RelTuple.equiv_shrink`,
  `FaceStructuredTuple.shrink`.
* `RelTuple.exists_equiv_isDiffeoComponent` (`|X|` paracompact, Theorem 13.1.8): every tuple
  is equivalent to one whose neighbourhoods satisfy condition (3) in `X`.
* **`FaceStructuredTuple.exists_equiv_faceGood`** and on classes
  **`FaceStructuredMultisection.exists_rep_faceGood`**: every structured sc⁺-multisection on
  `W|F` has a representative whose `U_F(x)` satisfy, inside the ep-groupoid `F`, the
  properness (1), the component condition (3), and the invariance of `U_F(x)` under the
  natural `G_x`-action (`Φ(g)(U(x) ∩ F) ⊆ U(x) ∩ F`).

## Reading

* The natural action on `U_F(x)` is that of `X` restricted to `U(x) ∩ F` (the text's reading
  on p. 680); a natural representation of the ep-groupoid `F` itself (Theorem 7.1.13 for
  `F`, with a connected domain inside `F`) is not constructed.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {θ : Set X.OrbitSpace}

/-- **Condition (1) inside the face**: properness of `cl(U ∩ X_θ)` in `X` gives properness of
`cl_{X_θ}(U ∩ X_θ)` in the ep-groupoid `X_θ`. -/
theorem isProperSubset_face (hX : X.IsEpFaceStructured) (hθ : X.IsOrbitFace θ) {U : Set Obj}
    (hU : X.IsProperSubset (closure (U ∩ X.faceObj θ))) :
    (faceEpGroupoid hX hθ).IsProperSubset
      (closure ((↑) ⁻¹' U : Set (X.faceObj θ))) := by
  have e : ((↑) ⁻¹' U : Set (X.faceObj θ)) = (↑) ⁻¹' (U ∩ X.faceObj θ) := by
    ext y; exact ⟨fun h => ⟨h, y.2⟩, fun h => h.1⟩
  rw [e]
  change X.IsProperSubsetIn (X.faceObj θ) _
  rw [isProperSubsetIn_iff_ultrafilter inter_subset_right]
  intro 𝒱 z hz hS hT
  have hS' : X.src ⁻¹' closure (U ∩ X.faceObj θ) ∈ 𝒱 :=
    Filter.mem_of_superset hS inter_subset_right
  obtain ⟨φ, hφ, htφ, hle⟩ := (X.isProperSubset_iff_ultrafilter _).1 hU 𝒱 z hS' hT
  have hcl : closure (U ∩ X.faceObj θ) ⊆ X.faceObj θ :=
    closure_minimal inter_subset_right (isClosed_faceObj hθ)
  exact ⟨φ, ⟨⟨hcl hφ, htφ ▸ hz⟩, hφ⟩, htφ, hle⟩

/-- **Condition (3) inside the face**: if every component of `{φ | s φ ∈ U, t φ ∈ U'}` in `X`
satisfies condition (3), then so does every component of the corresponding morphism set of the
ep-groupoid `X_θ`. -/
theorem isDiffeoComponent_face (hX : X.IsEpFaceStructured) (hθ : X.IsOrbitFace θ)
    {U U' : Set Obj} (hU : IsOpen U) (hU' : IsOpen U')
    (h : ∀ φ ∈ X.morBetween U U',
      X.IsDiffeoComponent (connectedComponentIn (X.morBetween U U') φ))
    (φ : X.morOn (X.faceObj θ))
    (hφ : φ ∈ (faceEpGroupoid hX hθ).morBetween ((↑) ⁻¹' U) ((↑) ⁻¹' U')) :
    (faceEpGroupoid hX hθ).IsDiffeoComponent
      (connectedComponentIn ((faceEpGroupoid hX hθ).morBetween ((↑) ⁻¹' U) ((↑) ⁻¹' U')) φ) := by
  set Y := faceEpGroupoid hX hθ
  set S := Y.morBetween ((↑) ⁻¹' U : Set (X.faceObj θ)) ((↑) ⁻¹' U')
  have hSo : IsOpen S := isOpen_morBetween (hU.preimage continuous_subtype_val)
    (hU'.preimage continuous_subtype_val)
  set C := connectedComponentIn S φ
  have hφX : (φ : Mor) ∈ X.morBetween U U' := hφ
  -- the image of the component lies in a component of `X`
  have hsub : ((↑) : X.morOn (X.faceObj θ) → Mor) '' C ⊆
      connectedComponentIn (X.morBetween U U') φ := by
    refine (isPreconnected_connectedComponentIn.image _
      continuous_subtype_val.continuousOn).subset_connectedComponentIn
      ⟨φ, mem_connectedComponentIn hφ, rfl⟩ ?_
    rintro _ ⟨ψ, hψ, rfl⟩
    exact connectedComponentIn_subset S φ hψ
  have hX3 := h φ hφX
  refine (isDiffeoComponent_iff_injOn (isOpen_connectedComponentIn_mor Y hSo φ)).2
    ⟨fun a ha b hb hab => ?_, fun a ha b hb hab => ?_⟩
  · have e : X.src (a : Mor) = X.src (b : Mor) := congrArg Subtype.val hab
    exact Subtype.ext (hX3.injOn_src (hsub ⟨a, ha, rfl⟩) (hsub ⟨b, hb, rfl⟩) e)
  · have e : X.tgt (a : Mor) = X.tgt (b : Mor) := congrArg Subtype.val hab
    exact Subtype.ext (hX3.injOn_tgt (hsub ⟨a, ha, rfl⟩) (hsub ⟨b, hb, rfl⟩) e)

namespace GoodSystem

/-- A good system of `X` restricts to the face `X_θ` with condition (1). -/
theorem isProperSubset_face (𝒰 : X.GoodSystem) (hX : X.IsEpFaceStructured)
    (hθ : X.IsOrbitFace θ) (x : Obj) :
    (faceEpGroupoid hX hθ).IsProperSubset
      (closure ((↑) ⁻¹' 𝒰.U x : Set (X.faceObj θ))) :=
  EpGroupoid.isProperSubset_face hX hθ
    (isProperMap_domRestrict_of_subset_of_isClosed X.continuous_src
      (𝒰.isProperSubset_closure x) (closure_mono inter_subset_left) isClosed_closure)

/-- A good system of `X` restricts to the face `X_θ` with condition (3). -/
theorem isDiffeoComponent_face (𝒰 : X.GoodSystem) (hX : X.IsEpFaceStructured)
    (hθ : X.IsOrbitFace θ) (x x' : Obj) (φ : X.morOn (X.faceObj θ))
    (hφ : φ ∈ (faceEpGroupoid hX hθ).morBetween ((↑) ⁻¹' 𝒰.U x) ((↑) ⁻¹' 𝒰.U x')) :
    (faceEpGroupoid hX hθ).IsDiffeoComponent
      (connectedComponentIn
        ((faceEpGroupoid hX hθ).morBetween ((↑) ⁻¹' 𝒰.U x) ((↑) ⁻¹' 𝒰.U x')) φ) :=
  EpGroupoid.isDiffeoComponent_face hX hθ (𝒰.nbhd x).isOpen_U (𝒰.nbhd x').isOpen_U
    (fun ψ hψ => 𝒰.isDiffeoComponent x x' ψ hψ) φ hφ

end GoodSystem

namespace NatNbhd

/-- The invariant core of `N.U ∩ V` as a neighbourhood with the same natural action. -/
def shrink {x : Obj} (N : X.NatNbhd x) (V : Set Obj) (hV : IsOpen V) (hx : x ∈ V) :
    X.NatNbhd x :=
  N.restrict _ (N.isOpen_invariantCore hV) (N.mem_invariantCore hx)
    (fun _ hy => (N.invariantCore_subset V hy).1) (N.mapsTo_Φ_invariantCore V)

theorem shrink_U_subset {x : Obj} (N : X.NatNbhd x) (V : Set Obj) (hV : IsOpen V)
    (hx : x ∈ V) : (N.shrink V hV hx).U ⊆ N.U ∩ V :=
  N.invariantCore_subset V

@[simp] theorem shrink_rep {x : Obj} (N : X.NatNbhd x) (V : Set Obj) (hV : IsOpen V)
    (hx : x ∈ V) : (N.shrink V hV hx).rep = N.rep := rfl

end NatNbhd

end EpGroupoid

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}} {K : Set A.Obj} {ι : IndexFamily A}

namespace RelTuple

/-- **Shrinking the neighbourhoods of a tuple** to the invariant cores of `U(x) ∩ W(x)`; `Λ`,
the sections and the correspondences are unchanged. -/
def shrink (T : RelTuple A K ι) (W : A.Obj → Set A.Obj) (hW : ∀ x, IsOpen (W x))
    (hxW : ∀ x, x ∈ W x) : RelTuple A K ι where
  Λ := T.Λ
  isFunctor := T.isFunctor
  nbhd x := (T.nbhd x).shrink (W x) (hW x) (hxW x)
  isProper x := isProperMap_domRestrict_of_subset_of_isClosed A.X.continuous_src (T.isProper x)
    (closure_mono (inter_subset_inter_left _ fun _ hy =>
      ((T.nbhd x).shrink_U_subset _ _ _ hy).1)) isClosed_closure
  s := T.s
  P_s x i y hy := T.P_s x i y ⟨((T.nbhd x).shrink_U_subset _ _ _ hy.1).1, hy.2⟩
  equivariant x g i y hy :=
    T.equivariant x g i y ⟨((T.nbhd x).shrink_U_subset _ _ _ hy.1).1, hy.2⟩
  rep x w hw := T.rep x w ⟨((T.nbhd x).shrink_U_subset _ _ _ hw.1).1, hw.2⟩
  τ := T.τ
  locallyConstant x x' φ hφ := by
    have hsub : A.X.morBetween (((T.nbhd x).shrink (W x) (hW x) (hxW x)).U ∩ K)
        (((T.nbhd x').shrink (W x') (hW x') (hxW x')).U ∩ K) ⊆
        A.X.morBetween ((T.nbhd x).U ∩ K) ((T.nbhd x').U ∩ K) :=
      morBetween_mono
        (inter_subset_inter_left _ fun _ hy => ((T.nbhd x).shrink_U_subset _ _ _ hy).1)
        (inter_subset_inter_left _ fun _ hy => ((T.nbhd x').shrink_U_subset _ _ _ hy).1)
    exact (T.locallyConstant x x' φ (hsub hφ)).filter_mono (nhdsWithin_mono _ hsub)
  finite x x' := (T.finite x x').subset (image_mono (morBetween_mono
    (inter_subset_inter_left _ fun _ hy => ((T.nbhd x).shrink_U_subset _ _ _ hy).1)
    (inter_subset_inter_left _ fun _ hy => ((T.nbhd x').shrink_U_subset _ _ _ hy).1)))
  swap x x' φ hφ := T.swap x x' φ
    ⟨⟨((T.nbhd x).shrink_U_subset _ _ _ hφ.1.1).1, hφ.1.2⟩,
      ⟨((T.nbhd x').shrink_U_subset _ _ _ hφ.2.1).1, hφ.2.2⟩⟩
  diag x g z hz := T.diag x g z ⟨((T.nbhd x).shrink_U_subset _ _ _ hz.1).1, hz.2⟩
  biact x x' φ hφ g' g := T.biact x x' φ
    ⟨⟨((T.nbhd x).shrink_U_subset _ _ _ hφ.1.1).1, hφ.1.2⟩,
      ⟨((T.nbhd x').shrink_U_subset _ _ _ hφ.2.1).1, hφ.2.2⟩⟩ g' g
  compat x x' φ hφ := T.compat x x' φ
    ⟨⟨((T.nbhd x).shrink_U_subset _ _ _ hφ.1.1).1, hφ.1.2⟩,
      ⟨((T.nbhd x').shrink_U_subset _ _ _ hφ.2.1).1, hφ.2.2⟩⟩

@[simp] theorem shrink_Λ (T : RelTuple A K ι) (W : A.Obj → Set A.Obj) (hW : ∀ x, IsOpen (W x))
    (hxW : ∀ x, x ∈ W x) : (T.shrink W hW hxW).Λ = T.Λ := rfl

@[simp] theorem shrink_s (T : RelTuple A K ι) (W : A.Obj → Set A.Obj) (hW : ∀ x, IsOpen (W x))
    (hxW : ∀ x, x ∈ W x) : (T.shrink W hW hxW).s = T.s := rfl

@[simp] theorem shrink_τ (T : RelTuple A K ι) (W : A.Obj → Set A.Obj) (hW : ∀ x, IsOpen (W x))
    (hxW : ∀ x, x ∈ W x) : (T.shrink W hW hxW).τ = T.τ := rfl

theorem shrink_nbhd_U_subset (T : RelTuple A K ι) (W : A.Obj → Set A.Obj)
    (hW : ∀ x, IsOpen (W x)) (hxW : ∀ x, x ∈ W x) (x : K) :
    ((T.shrink W hW hxW).nbhd x).U ⊆ (T.nbhd x).U ∩ W x :=
  (T.nbhd x).shrink_U_subset (W x) (hW x) (hxW x)

/-- **A shrunk tuple is equivalent to the original** (Definition 13.3.8's equivalence). -/
theorem equiv_shrink (T : RelTuple A K ι) (W : A.Obj → Set A.Obj) (hW : ∀ x, IsOpen (W x))
    (hxW : ∀ x, x ∈ W x) : T.Equiv (T.shrink W hW hxW) :=
  ⟨fun _ _ => rfl, fun x => ((T.shrink W hW hxW).nbhd x).U,
    fun x => ((T.shrink W hW hxW).nbhd x).isOpen_U, fun x => ((T.shrink W hW hxW).nbhd x).mem_U,
    fun x _ hy => ⟨⟨((T.shrink_nbhd_U_subset W hW hxW x) hy.1).1, hy.2⟩, hy⟩, fun _ => rfl,
    fun _ _ _ _ => (IndexCorr.map_cast_rfl _).symm⟩

/-- **Every tuple is equivalent to one satisfying condition (3) in `X`** (`|X|` paracompact):
shrink into a good system of `X` (Theorem 13.1.8); condition (3) passes to smaller sets. -/
theorem exists_equiv_isDiffeoComponent (hpara : A.X.HasParacompactOrbitSpace)
    (T : RelTuple A K ι) :
    ∃ T' : RelTuple A K ι, T.Equiv T' ∧ T'.Λ = T.Λ ∧ T'.s = T.s ∧ T'.τ = T.τ ∧
      (∀ x : K, (T'.nbhd x).U ⊆ (T.nbhd x).U) ∧
      ∀ x x' : K, ∀ φ ∈ A.X.morBetween (T'.nbhd x).U (T'.nbhd x').U,
        A.X.IsDiffeoComponent
          (connectedComponentIn (A.X.morBetween (T'.nbhd x).U (T'.nbhd x').U) φ) := by
  obtain ⟨𝒢, -⟩ := A.X.theorem_13_1_8 hpara (fun _ => univ) (fun _ => isOpen_univ)
    (fun _ => mem_univ _)
  have hW : ∀ x, IsOpen (𝒢.U x) := fun x => (𝒢.nbhd x).isOpen_U
  have hxW : ∀ x, x ∈ 𝒢.U x := fun x => (𝒢.nbhd x).mem_U
  have hsub := T.shrink_nbhd_U_subset 𝒢.U hW hxW
  refine ⟨T.shrink 𝒢.U hW hxW, T.equiv_shrink _ hW hxW, rfl, rfl, rfl,
    fun x _ hy => (hsub x hy).1, fun x x' φ hφ => ?_⟩
  exact 𝒢.isDiffeoComponent_of_subset (x := x) (x' := x') (NatNbhd.isOpen_U _)
    (NatNbhd.isOpen_U _) (fun _ hy => (hsub x hy).2) (fun _ hy => (hsub x' hy).2) hφ

end RelTuple

namespace FaceStructuredTuple

variable {F : Set A.Obj}

/-- Shrinking a face tuple (the sections stay sc⁺ relative to `F` on the smaller sets). -/
def shrink (T : FaceStructuredTuple A F ι) (W : A.Obj → Set A.Obj) (hW : ∀ x, IsOpen (W x))
    (hxW : ∀ x, x ∈ W x) : FaceStructuredTuple A F ι where
  toRelTuple := T.toRelTuple.shrink W hW hxW
  isFaceRelScPlus x i := (T.isFaceRelScPlus x i).mono
    (inter_subset_inter_left _ fun _ hy => (T.toRelTuple.shrink_nbhd_U_subset W hW hxW x hy).1)

/-- **The neighbourhoods `U_F(x)` form a good system for the ep-groupoid `F`, up to
equivalence** (§14.6, p. 680; gap F6-3): for a face `F = X_θ` of a tame face-structured `X`
with paracompact `|X|`, every face tuple is equivalent to one whose `U_F(x) = U(x) ∩ F` satisfy,
in the ep-groupoid `F` (`faceEpGroupoid`): (1) `t : s⁻¹(cl_F U_F(x)) → F` is proper, (3) every
component of `𝒰_F(x, x')` has `s` and `t` sc-diffeomorphisms onto open sets, and the natural
`G_x`-action of `X` maps `U_F(x)` into itself. -/
theorem exists_equiv_faceGood (hX : A.X.IsEpFaceStructured)
    (hpara : A.X.HasParacompactOrbitSpace) {θ : Set A.X.OrbitSpace}
    (hθ : A.X.IsOrbitFace θ) (T : FaceStructuredTuple A (A.X.faceObj θ) ι) :
    ∃ T' : FaceStructuredTuple A (A.X.faceObj θ) ι, T.toRelTuple.Equiv T'.toRelTuple ∧
      T'.Λ = T.Λ ∧ T'.s = T.s ∧ T'.τ = T.τ ∧
      (∀ x : A.X.faceObj θ, (faceEpGroupoid hX hθ).IsProperSubset
        (closure ((↑) ⁻¹' (T'.nbhd x).U : Set (A.X.faceObj θ)))) ∧
      (∀ x x' : A.X.faceObj θ, ∀ φ ∈ (faceEpGroupoid hX hθ).morBetween
          ((↑) ⁻¹' (T'.nbhd x).U) ((↑) ⁻¹' (T'.nbhd x').U),
        (faceEpGroupoid hX hθ).IsDiffeoComponent (connectedComponentIn
          ((faceEpGroupoid hX hθ).morBetween ((↑) ⁻¹' (T'.nbhd x).U)
            ((↑) ⁻¹' (T'.nbhd x').U)) φ)) ∧
      ∀ (x : A.X.faceObj θ) (g : A.X.Isotropy x), MapsTo ((T'.nbhd x).rep.Φ g)
        ((T'.nbhd x).U ∩ A.X.faceObj θ) ((T'.nbhd x).U ∩ A.X.faceObj θ) := by
  obtain ⟨𝒢, -⟩ := A.X.theorem_13_1_8 hpara (fun _ => univ) (fun _ => isOpen_univ)
    (fun _ => mem_univ _)
  have hW : ∀ x, IsOpen (𝒢.U x) := fun x => (𝒢.nbhd x).isOpen_U
  have hxW : ∀ x, x ∈ 𝒢.U x := fun x => (𝒢.nbhd x).mem_U
  set T' := T.shrink 𝒢.U hW hxW
  have hsub := T.toRelTuple.shrink_nbhd_U_subset 𝒢.U hW hxW
  refine ⟨T', T.toRelTuple.equiv_shrink _ hW hxW, rfl, rfl, rfl, fun x => ?_,
    fun x x' φ hφ => ?_, fun x g y hy => ?_⟩
  · exact EpGroupoid.isProperSubset_face hX hθ (T'.isProper x)
  · refine EpGroupoid.isDiffeoComponent_face hX hθ (NatNbhd.isOpen_U _) (NatNbhd.isOpen_U _)
      (fun ψ hψ => ?_) φ hφ
    exact 𝒢.isDiffeoComponent_of_subset (x := x) (x' := x') (NatNbhd.isOpen_U _)
      (NatNbhd.isOpen_U _) (fun _ hy => (hsub x hy).2) (fun _ hy => (hsub x' hy).2) hψ
  · exact ⟨(T'.nbhd x).Φ_mem g hy.1, IsEpFace.Φ_mem (X := A.X) ⟨θ, hθ, rfl⟩ _ g hy.1 hy.2⟩

end FaceStructuredTuple

/-- **On classes** (§14.6, p. 680; gap F6-3): every structured sc⁺-multisection on `W|F`,
`F = X_θ`, has a representative whose neighbourhoods `U_F(x)` satisfy, inside the ep-groupoid
`F`, conditions (1) and (3) of a good system, with the natural action of `X` preserving them. -/
theorem FaceStructuredMultisection.exists_rep_faceGood (hX : A.X.IsEpFaceStructured)
    (hpara : A.X.HasParacompactOrbitSpace) {θ : Set A.X.OrbitSpace} (hθ : A.X.IsOrbitFace θ)
    (L : FaceStructuredMultisection A (A.X.faceObj θ)) :
    ∃ T : Σ ι : IndexFamily A, FaceStructuredTuple A (A.X.faceObj θ) ι, ⟦T⟧ = L ∧
      (∀ x : A.X.faceObj θ, (faceEpGroupoid hX hθ).IsProperSubset
        (closure ((↑) ⁻¹' (T.2.nbhd x).U : Set (A.X.faceObj θ)))) ∧
      (∀ x x' : A.X.faceObj θ, ∀ φ ∈ (faceEpGroupoid hX hθ).morBetween
          ((↑) ⁻¹' (T.2.nbhd x).U) ((↑) ⁻¹' (T.2.nbhd x').U),
        (faceEpGroupoid hX hθ).IsDiffeoComponent (connectedComponentIn
          ((faceEpGroupoid hX hθ).morBetween ((↑) ⁻¹' (T.2.nbhd x).U)
            ((↑) ⁻¹' (T.2.nbhd x').U)) φ)) ∧
      ∀ (x : A.X.faceObj θ) (g : A.X.Isotropy x), MapsTo ((T.2.nbhd x).rep.Φ g)
        ((T.2.nbhd x).U ∩ A.X.faceObj θ) ((T.2.nbhd x).U ∩ A.X.faceObj θ) := by
  obtain ⟨⟨ι, T₀⟩, rfl⟩ := Quotient.exists_rep L
  obtain ⟨T', hT', -, -, -, h1, h3, h2⟩ := T₀.exists_equiv_faceGood hX hpara hθ
  exact ⟨⟨ι, T'⟩, Quotient.sound (s := FaceStructuredTuple.setoid A _) hT'.symm, h1, h3, h2⟩

end SBLocalization

end Polyfold
