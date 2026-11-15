import Polyfold.Chapter14.BoundaryExtensionTheorem
import Polyfold.Chapter14.FaceAssemblyCorner
import Polyfold.Chapter14.FaceGoodSystem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.6, pp. 680–682:
**Definition 14.6.2** and **Theorem 14.6.3** (2017: Definition 14.11, Theorem 14.4), with the
compatibility read so that it includes the sections.

# Compatible assignments whose sections agree near every point

## The text, paraphrased

(p. 681) The sets `U_F(x)` may be shrunk and the `τ_{F,x,x'}` restricted.  (p. 682) For a
compatible assignment, `sˣ_{F,i} = sˣ_{F',i}` on `U_F(x) ∩ U_{F'}(x)`.  (Theorem 14.6.3) A
compatible assignment defines a structured `Λ̃ : W|∂X → ℚ⁺`, which extends to `W`.

## What is formalized (namespace `Polyfold.SBLocalization`)

The equivalence of Definition 13.3.8 does not compare the sections, and with it the step on
p. 682 does not hold as we read it (`FaceCorner.not_theorem_14_6_3_class_statement`).  Here the
equivalence is read with the sections:

* `RelTuple.SecEquiv`: Definition 13.3.8 together with `sˣᵢ = s'ˣᵢ` on the common smaller
  neighbourhoods (an equivalence relation: `SecEquiv.refl`, `.symm`, `.trans`; it implies
  `RelTuple.Equiv`, `SecEquiv.equiv`).
* `RelTuple.shrink_secEquiv`: the text's shrinking of the `U_F(x)` to smaller neighbourhoods
  with the same natural action (`RelTuple.shrink`) gives an equivalent tuple, sections included.
* `SectionCompatibleFaceData A`: one index family, a tuple on every face, and
  `Λ̃_F|F' = Λ̃_{F'}|F` in the sense of `SecEquiv` (Definition 14.6.2 with this reading).
* `SectionCompatibleFaceData.toCompatible`: over a face-structured ep-groupoid (finitely many
  faces through a point), shrinking the `U_F(x)` gives representatives which agree on all of
  `U_F(x) ∩ U_{F'}(x)`, that is `CompatibleFaceData` (the statement of p. 682);
  `toCompatible_secEquiv`.
* **`SectionCompatibleFaceData.theorem_14_6_3`** and `theorem_14_6_3_extension`: Theorem 14.6.3
  for such an assignment, with the text's hypotheses.
* `CompatibleFaceData.toSectionCompatible` (the converse), and with it a witness with a corner
  and non-zero sections (`FaceCorner.cornerSectionCompatible`).
* `FaceCorner.not_exists_sectionCompatibleFaceData`: the classes `Λt F` of the corner example
  have no representatives which are compatible in this sense, so the example is excluded by
  this reading.

Not formalized: the same for tuples with different index families `I^F`, where
`I^F_x = I^{F'}_x` is given for `x ∈ F ∩ F'` only and a common family has to be chosen.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-! ### The equivalence with sections -/

namespace RelTuple

variable {K : Set A.Obj} {ι ι' ι'' : IndexFamily A}

/-- **Definition 13.3.8 with the sections**: `Λ = Λ'` over `K`, open `O(x) ∋ x` with
`O(x) ∩ K ⊆ U(x) ∩ U'(x)`, `I_x = I'_x`, and on the `O(x) ∩ K` the sections agree,
`s'ˣᵢ = sˣᵢ`, and `τ' = τ` on the morphisms between them. -/
def SecEquiv (T : RelTuple A K ι) (T' : RelTuple A K ι') : Prop :=
  (∀ w, A.P w ∈ K → T.Λ w = T'.Λ w) ∧
  ∃ O : K → Set A.Obj, (∀ x, IsOpen (O x)) ∧ (∀ x, (x : A.Obj) ∈ O x) ∧
    (∀ x, O x ∩ K ⊆ T.U x ∩ T'.U x) ∧
    ∃ hI : ∀ x : K, ι.I x = ι'.I x,
      (∀ (x : K) (i : ι.I x), ∀ y ∈ O x ∩ K, T'.s x (cast (hI x) i) y = T.s x i y) ∧
      ∀ x x' : K, ∀ φ ∈ A.X.morBetween (O x ∩ K) (O x' ∩ K),
        T'.τ x x' φ = (T.τ x x' φ).map (_root_.Equiv.cast (hI x)) (_root_.Equiv.cast (hI x'))

theorem SecEquiv.equiv {T : RelTuple A K ι} {T' : RelTuple A K ι'} (h : T.SecEquiv T') :
    T.Equiv T' := by
  obtain ⟨hΛ, O, hO, hxO, hsub, hI, -, hτ⟩ := h
  exact ⟨hΛ, O, hO, hxO, hsub, hI, hτ⟩

theorem SecEquiv.refl (T : RelTuple A K ι) : T.SecEquiv T :=
  ⟨fun _ _ => rfl, fun x => (T.nbhd x).U, fun x => (T.nbhd x).isOpen_U,
    fun x => (T.nbhd x).mem_U, fun _ _ hy => ⟨hy, hy⟩, fun _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ => (IndexCorr.map_cast_rfl _).symm⟩

theorem SecEquiv.symm {T : RelTuple A K ι} {T' : RelTuple A K ι'} (h : T.SecEquiv T') :
    T'.SecEquiv T := by
  obtain ⟨hΛ, O, hO, hxO, hsub, hI, hs, hτ⟩ := h
  refine ⟨fun w hw => (hΛ w hw).symm, O, hO, hxO,
    fun x y hy => ⟨(hsub x hy).2, (hsub x hy).1⟩, fun x => (hI x).symm,
    fun x j y hy => ?_, fun x x' φ hφ => ?_⟩
  · have h1 := hs x (cast (hI x).symm j) y hy
    rw [cast_cast, cast_eq] at h1
    exact h1.symm
  · rw [hτ x x' φ hφ, IndexCorr.map_cast_symm]

theorem SecEquiv.trans {T : RelTuple A K ι} {T' : RelTuple A K ι'} {T'' : RelTuple A K ι''}
    (h₁ : T.SecEquiv T') (h₂ : T'.SecEquiv T'') : T.SecEquiv T'' := by
  obtain ⟨hΛ₁, O₁, hO₁, hxO₁, hsub₁, hI₁, hs₁, hτ₁⟩ := h₁
  obtain ⟨hΛ₂, O₂, hO₂, hxO₂, hsub₂, hI₂, hs₂, hτ₂⟩ := h₂
  refine ⟨fun w hw => (hΛ₁ w hw).trans (hΛ₂ w hw), fun x => O₁ x ∩ O₂ x,
    fun x => (hO₁ x).inter (hO₂ x), fun x => ⟨hxO₁ x, hxO₂ x⟩,
    fun x y hy => ⟨(hsub₁ x ⟨hy.1.1, hy.2⟩).1, (hsub₂ x ⟨hy.1.2, hy.2⟩).2⟩,
    fun x => (hI₁ x).trans (hI₂ x), fun x i y hy => ?_, fun x x' φ hφ => ?_⟩
  · have e : cast ((hI₁ x).trans (hI₂ x)) i = cast (hI₂ x) (cast (hI₁ x) i) :=
      (cast_cast _ _ _).symm
    rw [e]
    exact (hs₂ x _ y ⟨hy.1.2, hy.2⟩).trans (hs₁ x i y ⟨hy.1.1, hy.2⟩)
  · have h₁ : φ ∈ A.X.morBetween (O₁ x ∩ K) (O₁ x' ∩ K) :=
      ⟨⟨hφ.1.1.1, hφ.1.2⟩, ⟨hφ.2.1.1, hφ.2.2⟩⟩
    have h₂ : φ ∈ A.X.morBetween (O₂ x ∩ K) (O₂ x' ∩ K) :=
      ⟨⟨hφ.1.1.2, hφ.1.2⟩, ⟨hφ.2.1.2, hφ.2.2⟩⟩
    rw [hτ₂ x x' φ h₂, hτ₁ x x' φ h₁, IndexCorr.map_cast_trans]

end RelTuple

/-! ### Shrinking the neighbourhoods -/

/-- **A shrunk tuple is equivalent to the original, sections included** (p. 681: the `U_F(x)`
may be shrunk and `τ` restricted). -/
theorem RelTuple.shrink_secEquiv {K : Set A.Obj} {ι : IndexFamily A} (T : RelTuple A K ι)
    (W : A.Obj → Set A.Obj) (hW : ∀ x, IsOpen (W x)) (hxW : ∀ x, x ∈ W x) :
    (T.shrink W hW hxW).SecEquiv T :=
  ⟨fun _ _ => rfl, fun x => ((T.shrink W hW hxW).nbhd x).U,
    fun x => ((T.shrink W hW hxW).nbhd x).isOpen_U, fun x => ((T.shrink W hW hxW).nbhd x).mem_U,
    fun x _ hy => ⟨hy, ((T.shrink_nbhd_U_subset W hW hxW x) hy.1).1, hy.2⟩, fun _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ _ => (IndexCorr.map_cast_rfl _).symm⟩

/-! ### Assignments which are compatible with the sections -/

/-- **A compatible assignment, with the sections** (Definition 14.6.2, the equivalence read as
`RelTuple.SecEquiv`): one index family, a representative `(Λ_F, 𝒰_F, S_F, τ_F)` on every face,
and `Λ̃_F|F' = Λ̃_{F'}|F` over `F ∩ F'`: near every point of `F ∩ F'` the sections and the
correspondences of the two restrictions agree. -/
structure SectionCompatibleFaceData (A : SEP.{u}) where
  /-- The index sets `I_x`. -/
  ι : IndexFamily A
  /-- The representatives `(Λ_F, 𝒰_F, S_F, τ_F)`. -/
  T : ∀ F, A.X.IsEpFace F → FaceStructuredTuple A F ι
  secEquiv : ∀ F hF F' hF', ((T F hF).restrictFace F').SecEquiv
    ((T F' hF').toRelTuple.restrictTo (F ∩ F') inter_subset_right)

namespace SectionCompatibleFaceData

variable (S : SectionCompatibleFaceData A)

/-- The neighbourhoods `O(x)`, `x ∈ F ∩ F'`, on which `Λ̃_F|F'` and `Λ̃_{F'}|F` agree. -/
def O (F : Set A.Obj) (hF : A.X.IsEpFace F) (F' : Set A.Obj) (hF' : A.X.IsEpFace F') :
    ↥(F ∩ F') → Set A.Obj :=
  (S.secEquiv F hF F' hF').2.choose

theorem O_spec (F : Set A.Obj) (hF : A.X.IsEpFace F) (F' : Set A.Obj) (hF' : A.X.IsEpFace F') :
    (∀ x, IsOpen (S.O F hF F' hF' x)) ∧ (∀ x, (x : A.Obj) ∈ S.O F hF F' hF' x) ∧
      (∀ (x : ↥(F ∩ F')) (i : S.ι.I x), ∀ y ∈ S.O F hF F' hF' x ∩ (F ∩ F'),
        (S.T F' hF').s x i y = (S.T F hF).s x i y) ∧
      ∀ x x' : ↥(F ∩ F'), ∀ φ ∈ A.X.morBetween (S.O F hF F' hF' x ∩ (F ∩ F'))
        (S.O F hF F' hF' x' ∩ (F ∩ F')), (S.T F' hF').τ x x' φ = (S.T F hF).τ x x' φ := by
  obtain ⟨hO, hxO, -, hI, hs, hτ⟩ := (S.secEquiv F hF F' hF').2.choose_spec
  refine ⟨hO, hxO, fun x i y hy => hs x i y hy, fun x x' φ hφ => ?_⟩
  exact (hτ x x' φ hφ).trans (IndexCorr.map_cast_rfl _)

variable (hX : A.X.IsEpFaceStructured)

/-- The intersection of the `O(x)` over the finitely many faces `F'` through `x ∈ F`
(all of `X` for `x ∉ F`). -/
def core (F : Set A.Obj) (hF : A.X.IsEpFace F) (x : A.Obj) : Set A.Obj :=
  if hx : x ∈ F then
    ⋂ F' : {F' // A.X.IsEpFace F' ∧ x ∈ F'}, S.O F hF F'.1 F'.2.1 ⟨x, hx, F'.2.2⟩
  else univ

include hX in
theorem isOpen_core (F : Set A.Obj) (hF : A.X.IsEpFace F) (x : A.Obj) :
    IsOpen (S.core F hF x) := by
  unfold core
  split_ifs with hx
  · have : Finite {F' // A.X.IsEpFace F' ∧ x ∈ F'} := (finite_isEpFace_mem hX x).to_subtype
    exact isOpen_iInter_of_finite fun F' => (S.O_spec F hF F'.1 F'.2.1).1 _
  · exact isOpen_univ

theorem mem_core (F : Set A.Obj) (hF : A.X.IsEpFace F) (x : A.Obj) : x ∈ S.core F hF x := by
  unfold core
  split_ifs with hx
  · exact mem_iInter.2 fun F' => (S.O_spec F hF F'.1 F'.2.1).2.1 ⟨x, hx, F'.2.2⟩
  · exact mem_univ x

theorem core_subset_O {F : Set A.Obj} (hF : A.X.IsEpFace F) {F' : Set A.Obj}
    (hF' : A.X.IsEpFace F') {x : A.Obj} (hx : x ∈ F) (hx' : x ∈ F') :
    S.core F hF x ⊆ S.O F hF F' hF' ⟨x, hx, hx'⟩ := fun y hy => by
  rw [core, dif_pos hx] at hy
  exact mem_iInter.1 hy ⟨F', hF', hx'⟩

theorem shrink_U_subset_O {F : Set A.Obj} (hF : A.X.IsEpFace F) {F' : Set A.Obj}
    (hF' : A.X.IsEpFace F') {x : A.Obj} (hx : x ∈ F) (hx' : x ∈ F') {y : A.Obj}
    (hy : y ∈ (((S.T F hF).shrink (S.core F hF) (S.isOpen_core hX F hF)
      (S.mem_core F hF)).nbhd ⟨x, hx⟩).U) : y ∈ S.O F hF F' hF' ⟨x, hx, hx'⟩ :=
  S.core_subset_O hF hF' hx hx' ((S.T F hF).toRelTuple.shrink_nbhd_U_subset (S.core F hF)
    (S.isOpen_core hX F hF) (S.mem_core F hF) ⟨x, hx⟩ hy).2

/-- **Representatives which agree on all of `U_F(x) ∩ U_{F'}(x)`** (the statement of p. 682),
after shrinking the `U_F(x)` into `core`. -/
def toCompatible : CompatibleFaceData A where
  ι := S.ι
  T F hF := (S.T F hF).shrink (S.core F hF) (S.isOpen_core hX F hF) (S.mem_core F hF)
  Λ_eq F hF F' hF' w hw := (S.secEquiv F hF F' hF').1 w hw
  s_eq F hF F' hF' x hx hx' i y hy :=
    ((S.O_spec F hF F' hF').2.2.1 ⟨x, hx, hx'⟩ i y
      ⟨S.shrink_U_subset_O hX hF hF' hx hx' hy.1.1, hy.1.2, hy.2.2⟩).symm
  τ_eq F hF F' hF' x hx hx' x' hx₂ hx₂' φ hφ :=
    ((S.O_spec F hF F' hF').2.2.2 ⟨x, hx, hx'⟩ ⟨x', hx₂, hx₂'⟩ φ
      ⟨⟨S.shrink_U_subset_O hX hF hF' hx hx' hφ.1.1.1, hφ.1.1.2, hφ.1.2.2⟩,
        ⟨S.shrink_U_subset_O hX hF hF' hx₂ hx₂' hφ.2.1.1, hφ.2.1.2, hφ.2.2.2⟩⟩).symm

/-- The representatives of `toCompatible` are equivalent to the given ones, sections included. -/
theorem toCompatible_secEquiv (F : Set A.Obj) (hF : A.X.IsEpFace F) :
    ((S.toCompatible hX).T F hF).toRelTuple.SecEquiv (S.T F hF).toRelTuple :=
  (S.T F hF).toRelTuple.shrink_secEquiv (S.core F hF) (S.isOpen_core hX F hF) (S.mem_core F hF)

theorem toCompatible_Λ (F : Set A.Obj) (hF : A.X.IsEpFace F) :
    ((S.toCompatible hX).T F hF).Λ = (S.T F hF).Λ := rfl

/-- **2021 Theorem 14.6.3, p. 682 (2017: Theorem 14.4)**, the structure part, for an assignment
which is compatible with the sections: over a tame face-structured ep-groupoid with paracompact
orbit space, `Λ(w) := Λ_F(w)` (`P(w) ∈ F`) is a structurable sc⁺-multisection over `∂X`. -/
theorem theorem_14_6_3 (hpara : A.X.HasParacompactOrbitSpace) :
    IsBoundaryStructurable A (S.toCompatible hX).Λg ∧
      ∀ F (hF : A.X.IsEpFace F) w, A.P w ∈ F → (S.toCompatible hX).Λg w = (S.T F hF).Λ w :=
  (S.toCompatible hX).theorem_14_6_3_hyp hX hpara

/-- **2021 Theorem 14.6.3, p. 682 (2017: Theorem 14.4)**, the extension part, for an assignment
which is compatible with the sections: the glued `Λ` extends to a structurable `Λ'` on `W` with
`N(Λ') ≤ f`, `dom-supp(Λ') ⊆ Ũ` and `Λ' = Λ_F` over every face `F` (Theorem 14.1.9). -/
theorem theorem_14_6_3_extension (hpara : A.X.HasParacompactOrbitSpace)
    (hpart : A.X.PObj.AdmitsScPartitionsOfUnity) (N : A.B.One → ℝ) (hN : A.E.IsAuxNorm N)
    (Ũ : Set A.Obj) (hŨ : IsOpen Ũ) (hŨs : A.X.IsSaturated Ũ)
    (hdom : boundaryDomSupp (S.toCompatible hX).Λg ⊆ Ũ)
    (f : A.Obj → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hff : ∀ φ, f (A.X.tgt φ) = f (A.X.src φ)) (hfU : tsupport f ⊆ Ũ)
    (hfN : ∀ x ∈ boundaryDomSupp (S.toCompatible hX).Λg,
      pointwiseNorm N (S.toCompatible hX).Λg x < f x) :
    ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧ (∀ x, pointwiseNorm N Λ' x ≤ f x) ∧
      domSupp Λ' ⊆ Ũ ∧ ∀ F (hF : A.X.IsEpFace F) w, A.P w ∈ F → Λ' w = (S.T F hF).Λ w :=
  (S.toCompatible hX).theorem_14_6_3_extension hX hpara hpart N hN Ũ hŨ hŨs hdom f hf hf0 hff
    hfU hfN

end SectionCompatibleFaceData

/-- **Representatives which agree on the `U_F(x) ∩ U_{F'}(x)` are compatible with the sections.**
-/
def CompatibleFaceData.toSectionCompatible (D : CompatibleFaceData A) :
    SectionCompatibleFaceData A where
  ι := D.ι
  T := D.T
  secEquiv F hF F' hF' :=
    ⟨fun w hw => D.Λ_eq F hF F' hF' w hw,
      fun x => ((D.T F hF).nbhd ⟨x, x.2.1⟩).U ∩ ((D.T F' hF').nbhd ⟨x, x.2.2⟩).U,
      fun _ => ((D.T F hF).nbhd _).isOpen_U.inter ((D.T F' hF').nbhd _).isOpen_U,
      fun _ => ⟨((D.T F hF).nbhd _).mem_U, ((D.T F' hF').nbhd _).mem_U⟩,
      fun _ _ hy => ⟨⟨hy.1.1, hy.2⟩, ⟨hy.1.2, hy.2⟩⟩, fun _ => rfl,
      fun x i y hy => (D.s_eq F hF F' hF' x x.2.1 x.2.2 i y
        ⟨⟨hy.1.1, hy.2.1⟩, ⟨hy.1.2, hy.2.2⟩⟩).symm,
      fun x x' φ hφ => ((D.τ_eq F hF F' hF' x x.2.1 x.2.2 x' x'.2.1 x'.2.2 φ
        ⟨⟨⟨hφ.1.1.1, hφ.1.2.1⟩, ⟨hφ.1.1.2, hφ.1.2.2⟩⟩,
          ⟨⟨hφ.2.1.1, hφ.2.2.1⟩, ⟨hφ.2.1.2, hφ.2.2.2⟩⟩⟩).symm).trans
            (IndexCorr.map_cast_rfl _).symm⟩

end SBLocalization

/-! ### The corner example -/

namespace FaceCorner

open SBLocalization QuadrantBundle

/-- A section-compatible assignment with a corner and non-zero sections. -/
def cornerSectionCompatible : SectionCompatibleFaceData A := cornerFaceData.toSectionCompatible

/-- **The corner example is excluded when the compatibility includes the sections**: the classes
`Λt F` have no representatives (on one index family) for which `Λ̃_F|F'` and `Λ̃_{F'}|F` agree
together with their sections. -/
theorem not_exists_sectionCompatibleFaceData :
    ¬ ∃ S : SectionCompatibleFaceData A, ∀ F (hF : A.X.IsEpFace F),
      Quotient.mk (FaceStructuredTuple.setoid A F) ⟨S.ι, S.T F hF⟩ = Λt F hF := by
  rintro ⟨S, hS⟩
  refine not_exists_compatibleFaceData ⟨S.toCompatible isEpFaceStructured_A, fun F hF => ?_⟩
  rw [← hS F hF]
  exact Quotient.sound (S.toCompatible_secEquiv isEpFaceStructured_A F hF).equiv

end FaceCorner

end Polyfold
