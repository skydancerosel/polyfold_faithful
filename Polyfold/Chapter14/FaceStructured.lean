import Polyfold.Chapter14.FaceGerm
import Polyfold.Chapter14.BoundaryStructured

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.6, pp. 680–682:
**Definition 14.6.1** (restriction of a structured sc⁺-multisection on `W|F` to `W|(F ∩ F')`) and
**Definition 14.6.2** (compatible assignments `F ↦ Λ̃_F`) (2017: Definitions 14.10, 14.11).

# Structured sc⁺-multisections on the faces and their restrictions

## The text, paraphrased

For a face-structured tame ep-groupoid `X` and a strong bundle `P : W → X`, one is given for
every face `F` a structured sc⁺-multisection `Λ̃_F = [Λ_F, 𝒰_F, S_F, τ_F]` of `W|F`: a functor
`Λ_F : W|F → ℚ⁺`, for every `x ∈ F` a good neighbourhood `U_F(x) ⊆ F` (natural `G_x`-action,
`t : s⁻¹(cl_F U_F(x)) → F` proper), index sets `I^F_x` with a `G_x`-action, symmetric sc⁺-section
structures `(sˣ_{F,i})` and correspondences `τ_{F,x,x'}` relating them in the usual way.
(Definition 14.6.1) The restriction `Λ̃_F|F'` to `W|(F ∩ F')` is `[Λ_F|…, (U_F(x) ∩ F'), S_F|…,
τ_F|…]`: restrict everything to `F ∩ F'`.  (Definition 14.6.2) The assignment `F ↦ Λ̃_F` is
compatible if `Λ̃_F|F' = Λ̃_{F'}|F` for all faces `F, F'`; then `Λ̃_{F ∩ F'} := Λ̃_F|F'`.  The text
notes that compatibility gives `I^F_x = I^{F'}_x` for `F, F' ∋ x`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `IndexFamily A`: index sets `I_x` with `G_x`-actions.
* `RelTuple A K ι`: the data `(Λ, 𝒰, S, τ)` of a structured sc⁺-multisection over a set `K` of
  objects (`K` a face or an intersection of faces), without the regularity of the sections:
  a functor `Λ` on `W|K`, neighbourhoods `U(x) ∩ K` with the natural action and the properness of
  `t` over `cl(U(x) ∩ K)`, sections with the symmetry and the representation of `Λ` on
  `U(x) ∩ K`, and correspondences on `{φ | s(φ) ∈ U(x) ∩ K, t(φ) ∈ U(x') ∩ K}` with the
  properties of Definition 14.1.7 (2), (4).  `RelTuple.Equiv` is the equivalence "similar to the
  `X`-case" (as in `BoundaryStructuredTuple.Equiv`), `RelStructured A K` the classes.
* `FaceStructuredTuple A F ι`: a `RelTuple` on a face `F` whose sections are sc⁺ relative to `F`
  (`IsFaceRelScPlusSectionOn`); `FaceStructuredMultisection A F` the classes: **a structured
  sc⁺-multisection of `W|F`**.
* **Definition 14.6.1**: `RelTuple.restrictTo` (to any `K' ⊆ K`), `FaceStructuredTuple.restrictFace`
  (to `F ∩ F'`), compatible with the equivalence (`RelTuple.Equiv.restrictTo`), hence on classes
  (`FaceStructuredMultisection.restrictFace`).  The sections of the restriction are sc⁺ relative
  to `F` (`FaceStructuredTuple.restrictFace_isFaceRelScPlus`).
* **Definition 14.6.2**: `IsCompatibleAssignment`; `IsCompatibleAssignment.index_eq`
  (`I^F_x = I^{F'}_x`) and `IsCompatibleAssignment.Λ_eq` (`Λ_F = Λ_{F'}` over `F ∩ F'`).
  Nonvacuity: `isCompatibleAssignment_zero` (the zero multisection on every face).

## Readings

* "Good neighbourhood `U_F(x) ⊆ F`" is read as the text explains it on p. 680: `U_F(x) = V ∩ F`
  for an open `V ∋ x` of `X` with the natural `G_x`-action, and `t : s⁻¹(cl(V ∩ F)) → X` proper
  (`F` is closed, so `cl_F = cl`).  Condition (2) of a good system (Definition 13.1.4: the
  components of the morphism sets) is not part of the data; §14.6 does not use it.
* The sc⁺-sections of `W|F` are read through the tame charts of `X` (`IsFaceRelScPlusSectionOn`).
* On `F ∩ F'` (a corner of codimension two) the project has no separate sc⁺-notion; the
  restriction of Definition 14.6.1 carries the sections restricted from `F`, which are sc⁺
  relative to `F`, and the equivalence of Definition 14.6.2 does not involve the regularity.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

/-- Index sets `I_x` with `G_x`-actions, one for every object. -/
structure IndexFamily (A : SEP.{u}) where
  /-- The index set `I_x`. -/
  I : A.Obj → Type u
  [fintype : ∀ x, Fintype (I x)]
  [mulAction : ∀ x, MulAction (A.X.Isotropy x) (I x)]

attribute [instance] IndexFamily.fintype IndexFamily.mulAction

variable {A : SEP.{u}}

/-- **The data of a structured sc⁺-multisection over a set `K` of objects** (Definitions 13.3.6
and 14.1.7 with `K` in place of `X` or `∂X`; §14.6 for `K` a face or an intersection of faces),
without the regularity of the sections: `Λ` a functor on `W|K`; for `x ∈ K` an open `U(x) ∋ x`
with the natural `G_x`-action and `t : s⁻¹(cl(U(x) ∩ K)) → X` proper; sections `sˣᵢ`, `i ∈ I_x`,
with `sˣ_{g(i)}(g ∗ y) = μ(Γ(g, y), sˣᵢ(y))` and `Λ(w) = |I_x|⁻¹ #{i | sˣᵢ(P(w)) = w}` on
`U(x) ∩ K`; correspondences `τ_{x,x'}` on `𝒰(x, x') = {φ | s(φ) ∈ U(x) ∩ K, t(φ) ∈ U(x') ∩ K}`,
locally constant with finitely many values, with (a)–(c) and (4) of Definition 14.1.7. -/
structure RelTuple (A : SEP.{u}) (K : Set A.Obj) (ι : IndexFamily A) where
  /-- `Λ : W|K → ℚ⁺` (only its values over `K` matter). -/
  Λ : A.W → ℚ≥0
  isFunctor : ∀ q : pullbackSpace A.P A.X.src, A.X.src (q : A.Mor × A.W).1 ∈ K →
    Λ (A.E.μ q) = Λ (q : A.Mor × A.W).2
  /-- `U(x)` with the natural action (the neighbourhood in `K` is `U(x) ∩ K`). -/
  nbhd : ∀ x : K, A.X.NatNbhd x
  isProper : ∀ x : K, A.X.IsProperSubset (closure ((nbhd x).U ∩ K))
  /-- The sections `sˣᵢ`. -/
  s : ∀ x : A.Obj, ι.I x → A.Obj → A.W
  P_s : ∀ (x : K) i, ∀ y ∈ (nbhd x).U ∩ K, A.P (s x i y) = y
  equivariant : ∀ (x : K) (g : A.X.Isotropy x) i, ∀ y ∈ (nbhd x).U ∩ K,
    s x (g • i) ((nbhd x).rep.Φ g y) = fibAct ((nbhd x).rep.Γ g y) (s x i y)
  rep : ∀ (x : K) w, A.P w ∈ (nbhd x).U ∩ K →
    Λ w = (Fintype.card (ι.I x) : ℚ≥0)⁻¹ *
      ((Finset.univ.filter fun i => s x i (A.P w) = w).card : ℚ≥0)
  /-- The correspondences `τ_{x,x'}`. -/
  τ : ∀ x x' : A.Obj, A.Mor → IndexCorr (ι.I x) (ι.I x')
  locallyConstant : ∀ x x' : K, ∀ φ ∈ A.X.morBetween ((nbhd x).U ∩ K) ((nbhd x').U ∩ K),
    ∀ᶠ ψ in 𝓝[A.X.morBetween ((nbhd x).U ∩ K) ((nbhd x').U ∩ K)] φ, τ x x' ψ = τ x x' φ
  finite : ∀ x x' : K, (τ x x' '' A.X.morBetween ((nbhd x).U ∩ K) ((nbhd x').U ∩ K)).Finite
  swap : ∀ x x' : K, ∀ φ ∈ A.X.morBetween ((nbhd x).U ∩ K) ((nbhd x').U ∩ K),
    τ x' x (A.X.inv φ) = (τ x x' φ).swap
  diag : ∀ (x : K) (g : A.X.Isotropy x), ∀ z ∈ (nbhd x).U ∩ K,
    τ x x ((nbhd x).rep.Γ g z) = IndexCorr.ofPerm (α := ι.I x) g
  biact : ∀ x x' : K, ∀ φ ∈ A.X.morBetween ((nbhd x).U ∩ K) ((nbhd x').U ∩ K),
    ∀ (g' : A.X.Isotropy x') (g : A.X.Isotropy x),
      τ x x' (EpGroupoid.biact (nbhd x) (nbhd x') g' φ g) = IndexCorr.biact g' (τ x x' φ) g
  compat : ∀ x x' : K, ∀ φ ∈ A.X.morBetween ((nbhd x).U ∩ K) ((nbhd x').U ∩ K),
    (τ x x' φ).Sat fun i j => s x' j (A.X.tgt φ) = fibAct φ (s x i (A.X.src φ))

namespace RelTuple

variable {K : Set A.Obj} {ι ι' ι'' : IndexFamily A}

/-- `U(x) ∩ K`. -/
def U (T : RelTuple A K ι) (x : K) : Set A.Obj := (T.nbhd x).U ∩ K

/-- `𝒰(x, x')`. -/
def mor (T : RelTuple A K ι) (x x' : K) : Set A.Mor := A.X.morBetween (T.U x) (T.U x')

/-- **The equivalence** ("similar to the `X`-case", Definition 13.3.8, in the form of
`BoundaryStructuredTuple.Equiv`): `Λ = Λ'` over `K`, open `O(x) ∋ x` with
`O(x) ∩ K ⊆ U(x) ∩ U'(x)`, `I_x = I'_x`, and `τ = τ'` (transported along these equalities) on the
morphisms between the `O(x) ∩ K`. -/
def Equiv (T : RelTuple A K ι) (T' : RelTuple A K ι') : Prop :=
  (∀ w, A.P w ∈ K → T.Λ w = T'.Λ w) ∧
  ∃ O : K → Set A.Obj, (∀ x, IsOpen (O x)) ∧ (∀ x, (x : A.Obj) ∈ O x) ∧
    (∀ x, O x ∩ K ⊆ T.U x ∩ T'.U x) ∧
    ∃ hI : ∀ x : K, ι.I x = ι'.I x, ∀ x x' : K,
      ∀ φ ∈ A.X.morBetween (O x ∩ K) (O x' ∩ K),
        T'.τ x x' φ = (T.τ x x' φ).map (_root_.Equiv.cast (hI x)) (_root_.Equiv.cast (hI x'))

theorem Equiv.refl (T : RelTuple A K ι) : T.Equiv T :=
  ⟨fun _ _ => rfl, fun x => (T.nbhd x).U, fun x => (T.nbhd x).isOpen_U,
    fun x => (T.nbhd x).mem_U, fun _ _ hy => ⟨hy, hy⟩, fun _ => rfl,
    fun _ _ _ _ => (IndexCorr.map_cast_rfl _).symm⟩

theorem Equiv.symm {T : RelTuple A K ι} {T' : RelTuple A K ι'} (h : T.Equiv T') : T'.Equiv T := by
  obtain ⟨hΛ, O, hO, hxO, hsub, hI, hτ⟩ := h
  refine ⟨fun w hw => (hΛ w hw).symm, O, hO, hxO,
    fun x y hy => ⟨(hsub x hy).2, (hsub x hy).1⟩, fun x => (hI x).symm,
    fun x x' φ hφ => ?_⟩
  rw [hτ x x' φ hφ, IndexCorr.map_cast_symm]

theorem Equiv.trans {T : RelTuple A K ι} {T' : RelTuple A K ι'} {T'' : RelTuple A K ι''}
    (h₁ : T.Equiv T') (h₂ : T'.Equiv T'') : T.Equiv T'' := by
  obtain ⟨hΛ₁, O₁, hO₁, hxO₁, hsub₁, hI₁, hτ₁⟩ := h₁
  obtain ⟨hΛ₂, O₂, hO₂, hxO₂, hsub₂, hI₂, hτ₂⟩ := h₂
  refine ⟨fun w hw => (hΛ₁ w hw).trans (hΛ₂ w hw), fun x => O₁ x ∩ O₂ x,
    fun x => (hO₁ x).inter (hO₂ x), fun x => ⟨hxO₁ x, hxO₂ x⟩,
    fun x y hy => ⟨(hsub₁ x ⟨hy.1.1, hy.2⟩).1, (hsub₂ x ⟨hy.1.2, hy.2⟩).2⟩,
    fun x => (hI₁ x).trans (hI₂ x), fun x x' φ hφ => ?_⟩
  have h₁ : φ ∈ A.X.morBetween (O₁ x ∩ K) (O₁ x' ∩ K) :=
    ⟨⟨hφ.1.1.1, hφ.1.2⟩, ⟨hφ.2.1.1, hφ.2.2⟩⟩
  have h₂ : φ ∈ A.X.morBetween (O₂ x ∩ K) (O₂ x' ∩ K) :=
    ⟨⟨hφ.1.1.2, hφ.1.2⟩, ⟨hφ.2.1.2, hφ.2.2⟩⟩
  rw [hτ₂ x x' φ h₂, hτ₁ x x' φ h₁, IndexCorr.map_cast_trans]

/-- The tuples over `K` with any index family. -/
def Sigma (A : SEP.{u}) (K : Set A.Obj) : Type (u + 1) := Σ ι : IndexFamily A, RelTuple A K ι

instance setoid (A : SEP.{u}) (K : Set A.Obj) : Setoid (Sigma A K) where
  r T T' := T.2.Equiv T'.2
  iseqv := ⟨fun T => Equiv.refl T.2, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-! ### Definition 14.6.1: restriction -/

/-- **The restriction to `K' ⊆ K`** (Definition 14.6.1 for `K' = F ∩ F'`): the same `Λ`, `I`, `s`,
`τ`, with the neighbourhoods `U(x) ∩ K'` for `x ∈ K'` and the correspondences restricted to the
morphisms between them. -/
def restrictTo (T : RelTuple A K ι) (K' : Set A.Obj) (h : K' ⊆ K) : RelTuple A K' ι where
  Λ := T.Λ
  isFunctor q hq := T.isFunctor q (h hq)
  nbhd x := T.nbhd ⟨x, h x.2⟩
  isProper x := isProperMap_domRestrict_of_subset_of_isClosed A.X.continuous_src
    (T.isProper ⟨x, h x.2⟩) (closure_mono (inter_subset_inter_right _ h)) isClosed_closure
  s := T.s
  P_s x i y hy := T.P_s ⟨x, h x.2⟩ i y ⟨hy.1, h hy.2⟩
  equivariant x g i y hy := T.equivariant ⟨x, h x.2⟩ g i y ⟨hy.1, h hy.2⟩
  rep x w hw := T.rep ⟨x, h x.2⟩ w ⟨hw.1, h hw.2⟩
  τ := T.τ
  locallyConstant x x' φ hφ := by
    have hsub : A.X.morBetween ((T.nbhd ⟨x, h x.2⟩).U ∩ K') ((T.nbhd ⟨x', h x'.2⟩).U ∩ K') ⊆
        A.X.morBetween ((T.nbhd ⟨x, h x.2⟩).U ∩ K) ((T.nbhd ⟨x', h x'.2⟩).U ∩ K) :=
      morBetween_mono (inter_subset_inter_right _ h) (inter_subset_inter_right _ h)
    exact (T.locallyConstant ⟨x, h x.2⟩ ⟨x', h x'.2⟩ φ (hsub hφ)).filter_mono
      (nhdsWithin_mono _ hsub)
  finite x x' := (T.finite ⟨x, h x.2⟩ ⟨x', h x'.2⟩).subset (image_mono
    (morBetween_mono (inter_subset_inter_right _ h) (inter_subset_inter_right _ h)))
  swap x x' φ hφ := T.swap ⟨x, h x.2⟩ ⟨x', h x'.2⟩ φ
    ⟨⟨hφ.1.1, h hφ.1.2⟩, ⟨hφ.2.1, h hφ.2.2⟩⟩
  diag x g z hz := T.diag ⟨x, h x.2⟩ g z ⟨hz.1, h hz.2⟩
  biact x x' φ hφ g' g := T.biact ⟨x, h x.2⟩ ⟨x', h x'.2⟩ φ
    ⟨⟨hφ.1.1, h hφ.1.2⟩, ⟨hφ.2.1, h hφ.2.2⟩⟩ g' g
  compat x x' φ hφ := T.compat ⟨x, h x.2⟩ ⟨x', h x'.2⟩ φ
    ⟨⟨hφ.1.1, h hφ.1.2⟩, ⟨hφ.2.1, h hφ.2.2⟩⟩

@[simp] theorem restrictTo_Λ (T : RelTuple A K ι) {K' : Set A.Obj} (h : K' ⊆ K) :
    (T.restrictTo K' h).Λ = T.Λ := rfl

@[simp] theorem restrictTo_s (T : RelTuple A K ι) {K' : Set A.Obj} (h : K' ⊆ K) :
    (T.restrictTo K' h).s = T.s := rfl

@[simp] theorem restrictTo_τ (T : RelTuple A K ι) {K' : Set A.Obj} (h : K' ⊆ K) :
    (T.restrictTo K' h).τ = T.τ := rfl

theorem restrictTo_U (T : RelTuple A K ι) {K' : Set A.Obj} (h : K' ⊆ K) (x : K') :
    (T.restrictTo K' h).U x = T.U ⟨x, h x.2⟩ ∩ K' := by
  simp only [U, restrictTo, inter_assoc, inter_eq_right.2 h]

/-- **Restriction respects the equivalence** (so Definition 14.6.1 is well defined on classes:
"obtained by taking a representative"). -/
theorem Equiv.restrictTo {T : RelTuple A K ι} {T' : RelTuple A K ι'} (hT : T.Equiv T')
    {K' : Set A.Obj} (h : K' ⊆ K) : (T.restrictTo K' h).Equiv (T'.restrictTo K' h) := by
  obtain ⟨hΛ, O, hO, hxO, hsub, hI, hτ⟩ := hT
  refine ⟨fun w hw => hΛ w (h hw), fun x => O ⟨x, h x.2⟩, fun x => hO _, fun x => hxO _,
    fun x y hy => ?_, fun x => hI ⟨x, h x.2⟩, fun x x' φ hφ => ?_⟩
  · have := hsub ⟨x, h x.2⟩ ⟨hy.1, h hy.2⟩
    exact ⟨⟨this.1.1, hy.2⟩, ⟨this.2.1, hy.2⟩⟩
  · exact hτ ⟨x, h x.2⟩ ⟨x', h x'.2⟩ φ ⟨⟨hφ.1.1, h hφ.1.2⟩, ⟨hφ.2.1, h hφ.2.2⟩⟩

/-- Restricting twice is restricting once (the text's `Λ̃_{F ∩ F' ∩ F''}` "can be done for an
arbitrary number of faces"). -/
theorem restrictTo_restrictTo_equiv (T : RelTuple A K ι) {K' K'' : Set A.Obj} (h : K' ⊆ K)
    (h' : K'' ⊆ K') : ((T.restrictTo K' h).restrictTo K'' h').Equiv
      (T.restrictTo K'' (h'.trans h)) :=
  Equiv.refl (T.restrictTo K'' (h'.trans h))

end RelTuple

/-- **Structured multisections over `K`**: the classes of `RelTuple`s. -/
def RelStructured (A : SEP.{u}) (K : Set A.Obj) : Type (u + 1) :=
  Quotient (RelTuple.setoid A K)

/-- Definition 14.6.1 on classes. -/
def RelStructured.restrictTo {K : Set A.Obj} (L : RelStructured A K) (K' : Set A.Obj)
    (h : K' ⊆ K) : RelStructured A K' :=
  Quotient.map (fun T => ⟨T.1, T.2.restrictTo K' h⟩)
    (fun a b (hT : a.2.Equiv b.2) => RelTuple.Equiv.restrictTo hT h) L

/-! ### Structured sc⁺-multisections on `W|F` -/

/-- **A representative `(Λ_F, 𝒰_F, S_F, τ_F)` of a structured sc⁺-multisection on `W|F`** (§14.6,
p. 680): a `RelTuple` over the face `F` whose sections are sc⁺-sections of `W|F` on the
`U_F(x) = U(x) ∩ F` (relative to `F`, `IsFaceRelScPlusSectionOn`). -/
structure FaceStructuredTuple (A : SEP.{u}) (F : Set A.Obj) (ι : IndexFamily A) extends
    RelTuple A F ι where
  isFaceRelScPlus : ∀ (x : F) i, IsFaceRelScPlusSectionOn A F (s x i) ((nbhd x).U ∩ F)

namespace FaceStructuredTuple

variable {F F' : Set A.Obj} {ι : IndexFamily A}

/-- **Definition 14.6.1**: `Λ̃_F|F'`, the restriction to `W|(F ∩ F')`. -/
def restrictFace (T : FaceStructuredTuple A F ι) (F' : Set A.Obj) : RelTuple A (F ∩ F') ι :=
  T.toRelTuple.restrictTo (F ∩ F') inter_subset_left

/-- The sections of `Λ̃_F|F'` are restrictions of sc⁺-sections of `W|F`. -/
theorem restrictFace_isFaceRelScPlus (T : FaceStructuredTuple A F ι) (F' : Set A.Obj)
    (x : ↥(F ∩ F')) (i : ι.I x) :
    IsFaceRelScPlusSectionOn A F ((T.restrictFace F').s x i) ((T.restrictFace F').U x) :=
  (T.isFaceRelScPlus ⟨x, x.2.1⟩ i).mono fun _ hy => ⟨hy.1, hy.2.1⟩

end FaceStructuredTuple

/-- The face tuples over `F` with any index family, with the equivalence of the underlying
`RelTuple`s. -/
instance FaceStructuredTuple.setoid (A : SEP.{u}) (F : Set A.Obj) :
    Setoid (Σ ι : IndexFamily A, FaceStructuredTuple A F ι) where
  r T T' := T.2.toRelTuple.Equiv T'.2.toRelTuple
  iseqv := ⟨fun T => RelTuple.Equiv.refl T.2.toRelTuple, fun h => h.symm,
    fun h₁ h₂ => h₁.trans h₂⟩

/-- **A structured sc⁺-multisection `Λ̃_F = [Λ_F, 𝒰_F, S_F, τ_F]` on `W|F`** (§14.6, p. 680). -/
def FaceStructuredMultisection (A : SEP.{u}) (F : Set A.Obj) : Type (u + 1) :=
  Quotient (FaceStructuredTuple.setoid A F)

/-- **Definition 14.6.1 on classes**: `Λ̃_F|F' = [Λ_F|F', 𝒰_F|F', S_F|F', τ_F|F']`, a class over
`F ∩ F'`, independent of the representative. -/
def FaceStructuredMultisection.restrictFace {F : Set A.Obj} (L : FaceStructuredMultisection A F)
    (F' : Set A.Obj) : RelStructured A (F ∩ F') :=
  Quotient.map (fun T => ⟨T.1, T.2.restrictFace F'⟩)
    (fun a b (hT : a.2.toRelTuple.Equiv b.2.toRelTuple) =>
      RelTuple.Equiv.restrictTo hT inter_subset_left) L

/-- The class of `Λ̃_{F'}|F` as a class over `F ∩ F'` (the text's `Λ̃_{F'}|F`, whose base
`F' ∩ F` is `F ∩ F'`). -/
def FaceStructuredMultisection.restrictFace' {F' : Set A.Obj}
    (L : FaceStructuredMultisection A F') (F : Set A.Obj) : RelStructured A (F ∩ F') :=
  Quotient.map (fun T => ⟨T.1, T.2.toRelTuple.restrictTo (F ∩ F') inter_subset_right⟩)
    (fun a b (hT : a.2.toRelTuple.Equiv b.2.toRelTuple) =>
      RelTuple.Equiv.restrictTo hT inter_subset_right) L

/-! ### Definition 14.6.2 -/

/-- **2021 Definition 14.6.2, p. 681 (2017: Definition 14.11)**: an assignment `F ↦ Λ̃_F` of
structured sc⁺-multisections on the `W|F`, `F` a face of `X`, is **compatible** if
`Λ̃_F|F' = Λ̃_{F'}|F` for all faces `F, F'` (classes over `F ∩ F'`). -/
def IsCompatibleAssignment (Λt : ∀ F, A.X.IsEpFace F → FaceStructuredMultisection A F) : Prop :=
  ∀ F (hF : A.X.IsEpFace F) F' (hF' : A.X.IsEpFace F'),
    (Λt F hF).restrictFace F' = (Λt F' hF').restrictFace' F

/-- **For a compatible assignment, `Λ̃_{F ∩ F'} := Λ̃_F|F'`** (Definition 14.6.2). -/
def IsCompatibleAssignment.inter {Λt : ∀ F, A.X.IsEpFace F → FaceStructuredMultisection A F}
    (_ : IsCompatibleAssignment Λt) (F : Set A.Obj) (hF : A.X.IsEpFace F) (F' : Set A.Obj) :
    RelStructured A (F ∩ F') :=
  (Λt F hF).restrictFace F'

section Consequences

variable {Λt : ∀ F, A.X.IsEpFace F → FaceStructuredMultisection A F}

theorem IsCompatibleAssignment.equiv (h : IsCompatibleAssignment Λt) {F F' : Set A.Obj}
    (hF : A.X.IsEpFace F) (hF' : A.X.IsEpFace F') :
    ((Quotient.out (Λt F hF)).2.restrictFace F').Equiv
      ((Quotient.out (Λt F' hF')).2.toRelTuple.restrictTo (F ∩ F') inter_subset_right) := by
  have e := h F hF F' hF'
  rw [← Quotient.out_eq (Λt F hF), ← Quotient.out_eq (Λt F' hF')] at e
  exact Quotient.exact e

/-- **"As a consequence of the compatibility condition `I^F_x = I^{F'}_x`"** (p. 682), for the
representatives of the classes and `x ∈ F ∩ F'`. -/
theorem IsCompatibleAssignment.index_eq (h : IsCompatibleAssignment Λt) {F F' : Set A.Obj}
    (hF : A.X.IsEpFace F) (hF' : A.X.IsEpFace F') (x : ↥(F ∩ F')) :
    (Quotient.out (Λt F hF)).1.I x = (Quotient.out (Λt F' hF')).1.I x := by
  obtain ⟨-, -, -, -, -, hI, -⟩ := h.equiv hF hF'
  exact hI x

/-- For a compatible assignment, `Λ_F = Λ_{F'}` over `F ∩ F'`. -/
theorem IsCompatibleAssignment.Λ_eq (h : IsCompatibleAssignment Λt) {F F' : Set A.Obj}
    (hF : A.X.IsEpFace F) (hF' : A.X.IsEpFace F') {w : A.W} (hw : A.P w ∈ F ∩ F') :
    (Quotient.out (Λt F hF)).2.Λ w = (Quotient.out (Λt F' hF')).2.Λ w :=
  (h.equiv hF hF').1 w hw

end Consequences

/-! ### The zero multisection on every face (nonvacuity) -/

/-- The index family `I_x = {∗}`. -/
def IndexFamily.unit (A : SEP.{u}) : IndexFamily A where
  I _ := PUnit.{u + 1}

/-- **The zero multisection as a structured sc⁺-multisection on `W|F`**, `F` a face, on chosen
neighbourhoods `N(x)` (`I_x = {∗}`, `s = 0`, `τ ≡ [{∗} ← {∗} → {∗}]`). -/
def FaceStructuredTuple.zero {F : Set A.Obj} (hF : F ⊆ A.X.PObj.boundary)
    (N : ∀ x : F, A.X.NatNbhd x) (hN : ∀ x, A.X.IsProperSubset (closure (N x).U)) :
    FaceStructuredTuple A F (IndexFamily.unit A) where
  Λ := zeroMultisection A
  isFunctor q _ := isWFunctor_zeroMultisection A q
  nbhd := N
  isProper x := isProperMap_domRestrict_of_subset_of_isClosed A.X.continuous_src
    (hN x) (closure_mono inter_subset_left) isClosed_closure
  s _ _ := fiberZero A.P
  P_s _ _ y _ := proj_fiberZero A.P y
  equivariant x g _ y hy :=
    (fibAct_fiberZero ((N x).src_Γ g hy.1) ((N x).tgt_Γ g hy.1)).symm
  rep x w _ := by
    by_cases h : w = fiberZero A.P (A.P w)
    · rw [Finset.filter_true_of_mem fun _ _ => h.symm]
      have h1 : Fintype.card ((IndexFamily.unit A).I x) = 1 :=
        Fintype.card_eq_one_iff.2 ⟨PUnit.unit, fun _ => rfl⟩
      rw [Finset.card_univ, h1]
      simp [zeroMultisection, if_pos h]
    · rw [Finset.filter_false_of_mem fun _ _ e => h e.symm]
      simp [zeroMultisection, if_neg h]
  τ _ _ _ := IndexCorr.ofEquiv (_root_.Equiv.refl PUnit.{u + 1})
  locallyConstant _ _ _ _ := Eventually.of_forall fun _ => rfl
  finite _ _ := (finite_singleton (IndexCorr.ofEquiv (_root_.Equiv.refl PUnit.{u + 1}))).subset
    (by rintro _ ⟨_, _, rfl⟩; rfl)
  swap _ _ _ _ := (IndexCorr.swap_ofEquiv_of_subsingleton (α := PUnit.{u + 1}) _).symm
  diag _ _ _ _ := IndexCorr.ofEquiv_eq_of_subsingleton (α := PUnit.{u + 1}) _ _
  biact _ _ _ _ g' g := (IndexCorr.example_13_3_3 g' _ g).symm
  compat _ _ _ _ := IndexCorr.sat_of_forall (fun _ _ => (fibAct_fiberZero rfl rfl).symm) _
  isFaceRelScPlus _ _ := isFaceRelScPlusSectionOn_fiberZero (inter_subset_right.trans hF)

/-- **Nonvacuity of Definitions 14.6.1 and 14.6.2**: the assignment of the zero multisection to
every face (on any choice of neighbourhoods) is compatible. -/
theorem isCompatibleAssignment_zero
    (N : ∀ F, A.X.IsEpFace F → ∀ x : F, A.X.NatNbhd x)
    (hN : ∀ F hF x, A.X.IsProperSubset (closure (N F hF x).U)) :
    IsCompatibleAssignment fun F hF =>
      Quotient.mk (FaceStructuredTuple.setoid A F)
        ⟨IndexFamily.unit A, FaceStructuredTuple.zero (IsEpFace.subset_boundary hF) (N F hF)
          (hN F hF)⟩ := by
  intro F hF F' hF'
  refine Quotient.sound ⟨fun _ _ => rfl,
    fun x => (N F hF ⟨x, x.2.1⟩).U ∩ (N F' hF' ⟨x, x.2.2⟩).U,
    fun x => (N F hF _).isOpen_U.inter (N F' hF' _).isOpen_U,
    fun x => ⟨(N F hF _).mem_U, (N F' hF' _).mem_U⟩,
    fun x y hy => ⟨⟨hy.1.1, hy.2⟩, ⟨hy.1.2, hy.2⟩⟩, fun _ => rfl,
    fun _ _ _ _ => (IndexCorr.map_cast_rfl _).symm⟩

end SBLocalization

end Polyfold
