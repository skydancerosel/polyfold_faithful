import Polyfold.Chapter14.FaceSectionCompatible
import Polyfold.Chapter13.AtomicStructurable

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.6, pp. 680–682:
**Definition 14.6.2** and **Theorem 14.6.3** (2017: Definition 14.11, Theorem 14.4) for face
representatives with their own index sets `I^F_x`, the compatibility read with the sections.

# Compatible assignments with different index families

## The text, paraphrased

(p. 680) Every face `F` carries a structured sc⁺-multisection `Λ̃_F = [Λ_F, 𝒰_F, S_F, τ_F]` with
index sets `I^F_x`, `x ∈ F`.  (p. 682) "As a consequence of the compatibility condition"
`I^F_x = I^{F'}_x` for `x ∈ F ∩ F'`, and the text abbreviates `I_x := I^F_x`.  (Theorem 14.6.3)
A compatible assignment defines a structured `Λ̃ : W|∂X → ℚ⁺`, which extends to `W`.

## What is formalized (namespace `Polyfold.SBLocalization`)

`SectionCompatibleFaceData` (`FaceSectionCompatible.lean`) has one index family for all faces.
Here every face has its own family, and they are identified only on the intersections:

* Relabelling: `IndexRelabel K κ ι` (maps `κ.I x → ι.I x`, bijective and equivariant for
  `x ∈ K`), `RelTuple.reindex`, `FaceStructuredTuple.reindex`.  The relabelled tuple is
  section-equivalent to the original when the maps are casts (`RelTuple.reindex_secEquiv`);
  relabelling respects `SecEquiv` (`RelTuple.SecEquiv.reindex`) and restriction
  (`RelTuple.reindex_restrictTo_secEquiv`); `RelTuple.SecEquiv.restrictTo`.
* The identification `I^F_x = I^{F'}_x` of `SecEquiv` is equivariant
  (`RelTuple.Equiv.cast_smul`): this follows from (1) of Definition 13.3.6 (`τ(Γ(g, x)) = [g]`)
  and the equality of the correspondences.
* `SectionCompatibleFaceFamilies A`: a family `I^F` and a tuple on every face, and
  `Λ̃_F|F'` `SecEquiv` `Λ̃_{F'}|F` (Definition 14.6.2 with the sections).
  `SectionCompatibleFaceFamilies.commonFamily`: `I_x := I^{F₀}_x` for a chosen face `F₀ ∋ x`;
  `toData`: the tuples relabelled to it, a `SectionCompatibleFaceData`; `toData_secEquiv`: each
  is section-equivalent to the given one.
* **`SectionCompatibleFaceFamilies.theorem_14_6_3`** and `theorem_14_6_3_extension`: Theorem
  14.6.3 for such an assignment, with the text's hypotheses.
* Classes: `FaceSecMultisection A F` (face tuples modulo `SecEquiv`, any index family),
  `IsSecCompatibleAssignment` (Definition 14.6.2 on these classes),
  `IsSecCompatibleAssignment.toFamilies`, and **`IsSecCompatibleAssignment.theorem_14_6_3`**:
  Theorem 14.6.3 for a compatible assignment of classes, in this reading.
* Witness (namespace `FaceCorner`): on the quadrant example the corner tuples relabelled to the
  families `I^F_x = {b : Bool // x ∈ F ∨ b}`, of two elements on `F` and one element off `F`
  (`familiesWitness`); at the point `(1, 0, 0)` two faces have families with one and two elements
  (`card_familiesWitness_ne`), and Theorem 14.6.3 applies (`theorem_14_6_3_families_witness`).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

/-! ### Relabelling correspondences -/

namespace IndexCorr

variable {α β α' β' : Type u}

theorem map_swap (e : α ≃ α') (e' : β ≃ β') (τ : IndexCorr α β) :
    (τ.map e e').swap = τ.swap.map e' e :=
  ind (fun _ => rfl) τ

section Act

variable {G G' : Type*} [Group G] [Group G'] [MulAction G α] [MulAction G α'] [MulAction G' β]
  [MulAction G' β']

/-- Relabelling along equivariant bijections commutes with the bi-action. -/
theorem map_biact (e : α ≃ α') (e' : β ≃ β') (he : ∀ (g : G) a, e (g • a) = g • e a)
    (he' : ∀ (g' : G') b, e' (g' • b) = g' • e' b) (g' : G') (τ : IndexCorr α β) (g : G) :
    (biact g' τ g).map e e' = biact g' (τ.map e e') g :=
  ind (fun _ => mk_eq_mk.2 ⟨_root_.Equiv.refl _, fun _ => ⟨(he _ _).symm, (he' _ _).symm⟩⟩) τ

/-- Relabelling `[g]` along an equivariant bijection gives `[g]`. -/
theorem map_ofPerm [Fintype α] [Fintype α'] (e : α ≃ α') (he : ∀ (g : G) a, e (g • a) = g • e a)
    (g : G) : (ofPerm g : IndexCorr α α).map e e = ofPerm g := by
  unfold ofPerm ofEquiv
  rw [map_mk]
  refine mk_eq_mk.2 ⟨e, fun k => ⟨rfl, ?_⟩⟩
  simp only [IndexDiagram.map, IndexDiagram.ofEquiv, Function.comp, MulAction.toPerm_apply]
  exact (he g k).symm

/-- Conversely, a bijection which relabels `[g]` to `[g]` commutes with `g`. -/
theorem smul_of_map_ofPerm [Fintype α] [Fintype α'] (e : α ≃ α') (g : G)
    (h : (ofPerm g : IndexCorr α α).map e e = ofPerm g) (a : α) : e (g • a) = g • e a := by
  obtain ⟨c, hc⟩ := mk_eq_mk.1 h
  have h1 : (show α' from c a) = e a := (hc a).1
  have h2 : g • (show α' from c a) = e (g • a) := (hc a).2
  exact h2.symm.trans (congrArg (fun b : α' => g • b) h1)

end Act

end IndexCorr

variable {A : SEP.{u}}

/-! ### Relabelling the index sets of a tuple -/

/-- **Relabelling data** over `K`: maps `κ.I x → ι.I x`, bijective and `G_x`-equivariant for
`x ∈ K` (arbitrary off `K`). -/
structure IndexRelabel (K : Set A.Obj) (κ ι : IndexFamily A) where
  /-- The maps `κ.I x → ι.I x`. -/
  f : ∀ x : A.Obj, κ.I x → ι.I x
  bijective : ∀ x : K, Bijective (f x)
  smul : ∀ (x : K) (g : A.X.Isotropy x) (i : κ.I x), f x (g • i) = g • f x i

namespace IndexRelabel

variable {K : Set A.Obj} {κ ι : IndexFamily A} (R : IndexRelabel K κ ι)

/-- The bijection `κ.I x ≃ ι.I x`, `x ∈ K`. -/
def e (x : K) : κ.I x ≃ ι.I x := _root_.Equiv.ofBijective (R.f x) (R.bijective x)

theorem e_apply (x : K) (i : κ.I x) : R.e x i = R.f x i := rfl

theorem f_e_symm (x : K) (j : ι.I x) : R.f x ((R.e x).symm j) = j :=
  (R.e x).apply_symm_apply j

theorem e_symm_smul (x : K) (g : A.X.Isotropy x) (j : ι.I x) :
    (R.e x).symm (g • j) = g • (R.e x).symm j := by
  apply (R.e x).injective
  rw [_root_.Equiv.apply_symm_apply, e_apply, R.smul, ← e_apply, _root_.Equiv.apply_symm_apply]

/-- The same data over a smaller set. -/
def restrict {K' : Set A.Obj} (h : K' ⊆ K) : IndexRelabel K' κ ι where
  f := R.f
  bijective x := R.bijective ⟨x, h x.2⟩
  smul x := R.smul ⟨x, h x.2⟩

end IndexRelabel

namespace RelTuple

variable {K : Set A.Obj} {ι ι' κ κ' : IndexFamily A}

/-- The relabelled correspondences `[e⁻¹ ∘ a, e'⁻¹ ∘ b]` (the full correspondence off `K`). -/
def reindexτ (T : RelTuple A K ι) (R : IndexRelabel K κ ι) (x x' : A.Obj) (φ : A.Mor) :
    IndexCorr (κ.I x) (κ.I x') :=
  if h : x ∈ K ∧ x' ∈ K then (T.τ x x' φ).map (R.e ⟨x, h.1⟩).symm (R.e ⟨x', h.2⟩).symm
  else IndexCorr.full _ _

theorem reindexτ_of_mem (T : RelTuple A K ι) (R : IndexRelabel K κ ι) {x x' : A.Obj}
    (hx : x ∈ K) (hx' : x' ∈ K) (φ : A.Mor) :
    T.reindexτ R x x' φ = (T.τ x x' φ).map (R.e ⟨x, hx⟩).symm (R.e ⟨x', hx'⟩).symm :=
  dif_pos ⟨hx, hx'⟩

/-- **The tuple with the index sets relabelled** along `R`: `s'ˣᵢ = sˣ_{f(i)}`, the
correspondences relabelled; `Λ`, the neighbourhoods and the actions are unchanged. -/
def reindex (T : RelTuple A K ι) (R : IndexRelabel K κ ι) : RelTuple A K κ where
  Λ := T.Λ
  isFunctor := T.isFunctor
  nbhd := T.nbhd
  isProper := T.isProper
  s x i := T.s x (R.f x i)
  P_s x i := T.P_s x (R.f x i)
  equivariant x g i y hy := by
    rw [R.smul]
    exact T.equivariant x g (R.f x i) y hy
  rep x w hw := by
    rw [T.rep x w hw, Fintype.card_congr (R.e x)]
    congr 2
    refine Finset.card_equiv (R.e x).symm fun j => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, R.f_e_symm]
  τ := T.reindexτ R
  locallyConstant x x' φ hφ := (T.locallyConstant x x' φ hφ).mono fun ψ hψ => by
    rw [reindexτ_of_mem _ _ x.2 x'.2, reindexτ_of_mem _ _ x.2 x'.2, hψ]
  finite x x' := ((T.finite x x').image (IndexCorr.map (R.e x).symm (R.e x').symm)).subset (by
    rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨T.τ x x' φ, ⟨φ, hφ, rfl⟩, (reindexτ_of_mem _ _ x.2 x'.2 φ).symm⟩)
  swap x x' φ hφ := by
    rw [reindexτ_of_mem _ _ x'.2 x.2, reindexτ_of_mem _ _ x.2 x'.2, T.swap x x' φ hφ,
      IndexCorr.map_swap]
  diag x g z hz := by
    rw [reindexτ_of_mem _ _ x.2 x.2, T.diag x g z hz]
    exact IndexCorr.map_ofPerm _ (R.e_symm_smul x) g
  biact x x' φ hφ g' g := by
    rw [reindexτ_of_mem _ _ x.2 x'.2, reindexτ_of_mem _ _ x.2 x'.2, T.biact x x' φ hφ g' g]
    exact IndexCorr.map_biact _ _ (R.e_symm_smul x) (R.e_symm_smul x') g' _ g
  compat x x' φ hφ := by
    rw [reindexτ_of_mem _ _ x.2 x'.2]
    refine IndexCorr.sat_map _ _ (fun i j h => ?_) (T.compat x x' φ hφ)
    change T.s x' (R.f x' ((R.e x').symm j)) _ = fibAct φ (T.s x (R.f x ((R.e x).symm i)) _)
    rw [R.f_e_symm, R.f_e_symm]
    exact h

theorem reindex_τ (T : RelTuple A K ι) (R : IndexRelabel K κ ι) (x x' : K) (φ : A.Mor) :
    (T.reindex R).τ x x' φ = (T.τ x x' φ).map (R.e x).symm (R.e x').symm :=
  reindexτ_of_mem T R x.2 x'.2 φ

/-- **Relabelling along casts gives a section-equivalent tuple.** -/
theorem reindex_secEquiv (T : RelTuple A K ι) (R : IndexRelabel K κ ι)
    (hR : ∀ x : K, ∃ h : κ.I x = ι.I x, ∀ i, R.f x i = cast h i) : (T.reindex R).SecEquiv T := by
  have he : ∀ x : K, R.e x = _root_.Equiv.cast (hR x).choose := fun x =>
    _root_.Equiv.ext fun i => (hR x).choose_spec i
  refine ⟨fun _ _ => rfl, fun x => (T.nbhd x).U, fun x => (T.nbhd x).isOpen_U,
    fun x => (T.nbhd x).mem_U, fun _ _ hy => ⟨hy, hy⟩, fun x => (hR x).choose,
    fun x i y _ => ?_, fun x x' φ _ => ?_⟩
  · change T.s x (cast _ i) y = T.s x (R.f x i) y
    rw [(hR x).choose_spec i]
  · rw [reindex_τ, IndexCorr.map_map, ← he, ← he, _root_.Equiv.symm_trans_self,
      _root_.Equiv.symm_trans_self, IndexCorr.map_refl]

/-- **Relabelling respects the equivalence with sections**, when the relabellings agree with
the identification of the index sets. -/
theorem SecEquiv.reindex {T : RelTuple A K ι} {T' : RelTuple A K ι'} (hT : T.SecEquiv T')
    (R : IndexRelabel K κ ι) (R' : IndexRelabel K κ' ι') (hκ : ∀ x : K, κ.I x = κ'.I x)
    (hc : ∀ (x : K) (h : ι.I x = ι'.I x) (i : κ.I x), R'.f x (cast (hκ x) i) = cast h (R.f x i)) :
    (T.reindex R).SecEquiv (T'.reindex R') := by
  obtain ⟨hΛ, O, hO, hxO, hsub, hI, hs, hτ⟩ := hT
  have hcomm : ∀ x : K, (_root_.Equiv.cast (hI x)).trans (R'.e x).symm =
      (R.e x).symm.trans (_root_.Equiv.cast (hκ x)) := fun x => _root_.Equiv.ext fun j => by
    apply (R'.e x).injective
    change R'.e x ((R'.e x).symm (cast (hI x) j)) = R'.f x (cast (hκ x) ((R.e x).symm j))
    rw [_root_.Equiv.apply_symm_apply, hc x (hI x), R.f_e_symm]
  refine ⟨hΛ, O, hO, hxO, hsub, hκ, fun x i y hy => ?_, fun x x' φ hφ => ?_⟩
  · change T'.s x (R'.f x (cast (hκ x) i)) y = T.s x (R.f x i) y
    rw [hc x (hI x)]
    exact hs x _ y hy
  · rw [reindex_τ, reindex_τ, hτ x x' φ hφ, IndexCorr.map_map, IndexCorr.map_map, hcomm, hcomm]

/-- **Restriction respects the equivalence with sections** (Definition 14.6.1 on classes). -/
theorem SecEquiv.restrictTo {T : RelTuple A K ι} {T' : RelTuple A K ι'} (hT : T.SecEquiv T')
    {K' : Set A.Obj} (h : K' ⊆ K) : (T.restrictTo K' h).SecEquiv (T'.restrictTo K' h) := by
  obtain ⟨hΛ, O, hO, hxO, hsub, hI, hs, hτ⟩ := hT
  refine ⟨fun w hw => hΛ w (h hw), fun x => O ⟨x, h x.2⟩, fun x => hO _, fun x => hxO _,
    fun x y hy => ?_, fun x => hI ⟨x, h x.2⟩, fun x i y hy => hs ⟨x, h x.2⟩ i y ⟨hy.1, h hy.2⟩,
    fun x x' φ hφ => ?_⟩
  · have := hsub ⟨x, h x.2⟩ ⟨hy.1, h hy.2⟩
    exact ⟨⟨this.1.1, hy.2⟩, ⟨this.2.1, hy.2⟩⟩
  · exact hτ ⟨x, h x.2⟩ ⟨x', h x'.2⟩ φ ⟨⟨hφ.1.1, h hφ.1.2⟩, ⟨hφ.2.1, h hφ.2.2⟩⟩

/-- Relabelling and restricting commute up to the equivalence with sections. -/
theorem reindex_restrictTo_secEquiv (T : RelTuple A K ι) (R : IndexRelabel K κ ι)
    {K' : Set A.Obj} (h : K' ⊆ K) :
    ((T.reindex R).restrictTo K' h).SecEquiv ((T.restrictTo K' h).reindex (R.restrict h)) := by
  refine ⟨fun _ _ => rfl, fun x => (T.nbhd ⟨x, h x.2⟩).U, fun x => (T.nbhd _).isOpen_U,
    fun x => (T.nbhd _).mem_U, fun _ _ hy => ⟨hy, hy⟩, fun _ => rfl, fun _ _ _ _ => rfl,
    fun x x' φ _ => ?_⟩
  rw [IndexCorr.map_cast_rfl, reindex_τ]
  exact (reindexτ_of_mem T R (h x.2) (h x'.2) φ).symm

/-- **The identification `I_x = I'_x` of equivalent tuples is equivariant**: (1) of Definition
13.3.6 gives `τ(g) = [g]` for `g ∈ G_x` in both tuples, and `τ' = τ` transported. -/
theorem Equiv.cast_smul {T : RelTuple A K ι} {T' : RelTuple A K ι'} (hT : T.Equiv T') (x : K)
    (h : ι.I x = ι'.I x) (g : A.X.Isotropy x) (i : ι.I x) : cast h (g • i) = g • cast h i := by
  obtain ⟨-, O, -, hxO, hsub, hI, hτ⟩ := hT
  have hm : g.val ∈ A.X.morBetween (O x ∩ K) (O x ∩ K) :=
    ⟨by rw [g.src_val]; exact ⟨hxO x, x.2⟩, by rw [g.tgt_val]; exact ⟨hxO x, x.2⟩⟩
  have d1 : T.τ x x g.val = IndexCorr.ofPerm g := by
    rw [← (T.nbhd x).rep.Γ_self g]; exact T.diag x g x ⟨(T.nbhd x).mem_U, x.2⟩
  have d2 : T'.τ x x g.val = IndexCorr.ofPerm g := by
    rw [← (T'.nbhd x).rep.Γ_self g]; exact T'.diag x g x ⟨(T'.nbhd x).mem_U, x.2⟩
  have h1 := hτ x x g.val hm
  rw [d1, d2] at h1
  exact IndexCorr.smul_of_map_ofPerm (_root_.Equiv.cast (hI x)) g h1.symm i

end RelTuple

/-- Relabelling a face tuple: the relabelled sections are the old ones, so still sc⁺. -/
def FaceStructuredTuple.reindex {F : Set A.Obj} {ι κ : IndexFamily A}
    (T : FaceStructuredTuple A F ι) (R : IndexRelabel F κ ι) : FaceStructuredTuple A F κ :=
  { T.toRelTuple.reindex R with isFaceRelScPlus := fun x i => T.isFaceRelScPlus x (R.f x i) }

/-! ### Assignments with an index family per face -/

/-- **A compatible assignment with the index families of the faces** (Definition 14.6.2, the
equivalence read with the sections, `RelTuple.SecEquiv`): on every face `F` a family `I^F` and a
representative `(Λ_F, 𝒰_F, S_F, τ_F)`, and `Λ̃_F|F'` equivalent to `Λ̃_{F'}|F` over `F ∩ F'`
(which identifies `I^F_x = I^{F'}_x` there). -/
structure SectionCompatibleFaceFamilies (A : SEP.{u}) where
  /-- The index families `I^F`. -/
  ι : ∀ F, A.X.IsEpFace F → IndexFamily A
  /-- The representatives `(Λ_F, 𝒰_F, S_F, τ_F)`. -/
  T : ∀ F (hF : A.X.IsEpFace F), FaceStructuredTuple A F (ι F hF)
  secEquiv : ∀ F hF F' hF', ((T F hF).restrictFace F').SecEquiv
    ((T F' hF').toRelTuple.restrictTo (F ∩ F') inter_subset_right)

/-- One index family for all faces is the special case of constant families. -/
def SectionCompatibleFaceData.toFamilies (S : SectionCompatibleFaceData A) :
    SectionCompatibleFaceFamilies A where
  ι _ _ := S.ι
  T := S.T
  secEquiv := S.secEquiv

namespace SectionCompatibleFaceFamilies

variable (S : SectionCompatibleFaceFamilies A)

/-- The family of a chosen face through `x` (the one-point family if there is none). -/
def pick (x : A.Obj) : IndexFamily A :=
  if h : ∃ F, A.X.IsEpFace F ∧ x ∈ F then S.ι h.choose h.choose_spec.1 else IndexFamily.unit A

theorem exists_pick {F : Set A.Obj} (hF : A.X.IsEpFace F) {x : A.Obj} (hx : x ∈ F) :
    ∃ (F₀ : Set A.Obj) (hF₀ : A.X.IsEpFace F₀), x ∈ F₀ ∧ S.pick x = S.ι F₀ hF₀ := by
  have h : ∃ F, A.X.IsEpFace F ∧ x ∈ F := ⟨F, hF, hx⟩
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, dif_pos h⟩

/-- **The common index family** `I_x := I^{F₀}_x` for a chosen face `F₀ ∋ x` (the text's
"we abbreviate `I_x := I^F_x`"). -/
def commonFamily : IndexFamily A where
  I x := (S.pick x).I x
  fintype x := (S.pick x).fintype x
  mulAction x := (S.pick x).mulAction x
  nonempty x := (S.pick x).nonempty x

theorem commonFamily_eq {F : Set A.Obj} (hF : A.X.IsEpFace F) {x : A.Obj} (hx : x ∈ F) :
    S.commonFamily.I x = (S.ι F hF).I x := by
  obtain ⟨F₀, hF₀, hx₀, he⟩ := S.exists_pick hF hx
  obtain ⟨-, -, -, -, -, hI, -⟩ := S.secEquiv F₀ hF₀ F hF
  change (S.pick x).I x = _
  rw [he]
  exact hI ⟨x, hx₀, hx⟩

theorem cast_smul_of_eq {κ κ' : IndexFamily A} (he : κ = κ') (x : A.Obj) (h : κ.I x = κ'.I x)
    (g : A.X.Isotropy x) (i : κ.I x) : cast h (g • i) = g • cast h i := by
  subst he; rfl

theorem commonFamily_cast_smul {F : Set A.Obj} (hF : A.X.IsEpFace F) {x : A.Obj} (hx : x ∈ F)
    (g : A.X.Isotropy x) (i : S.commonFamily.I x) :
    cast (S.commonFamily_eq hF hx) (g • i) = g • cast (S.commonFamily_eq hF hx) i := by
  obtain ⟨F₀, hF₀, hx₀, he⟩ := S.exists_pick hF hx
  have hE := (S.secEquiv F₀ hF₀ F hF).equiv
  obtain ⟨-, -, -, -, -, hI, -⟩ := id hE
  have h₁ : (S.pick x).I x = (S.ι F₀ hF₀).I x := by rw [he]
  have hs₁ : ∀ j : (S.pick x).I x, cast h₁ (g • j) = g • cast h₁ j :=
    cast_smul_of_eq he x h₁ g
  have h₂ : (S.ι F₀ hF₀).I x = (S.ι F hF).I x := hI ⟨x, hx₀, hx⟩
  have hs₂ : ∀ j : (S.ι F₀ hF₀).I x, cast h₂ (g • j) = g • cast h₂ j :=
    hE.cast_smul ⟨x, hx₀, hx⟩ h₂ g
  have e : S.commonFamily_eq hF hx = h₁.trans h₂ := rfl
  rw [e]
  calc cast (h₁.trans h₂) (g • i) = cast h₂ (cast h₁ (g • i)) := (cast_cast _ _ _).symm
    _ = cast h₂ (g • cast h₁ i) := congrArg (cast h₂) (hs₁ i)
    _ = g • cast h₂ (cast h₁ i) := hs₂ _
    _ = g • cast (h₁.trans h₂) i := congrArg (fun j => g • j) (cast_cast h₁ h₂ i)

/-- The relabelling of the common family to `I^F` (casts on `F`). -/
def relabelFun (F : Set A.Obj) (hF : A.X.IsEpFace F) (x : A.Obj)
    (i : S.commonFamily.I x) : (S.ι F hF).I x :=
  if hx : x ∈ F then cast (S.commonFamily_eq hF hx) i else Classical.arbitrary _

theorem relabelFun_of_mem {F : Set A.Obj} (hF : A.X.IsEpFace F) {x : A.Obj} (hx : x ∈ F) :
    S.relabelFun F hF x = cast (S.commonFamily_eq hF hx) :=
  funext fun _ => dif_pos hx

/-- The relabelling `I_x → I^F_x`, `x ∈ F`. -/
def relabel (F : Set A.Obj) (hF : A.X.IsEpFace F) : IndexRelabel F S.commonFamily (S.ι F hF) where
  f := S.relabelFun F hF
  bijective x := by
    rw [S.relabelFun_of_mem hF x.2]; exact (_root_.Equiv.cast _).bijective
  smul x g i := by
    rw [S.relabelFun_of_mem hF x.2]; exact S.commonFamily_cast_smul hF x.2 g i

theorem relabel_secEquiv (F : Set A.Obj) (hF : A.X.IsEpFace F) :
    ((S.T F hF).toRelTuple.reindex (S.relabel F hF)).SecEquiv (S.T F hF).toRelTuple :=
  RelTuple.reindex_secEquiv _ _ fun x =>
    ⟨S.commonFamily_eq hF x.2, fun i => congrFun (S.relabelFun_of_mem hF x.2) i⟩

/-- **The assignment on the common family**: the representatives relabelled to `I_x`. -/
def toData : SectionCompatibleFaceData A where
  ι := S.commonFamily
  T F hF := (S.T F hF).reindex (S.relabel F hF)
  secEquiv F hF F' hF' :=
    ((S.relabel_secEquiv F hF).restrictTo inter_subset_left).trans
      ((S.secEquiv F hF F' hF').trans
        ((S.relabel_secEquiv F' hF').restrictTo inter_subset_right).symm)

/-- The relabelled representatives are equivalent to the given ones, sections included. -/
theorem toData_secEquiv (F : Set A.Obj) (hF : A.X.IsEpFace F) :
    (S.toData.T F hF).toRelTuple.SecEquiv (S.T F hF).toRelTuple :=
  S.relabel_secEquiv F hF

variable (hX : A.X.IsEpFaceStructured)

/-- **2021 Theorem 14.6.3, p. 682 (2017: Theorem 14.4)**, the structure part, for representatives
with their own index families, compatible with the sections: over a face-structured
ep-groupoid with paracompact orbit space there is a structurable sc⁺-multisection `Λ` over `∂X`
with `Λ = Λ_F` over every face `F`. -/
theorem theorem_14_6_3 (hpara : A.X.HasParacompactOrbitSpace) :
    IsBoundaryStructurable A (S.toData.toCompatible hX).Λg ∧
      ∀ F (hF : A.X.IsEpFace F) w, A.P w ∈ F → (S.toData.toCompatible hX).Λg w = (S.T F hF).Λ w :=
  S.toData.theorem_14_6_3 hX hpara

/-- **2021 Theorem 14.6.3, p. 682 (2017: Theorem 14.4)**, the extension part, for representatives
with their own index families (Theorem 14.1.9 applied to the glued `Λ`). -/
theorem theorem_14_6_3_extension (hpara : A.X.HasParacompactOrbitSpace)
    (hpart : A.X.PObj.AdmitsScPartitionsOfUnity) (N : A.B.One → ℝ) (hN : A.E.IsAuxNorm N)
    (Ũ : Set A.Obj) (hŨ : IsOpen Ũ) (hŨs : A.X.IsSaturated Ũ)
    (hdom : boundaryDomSupp (S.toData.toCompatible hX).Λg ⊆ Ũ)
    (f : A.Obj → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hff : ∀ φ, f (A.X.tgt φ) = f (A.X.src φ)) (hfU : tsupport f ⊆ Ũ)
    (hfN : ∀ x ∈ boundaryDomSupp (S.toData.toCompatible hX).Λg,
      pointwiseNorm N (S.toData.toCompatible hX).Λg x < f x) :
    ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧ (∀ x, pointwiseNorm N Λ' x ≤ f x) ∧
      domSupp Λ' ⊆ Ũ ∧ ∀ F (hF : A.X.IsEpFace F) w, A.P w ∈ F → Λ' w = (S.T F hF).Λ w :=
  S.toData.theorem_14_6_3_extension hX hpara hpart N hN Ũ hŨ hŨs hdom f hf hf0 hff hfU hfN

end SectionCompatibleFaceFamilies

/-! ### Classes for the equivalence with sections -/

/-- Tuples over `K` (any index family) modulo the equivalence with sections. -/
instance RelTuple.secSetoid (A : SEP.{u}) (K : Set A.Obj) : Setoid (RelTuple.Sigma A K) where
  r T T' := T.2.SecEquiv T'.2
  iseqv := ⟨fun T => RelTuple.SecEquiv.refl T.2, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- **Structured multisections over `K`, the equivalence read with the sections.** -/
def RelSecStructured (A : SEP.{u}) (K : Set A.Obj) : Type (u + 1) :=
  Quotient (RelTuple.secSetoid A K)

/-- Face tuples over `F` (any index family) modulo the equivalence with sections. -/
instance FaceStructuredTuple.secSetoid (A : SEP.{u}) (F : Set A.Obj) :
    Setoid (Σ ι : IndexFamily A, FaceStructuredTuple A F ι) where
  r T T' := T.2.toRelTuple.SecEquiv T'.2.toRelTuple
  iseqv := ⟨fun T => RelTuple.SecEquiv.refl T.2.toRelTuple, fun h => h.symm,
    fun h₁ h₂ => h₁.trans h₂⟩

/-- **A structured sc⁺-multisection on `W|F`**, the equivalence read with the sections. -/
def FaceSecMultisection (A : SEP.{u}) (F : Set A.Obj) : Type (u + 1) :=
  Quotient (FaceStructuredTuple.secSetoid A F)

/-- **Definition 14.6.1 on these classes**: `Λ̃_F|F'`. -/
def FaceSecMultisection.restrictFace {F : Set A.Obj} (L : FaceSecMultisection A F)
    (F' : Set A.Obj) : RelSecStructured A (F ∩ F') :=
  Quotient.map (fun T => ⟨T.1, T.2.restrictFace F'⟩)
    (fun _ _ hT => RelTuple.SecEquiv.restrictTo hT inter_subset_left) L

/-- `Λ̃_{F'}|F` as a class over `F ∩ F'`. -/
def FaceSecMultisection.restrictFace' {F' : Set A.Obj} (L : FaceSecMultisection A F')
    (F : Set A.Obj) : RelSecStructured A (F ∩ F') :=
  Quotient.map (fun T => ⟨T.1, T.2.toRelTuple.restrictTo (F ∩ F') inter_subset_right⟩)
    (fun _ _ hT => RelTuple.SecEquiv.restrictTo hT inter_subset_right) L

/-- **Definition 14.6.2 on these classes**: `Λ̃_F|F' = Λ̃_{F'}|F` for all faces. -/
def IsSecCompatibleAssignment (Λt : ∀ F, A.X.IsEpFace F → FaceSecMultisection A F) : Prop :=
  ∀ F (hF : A.X.IsEpFace F) F' (hF' : A.X.IsEpFace F'),
    (Λt F hF).restrictFace F' = (Λt F' hF').restrictFace' F

namespace IsSecCompatibleAssignment

variable {Λt : ∀ F, A.X.IsEpFace F → FaceSecMultisection A F}

/-- The chosen representatives of a compatible assignment of classes, each with its own index
family. -/
def toFamilies (h : IsSecCompatibleAssignment Λt) : SectionCompatibleFaceFamilies A where
  ι F hF := (Quotient.out (Λt F hF)).1
  T F hF := (Quotient.out (Λt F hF)).2
  secEquiv F hF F' hF' := by
    have e := h F hF F' hF'
    rw [← Quotient.out_eq (Λt F hF), ← Quotient.out_eq (Λt F' hF')] at e
    exact Quotient.exact e

/-- **2021 Theorem 14.6.3, p. 682 (2017: Theorem 14.4), for a compatible assignment of classes**,
the equivalence read with the sections: over a face-structured ep-groupoid with paracompact orbit
space there is a structurable sc⁺-multisection `Λ` over `∂X` with `Λ = Λ_F` over every face
(for any representative of the class `Λ̃_F`: equivalent tuples have the same `Λ` over `F`). -/
theorem theorem_14_6_3 (h : IsSecCompatibleAssignment Λt) (hX : A.X.IsEpFaceStructured)
    (hpara : A.X.HasParacompactOrbitSpace) :
    ∃ Λ : A.W → ℚ≥0, IsBoundaryStructurable A Λ ∧ ∀ F (hF : A.X.IsEpFace F)
      (T : Σ ι : IndexFamily A, FaceStructuredTuple A F ι),
        Quotient.mk (FaceStructuredTuple.secSetoid A F) T = Λt F hF →
          ∀ w, A.P w ∈ F → Λ w = T.2.Λ w := by
  obtain ⟨hΛ, hF⟩ := h.toFamilies.theorem_14_6_3 hX hpara
  refine ⟨_, hΛ, fun F hF' T hT w hw => (hF F hF' w hw).trans ?_⟩
  have e : Quotient.out (Λt F hF') ≈ T := by
    rw [← hT]; exact Quotient.mk_out T
  exact e.1 w hw

end IsSecCompatibleAssignment

end SBLocalization

/-! ### A witness with different index families on the faces -/

namespace FaceCorner

open SBLocalization StrongBundle EpGroupoid MPolyfold TameBoundaryExample QuadrantBundle

/-- The trivial action on a set of signs. -/
@[instance_reducible]
def subAction (G : Type) [Monoid G] (p : Bool → Prop) : MulAction G {b : Bool // p b} where
  smul _ b := b
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- `I^F_x = {b : Bool // x ∈ F ∨ b}`: the two signs on `F`, one element off `F`. -/
def faceFamily (F : Set A.Obj) : IndexFamily A where
  I x := {b : Bool // x ∈ F ∨ b = true}
  fintype _ := inferInstance
  mulAction _ := subAction _ _
  nonempty _ := ⟨⟨true, Or.inr rfl⟩⟩

/-- The relabelling `I^F_x → {±}`, `b ↦ b`. -/
def faceRelabel (F : Set A.Obj) : IndexRelabel F (faceFamily F) ι where
  f _ i := i.1
  bijective x := ⟨Subtype.val_injective, fun b => ⟨⟨b, Or.inl x.2⟩, rfl⟩⟩
  smul _ _ _ := rfl

theorem val_cast_subtype {α : Type} {p q : α → Prop} (h : Subtype p = Subtype q) (hpq : p = q)
    (i : Subtype p) : (cast h i).1 = i.1 := by
  subst hpq; rfl

theorem faceFamily_eq {F F' : Set A.Obj} (x : ↥(F ∩ F')) :
    (faceFamily F).I x = (faceFamily F').I x :=
  congrArg Subtype (funext fun _ => propext ⟨fun _ => Or.inl x.2.2, fun _ => Or.inl x.2.1⟩)

/-- **Representatives with different index families on the faces**: the corner tuples of
`cornerFaceData`, relabelled to `I^F_x = {b // x ∈ F ∨ b}`. -/
def familiesWitness : SectionCompatibleFaceFamilies A where
  ι F _ := faceFamily F
  T F hF := (cornerSectionCompatible.T F hF).reindex (faceRelabel F)
  secEquiv F hF F' hF' := by
    have h1 := RelTuple.reindex_restrictTo_secEquiv (cornerSectionCompatible.T F hF).toRelTuple
      (faceRelabel F) (inter_subset_left (s := F) (t := F'))
    have h3 := RelTuple.reindex_restrictTo_secEquiv (cornerSectionCompatible.T F' hF').toRelTuple
      (faceRelabel F') (inter_subset_right (s := F) (t := F'))
    have h2 := (cornerSectionCompatible.secEquiv F hF F' hF').reindex
      ((faceRelabel F).restrict inter_subset_left) ((faceRelabel F').restrict inter_subset_right)
      faceFamily_eq fun x h i => by
        rw [cast_eq]
        exact val_cast_subtype _
          (funext fun _ => propext ⟨fun _ => Or.inl x.2.2, fun _ => Or.inl x.2.1⟩) i
    exact h1.trans (h2.trans h3.symm)

theorem card_faceFamily_of_mem {F : Set A.Obj} {x : A.Obj} (hx : x ∈ F) :
    Fintype.card ((faceFamily F).I x) = 2 :=
  (Fintype.card_congr (_root_.Equiv.subtypeUnivEquiv fun _ => Or.inl hx)).trans Fintype.card_bool

theorem card_faceFamily_of_not_mem {F : Set A.Obj} {x : A.Obj} (hx : x ∉ F) :
    Fintype.card ((faceFamily F).I x) = 1 :=
  Fintype.card_eq_one_iff.2 ⟨⟨true, Or.inr rfl⟩, fun b => Subtype.ext (b.2.resolve_left hx)⟩

/-- **The families of `familiesWitness` differ**: at `(1, 0, 0)` a face in `{x₁ = 0}` has one
index and a face through the point has two. -/
theorem card_familiesWitness_ne : ∃ (F₁ : Set A.Obj) (hF₁ : A.X.IsEpFace F₁) (F₂ : Set A.Obj)
    (hF₂ : A.X.IsEpFace F₂) (x : A.Obj),
      Fintype.card ((familiesWitness.ι F₁ hF₁).I x) = 1 ∧
        Fintype.card ((familiesWitness.ι F₂ hF₂).I x) = 2 := by
  have hu : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨F₁, hF₁, -, hF₁Z⟩ := exists_isEpFace_mem_of_part (k := 2) (path₁_mem_part one_pos hu)
  obtain ⟨F₂, hF₂, hx₂, -⟩ := exists_isEpFace_mem_of_part (k := 2) (path₂_mem_part one_pos hu)
  refine ⟨F₁, hF₁, F₂, hF₂, path₂ 1 0, card_faceFamily_of_not_mem fun h => ?_,
    card_faceFamily_of_mem hx₂⟩
  have h0 : max ((1 : ℝ) * (1 - 0 ^ 2)) 0 = 0 := hF₁Z h
  norm_num at h0

/-- **Theorem 14.6.3 with different index families, at a corner with non-zero sections**: the
families of `familiesWitness` differ (`card_familiesWitness_ne`), and the glued functor is
structurable over `∂X`, equal to `Λ_F` over every face, and charges a non-zero point over the
corner point `(0, 0, 1)` (`d = 2`). -/
theorem theorem_14_6_3_families_witness :
    let Λ := (familiesWitness.toData.toCompatible isEpFaceStructured_A).Λg
    IsBoundaryStructurable A Λ ∧
      (∀ F (_ : A.X.IsEpFace F) w, A.P w ∈ F → Λ w = signMulti (germMapEq F) w) ∧
      ∃ y : A.Obj, A.X.PObj.degIndex y = 2 ∧ ∃ w, A.P w = y ∧ w ≠ fiberZero A.P y ∧ 0 < Λ w := by
  intro Λ
  obtain ⟨hΛ, hF⟩ := familiesWitness.theorem_14_6_3 isEpFaceStructured_A
    (hasParacompactOrbitSpace_quadSEP 2 1 2)
  refine ⟨hΛ, fun F hF' w hw => hF F hF' w hw, pt 0 0 1, ?_, ?_⟩
  · change dq 2 (rnSc 1) (pt 0 0 1) = 2
    rw [dq_eq, Finset.filter_true_of_mem fun i _ => by fin_cases i <;> exact max_self 0]
    rfl
  · have hb : (show A.Obj from pt 0 0 1) ∈ A.X.PObj.boundary :=
      mem_boundary_of_coord (i := 0) (max_self 0)
    obtain ⟨F, hFace, hyF⟩ := exists_isEpFace_mem isEpFaceStructured_A hb
    refine ⟨sec (germMapEq F) true (pt 0 0 1), rfl, fun h => ?_, ?_⟩
    · have h2 : sgn true • germMapEq F (pt 0 0 1 : E₀) = 0 := congrArg Prod.snd h
      have h3 : germMapEq F (pt 0 0 1 : E₀) 0 = 0 := by
        have := congrFun h2 0
        simpa [sgn] using this
      have h4 : germMapEq F (pt 0 0 1 : E₀) 0 = hfun 1 := by
        unfold germMapEq; split_ifs <;> rfl
      exact hfun_ne_zero one_ne_zero (h4.symm.trans h3)
    · change 0 < (familiesWitness.toData.toCompatible isEpFaceStructured_A).Λg _
      rw [hF F hFace _ (show A.P (sec (germMapEq F) true (pt 0 0 1)) ∈ F from hyF)]
      exact signMulti_sec_pos _ _ _

end FaceCorner

end Polyfold
