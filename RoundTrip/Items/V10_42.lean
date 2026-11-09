import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_42

/-! Round trip for V10_42 (2021 Theorem 10.3.10, p. 489; 2017: Theorem 10.4, p. 353; proof in
Appendix §10.6.2: the generalized isomorphisms).

The item lists the definitions `Diagram.symm`, `diagFunctor` (vocabulary) and fifteen theorems.
`A` is the conjunction of their types, universes at `0`: `EPLoc.theorem_10_3_10` ((1)
`[d]` is a generalized isomorphism iff `Φ` is an equivalence; (2) then every two-sided inverse
of `[d]` is `[d.symm hΦ] = [Y ←Φ A →F X]`), the proof steps `isEquivalence_diagFunctor`,
`isRefinement_comp_symm`, `isRefinement_id`, `equiv_comp_symm`, `equiv_symm_comp`,
`isEquivalence_Φ_of_equiv_id`, the claims (C1) `isEquivalence_toFunctor_of_comp` and (C2)
`isLocalScDiffeo_obj_of_comp`, `isEquivalence_Φ_of_equiv`, the `IsIso` forms `isIso_homMk_iff`,
`isIso_homMk`, `inv_homMk`, and two general M-polyfold lemmas `isLocalScDiffeoAt_of_injOn`,
`IsLocalScDiffeoAt.exists_injOn`.

`B` (at universe `0`): `IsGenIsoB d ↔ d.Φ.IsEquivalence` (a two-sided inverse up to `EquivB`,
definitionally `Diagram.Equiv`, with `Diagram.comp` and `Diagram.id`), and for `Φ` an equivalence
the reversed diagram `revB d hΦ` (definitionally `d.symm hΦ`) is a two-sided inverse.

* Glue `isGenIso_iff`: `EPLoc.IsGeneralizedIso (homMk d) ↔ IsGenIsoB d` (`homMk d ≫ homMk e` is
  definitionally `homMk (d.comp e)`, `𝟙 (of X)` is `homMk (id X)`, and `Quotient.eq`).
* `A ⇒ B`: from `theorem_10_3_10` alone: (1) through the glue; for the inverse, (1) gives some
  two-sided inverse `g` of `[d]`, (2) says `g = [d.symm hΦ]`, and `Quotient.eq` turns the two
  equations into `EquivB`.
* `B ⇒ A`: `theorem_10_3_10` ((1) through the glue; (2) by uniqueness of two-sided inverses in a
  category, with `B`'s inverse `[revB d hΦ]`), `equiv_comp_symm`, `equiv_symm_comp`,
  `isEquivalence_Φ_of_equiv`, `isIso_homMk_iff`, `isIso_homMk`, `inv_homMk` come from `B`;
  `isEquivalence_Φ_of_equiv_id` also comes from `B` (if `d ~ 1_X` then `[1_X]` is a two-sided
  inverse of `[d]`, by the unit laws `isRefinement_comp_id`, `isRefinement_id_comp` and
  transitivity, non-item lemmas).  The remaining six conjuncts (`isEquivalence_diagFunctor`,
  `isRefinement_comp_symm`, `isRefinement_id`, (C1), (C2) and the two M-polyfold lemmas) are
  statements about refinements, general functors between weak fibred products, or M-polyfolds,
  which `B` does not give; they are re-proved outright (the project's proofs, own copies, from
  non-item lemmas).

**Harness note.**  The statement of `inv_homMk` contains the banned theorem `isIso_homMk` (as the
`IsIso` instance of `inv`, from its `haveI`), so every term mentioning `A` reaches it.  As in
V8_4, both directions are proved through `A'`, which is `A` with that instance replaced by our
own proof `isIso_homMk'` (from outright copies); `A = A'` is `rfl` (proof irrelevance), and
`A_to_B := A'_to_B`, `B_to_A := B_to_A'` are stated point-free, so that plain `#rt_check`
passes on all four.
-/

namespace RoundTrip.V10_42
open Set Function CategoryTheory Polyfold Polyfold.EPLocalization WeakFibredProduct

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.EPLoc.theorem_10_3_10.{0}) ∧
  (type_of% @Polyfold.EPLocalization.isEquivalence_diagFunctor.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isRefinement_comp_symm.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isRefinement_id.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.equiv_comp_symm.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.equiv_symm_comp.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isEquivalence_Φ_of_equiv_id.{0}) ∧
  (type_of% @Polyfold.EPLocalization.isEquivalence_toFunctor_of_comp.{0}) ∧
  (type_of% @Polyfold.EPLocalization.isLocalScDiffeo_obj_of_comp.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isEquivalence_Φ_of_equiv.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.isIso_homMk_iff.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.isIso_homMk.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.inv_homMk.{0}) ∧
  (type_of% @Polyfold.MPolyfold.isLocalScDiffeoAt_of_injOn.{0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.IsLocalScDiffeoAt.exists_injOn.{0, 0})

theorem A_holds : A :=
  ⟨@EPLoc.theorem_10_3_10.{0}, @isEquivalence_diagFunctor.{0},
    @Diagram.isRefinement_comp_symm.{0}, @Diagram.isRefinement_id.{0},
    @Diagram.equiv_comp_symm.{0}, @Diagram.equiv_symm_comp.{0},
    @Diagram.isEquivalence_Φ_of_equiv_id.{0}, @isEquivalence_toFunctor_of_comp.{0},
    @isLocalScDiffeo_obj_of_comp.{0}, @Diagram.isEquivalence_Φ_of_equiv.{0},
    @EPLoc.isIso_homMk_iff.{0}, @EPLoc.isIso_homMk.{0}, @EPLoc.inv_homMk.{0},
    @MPolyfold.isLocalScDiffeoAt_of_injOn.{0, 0}, @MPolyfold.IsLocalScDiffeoAt.exists_injOn.{0, 0}⟩

/-! ### Outright copies of the side conjuncts (the project's proofs) -/

section Copies

universe u v

namespace MPolyfold'

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ParacompactSpace M] {P : MPolyfold M}
  {N : Type v} [TopologicalSpace N] [T2Space N] [ParacompactSpace N] {Q : MPolyfold N}

/-- Copy of `MPolyfold.isLocalScDiffeoAt_of_injOn`. -/
theorem isLocalScDiffeoAt_of_injOn' {f : M → N} {x : M} (hf : P.IsScSmoothMap Q f) {U : Set M}
    (hU : IsOpen U) (hxU : x ∈ U) (hinj : InjOn f U) {V : Set N} {r : N → M}
    (hr : Q.IsScSmoothOn P r V) (hxV : f x ∈ V) (hfr : ∀ y ∈ V, f (r y) = y)
    (hrx : r (f x) = x) : P.IsLocalScDiffeoAt Q f x := by
  have hfc : Continuous f := continuousOn_univ.1 hf.continuousOn
  have hV' : IsOpen (V ∩ r ⁻¹' U) := hr.continuousOn.isOpen_inter_preimage hr.isOpen hU
  set W := U ∩ f ⁻¹' (V ∩ r ⁻¹' U) with hWdef
  have hW : IsOpen W := hU.inter (hV'.preimage hfc)
  have hrf : ∀ w ∈ W, r (f w) = w := fun w hw => hinj hw.2.2 hw.1 (hfr _ hw.2.1)
  have hW' : IsOpen (V ∩ r ⁻¹' W) := hr.continuousOn.isOpen_inter_preimage hr.isOpen hW
  have hxW : x ∈ W := ⟨hxU, hxV, by rw [mem_preimage, hrx]; exact hxU⟩
  exact ⟨W, V ∩ r ⁻¹' W, r, hxW,
    { isScSmoothOn := hf.mono hW (subset_univ _)
      isScSmoothOn_inv := hr.mono hW' inter_subset_left
      mapsTo := fun w hw => ⟨hw.2.1, by rw [mem_preimage, hrf w hw]; exact hw⟩
      mapsTo_inv := fun _ hy => hy.2
      left_inv := hrf
      right_inv := fun y hy => hfr y hy.1 }⟩

/-- Copy of `MPolyfold.IsLocalScDiffeoAt.exists_injOn`. -/
theorem exists_injOn' {f : M → N} {x : M} (h : P.IsLocalScDiffeoAt Q f x) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ InjOn f U := by
  obtain ⟨U, V, g, hx, hd⟩ := h
  exact ⟨U, hd.isScSmoothOn.isOpen, hx, fun a ha b hb hab => by
    rw [← hd.left_inv a ha, hab, hd.left_inv b hb]⟩

end MPolyfold'

section Diagonal

variable {A Y : EP.{u}} (G : EpFunctor A.X Y.X)

/-- Copy of `isEquivalence_diagFunctor`. -/
theorem isEquivalence_diagFunctor' (hG : G.IsEquivalence) (h : Admissible G G) :
    (diagFunctor G h).IsEquivalence :=
  EpFunctor.IsEquivalence.of_comp_left (isEquivalence_projLeft hG h)
    (EpFunctor.IsEquivalence.id A.X)

end Diagonal

variable {X Y Z : EP.{u}}

/-- Copy of `Diagram.isRefinement_comp_symm`. -/
theorem isRefinement_comp_symm' (A : EP.{u}) (F : EpFunctor A.X X.X) (hF : F.IsEquivalence)
    (G : EpFunctor A.X Y.X) (hG : G.IsEquivalence) (Ψ : EpFunctor A.X Z.X) :
    (⟨A, F, hF, Ψ⟩ : Diagram X Z).IsRefinement
      ((⟨A, F, hF, G⟩ : Diagram X Y).comp ⟨A, G, hG, Ψ⟩) :=
  ⟨diagFunctor G (.of_isEquivalence_right hG), isEquivalence_diagFunctor' G hG _, .refl _,
    .refl _⟩

/-- Copy of `Diagram.isRefinement_id`. -/
theorem isRefinement_id' (A : EP.{u}) (F : EpFunctor A.X X.X) (hF : F.IsEquivalence) :
    (⟨A, F, hF, F⟩ : Diagram X X).IsRefinement (Diagram.id X) :=
  ⟨F, hF, .refl _, .refl _⟩

/-- Copy of `Diagram.equiv_comp_symm` (used only for the instance in `A'`). -/
theorem equiv_comp_symm' (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) :
    Diagram.Equiv (d.comp (d.symm hΦ)) (Diagram.id X) :=
  ⟨⟨d.A, d.F, d.isEquivalence_F, d.F⟩,
    isRefinement_comp_symm' d.A d.F d.isEquivalence_F d.Φ hΦ d.F,
    isRefinement_id' d.A d.F d.isEquivalence_F⟩

/-- Copy of `Diagram.equiv_symm_comp` (used only for the instance in `A'`). -/
theorem equiv_symm_comp' (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) :
    Diagram.Equiv ((d.symm hΦ).comp d) (Diagram.id Y) :=
  ⟨⟨d.A, d.Φ, hΦ, d.Φ⟩, isRefinement_comp_symm' d.A d.Φ hΦ d.F d.isEquivalence_F d.Φ,
    isRefinement_id' d.A d.Φ hΦ⟩

/-- Our own proof that `[d]` is an isomorphism when `Φ` is an equivalence (for `A'`). -/
theorem isIso_homMk' (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) : IsIso (EPLoc.homMk d) :=
  ⟨⟨EPLoc.homMk (d.symm hΦ), Quotient.sound (equiv_comp_symm' d hΦ),
    Quotient.sound (equiv_symm_comp' d hΦ)⟩⟩

section Inverse

variable {A B : EP.{u}} {F : EpFunctor A.X X.X} {Φ : EpFunctor A.X Y.X}
  {G : EpFunctor B.X Y.X} {Ψ : EpFunctor B.X X.X}

/-- Copy of `isEquivalence_toFunctor_of_comp` (claim (C1)). -/
theorem isEquivalence_toFunctor_of_comp' (hG : G.IsEquivalence) (h : Admissible Φ G)
    (h' : Admissible Ψ F) (hP : (Ψ.comp (projRight Φ G h)).IsEquivalence)
    (hQ : (Φ.comp (projRight Ψ F h')).IsEquivalence) : Φ.toFunctor.IsEquivalence where
  faithful := (GroupoidFunctor.faithful_iff _).2 fun h₁ h₂ hs ht he => by
    obtain ⟨b, φ₀, hs₀, ht₀⟩ := hG.exists_iso (Φ.obj (A.X.src h₁))
    have e₁ : Y.X.src (Y.X.inv φ₀) = Φ.obj (A.X.src h₁) := by rw [Y.X.src_inv, ht₀]
    have e₂ : Y.X.tgt (Y.X.inv φ₀) = G.obj (B.X.src (B.X.unit b)) := by
      rw [Y.X.tgt_inv, B.X.src_unit, hs₀]
    have hm : Mor.mk Φ G h₁ (Y.X.inv φ₀) (B.X.unit b) e₁ e₂ =
        Mor.mk Φ G h₂ (Y.X.inv φ₀) (B.X.unit b) (e₁.trans (congrArg Φ.obj hs)) e₂ :=
      hP.mor_injective (Obj.ext hs rfl rfl)
        (Obj.ext ht (by
          change conj Φ G h₁ _ _ = conj Φ G h₂ _ _
          simp only [conj]
          rw [he]
          rfl) rfl) rfl
    exact congrArg Mor.h hm
  full := (GroupoidFunctor.full_iff _).2 fun a a' ψ hs ht => by
    obtain ⟨p, φ, hsφ, htφ⟩ := hP.exists_iso (F.obj a)
    obtain ⟨p', φ', hsφ', htφ'⟩ := hP.exists_iso (F.obj a')
    obtain ⟨m, hm₁, hm₂, hm₃⟩ := hQ.exists_mor_eq (x := Obj.mk Ψ F p.z φ a hsφ htφ)
      (x' := Obj.mk Ψ F p'.z φ' a' hsφ' htφ') hs ht
    exact ⟨m.k, congrArg Obj.z hm₁, congrArg Obj.z hm₂, hm₃⟩
  essSurj := (GroupoidFunctor.essSurj_iff _).2 fun y => by
    obtain ⟨q, ψ, hs, ht⟩ := hQ.exists_iso y
    exact ⟨q.z, ψ, hs, ht⟩

/-- Copy of `isLocalScDiffeo_obj_of_comp` (claim (C2)). -/
theorem isLocalScDiffeo_obj_of_comp' (hG : G.IsEquivalence) (h : Admissible Φ G)
    (h' : Admissible Ψ F) (hP : (Ψ.comp (projRight Φ G h)).IsEquivalence)
    (hQ : (Φ.comp (projRight Ψ F h')).IsEquivalence) :
    A.X.PObj.IsLocalScDiffeo Y.X.PObj Φ.obj := fun a => by
  obtain ⟨p, ψ, hs, ht⟩ := hP.exists_iso (F.obj a)
  obtain ⟨U₀, V, κ, hqU₀, hd⟩ := hQ.isLocalScDiffeo_obj (Obj.mk Ψ F p.z ψ a hs ht)
  have hr : Y.X.PObj.IsScSmoothOn A.X.PObj (Obj.z ∘ κ) V :=
    MPolyfold.IsScSmoothOn.comp (isScSmoothMap_z h') hd.isScSmoothOn_inv (mapsTo_univ _ _)
  have hrx : (Obj.z ∘ κ) (Φ.obj a) = a := by
    change (κ ((Φ.comp (projRight Ψ F h')).obj (Obj.mk Ψ F p.z ψ a hs ht))).z = a
    rw [hd.left_inv _ hqU₀]
    rfl
  obtain ⟨b, φ₀, hs₀, ht₀⟩ := hG.exists_iso (Φ.obj a)
  let p₀ : WeakFibredProduct.Obj Φ G := Obj.mk Φ G a (Y.X.inv φ₀) b
    (by rw [Y.X.src_inv, ht₀]) (by rw [Y.X.tgt_inv, hs₀])
  obtain ⟨V₀, W₀, σ, hp₀, hσ⟩ := isLocalScDiffeo_x h hG.isLocalScDiffeo_obj p₀
  obtain ⟨U₁, hU₁, hp₁, hinj₁⟩ := MPolyfold'.exists_injOn' (hP.isLocalScDiffeo_obj.at p₀)
  obtain ⟨U₂, hU₂, hp₂, hinj₂⟩ := MPolyfold'.exists_injOn' (Y.X.isLocalScDiffeo_src.at p₀.φ)
  obtain ⟨U₃, hU₃, hp₃, hinj₃⟩ := MPolyfold'.exists_injOn' (hG.isLocalScDiffeo_obj.at b)
  have hσa : σ a = p₀ := hσ.left_inv p₀ hp₀
  have hU : IsOpen (W₀ ∩ σ ⁻¹' (U₁ ∩ Obj.φ ⁻¹' U₂ ∩ Obj.z ⁻¹' U₃)) :=
    hσ.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hσ.isOpen_target
      ((hU₁.inter (hU₂.preimage continuous_φ)).inter (hU₃.preimage continuous_z))
  have haU : a ∈ W₀ ∩ σ ⁻¹' (U₁ ∩ Obj.φ ⁻¹' U₂ ∩ Obj.z ⁻¹' U₃) :=
    ⟨hσ.mapsTo hp₀, by rw [mem_preimage, hσa]; exact ⟨⟨hp₁, hp₂⟩, hp₃⟩⟩
  have hinj : InjOn Φ.obj (W₀ ∩ σ ⁻¹' (U₁ ∩ Obj.φ ⁻¹' U₂ ∩ Obj.z ⁻¹' U₃)) := by
    intro a₁ ha₁ a₂ ha₂ he
    have hx₁ : (σ a₁).x = a₁ := hσ.right_inv a₁ ha₁.1
    have hx₂ : (σ a₂).x = a₂ := hσ.right_inv a₂ ha₂.1
    have hφ : (σ a₁).φ = (σ a₂).φ :=
      hinj₂ ha₁.2.1.2 ha₂.2.1.2 (by rw [Obj.src_φ, Obj.src_φ, hx₁, hx₂, he])
    have hz : (σ a₁).z = (σ a₂).z := hinj₃ ha₁.2.2 ha₂.2.2
      ((Obj.tgt_φ (σ a₁)).symm.trans ((congrArg Y.X.tgt hφ).trans (Obj.tgt_φ (σ a₂))))
    have hp : σ a₁ = σ a₂ := hinj₁ ha₁.2.1.1 ha₂.2.1.1 (congrArg Ψ.obj hz)
    rw [← hx₁, ← hx₂, hp]
  exact MPolyfold'.isLocalScDiffeoAt_of_injOn' Φ.isScSmoothMap_obj hU haU hinj hr
    (hd.mapsTo hqU₀) (fun y hy => hd.right_inv y hy) hrx

end Inverse

end Copies

/-- `A` with the `IsIso` instance of `inv_homMk`'s statement given by our own proof
`isIso_homMk'` instead of the banned `isIso_homMk`. -/
def A' : Prop :=
  (type_of% @Polyfold.EPLocalization.EPLoc.theorem_10_3_10.{0}) ∧
  (type_of% @Polyfold.EPLocalization.isEquivalence_diagFunctor.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isRefinement_comp_symm.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isRefinement_id.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.equiv_comp_symm.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.equiv_symm_comp.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isEquivalence_Φ_of_equiv_id.{0}) ∧
  (type_of% @Polyfold.EPLocalization.isEquivalence_toFunctor_of_comp.{0}) ∧
  (type_of% @Polyfold.EPLocalization.isLocalScDiffeo_obj_of_comp.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isEquivalence_Φ_of_equiv.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.isIso_homMk_iff.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.isIso_homMk.{0}) ∧
  (∀ {X Y : EP.{0}} (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence),
    haveI := isIso_homMk' d hΦ
    inv (EPLoc.homMk d) = EPLoc.homMk (d.symm hΦ)) ∧
  (type_of% @Polyfold.MPolyfold.isLocalScDiffeoAt_of_injOn.{0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.IsLocalScDiffeoAt.exists_injOn.{0, 0})

/-- `A` and `A'` are the same proposition (proof irrelevance). -/
theorem A_eq_A' : A = A' := rfl

/-! ### Glue -/

/-- The project's generalized isomorphisms of classes are B's two-sided inverses. -/
theorem isGenIso_iff {X Y : EP.{0}} (d : Diagram X Y) :
    EPLoc.IsGeneralizedIso (EPLoc.homMk d) ↔ IsGenIsoB d := by
  constructor
  · rintro ⟨g, h₁, h₂⟩
    obtain ⟨e, rfl⟩ := Quotient.exists_rep g
    exact ⟨e, Quotient.eq.1 h₁, Quotient.eq.1 h₂⟩
  · rintro ⟨e, h₁, h₂⟩
    exact ⟨Quotient.mk (Diagram.setoid Y X) e, Quotient.sound h₁, Quotient.sound h₂⟩

/-! ### The two directions -/

theorem A'_to_B : A' → B.{0} := by
  rintro ⟨h, -⟩ X Y d
  refine ⟨(isGenIso_iff d).symm.trans (h d).1, fun hΦ => ?_⟩
  obtain ⟨g, hg₁, hg₂⟩ := (h d).1.2 hΦ
  have hg : g = EPLoc.homMk (d.symm hΦ) := (h d).2 hΦ g hg₁ hg₂
  subst hg
  exact ⟨Quotient.eq.1 hg₁, Quotient.eq.1 hg₂⟩

theorem B_to_A' : B.{0} → A' := by
  intro hB
  -- the facts read off `B`
  have hiso : ∀ {X Y : EP.{0}} (d : Diagram X Y),
      EPLoc.IsGeneralizedIso (EPLoc.homMk d) ↔ d.Φ.IsEquivalence := fun {X Y} d =>
    (isGenIso_iff d).trans (hB X Y d).1
  have hinv₁ : ∀ {X Y : EP.{0}} (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence),
      EPLoc.homMk d ≫ EPLoc.homMk (d.symm hΦ) = 𝟙 _ := fun {X Y} d hΦ =>
    Quotient.sound ((hB X Y d).2 hΦ).1
  have hinv₂ : ∀ {X Y : EP.{0}} (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence),
      EPLoc.homMk (d.symm hΦ) ≫ EPLoc.homMk d = 𝟙 _ := fun {X Y} d hΦ =>
    Quotient.sound ((hB X Y d).2 hΦ).2
  have hisoIso : ∀ {X Y : EP.{0}} (d : Diagram X Y),
      IsIso (EPLoc.homMk d) ↔ d.Φ.IsEquivalence := fun d =>
    ⟨fun h => (hiso d).1 h.out, fun h => ⟨(hiso d).2 h⟩⟩
  refine ⟨?_, @isEquivalence_diagFunctor'.{0}, @isRefinement_comp_symm'.{0}, @isRefinement_id'.{0},
    ?_, ?_, ?_, @isEquivalence_toFunctor_of_comp'.{0}, @isLocalScDiffeo_obj_of_comp'.{0}, ?_,
    fun {X Y} d => hisoIso d, fun {X Y} d hΦ => (hisoIso d).2 hΦ, ?_,
    @MPolyfold'.isLocalScDiffeoAt_of_injOn'.{0, 0}, @MPolyfold'.exists_injOn'.{0, 0}⟩
  · -- `theorem_10_3_10`: (1) from `B`; (2) uniqueness of two-sided inverses
    intro X Y d
    refine ⟨hiso d, fun hΦ g hg₁ hg₂ => ?_⟩
    calc g = g ≫ EPLoc.homMk d ≫ EPLoc.homMk (d.symm hΦ) := by
            rw [hinv₁ d hΦ, Category.comp_id]
      _ = EPLoc.homMk (d.symm hΦ) := by rw [← Category.assoc, hg₂, Category.id_comp]
  · -- `equiv_comp_symm`: `B`
    intro X Y d hΦ
    exact ((hB X Y d).2 hΦ).1
  · -- `equiv_symm_comp`: `B`
    intro X Y d hΦ
    exact ((hB X Y d).2 hΦ).2
  · -- `isEquivalence_Φ_of_equiv_id`: `[1_X]` is a two-sided inverse of `[d] = [1_X]`
    intro X d h
    refine (hB X X d).1.1 ⟨Diagram.id X, ?_, ?_⟩
    · exact (Diagram.isRefinement_comp_id d).equiv.trans h
    · exact (Diagram.isRefinement_id_comp d).equiv.trans h
  · -- `isEquivalence_Φ_of_equiv`: `B`
    intro X Y a b hab hba
    exact (hB X Y a).1.1 ⟨b, hab, hba⟩
  · -- `inv_homMk` (with our instance): `B`
    intro X Y d hΦ
    have := isIso_homMk' d hΦ
    exact IsIso.inv_eq_of_hom_inv_id (hinv₁ d hΦ)

theorem A_to_B : A → B.{0} := A'_to_B

theorem B_to_A : B.{0} → A := B_to_A'

#rt_check RoundTrip.V10_42.A_to_B [Polyfold.EPLocalization.EPLoc.theorem_10_3_10,
  Polyfold.EPLocalization.isEquivalence_diagFunctor,
  Polyfold.EPLocalization.Diagram.isRefinement_comp_symm,
  Polyfold.EPLocalization.Diagram.isRefinement_id, Polyfold.EPLocalization.Diagram.equiv_comp_symm,
  Polyfold.EPLocalization.Diagram.equiv_symm_comp,
  Polyfold.EPLocalization.Diagram.isEquivalence_Φ_of_equiv_id,
  Polyfold.EPLocalization.isEquivalence_toFunctor_of_comp,
  Polyfold.EPLocalization.isLocalScDiffeo_obj_of_comp,
  Polyfold.EPLocalization.Diagram.isEquivalence_Φ_of_equiv,
  Polyfold.EPLocalization.EPLoc.isIso_homMk_iff, Polyfold.EPLocalization.EPLoc.isIso_homMk,
  Polyfold.EPLocalization.EPLoc.inv_homMk, Polyfold.MPolyfold.isLocalScDiffeoAt_of_injOn,
  Polyfold.MPolyfold.IsLocalScDiffeoAt.exists_injOn]
#rt_check RoundTrip.V10_42.B_to_A [Polyfold.EPLocalization.EPLoc.theorem_10_3_10,
  Polyfold.EPLocalization.isEquivalence_diagFunctor,
  Polyfold.EPLocalization.Diagram.isRefinement_comp_symm,
  Polyfold.EPLocalization.Diagram.isRefinement_id, Polyfold.EPLocalization.Diagram.equiv_comp_symm,
  Polyfold.EPLocalization.Diagram.equiv_symm_comp,
  Polyfold.EPLocalization.Diagram.isEquivalence_Φ_of_equiv_id,
  Polyfold.EPLocalization.isEquivalence_toFunctor_of_comp,
  Polyfold.EPLocalization.isLocalScDiffeo_obj_of_comp,
  Polyfold.EPLocalization.Diagram.isEquivalence_Φ_of_equiv,
  Polyfold.EPLocalization.EPLoc.isIso_homMk_iff, Polyfold.EPLocalization.EPLoc.isIso_homMk,
  Polyfold.EPLocalization.EPLoc.inv_homMk, Polyfold.MPolyfold.isLocalScDiffeoAt_of_injOn,
  Polyfold.MPolyfold.IsLocalScDiffeoAt.exists_injOn]
/-- The same proof stated pointwise: the binder `h : A` brings in `A`'s statement, hence the
banned `isIso_homMk` (the instance in `inv_homMk`'s statement) and, through the project's proof
of `isIso_homMk`, every other banned theorem except `inv_homMk` itself. -/
theorem A_to_B_pointwise : A → B.{0} := fun h => A'_to_B h

/--
error: rt_check FAIL: RoundTrip.V10_42.A_to_B_pointwise uses [Polyfold.EPLocalization.EPLoc.theorem_10_3_10,
 Polyfold.EPLocalization.isEquivalence_diagFunctor,
 Polyfold.EPLocalization.Diagram.isRefinement_comp_symm,
 Polyfold.EPLocalization.Diagram.isRefinement_id,
 Polyfold.EPLocalization.Diagram.equiv_comp_symm,
 Polyfold.EPLocalization.Diagram.equiv_symm_comp,
 Polyfold.EPLocalization.Diagram.isEquivalence_Φ_of_equiv_id,
 Polyfold.EPLocalization.isEquivalence_toFunctor_of_comp,
 Polyfold.EPLocalization.isLocalScDiffeo_obj_of_comp,
 Polyfold.EPLocalization.Diagram.isEquivalence_Φ_of_equiv,
 Polyfold.EPLocalization.EPLoc.isIso_homMk_iff,
 Polyfold.EPLocalization.EPLoc.isIso_homMk,
 Polyfold.MPolyfold.isLocalScDiffeoAt_of_injOn,
 Polyfold.MPolyfold.IsLocalScDiffeoAt.exists_injOn]
-/
#guard_msgs in
#rt_check RoundTrip.V10_42.A_to_B_pointwise [Polyfold.EPLocalization.EPLoc.theorem_10_3_10,
  Polyfold.EPLocalization.isEquivalence_diagFunctor,
  Polyfold.EPLocalization.Diagram.isRefinement_comp_symm,
  Polyfold.EPLocalization.Diagram.isRefinement_id, Polyfold.EPLocalization.Diagram.equiv_comp_symm,
  Polyfold.EPLocalization.Diagram.equiv_symm_comp,
  Polyfold.EPLocalization.Diagram.isEquivalence_Φ_of_equiv_id,
  Polyfold.EPLocalization.isEquivalence_toFunctor_of_comp,
  Polyfold.EPLocalization.isLocalScDiffeo_obj_of_comp,
  Polyfold.EPLocalization.Diagram.isEquivalence_Φ_of_equiv,
  Polyfold.EPLocalization.EPLoc.isIso_homMk_iff, Polyfold.EPLocalization.EPLoc.isIso_homMk,
  Polyfold.EPLocalization.EPLoc.inv_homMk, Polyfold.MPolyfold.isLocalScDiffeoAt_of_injOn,
  Polyfold.MPolyfold.IsLocalScDiffeoAt.exists_injOn]
#rt_overlap RoundTrip.V10_42.B_to_A [Polyfold.EPLocalization.EPLoc.theorem_10_3_10,
  Polyfold.EPLocalization.isEquivalence_diagFunctor,
  Polyfold.EPLocalization.Diagram.isRefinement_comp_symm,
  Polyfold.EPLocalization.Diagram.isRefinement_id, Polyfold.EPLocalization.Diagram.equiv_comp_symm,
  Polyfold.EPLocalization.Diagram.equiv_symm_comp,
  Polyfold.EPLocalization.Diagram.isEquivalence_Φ_of_equiv_id,
  Polyfold.EPLocalization.isEquivalence_toFunctor_of_comp,
  Polyfold.EPLocalization.isLocalScDiffeo_obj_of_comp,
  Polyfold.EPLocalization.Diagram.isEquivalence_Φ_of_equiv,
  Polyfold.EPLocalization.EPLoc.isIso_homMk_iff, Polyfold.EPLocalization.EPLoc.isIso_homMk,
  Polyfold.EPLocalization.EPLoc.inv_homMk, Polyfold.MPolyfold.isLocalScDiffeoAt_of_injOn,
  Polyfold.MPolyfold.IsLocalScDiffeoAt.exists_injOn]

end RoundTrip.V10_42
