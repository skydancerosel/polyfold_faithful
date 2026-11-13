import Polyfold.Chapter10.Localization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.3 (pp. 489–492; 2017: pp. 352–355): **Definition 10.3.9, Theorem
10.3.10, Proposition 10.3.11, Definition 10.3.12, Theorems 10.3.14 and 10.3.15** (2017:
Definitions 10.8, 10.9, Theorems 10.4–10.6, Proposition 10.6), with the proof of Theorem 10.3.10
in Appendix 10.6.2 (pp. 515–519), and the example (E1) of p. 483.  Numbers and pages are the
2021 text's, the 2017 ones in parentheses.  The diagrams, their equivalence and composition
(Theorem 10.3.8) are in `Localization.lean`; Propositions 10.3.16, 10.3.17, Definition 10.3.20
and Theorem 10.3.21 in `LocalizationProperties.lean`.

# The category `EP(E⁻¹)`

## The text, paraphrased

(Definition 10.3.9, p. 489) A class `[a] = [X ←F A →G Y]` is a generalized map `X → Y`; it is a
generalized isomorphism if some `[b] : Y → X` has `[b] ∘ [a] = [1_X]`, `[a] ∘ [b] = [1_Y]`, and
`[b] = [a]⁻¹`.  (Theorem 10.3.10) `[a]` is a generalized isomorphism iff `G` is an equivalence, and
then `[a]⁻¹ = [Y ←G A →F X]`.  *Proof* (Appendix 10.6.2): if `G` is an equivalence, the composite
`X ←(F∘π₁) A ×_Y A →(F∘π₂) X` is refined by `X ←F A →F X` (diagonal), which refines `1_X` (by
`F`).  Conversely, for `[b] = [Y ←G B →Ψ X]`, comparing with `1_X` shows that `Ψ ∘ πB` and
`Φ ∘ πA'` are equivalences (Propositions 10.1.5, 10.1.6); (C1) then `Φ` is full, faithful and
essentially surjective, and (C2) a local sc-diffeomorphism, so an equivalence by Lemma 10.1.2.
(p. 490, Proposition 10.3.11) `|g ∘ f| = |g| ∘ |f|`.  (Definition 10.3.12) The category
`EP(E⁻¹)`: ep-groupoids and generalized maps.  (Remark 10.3.13, p. 491, not formalized: `X` as an
atlas for an orbifold-type structure on `|X|`.)  (Theorem 10.3.14) A functor `i : EP → EP(E⁻¹)`,
the identity on objects, `i(Φ) = [X ←1 X →Φ Y]`; for an equivalence `F`, `i(F)` is invertible
with `i(F)⁻¹ = [Y ←F X →1 X]`; *proof*: `X ←πX X ×_Y Y →(Ψ∘πY) Z` and `d_{Ψ∘Φ}` are related by
the refinement `πX`, as `Φ ∘ πX ≃ πY`.  (Theorem 10.3.15, p. 492) `|·| : EP(E⁻¹) → TOP`,
`X ↦ |X|`, `[d] ↦ |Φ| ∘ |F|⁻¹`.  (p. 483, (E1)) Isomorphisms of `EP` are equivalences.

## What is formalized (namespace `Polyfold.EPLocalization`)

* Helpers: `MPolyfold.isLocalScDiffeoAt_of_injOn` (local injectivity and a local sc-smooth right
  inverse give a local sc-diffeomorphism), `MPolyfold.IsLocalScDiffeoAt.exists_injOn`.
* **Definition 10.3.12**: `EPLoc` (a one-field structure around `EP`: `EPLoc.of`,
  `EPLoc.toEP`) with its `Category` instance, morphisms `Quotient (Diagram.setoid X Y)`;
  `EPLoc.homMk` (`[d]`), `homMk_comp`, `id_eq`, `homMk_eq_homMk_iff`, `homMk_surjective`.
* **Definition 10.3.9**: `EPLoc.IsGeneralizedIso`, `isGeneralizedIso_iff_isIso`.
* **Theorem 10.3.10**: `EPLoc.theorem_10_3_10`, from `Diagram.isEquivalence_Φ_of_equiv_id`,
  (C1) `isEquivalence_toFunctor_of_comp`, (C2) `isLocalScDiffeo_obj_of_comp`,
  `Diagram.isEquivalence_Φ_of_equiv`, `Diagram.symm`, `Diagram.equiv_comp_symm`,
  `Diagram.equiv_symm_comp`; corollaries `isIso_homMk_iff`, `isIso_homMk`, `inv_homMk`.
* **Proposition 10.3.11**: `EPLoc.proposition_10_3_11` (`EPLoc.orbitMap`,
  `continuous_orbitMap`, `orbitMap_id`).  **Theorem 10.3.15**: `EPLoc.orbitFunctor`,
  `EPLoc.theorem_10_3_15`.
* **Theorem 10.3.14**: `Diagram.ofFunctor` (`d_Φ`), `Diagram.isRefinement_ofFunctor_comp`,
  `EPLoc.localizationFunctor`, `EPLoc.theorem_10_3_14`, `isInvertedBy_localizationFunctor`,
  `inv_localizationFunctor_map`; `homMk_eq` (`[X ←F A →Φ Y] = i(Φ) ∘ i(F)⁻¹`).
* **(E1)**: `isEquivalence_of_isIso`.  ((E2), (E3) are `EpFunctor.IsEquivalence.comp` and
  `EpFunctor.proposition_10_1_5` of `Equivalence.lean`.)
* Witnesses (`Examples`): `pairEP`, `pointEP`, `pairToPointEP`; `isGeneralizedIso_pairToPoint`
  (`i(pairToPoint)` is a generalized isomorphism, `pairToPoint` is not an isomorphism of `EP`),
  `inv_localizationFunctor_map_pairToPoint`, and `equiv_pairToPoint_id` (the diagram
  `point ← ℤ-pair → point` of two copies of `pairToPoint` is equivalent to `1_point`).

## What the text leaves implicit, and the choices made

* **Size and order.**  `EPLoc.{u} : Type (u + 1)` wraps `EP.{u}`, with `Category.{u + 1}`, a
  large category like `EP`; `f ≫ g` is the text's `g ∘ f` (`homMk_comp`).
* **Relation with Mathlib's localization.**  This file proves `MorphismProperty.IsInvertedBy`
  (`isInvertedBy_localizationFunctor`).  The universal property mentioned on p. 483 is proved
  since 2026-11-12 in `GapP2_F_LocUniversal.lean` (`EPLoc.isLocalization`, Mathlib's
  `Functor.IsLocalization`, and `EPLoc.universal_property`): a functor inverting the equivalences
  identifies naturally equivalent sc-smooth functors, with the weak fibred product `X ×_Y Y` as
  the cylinder (`map_eq_of_naturallyEquivalent`).
* **Theorem 10.3.10 (2)** ("the inverse is") is stated as: every inverse of `[a]` equals
  `[Y ←G A →F X]`; `inv_homMk` is the same with Mathlib's `inv`.
* **(C1).**  Faithfulness is checked with `k = k' = 1_b` in the text's morphisms `(h, ϕ, k)`; in
  the text's injectivity argument `A ×_X B` is read as `A ×_Y B` and `mor_Y(Ψ(a), Ψ(a'))` as
  `mor_X(Ψ(b), Ψ(b'))`, and in the essential surjectivity "between `Φ(a)` and `x`" as "and `y`"
  (possible misprints).  Fullness and essential surjectivity follow the text.
* **(C2).**  The text's map `Γ(b') = (b', (s|U)⁻¹(b'), …)` is read with `(s|U)⁻¹(Ψ(b'))`
  (possible misprint), and the text then uses that `Γ' : U' → A` is a local sc-diffeomorphism;
  as we read it, this needs `Ψ` to be a local sc-diffeomorphism, the other half of (C2).  We argue
  differently: a local inverse `κ` of the equivalence `Φ ∘ πA'` at `(b, ϕ, a)` gives the local
  sc-smooth right inverse `πA' ∘ κ` of `Φ` with value `a` at `Φ(a)`; and `Φ` is injective near
  `a`, by a local section `a' ↦ (a', ϕ(a'), b(a'))` of the local sc-diffeomorphism
  `πA : A ×_Y B → A` and the local injectivity of `Ψ ∘ πB`, of `s` and of `G`
  (`isLocalScDiffeoAt_of_injOn`).
* **Theorem 10.3.14.**  The text calls `d_{Ψ∘Φ}` a refinement of (10.13) with
  `πX : X ×_Y Y → X`; with Definition 10.3.1 as stated (the refining equivalence goes from the
  refinement), it is (10.13) that refines `d_{Ψ∘Φ}` by `πX`, which is what we prove; the
  equality of classes is the same.
* **Theorem 10.3.15.**  `TOP` is `TopCat.{u}`; the remark that the orbit spaces are metrizable
  is not part of the formalized statement.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v

/-! ### Local sc-diffeomorphisms from local injectivity and a local right inverse -/

namespace MPolyfold

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ParacompactSpace M] {P : MPolyfold M}
  {N : Type v} [TopologicalSpace N] [T2Space N] [ParacompactSpace N] {Q : MPolyfold N}

/-- An sc-smooth map which is injective on an open neighbourhood `U` of `x` and has an
sc-smooth right inverse `r` near `f(x)` with `r(f(x)) = x` is a local sc-diffeomorphism at `x`. -/
theorem isLocalScDiffeoAt_of_injOn {f : M → N} {x : M} (hf : P.IsScSmoothMap Q f) {U : Set M}
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

/-- A local sc-diffeomorphism at `x` is injective on an open neighbourhood of `x`. -/
theorem IsLocalScDiffeoAt.exists_injOn {f : M → N} {x : M} (h : P.IsLocalScDiffeoAt Q f x) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ InjOn f U := by
  obtain ⟨U, V, g, hx, hd⟩ := h
  exact ⟨U, hd.isScSmoothOn.isOpen, hx, fun a ha b hb hab => by
    rw [← hd.left_inv a ha, hab, hd.left_inv b hb]⟩

end MPolyfold

namespace EPLocalization

open WeakFibredProduct

variable {X Y Z : EP.{u}}

/-! ### Theorem 10.3.10: the generalized isomorphisms -/

namespace Diagram

/-- If `d : X ←F A →Φ X` is equivalent to `1_X`, then `Φ` is an equivalence (2021 p. 517:
`Ψ ∘ πB ∘ Γ ≃ Ψ' ≃ 1_X ∘ Θ = Θ`, Propositions 10.1.5 and 10.1.6). -/
theorem isEquivalence_Φ_of_equiv_id {d : Diagram X X} (h : Equiv d (id X)) :
    d.Φ.IsEquivalence := by
  obtain ⟨w, ⟨Γ, hΓ, -, hΦΓ⟩, ⟨Θ, hΘ, -, hΘΦ⟩⟩ := h
  have : (d.Φ.comp Γ).IsEquivalence := (EpFunctor.proposition_10_1_5 (hΦΓ.trans hΘΦ.symm)).2 hΘ
  exact EpFunctor.proposition_10_1_6 hΓ this

end Diagram

section Inverse

variable {A B : EP.{u}} {F : EpFunctor A.X X.X} {Φ : EpFunctor A.X Y.X}
  {G : EpFunctor B.X Y.X} {Ψ : EpFunctor B.X X.X}

/-- **Claim (C1) of the proof of Theorem 10.3.10** (2021 pp. 517–518): if `G` is an equivalence
and `Ψ ∘ πB : A ×_Y B → X`, `Φ ∘ πA' : B ×_X A → Y` are equivalences, then `Φ` is an
equivalence of categories. -/
theorem isEquivalence_toFunctor_of_comp (hG : G.IsEquivalence) (h : Admissible Φ G)
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

/-- **Claim (C2) of the proof of Theorem 10.3.10** (2021 pp. 518–519): under the hypotheses of
`isEquivalence_toFunctor_of_comp`, `Φ` is a local sc-diffeomorphism on objects.  Near `a`, a
local inverse of `Φ ∘ πA'` at a point `(b, ϕ, a)` gives a local right inverse of `Φ`, and `Φ` is
injective near `a` (through a local section of `πA : A ×_Y B → A` and the local injectivity of
`Ψ ∘ πB`, `s` and `G`). -/
theorem isLocalScDiffeo_obj_of_comp (hG : G.IsEquivalence) (h : Admissible Φ G)
    (h' : Admissible Ψ F) (hP : (Ψ.comp (projRight Φ G h)).IsEquivalence)
    (hQ : (Φ.comp (projRight Ψ F h')).IsEquivalence) :
    A.X.PObj.IsLocalScDiffeo Y.X.PObj Φ.obj := fun a => by
  -- a local right inverse `r = πA' ∘ κ` of `Φ` near `Φ(a)`
  obtain ⟨p, ψ, hs, ht⟩ := hP.exists_iso (F.obj a)
  obtain ⟨U₀, V, κ, hqU₀, hd⟩ := hQ.isLocalScDiffeo_obj (Obj.mk Ψ F p.z ψ a hs ht)
  have hr : Y.X.PObj.IsScSmoothOn A.X.PObj (Obj.z ∘ κ) V :=
    MPolyfold.IsScSmoothOn.comp (isScSmoothMap_z h') hd.isScSmoothOn_inv (mapsTo_univ _ _)
  have hrx : (Obj.z ∘ κ) (Φ.obj a) = a := by
    change (κ ((Φ.comp (projRight Ψ F h')).obj (Obj.mk Ψ F p.z ψ a hs ht))).z = a
    rw [hd.left_inv _ hqU₀]
    rfl
  -- the injectivity of `Φ` near `a`
  obtain ⟨b, φ₀, hs₀, ht₀⟩ := hG.exists_iso (Φ.obj a)
  let p₀ : WeakFibredProduct.Obj Φ G := Obj.mk Φ G a (Y.X.inv φ₀) b
    (by rw [Y.X.src_inv, ht₀]) (by rw [Y.X.tgt_inv, hs₀])
  obtain ⟨V₀, W₀, σ, hp₀, hσ⟩ := isLocalScDiffeo_x h hG.isLocalScDiffeo_obj p₀
  obtain ⟨U₁, hU₁, hp₁, hinj₁⟩ := (hP.isLocalScDiffeo_obj.at p₀).exists_injOn
  obtain ⟨U₂, hU₂, hp₂, hinj₂⟩ := (Y.X.isLocalScDiffeo_src.at p₀.φ).exists_injOn
  obtain ⟨U₃, hU₃, hp₃, hinj₃⟩ := (hG.isLocalScDiffeo_obj.at b).exists_injOn
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
  exact MPolyfold.isLocalScDiffeoAt_of_injOn Φ.isScSmoothMap_obj hU haU hinj hr
    (hd.mapsTo hqU₀) (fun y hy => hd.right_inv y hy) hrx

end Inverse

namespace Diagram

/-- **The hard direction of Theorem 10.3.10 (1)** (2021 pp. 516–519): if `[b] ∘ [a] = [1_X]` and
`[a] ∘ [b] = [1_Y]`, then the functor `Φ` of `a : X ←F A →Φ Y` is an equivalence. -/
theorem isEquivalence_Φ_of_equiv {a : Diagram X Y} {b : Diagram Y X}
    (hab : Equiv (a.comp b) (id X)) (hba : Equiv (b.comp a) (id Y)) : a.Φ.IsEquivalence := by
  have hP := isEquivalence_Φ_of_equiv_id hab
  have hQ := isEquivalence_Φ_of_equiv_id hba
  exact a.Φ.lemma_10_1_2
    (isEquivalence_toFunctor_of_comp b.isEquivalence_F (a.admissible b) (b.admissible a) hP hQ)
    (isLocalScDiffeo_obj_of_comp b.isEquivalence_F (a.admissible b) (b.admissible a) hP hQ)

/-- The reversed diagram `Y ←Φ A →F X` of a diagram `X ←F A →Φ Y` whose `Φ` is an
equivalence (2021 Theorem 10.3.10 (2)). -/
def symm (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) : Diagram Y X :=
  ⟨d.A, d.Φ, hΦ, d.F⟩

/-- `[symm d] ∘ [d] = [1_X]` (2021 p. 516). -/
theorem equiv_comp_symm (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) :
    Equiv (d.comp (d.symm hΦ)) (id X) :=
  ⟨⟨d.A, d.F, d.isEquivalence_F, d.F⟩, isRefinement_comp_symm d.A d.F d.isEquivalence_F d.Φ hΦ d.F,
    isRefinement_id d.A d.F d.isEquivalence_F⟩

/-- `[d] ∘ [symm d] = [1_Y]` (2021 p. 516, "similarly"). -/
theorem equiv_symm_comp (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) :
    Equiv ((d.symm hΦ).comp d) (id Y) :=
  ⟨⟨d.A, d.Φ, hΦ, d.Φ⟩, isRefinement_comp_symm d.A d.Φ hΦ d.F d.isEquivalence_F d.Φ,
    isRefinement_id d.A d.Φ hΦ⟩

end Diagram

/-! ### Definition 10.3.12: the category `EP(E⁻¹)` -/

/-- **2021 Definition 10.3.12, p. 490 (2017: Definition 10.9, p. 354)**: the category
`EP(E⁻¹)`, with the ep-groupoids as objects and the equivalence classes of diagrams (the
generalized maps) as morphisms. -/
structure EPLoc : Type (u + 1) where
  /-- The ep-groupoid `X` as an object of `EP(E⁻¹)`. -/
  of ::
  /-- The ep-groupoid underlying an object of `EP(E⁻¹)`. -/
  toEP : EP.{u}

namespace EPLoc

@[simp] theorem toEP_of (X : EP.{u}) : (of X).toEP = X := rfl

@[simp] theorem of_toEP (X : EPLoc.{u}) : of X.toEP = X := rfl

instance : Category.{u + 1} EPLoc.{u} where
  Hom X Y := Quotient (Diagram.setoid X.toEP Y.toEP)
  id X := ⟦Diagram.id X.toEP⟧
  comp f g := Quotient.map₂ Diagram.comp (fun _ _ hd _ _ he => Diagram.Equiv.comp hd he) f g
  id_comp f := Quotient.inductionOn f fun d => Quotient.sound (Diagram.isRefinement_id_comp d).equiv
  comp_id f := Quotient.inductionOn f fun d => Quotient.sound (Diagram.isRefinement_comp_id d).equiv
  assoc f g k := Quotient.inductionOn₃ f g k fun d e c => Quotient.sound (Diagram.equiv_assoc d e c)

/-- The generalized map `[d] : X → Y` of a diagram (2021 Definition 10.3.9). -/
def homMk (d : Diagram X Y) : of X ⟶ of Y := ⟦d⟧

theorem homMk_comp (d : Diagram X Y) (e : Diagram Y Z) : homMk d ≫ homMk e = homMk (d.comp e) :=
  rfl

theorem id_eq (X : EP.{u}) : 𝟙 (of X) = homMk (Diagram.id X) := rfl

theorem homMk_eq_homMk_iff {d d' : Diagram X Y} : homMk d = homMk d' ↔ Diagram.Equiv d d' :=
  Quotient.eq

theorem homMk_surjective (f : of X ⟶ of Y) : ∃ d : Diagram X Y, homMk d = f :=
  Quotient.exists_rep f

/-! ### Definition 10.3.9 and Theorem 10.3.10 -/

/-- **2021 Definition 10.3.9, p. 489 (2017: Definition 10.8, p. 352)**: a generalized map
`f : X → Y` is a **generalized isomorphism** if some `g : Y → X` has `g ∘ f = 1_X` and
`f ∘ g = 1_Y` (Mathlib's `f ≫ g = 𝟙 X`, `g ≫ f = 𝟙 Y`); `g` is the inverse `f⁻¹`. -/
def IsGeneralizedIso {X Y : EPLoc.{u}} (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y

/-- Generalized isomorphisms are the isomorphisms of `EP(E⁻¹)`. -/
theorem isGeneralizedIso_iff_isIso {X Y : EPLoc.{u}} (f : X ⟶ Y) :
    IsGeneralizedIso f ↔ IsIso f :=
  ⟨fun h => ⟨h⟩, fun h => h.out⟩

/-- **2021 Theorem 10.3.10, p. 489 (2017: Theorem 10.4, p. 353)**, proved in Appendix 10.6.2
(pp. 515–519): (1) `[X ←F A →Φ Y]` is a generalized isomorphism iff `Φ` is an equivalence;
(2) its inverse is then `[Y ←Φ A →F X]`. -/
theorem theorem_10_3_10 (d : Diagram X Y) :
    (IsGeneralizedIso (homMk d) ↔ d.Φ.IsEquivalence) ∧
    ∀ hΦ : d.Φ.IsEquivalence, ∀ g : of Y ⟶ of X, homMk d ≫ g = 𝟙 _ → g ≫ homMk d = 𝟙 _ →
      g = homMk (d.symm hΦ) := by
  have h₁ : ∀ hΦ : d.Φ.IsEquivalence, homMk d ≫ homMk (d.symm hΦ) = 𝟙 _ := fun hΦ =>
    homMk_eq_homMk_iff.2 (d.equiv_comp_symm hΦ)
  have h₂ : ∀ hΦ : d.Φ.IsEquivalence, homMk (d.symm hΦ) ≫ homMk d = 𝟙 _ := fun hΦ =>
    homMk_eq_homMk_iff.2 (d.equiv_symm_comp hΦ)
  refine ⟨⟨fun ⟨g, hg₁, hg₂⟩ => ?_, fun hΦ => ⟨_, h₁ hΦ, h₂ hΦ⟩⟩, fun hΦ g hg₁ hg₂ => ?_⟩
  · obtain ⟨e, rfl⟩ := homMk_surjective g
    exact Diagram.isEquivalence_Φ_of_equiv (homMk_eq_homMk_iff.1 hg₁) (homMk_eq_homMk_iff.1 hg₂)
  · calc g = g ≫ homMk d ≫ homMk (d.symm hΦ) := by rw [h₁ hΦ, Category.comp_id]
      _ = homMk (d.symm hΦ) := by rw [← Category.assoc, hg₂, Category.id_comp]

/-- `[X ←F A →Φ Y]` is an isomorphism of `EP(E⁻¹)` iff `Φ` is an equivalence. -/
theorem isIso_homMk_iff (d : Diagram X Y) : IsIso (homMk d) ↔ d.Φ.IsEquivalence :=
  (isGeneralizedIso_iff_isIso _).symm.trans (theorem_10_3_10 d).1

theorem isIso_homMk (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) : IsIso (homMk d) :=
  (isIso_homMk_iff d).2 hΦ

/-- The inverse of `[X ←F A →Φ Y]` is `[Y ←Φ A →F X]` (Theorem 10.3.10 (2)). -/
theorem inv_homMk (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) :
    haveI := isIso_homMk d hΦ
    inv (homMk d) = homMk (d.symm hΦ) := by
  have := isIso_homMk d hΦ
  exact IsIso.inv_eq_of_hom_inv_id (homMk_eq_homMk_iff.2 (d.equiv_comp_symm hΦ))

/-! ### Proposition 10.3.11 and Theorem 10.3.15: the orbit-space functor -/

/-- The map of orbit spaces `|f| : |X| → |Y|` of a generalized map (2021 Definition 10.3.7). -/
def orbitMap {X Y : EPLoc.{u}} (f : X ⟶ Y) : X.toEP.X.OrbitSpace → Y.toEP.X.OrbitSpace :=
  Diagram.orbitMapQ f

@[simp] theorem orbitMap_homMk (d : Diagram X Y) : orbitMap (homMk d) = d.orbitMap := rfl

theorem continuous_orbitMap {X Y : EPLoc.{u}} (f : X ⟶ Y) : Continuous (orbitMap f) :=
  Quotient.inductionOn (motive := fun f : X ⟶ Y => Continuous (orbitMap f)) f
    fun d => Diagram.continuous_orbitMap d

theorem orbitMap_id (X : EPLoc.{u}) : orbitMap (𝟙 X) = _root_.id := Diagram.orbitMap_id

/-- **2021 Proposition 10.3.11, p. 490 (2017: Proposition 10.6, p. 353)**: `|g ∘ f| = |g| ∘ |f|`
for generalized maps `f : X → Y`, `g : Y → Z`. -/
theorem proposition_10_3_11 {X Y Z : EPLoc.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    orbitMap (f ≫ g) = orbitMap g ∘ orbitMap f :=
  Quotient.inductionOn₂ (motive := fun (f : X ⟶ Y) (g : Y ⟶ Z) =>
    orbitMap (f ≫ g) = orbitMap g ∘ orbitMap f) f g fun d e => Diagram.orbitMap_comp d e

/-- **The orbit-space functor** `|·| : EP(E⁻¹) → TOP` (2021 (10.12), Theorem 10.3.15). -/
def orbitFunctor : EPLoc.{u} ⥤ TopCat.{u} where
  obj X := TopCat.of X.toEP.X.OrbitSpace
  map f := TopCat.ofHom ⟨orbitMap f, continuous_orbitMap f⟩
  map_id X := by
    ext q
    exact congrFun (orbitMap_id X) q
  map_comp f g := by
    ext q
    exact congrFun (proposition_10_3_11 f g) q

/-- **2021 Theorem 10.3.15, p. 492 (2017: Theorem 10.6, p. 355)**: the functor
`|·| : EP(E⁻¹) → TOP` takes `X` to its orbit space `|X|` and `[X ←F A →Φ Y]` to
`|Φ| ∘ |F|⁻¹ : |X| → |Y|`. -/
theorem theorem_10_3_15 :
    (∀ X : EP.{u}, orbitFunctor.obj (of X) = TopCat.of X.X.OrbitSpace) ∧
    ∀ {X Y : EP.{u}} (d : Diagram X Y), ⇑(orbitFunctor.map (homMk d)).hom =
      d.Φ.orbitMap ∘ (IsHomeomorph.homeomorph _ d.isEquivalence_F.isHomeomorph_orbitMap).symm :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-! ### Theorem 10.3.14: the localization functor `EP → EP(E⁻¹)` -/

/-- The diagram `d_Φ = X ←1 X →Φ Y` of an sc-smooth functor (2021 Theorem 10.3.14). -/
def _root_.Polyfold.EPLocalization.Diagram.ofFunctor (Φ : X ⟶ Y) : Diagram X Y :=
  ⟨X, EpFunctor.id X.X, EpFunctor.IsEquivalence.id X.X, Φ⟩

/-- `X ←πX X ×_Y Y →(Ψ∘πY) Z` (the representative (10.13) of `[d_Ψ] ∘ [d_Φ]`) refines
`d_{Ψ∘Φ}` by `πX`, since `Φ ∘ πX ≃ πY` (2021 p. 491). -/
theorem _root_.Polyfold.EPLocalization.Diagram.isRefinement_ofFunctor_comp (Φ : X ⟶ Y)
    (Ψ : Y ⟶ Z) : ((Diagram.ofFunctor Φ).comp (Diagram.ofFunctor Ψ)).IsRefinement
      (Diagram.ofFunctor (Φ ≫ Ψ)) :=
  ⟨projLeft Φ (EpFunctor.id Y.X) _, isEquivalence_projLeft (EpFunctor.IsEquivalence.id _) _,
    .refl _, (naturallyEquivalent _).comp_right Ψ⟩

/-- **The localization functor** `i : EP → EP(E⁻¹)`, the identity on objects and
`Φ ↦ [d_Φ] = [X ←1 X →Φ Y]` on morphisms (2021 Theorem 10.3.14). -/
def localizationFunctor : EP.{u} ⥤ EPLoc.{u} where
  obj X := of X
  map Φ := homMk (Diagram.ofFunctor Φ)
  map_id _ := rfl
  map_comp Φ Ψ := homMk_eq_homMk_iff.2 (Diagram.isRefinement_ofFunctor_comp Φ Ψ).equiv.symm

@[simp] theorem localizationFunctor_obj (X : EP.{u}) : localizationFunctor.obj X = of X := rfl

theorem localizationFunctor_map (Φ : X ⟶ Y) :
    localizationFunctor.map Φ = homMk (Diagram.ofFunctor Φ) := rfl

/-- **2021 Theorem 10.3.14, p. 491 (2017: Theorem 10.5, p. 354)**: the functor
`i : EP → EP(E⁻¹)` is the identity on objects, `i(Φ) = [X ←1 X →Φ Y]`, and for an equivalence
`F : X → Y` the morphism `i(F)` is invertible with `i(F)⁻¹ = [Y ←F X →1 X]`. -/
theorem theorem_10_3_14 :
    (∀ X : EP.{u}, localizationFunctor.obj X = of X) ∧
    (∀ {X Y : EP.{u}} (Φ : X ⟶ Y), localizationFunctor.map Φ =
      homMk ⟨X, EpFunctor.id X.X, EpFunctor.IsEquivalence.id X.X, Φ⟩) ∧
    ∀ {X Y : EP.{u}} (F : X ⟶ Y) (hF : EpFunctor.IsEquivalence F),
      IsGeneralizedIso (localizationFunctor.map F) ∧
      ∀ g : of Y ⟶ of X, localizationFunctor.map F ≫ g = 𝟙 _ →
        g ≫ localizationFunctor.map F = 𝟙 _ →
        g = homMk ⟨X, F, hF, EpFunctor.id X.X⟩ :=
  ⟨fun _ => rfl, fun _ => rfl, fun F hF =>
    ⟨((theorem_10_3_10 (Diagram.ofFunctor F)).1).2 hF,
      (theorem_10_3_10 (Diagram.ofFunctor F)).2 hF⟩⟩

/-- **The relation with Mathlib's localization API**: `i` inverts the equivalences
(`MorphismProperty.IsInvertedBy`), the property that the text's construction is designed for
(2021 p. 483).  The universal property itself is `EPLoc.isLocalization` and
`EPLoc.universal_property` (`GapP2_F_LocUniversal.lean`). -/
theorem isInvertedBy_localizationFunctor :
    EP.equivalences.{u}.IsInvertedBy localizationFunctor := fun _ _ F hF =>
  isIso_homMk (Diagram.ofFunctor F) hF

/-- The inverse of `i(F)` for an equivalence `F`. -/
theorem inv_localizationFunctor_map (F : X ⟶ Y) (hF : EpFunctor.IsEquivalence F) :
    haveI := isInvertedBy_localizationFunctor F hF
    inv (localizationFunctor.map F) = homMk ⟨X, F, hF, EpFunctor.id X.X⟩ :=
  inv_homMk (Diagram.ofFunctor F) hF

/-- Every generalized map is `i(Φ) ∘ i(F)⁻¹` (2021 p. 487: `[X ←F A →Φ Y]`). -/
theorem homMk_eq (d : Diagram X Y) :
    haveI := isInvertedBy_localizationFunctor d.F d.isEquivalence_F
    homMk d = inv (localizationFunctor.map d.F) ≫ localizationFunctor.map d.Φ := by
  rw [inv_localizationFunctor_map _ d.isEquivalence_F]
  refine homMk_eq_homMk_iff.2 (Diagram.IsRefinement.equiv (d' := Diagram.comp
    ⟨d.A, d.F, d.isEquivalence_F, EpFunctor.id d.A.X⟩ (Diagram.ofFunctor d.Φ)) ?_).symm
  exact ⟨projLeft (EpFunctor.id d.A.X) (EpFunctor.id d.A.X) _,
    isEquivalence_projLeft (EpFunctor.IsEquivalence.id _) _, .refl _,
    (naturallyEquivalent _).comp_right d.Φ⟩

end EPLoc

/-! ### (E1): isomorphisms of `EP` are equivalences -/

/-- **(E1), 2021 p. 483**: every isomorphism of the category `EP` is an equivalence. -/
theorem isEquivalence_of_isIso {X Y : EP.{u}} (F : X ⟶ Y) [IsIso F] :
    EpFunctor.IsEquivalence F := by
  obtain ⟨G, hFG, hGF⟩ := (inferInstance : IsIso F).out
  have hGFo : ∀ x, G.obj (F.obj x) = x := fun x => congrArg (fun H : X ⟶ X => H.obj x) hFG
  have hFGo : ∀ y, F.obj (G.obj y) = y := fun y => congrArg (fun H : Y ⟶ Y => H.obj y) hGF
  have hGFm : ∀ φ, G.mor (F.mor φ) = φ := fun φ => congrArg (fun H : X ⟶ X => H.mor φ) hFG
  have hFGm : ∀ ψ, F.mor (G.mor ψ) = ψ := fun ψ => congrArg (fun H : Y ⟶ Y => H.mor ψ) hGF
  refine EpFunctor.lemma_10_1_2 F
    { faithful := (GroupoidFunctor.faithful_iff _).2 fun φ φ' _ _ he => by
        rw [← hGFm φ, ← hGFm φ']
        exact congrArg G.mor he
      full := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht =>
        ⟨G.mor ψ, by rw [G.src_mor, hs, hGFo], by rw [G.tgt_mor, ht, hGFo], hFGm ψ⟩
      essSurj := (GroupoidFunctor.essSurj_iff _).2 fun y =>
        ⟨G.obj y, Y.X.unit y, by rw [Y.X.src_unit, hFGo], Y.X.tgt_unit y⟩ } fun x =>
    ⟨univ, univ, G.obj, mem_univ x,
      { isScSmoothOn := F.isScSmoothMap_obj
        isScSmoothOn_inv := G.isScSmoothMap_obj
        mapsTo := mapsTo_univ _ _
        mapsTo_inv := mapsTo_univ _ _
        left_inv := fun x _ => hGFo x
        right_inv := fun y _ => hFGo y }⟩

/-! ### Witnesses -/

namespace Examples

open EpGroupoid.Examples EPLoc

/-- The pair groupoid of `ℤ` as an object of `EP`. -/
abbrev pairEP : EP.{0} := ⟨ℤ, ℤ × ℤ, pairEpGroupoid⟩

/-- The point ep-groupoid as an object of `EP`. -/
abbrev pointEP : EP.{0} := ⟨Unit, Unit, pointEpGroupoid⟩

/-- The equivalence `pairToPoint` as a morphism of `EP`. -/
def pairToPointEP : pairEP ⟶ pointEP := pairToPoint

theorem isEquivalence_pairToPointEP : EpFunctor.IsEquivalence pairToPointEP :=
  isEquivalence_pairToPoint

/-- `pairToPoint` is not an isomorphism of `EP`. -/
theorem not_isIso_pairToPointEP : ¬ IsIso pairToPointEP := fun h => by
  obtain ⟨G, hFG, -⟩ := h.out
  exact not_exists_leftInverse_pairToPoint
    ⟨G, fun x => congrArg (fun H : pairEP ⟶ pairEP => H.obj x) hFG⟩

/-- **Witness for Definition 10.3.9 and Theorem 10.3.14**: `i(pairToPoint)` is a generalized
isomorphism, although `pairToPoint` is not an isomorphism of `EP`. -/
theorem isGeneralizedIso_pairToPoint :
    IsGeneralizedIso (localizationFunctor.map pairToPointEP) ∧ ¬ IsIso pairToPointEP :=
  ⟨(theorem_10_3_14.2.2 pairToPointEP isEquivalence_pairToPointEP).1, not_isIso_pairToPointEP⟩

/-- **Witness for Definition 10.3.5**: `point ←pairToPoint ℤ-pair →pairToPoint point` is
equivalent to `1_point`, through the refinement `pairToPoint`, which is not an isomorphism. -/
theorem equiv_pairToPoint_id :
    Diagram.Equiv (⟨pairEP, pairToPoint, isEquivalence_pairToPoint, pairToPoint⟩ :
      Diagram pointEP pointEP) (Diagram.id pointEP) :=
  (Diagram.isRefinement_id (X := pointEP) pairEP pairToPoint isEquivalence_pairToPoint).equiv

/-- The inverse of `i(pairToPoint)` is `[point ←pairToPoint ℤ-pair →1 ℤ-pair]`. -/
theorem inv_localizationFunctor_map_pairToPoint :
    haveI := isInvertedBy_localizationFunctor pairToPointEP isEquivalence_pairToPointEP
    inv (localizationFunctor.map pairToPointEP) =
      homMk ⟨pairEP, pairToPoint, isEquivalence_pairToPoint, EpFunctor.id pairEP.X⟩ :=
  inv_localizationFunctor_map pairToPointEP isEquivalence_pairToPointEP

end Examples

end EPLocalization

end Polyfold

