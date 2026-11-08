import Polyfold.Chapter10.WeakFibredProductTheorem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.3 "Localization at the System of Equivalences" (pp. 483–495; 2017:
pp. 347–356): **Definitions 10.3.1, 10.3.3, 10.3.5, 10.3.7, Lemmas 10.3.2, 10.3.4, 10.3.6 and
Theorem 10.3.8** (2017: Definitions 10.4–10.7, Lemmas 10.3–10.5, Theorem 10.3), with the proof of
Theorem 10.3.8 in Appendix 10.6.1 (pp. 509–515).  Numbers and pages are the 2021 text's, the 2017
ones in parentheses.  The category `EP(E⁻¹)` and the rest of §10.3 are in
`LocalizationCategory.lean` and `LocalizationProperties.lean`.

# Diagrams of ep-groupoids and their equivalence classes

## The text, paraphrased

(pp. 483–484) For ep-groupoids `X`, `Y` one considers diagrams `d : X ←F A →Φ Y` with `F` an
equivalence and `Φ` an sc-smooth functor.  (Definition 10.3.1, p. 484) `d'` refines `d`
(`H : d' → d`) if there is an equivalence `H : A' → A` with `F ∘ H ≃ F'` and `Φ ∘ H ≃ Φ'`;
examples: `X ←(F∘H) A' →(Φ∘H) Y`, and `X ←G A →Ψ Y` with `G ≃ F`, `Ψ ≃ Φ` (`H = 1_A`).  (Lemma
10.3.2) A refinement of a refinement is a refinement.  (Definition 10.3.3, p. 485) A common
refinement of `(d, d')` refines both.  (Lemma 10.3.4) Having a common refinement is transitive;
*proof*: for common refinements `W` of `(d, d')` and `W'` of `(d', d'')`, the diagram (10.11)
`X ← W ×_{A'} W' → Y` is one of `(d, d'')`.  (Definition 10.3.5, p. 486) `d`, `d'` are
equivalent if they have a common refinement; the class `[d] : X → Y` is a morphism of a new
category, `Φ ↦ [X ←1 X →Φ Y]`.  (pp. 487–488, Lemma 10.3.6, Definition 10.3.7) `|d| = |Φ| ∘
|F|⁻¹ : |X| → |Y|` is continuous and unchanged under refinement, so `|[d]|` is defined; it is a
homeomorphism if `Φ` is an equivalence too.  (Theorem 10.3.8, p. 488) For `d : X ←F A →Φ Y`,
`d' : Y ←G B →Ψ Z` the class of `X ←(F∘πA) A ×_Y B →(Ψ∘πB) Z` depends only on `[d]`, `[d']`;
the composition is associative, with units `[1_X] = [X ←1 X →1 X]`.  *Proof* (Appendix 10.6.1):
for refinements `H`, `K` with `τ_A' : Φ' → Φ ∘ H`, `τ_B' : G' → G ∘ K`, the functor `L(a', ϕ, b')
= (H(a'), τ_B'(b') ∘ ϕ ∘ τ_A'(a')⁻¹, K(b'))` is an equivalence with `F ∘ πA ∘ L ≃ F' ∘ πA'` and
`Ψ ∘ πB ∘ L ≃ Ψ' ∘ πB'`; the two iterated weak fibred products are "the same space"; and
`X ←πX X ×_X A →(Φ∘πA) Y` refines `d` by `πA`.

## What is formalized (namespace `Polyfold.EPLocalization`)

* Helpers: `GroupoidStr.comp_comp_inv_comp_inv`; `EpFunctor.IsEquivalence.of_comp_left` (if `G`
  and `G ∘ L` are equivalences, so is `L`); `NaturallyEquivalent.of_eq`,
  `NaturallyEquivalent.orbitMap_eq`, `EpFunctor.orbitMap_comp`, `EpFunctor.orbitMap_id`; `wfp`
  (the weak fibred product as an object of `EP`).
* `Diagram X Y` (`A`, `F`, `isEquivalence_F`, `Φ`).  **Definition 10.3.1**: `IsRefinement`, with
  the two examples `isRefinement_precomp` (`precomp`) and `isRefinement_of_naturallyEquivalent`;
  `IsRefinement.refl`.  **Lemma 10.3.2**: `lemma_10_3_2` (`IsRefinement.trans`).
  **Definition 10.3.3**: `IsCommonRefinement`.  **Lemma 10.3.4**: `lemma_10_3_4`.
  **Definition 10.3.5**: `Equiv`, `Diagram.setoid`.
* The functors of Appendix 10.6.1: `wfpMap` (`L`, from `mapMid`, `mapObj`, `mapMor`) with
  `projLeft_comp_wfpMap`, `projRight_comp_wfpMap`, `isEquivalence_wfpMap`; the reassociation
  `assocFunctor` (`assocObj`, `assocMor`), `isEquivalence_assocFunctor`; the diagonal
  `diagFunctor` (`A → A ×_Y A`, used for Theorem 10.3.10), `isEquivalence_diagFunctor`.
* `Diagram.id`, `Diagram.comp` (`d.comp e` represents `[e] ∘ [d]`), `IsRefinement.comp`,
  `Equiv.comp`, `isRefinement_assoc`, `isRefinement_id_comp`, `isRefinement_comp_id`;
  **Theorem 10.3.8**: `theorem_10_3_8`.  For Theorem 10.3.10: `isRefinement_comp_symm`,
  `isRefinement_id`.
* `Diagram.orbitMap` (`|d|`), `continuous_orbitMap`, `isHomeomorph_orbitMap`; **Lemma 10.3.6**:
  `lemma_10_3_6`, `Equiv.orbitMap_eq`; **Definition 10.3.7**: `orbitMapQ`; `orbitMap_id`,
  `orbitMap_comp` (the computation behind Proposition 10.3.11).

## What the text leaves implicit, and the choices made

* **Size.**  A diagram is a structure in `Type (u + 1)`: its middle ep-groupoid ranges over the
  bundled `EP.{u}` (objects and morphisms in `Type u`), and `Diagram.setoid X Y` is a setoid on
  that type.  No class-sized collection occurs: the quotient lives in `Type (u + 1)`, the universe
  of the objects of `EP.{u}` itself.
* **Order of composition.**  `d.comp e` (first `d`, then `e`) is Mathlib's `≫`-order; the text
  writes `[e] ∘ [d]`.  The weak fibred product `A ×_Y B` is `WeakFibredProduct` of `Φ` and `G`
  (objects `(a, ϕ, b)` with `ϕ : Φ(a) → G(b)`); since `G` is an equivalence, `πA` is one
  (`isEquivalence_projLeft`).
* **`L` is an equivalence** (pp. 512–514) is proved by two out of three: `πA ∘ L = H ∘ πA'` holds
  on the nose, `πA`, `πA'` and `H` are equivalences.  The text instead checks directly that `L` is
  a local sc-diffeomorphism, full and faithful; its sc-smoothness, asserted in the text, is proved
  entrywise.  In the text's statement of the naturality of `τ_B'` the letter `τ_A` appears for
  `τ_B'`, and "`(Φ ∘ πB) ∘ L ≃ Ψ' ∘ πB'`" is read as `(Ψ ∘ πB) ∘ L ≃ Ψ' ∘ πB'` (possible
  misprints).
* **Associativity.**  The text identifies `(A ×_Y A') ×_Z A''` and `A ×_Y (A' ×_Z A'')` ("the same
  space"); in Lean they are different types, and the identification is the reassociation functor
  `assocFunctor`, an equivalence by two out of three.  The refinement then holds with the
  identity natural transformations.
* **Units.**  The proof of the unit law writes `[1_X] ∘ [d] = [d]` for `[d] ∘ [1_X] = [d]`
  (possible misprint); `τ(a, ϕ, a)` is read as `τ(x, ϕ, a)` and `ψ = φ` as `ψ = ϕ`.
* **Lemma 10.3.6** uses that naturally equivalent functors induce the same map of orbit spaces
  and `|F ∘ H| = |F| ∘ |H|` (`EpFunctor.orbitMap_comp`); the inverse `|F|⁻¹` is that of the
  homeomorphism of Definition 10.1.1 (2).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v w

/-! ### Helpers -/

namespace GroupoidStr

variable {Obj Mor : Type u} {G : GroupoidStr Obj Mor}

/-- `a ∘ ((b ∘ c) ∘ d⁻¹) ∘ e⁻¹ = ((a ∘ b) ∘ c) ∘ (e ∘ d)⁻¹`. -/
theorem comp_comp_inv_comp_inv {a b c d e : Mor} (h₁ : G.src a = G.tgt b)
    (h₂ : G.src b = G.tgt c) (h₃ : G.src c = G.src d) (h₄ : G.src e = G.tgt d) :
    G.comp (G.comp a (G.comp (G.comp b c) (G.inv d))) (G.inv e) =
      G.comp (G.comp (G.comp a b) c) (G.inv (G.comp e d)) := by
  have s₁ : G.src (G.comp b c) = G.tgt (G.inv d) := by rw [G.src_comp _ _ h₂, G.tgt_inv, h₃]
  have s₂ : G.src a = G.tgt (G.comp b c) := by rw [G.tgt_comp _ _ h₂, h₁]
  have s₃ : G.src (G.comp a b) = G.tgt c := by rw [G.src_comp _ _ h₁, h₂]
  have s₄ : G.src (G.comp (G.comp a b) c) = G.tgt (G.inv d) := by
    rw [G.src_comp _ _ s₃, G.tgt_inv, h₃]
  have s₅ : G.src (G.inv d) = G.tgt (G.inv e) := by rw [G.src_inv, G.tgt_inv, h₄]
  rw [← G.comp_assoc _ _ _ s₂ s₁, ← G.comp_assoc _ _ _ h₁ h₂, G.comp_assoc _ _ _ s₄ s₅,
    inv_comp_rev h₄]

end GroupoidStr

section TwoOutOfThree

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {Obj'' Mor'' : Type w} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Z : EpGroupoid Obj'' Mor''}

namespace EpFunctor

/-- **Two out of three**: if `G` and `G ∘ L` are equivalences, so is `L` (the companion of
Proposition 10.1.6, which cancels on the other side). -/
theorem IsEquivalence.of_comp_left {G : EpFunctor Y Z} {L : EpFunctor X Y}
    (hG : G.IsEquivalence) (hGL : (G.comp L).IsEquivalence) : L.IsEquivalence := by
  rw [isEquivalence_iff] at hG hGL ⊢
  have := hG.1
  have : (L.toFunctor ⋙ G.toFunctor).IsEquivalence := hGL.1
  exact ⟨Functor.isEquivalence_of_comp_right L.toFunctor G.toFunctor, fun x =>
    MPolyfold.IsLocalScDiffeoAt.of_comp_left (hG.2.at (L.obj x)) L.continuous_obj' (hGL.2.at x)⟩

theorem NaturallyEquivalent.of_eq {F G : EpFunctor X Y} (h : F = G) : F.NaturallyEquivalent G :=
  h ▸ NaturallyEquivalent.refl F

/-- Naturally equivalent functors induce the same map of orbit spaces. -/
theorem NaturallyEquivalent.orbitMap_eq {F G : EpFunctor X Y} (h : F.NaturallyEquivalent G) :
    F.orbitMap = G.orbitMap := by
  obtain ⟨τ⟩ := h
  funext q
  induction q using Quotient.inductionOn with | h x => ?_
  exact Y.π_eq_π_iff.2 ⟨τ.app x, τ.src_app x, τ.tgt_app x⟩

/-- `|G ∘ F| = |G| ∘ |F|`. -/
theorem orbitMap_comp (G : EpFunctor Y Z) (F : EpFunctor X Y) :
    (G.comp F).orbitMap = G.orbitMap ∘ F.orbitMap := by
  funext q
  induction q using Quotient.inductionOn with | h x => rfl

theorem orbitMap_id : (EpFunctor.id X).orbitMap = _root_.id := by
  funext q
  induction q using Quotient.inductionOn with | h x => rfl

end EpFunctor

end TwoOutOfThree

/-! ### Diagrams -/

namespace EPLocalization

open WeakFibredProduct

/-- The weak fibred product `A ×_C B` of `F : A → C` and `G : B → C`, an object of `EP`
(Theorem 10.2.2). -/
def wfp {A B C : EP.{u}} (F : EpFunctor A.X C.X) (G : EpFunctor B.X C.X) (h : Admissible F G) :
    EP.{u} :=
  EP.mk (WeakFibredProduct.Obj F G) (WeakFibredProduct.Mor F G) (epGroupoid F G h)

/-- A **diagram** `d : X ←F A →Φ Y` (2021 p. 483 (2017: p. 347)): an ep-groupoid `A`, an
equivalence `F : A → X` and an sc-smooth functor `Φ : A → Y`. -/
structure Diagram (X Y : EP.{u}) : Type (u + 1) where
  /-- The middle ep-groupoid. -/
  A : EP.{u}
  /-- The equivalence `F : A → X`. -/
  F : EpFunctor A.X X.X
  isEquivalence_F : F.IsEquivalence
  /-- The sc-smooth functor `Φ : A → Y`. -/
  Φ : EpFunctor A.X Y.X

namespace Diagram

variable {X Y Z W : EP.{u}}

/-- **2021 Definition 10.3.1, p. 484 (2017: Definition 10.4, p. 348)**: `d'` is a
**refinement** of `d` (`H : d' → d`) if there is an equivalence `H : A' → A` with `F ∘ H ≃ F'`
and `Φ ∘ H ≃ Φ'`. -/
def IsRefinement (d' d : Diagram X Y) : Prop :=
  ∃ H : EpFunctor d'.A.X d.A.X, H.IsEquivalence ∧
    (d.F.comp H).NaturallyEquivalent d'.F ∧ (d.Φ.comp H).NaturallyEquivalent d'.Φ

/-- The diagram `X ←(F∘H) A' →(Φ∘H) Y` for an equivalence `H : A' → A` (the first example after
Definition 10.3.1). -/
def precomp (d : Diagram X Y) {A' : EP.{u}} (H : EpFunctor A'.X d.A.X) (hH : H.IsEquivalence) :
    Diagram X Y :=
  ⟨A', d.F.comp H, d.isEquivalence_F.comp hH, d.Φ.comp H⟩

/-- **The first example after Definition 10.3.1** (2021 p. 484): `X ←(F∘H) A' →(Φ∘H) Y` is a
refinement of `d`. -/
theorem isRefinement_precomp (d : Diagram X Y) {A' : EP.{u}} (H : EpFunctor A'.X d.A.X)
    (hH : H.IsEquivalence) : (d.precomp H hH).IsRefinement d :=
  ⟨H, hH, .refl _, .refl _⟩

/-- **The second example after Definition 10.3.1** (2021 p. 484): if `G ≃ F` and `Ψ ≃ Φ`, then
`X ←G A →Ψ Y` is a refinement of `X ←F A →Φ Y`, with `H = 1_A`. -/
theorem isRefinement_of_naturallyEquivalent (d : Diagram X Y) (G : EpFunctor d.A.X X.X)
    (hG : G.IsEquivalence) (Ψ : EpFunctor d.A.X Y.X) (hGF : G.NaturallyEquivalent d.F)
    (hΨΦ : Ψ.NaturallyEquivalent d.Φ) : (⟨d.A, G, hG, Ψ⟩ : Diagram X Y).IsRefinement d :=
  ⟨EpFunctor.id d.A.X, EpFunctor.IsEquivalence.id _, hGF.symm, hΨΦ.symm⟩

theorem IsRefinement.refl (d : Diagram X Y) : d.IsRefinement d :=
  ⟨EpFunctor.id d.A.X, EpFunctor.IsEquivalence.id _, .refl _, .refl _⟩

/-- **2021 Lemma 10.3.2, p. 484 (2017: Lemma 10.3, p. 348)**: a refinement of a refinement of `d`
is a refinement of `d`. -/
theorem lemma_10_3_2 {d d' d'' : Diagram X Y} (h' : d'.IsRefinement d)
    (h'' : d''.IsRefinement d') : d''.IsRefinement d := by
  obtain ⟨H, hH, hF, hΦ⟩ := h'
  obtain ⟨H', hH', hF', hΦ'⟩ := h''
  exact ⟨H.comp H', hH.comp hH', (hF.comp_left H').trans hF', (hΦ.comp_left H').trans hΦ'⟩

theorem IsRefinement.trans {d d' d'' : Diagram X Y} (h'' : d''.IsRefinement d')
    (h' : d'.IsRefinement d) : d''.IsRefinement d :=
  lemma_10_3_2 h' h''

/-- **2021 Definition 10.3.3, p. 485 (2017: Definition 10.5, p. 349)**: `d''` is a **common
refinement** of `(d, d')` if it is a refinement of both. -/
def IsCommonRefinement (d'' d d' : Diagram X Y) : Prop := d''.IsRefinement d ∧ d''.IsRefinement d'

/-- **2021 Definition 10.3.5, p. 486 (2017: Definition 10.6, p. 350)**: two diagrams are
**equivalent** if they have a common refinement. -/
def Equiv (d d' : Diagram X Y) : Prop := ∃ d'' : Diagram X Y, d''.IsCommonRefinement d d'

theorem Equiv.refl (d : Diagram X Y) : Equiv d d := ⟨d, .refl d, .refl d⟩

theorem Equiv.symm {d d' : Diagram X Y} (h : Equiv d d') : Equiv d' d :=
  let ⟨d'', h₁, h₂⟩ := h
  ⟨d'', h₂, h₁⟩

/-- A refinement is equivalent to the refined diagram. -/
theorem IsRefinement.equiv {d' d : Diagram X Y} (h : d'.IsRefinement d) : Equiv d' d :=
  ⟨d', .refl d', h⟩

/-- **2021 Lemma 10.3.4, p. 485 (2017: Lemma 10.4, p. 349)**: if `(d, d')` and `(d', d'')` have
common refinements, so has `(d, d'')`: with `W` refining `d` (by `H`) and `d'` (by `H'`), `W'`
refining `d'` (by `K`) and `d''` (by `K'`), the diagram `e : X ← W ×_{A'} W' → Y` of (10.11)
(the weak fibred product of `H'` and `K`) refines `d` by `H ∘ πW` and `d''` by `K' ∘ πW'`. -/
theorem lemma_10_3_4 {d d' d'' : Diagram X Y} (h : Equiv d d') (h' : Equiv d' d'') :
    Equiv d d'' := by
  obtain ⟨w, ⟨H, hH, hFH, hΦH⟩, ⟨H', hH', hF'H', hΦ'H'⟩⟩ := h
  obtain ⟨w', ⟨K, hK, hF'K, hΦ'K⟩, ⟨K', hK', hF''K', hΦ''K'⟩⟩ := h'
  have hadm : Admissible H' K := .of_isEquivalence_left hH'
  have hπW : (projLeft H' K hadm).IsEquivalence := isEquivalence_projLeft hK hadm
  have hπW' : (projRight H' K hadm).IsEquivalence := isEquivalence_projRight hH' hadm
  have hnat := naturallyEquivalent hadm
  let e : Diagram X Y := ⟨wfp H' K hadm, w.F.comp (projLeft H' K hadm),
    w.isEquivalence_F.comp hπW, w'.Φ.comp (projRight H' K hadm)⟩
  refine ⟨e, ⟨H.comp (projLeft H' K hadm), hH.comp hπW, ?_, ?_⟩,
    ⟨K'.comp (projRight H' K hadm), hK'.comp hπW', ?_, ?_⟩⟩
  · exact hFH.comp_left _
  · exact (hΦH.comp_left _).trans ((hΦ'H'.symm.comp_left _).trans
      ((hnat.comp_right d'.Φ).trans (hΦ'K.comp_left _)))
  · exact (hF''K'.comp_left _).trans ((hF'K.symm.comp_left _).trans
      ((hnat.symm.comp_right d'.F).trans (hF'H'.comp_left _)))
  · exact hΦ''K'.comp_left _

theorem Equiv.trans {d d' d'' : Diagram X Y} (h : Equiv d d') (h' : Equiv d' d'') :
    Equiv d d'' :=
  lemma_10_3_4 h h'

/-- **The equivalence relation of Definition 10.3.5** (2021 p. 486): having a common refinement. -/
instance setoid (X Y : EP.{u}) : Setoid (Diagram X Y) where
  r := Equiv
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

theorem equiv_iff {d d' : Diagram X Y} : d ≈ d' ↔ Equiv d d' := Iff.rfl

end Diagram

/-! ### The functor `L` of the proof of Theorem 10.3.8 -/

section Map

variable {A A' B B' Y : EP.{u}} {Φ : EpFunctor A.X Y.X} {G : EpFunctor B.X Y.X}
  {Φ' : EpFunctor A'.X Y.X} {G' : EpFunctor B'.X Y.X}
  {H : EpFunctor A'.X A.X} {K : EpFunctor B'.X B.X}
  (τ : EpNatTrans Φ' (Φ.comp H)) (σ : EpNatTrans G' (G.comp K))

/-- The middle entry `τ_B'(z) ∘ ϕ ∘ τ_A'(x)⁻¹` of `L(x, ϕ, z)` ((10.28) of the text). -/
def mapMid (x : A'.Obj) (φ : Y.Mor) (z : B'.Obj) : Y.Mor :=
  Y.X.comp (Y.X.comp (σ.app z) φ) (Y.X.inv (τ.app x))

variable {τ σ}

theorem mapMid_aux {φ : Y.Mor} {z : B'.Obj} (h₂ : Y.X.tgt φ = G'.obj z) :
    Y.X.src (σ.app z) = Y.X.tgt φ :=
  (σ.src_app z).trans h₂.symm

theorem mapMid_aux' {x : A'.Obj} {φ : Y.Mor} {z : B'.Obj} (h₁ : Y.X.src φ = Φ'.obj x)
    (h₂ : Y.X.tgt φ = G'.obj z) :
    Y.X.src (Y.X.comp (σ.app z) φ) = Y.X.tgt (Y.X.inv (τ.app x)) := by
  rw [Y.X.src_comp _ _ (mapMid_aux h₂), Y.X.tgt_inv, τ.src_app, h₁]

theorem src_mapMid {x : A'.Obj} {φ : Y.Mor} {z : B'.Obj} (h₁ : Y.X.src φ = Φ'.obj x)
    (h₂ : Y.X.tgt φ = G'.obj z) : Y.X.src (mapMid τ σ x φ z) = Φ.obj (H.obj x) := by
  rw [mapMid, Y.X.src_comp _ _ (mapMid_aux' h₁ h₂), Y.X.src_inv, τ.tgt_app]
  rfl

theorem tgt_mapMid {x : A'.Obj} {φ : Y.Mor} {z : B'.Obj} (h₁ : Y.X.src φ = Φ'.obj x)
    (h₂ : Y.X.tgt φ = G'.obj z) : Y.X.tgt (mapMid τ σ x φ z) = G.obj (K.obj z) := by
  rw [mapMid, Y.X.tgt_comp _ _ (mapMid_aux' h₁ h₂), Y.X.tgt_comp _ _ (mapMid_aux h₂),
    σ.tgt_app]
  rfl

variable (τ σ)

/-- `L(x, ϕ, z) = (H(x), τ_B'(z) ∘ ϕ ∘ τ_A'(x)⁻¹, K(z))` ((10.28) of the text). -/
def mapObj (p : Obj Φ' G') : Obj Φ G :=
  Obj.mk Φ G (H.obj p.x) (mapMid τ σ p.x p.φ p.z) (K.obj p.z) (src_mapMid p.src_φ p.tgt_φ)
    (tgt_mapMid p.src_φ p.tgt_φ)

/-- `L(h, ϕ, k) = (H(h), τ_B'(s k) ∘ ϕ ∘ τ_A'(s h)⁻¹, K(k))` ((10.30) of the text). -/
def mapMor (m : Mor Φ' G') : Mor Φ G :=
  Mor.mk Φ G (H.mor m.h) (mapMid τ σ (A'.X.src m.h) m.φ (B'.X.src m.k)) (K.mor m.k)
    ((src_mapMid m.src_φ m.tgt_φ).trans (congrArg Φ.obj (H.src_mor m.h).symm))
    ((tgt_mapMid m.src_φ m.tgt_φ).trans (congrArg G.obj (K.src_mor m.k).symm))

variable {τ σ}

theorem src_mapMor (m : Mor Φ' G') : src (mapMor τ σ m) = mapObj τ σ (src m) :=
  Obj.ext (H.src_mor _) rfl (K.src_mor _)

theorem tgt_mapMor (m : Mor Φ' G') : tgt (mapMor τ σ m) = mapObj τ σ (tgt m) := by
  refine Obj.ext (H.tgt_mor _) ?_ (K.tgt_mor _)
  change Y.X.comp (Y.X.comp (G.mor (K.mor m.k)) (mapMid τ σ (A'.X.src m.h) m.φ (B'.X.src m.k)))
      (Y.X.inv (Φ.mor (H.mor m.h))) =
    mapMid τ σ (A'.X.tgt m.h) (conj Φ' G' m.h m.φ m.k) (B'.X.tgt m.k)
  rw [mapMid, mapMid, conj,
    GroupoidStr.comp_comp_inv_comp_inv
      ((G.src_mor _).trans ((congrArg G.obj (K.src_mor _)).trans (σ.tgt_app _).symm))
      ((σ.src_app _).trans m.tgt_φ.symm) (m.src_φ.trans (τ.src_app _).symm)
      ((Φ.src_mor _).trans ((congrArg Φ.obj (H.src_mor _)).trans (τ.tgt_app _).symm)),
    GroupoidStr.comp_comp_inv_comp_inv ((σ.src_app _).trans (G'.tgt_mor _).symm)
      ((G'.src_mor _).trans m.tgt_φ.symm) (m.src_φ.trans (Φ'.src_mor _).symm)
      ((τ.src_app _).trans (Φ'.tgt_mor _).symm),
    σ.naturality, τ.naturality]
  rfl

variable (τ σ)

/-- **The functor `L : A' ×_Y B' → A ×_Y B`** of the proof of Theorem 10.3.8 (2021 pp. 510–511,
(10.28) and (10.30)), for `H : A' → A`, `K : B' → B` and natural transformations
`τ_A' : Φ' → Φ ∘ H`, `τ_B' : G' → G ∘ K`. -/
def wfpMap (h : Admissible Φ G) (h' : Admissible Φ' G') :
    EpFunctor (epGroupoid Φ' G' h') (epGroupoid Φ G h) where
  obj := mapObj τ σ
  mor := mapMor τ σ
  src_mor := src_mapMor
  tgt_mor := tgt_mapMor
  mor_comp m m' hc := by
    have hc : src m = tgt m' := hc
    have hc' : src (mapMor τ σ m) = tgt (mapMor τ σ m') := by
      rw [src_mapMor, tgt_mapMor, hc]
    change mapMor τ σ (comp m m') = comp (mapMor τ σ m) (mapMor τ σ m')
    have e₁ := (src_eq_tgt_iff.1 hc).1
    have e₂ := (src_eq_tgt_iff.1 hc).2.2
    refine Mor.ext ?_ ?_ ?_
    · rw [h_comp hc']
      change H.mor (comp m m').h = A.X.comp (H.mor m.h) (H.mor m'.h)
      rw [h_comp hc]
      exact H.mor_comp _ _ e₁
    · rw [φ_comp hc']
      change mapMid τ σ (A'.X.src (comp m m').h) (comp m m').φ (B'.X.src (comp m m').k) =
        mapMid τ σ (A'.X.src m'.h) m'.φ (B'.X.src m'.k)
      rw [h_comp hc, φ_comp hc, k_comp hc, A'.X.src_comp _ _ e₁, B'.X.src_comp _ _ e₂]
    · rw [k_comp hc']
      change K.mor (comp m m').k = B.X.comp (K.mor m.k) (K.mor m'.k)
      rw [k_comp hc]
      exact K.mor_comp _ _ e₂
  mor_unit p := by
    refine Mor.ext (H.mor_unit _) ?_ (K.mor_unit _)
    change mapMid τ σ (A'.X.src (A'.X.unit p.x)) p.φ (B'.X.src (B'.X.unit p.z)) =
      mapMid τ σ p.x p.φ p.z
    rw [A'.X.src_unit, B'.X.src_unit]
  isScSmoothMap_obj := isScSmoothOn_obj_of h (H.isScSmoothMap_obj.comp (isScSmoothMap_x h'))
    (Y.X.isScSmoothOn_comp_of
      (Y.X.isScSmoothOn_comp_of (σ.isScSmoothMap_app.comp (isScSmoothMap_z h'))
        (isScSmoothMap_φ h') fun p _ => mapMid_aux p.tgt_φ)
      (Y.X.isScSmoothMap_inv.comp (τ.isScSmoothMap_app.comp (isScSmoothMap_x h')))
      fun p _ => mapMid_aux' p.src_φ p.tgt_φ)
    (K.isScSmoothMap_obj.comp (isScSmoothMap_z h'))
  isScSmoothMap_mor := isScSmoothOn_mor_of h (H.isScSmoothMap_mor.comp (isScSmoothMap_h h'))
    (Y.X.isScSmoothOn_comp_of
      (Y.X.isScSmoothOn_comp_of
        (σ.isScSmoothMap_app.comp (B'.X.isScSmoothMap_src.comp (isScSmoothMap_k h')))
        (isScSmoothMap_mφ h') fun m _ => mapMid_aux m.tgt_φ)
      (Y.X.isScSmoothMap_inv.comp
        (τ.isScSmoothMap_app.comp (A'.X.isScSmoothMap_src.comp (isScSmoothMap_h h'))))
      fun m _ => mapMid_aux' m.src_φ m.tgt_φ)
    (K.isScSmoothMap_mor.comp (isScSmoothMap_k h'))

theorem projLeft_comp_wfpMap (h : Admissible Φ G) (h' : Admissible Φ' G') :
    (projLeft Φ G h).comp (wfpMap τ σ h h') = H.comp (projLeft Φ' G' h') := rfl

theorem projRight_comp_wfpMap (h : Admissible Φ G) (h' : Admissible Φ' G') :
    (projRight Φ G h).comp (wfpMap τ σ h h') = K.comp (projRight Φ' G' h') := rfl

/-- **`L` is an equivalence** (2021 pp. 512–514).  We use that `πA ∘ L = H ∘ πA'` is an
equivalence and that `πA` is one (two out of three), in place of the text's direct verification
that `L` is a local sc-diffeomorphism, full and faithful. -/
theorem isEquivalence_wfpMap (h : Admissible Φ G) (h' : Admissible Φ' G') (hH : H.IsEquivalence)
    (hG : G.IsEquivalence) (hG' : G'.IsEquivalence) : (wfpMap τ σ h h').IsEquivalence :=
  EpFunctor.IsEquivalence.of_comp_left (isEquivalence_projLeft hG h)
    (by rw [projLeft_comp_wfpMap]; exact hH.comp (isEquivalence_projLeft hG' h'))

end Map

/-! ### The reassociation `(A ×_Y B) ×_Z C → A ×_Y (B ×_Z C)` -/

section Assoc

variable {A B C Y Z : EP.{u}} {Φ : EpFunctor A.X Y.X} {G : EpFunctor B.X Y.X}
  {Ψ : EpFunctor B.X Z.X} {H : EpFunctor C.X Z.X} {h₁ : Admissible Φ G} {h₃ : Admissible Ψ H}

variable (h₁ h₃) in
/-- `((a, φ, b), ψ, c) ↦ (a, φ, (b, ψ, c))` on objects. -/
def assocObj (p : Obj (Ψ.comp (projRight Φ G h₁)) H) : Obj Φ (G.comp (projLeft Ψ H h₃)) :=
  Obj.mk Φ (G.comp (projLeft Ψ H h₃)) p.x.x p.x.φ (Obj.mk Ψ H p.x.z p.φ p.z p.src_φ p.tgt_φ)
    p.x.src_φ p.x.tgt_φ

variable (h₁ h₃) in
/-- `((h, φ, k), ψ, l) ↦ (h, φ, (k, ψ, l))` on morphisms. -/
def assocMor (m : Mor (Ψ.comp (projRight Φ G h₁)) H) : Mor Φ (G.comp (projLeft Ψ H h₃)) :=
  Mor.mk Φ (G.comp (projLeft Ψ H h₃)) m.h.h m.h.φ (Mor.mk Ψ H m.h.k m.φ m.k m.src_φ m.tgt_φ)
    m.h.src_φ m.h.tgt_φ

theorem src_assocMor (m : Mor (Ψ.comp (projRight Φ G h₁)) H) :
    src (assocMor h₁ h₃ m) = assocObj h₁ h₃ (src m) := rfl

theorem tgt_assocMor (m : Mor (Ψ.comp (projRight Φ G h₁)) H) :
    tgt (assocMor h₁ h₃ m) = assocObj h₁ h₃ (tgt m) := rfl

/-- **The reassociation** `(A ×_Y B) ×_Z C → A ×_Y (B ×_Z C)` (2021 p. 514: the text identifies
the two weak fibred products and uses the identity map). -/
def assocFunctor (h₂ : Admissible (Ψ.comp (projRight Φ G h₁)) H)
    (h₄ : Admissible Φ (G.comp (projLeft Ψ H h₃))) :
    EpFunctor (epGroupoid (Ψ.comp (projRight Φ G h₁)) H h₂)
      (epGroupoid Φ (G.comp (projLeft Ψ H h₃)) h₄) where
  obj := assocObj h₁ h₃
  mor := assocMor h₁ h₃
  src_mor := src_assocMor
  tgt_mor := tgt_assocMor
  mor_comp m m' hc := by
    have hc : src m = tgt m' := hc
    have hc' : src (assocMor h₁ h₃ m) = tgt (assocMor h₁ h₃ m') := by
      rw [src_assocMor, tgt_assocMor, hc]
    have hcx : src m.h = tgt m'.h := (src_eq_tgt_iff.1 hc).1
    have hc'z : src (assocMor h₁ h₃ m).k = tgt (assocMor h₁ h₃ m').k :=
      (src_eq_tgt_iff.1 hc').2.2
    change assocMor h₁ h₃ (comp m m') = comp (assocMor h₁ h₃ m) (assocMor h₁ h₃ m')
    refine Mor.ext ?_ ?_ ?_
    · rw [h_comp hc']
      change (comp m m').h.h = A.X.comp m.h.h m'.h.h
      rw [h_comp hc]
      exact h_comp hcx
    · rw [φ_comp hc']
      change (comp m m').h.φ = m'.h.φ
      rw [h_comp hc]
      exact φ_comp hcx
    · rw [k_comp hc']
      change _ = comp (assocMor h₁ h₃ m).k (assocMor h₁ h₃ m').k
      refine Mor.ext ?_ ?_ ?_
      · rw [h_comp hc'z]
        change (comp m m').h.k = B.X.comp m.h.k m'.h.k
        rw [h_comp hc]
        exact k_comp hcx
      · rw [φ_comp hc'z]
        change (comp m m').φ = m'.φ
        rw [φ_comp hc]
      · rw [k_comp hc'z]
        change (comp m m').k = C.X.comp m.k m'.k
        rw [k_comp hc]
  mor_unit _ := rfl
  isScSmoothMap_obj := isScSmoothOn_obj_of h₄ ((isScSmoothMap_x h₁).comp (isScSmoothMap_x h₂))
    ((isScSmoothMap_φ h₁).comp (isScSmoothMap_x h₂))
    (isScSmoothOn_obj_of h₃ ((isScSmoothMap_z h₁).comp (isScSmoothMap_x h₂)) (isScSmoothMap_φ h₂)
      (isScSmoothMap_z h₂))
  isScSmoothMap_mor := isScSmoothOn_mor_of h₄ ((isScSmoothMap_h h₁).comp (isScSmoothMap_h h₂))
    ((isScSmoothMap_mφ h₁).comp (isScSmoothMap_h h₂))
    (isScSmoothOn_mor_of h₃ ((isScSmoothMap_k h₁).comp (isScSmoothMap_h h₂))
      (isScSmoothMap_mφ h₂) (isScSmoothMap_k h₂))

theorem projLeft_comp_assocFunctor (h₂ : Admissible (Ψ.comp (projRight Φ G h₁)) H)
    (h₄ : Admissible Φ (G.comp (projLeft Ψ H h₃))) :
    (projLeft Φ (G.comp (projLeft Ψ H h₃)) h₄).comp (assocFunctor h₂ h₄) =
      (projLeft Φ G h₁).comp (projLeft (Ψ.comp (projRight Φ G h₁)) H h₂) := rfl

/-- The reassociation is an equivalence when `G` and `H` are (two out of three, with
`πA ∘ R = πA ∘ π_{A ×_Y B}`). -/
theorem isEquivalence_assocFunctor (hG : G.IsEquivalence) (hH : H.IsEquivalence)
    (h₂ : Admissible (Ψ.comp (projRight Φ G h₁)) H)
    (h₄ : Admissible Φ (G.comp (projLeft Ψ H h₃))) : (assocFunctor h₂ h₄).IsEquivalence :=
  EpFunctor.IsEquivalence.of_comp_left
    (isEquivalence_projLeft (hG.comp (isEquivalence_projLeft hH h₃)) h₄)
    (by rw [projLeft_comp_assocFunctor]
        exact (isEquivalence_projLeft hG h₁).comp (isEquivalence_projLeft hH h₂))

end Assoc

/-! ### The diagonal `A → A ×_Y A` -/

section Diagonal

variable {A Y : EP.{u}} (G : EpFunctor A.X Y.X)

/-- `a ↦ (a, 1_{G(a)}, a)`. -/
def diagObj (a : A.Obj) : Obj G G :=
  Obj.mk G G a (Y.X.unit (G.obj a)) a (Y.X.src_unit _) (Y.X.tgt_unit _)

/-- `h ↦ (h, 1_{G(s h)}, h)`. -/
def diagMor (m : A.Mor) : Mor G G :=
  Mor.mk G G m (Y.X.unit (G.obj (A.X.src m))) m (Y.X.src_unit _) (Y.X.tgt_unit _)

/-- **The diagonal** `A → A ×_Y A`, `a ↦ (a, 1_{G(a)}, a)` (2021 p. 516, proof of Theorem
10.3.10). -/
def diagFunctor (h : Admissible G G) : EpFunctor A.X (epGroupoid G G h) where
  obj := diagObj G
  mor := diagMor G
  src_mor _ := rfl
  tgt_mor m := by
    refine Obj.ext rfl ?_ rfl
    change Y.X.comp (Y.X.comp (G.mor m) (Y.X.unit (G.obj (A.X.src m)))) (Y.X.inv (G.mor m)) =
      Y.X.unit (G.obj (A.X.tgt m))
    rw [GroupoidStr.comp_unit_of_eq (G.src_mor m), Y.X.comp_inv, G.tgt_mor]
  mor_comp m m' hc := by
    have hc' : src (diagMor G m) = tgt (diagMor G m') := by
      refine Obj.ext hc ?_ hc
      change Y.X.unit (G.obj (A.X.src m)) =
        Y.X.comp (Y.X.comp (G.mor m') (Y.X.unit (G.obj (A.X.src m')))) (Y.X.inv (G.mor m'))
      rw [GroupoidStr.comp_unit_of_eq (G.src_mor m'), Y.X.comp_inv, G.tgt_mor, hc]
    change diagMor G (A.X.comp m m') = comp (diagMor G m) (diagMor G m')
    refine Mor.ext (h_comp hc').symm ?_ (k_comp hc').symm
    rw [φ_comp hc']
    change Y.X.unit (G.obj (A.X.src (A.X.comp m m'))) = Y.X.unit (G.obj (A.X.src m'))
    rw [A.X.src_comp _ _ hc]
  mor_unit a := by
    refine Mor.ext rfl ?_ rfl
    change Y.X.unit (G.obj (A.X.src (A.X.unit a))) = Y.X.unit (G.obj a)
    rw [A.X.src_unit]
  isScSmoothMap_obj := isScSmoothOn_obj_of h MPolyfold.isScSmoothMap_id
    (Y.X.isScSmoothMap_unit.comp G.isScSmoothMap_obj) MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor := isScSmoothOn_mor_of h MPolyfold.isScSmoothMap_id
    (Y.X.isScSmoothMap_unit.comp (G.isScSmoothMap_obj.comp A.X.isScSmoothMap_src))
    MPolyfold.isScSmoothMap_id

/-- The diagonal is an equivalence when `G` is one (`π₁ ∘ Δ = 1_A`). -/
theorem isEquivalence_diagFunctor (hG : G.IsEquivalence) (h : Admissible G G) :
    (diagFunctor G h).IsEquivalence :=
  EpFunctor.IsEquivalence.of_comp_left (isEquivalence_projLeft hG h)
    (EpFunctor.IsEquivalence.id A.X)

end Diagonal

/-! ### Composition of diagrams and Theorem 10.3.8 -/

namespace Diagram

variable {X Y Z W : EP.{u}}

/-- The diagram `1_X = X ←1 X →1 X`. -/
def id (X : EP.{u}) : Diagram X X :=
  ⟨X, EpFunctor.id X.X, EpFunctor.IsEquivalence.id X.X, EpFunctor.id X.X⟩

/-- The admissibility of the weak fibred product of `d.Φ : A → Y` and `e.F : B → Y`. -/
theorem admissible (d : Diagram X Y) (e : Diagram Y Z) : Admissible d.Φ e.F :=
  .of_isEquivalence_right e.isEquivalence_F

/-- **The composite diagram** `X ←(F∘πA) A ×_Y B →(Ψ∘πB) Z` of `d : X ←F A →Φ Y` and
`e : Y ←G B →Ψ Z` (2021 Theorem 10.3.8, p. 488), the weak fibred product being that of `Φ` and
`G`; `d.comp e` is the text's `d'' ` representing `[e] ∘ [d]`. -/
def comp (d : Diagram X Y) (e : Diagram Y Z) : Diagram X Z :=
  ⟨wfp d.Φ e.F (d.admissible e), d.F.comp (projLeft d.Φ e.F (d.admissible e)),
    d.isEquivalence_F.comp (isEquivalence_projLeft e.isEquivalence_F _),
    e.Φ.comp (projRight d.Φ e.F (d.admissible e))⟩

/-- **The main step of the proof of Theorem 10.3.8** (2021 pp. 509–514): if `d'` refines `d` and
`e'` refines `e`, then `d'.comp e'` refines `d.comp e`, by the equivalence
`L : A' ×_Y B' → A ×_Y B` of (10.28), (10.30). -/
theorem IsRefinement.comp {d d' : Diagram X Y} {e e' : Diagram Y Z} (hd : d'.IsRefinement d)
    (he : e'.IsRefinement e) : (d'.comp e').IsRefinement (d.comp e) := by
  obtain ⟨H, hH, hFH, hΦH⟩ := hd
  obtain ⟨K, hK, hGK, hΨK⟩ := he
  obtain ⟨τ⟩ := hΦH.symm
  obtain ⟨σ⟩ := hGK.symm
  refine ⟨wfpMap τ σ (d.admissible e) (d'.admissible e'),
    isEquivalence_wfpMap τ σ _ _ hH e.isEquivalence_F e'.isEquivalence_F, ?_, ?_⟩
  · exact hFH.comp_left (projLeft d'.Φ e'.F _)
  · exact hΨK.comp_left (projRight d'.Φ e'.F _)

/-- **Theorem 10.3.8, first claim**: the class of the composite only depends on the classes. -/
theorem Equiv.comp {d₁ d₂ : Diagram X Y} {e₁ e₂ : Diagram Y Z} (hd : Equiv d₁ d₂)
    (he : Equiv e₁ e₂) : Equiv (d₁.comp e₁) (d₂.comp e₂) := by
  obtain ⟨d, hd₁, hd₂⟩ := hd
  obtain ⟨e, he₁, he₂⟩ := he
  exact ⟨d.comp e, hd₁.comp he₁, hd₂.comp he₂⟩

/-- **Associativity** (2021 p. 514): `(d.comp d').comp d''` refines `d.comp (d'.comp d'')` by
the reassociation `(A ×_Y A') ×_Z A'' → A ×_Y (A' ×_Z A'')`. -/
theorem isRefinement_assoc (d : Diagram X Y) (d' : Diagram Y Z) (d'' : Diagram Z W) :
    ((d.comp d').comp d'').IsRefinement (d.comp (d'.comp d'')) :=
  ⟨assocFunctor ((d.comp d').admissible d'') (d.admissible (d'.comp d'')),
    isEquivalence_assocFunctor d'.isEquivalence_F d''.isEquivalence_F _ _, .refl _, .refl _⟩

theorem equiv_assoc (d : Diagram X Y) (d' : Diagram Y Z) (d'' : Diagram Z W) :
    Equiv ((d.comp d').comp d'') (d.comp (d'.comp d'')) :=
  (isRefinement_assoc d d' d'').equiv

/-- **`[d] ∘ [1_X] = [d]`** (2021 p. 515): `X ←πX X ×_X A →(Φ∘πA) Y` refines `d` by `πA`, with
`F ∘ πA ≃ πX` by `τ(x, ϕ, a) = ϕ`. -/
theorem isRefinement_id_comp (d : Diagram X Y) : ((id X).comp d).IsRefinement d :=
  ⟨projRight (EpFunctor.id X.X) d.F ((id X).admissible d),
    isEquivalence_projRight (EpFunctor.IsEquivalence.id _) _,
    (naturallyEquivalent ((id X).admissible d)).symm, .refl _⟩

/-- **`[1_Y] ∘ [d] = [d]`** (2021 p. 515, "similarly"): `X ←(F∘πA) A ×_Y Y →πY Y` refines `d` by
`πA`. -/
theorem isRefinement_comp_id (d : Diagram X Y) : (d.comp (id Y)).IsRefinement d :=
  ⟨projLeft d.Φ (EpFunctor.id Y.X) (d.admissible (id Y)),
    isEquivalence_projLeft (EpFunctor.IsEquivalence.id _) _, .refl _,
    naturallyEquivalent (d.admissible (id Y))⟩

/-- **2021 Theorem 10.3.8, p. 488 (2017: Theorem 10.3, p. 352)**, proved in Appendix 10.6.1
(pp. 509–515): the class of the composite `X ←(F∘πA) A ×_Y B →(Ψ∘πB) Z` is independent of the
representatives; the composition is associative; and `[1_X]`, `[1_Y]` are units. -/
theorem theorem_10_3_8 :
    (∀ {d₁ d₂ : Diagram X Y} {e₁ e₂ : Diagram Y Z}, d₁ ≈ d₂ → e₁ ≈ e₂ →
      d₁.comp e₁ ≈ d₂.comp e₂) ∧
    (∀ (d : Diagram X Y) (d' : Diagram Y Z) (d'' : Diagram Z W),
      (d.comp d').comp d'' ≈ d.comp (d'.comp d'')) ∧
    (∀ d : Diagram X Y, (id X).comp d ≈ d ∧ d.comp (id Y) ≈ d) :=
  ⟨Equiv.comp, equiv_assoc, fun d => ⟨(isRefinement_id_comp d).equiv,
    (isRefinement_comp_id d).equiv⟩⟩

/-! ### Diagrams with two equivalences -/

/-- **The composite with the reversed diagram** (2021 p. 516, proof of Theorem 10.3.10): for
equivalences `F : A → X`, `G : A → Y` and any `Ψ : A → Z`, the composite of `X ←F A →G Y` and
`Y ←G A →Ψ Z` is refined by `X ←F A →Ψ Z`, through the diagonal `A → A ×_Y A`. -/
theorem isRefinement_comp_symm (A : EP.{u}) (F : EpFunctor A.X X.X) (hF : F.IsEquivalence)
    (G : EpFunctor A.X Y.X) (hG : G.IsEquivalence) (Ψ : EpFunctor A.X Z.X) :
    (⟨A, F, hF, Ψ⟩ : Diagram X Z).IsRefinement
      ((⟨A, F, hF, G⟩ : Diagram X Y).comp ⟨A, G, hG, Ψ⟩) :=
  ⟨diagFunctor G (.of_isEquivalence_right hG), isEquivalence_diagFunctor G hG _, .refl _,
    .refl _⟩

/-- `X ←F A →F X` refines `1_X` through `F` (2021 p. 516). -/
theorem isRefinement_id (A : EP.{u}) (F : EpFunctor A.X X.X) (hF : F.IsEquivalence) :
    (⟨A, F, hF, F⟩ : Diagram X X).IsRefinement (id X) :=
  ⟨F, hF, .refl _, .refl _⟩

/-! ### Lemma 10.3.6 and Definition 10.3.7: the maps of orbit spaces -/

/-- **The map of orbit spaces** `|d| = |Φ| ∘ |F|⁻¹ : |X| → |Y|` of a diagram (2021 p. 487), `|F|`
being a homeomorphism by Definition 10.1.1 (2). -/
def orbitMap (d : Diagram X Y) : X.X.OrbitSpace → Y.X.OrbitSpace :=
  d.Φ.orbitMap ∘ (IsHomeomorph.homeomorph _ d.isEquivalence_F.isHomeomorph_orbitMap).symm

/-- `|d|` is continuous (2021 p. 487). -/
theorem continuous_orbitMap (d : Diagram X Y) : Continuous d.orbitMap :=
  d.Φ.continuous_orbitMap.comp (Homeomorph.continuous _)

/-- `|d|(|F|(q)) = |Φ|(q)`. -/
theorem orbitMap_orbitMap_F (d : Diagram X Y) (q : d.A.X.OrbitSpace) :
    d.orbitMap (d.F.orbitMap q) = d.Φ.orbitMap q := by
  change d.Φ.orbitMap ((IsHomeomorph.homeomorph _ d.isEquivalence_F.isHomeomorph_orbitMap).symm
    ((IsHomeomorph.homeomorph _ d.isEquivalence_F.isHomeomorph_orbitMap) q)) = _
  rw [Homeomorph.symm_apply_apply]

theorem orbitMap_eq_of {d : Diagram X Y} {q : X.X.OrbitSpace} {r : d.A.X.OrbitSpace}
    (h : d.F.orbitMap r = q) : d.orbitMap q = d.Φ.orbitMap r :=
  h ▸ d.orbitMap_orbitMap_F r

/-- **2021 Lemma 10.3.6, p. 488 (2017: Lemma 10.5, p. 351)**: if `H : d' → d` is a refinement,
then `|d| = |d'|`. -/
theorem lemma_10_3_6 {d d' : Diagram X Y} (h : d'.IsRefinement d) : d.orbitMap = d'.orbitMap := by
  obtain ⟨H, -, hF, hΦ⟩ := h
  funext q
  obtain ⟨r, rfl⟩ := d'.isEquivalence_F.isHomeomorph_orbitMap.surjective q
  rw [orbitMap_orbitMap_F, ← hΦ.orbitMap_eq, EpFunctor.orbitMap_comp]
  refine orbitMap_eq_of ?_
  rw [← hF.orbitMap_eq, EpFunctor.orbitMap_comp]
  rfl

/-- Equivalent diagrams induce the same map of orbit spaces (2021 p. 488, after Lemma 10.3.6). -/
theorem Equiv.orbitMap_eq {d d' : Diagram X Y} (h : Equiv d d') : d.orbitMap = d'.orbitMap := by
  obtain ⟨d'', h₁, h₂⟩ := h
  rw [lemma_10_3_6 h₁, lemma_10_3_6 h₂]

/-- **2021 Definition 10.3.7, p. 488 (2017: Definition 10.7, p. 351)**: the map of orbit spaces
`|[d]| : |X| → |Y|` of an equivalence class `[d]`, `|Φ| ∘ |F|⁻¹` for any representative. -/
def orbitMapQ : Quotient (setoid X Y) → X.X.OrbitSpace → Y.X.OrbitSpace :=
  Quotient.lift orbitMap fun _ _ h => Equiv.orbitMap_eq h

@[simp]
theorem orbitMapQ_mk (d : Diagram X Y) : orbitMapQ ⟦d⟧ = d.orbitMap := rfl

/-- If both legs are equivalences, `|[d]|` is a homeomorphism (2021 p. 488). -/
theorem isHomeomorph_orbitMap (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) :
    IsHomeomorph d.orbitMap :=
  (((IsHomeomorph.homeomorph _ d.isEquivalence_F.isHomeomorph_orbitMap).symm.trans
    (IsHomeomorph.homeomorph _ hΦ.isHomeomorph_orbitMap))).isHomeomorph

/-- `|1_X| = 1`. -/
theorem orbitMap_id : (id X).orbitMap = _root_.id := by
  funext q
  rw [orbitMap_eq_of (r := q) (congrFun EpFunctor.orbitMap_id q)]
  exact congrFun EpFunctor.orbitMap_id q

/-- **The computation before Proposition 10.3.11** (2021 p. 490): `|d.comp e| = |e| ∘ |d|`; with
`(a, ϕ, b) ∈ A ×_Y B`, `ϕ : Φ(a) → G(b)` gives `|Φ(a)| = |G(b)|`. -/
theorem orbitMap_comp (d : Diagram X Y) (e : Diagram Y Z) :
    (d.comp e).orbitMap = e.orbitMap ∘ d.orbitMap := by
  funext q
  obtain ⟨r, rfl⟩ := (d.comp e).isEquivalence_F.isHomeomorph_orbitMap.surjective q
  rw [orbitMap_orbitMap_F, Function.comp_apply]
  have hnat := (naturallyEquivalent (d.admissible e)).orbitMap_eq
  have h₁ : d.orbitMap ((d.comp e).F.orbitMap r) =
      e.F.orbitMap ((projRight d.Φ e.F (d.admissible e)).orbitMap r) := by
    refine (orbitMap_eq_of (r := (projLeft d.Φ e.F (d.admissible e)).orbitMap r) ?_).trans ?_
    · change d.F.orbitMap _ = (d.F.comp (projLeft d.Φ e.F (d.admissible e))).orbitMap r
      rw [EpFunctor.orbitMap_comp]
      rfl
    · have := congrFun hnat r
      simp only [EpFunctor.orbitMap_comp] at this
      exact this
  rw [h₁, orbitMap_orbitMap_F]
  change (e.Φ.comp (projRight d.Φ e.F (d.admissible e))).orbitMap r = _
  rw [EpFunctor.orbitMap_comp]
  rfl

end Diagram

end EPLocalization

end Polyfold
