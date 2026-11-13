import Polyfold.Chapter11.EquivalenceFormsInfty
import Polyfold.Chapter10.LocalizationCategory

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §11.2,
pp. 526 and 531–532: **Definition 11.2.7** (2017: Definition 11.3) and **Theorem 11.2.1
(1)–(3)** (2017: Theorem 11.2) (gap G.129).  Numbers and pages are the 2021 text's.

# Sc-differential forms along generalized maps

## The text, paraphrased

(Definition 11.2.7) For a generalized map `[d] = [X ←F A →G Y]` the pull-back of a form `ω'`
on `Y` is `[d]^*ω' = F_* G^*ω'`; for a generalized isomorphism (`G` an equivalence) the
push-forward of a form `ω` on `X` is `[d]_*ω = G_* F^*ω`.  By Lemma 11.2.6 they do not depend
on the diagram representing `[d]`.  (Theorem 11.2.1) (1) `d ∘ d = 0` on `Ω*_{ep,∞}(X)`;
(2) a generalized map `f : X → Y` has a well-defined pull-back `f^*` with
`d_X ∘ f^* = f^* ∘ d_Y`; (3) a generalized isomorphism `h` has a well-defined push-forward
`h_*` with `h_* ∘ d_X = d_Y ∘ h_*`, `h_* ∘ h^* = 1`, `h^* ∘ h_* = 1`.

## What is formalized

Namespace `Polyfold.EPLocalization` (Chapter 10's diagrams `Diagram X Y` and the category
`EPLoc = EP(E⁻¹)` of generalized maps):
* `Diagram.formsPullback d k = F_* ∘ Φ^*` and `Diagram.formsPush d hΦ k = Φ_* ∘ F^*` for a
  diagram `d : X ←F A →Φ Y`; `formsPullback_eq_of_isRefinement`, `formsPullback_eq_of_equiv`,
  `formsPush_eq_of_isRefinement`, `formsPush_eq_of_equiv` (independence of the diagram, from
  Lemma 11.2.6); `formsPullback_comp_formsPush`, `formsPush_comp_formsPullback`;
  `epFormsInftyD_comp_formsPullback`, `epFormsInftyD_comp_formsPush`; `formsPullback_id`,
  `formsPullback_ofFunctor`, `formsPullback_comp` (the pull-back of the composite diagram).
* **Definition 11.2.7**: `EPLoc.formsPullback f k : Ωᵏ_{ep,∞}(Y) → Ωᵏ_{ep,∞}(X)` for a
  generalized map `f : X → Y` (`formsPullback_homMk`: it is `F_* ∘ Φ^*` for every diagram
  representing `f`), and `EPLoc.formsPush f hf k : Ωᵏ_{ep,∞}(X) → Ωᵏ_{ep,∞}(Y)` for a
  generalized isomorphism (`formsPush_homMk`: it is `Φ_* ∘ F^*` for every diagram representing
  `f`).
* **Theorem 11.2.1**: `theorem_11_2_1_one` (`d ∘ d = 0`), `theorem_11_2_1_two`
  (`d_X ∘ f^* = f^* ∘ d_Y`), `theorem_11_2_1_three` (`h_* ∘ d_X = d_Y ∘ h_*`,
  `h_* ∘ h^* = 1`, `h^* ∘ h_* = 1`).
* Beyond the text: `EPLoc.formsPullback_id`, `EPLoc.formsPullback_comp`
  (`(g ∘ f)^* = f^* ∘ g^*` for generalized maps) and `EPLoc.formsPullback_localizationFunctor_map`
  (for an sc-smooth functor `Φ` the pull-back along `[d_Φ]` is `Φ^*`): `Ωᵏ_{ep,∞}` is a
  contravariant functor on `EP(E⁻¹)`.

## The reading

A generalized isomorphism is `EPLoc.IsGeneralizedIso` (Definition 10.3.9: it has a two-sided
inverse `g`); `formsPush f hf` is defined as `g^*`, and by Theorem 10.3.10 it is `Φ_* ∘ F^*`
for every diagram `X ←F A →Φ Y` representing `f` (`formsPush_homMk`), which is the text's
definition.  No hypothesis is added.
-/

set_option maxSynthPendingDepth 3

open Set Function CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace EPLocalization

open WeakFibredProduct

namespace Diagram

variable {X Y Z : EP.{u}}

/-- **2021 Definition 11.2.7, p. 532 (2017: Definition 11.3), on a diagram**: the pull-back
`F_* ∘ Φ^* : Ωᵏ_{ep,∞}(Y) → Ωᵏ_{ep,∞}(X)` of `d : X ←F A →Φ Y`. -/
def formsPullback (d : Diagram X Y) (k : ℕ) : Y.epFormsInfty k →ₗ[ℝ] X.epFormsInfty k :=
  (EP.epFormsInftyPush d.isEquivalence_F k).comp (EP.epFormsInftyPullback d.Φ k)

/-- **2021 Definition 11.2.7, p. 532 (2017: Definition 11.3), on a diagram**: the push-forward
`Φ_* ∘ F^* : Ωᵏ_{ep,∞}(X) → Ωᵏ_{ep,∞}(Y)` of `d : X ←F A →Φ Y` with `Φ` an equivalence. -/
def formsPush (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) (k : ℕ) :
    X.epFormsInfty k →ₗ[ℝ] Y.epFormsInfty k :=
  (EP.epFormsInftyPush hΦ k).comp (EP.epFormsInftyPullback d.F k)

/-- The push-forward of `d` is the pull-back of the reversed diagram. -/
theorem formsPush_eq_formsPullback_symm (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) (k : ℕ) :
    d.formsPush hΦ k = (d.symm hΦ).formsPullback k := rfl

/-- **The pull-back does not change under refinements** (Lemma 11.2.6). -/
theorem formsPullback_eq_of_isRefinement {d d' : Diagram X Y} (h : d'.IsRefinement d) (k : ℕ) :
    d'.formsPullback k = d.formsPullback k := by
  obtain ⟨H, hH, hF, hΦ⟩ := h
  exact (EP.lemma_11_2_6 d.isEquivalence_F d.Φ d'.isEquivalence_F d'.Φ hH hF hΦ k).symm

/-- **Equivalent diagrams have the same pull-back** (2021 p. 532, after Definition 11.2.7). -/
theorem formsPullback_eq_of_equiv {d d' : Diagram X Y} (h : Equiv d d') (k : ℕ) :
    d.formsPullback k = d'.formsPullback k := by
  obtain ⟨d'', h₁, h₂⟩ := h
  rw [← formsPullback_eq_of_isRefinement h₁, ← formsPullback_eq_of_isRefinement h₂]

/-- **The push-forward does not change under refinements** (Lemma 11.2.6). -/
theorem formsPush_eq_of_isRefinement {d d' : Diagram X Y} (h : d'.IsRefinement d)
    (hΦ : d.Φ.IsEquivalence) (hΦ' : d'.Φ.IsEquivalence) (k : ℕ) :
    d'.formsPush hΦ' k = d.formsPush hΦ k := by
  obtain ⟨H, hH, hF, hG⟩ := h
  exact (EP.lemma_11_2_6_push d.F hΦ d'.F hΦ' hH hF hG k).symm

/-- A refinement of a diagram of two equivalences is a diagram of two equivalences. -/
theorem IsRefinement.isEquivalence_Φ {d d' : Diagram X Y} (h : d'.IsRefinement d)
    (hΦ : d.Φ.IsEquivalence) : d'.Φ.IsEquivalence := by
  obtain ⟨H, hH, -, hG⟩ := h
  obtain ⟨τ⟩ := hG
  exact EpFunctor.IsEquivalence.of_natTrans τ (hΦ.comp hH)

/-- **Equivalent diagrams have the same push-forward** (2021 p. 532, after Definition
11.2.7). -/
theorem formsPush_eq_of_equiv {d d' : Diagram X Y} (h : Equiv d d') (hΦ : d.Φ.IsEquivalence)
    (hΦ' : d'.Φ.IsEquivalence) (k : ℕ) : d.formsPush hΦ k = d'.formsPush hΦ' k := by
  obtain ⟨d'', h₁, h₂⟩ := h
  rw [← formsPush_eq_of_isRefinement h₁ hΦ (h₁.isEquivalence_Φ hΦ),
    ← formsPush_eq_of_isRefinement h₂ hΦ' (h₁.isEquivalence_Φ hΦ)]

/-- `[d]^* ∘ [d]_* = 1` on a diagram of two equivalences. -/
theorem formsPullback_comp_formsPush (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) (k : ℕ) :
    (d.formsPullback k).comp (d.formsPush hΦ k) = LinearMap.id := by
  refine LinearMap.ext fun a => ?_
  simp only [formsPullback, formsPush, LinearMap.comp_apply, LinearMap.id_apply]
  rw [EP.epFormsInftyPullback_epFormsInftyPush, EP.epFormsInftyPush_epFormsInftyPullback]

/-- `[d]_* ∘ [d]^* = 1` on a diagram of two equivalences. -/
theorem formsPush_comp_formsPullback (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) (k : ℕ) :
    (d.formsPush hΦ k).comp (d.formsPullback k) = LinearMap.id := by
  refine LinearMap.ext fun a => ?_
  simp only [formsPullback, formsPush, LinearMap.comp_apply, LinearMap.id_apply]
  rw [EP.epFormsInftyPullback_epFormsInftyPush, EP.epFormsInftyPush_epFormsInftyPullback]

/-- `d_X ∘ (F_* Φ^*) = (F_* Φ^*) ∘ d_Y`. -/
theorem epFormsInftyD_comp_formsPullback (d : Diagram X Y) (k : ℕ) :
    (X.epFormsInftyD k).comp (d.formsPullback k) =
      (d.formsPullback (k + 1)).comp (Y.epFormsInftyD k) := by
  rw [formsPullback, ← LinearMap.comp_assoc, EP.epFormsInftyD_comp_epFormsInftyPush,
    LinearMap.comp_assoc, EP.epFormsInftyD_comp_epFormsInftyPullback, ← LinearMap.comp_assoc]
  rfl

/-- `d_Y ∘ (Φ_* F^*) = (Φ_* F^*) ∘ d_X`. -/
theorem epFormsInftyD_comp_formsPush (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) (k : ℕ) :
    (Y.epFormsInftyD k).comp (d.formsPush hΦ k) =
      (d.formsPush hΦ (k + 1)).comp (X.epFormsInftyD k) :=
  (d.symm hΦ).epFormsInftyD_comp_formsPullback k

/-- The push-forward by the identity functor is the identity. -/
theorem _root_.Polyfold.EP.epFormsInftyPush_id (X : EP.{u}) (k : ℕ) :
    EP.epFormsInftyPush (EpFunctor.IsEquivalence.id X.X) k = LinearMap.id :=
  (EP.epFormsInftyPush_eq_of_comp_eq_id _ k (by
    rw [EP.epFormsInftyPullback_id, LinearMap.id_comp])).symm

/-- The pull-back of the identity diagram is the identity. -/
theorem formsPullback_id (X : EP.{u}) (k : ℕ) : (id X).formsPullback k = LinearMap.id := by
  change (EP.epFormsInftyPush (EpFunctor.IsEquivalence.id X.X) k).comp
    (EP.epFormsInftyPullback (EpFunctor.id X.X) k) = _
  rw [EP.epFormsInftyPush_id, EP.epFormsInftyPullback_id, LinearMap.id_comp]

/-- For an sc-smooth functor `Φ : X → Y`, the pull-back of the diagram `X ←1 X →Φ Y` is
`Φ^*`. -/
theorem formsPullback_ofFunctor (Φ : X ⟶ Y) (k : ℕ) :
    (ofFunctor Φ).formsPullback k = EP.epFormsInftyPullback Φ k := by
  change (EP.epFormsInftyPush (EpFunctor.IsEquivalence.id X.X) k).comp
    (EP.epFormsInftyPullback Φ k) = _
  rw [EP.epFormsInftyPush_id, LinearMap.id_comp]

/-- **Base change**: for `Φ : A → Y`, an equivalence `G : B → Y` and `A ←π_A W →π_B B` with
`π_A` an equivalence and `Φ ∘ π_A ≃ G ∘ π_B`: `(π_A)_* (π_B)^* = Φ^* G_*`. -/
theorem _root_.Polyfold.EP.epFormsInftyPush_epFormsInftyPullback_of_square
    {Y A B W : EP.{u}} (Φ : EpFunctor A.X Y.X) {G : EpFunctor B.X Y.X} (hG : G.IsEquivalence)
    {πL : EpFunctor W.X A.X} (hL : πL.IsEquivalence) (πR : EpFunctor W.X B.X)
    (hnat : (Φ.comp πL).NaturallyEquivalent (G.comp πR)) (k : ℕ) (a : B.epFormsInfty k) :
    EP.epFormsInftyPush hL k (EP.epFormsInftyPullback πR k a) =
      EP.epFormsInftyPullback Φ k (EP.epFormsInftyPush hG k a) := by
  have h : (EP.epFormsInftyPullback πL k).comp (EP.epFormsInftyPullback Φ k) =
      (EP.epFormsInftyPullback πR k).comp (EP.epFormsInftyPullback G k) :=
    (EP.epFormsInftyPullback_comp πL k Φ).symm.trans
      ((EP.epFormsInftyPullback_eq_of_natTrans k hnat).trans
        (EP.epFormsInftyPullback_comp πR k G))
  have h1 : EP.epFormsInftyPullback πL k
      (EP.epFormsInftyPullback Φ k (EP.epFormsInftyPush hG k a)) =
      EP.epFormsInftyPullback πR k
        (EP.epFormsInftyPullback G k (EP.epFormsInftyPush hG k a)) :=
    LinearMap.congr_fun h (EP.epFormsInftyPush hG k a)
  have h2 : EP.epFormsInftyPullback G k (EP.epFormsInftyPush hG k a) = a :=
    EP.epFormsInftyPullback_epFormsInftyPush hG k a
  have h3 := EP.epFormsInftyPush_epFormsInftyPullback hL k
    (EP.epFormsInftyPullback Φ k (EP.epFormsInftyPush hG k a))
  exact (congrArg (EP.epFormsInftyPush hL k)
    ((congrArg (EP.epFormsInftyPullback πR k) h2).symm.trans h1.symm)).trans h3

/-- For `X ←F A →Φ Y`, `Y ←G B →Ψ Z` and `A ←π_A W →π_B B` with `π_A` an equivalence and
`Φ ∘ π_A ≃ G ∘ π_B`: `(F ∘ π_A)_* (Ψ ∘ π_B)^* = (F_* Φ^*) ∘ (G_* Ψ^*)`. -/
theorem _root_.Polyfold.EP.epFormsInftyPush_comp_epFormsInftyPullback_of_square
    {X Y Z A B W : EP.{u}} {F : EpFunctor A.X X.X} (hF : F.IsEquivalence)
    (Φ : EpFunctor A.X Y.X) {G : EpFunctor B.X Y.X} (hG : G.IsEquivalence)
    (Ψ : EpFunctor B.X Z.X) {πL : EpFunctor W.X A.X} (hL : πL.IsEquivalence)
    (πR : EpFunctor W.X B.X) (hnat : (Φ.comp πL).NaturallyEquivalent (G.comp πR))
    (hFL : (F.comp πL).IsEquivalence) (k : ℕ) :
    (EP.epFormsInftyPush hFL k).comp (EP.epFormsInftyPullback (Ψ.comp πR) k) =
      ((EP.epFormsInftyPush hF k).comp (EP.epFormsInftyPullback Φ k)).comp
        ((EP.epFormsInftyPush hG k).comp (EP.epFormsInftyPullback Ψ k)) := by
  refine LinearMap.ext fun a => ?_
  have e1 : EP.epFormsInftyPush hFL k (EP.epFormsInftyPullback (Ψ.comp πR) k a) =
      EP.epFormsInftyPush hF k (EP.epFormsInftyPush hL k (EP.epFormsInftyPullback πR k
        (EP.epFormsInftyPullback Ψ k a))) :=
    (LinearMap.congr_fun (EP.lemma_11_2_4_two hL k hF hFL) _).trans
      (congrArg (fun b => EP.epFormsInftyPush hF k (EP.epFormsInftyPush hL k b))
        (LinearMap.congr_fun (EP.epFormsInftyPullback_comp πR k Ψ) a))
  exact e1.trans (congrArg (EP.epFormsInftyPush hF k)
    (EP.epFormsInftyPush_epFormsInftyPullback_of_square Φ hG hL πR hnat k
      (EP.epFormsInftyPullback Ψ k a)))

/-- **The pull-back of the composite diagram** `X ←(F∘π_A) A ×_Y B →(Ψ∘π_B) Z` of
`d : X ←F A →Φ Y` and `e : Y ←G B →Ψ Z` is `(F_* Φ^*) ∘ (G_* Ψ^*)`. -/
theorem formsPullback_comp (d : Diagram X Y) (e : Diagram Y Z) (k : ℕ) :
    (d.comp e).formsPullback k = (d.formsPullback k).comp (e.formsPullback k) :=
  EP.epFormsInftyPush_comp_epFormsInftyPullback_of_square (W := wfp d.Φ e.F (d.admissible e))
    d.isEquivalence_F d.Φ e.isEquivalence_F e.Φ
    (isEquivalence_projLeft e.isEquivalence_F (d.admissible e))
    (projRight d.Φ e.F (d.admissible e)) (naturallyEquivalent (d.admissible e))
    (d.comp e).isEquivalence_F k

end Diagram

namespace EPLoc

variable {X Y Z : EP.{u}}

/-- **2021 Definition 11.2.7, p. 532 (2017: Definition 11.3): the pull-back
`f^* : Ωᵏ_{ep,∞}(Y) → Ωᵏ_{ep,∞}(X)`** of sc-differential forms by a generalized map
`f : X → Y`; it is `F_* ∘ Φ^*` for every diagram `X ←F A →Φ Y` representing `f`
(`formsPullback_homMk`). -/
def formsPullback (f : of X ⟶ of Y) (k : ℕ) : Y.epFormsInfty k →ₗ[ℝ] X.epFormsInfty k :=
  Quotient.lift (fun d : Diagram X Y => d.formsPullback k)
    (fun _ _ h => Diagram.formsPullback_eq_of_equiv h k) f

@[simp] theorem formsPullback_homMk (d : Diagram X Y) (k : ℕ) :
    formsPullback (homMk d) k = d.formsPullback k := rfl

/-- `1^* = 1`. -/
theorem formsPullback_id (X : EP.{u}) (k : ℕ) : formsPullback (𝟙 (of X)) k = LinearMap.id :=
  Diagram.formsPullback_id X k

/-- **`(g ∘ f)^* = f^* ∘ g^*`** for generalized maps `f : X → Y`, `g : Y → Z`. -/
theorem formsPullback_comp (f : of X ⟶ of Y) (g : of Y ⟶ of Z) (k : ℕ) :
    formsPullback (f ≫ g) k = (formsPullback f k).comp (formsPullback g k) := by
  obtain ⟨d, rfl⟩ := homMk_surjective f
  obtain ⟨e, rfl⟩ := homMk_surjective g
  exact Diagram.formsPullback_comp d e k

/-- For an sc-smooth functor `Φ : X → Y`, the pull-back along the generalized map `[d_Φ]` is
`Φ^*`. -/
theorem formsPullback_localizationFunctor_map (Φ : X ⟶ Y) (k : ℕ) :
    formsPullback (localizationFunctor.map Φ) k = EP.epFormsInftyPullback Φ k :=
  Diagram.formsPullback_ofFunctor Φ k

/-- **2021 Definition 11.2.7, p. 532 (2017: Definition 11.3): the push-forward
`f_* : Ωᵏ_{ep,∞}(X) → Ωᵏ_{ep,∞}(Y)`** of sc-differential forms by a generalized isomorphism
`f : X → Y` (Definition 10.3.9), the pull-back by its inverse; it is `Φ_* ∘ F^*` for every
diagram `X ←F A →Φ Y` representing `f` (`formsPush_homMk`). -/
def formsPush (f : of X ⟶ of Y) (hf : IsGeneralizedIso f) (k : ℕ) :
    X.epFormsInfty k →ₗ[ℝ] Y.epFormsInfty k :=
  formsPullback hf.choose k

/-- **The push-forward by `[X ←F A →Φ Y]` is `Φ_* ∘ F^*`** (the text's Definition 11.2.7),
for every diagram representing the generalized isomorphism. -/
theorem formsPush_homMk (d : Diagram X Y) (hf : IsGeneralizedIso (homMk d))
    (hΦ : d.Φ.IsEquivalence) (k : ℕ) : formsPush (homMk d) hf k = d.formsPush hΦ k := by
  have h := (theorem_10_3_10 d).2 hΦ hf.choose hf.choose_spec.1 hf.choose_spec.2
  rw [formsPush, h]
  rfl

/-- **2021 Theorem 11.2.1 (1), p. 526 (2017: Theorem 11.2)**: `d ∘ d = 0` on
`Ω*_{ep,∞}(X)` (Section 8.2). -/
theorem theorem_11_2_1_one (X : EP.{u}) (k : ℕ) :
    (X.epFormsInftyD (k + 1)).comp (X.epFormsInftyD k) = 0 :=
  X.epFormsInftyD_comp_epFormsInftyD k

/-- **2021 Theorem 11.2.1 (2), p. 526 (2017: Theorem 11.2)**: for a generalized sc-smooth map
`f : X → Y` the pull-back `f^* : Ω*_{ep,∞}(Y) → Ω*_{ep,∞}(X)` (well defined:
`formsPullback_homMk`) satisfies `d_X ∘ f^* = f^* ∘ d_Y`. -/
theorem theorem_11_2_1_two (f : of X ⟶ of Y) (k : ℕ) :
    (X.epFormsInftyD k).comp (formsPullback f k) =
      (formsPullback f (k + 1)).comp (Y.epFormsInftyD k) := by
  obtain ⟨d, rfl⟩ := homMk_surjective f
  exact d.epFormsInftyD_comp_formsPullback k

/-- **2021 Theorem 11.2.1 (3), p. 526 (2017: Theorem 11.2)**: for a generalized isomorphism
`h : X → Y` the push-forward `h_* : Ω*_{ep,∞}(X) → Ω*_{ep,∞}(Y)` (well defined:
`formsPush_homMk`) satisfies `h_* ∘ d_X = d_Y ∘ h_*`, `h_* ∘ h^* = 1` and `h^* ∘ h_* = 1`. -/
theorem theorem_11_2_1_three (h : of X ⟶ of Y) (hh : IsGeneralizedIso h) (k : ℕ) :
    (formsPush h hh (k + 1)).comp (X.epFormsInftyD k) =
        (Y.epFormsInftyD k).comp (formsPush h hh k) ∧
      (formsPush h hh k).comp (formsPullback h k) = LinearMap.id ∧
      (formsPullback h k).comp (formsPush h hh k) = LinearMap.id := by
  refine ⟨(theorem_11_2_1_two hh.choose k).symm, ?_, ?_⟩
  · rw [formsPush, ← formsPullback_comp, hh.choose_spec.2]
    exact formsPullback_id Y k
  · rw [formsPush, ← formsPullback_comp, hh.choose_spec.1]
    exact formsPullback_id X k

end EPLoc

end EPLocalization

end Polyfold
