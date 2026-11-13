import Polyfold.Chapter16.P3H_TangentLemma
import Polyfold.Chapter16.P3H_PolyfoldForms
import Polyfold.Chapter8.TangentZhouReflect2021
import Polyfold.Chapter8.TangentOrbit

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.2, pp. 716–719: the **tangent of a polyfold**, the maps `Tα` with (16.5), **Lemma 16.2.2** and
**Definition 16.2.3** (2017: §16.2, Lemma 16.4, Definition 16.14).  Numbers and pages are the 2021
text's.

## The text, paraphrased

For `(X, α) ∈ c` the tangent space `T(Z, c)` is glued from the classes `[(z, (X, α), h)]`,
`h ∈ T_x X`, `α(|x|) = z`, by canonical bijections; `Tα : |TX| → T(Z, c)` is a bijection and
`Tβ ∘ |Tf| = Tα` (16.5) for the generalized isomorphism `f : X → Y` with `β ∘ |f| = α`.  (Lemma
16.2.2) `T(Z, c)` has a unique topology for which every `Tα` is a homeomorphism; it is metrizable.
(Definition 16.2.3) `Tc` is the class of the polyfold structures `(TX, Tα)`; `(T(Z, c), Tc)` is a
polyfold, the tangent of `(Z, c)`.

## What is formalized

We take `T(Z, c) := |T X₀|` for the chosen structure `(X₀, α₀) = c.out` (`TangentSpace c`) and
`Tα := |T𝔣|` for a generalized isomorphism `𝔣 : X → X₀` with `α₀ ∘ |𝔣| = α`
(`PolyfoldClass.tangentMap`).  `Tα` does not depend on `𝔣`: although `𝔣` itself need not be unique
(Lemma 16.2.1 does not hold as we read it, `not_lemma_16_2_1`), `|T𝔣|` depends only on `|𝔣|`
(`EPLoc.orbitMap_tangentHom_eq`; (ZHOU) ⇒ (LR)).  This is the gluing of the text with `X₀` as the
base point.
* **`tangentMap_comp`**: (16.5), `Tβ ∘ |Th| = Tα` for every `h : X → Y` with `β ∘ |h| = α`.
* **`PolyfoldStructure.metrizableSpace`**: a space with a polyfold structure is metrizable (the
  remark after Definition 16.1.1, gap G.146).
* **`lemma_16_2_2`**: every `Tα` is a homeomorphism, no other topology makes one of them a
  homeomorphism, and `T(Z, c)` is metrizable (Theorem 8.1.15's proof).
* **`tangentStructure q hq = (TX, Tα)`**, a polyfold structure on `T(Z, c)` (`|TX|` paracompact by
  Theorem 8.1.15, `TX` satisfies (ZHOU) by Proposition 8.1.16), **`PolyfoldClass.tangent c = Tc`**,
  **`definition_16_2_3`**: all `(TX, Tα)`, `(X, α) ∈ c`, are equivalent and lie in `Tc`.
* Not formalized: the projection `τ_Z : T(Z, c) → Z¹` (it needs the raised polyfold `(Z, c)¹`) and
  Theorem 16.2.4 (the tangent functor on sc-smooth maps of polyfolds).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization EPLocalization.EPLoc

namespace EPLocalization.EPLoc

variable {X Y : EP.{u}}

/-- The orbit map of a generalized isomorphism is a homeomorphism (Definition 10.1.1 (2) for a
representative diagram). -/
theorem isHomeomorph_orbitMap_of_isGeneralizedIso {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) :
    IsHomeomorph (orbitMap f) := by
  obtain ⟨d, rfl, hΦ⟩ := exists_diagram_of_isGeneralizedIso hf
  exact d.isHomeomorph_orbitMap hΦ

end EPLocalization.EPLoc

namespace PolyfoldStructure

variable {Z : Type u} [TopologicalSpace Z]

/-- `|TX|` is paracompact (Theorem 8.1.15). -/
theorem tangent_paracompact (p : PolyfoldStructure Z) :
    p.X.tangentAny.X.HasParacompactOrbitSpace :=
  p.X.X.theorem_8_1_15 p.paracompact

/-- **Polyfolds are metrizable** (2021 p. 706, the remark after Definition 16.1.1; 2017:
Proposition 16.1): `|X|` is paracompact, regular, Hausdorff and locally metrizable, hence
metrizable (Theorem 7.3.1, `theorem_7_3_1_metrizable`, by Part I's metrization theorem
`metrizableSpace_of_pullback`), and `β : |X| ≃ₜ Z`. -/
theorem metrizableSpace (p : PolyfoldStructure Z) : TopologicalSpace.MetrizableSpace Z :=
  have := p.X.X.theorem_7_3_1_metrizable p.paracompact
  p.β.symm.isEmbedding.metrizableSpace

/-- `TX` satisfies (ZHOU) (Proposition 8.1.16). -/
theorem tangent_isZhou (p : PolyfoldStructure Z) : p.X.tangentAny.X.IsZhou :=
  p.X.X.proposition_8_1_16_2021 p.isZhou

end PolyfoldStructure

namespace PolyfoldClass

variable {Z : Type u} [TopologicalSpace Z] {c : PolyfoldClass Z}

/-- **The tangent space `T(Z, c)`** (2021 p. 717), as `|T X₀|` for `(X₀, α₀) = c.out`. -/
def TangentSpace (c : PolyfoldClass Z) : Type (max u 1) := c.out.X.tangentAny.X.OrbitSpace

instance tangentSpaceTopology (c : PolyfoldClass Z) : TopologicalSpace (TangentSpace c) :=
  inferInstanceAs (TopologicalSpace c.out.X.tangentAny.X.OrbitSpace)

/-- **`Tα : |TX| → T(Z, c)`** (2021 p. 717, (16.4)) for `(X, α) ∈ c`: `|T𝔣|` for a generalized
isomorphism `𝔣 : X → X₀` with `α₀ ∘ |𝔣| = α`. -/
def tangentMap (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    q.X.tangentAny.X.OrbitSpace → TangentSpace c :=
  orbitMap (tangentHom (ScForm.exists_iso hq (Quotient.out_eq c)).choose)

/-- `Tα = |T𝔣|` for every `𝔣 : X → X₀` with `α₀ ∘ |𝔣| = α`. -/
theorem tangentMap_eq (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c)
    {𝔣 : EPLoc.of q.X ⟶ EPLoc.of c.out.X} (h𝔣 : IsGeneralizedIso 𝔣)
    (hβ : ⇑q.β = ⇑c.out.β ∘ orbitMap 𝔣) : tangentMap q hq = orbitMap (tangentHom 𝔣) := by
  have h := (ScForm.exists_iso hq (Quotient.out_eq c)).choose_spec
  exact orbitMap_tangentHom_eq (Or.inl q.isLR) h.1 h𝔣
    ((PolyfoldStructure.orbitMap_eq_of_equiv h.2).trans
      (PolyfoldStructure.orbitMap_eq_of_equiv hβ).symm)

/-- **(16.5), 2021 p. 718**: `Tβ ∘ |Th| = Tα` for every generalized isomorphism `h : X → Y` with
`β ∘ |h| = α`. -/
theorem tangentMap_comp {p q : PolyfoldStructure Z} (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (hq : (⟦q⟧ : PolyfoldClass Z) = c) {h : EPLoc.of p.X ⟶ EPLoc.of q.X}
    (hh : IsGeneralizedIso h) (hβ : ⇑p.β = ⇑q.β ∘ orbitMap h) :
    tangentMap q hq ∘ orbitMap (tangentHom h) = tangentMap p hp := by
  obtain ⟨𝔣, h𝔣, hβ𝔣⟩ := ScForm.exists_iso hq (Quotient.out_eq c)
  rw [tangentMap_eq q hq h𝔣 hβ𝔣,
    tangentMap_eq p hp (isGeneralizedIso_comp hh h𝔣)
      (by rw [hβ, hβ𝔣, proposition_10_3_11]; rfl),
    tangentHom_comp, proposition_10_3_11]
  rfl

/-- `Tα` is a homeomorphism. -/
theorem isHomeomorph_tangentMap (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    IsHomeomorph (tangentMap q hq) :=
  isHomeomorph_orbitMap_of_isGeneralizedIso
    (isGeneralizedIso_tangentHom (ScForm.exists_iso hq (Quotient.out_eq c)).choose_spec.1)

/-- `Tα` as a homeomorphism `|TX| ≃ₜ T(Z, c)`. -/
def tangentHomeomorph (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    q.X.tangentAny.X.OrbitSpace ≃ₜ TangentSpace c :=
  (isHomeomorph_tangentMap q hq).homeomorph

@[simp] theorem tangentHomeomorph_apply (q : PolyfoldStructure Z)
    (hq : (⟦q⟧ : PolyfoldClass Z) = c) (v : q.X.tangentAny.X.OrbitSpace) :
    tangentHomeomorph q hq v = tangentMap q hq v :=
  rfl

/-- **2021 Lemma 16.2.2, p. 718 (2017: Lemma 16.4)**: `T(Z, c)` has a unique topology for which
the maps `Tα : |TX| → T(Z, c)`, `(X, α) ∈ c`, are homeomorphisms (every `Tα` is one for the
topology of `TangentSpace c`, and a topology for which one `Tα` is a homeomorphism is this one);
it is metrizable. -/
theorem lemma_16_2_2 (c : PolyfoldClass Z) :
    (∀ (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c),
      IsHomeomorph (tangentMap q hq)) ∧
    (∀ t : TopologicalSpace (TangentSpace c),
      (∃ (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c),
        @IsHomeomorph _ _ _ t (tangentMap q hq)) →
      t = tangentSpaceTopology c) ∧
    TopologicalSpace.MetrizableSpace (TangentSpace c) := by
  refine ⟨isHomeomorph_tangentMap, fun t ⟨q, hq, ht⟩ => ?_, ?_⟩
  · have h₂ := isHomeomorph_tangentMap q hq
    ext s
    have key : ∀ t' : TopologicalSpace (TangentSpace c),
        @IsHomeomorph _ _ _ t' (tangentMap q hq) →
          (IsOpen[t'] s ↔ IsOpen (tangentMap q hq ⁻¹' s)) := fun t' h => by
      refine ⟨fun hs => h.continuous.isOpen_preimage s hs, fun hs => ?_⟩
      have := h.isOpenMap _ hs
      rwa [Set.image_preimage_eq s h.bijective.2] at this
    exact (key t ht).trans (key (tangentSpaceTopology c) h₂).symm
  · exact c.out.X.X.metrizableSpace_tangent_orbitSpace c.out.paracompact

/-- **The polyfold structure `(TX, Tα)` on `T(Z, c)`** (2021 p. 718). -/
def tangentStructure (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    PolyfoldStructure (TangentSpace c) where
  X := q.X.tangentAny
  paracompact := q.tangent_paracompact
  isZhou := q.tangent_isZhou
  β := tangentHomeomorph q hq

/-- `(TX, Tα)` and `(TY, Tβ)` are equivalent, via `Th` for `h : X → Y` with `β ∘ |h| = α`
(2021 p. 718). -/
theorem tangentStructure_equiv {p q : PolyfoldStructure Z} (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    PolyfoldStructure.Equiv (tangentStructure p hp) (tangentStructure q hq) := by
  obtain ⟨h, hh, hβ⟩ := ScForm.exists_iso hp hq
  exact ⟨tangentHom h, isGeneralizedIso_tangentHom hh, (tangentMap_comp hp hq hh hβ).symm⟩

/-- **2021 Definition 16.2.3, p. 719 (2017: Definition 16.14)**: the tangent `Tc` of the polyfold
`(Z, c)`, the class of the structures `(TX, Tα)` on `T(Z, c)`. -/
def tangent (c : PolyfoldClass Z) : PolyfoldClass (TangentSpace c) :=
  ⟦tangentStructure c.out (Quotient.out_eq c)⟧

/-- **Definition 16.2.3 is well posed**: for every `(X, α) ∈ c`, `(TX, Tα) ∈ Tc`. -/
theorem definition_16_2_3 (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    (⟦tangentStructure q hq⟧ : PolyfoldClass (TangentSpace c)) = c.tangent :=
  Quotient.sound (tangentStructure_equiv hq (Quotient.out_eq c))

/-- Witness: the tangent of `[ℤ/3 ⋉ ℝ]` (Definition 16.2.3 is not vacuous). -/
example : PolyfoldClass (TangentSpace PolyfoldStructure.z3Polyfold) :=
  PolyfoldStructure.z3Polyfold.tangent

end PolyfoldClass

end Polyfold
