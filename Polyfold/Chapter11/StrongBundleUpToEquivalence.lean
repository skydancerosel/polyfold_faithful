import Polyfold.Chapter10.StrongBundleLocalizationSections
import Polyfold.Chapter8.Book2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.5 "Strong Bundles up to Equivalence" (pp. 546–548; 2017: pp. 399–401):
**Proposition 11.5.1** (2017: Proposition 11.6), the construction before **Lemma 11.5.2** (2017:
Lemma 11.7) and **Proposition 11.5.3** (2017: Proposition 11.7).  Numbers and pages are the 2021
text's, the 2017 ones in parentheses.

# Auxiliary norms and multisection functors under generalized strong bundle isomorphisms

## The text, paraphrased

(p. 546) The section recalls Theorem 10.5.4 (formalized in Chapter 10 as
`GenSBMap.theorem_10_5_4`).  (Proposition 11.5.1, p. 547) For a generalized strong bundle
isomorphism `[D] : W → W'` and an auxiliary norm `N'` of `(P', μ')` (Definition 8.3.5) there is a
well-defined pull-back `N = [D]^* N'`, an auxiliary norm, and a push-forward `[D]_* N`, with
`[D]^* [D]_* N = N`, `[D]_* [D]^* N' = N'`; both depend only on `|[D]|`.  *Proof*: for a
representative `W ←Φ W'' →Ψ W'` and `e ∈ W_{0,1}` pick `e'' ∈ W''_{0,1}` and `Φ(e'') → e`, and set
`N(e) = N'(Ψ(e''))`; independent of the choices since `N'` is a functor.  (pp. 547–548) For an
equivalence `Φ : W → W'` the pull-back of an sc⁺-multisection is `Φ^*Λ' = Λ' ∘ Φ`; the
push-forward is `Φ_*Λ(w') = Λ(w)` for a morphism `Φ(w) → w'`, independent of the choices.
(Lemma 11.5.2) `Φ_*Λ` is a functor.  The local section structures are carried along `Φ`;
`Φ^* ∘ Φ_* Λ = Λ`; `[D]_*Λ = Ψ_* ∘ Φ^* Λ`, independent of the diagram.  (Proposition 11.5.3)
Push-forward and pull-back of sc⁺-multisections are well defined, mutually inverse, and equal for
`[D]`, `[D']` with `|[D]| = |[D']|`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* Multisection functors: `IsWFunctor A Λ` (`Λ(μ(φ, w)) = Λ(w)`: a functor `W → α`, the functor
  part of 2021 Definition 13.2.1 with `α = ℚ⁺`), `IsWFunctor.eq_of_π_eq`, witness
  `isWFunctor_const`.  Along a strong bundle functor `Ψ`: `pullMult` (`Ψ^*`); along a strong
  bundle equivalence `Φ`: `pushMult` (`Φ_*`), `pushMult_eq` (independence of the choices),
  **Lemma 11.5.2** (`lemma_11_5_2`), `pullMult_pushMult` (`Φ^* Φ_* Λ = Λ`), `pushMult_pullMult`.
  Diagrams: `SDiagram.pushMult` (`Ψ_* Φ^*`), `SDiagram.pullMult` (`Φ_* Ψ^*`), `pushMult_eq`,
  `pullMult_eq`, inverses, `pushMult_eq_of_orbitMap_eq`, `pullMult_eq_of_orbitMap_eq`; classes:
  `GenSBMap.pushMult`, `GenSBMap.pullMult`; **Proposition 11.5.3** (`GenSBMap.proposition_11_5_3`).
* Auxiliary norms: `IsOneInvariant` (condition (3) of Definition 8.3.5, `isOneInvariant_iff`;
  `EpStrongBundle.IsAuxNorm.isOneInvariant`; witness `isOneInvariant_const`); `oneToOrbit`
  (`|W[1]| → |W|`, injective), `oneMap` (`|Ψ| : |W[1]| → |W'[1]|`), `SDiagram.oneOrbitMap`
  (`|D|` on `|W[1]|`, determined by `|D|`); `SDiagram.pullNorm` (`N(e) = N'(Ψ(e''))`,
  `pullNorm_eq_Ψ`), `SDiagram.pushNorm`; `GenSBMap.pullNorm`, `GenSBMap.pushNorm`;
  **Proposition 11.5.1** (`GenSBMap.proposition_11_5_1`): well defined, continuity and (3) of
  Definition 8.3.5 preserved, mutually inverse, dependence on `|[D]|` only.

## What the text leaves implicit, and the choices made

* **Choices.**  `pushMult` uses the choice of `w` and `Φ(w) → w'` given by essential surjectivity;
  `pullNorm` uses a representative `Quotient.out` of `|D|(|e|) ∈ |W'[1]|`, which is the text's
  `Ψ(e'')` for `Φ(e'') → e` up to isomorphism (`pullNorm_eq_Ψ`).  Both are independent of the
  choices on functors (`pushMult_eq`, `pullNorm_eq`).
* **`|D|` on `W[1]`.**  It is `|Ψ| ∘ |Φ|⁻¹` with `|Φ| : |W''[1]| → |W[1]|` the homeomorphism of
  Definition 10.4.1 (1); since `|W[1]| → |W|` is injective, it is determined by `|[D]|`, which
  gives the last assertion of Proposition 11.5.1.
* **Not formalized**: conditions (1) (a complete norm on each fibre) and (2) (`P(h_k) → x`,
  `N(h_k) → 0` ⇒ `h_k → 0_x`) of Definition 8.3.5 for `[D]^* N'` and `[D]_* N` (they need the
  level-`1` fibre maps of `μ` and of a strong bundle equivalence as linear bijections, and the
  level-`1` local homeomorphism property of `Φ` near the zero section); and the local section
  structures of sc⁺-multisections (Definition 13.2.1 is not in the repository, and their
  transport needs the strong-bundle form of the natural representation transport of
  Proposition 10.1.9).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v

namespace SBLocalization

open EPLocalization

variable {A A' : SEP.{u}} {α : Type v}

/-! ### Multisection functors -/

/-- **A functor `Λ : W → α`** on the total ep-groupoid `(W, 𝐖)`: `Λ(μ(φ, w)) = Λ(w)` (2021
Definition 13.2.1, the functor part, for `α = ℚ⁺`; p. 547). -/
def IsWFunctor (A : SEP.{u}) (Λ : A.W → α) : Prop :=
  ∀ q : pullbackSpace A.P A.X.src, Λ (A.E.μ q) = Λ (q : A.Mor × A.W).2

/-- Constant functions are functors (the definition is satisfiable). -/
theorem isWFunctor_const (A : SEP.{u}) (a : α) : IsWFunctor A fun _ : A.W => a :=
  fun _ => rfl

theorem IsWFunctor.eq_of_π_eq {Λ : A.W → α} (h : IsWFunctor A Λ) {a b : A.W}
    (hab : A.E.toEpGroupoid.π a = A.E.toEpGroupoid.π b) : Λ a = Λ b := by
  obtain ⟨q, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hab
  have hs' : (q : A.Mor × A.W).2 = a := hs
  have ht' : A.E.μ q = b := ht
  rw [← hs', ← ht', h q]

/-- **The pull-back `Ψ^*Λ' = Λ' ∘ Ψ`** along a strong bundle functor (p. 547). -/
def pullMult (Ψ : A ⟶ A') (Λ' : A'.W → α) : A.W → α := Λ' ∘ (SEP.Hom.Φ Ψ).obj

theorem IsWFunctor.pullMult {Λ' : A'.W → α} (h : IsWFunctor A' Λ') (Ψ : A ⟶ A') :
    IsWFunctor A (SBLocalization.pullMult Ψ Λ') := fun q => by
  refine h.eq_of_π_eq ?_
  change A'.E.toEpGroupoid.π ((SEP.Hom.Φ Ψ).obj (A.E.toEpGroupoid.tgt q)) =
    A'.E.toEpGroupoid.π ((SEP.Hom.Φ Ψ).obj (A.E.toEpGroupoid.src q))
  rw [← GroupoidFunctor.orbitMap_π, ← GroupoidFunctor.orbitMap_π,
    ← A.E.toEpGroupoid.π_src_eq_π_tgt q]

/-- **The push-forward `Φ_*Λ(w') = Λ(w)`** along a strong bundle equivalence, for the chosen `w`
and morphism `Φ(w) → w'` (p. 547). -/
def pushMult (Φ : A ⟶ A') (hΦ : SEP.equivalences Φ) (Λ : A.W → α) : A'.W → α :=
  fun w' => Λ ((sbe hΦ).isEquivalence.exists_iso w').choose

theorem π_obj_choose {Φ : A ⟶ A'} (hΦ : SEP.equivalences Φ) (w' : A'.W) :
    A'.E.toEpGroupoid.π ((SEP.Hom.Φ Φ).obj ((sbe hΦ).isEquivalence.exists_iso w').choose) =
      A'.E.toEpGroupoid.π w' := by
  obtain ⟨ψ, hs, ht⟩ := ((sbe hΦ).isEquivalence.exists_iso w').choose_spec
  exact (GroupoidStr.π_eq_π_iff _).2 ⟨ψ, hs, ht⟩

/-- **`Φ_*Λ` does not depend on the choices** (p. 547): `Φ_*Λ(w') = Λ(w)` whenever `Φ(w) ≅ w'`. -/
theorem pushMult_eq {Φ : A ⟶ A'} (hΦ : SEP.equivalences Φ) {Λ : A.W → α} (hΛ : IsWFunctor A Λ)
    {w : A.W} {w' : A'.W}
    (h : A'.E.toEpGroupoid.π ((SEP.Hom.Φ Φ).obj w) = A'.E.toEpGroupoid.π w') :
    pushMult Φ hΦ Λ w' = Λ w := by
  refine hΛ.eq_of_π_eq ((sbe hΦ).isEquivalence.isHomeomorph_orbitMap.injective ?_)
  rw [GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π, π_obj_choose hΦ w', h]

/-- **2021 Lemma 11.5.2, p. 548 (2017: Lemma 11.7, p. 400)**: `Φ_*Λ` is a functor. -/
theorem lemma_11_5_2 {Φ : A ⟶ A'} (hΦ : SEP.equivalences Φ) {Λ : A.W → α}
    (hΛ : IsWFunctor A Λ) : IsWFunctor A' (pushMult Φ hΦ Λ) := fun q' => by
  set w := ((sbe hΦ).isEquivalence.exists_iso (q' : A'.Mor × A'.W).2).choose
  have hw := π_obj_choose hΦ (q' : A'.Mor × A'.W).2
  have e : pushMult Φ hΦ Λ (A'.E.μ q') = Λ w :=
    pushMult_eq hΦ hΛ (hw.trans (A'.E.toEpGroupoid.π_src_eq_π_tgt q'))
  rw [e]
  rfl

/-- **`Φ^* ∘ Φ_* Λ = Λ`** (p. 548, "by construction"). -/
theorem pullMult_pushMult {Φ : A ⟶ A'} (hΦ : SEP.equivalences Φ) {Λ : A.W → α}
    (hΛ : IsWFunctor A Λ) : pullMult Φ (pushMult Φ hΦ Λ) = Λ :=
  funext fun _ => pushMult_eq hΦ hΛ rfl

/-- `Φ_* ∘ Φ^* Λ' = Λ'`. -/
theorem pushMult_pullMult {Φ : A ⟶ A'} (hΦ : SEP.equivalences Φ) {Λ' : A'.W → α}
    (hΛ' : IsWFunctor A' Λ') : pushMult Φ hΦ (pullMult Φ Λ') = Λ' :=
  funext fun w' => hΛ'.eq_of_π_eq (π_obj_choose hΦ w')

namespace SDiagram

variable (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)

/-- **`[D]_*Λ = Ψ_* ∘ Φ^* Λ`** (p. 548) for a diagram whose `Ψ` is a strong bundle equivalence. -/
def pushMult (Λ : A.W → α) : A'.W → α :=
  SBLocalization.pushMult D.Ψ hΨ (SBLocalization.pullMult D.Φ Λ)

/-- **`[D]^*Λ' = Φ_* ∘ Ψ^* Λ'`**, the push-forward along the reversed diagram. -/
def pullMult (Λ' : A'.W → α) : A.W → α := (D.symm hΨ).pushMult D.isEquivalence_Φ Λ'

variable {D hΨ}

/-- `[D]_*Λ(w') = Λ(w)` whenever `|D|(|w|) = |w'|`. -/
theorem pushMult_eq {Λ : A.W → α} (hΛ : IsWFunctor A Λ) {w : A.W} {w' : A'.W}
    (h : D.orbitMap (A.E.toEpGroupoid.π w) = A'.E.toEpGroupoid.π w') :
    D.pushMult hΨ Λ w' = Λ w := by
  set w'' := ((sbe hΨ).isEquivalence.exists_iso w').choose
  change Λ ((SEP.Hom.Φ D.Φ).obj w'') = Λ w
  refine hΛ.eq_of_π_eq ((D.total.isHomeomorph_orbitMap (sbe hΨ).isEquivalence).injective ?_)
  change D.orbitMap _ = D.orbitMap _
  rw [h, ← GroupoidFunctor.orbitMap_π, D.orbitMap_orbitMap_Φ, GroupoidFunctor.orbitMap_π]
  exact π_obj_choose hΨ w'

/-- `[D]^*Λ'(w) = Λ'(w')` whenever `|D|(|w|) = |w'|`. -/
theorem pullMult_eq {Λ' : A'.W → α} (hΛ' : IsWFunctor A' Λ') {w : A.W} {w' : A'.W}
    (h : D.orbitMap (A.E.toEpGroupoid.π w) = A'.E.toEpGroupoid.π w') :
    D.pullMult hΨ Λ' w = Λ' w' :=
  SDiagram.pushMult_eq hΛ' (by rw [← h]; exact D.orbitMap_symm_orbitMap hΨ _)

theorem isWFunctor_pushMult {Λ : A.W → α} (hΛ : IsWFunctor A Λ) :
    IsWFunctor A' (D.pushMult hΨ Λ) :=
  lemma_11_5_2 hΨ (hΛ.pullMult D.Φ)

theorem isWFunctor_pullMult {Λ' : A'.W → α} (hΛ' : IsWFunctor A' Λ') :
    IsWFunctor A (D.pullMult hΨ Λ') :=
  (D.symm hΨ).isWFunctor_pushMult hΛ'

theorem pullMult_pushMult {Λ : A.W → α} (hΛ : IsWFunctor A Λ) :
    D.pullMult hΨ (D.pushMult hΨ Λ) = Λ := funext fun w => by
  obtain ⟨w', hw'⟩ := A'.E.toEpGroupoid.surjective_π (D.orbitMap (A.E.toEpGroupoid.π w))
  rw [pullMult_eq (isWFunctor_pushMult hΛ) hw'.symm, pushMult_eq hΛ hw'.symm]

theorem pushMult_pullMult {Λ' : A'.W → α} (hΛ' : IsWFunctor A' Λ') :
    D.pushMult hΨ (D.pullMult hΨ Λ') = Λ' := funext fun w' => by
  obtain ⟨q, hq⟩ := (D.total.isHomeomorph_orbitMap (sbe hΨ).isEquivalence).surjective
    (A'.E.toEpGroupoid.π w')
  obtain ⟨w, rfl⟩ := A.E.toEpGroupoid.surjective_π q
  rw [pushMult_eq (isWFunctor_pullMult hΛ') hq, pullMult_eq hΛ' hq]

/-- **`|D₁| = |D₂|` implies `[D₁]_* = [D₂]_*`** on functors. -/
theorem pushMult_eq_of_orbitMap_eq {D₁ D₂ : SDiagram A A'} (hΨ₁ : SEP.equivalences D₁.Ψ)
    (hΨ₂ : SEP.equivalences D₂.Ψ) (h : D₁.orbitMap = D₂.orbitMap) {Λ : A.W → α}
    (hΛ : IsWFunctor A Λ) : D₁.pushMult hΨ₁ Λ = D₂.pushMult hΨ₂ Λ := funext fun w' => by
  obtain ⟨q, hq⟩ := (D₁.total.isHomeomorph_orbitMap (sbe hΨ₁).isEquivalence).surjective
    (A'.E.toEpGroupoid.π w')
  obtain ⟨w, rfl⟩ := A.E.toEpGroupoid.surjective_π q
  have hq₂ : D₂.orbitMap (A.E.toEpGroupoid.π w) = A'.E.toEpGroupoid.π w' := by rw [← h]; exact hq
  rw [pushMult_eq hΛ hq, pushMult_eq hΛ hq₂]

/-- **`|D₁| = |D₂|` implies `[D₁]^* = [D₂]^*`** on functors. -/
theorem pullMult_eq_of_orbitMap_eq {D₁ D₂ : SDiagram A A'} (hΨ₁ : SEP.equivalences D₁.Ψ)
    (hΨ₂ : SEP.equivalences D₂.Ψ) (h : D₁.orbitMap = D₂.orbitMap) {Λ' : A'.W → α}
    (hΛ' : IsWFunctor A' Λ') : D₁.pullMult hΨ₁ Λ' = D₂.pullMult hΨ₂ Λ' := funext fun w => by
  obtain ⟨w', hw'⟩ := A'.E.toEpGroupoid.surjective_π (D₁.orbitMap (A.E.toEpGroupoid.π w))
  have hw₂ : D₂.orbitMap (A.E.toEpGroupoid.π w) = A'.E.toEpGroupoid.π w' := by
    rw [← h]; exact hw'.symm
  rw [pullMult_eq hΛ' hw'.symm, pullMult_eq hΛ' hw₂]

end SDiagram

namespace GenSBMap

variable {f : GenSBMap A A'} (hf : f.IsGeneralizedIso)

/-- **The push-forward `[D]_*Λ`** of a functor `Λ : W → α` along a generalized strong bundle
isomorphism, `Ψ_* Φ^* Λ` for a chosen representative (p. 548). -/
def pushMult (Λ : A.W → α) : A'.W → α := (rep hf).pushMult (isEquivalence_rep_Ψ hf) Λ

/-- **The pull-back `[D]^*Λ'`**, `Φ_* Ψ^* Λ'`. -/
def pullMult (Λ' : A'.W → α) : A.W → α := (rep hf).pullMult (isEquivalence_rep_Ψ hf) Λ'

/-- **2021 Proposition 11.5.3, p. 548 (2017: Proposition 11.7, p. 401)**, for the functors
`Λ : W → ℚ⁺` underlying sc⁺-multisections: for a generalized strong bundle isomorphism `[D]`,
* the push-forward `[D]_*Λ = Ψ_* Φ^* Λ` and the pull-back `[D]^*Λ' = Φ_* Ψ^* Λ'` do not depend on
  the representative `W ←Φ W'' →Ψ W'` (both legs strong bundle equivalences);
* they map functors to functors and are mutually inverse;
* if `[D']` is another generalized strong bundle isomorphism with `|[D]| = |[D']|`, the
  push-forwards and the pull-backs agree.
The local section structures (Definition 13.2.1) are not formalized. -/
theorem proposition_11_5_3 :
    (∀ (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ), D.cls = f →
      ∀ Λ : A.W → ℚ≥0, IsWFunctor A Λ → pushMult hf Λ = D.pushMult hΨ Λ) ∧
    (∀ (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ), D.cls = f →
      ∀ Λ' : A'.W → ℚ≥0, IsWFunctor A' Λ' → pullMult hf Λ' = D.pullMult hΨ Λ') ∧
    (∀ Λ : A.W → ℚ≥0, IsWFunctor A Λ → IsWFunctor A' (pushMult hf Λ) ∧
      pullMult hf (pushMult hf Λ) = Λ) ∧
    (∀ Λ' : A'.W → ℚ≥0, IsWFunctor A' Λ' → IsWFunctor A (pullMult hf Λ') ∧
      pushMult hf (pullMult hf Λ') = Λ') ∧
    (∀ {g : GenSBMap A A'} (hg : g.IsGeneralizedIso), f.orbitMap = g.orbitMap →
      (∀ Λ : A.W → ℚ≥0, IsWFunctor A Λ → pushMult hf Λ = pushMult hg Λ) ∧
      ∀ Λ' : A'.W → ℚ≥0, IsWFunctor A' Λ' → pullMult hf Λ' = pullMult hg Λ') := by
  have ho : ∀ {D : SDiagram A A'}, D.cls = f → (rep hf).orbitMap = D.orbitMap := fun hD => by
    rw [← orbitMap_cls, ← orbitMap_cls, cls_rep, hD]
  refine ⟨fun D hΨ hD Λ hΛ => SDiagram.pushMult_eq_of_orbitMap_eq _ hΨ (ho hD) hΛ,
    fun D hΨ hD Λ' hΛ' => SDiagram.pullMult_eq_of_orbitMap_eq _ hΨ (ho hD) hΛ',
    fun Λ hΛ => ⟨SDiagram.isWFunctor_pushMult hΛ, SDiagram.pullMult_pushMult hΛ⟩,
    fun Λ' hΛ' => ⟨SDiagram.isWFunctor_pullMult hΛ', SDiagram.pushMult_pullMult hΛ'⟩,
    fun hg hfg => ?_⟩
  have h : (rep hf).orbitMap = (rep hg).orbitMap := by
    rw [← orbitMap_cls, ← orbitMap_cls, cls_rep, cls_rep, hfg]
  exact ⟨fun Λ hΛ => SDiagram.pushMult_eq_of_orbitMap_eq _ _ h hΛ,
    fun Λ' hΛ' => SDiagram.pullMult_eq_of_orbitMap_eq _ _ h hΛ'⟩

end GenSBMap

/-! ### Auxiliary norms -/

/-- **Condition (3) of 2021 Definition 8.3.5** in orbit form: `N : W_{0,1} → ℝ` is constant on
the orbits of `(W, 𝐖)` (`isOneInvariant_iff`). -/
def IsOneInvariant (A : SEP.{u}) (N : A.B.One → ℝ) : Prop :=
  ∀ a b : A.B.One, A.E.toEpGroupoid.π (A.B.oneVal a) = A.E.toEpGroupoid.π (A.B.oneVal b) →
    N a = N b

/-- Constant functions are invariant (the definition is satisfiable). -/
theorem isOneInvariant_const (A : SEP.{u}) (c : ℝ) : IsOneInvariant A fun _ => c :=
  fun _ _ _ => rfl

/-- `IsOneInvariant` is condition (3) of Definition 8.3.5. -/
theorem isOneInvariant_iff {N : A.B.One → ℝ} :
    IsOneInvariant A N ↔ ∀ (h k : A.B.One) (φ : A.Mor) (hk : A.P (A.B.oneVal k) = A.X.src φ),
      A.B.oneVal h = A.E.μ ⟨(φ, A.B.oneVal k), hk⟩ → N h = N k := by
  constructor
  · intro hN h k φ hk hμ
    refine hN h k ?_
    rw [hμ, EpStrongBundle.π_μ]
  · intro hN a b hab
    obtain ⟨q, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hab
    have hs' : (q : A.Mor × A.W).2 = A.B.oneVal a := hs
    have ht' : A.E.μ q = A.B.oneVal b := ht
    have hk : A.P (A.B.oneVal a) = A.X.src (q : A.Mor × A.W).1 := by rw [← hs']; exact q.2
    refine (hN b a (q : A.Mor × A.W).1 hk ?_).symm
    rw [← ht']
    exact A.E.μ_congr (Prod.ext rfl hs')

/-- An auxiliary norm (Definition 8.3.5) is invariant. -/
theorem _root_.Polyfold.EpStrongBundle.IsAuxNorm.isOneInvariant {N : A.B.One → ℝ}
    (hN : A.E.IsAuxNorm N) : IsOneInvariant A N :=
  isOneInvariant_iff.2 hN.map_μ

/-- `|W[1]| → |W|`, `|e| ↦ |e|`. -/
def oneToOrbit (A : SEP.{u}) : A.E.OneOrbitSpace → A.E.toEpGroupoid.OrbitSpace :=
  Quotient.lift (fun a => A.E.toEpGroupoid.π (A.B.oneVal a)) fun _ _ h => Quotient.sound h

@[simp] theorem oneToOrbit_mk (a : A.B.One) :
    oneToOrbit A (Quotient.mk _ a) = A.E.toEpGroupoid.π (A.B.oneVal a) := rfl

/-- `|W[1]| → |W|` is injective (`𝐖[1]` consists of the morphisms of `𝐖` between points of
`W_{0,1}`). -/
theorem oneToOrbit_injective (A : SEP.{u}) : Injective (oneToOrbit A) := by
  intro p q h
  induction p using Quotient.inductionOn
  induction q using Quotient.inductionOn
  exact Quotient.sound ((GroupoidStr.π_eq_π_iff _).1 h)

theorem mk_eq_mk_of_π_eq {a b : A.B.One}
    (h : A.E.toEpGroupoid.π (A.B.oneVal a) = A.E.toEpGroupoid.π (A.B.oneVal b)) :
    (Quotient.mk A.E.oneOrbitSetoid a) = Quotient.mk _ b :=
  Quotient.sound ((GroupoidStr.π_eq_π_iff _).1 h)

/-- `|Ψ| : |W[1]| → |W'[1]|` for a strong bundle functor `Ψ`. -/
def oneMap (Ψ : A ⟶ A') : A.E.OneOrbitSpace → A'.E.OneOrbitSpace :=
  A.E.oneOrbitMap A'.E (SEP.Hom.Φ Ψ)
    (SEP.Hom.isStrongBundleFunctor Ψ).isStrongBundleMap_obj.mapsTo_oneSet

theorem continuous_oneMap (Ψ : A ⟶ A') : Continuous (oneMap Ψ) :=
  EpStrongBundle.continuous_oneOrbitMap (continuousOn_univ.1
    (SEP.Hom.isStrongBundleFunctor Ψ).isStrongBundleMap_obj.isScSmoothMap_one.continuousOn)

theorem oneToOrbit_oneMap (Ψ : A ⟶ A') (q : A.E.OneOrbitSpace) :
    oneToOrbit A' (oneMap Ψ q) = (SEP.Hom.Φ Ψ).orbitMap (oneToOrbit A q) := by
  induction q using Quotient.inductionOn
  rfl

namespace SDiagram

variable (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)

/-- **`|D| : |W[1]| → |W'[1]|`**, `|Ψ| ∘ |Φ|⁻¹` with the homeomorphism `|Φ|` of Definition
10.4.1 (1) at level `[1]`. -/
def oneOrbitMap : A.E.OneOrbitSpace → A'.E.OneOrbitSpace :=
  oneMap D.Ψ ∘ (IsHomeomorph.homeomorph _ D.hΦ.isHomeomorph_oneOrbitMap).symm

theorem continuous_oneOrbitMap : Continuous D.oneOrbitMap :=
  (continuous_oneMap D.Ψ).comp (Homeomorph.continuous _)

theorem oneOrbitMap_oneMap (r : D.B.E.OneOrbitSpace) :
    D.oneOrbitMap (oneMap D.Φ r) = oneMap D.Ψ r := by
  change oneMap D.Ψ ((IsHomeomorph.homeomorph _ D.hΦ.isHomeomorph_oneOrbitMap).symm
    ((IsHomeomorph.homeomorph _ D.hΦ.isHomeomorph_oneOrbitMap) r)) = _
  rw [Homeomorph.symm_apply_apply]

/-- `|W'[1]| → |W'|` intertwines `|D|` on `|W[1]|` and on `|W|`. -/
theorem oneToOrbit_oneOrbitMap (q : A.E.OneOrbitSpace) :
    oneToOrbit A' (D.oneOrbitMap q) = D.orbitMap (oneToOrbit A q) := by
  obtain ⟨r, rfl⟩ := D.hΦ.isHomeomorph_oneOrbitMap.surjective q
  change oneToOrbit A' (D.oneOrbitMap (oneMap D.Φ r)) = D.orbitMap (oneToOrbit A (oneMap D.Φ r))
  rw [oneOrbitMap_oneMap, oneToOrbit_oneMap, oneToOrbit_oneMap, D.orbitMap_orbitMap_Φ]

/-- `|D|` on `|W[1]|` is determined by `|D|` on `|W|`. -/
theorem oneOrbitMap_eq_of_orbitMap_eq {D₁ D₂ : SDiagram A A'} (h : D₁.orbitMap = D₂.orbitMap) :
    D₁.oneOrbitMap = D₂.oneOrbitMap := funext fun q =>
  oneToOrbit_injective A' (by rw [oneToOrbit_oneOrbitMap, oneToOrbit_oneOrbitMap, h])

theorem oneOrbitMap_symm_oneOrbitMap (q : A.E.OneOrbitSpace) :
    (D.symm hΨ).oneOrbitMap (D.oneOrbitMap q) = q :=
  oneToOrbit_injective A (by
    rw [oneToOrbit_oneOrbitMap, oneToOrbit_oneOrbitMap]
    exact D.orbitMap_symm_orbitMap hΨ _)

theorem oneOrbitMap_oneOrbitMap_symm (q : A'.E.OneOrbitSpace) :
    D.oneOrbitMap ((D.symm hΨ).oneOrbitMap q) = q :=
  oneToOrbit_injective A' (by
    rw [oneToOrbit_oneOrbitMap, oneToOrbit_oneOrbitMap]
    exact D.orbitMap_orbitMap_symm hΨ _)

/-- **The pull-back `[D]^*N'`** (2021 p. 547): `e ↦ N'(e')` for a representative `e'` of
`|D|(|e|) ∈ |W'[1]|`. -/
def pullNorm (N' : A'.B.One → ℝ) : A.B.One → ℝ := fun e => N' (D.oneOrbitMap ⟦e⟧).out

/-- **The push-forward `[D]_*N`**, the pull-back along the reversed diagram. -/
def pushNorm (N : A.B.One → ℝ) : A'.B.One → ℝ := (D.symm hΨ).pullNorm N

variable {D hΨ}

/-- `[D]^*N'(e) = N'(e')` whenever `|D|(|e|) = |e'|` in `|W'[1]|`. -/
theorem pullNorm_eq {N' : A'.B.One → ℝ} (hN' : IsOneInvariant A' N') {e : A.B.One}
    {e' : A'.B.One} (h : D.oneOrbitMap ⟦e⟧ = ⟦e'⟧) : D.pullNorm N' e = N' e' := by
  refine hN' _ _ ?_
  exact (congrArg (oneToOrbit A') (Quotient.out_eq (D.oneOrbitMap ⟦e⟧))).trans
    (congrArg (oneToOrbit A') h)

/-- **The text's formula** (2021 p. 547): `[D]^*N'(e) = N'(Ψ(e''))` for `e'' ∈ W''_{0,1}` with a
morphism `Φ(e'') → e`. -/
theorem pullNorm_eq_Ψ {N' : A'.B.One → ℝ} (hN' : IsOneInvariant A' N') {e : A.B.One}
    (e'' : D.B.B.One) (h : oneMap D.Φ ⟦e''⟧ = ⟦e⟧) :
    D.pullNorm N' e = N' (StrongBundle.oneRestrict D.B.B A'.B (SEP.Hom.Φ D.Ψ).obj
      (SEP.Hom.isStrongBundleFunctor D.Ψ).isStrongBundleMap_obj.mapsTo_oneSet e'') :=
  pullNorm_eq hN' (by rw [← h, oneOrbitMap_oneMap]; rfl)

theorem isOneInvariant_pullNorm (N' : A'.B.One → ℝ) : IsOneInvariant A (D.pullNorm N') :=
  fun a b hab => by
    change N' (D.oneOrbitMap ⟦a⟧).out = N' (D.oneOrbitMap ⟦b⟧).out
    rw [mk_eq_mk_of_π_eq hab]

theorem pullNorm_eq_lift {N' : A'.B.One → ℝ} (hN' : IsOneInvariant A' N') :
    D.pullNorm N' = Quotient.lift N' (fun a b h => hN' a b (Quotient.sound h)) ∘
      D.oneOrbitMap ∘ Quotient.mk _ := funext fun e => by
  obtain ⟨e', he'⟩ := Quotient.exists_rep (D.oneOrbitMap ⟦e⟧)
  rw [pullNorm_eq hN' he'.symm]
  simp only [Function.comp_apply, ← he', Quotient.lift_mk]

theorem continuous_pullNorm {N' : A'.B.One → ℝ} (hN' : IsOneInvariant A' N')
    (hc : Continuous N') : Continuous (D.pullNorm N') := by
  rw [pullNorm_eq_lift hN']
  exact (hc.quotient_lift _).comp (D.continuous_oneOrbitMap.comp continuous_quot_mk)

theorem pushNorm_pullNorm {N' : A'.B.One → ℝ} (hN' : IsOneInvariant A' N') :
    D.pushNorm hΨ (D.pullNorm N') = N' := funext fun e' => by
  obtain ⟨e, he⟩ := Quotient.exists_rep ((D.symm hΨ).oneOrbitMap ⟦e'⟧)
  have h₁ : D.pushNorm hΨ (D.pullNorm N') e' = D.pullNorm N' e :=
    pullNorm_eq (isOneInvariant_pullNorm N') he.symm
  rw [h₁]
  exact pullNorm_eq hN' (by rw [he, oneOrbitMap_oneOrbitMap_symm])

theorem pullNorm_pushNorm {N : A.B.One → ℝ} (hN : IsOneInvariant A N) :
    D.pullNorm (D.pushNorm hΨ N) = N := funext fun e => by
  obtain ⟨e', he'⟩ := Quotient.exists_rep (D.oneOrbitMap ⟦e⟧)
  have h₁ : D.pullNorm (D.pushNorm hΨ N) e = D.pushNorm hΨ N e' :=
    pullNorm_eq (isOneInvariant_pullNorm _) he'.symm
  rw [h₁]
  exact pullNorm_eq hN (by rw [he', oneOrbitMap_symm_oneOrbitMap])

theorem pullNorm_eq_of_orbitMap_eq {D₁ D₂ : SDiagram A A'} (h : D₁.orbitMap = D₂.orbitMap)
    (N' : A'.B.One → ℝ) : D₁.pullNorm N' = D₂.pullNorm N' := by
  change (fun e => N' (D₁.oneOrbitMap ⟦e⟧).out) = fun e => N' (D₂.oneOrbitMap ⟦e⟧).out
  rw [oneOrbitMap_eq_of_orbitMap_eq h]

theorem pushNorm_eq_of_orbitMap_eq {D₁ D₂ : SDiagram A A'} (hΨ₁ : SEP.equivalences D₁.Ψ)
    (hΨ₂ : SEP.equivalences D₂.Ψ) (h : D₁.orbitMap = D₂.orbitMap) (N : A.B.One → ℝ) :
    D₁.pushNorm hΨ₁ N = D₂.pushNorm hΨ₂ N :=
  pullNorm_eq_of_orbitMap_eq (orbitMap_symm_eq hΨ₁ hΨ₂ h) N

end SDiagram

namespace GenSBMap

variable {f : GenSBMap A A'} (hf : f.IsGeneralizedIso)

/-- **The pull-back `[D]^*N'`** of a function on `W'_{0,1}` along a generalized strong bundle
isomorphism (2021 Proposition 11.5.1), for a chosen representative. -/
def pullNorm (N' : A'.B.One → ℝ) : A.B.One → ℝ := (rep hf).pullNorm N'

/-- **The push-forward `[D]_*N`** (2021 Proposition 11.5.1). -/
def pushNorm (N : A.B.One → ℝ) : A'.B.One → ℝ := (rep hf).pushNorm (isEquivalence_rep_Ψ hf) N

/-- **2021 Proposition 11.5.1, p. 547 (2017: Proposition 11.6, p. 399)**, without conditions (1)
and (2) of Definition 8.3.5: for a generalized strong bundle isomorphism `[D] : W → W'`,
* `[D]^*N'` and `[D]_*N` do not depend on the representative, and `[D]^*N'(e) = N'(Ψ(e''))` for
  `e'' ∈ W''_{0,1}` with `Φ(e'') ≅ e`;
* if `N'` (resp. `N`) is an auxiliary norm, `[D]^*N'` (resp. `[D]_*N`) is continuous and satisfies
  condition (3) of Definition 8.3.5;
* `[D]^*[D]_*N = N` and `[D]_*[D]^*N' = N'` for auxiliary norms (indeed for every invariant `N`);
* if `|[D]| = |[D']|`, then `[D]^*N' = [D']^*N'` and `[D]_*N = [D']_*N`. -/
theorem proposition_11_5_1 :
    (∀ D : SDiagram A A', D.cls = f → ∀ N', pullNorm hf N' = D.pullNorm N') ∧
    (∀ (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ), D.cls = f →
      ∀ N, pushNorm hf N = D.pushNorm hΨ N) ∧
    (∀ (D : SDiagram A A'), D.cls = f → ∀ N', IsOneInvariant A' N' →
      ∀ (e : A.B.One) (e'' : D.B.B.One), oneMap D.Φ ⟦e''⟧ = ⟦e⟧ →
        pullNorm hf N' e = N' (StrongBundle.oneRestrict D.B.B A'.B (SEP.Hom.Φ D.Ψ).obj
          (SEP.Hom.isStrongBundleFunctor D.Ψ).isStrongBundleMap_obj.mapsTo_oneSet e'')) ∧
    (∀ N', A'.E.IsAuxNorm N' → Continuous (pullNorm hf N') ∧
      ∀ (h k : A.B.One) (φ : A.Mor) (hk : A.P (A.B.oneVal k) = A.X.src φ),
        A.B.oneVal h = A.E.μ ⟨(φ, A.B.oneVal k), hk⟩ → pullNorm hf N' h = pullNorm hf N' k) ∧
    (∀ N, A.E.IsAuxNorm N → Continuous (pushNorm hf N) ∧
      ∀ (h k : A'.B.One) (φ : A'.Mor) (hk : A'.P (A'.B.oneVal k) = A'.X.src φ),
        A'.B.oneVal h = A'.E.μ ⟨(φ, A'.B.oneVal k), hk⟩ → pushNorm hf N h = pushNorm hf N k) ∧
    (∀ N, IsOneInvariant A N → pullNorm hf (pushNorm hf N) = N) ∧
    (∀ N', IsOneInvariant A' N' → pushNorm hf (pullNorm hf N') = N') ∧
    (∀ {g : GenSBMap A A'} (hg : g.IsGeneralizedIso), f.orbitMap = g.orbitMap →
      (∀ N', pullNorm hf N' = pullNorm hg N') ∧ ∀ N, pushNorm hf N = pushNorm hg N) := by
  have ho : ∀ {D : SDiagram A A'}, D.cls = f → (rep hf).orbitMap = D.orbitMap := fun hD => by
    rw [← orbitMap_cls, ← orbitMap_cls, cls_rep, hD]
  refine ⟨fun D hD N' => SDiagram.pullNorm_eq_of_orbitMap_eq (ho hD) N',
    fun D hΨ hD N => SDiagram.pushNorm_eq_of_orbitMap_eq _ hΨ (ho hD) N,
    fun D hD N' hN' e e'' h => ?_, fun N' hN' => ⟨?_, ?_⟩, fun N hN => ⟨?_, ?_⟩,
    fun N hN => SDiagram.pullNorm_pushNorm hN, fun N' hN' => SDiagram.pushNorm_pullNorm hN',
    fun hg hfg => ?_⟩
  · rw [pullNorm, SDiagram.pullNorm_eq_of_orbitMap_eq (ho hD)]
    exact SDiagram.pullNorm_eq_Ψ hN' e'' h
  · exact SDiagram.continuous_pullNorm hN'.isOneInvariant hN'.isAuxNorm.continuous
  · exact isOneInvariant_iff.1 (SDiagram.isOneInvariant_pullNorm N')
  · exact SDiagram.continuous_pullNorm hN.isOneInvariant hN.isAuxNorm.continuous
  · exact isOneInvariant_iff.1 (SDiagram.isOneInvariant_pullNorm N)
  · have h : (rep hf).orbitMap = (rep hg).orbitMap := by
      rw [← orbitMap_cls, ← orbitMap_cls, cls_rep, cls_rep, hfg]
    exact ⟨fun N' => SDiagram.pullNorm_eq_of_orbitMap_eq h N',
      fun N => SDiagram.pushNorm_eq_of_orbitMap_eq _ _ h N⟩

end GenSBMap

end SBLocalization

end Polyfold
