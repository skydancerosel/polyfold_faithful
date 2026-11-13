import Polyfold.Chapter11.EquivalenceForms
import Polyfold.Chapter8.EpFormsFunctor

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §11.2,
pp. 528–532: **Definition 11.2.3** on `Ω*_{ep,∞}`, formula (11.5), **Lemma 11.2.4**,
**Lemma 11.2.5**, **Lemma 11.2.6** (2017: Definition 11.2, Lemmas 11.2–11.4) (gap G.129).
Numbers and pages are the 2021 text's.

# Push-forward and pull-back along equivalences on `Ω*_{ep,∞}`

## The text, paraphrased

For an equivalence `F : X → Y` the push-forward `F_*ω ∈ Ω_{ep,∞}(Y)` of `ω ∈ Ω_{ep,∞}(X)`
satisfies `d_Y(F_*ω) = F_*(d_Xω)` (11.5).  (Lemma 11.2.4) For equivalences `F : X → Y`,
`G : Y → Z`: (1) `(G ∘ F)^* = F^* ∘ G^*`, (2) `(G ∘ F)_* = G_* ∘ F_*`, (3) `F_* F^* = 1`,
`F^* F_* = 1`.  (Lemma 11.2.5) Naturally equivalent equivalences `F, G : X → Y` have
`F_* = G_*`, `F^* = G^*`; naturally equivalent sc-smooth functors have the same pull-back.
(Lemma 11.2.6) For diagrams `X ←F A →G Y`, `X ←F' A' →G' Y` and an equivalence `H : A' → A`
with `F ∘ H ≃ F'`, `G ∘ H ≃ G'`: `F_* G^* = F'_* G'^*`, and `G_* F^* = G'_* F'^*` if `G`, `G'`
are equivalences.

## What is formalized

Namespace `Polyfold.EP` (bundled ep-groupoids `A`, `B`, `C`; `F : EpFunctor A.X B.X` with
`hF : F.IsEquivalence`):
* `isEquivalence_liftFunctor`: the index raises `Fⁱ : Xⁱ → Yⁱ` of an equivalence are
  equivalences (Chapter 10).
* `epFormsPush hF k i = (Fⁱ)_* : Ωᵏ_ep(Xⁱ) → Ωᵏ_ep(Yⁱ)`, inverse to `(Fⁱ)^*`
  (`epFormsPullback_epFormsPush`, `epFormsPush_epFormsPullback`), commuting with the maps of
  the directed systems (`epFormsPush_epFormsMap`).
* **`epFormsInftyPush hF k = F_* : Ωᵏ_{ep,∞}(X) → Ωᵏ_{ep,∞}(Y)`** (Definition 11.2.3), with
  `epFormsInftyPush_of` (`F_*[ω] = [(Fⁱ)_*ω]`); **Lemma 11.2.4 (3)**:
  `epFormsInftyPullback_epFormsInftyPush` (`F^* F_* = 1`), `epFormsInftyPush_epFormsInftyPullback`
  (`F_* F^* = 1`); `epFormsInftyEquiv`, the linear isomorphism `F_*`.
* **(11.5)**: `epFormsInftyD_comp_epFormsInftyPush`, `d_Y ∘ F_* = F_* ∘ d_X`.
* **Lemma 11.2.4 (2)**: `lemma_11_2_4_two`, `(G ∘ F)_* = G_* ∘ F_*`.  ((1) is
  `EP.epFormsInftyPullback_comp` of Chapter 8.)
* **Lemma 11.2.5**: `lemma_11_2_5_push` (`F_* = G_*` for naturally equivalent equivalences);
  the statements on pull-backs are `EP.epFormsInftyPullback_eq_of_natTrans` of Chapter 8.
* **Lemma 11.2.6**: `lemma_11_2_6` (`F_* ∘ G^* = F'_* ∘ G'^*`) and `lemma_11_2_6_push`
  (`G_* ∘ F^* = G'_* ∘ F'^*`).
* `epFormsInftyPush_eq_of_comp_eq_id`: `F_*` is the only right inverse of `F^*`.

## The reading

`Ω_{ep,∞}(X)` is the direct limit over the index lifts `Xⁱ`; `F_*` is defined on each
`Ωᵏ_ep(Xⁱ)` by the equivalence `Fⁱ : Xⁱ → Yⁱ` (the text's formula on level `i`, see
`EpFunctor.IsEquivalence.definition_11_2_3`).  No hypothesis is added.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

open MPolyfold

universe u v w

namespace EP

variable {A : EP.{u}} {B : EP.{v}} {C : EP.{w}}

/-- **The index raises `Fⁱ : Xⁱ → Yⁱ` of an equivalence are equivalences** (the proof of
Proposition 10.1.18). -/
theorem isEquivalence_liftFunctor {F : EpFunctor A.X B.X} (hF : F.IsEquivalence) :
    ∀ i : ℕ, (liftFunctor F i).IsEquivalence
  | 0 => hF
  | i + 1 => (isEquivalence_liftFunctor hF i).liftOne

variable {F : EpFunctor A.X B.X} (hF : F.IsEquivalence) (k : ℕ)

/-- **The push-forward `(Fⁱ)_* : Ωᵏ_ep(Xⁱ) → Ωᵏ_ep(Yⁱ)`** by the index raise of an equivalence. -/
def epFormsPush (i : ℕ) : A.epForms k i →ₗ[ℝ] B.epForms k i :=
  (isEquivalence_liftFunctor hF i).formPush k

theorem epFormsPullback_epFormsPush (i : ℕ) (ω : A.epForms k i) :
    epFormsPullback F k i (epFormsPush hF k i ω) = ω :=
  (isEquivalence_liftFunctor hF i).formPullback_formPush ω

theorem epFormsPush_epFormsPullback (i : ℕ) (τ : B.epForms k i) :
    epFormsPush hF k i (epFormsPullback F k i τ) = τ :=
  (isEquivalence_liftFunctor hF i).formPush_formPullback τ

/-- `(Fⁱ)_*ω = τ` iff `(Fⁱ)^*τ = ω`. -/
theorem epFormsPush_eq_iff (i : ℕ) (ω : A.epForms k i) (τ : B.epForms k i) :
    epFormsPush hF k i ω = τ ↔ epFormsPullback F k i τ = ω :=
  (isEquivalence_liftFunctor hF i).formPush_eq_iff ω τ

/-- The push-forward commutes with the maps of the directed systems. -/
theorem epFormsPush_epFormsMap {i j : ℕ} (h : i ≤ j) (ω : A.epForms k i) :
    epFormsPush hF k j (A.epFormsMap k i j h ω) =
      B.epFormsMap k i j h (epFormsPush hF k i ω) := by
  rw [epFormsPush_eq_iff, epFormsPullback_epFormsMap, epFormsPullback_epFormsPush]

/-- **2021 Definition 11.2.3, p. 528 (2017: Definition 11.2): the push-forward
`F_* : Ωᵏ_{ep,∞}(X) → Ωᵏ_{ep,∞}(Y)`** of sc-differential forms by an equivalence
`F : X → Y`. -/
def epFormsInftyPush : A.epFormsInfty k →ₗ[ℝ] B.epFormsInfty k :=
  Module.DirectLimit.lift ℝ ℕ (fun i => ↥(A.epForms k i)) (A.epFormsMap k)
    (fun i => (B.epFormsInftyOf k i).comp (epFormsPush hF k i)) fun i j h ω => by
      simp only [LinearMap.comp_apply]
      rw [epFormsPush_epFormsMap, epFormsInftyOf_epFormsMap]

/-- `F_*[ω] = [(Fⁱ)_*ω]`. -/
theorem epFormsInftyPush_of (i : ℕ) (ω : A.epForms k i) :
    epFormsInftyPush hF k (A.epFormsInftyOf k i ω) =
      B.epFormsInftyOf k i (epFormsPush hF k i ω) :=
  Module.DirectLimit.lift_of _ _ _

/-- **2021 Lemma 11.2.4 (3), p. 528 (2017: Lemma 11.2): `F^* ∘ F_* = 1`** on
`Ωᵏ_{ep,∞}(X)`. -/
theorem epFormsInftyPullback_comp_epFormsInftyPush :
    (epFormsInftyPullback F k).comp (epFormsInftyPush hF k) = LinearMap.id := by
  refine Module.DirectLimit.hom_ext fun i => LinearMap.ext fun ω => ?_
  simp only [LinearMap.comp_apply]
  rw [epFormsInftyPush_of, epFormsInftyPullback_of, epFormsPullback_epFormsPush]
  rfl

/-- **2021 Lemma 11.2.4 (3), p. 528 (2017: Lemma 11.2): `F_* ∘ F^* = 1`** on
`Ωᵏ_{ep,∞}(Y)`. -/
theorem epFormsInftyPush_comp_epFormsInftyPullback :
    (epFormsInftyPush hF k).comp (epFormsInftyPullback F k) = LinearMap.id := by
  refine Module.DirectLimit.hom_ext fun i => LinearMap.ext fun ω => ?_
  simp only [LinearMap.comp_apply]
  rw [epFormsInftyPullback_of, epFormsInftyPush_of, epFormsPush_epFormsPullback]
  rfl

theorem epFormsInftyPullback_epFormsInftyPush (a : A.epFormsInfty k) :
    epFormsInftyPullback F k (epFormsInftyPush hF k a) = a :=
  LinearMap.congr_fun (epFormsInftyPullback_comp_epFormsInftyPush hF k) a

theorem epFormsInftyPush_epFormsInftyPullback (b : B.epFormsInfty k) :
    epFormsInftyPush hF k (epFormsInftyPullback F k b) = b :=
  LinearMap.congr_fun (epFormsInftyPush_comp_epFormsInftyPullback hF k) b

/-- **The linear isomorphism `F_* : Ωᵏ_{ep,∞}(X) ≃ Ωᵏ_{ep,∞}(Y)`** of an equivalence, with
inverse `F^*`. -/
def epFormsInftyEquiv : A.epFormsInfty k ≃ₗ[ℝ] B.epFormsInfty k :=
  LinearEquiv.ofLinearMap (epFormsInftyPush hF k) (epFormsInftyPullback F k)
    (epFormsInftyPush_comp_epFormsInftyPullback hF k)
    (epFormsInftyPullback_comp_epFormsInftyPush hF k)

/-- **`F_*` is the only right inverse of `F^*`.** -/
theorem epFormsInftyPush_eq_of_comp_eq_id {T : A.epFormsInfty k →ₗ[ℝ] B.epFormsInfty k}
    (h : (epFormsInftyPullback F k).comp T = LinearMap.id) : T = epFormsInftyPush hF k := by
  refine LinearMap.ext fun a => ?_
  have h1 := LinearMap.congr_fun h a
  rw [LinearMap.comp_apply, LinearMap.id_apply] at h1
  rw [← h1, epFormsInftyPush_epFormsInftyPullback, h1]

/-- **2021 (11.5), p. 528: `d_Y ∘ F_* = F_* ∘ d_X`** on `Ω*_{ep,∞}`, for an equivalence
`F : X → Y`. -/
theorem epFormsInftyD_comp_epFormsInftyPush :
    (B.epFormsInftyD k).comp (epFormsInftyPush hF k) =
      (epFormsInftyPush hF (k + 1)).comp (A.epFormsInftyD k) := by
  refine LinearMap.ext fun a => ?_
  have e := LinearMap.congr_fun (epFormsInftyD_comp_epFormsInftyPullback F k)
    (epFormsInftyPush hF k a)
  simp only [LinearMap.comp_apply] at e ⊢
  rw [epFormsInftyPullback_epFormsInftyPush] at e
  rw [e, epFormsInftyPush_epFormsInftyPullback]

/-- **2021 Lemma 11.2.4 (2), p. 528 (2017: Lemma 11.2): `(G ∘ F)_* = G_* ∘ F_*`** for
equivalences `F : X → Y`, `G : Y → Z`. -/
theorem lemma_11_2_4_two {G : EpFunctor B.X C.X} (hG : G.IsEquivalence)
    (hGF : (G.comp F).IsEquivalence) :
    epFormsInftyPush hGF k = (epFormsInftyPush hG k).comp (epFormsInftyPush hF k) := by
  refine (epFormsInftyPush_eq_of_comp_eq_id hGF k ?_).symm
  rw [epFormsInftyPullback_comp, LinearMap.comp_assoc,
    ← LinearMap.comp_assoc (epFormsInftyPush hF k), epFormsInftyPullback_comp_epFormsInftyPush,
    LinearMap.id_comp, epFormsInftyPullback_comp_epFormsInftyPush]

/-- **2021 Lemma 11.2.5, p. 529 (2017: Lemma 11.3), the push-forward**: naturally equivalent
equivalences `F, G : X → Y` have the same push-forward, `F_* = G_*`.  (The statements on the
pull-backs are `epFormsInftyPullback_eq_of_natTrans`.) -/
theorem lemma_11_2_5_push {G : EpFunctor A.X B.X} (hG : G.IsEquivalence)
    (h : F.NaturallyEquivalent G) : epFormsInftyPush hF k = epFormsInftyPush hG k := by
  refine epFormsInftyPush_eq_of_comp_eq_id hG k ?_
  rw [← epFormsInftyPullback_eq_of_natTrans k h, epFormsInftyPullback_comp_epFormsInftyPush]

/-- **2021 Lemma 11.2.6, p. 531 (2017: Lemma 11.4)**: for diagrams `X ←F A →G Y` and
`X ←F' A' →G' Y` (`F`, `F'` equivalences, `G`, `G'` sc-smooth functors) and an equivalence
`H : A' → A` with `F ∘ H ≃ F'` and `G ∘ H ≃ G'`: `F_* ∘ G^* = F'_* ∘ G'^*` on
`Ω*_{ep,∞}(Y)`. -/
theorem lemma_11_2_6 {X : EP.{u}} {Y : EP.{v}} {A : EP.{w}} {A' : EP.{w}}
    {F : EpFunctor A.X X.X} (hF : F.IsEquivalence) (G : EpFunctor A.X Y.X)
    {F' : EpFunctor A'.X X.X} (hF' : F'.IsEquivalence) (G' : EpFunctor A'.X Y.X)
    {H : EpFunctor A'.X A.X} (hH : H.IsEquivalence) (hFH : (F.comp H).NaturallyEquivalent F')
    (hGH : (G.comp H).NaturallyEquivalent G') (k : ℕ) :
    (epFormsInftyPush hF k).comp (epFormsInftyPullback G k) =
      (epFormsInftyPush hF' k).comp (epFormsInftyPullback G' k) := by
  rw [← lemma_11_2_5_push (hF.comp hH) k hF' hFH, lemma_11_2_4_two hH k hF (hF.comp hH),
    ← epFormsInftyPullback_eq_of_natTrans k hGH, epFormsInftyPullback_comp,
    LinearMap.comp_assoc, ← LinearMap.comp_assoc (epFormsInftyPullback G k),
    epFormsInftyPush_comp_epFormsInftyPullback, LinearMap.id_comp]

/-- **2021 Lemma 11.2.6, p. 531 (2017: Lemma 11.4), second part**: if in addition `G`, `G'`
are equivalences, `G_* ∘ F^* = G'_* ∘ F'^*` on `Ω*_{ep,∞}(X)`. -/
theorem lemma_11_2_6_push {X : EP.{u}} {Y : EP.{v}} {A : EP.{w}} {A' : EP.{w}}
    (F : EpFunctor A.X X.X) {G : EpFunctor A.X Y.X} (hG : G.IsEquivalence)
    (F' : EpFunctor A'.X X.X) {G' : EpFunctor A'.X Y.X} (hG' : G'.IsEquivalence)
    {H : EpFunctor A'.X A.X} (hH : H.IsEquivalence) (hFH : (F.comp H).NaturallyEquivalent F')
    (hGH : (G.comp H).NaturallyEquivalent G') (k : ℕ) :
    (epFormsInftyPush hG k).comp (epFormsInftyPullback F k) =
      (epFormsInftyPush hG' k).comp (epFormsInftyPullback F' k) :=
  lemma_11_2_6 hG F hG' F' hH hGH hFH k

end EP

end Polyfold
