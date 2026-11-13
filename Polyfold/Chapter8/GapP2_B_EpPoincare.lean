import Polyfold.Chapter8.GapP2_B_EpFormsObj
import Polyfold.Chapter4.Poincare2021b
import Polyfold.Chapter4.GapP1_OpenForms

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §8.2,
**Proposition 8.2.3** (Poincaré Lemma, pp. 373–374; not in the 2017 numbering of gap G.87):
the first step of its proof.

# The Poincaré lemma on an ep-groupoid: the step on the object M-polyfold

## The text, paraphrased

(Proposition 8.2.3) Every object `x` has saturated open neighbourhoods `V ⊆ U` such that every
closed `[ω] ∈ Ωᵏ_{ep,∞}(U)`, `k ≥ 1`, is `d[σ]` on `V` for some `[σ] ∈ Ωᵏ⁻¹_{ep,∞}(V)`.
(Proof) "Using Lemma 4.4.8 and just viewing the object polyfold" one finds `V'(x) ⊆ U'(x)` and a
primitive `[τ] ∈ Ωᵏ⁻¹_∞(V'(x))` of `[ω]`; `τ` is then averaged over `G_x` and extended to the
saturation of `V'(x)` by the morphisms.

## What is formalized

* `EP.proposition_8_2_3_object`: **the first step**.  Every object `x` has an open neighbourhood
  `V` such that every closed `a ∈ Ωᵏ⁺¹_{ep,∞}(X)` has a primitive on `V` among the forms of the
  object M-polyfold: `b ∈ Ωᵏ_∞(V)` with `db = a|V`.  (Lemma 4.4.8 for the image of `a` in
  `Ω*_∞(Ob X)`, `epFormsInftyToObj`.)

## Continued in Chapter 11

The averaging over `G_x` and the extension to the saturation, hence Proposition 8.2.3 itself,
use the push-forward of forms along the equivalence `G_x ⋉ U(x) → X|π⁻¹(π(U(x)))` of §11.2:
`EP.proposition_8_2_3` in `Chapter11/GapP2_B2_Poincare.lean` (gap G.87 closed, 2026-11-12).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace EP

variable (A : EP.{u})

theorem objPolyfold_carrier : A.objPolyfold.carrier = A.Obj := rfl

/-- **2021 Proposition 8.2.3, first step of the proof (p. 373)**: every object `x` of the
ep-groupoid has an open neighbourhood `V` on which every closed form `a ∈ Ωᵏ⁺¹_{ep,∞}(X)` is
exact as a form of the object M-polyfold, `db = a|V` with `b ∈ Ωᵏ_∞(V)`.  This is Lemma 4.4.8
applied to the image of `a` in `Ω*_∞(Ob X)`; the primitive is not yet compatible with the
morphisms.  (`A.objPolyfold.carrier` is the object space `A.Obj`, `objPolyfold_carrier`.) -/
theorem proposition_8_2_3_object (x : A.objPolyfold.carrier) :
    ∃ (V : Set A.objPolyfold.carrier) (hV : IsOpen V) (hxV : x ∈ V),
      ∀ (k : ℕ) (a : A.epFormsInfty (k + 1)), A.epFormsInftyD (k + 1) a = 0 →
        ∃ b : (A.objPolyfold.openSub hV ⟨x, hxV⟩).formsInfty k,
          (A.objPolyfold.openSub hV ⟨x, hxV⟩).formsInftyD k b =
            A.objPolyfold.formsInftyResOpen (k + 1) hV ⟨x, hxV⟩
              (A.epFormsInftyToObj (k + 1) a) := by
  obtain ⟨U, V, hU, hV, hxV, hVU, h⟩ := lemma_4_4_8 A.objPolyfold x
  refine ⟨V, hV, hxV, fun k a ha => ?_⟩
  have hc : A.objPolyfold.formsInftyD (k + 1) (A.epFormsInftyToObj (k + 1) a) = 0 := by
    have e := LinearMap.congr_fun (A.formsInftyD_comp_epFormsInftyToObj (k + 1)) a
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ha, map_zero] at e
    exact e
  obtain ⟨b, hb⟩ := h k (A.objPolyfold.formsInftyResOpen (k + 1) hU ⟨x, hVU hxV⟩
    (A.epFormsInftyToObj (k + 1) a))
    ((A.objPolyfold.formsInftyD_formsInftyResOpen (k + 1) hU ⟨x, hVU hxV⟩ _).trans (by
      rw [hc, map_zero]))
  exact ⟨b, hb.trans (A.objPolyfold.formsInftyResOpenOpen_comp (k + 1) hU ⟨x, hVU hxV⟩ hV
    ⟨x, hxV⟩ hVU _)⟩

end EP

end Polyfold
