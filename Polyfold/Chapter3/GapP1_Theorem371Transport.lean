import Polyfold.Chapter3.BasicClassComposition
import Polyfold.Chapter3.StrongBundleIsoSBR

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Theorem 3.7.1**
(preprint 3.58), p. 140: moving the conclusion back from the coordinates of the proof.

# Conjugation to a basic germ through sc-isomorphisms

The proof of Theorem 3.7.1 works in coordinates `E ≅ ℝⁿ ⊕ X`, `F ≅ ℝᴺ ⊕ Y`
(`GapP1_Theorem371Split`, row V3.89).  Its conclusion, "`f − f(0)` is conjugated to a basic germ
near `0`" (Definition 3.1.11, `IsConjugateToBasicGerm`), passes back through sc-isomorphisms:

* **`IsConjugateToBasicGerm.of_scIso`**: if `S : E ≅ E'`, `T : F ≅ F'` are sc-isomorphisms, `U` is
  relatively open in a partial quadrant of `E` and `S(U)` in one of `E'`, and the push-forward
  `T ∘ k ∘ S⁻¹` is conjugated to a basic germ on `S(U)`, then `k` is conjugated to a basic germ on
  `U` (compose the strong bundle isomorphism with `(u, v) ↦ (Su, Tv)`,
  `ScOperator.isStrongBundleIso_prodMap`, `IsStrongBundleIso.trans`).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

variable {E F E' F' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)}

/-- **Conjugation to a basic germ is invariant under sc-isomorphisms** of the base and the fibre:
if `T ∘ k ∘ S⁻¹` is conjugated to a basic germ on `S(U)`, then `k` is on `U`. -/
theorem IsConjugateToBasicGerm.of_scIso (hU : IsRelOpenInQuadrant E C U) (S : ScIso E E')
    (T : ScIso F F') (hU' : IsRelOpenInQuadrant E' C' (S 0 '' U)) {k : E 0 → F 0}
    (h : IsConjugateToBasicGerm (S 0 '' U) fun u' => T 0 (k ((S 0).symm u'))) :
    IsConjugateToBasicGerm U k := by
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U'', Ψ, Ψ', G, hb, Bc, hCt, hU'', hΨ, h0, hG,
    hh, hev⟩ := h
  have hΦ := ScOperator.isStrongBundleIso_prodMap hU hU' S.toScOperator S.symm.toScOperator
    T.toScOperator T.symm.toScOperator (fun u hu => mem_image_of_mem _ hu)
    (by rintro _ ⟨u, hu, rfl⟩; simpa using hu)
    (fun u _ => (S 0).symm_apply_apply u) (fun u _ => (S 0).apply_symm_apply u)
    (fun v => (T 0).symm_apply_apply v) (fun v => (T 0).apply_symm_apply v)
  have hiso := IsStrongBundleIso.trans hU hU' hU'' hΦ hΨ
  refine ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U'', _, _, G, hb, Bc, hCt, hU'', hiso, ?_, hG,
    hh, ?_⟩
  · change (Ψ (S 0 0, T 0 0)).1 = 0
    rw [map_zero, map_zero]
    exact h0
  · have hcont : Tendsto (S 0) (𝓝 0) (𝓝 0) := by
      have := (S 0).continuous.tendsto 0
      rwa [map_zero] at this
    filter_upwards [hcont.eventually hev] with u hu huU
    have h1 := hu (mem_image_of_mem _ huU)
    rw [(S 0).symm_apply_apply] at h1
    change (Ψ (S.toScOperator 0 u, T.toScOperator 0 (k u))).2 =
      hb ((Ψ (S.toScOperator 0 u, T.toScOperator 0 0)).1)
    rw [ScIso.toScOperator_apply, ScIso.toScOperator_apply, map_zero]
    exact h1

end Polyfold
