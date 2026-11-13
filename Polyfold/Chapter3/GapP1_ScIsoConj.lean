import Polyfold.Chapter3.FredholmGermLinearization
import Polyfold.Chapter2.TameFaces
import Polyfold.Chapter1.ScFredholmCriterion

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Theorem 3.7.1**
(preprint 3.58), p. 140: the calculus needed to move the hypotheses into the coordinates of the
proof (row V3.89).

# Conjugating an sc-smooth map by sc-isomorphisms

For sc-isomorphisms `S : E ≅ E'`, `T : F ≅ F'` and `f : U → F`, the conjugate
`g = T ∘ f ∘ S⁻¹ : S(U) → F'` (`scIsoConjMap S T f`, on the preimage `(S⁻¹)⁻¹(U)`):

* `isScSmooth_conjMap`: `g` is sc-smooth when `f` is;
* `scDeriv_conjMap`: `Dg(y) = T ∘ Df(S⁻¹y) ∘ S⁻¹` (the chain rule, with `D(S⁻¹) = S⁻¹`);
* `levelDeriv_conjMap`: the same on every level `m`, for the level operators;
* `isScFredholm_of_conj`: an sc-operator whose base map is `T ∘ L ∘ S⁻¹` for an sc-Fredholm `L` is
  sc-Fredholm with the same index (Fredholm on level `0` and regularizing,
  `isScFredholm_iff`).
-/

open Set Function Topology

noncomputable section

namespace Polyfold

variable {E F E' F' : ScBanach}

/-- An sc-operator commutes with the base maps of the shifted scales. -/
lemma ScOperator.shift_toBase_apply (L : ScOperator E E') (m : ℕ) (x : E (m + 1)) :
    E'.shift.toBase m (L (m + 1) x) = L 1 (E.shift.toBase m x) := by
  apply E'.toBase_injective 1
  rw [← E'.shift_toBase, L.toBase_comm, L.toBase_comm, ← E.shift_toBase]

/-- The conjugate `T ∘ f ∘ S⁻¹` of `f : E₀ → F₀` by sc-isomorphisms `S : E ≅ E'`, `T : F ≅ F'`. -/
def scIsoConjMap (S : ScIso E E') (T : ScIso F F') (f : E 0 → F 0) : E' 0 → F' 0 :=
  fun u => T 0 (f ((S 0).symm u))

section Conj

variable (S : ScIso E E') (T : ScIso F F') {U : Set (E 0)} {f : E 0 → F 0}

lemma scIsoConjMap_eq : scIsoConjMap S T f = T.toScOperator 0 ∘ (f ∘ S.symm.toScOperator 0) := rfl

/-- The conjugate of an sc-smooth map is sc-smooth on the preimage `(S⁻¹)⁻¹(U)`. -/
theorem isScSmooth_conjMap (hU : IsScDomain E U) (hU' : IsScDomain E' ((S 0).symm ⁻¹' U))
    (hf : IsScSmooth U f) : IsScSmooth ((S 0).symm ⁻¹' U) (scIsoConjMap S T f) := by
  have h1 : IsScSmooth ((S 0).symm ⁻¹' U) (f ∘ S.symm.toScOperator 0) :=
    IsScSmooth.comp hU' hU hf (S.symm.toScOperator.isScSmooth hU') fun u hu => hu
  rw [scIsoConjMap_eq]
  exact IsScSmooth.comp hU' (isScDomain_univ F) (T.toScOperator.isScSmooth (isScDomain_univ F)) h1
    (mapsTo_univ _ _)

/-- **The chain rule for the conjugate**: `Dg(y) = T ∘ Df(S⁻¹y) ∘ S⁻¹` at level-`1` points. -/
theorem scDeriv_conjMap (hU : IsScDomain E U) (hU' : IsScDomain E' ((S 0).symm ⁻¹' U))
    (hf : IsScSmooth U f) {y : E' 1} (hy : y ∈ E'.lvlSet ((S 0).symm ⁻¹' U) 1) (w : E' 0) :
    scDeriv ((S 0).symm ⁻¹' U) (scIsoConjMap S T f) y w =
      T 0 (scDeriv U f ((S 1).symm y) ((S 0).symm w)) := by
  have hSs := S.symm.toScOperator.isScSmooth hU'
  have hmaps : MapsTo (S.symm.toScOperator 0) ((S 0).symm ⁻¹' U) U := fun u hu => hu
  have h1 : IsScSmooth ((S 0).symm ⁻¹' U) (f ∘ S.symm.toScOperator 0) :=
    IsScSmooth.comp hU' hU hf hSs hmaps
  have hT := T.toScOperator.isScSmooth (isScDomain_univ F)
  -- inner chain rule
  have hin := scDeriv_comp_apply_of_isScDomain hU' hU hSs.isSc1 hf.isSc1 hmaps hy w
  rw [ScOperator.scDeriv_eq _ hU' hy, ScOperator.levelMap_eq] at hin
  -- outer chain rule
  have hout := scDeriv_comp_apply_of_isScDomain hU' (isScDomain_univ F) h1.isSc1 hT.isSc1
    (mapsTo_univ _ _) hy w
  rw [ScOperator.scDeriv_eq _ (isScDomain_univ F) (mem_univ _)] at hout
  rw [scIsoConjMap_eq, ← hout, ← hin]
  rfl

/-- **The level operators of the conjugate**: `Dg(y) = T_m ∘ Df(S⁻¹y) ∘ S_m⁻¹` on `E'_m`, for
`y ∈ (S⁻¹)⁻¹(U)_{m+1}`. -/
theorem levelDeriv_conjMap (hU : IsScDomain E U) (hU' : IsScDomain E' ((S 0).symm ⁻¹' U))
    (hf : IsScSmooth U f) (m : ℕ) {y : E' (m + 1)}
    (hy : y ∈ E'.lvlSet ((S 0).symm ⁻¹' U) (m + 1)) (v : E' m) :
    levelDeriv (scDeriv ((S 0).symm ⁻¹' U) (scIsoConjMap S T f)) m y v =
      T m (levelDeriv (scDeriv U f) m ((S (m + 1)).symm y) ((S m).symm v)) := by
  have hg := isScSmooth_conjMap S T hU hU' hf
  have hyU : (S (m + 1)).symm y ∈ E.lvlSet U (m + 1) := by
    rw [ScBanach.mem_lvlSet, ScIso.symm_toBase_comm]; exact hy
  have hy1 : E'.shift.toBase m y ∈ E'.lvlSet ((S 0).symm ⁻¹' U) 1 := by
    rw [ScBanach.mem_lvlSet, ← E'.shift_toBase]; exact hy
  apply F'.toBase_injective m
  rw [hg.isSc1.isSc1With_scDeriv.toBase_levelDeriv hy, T.toBase_comm,
    hf.isSc1.isSc1With_scDeriv.toBase_levelDeriv hyU, scDeriv_conjMap S T hU hU' hf hy1,
    ScIso.symm_toBase_comm]
  have h := S.symm.toScOperator.shift_toBase_apply m y
  change E.shift.toBase m ((S (m + 1)).symm y) = (S 1).symm (E'.shift.toBase m y) at h
  rw [h]

/-- **Sc-Fredholm operators under conjugation by sc-isomorphisms**: if the base map of `L'` is
`T ∘ L ∘ S⁻¹` and `L` is sc-Fredholm, then `L'` is sc-Fredholm with the same index. -/
theorem isScFredholm_of_conj {L : ScOperator E F} {L' : ScOperator E' F'}
    (h : ∀ v, L' 0 v = T 0 (L 0 ((S 0).symm v))) (hL : IsScFredholm L) :
    IsScFredholm L' ∧ scIndex L' = scIndex L := by
  have hL0 : L' 0 = ((T 0 : F 0 →L[ℝ] F' 0)).comp ((L 0).comp ((S 0).symm : E' 0 →L[ℝ] E 0)) :=
    ContinuousLinearMap.ext h
  obtain ⟨hF, hR⟩ := isScFredholm_iff.1 hL
  obtain ⟨hF', hind⟩ := isFredholm_equiv_comp_equiv hF (S 0).symm (T 0)
  refine ⟨isScFredholm_iff.2 ⟨hL0 ▸ hF', fun m e he => ?_⟩, ?_⟩
  · obtain ⟨w, hw⟩ := he
    have h1 : L 0 ((S 0).symm e) ∈ range (F.toBase m) := by
      refine ⟨(T m).symm w, ?_⟩
      rw [ScIso.symm_toBase_comm, hw, h, ContinuousLinearEquiv.symm_apply_apply]
    obtain ⟨u, hu⟩ := hR m _ h1
    refine ⟨S m u, ?_⟩
    rw [S.toBase_comm, hu, ContinuousLinearEquiv.apply_symm_apply]
  · rw [scIndex_eq_fredholmIndex, scIndex_eq_fredholmIndex, hL0]
    exact hind

end Conj

end Polyfold
