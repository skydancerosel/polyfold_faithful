import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_15

namespace RoundTrip.V6_15
open Polyfold Module

/-- The project's statement (Corollary 6.13), universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.corollary_6_4_12.{0, 0}

theorem A_holds : A := @Polyfold.corollary_6_4_12.{0, 0}

section Glue
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {T : E →L[ℝ] F} {P : F →L[ℝ] F}

/-- B's classical Fredholm notion gives Mathlib's (Banach spaces). -/
theorem isFredholm_of_op (hT : IsFredholmOp T) : T.IsFredholm :=
  isFredholm_of_banach T hT.1 hT.2.1 hT.2.2

omit [CompleteSpace E] [CompleteSpace F] in
theorem op_of_isFredholm (hT : T.IsFredholm) : IsFredholmOp T :=
  ⟨hT.finite_ker, hT.isClosed_range, hT.finite_coker⟩

omit [CompleteSpace E] [CompleteSpace F] in
theorem glp_of_good (hP : IsGoodLeftProj T P) : IsGLP T P :=
  ⟨hP.isProj, hP.finite_coker, hP.range_comp⟩

omit [CompleteSpace E] [CompleteSpace F] in
theorem good_of_glp (hP : IsGLP T P) : IsGoodLeftProj T P :=
  ⟨hP.1, hP.2.1, hP.2.2⟩

/-- The project's `γ^P_T` has B's defining property (91), for every choice. -/
theorem gammaProj_isGamma (hT : T.IsFredholm) (hP : IsGoodLeftProj T P) :
    IsGamma T P (gammaProj hT hP).toLinearMap := by
  intro n l j a d b' f hA hD hB hC ha hd hb hf
  have key := gammaProj_wedge_tmul hT hP ha hA hd hD (b := b') hb hB
    (c := fun i => (Submodule.Quotient.mk (f i) : F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)))
    (fun i => hf i) hC
  have hfun : (⇑(cokerCompEquiv hP).symm ∘ Fin.append
      (fun i => (Submodule.Quotient.mk (f i) : F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)))
      (projSeqPhi T P ∘ b')) =
      Fin.append (fun i => (LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).mkQ (f i))
        (fun k => (LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).mkQ (T (b' k : E))) := by
    funext i
    induction i using Fin.addCases with
    | left i => simp only [Function.comp_apply, Fin.append_left]; rfl
    | right i => simp only [Function.comp_apply, Fin.append_right]; rfl
  rw [hfun] at key
  exact key

/-- Uniqueness: a map with B's defining property (91) is the project's `γ^P_T` (both agree on one
nonzero vector of the line `det(T)`). -/
theorem eq_gammaProj_of_isGamma (hT : T.IsFredholm) (hP : IsGoodLeftProj T P)
    {g : fredholmDet T →ₗ[ℝ] fredholmDet (P ∘L T)} (hg : IsGamma T P g) :
    g = (gammaProj hT hP).toLinearMap := by
  have iT := hT.finite_ker
  have iTc : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have := hP.finite_coker
  have := (hP.isFredholm_comp hT).finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    (hP.isFredholm_comp hT).finite_coker
  obtain ⟨n, hn⟩ : ∃ n, n = finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)) := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, l = finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := ⟨_, rfl⟩
  let a : Basis (Fin n) ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)) :=
    (Module.finBasis ℝ _).reindex (finCongr hn.symm)
  let d0 : Basis (Fin l) ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) :=
    (Module.finBasis ℝ _).reindex (finCongr hl.symm)
  obtain ⟨j, b, hb, hj⟩ :=
    exists_linearIndependent_append (projSeqJ T P) (proposition_6_4_10 hP).1 a.linearIndependent hn
  have hlift : ∀ i, ∃ f : F, (LinearMap.range (T : E →ₗ[ℝ] F)).mkQ (f - P f) = d0 i := by
    intro i
    obtain ⟨c, hc⟩ := (proposition_6_4_10 hP).2.2.2 (d0 i)
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    exact ⟨f, hc⟩
  choose f hf using hlift
  have hC : l + j = finrank ℝ (F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    ((projSeq hP).finrank_eq_of_families hn hl hj).trans (cokerCompEquiv hP).finrank_eq.symm
  let h0 : fredholmDet T := wedge (⇑a) hn ⊗ₜ[ℝ] dualVec (wedge (⇑d0) hl)
  have h0ne : h0 ≠ 0 :=
    tmul_ne_zero_of_ne_zero (wedge_basis_ne_zero' a hn)
      (dualVec_ne_zero finrank_maxPow (wedge_basis_ne_zero' d0 hl))
  refine linearMap_ext_of_ne_zero (L := fredholmDet T) (M := fredholmDet (P ∘L T))
    (finrank_fredholmDet hT) h0ne ?_
  rw [hg n l j a d0 b f hn hl hj hC a.linearIndependent d0.linearIndependent hb hf,
    gammaProj_isGamma hT hP n l j a d0 b f hn hl hj hC a.linearIndependent d0.linearIndependent
      hb hf]

/-- With A: B's map `(γ^P_{RT})⁻¹ ∘ γ^P_{ST}` (any `γ`'s with the defining property) is the
project's `γ^R_T ∘ (γ^S_T)⁻¹`. -/
theorem corMap_eq (hA : A) (hT : T.IsFredholm) {R S : F →L[ℝ] F} (hP : IsGLP T P)
    (hR : IsGLP T R) (hS : IsGLP T S) (hPR : PLe P R) (hPS : PLe P S)
    (γPRT : fredholmDet (R ∘L T) ≃ₗ[ℝ] fredholmDet (P ∘L (R ∘L T)))
    (γPST : fredholmDet (S ∘L T) →ₗ[ℝ] fredholmDet (P ∘L (S ∘L T)))
    (h1 : IsGamma (R ∘L T) P γPRT.toLinearMap) (h2 : IsGamma (S ∘L T) P γPST) :
    corMap T hPR hPS γPRT γPST =
      (gammaProj hT (good_of_glp hR)).toLinearMap ∘ₗ
        (gammaProj hT (good_of_glp hS)).symm.toLinearMap := by
  have hP' := good_of_glp hP
  have hR' := good_of_glp hR
  have hS' := good_of_glp hS
  have e1 : γPRT = gammaProj (hR'.isFredholm_comp hT) (hP'.of_projLE hPR) :=
    LinearEquiv.toLinearMap_injective (eq_gammaProj_of_isGamma _ _ h1)
  have e2 : γPST = (gammaProj (hS'.isFredholm_comp hT) (hP'.of_projLE hPS)).toLinearMap :=
    eq_gammaProj_of_isGamma _ _ h2
  subst e1 e2
  refine LinearMap.ext fun h => ?_
  exact hA hT hP' hR' hS' hPS hPR h

end Glue

/-- `A ⇒ B`: every `γ` with the defining property (91) is the project's `gammaProj` (uniqueness on
the line `det`), then Corollary 6.13; the independence of `P` follows from the formula. -/
theorem A_to_B : A → B := by
  intro hA E F _ _ _ _ _ _ T hT
  have hT' := isFredholm_of_op hT
  refine ⟨?_, ?_⟩
  · intro P₁ P₂ R S hP₁ hP₂ hR hS hR₁ hS₁ hR₂ hS₂ γ₁PRT γ₁PST γ₂PRT γ₂PST h1 h2 h3 h4
    rw [corMap_eq hA hT' hP₁ hR hS hR₁ hS₁ _ _ h1 h2, corMap_eq hA hT' hP₂ hR hS hR₂ hS₂ _ _ h3 h4]
  · intro P R S hP hR hS hPR hPS γPRT γPST γRT γST h1 h2 h3 h4
    have e4 : γST = gammaProj hT' (good_of_glp hS) :=
      LinearEquiv.toLinearMap_injective (eq_gammaProj_of_isGamma hT' (good_of_glp hS) h4)
    rw [corMap_eq hA hT' hP hR hS hPR hPS _ _ h1 h2,
      eq_gammaProj_of_isGamma hT' (good_of_glp hR) h3, e4]

/-- `B ⇒ A`: B's second conjunct for the project's `gammaProj`'s, which have the defining
property. -/
theorem B_to_A : B → A := by
  intro hB E F _ _ _ _ _ _ T P R S hT hP hR hS hPS hPR h
  have := (hB E F T (op_of_isFredholm hT)).2 P R S (glp_of_good hP) (glp_of_good hR)
    (glp_of_good hS) hPR hPS
    (gammaProj (hR.isFredholm_comp hT) (hP.of_projLE hPR))
    (gammaProj (hS.isFredholm_comp hT) (hP.of_projLE hPS)).toLinearMap
    (gammaProj hT hR).toLinearMap (gammaProj hT hS)
    (gammaProj_isGamma _ _) (gammaProj_isGamma _ _) (gammaProj_isGamma _ _) (gammaProj_isGamma _ _)
  exact LinearMap.congr_fun this h

#rt_check RoundTrip.V6_15.A_to_B [Polyfold.corollary_6_4_12]
#rt_check RoundTrip.V6_15.B_to_A [Polyfold.corollary_6_4_12]
#rt_overlap RoundTrip.V6_15.B_to_A [Polyfold.corollary_6_4_12]

end RoundTrip.V6_15
