import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_13

/-!
Round trip for V6_13 (the isomorphism `γ^P_T`, p. 210).  `A` is
`gammaProj_tmul ∧ gammaProj_wedge_tmul` (universes at `0`): the project's map `gammaProj hT hP`
satisfies formula (91) for every choice of `E(T,P)` (as a `Choice` structure, and for families of
vectors).  `gammaProj`, `projSeq`, `cokerCompEquiv` are vocabulary.

* `A ⇒ B`: `γ := gammaProj`; A's family form gives B's `IsGamma` once the `C`-side cosets
  `(cokerCompEquiv hP)⁻¹ (f + R(P), T b' + R(P))` are read as `(f + R(PT), T b' + R(PT))`
  (`symm_comp_append`).
* `B ⇒ A`: B's `γ` has the value (91) on every `Choice` (`value_of_isGamma`: translate a `Choice`
  into B's families: bases `a`, `d`, `b' = Z ∘ b'`, lifts `f` of the `c`).  The project's
  `gammaProj` is by definition `smulRight (dualVec χ₀.source) χ₀.value` for the canonical choice
  `χ₀`, so it agrees with `γ` on `χ₀.source ≠ 0` (unfolding only, NOT the banned theorems nor the
  choice-independence `lemma_6_3_3`); `det(T)` is a line, hence `gammaProj = γ`
  (`gammaProj_eq_of_isGamma`) and both conjuncts of A follow from B's `IsGamma`.  So B's
  choice-independence (Lemma 6.5 for `E(T,P)`) is what B ⇒ A uses.
-/

namespace RoundTrip.V6_13
open Polyfold TensorProduct

/-- The project's statement: `γ^P_T` on wedges, formula (91), universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.gammaProj_tmul.{0, 0} ∧ type_of% @Polyfold.gammaProj_wedge_tmul.{0, 0}

theorem A_holds : A := ⟨@Polyfold.gammaProj_tmul, @Polyfold.gammaProj_wedge_tmul⟩

set_option linter.unusedSectionVars false

section Glue

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem isGLP_iff (T : E →L[ℝ] F) (P : F →L[ℝ] F) : IsGLP T P ↔ IsGoodLeftProj T P :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.isProj, h.finite_coker, h.range_comp⟩⟩

theorem isFredholmOp_of_isFredholm {L : E →L[ℝ] F} (h : L.IsFredholm) : IsFredholmOp L :=
  ⟨h.finite_ker, h.isClosed_range, h.finite_coker⟩

theorem isFredholm_of_isFredholmOp {L : E →L[ℝ] F} (h : IsFredholmOp L) : L.IsFredholm :=
  isFredholm_of_banach L h.1 h.2.1 h.2.2

variable {T : E →L[ℝ] F} {P : F →L[ℝ] F}

/-- Equal families have equal wedges. -/
theorem wedge_congr {V : Type} [AddCommGroup V] [Module ℝ V] {k : ℕ} {v w : Fin k → V}
    (h : v = w) (hv : k = Module.finrank ℝ V) (hw : k = Module.finrank ℝ V) :
    wedge v hv = wedge w hw := by
  subst h; rfl

/-- The `C`-side of (91) read in `F / R(P T)`: if `cᵢ = fᵢ + R(P)`, then
`(cokerCompEquiv hP)⁻¹ ∘ (c, Φ ∘ b) = (f + R(PT), T b + R(PT))`. -/
theorem symm_comp_append (hP : IsGoodLeftProj T P) {l j : ℕ} {c : Fin l → F ⧸
    LinearMap.range (P : F →ₗ[ℝ] F)} (f : Fin l → F)
    (hcf : ∀ i, (LinearMap.range (P : F →ₗ[ℝ] F)).mkQ (f i) = c i)
    (b : Fin j → LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :
    ⇑(cokerCompEquiv hP).symm ∘ Fin.append c (⇑(projSeqPhi T P) ∘ b) =
      Fin.append (fun i => (LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).mkQ (f i))
        (fun k => (LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).mkQ (T (b k : E))) := by
  funext i
  induction i using Fin.addCases with
  | left i =>
    simp only [Function.comp_apply, Fin.append_left]
    rw [← hcf i]
    rfl
  | right i =>
    simp only [Function.comp_apply, Fin.append_right]
    rfl

/-- Lifts `f` of a family of cosets `c`. -/
theorem exists_lift {l : ℕ} (c : Fin l → F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)) :
    ∃ f : Fin l → F, ∀ i, (LinearMap.range (P : F →ₗ[ℝ] F)).mkQ (f i) = c i :=
  ⟨fun i => (Submodule.Quotient.mk_surjective _ (c i)).choose,
    fun i => (Submodule.Quotient.mk_surjective _ (c i)).choose_spec⟩

/-- **B's `γ` on a `Choice`**: a map with B's property `IsGamma` has the value (91) on the source
vector of every choice of `E(T,P)` in the project's sense. -/
theorem value_of_isGamma (_hT : T.IsFredholm) (hP : IsGoodLeftProj T P)
    [FiniteDimensional ℝ (LinearMap.ker (T : E →ₗ[ℝ] F))]
    [FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))]
    [FiniteDimensional ℝ (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F))]
    [FiniteDimensional ℝ (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F))]
    (g : fredholmDet T →ₗ[ℝ] fredholmDet (P ∘L T)) (hg : IsGamma T P g)
    (χ : (projSeq hP).Choice) :
    g χ.source = χ.wedgeB ⊗ₜ maxPowDualEquiv (cokerCompEquiv hP) (dualVec χ.wedgeC) := by
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    (cokerCompEquiv hP).symm.finiteDimensional
  obtain ⟨f, hf⟩ := exists_lift χ.c
  have hC : χ.l + χ.j =
      Module.finrank ℝ (F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    χ.hC.trans (cokerCompEquiv hP).finrank_eq.symm
  have hb : LinearIndependent ℝ (Fin.append (jMap T P ∘ ⇑χ.a) (χ.Z.subtype ∘ ⇑χ.b')) :=
    (wedge_ne_zero_iff χ.hB).1 χ.wedgeB_ne_zero
  have hw : LinearIndependent ℝ (Fin.append χ.c ((projSeq hP).β ∘ χ.Z.subtype ∘ ⇑χ.b')) :=
    (wedge_ne_zero_iff χ.hC).1 χ.wedgeC_ne_zero
  have hfd : ∀ i, (LinearMap.range (T : E →ₗ[ℝ] F)).mkQ (f i - P (f i)) = χ.d i := by
    intro i
    have := χ.γ_c i
    rw [← hf i] at this
    exact this
  have key := hg χ.n χ.l χ.j χ.a χ.d (χ.Z.subtype ∘ ⇑χ.b') f χ.n_eq χ.l_eq χ.hB hC
    χ.a.linearIndependent χ.d.linearIndependent hb hfd
  refine key.trans ?_
  change _ = _ ⊗ₜ maxPowDualEquiv (cokerCompEquiv hP) (dualVec (wedge
    (Fin.append χ.c ((projSeq hP).β ∘ χ.Z.subtype ∘ ⇑χ.b')) χ.hC))
  rw [maxPowDualEquiv_dualVec_symm _ hw χ.hC]
  congr 2
  exact wedge_congr (symm_comp_append hP f hf (χ.Z.subtype ∘ ⇑χ.b')).symm _ _

/-- `Φ_E` on the canonical choice: its definition (`smulRight (dualVec χ₀.source) χ₀.value`). -/
theorem phi_canonical {A' B' C' D' : Type} [AddCommGroup A'] [Module ℝ A'] [AddCommGroup B']
    [Module ℝ B'] [AddCommGroup C'] [Module ℝ C'] [AddCommGroup D'] [Module ℝ D']
    (S : FourTermExact A' B' C' D') [FiniteDimensional ℝ A'] [FiniteDimensional ℝ B']
    [FiniteDimensional ℝ C'] [FiniteDimensional ℝ D'] :
    S.phi S.canonicalChoice.source = S.canonicalChoice.value := by
  rw [FourTermExact.phi, LinearMap.smulRight_apply,
    dualVec_self FourTermExact.finrank_source S.canonicalChoice.source_ne_zero, one_smul]

/-- **B's `γ` is the project's `gammaProj`**: `gammaProj` is defined from the canonical choice
`χ₀` (`phi = smulRight (dualVec χ₀.source) χ₀.value`), so it agrees with `γ` on `χ₀.source`; both
are maps out of the line `det(T)`. -/
theorem gammaProj_eq_of_isGamma (hT : T.IsFredholm) (hP : IsGoodLeftProj T P)
    (g : fredholmDet T →ₗ[ℝ] fredholmDet (P ∘L T)) (hg : IsGamma T P g) :
    ((gammaProj hT hP : fredholmDet T ≃ₗ[ℝ] fredholmDet (P ∘L T)) :
      fredholmDet T →ₗ[ℝ] fredholmDet (P ∘L T)) = g := by
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have := hP.finite_coker
  have hk : FiniteDimensional ℝ (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    (hP.isFredholm_comp hT).finite_ker
  have hsrc := (projSeq hP).canonicalChoice.source_ne_zero
  have hval : (gammaProj hT hP) (projSeq hP).canonicalChoice.source =
      (projSeq hP).canonicalChoice.wedgeB ⊗ₜ maxPowDualEquiv (cokerCompEquiv hP)
        (dualVec (projSeq hP).canonicalChoice.wedgeC) := by
    have h0 := phi_canonical (projSeq hP)
    calc (gammaProj hT hP) (projSeq hP).canonicalChoice.source
        = TensorProduct.congr (LinearEquiv.refl ℝ _) (maxPowDualEquiv (cokerCompEquiv hP))
            ((projSeq hP).phi (projSeq hP).canonicalChoice.source) := rfl
      _ = TensorProduct.congr (LinearEquiv.refl ℝ _) (maxPowDualEquiv (cokerCompEquiv hP))
            (projSeq hP).canonicalChoice.value := by rw [h0]
      _ = _ := TensorProduct.congr_tmul _ _ _ _
  have h2 := value_of_isGamma hT hP g hg (projSeq hP).canonicalChoice
  apply LinearMap.ext
  intro w
  obtain ⟨r, rfl⟩ := exists_smul_eq_of_finrank_eq_one (L := fredholmDet T)
    (finrank_fredholmDet hT) hsrc w
  rw [map_smul, map_smul, LinearEquiv.coe_coe, hval, h2]

end Glue

theorem A_to_B : A → B := by
  intro hA E F _ _ _ _ _ _ T hT P hP
  have hT' := isFredholm_of_isFredholmOp hT
  have hP' := (isGLP_iff T P).1 hP
  refine ⟨gammaProj hT' hP', ?_⟩
  intro n l j a d b' f hn hl hj hC ha hd hb hf
  have key := hA.2 hT' hP' ha hn hd hl hb hj
    (c := fun i => (LinearMap.range (P : F →ₗ[ℝ] F)).mkQ (f i)) (fun i => hf i) hC
  refine key.trans ?_
  congr 2
  exact wedge_congr (symm_comp_append hP' f (fun _ => rfl) b') _ _

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · intro E F _ _ _ _ _ _ T P hT hP
    obtain ⟨γ, hγ⟩ := hB E F T (isFredholmOp_of_isFredholm hT) P ((isGLP_iff T P).2 hP)
    have heq := gammaProj_eq_of_isGamma hT hP _ hγ
    have := hT.finite_ker
    have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
    have := hP.finite_coker
    have := (hP.isFredholm_comp hT).finite_ker
    intro χ
    have h1 : gammaProj hT hP χ.source = γ χ.source := by
      rw [← LinearEquiv.coe_coe, heq]; rfl
    rw [h1]
    exact value_of_isGamma hT hP _ hγ χ
  · intro E F _ _ _ _ _ _ T P hT hP n l j a ha hn d hd hl b hb hj c hc hC
    obtain ⟨γ, hγ⟩ := hB E F T (isFredholmOp_of_isFredholm hT) P ((isGLP_iff T P).2 hP)
    have heq := gammaProj_eq_of_isGamma hT hP _ hγ
    obtain ⟨f, hf⟩ := exists_lift c
    have hfd : ∀ i, (LinearMap.range (T : E →ₗ[ℝ] F)).mkQ (f i - P (f i)) = d i := by
      intro i
      have := hc i
      rw [← hf i] at this
      exact this
    have h1 : gammaProj hT hP (wedge a hn ⊗ₜ dualVec (wedge d hl)) =
        γ (wedge a hn ⊗ₜ dualVec (wedge d hl)) := by
      rw [← LinearEquiv.coe_coe, heq]; rfl
    rw [h1]
    refine (hγ n l j a d b f hn hl hj hC ha hd hb hfd).trans ?_
    congr 2
    exact wedge_congr (symm_comp_append hP f hf b).symm _ _

#rt_check RoundTrip.V6_13.A_to_B [Polyfold.gammaProj_tmul, Polyfold.gammaProj_wedge_tmul]
#rt_check RoundTrip.V6_13.B_to_A [Polyfold.gammaProj_tmul, Polyfold.gammaProj_wedge_tmul]
#rt_overlap RoundTrip.V6_13.B_to_A [Polyfold.gammaProj_tmul, Polyfold.gammaProj_wedge_tmul]

/-! `B ⇒ A` does not use the choice-independence `lemma_6_3_3` of `Φ_E` (nor its family form
`phi_wedge_tmul`): that content comes from B. -/
#rt_check RoundTrip.V6_13.B_to_A [Polyfold.FourTermExact.lemma_6_3_3,
  Polyfold.FourTermExact.phi_wedge_tmul, Polyfold.FourTermExact.exists_smul_source_value]

end RoundTrip.V6_13
