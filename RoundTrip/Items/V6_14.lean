import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_14

/-!
Round trip for V6_14 (Proposition 6.12).  `A` is
`proposition_6_4_11 ∧ IsGoodLeftProj.of_projLE ∧ comp_comp_eq_of_projLE` (universes at `0`).

**The statement of A mentions two of the banned theorems.**  `proposition_6_4_11` is stated with
`gammaProj (hQ.isFredholm_comp hT) (hP.of_projLE hPQ)` and
`linDetEquivOfEq (congrArg _ (comp_comp_eq_of_projLE hPQ))`: the proofs `of_projLE` and
`comp_comp_eq_of_projLE` occur inside A's statement.  So every term mentioning A (in particular
`A_to_B` and `B_to_A`) reaches them, and `#rt_check` with the full banned list cannot pass
(recorded with `#guard_msgs` below).  As in V2_53/V2_61 we therefore go through `A'`: A with
those proof arguments abstracted (`∀ hQT hP' heq, …`; equal to A's by proof irrelevance,
`A_to_A'`, `A'_to_A`).  `A'_to_B` and `B_to_A'` pass `#rt_check` with the full list, and
`A_to_B`, `B_to_A` pass it with `proposition_6_4_11` banned.

Glue (copied from our V6_13, since B's `IsGamma` is a separate constant here):
* `gammaProj_eq_of_isGamma`: a map with B's `IsGamma` (formula (91) for every choice) IS the
  project's `gammaProj` (`gammaProj` unfolds, at the canonical choice, to (91); `det(T)` is a
  line).  This uses only B-side information plus the definition of `gammaProj`.
* `isGamma_gammaProj`: `gammaProj` has B's property, from `gammaProj_wedge_tmul` (V6_13's
  theorem, not banned here).

Then `A' ⇒ B`: B's three `γ`s are `gammaProj`s, and A's composition law is B's.  `B ⇒ A'`: B
applied to the three `gammaProj`s gives A's composition law; `Q T` Fredholm and `P ∈ Π_{QT}`
come from B.  The two helper conjuncts `of_projLE` (`P ≤ Q`, `P ∈ Π_T` ⇒ `P ∈ Π_{QT}`, for any `T`)
and `comp_comp_eq_of_projLE` (`P(QT) = PT`) are proved directly (two lines of algebra, without
B); `of_projLE` is more general than B's clause (no Fredholm hypothesis on `T`, `Q` not assumed in
`Π_T`).
-/

namespace RoundTrip.V6_14
open Polyfold TensorProduct

/-- The project's statement (Proposition 6.12 and its two helper lemmas), universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.proposition_6_4_11.{0, 0} ∧
  type_of% @Polyfold.IsGoodLeftProj.of_projLE.{0, 0} ∧
  type_of% @Polyfold.comp_comp_eq_of_projLE.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.proposition_6_4_11, @Polyfold.IsGoodLeftProj.of_projLE,
    @Polyfold.comp_comp_eq_of_projLE⟩

/-- A with the proof arguments `hQ.isFredholm_comp hT`, `hP.of_projLE hPQ` and
`congrArg _ (comp_comp_eq_of_projLE hPQ)` of its statement abstracted. -/
def A' : Prop :=
  (∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {T : E →L[ℝ] F} {P Q : F →L[ℝ] F}
    (hT : T.IsFredholm) (hP : IsGoodLeftProj T P) (hQ : IsGoodLeftProj T Q), ProjLE P Q →
      (Q ∘L T).IsFredholm ∧ IsGoodLeftProj (Q ∘L T) P ∧
      ∀ (hQT : (Q ∘L T).IsFredholm) (hP' : IsGoodLeftProj (Q ∘L T) P)
        (heq : ((P ∘L (Q ∘L T) : E →L[ℝ] F) : E →ₗ[ℝ] F) = ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F))
        (h : fredholmDet T),
        linDetEquivOfEq heq (gammaProj hQT hP' (gammaProj hT hQ h)) = gammaProj hT hP h) ∧
  type_of% @Polyfold.IsGoodLeftProj.of_projLE.{0, 0} ∧
  type_of% @Polyfold.comp_comp_eq_of_projLE.{0, 0}

theorem A_to_A' : A → A' := fun hA =>
  ⟨fun hT hP hQ hPQ => ⟨(hA.1 hT hP hQ hPQ).1, (hA.1 hT hP hQ hPQ).2.1,
    fun _ _ _ h => (hA.1 hT hP hQ hPQ).2.2 h⟩, hA.2.1, hA.2.2⟩

theorem A'_to_A : A' → A := fun hA =>
  ⟨fun hT hP hQ hPQ => ⟨(hA.1 hT hP hQ hPQ).1, (hA.1 hT hP hQ hPQ).2.1,
    fun h => (hA.1 hT hP hQ hPQ).2.2 _ _ _ h⟩, hA.2.1, hA.2.2⟩

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

/-- `gammaProj` has B's property (formula (91) for every family choice), by
`gammaProj_wedge_tmul` (V6_13's theorem). -/
theorem isGamma_gammaProj (hT : T.IsFredholm) (hP : IsGoodLeftProj T P) :
    IsGamma T P ((gammaProj hT hP : fredholmDet T ≃ₗ[ℝ] fredholmDet (P ∘L T)) :
      fredholmDet T →ₗ[ℝ] fredholmDet (P ∘L T)) := by
  intro n l j a d b' f hn hl hj hC ha hd hb hf
  have key := Polyfold.gammaProj_wedge_tmul hT hP ha hn hd hl hb hj
    (c := fun i => (LinearMap.range (P : F →ₗ[ℝ] F)).mkQ (f i)) (fun i => hf i) hC
  refine key.trans ?_
  congr 2
  exact wedge_congr (symm_comp_append hP f (fun _ => rfl) b') _ _

/-- `P(QT) = PT` for `P ≤ Q` (proved here). -/
theorem comp_comp_of_le {Q : F →L[ℝ] F} (hPQ : ProjLE P Q) : P ∘L (Q ∘L T) = P ∘L T := by
  rw [← ContinuousLinearMap.comp_assoc, ← hPQ.1]

end Glue

theorem A'_to_B : A' → B := by
  intro hA E F _ _ _ _ _ _ T hT Q P hQ hP hle
  have hT' := isFredholm_of_isFredholmOp hT
  have hQ' := (isGLP_iff T Q).1 hQ
  have hP' := (isGLP_iff T P).1 hP
  obtain ⟨hQT, hP'', hcomp⟩ := hA.1 hT' hP' hQ' hle
  refine ⟨isFredholmOp_of_isFredholm hQT, (isGLP_iff _ P).2 hP'', ?_⟩
  intro γQT γPQT γPT h1 h2 h3
  rw [← gammaProj_eq_of_isGamma hT' hQ' γQT h1, ← gammaProj_eq_of_isGamma hQT hP'' γPQT h2,
    ← gammaProj_eq_of_isGamma hT' hP' γPT h3]
  apply LinearMap.ext
  intro h
  exact hcomp hQT hP''
    (congrArg (fun A : E →L[ℝ] F => (A : E →ₗ[ℝ] F)) (comp_comp_of_le (T := T) hle)) h

theorem B_to_A' : B → A' := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro E F _ _ _ _ _ _ T P Q hT hP hQ hPQ
    obtain ⟨hQT, hP'', hcomp⟩ := hB E F T (isFredholmOp_of_isFredholm hT) Q P
      ((isGLP_iff T Q).2 hQ) ((isGLP_iff T P).2 hP) hPQ
    refine ⟨isFredholm_of_isFredholmOp hQT, (isGLP_iff _ P).1 hP'', fun hQT2 hP2 heq h => ?_⟩
    have := hcomp _ _ _ (isGamma_gammaProj hT hQ) (isGamma_gammaProj hQT2 hP2)
      (isGamma_gammaProj hT hP)
    exact LinearMap.congr_fun this h
  · intro E F _ _ _ _ _ _ T P Q hP hPQ
    exact ⟨hP.isProj, hP.finite_coker, by rw [comp_comp_of_le hPQ]; exact hP.range_comp⟩
  · intro E F _ _ _ _ _ _ T P Q hPQ
    exact comp_comp_of_le hPQ

theorem A_to_B : A → B := fun hA => A'_to_B (A_to_A' hA)

theorem B_to_A : B → A := fun hB => A'_to_A (B_to_A' hB)

/-! With the full banned list, `A_to_B` and `B_to_A` fail only because A's statement contains
`of_projLE` and `comp_comp_eq_of_projLE` (see the header); `A'_to_B` and `B_to_A'` pass. -/

#rt_check RoundTrip.V6_14.A'_to_B [Polyfold.proposition_6_4_11, Polyfold.IsGoodLeftProj.of_projLE,
  Polyfold.comp_comp_eq_of_projLE]
#rt_check RoundTrip.V6_14.B_to_A' [Polyfold.proposition_6_4_11, Polyfold.IsGoodLeftProj.of_projLE,
  Polyfold.comp_comp_eq_of_projLE]
#rt_check RoundTrip.V6_14.A_to_B [Polyfold.proposition_6_4_11]
#rt_check RoundTrip.V6_14.B_to_A [Polyfold.proposition_6_4_11]
/--
error: rt_check FAIL: RoundTrip.V6_14.A_to_B uses [Polyfold.IsGoodLeftProj.of_projLE, Polyfold.comp_comp_eq_of_projLE]
-/
#guard_msgs in
#rt_check RoundTrip.V6_14.A_to_B [Polyfold.proposition_6_4_11, Polyfold.IsGoodLeftProj.of_projLE,
  Polyfold.comp_comp_eq_of_projLE]
/--
error: rt_check FAIL: RoundTrip.V6_14.B_to_A uses [Polyfold.IsGoodLeftProj.of_projLE, Polyfold.comp_comp_eq_of_projLE]
-/
#guard_msgs in
#rt_check RoundTrip.V6_14.B_to_A [Polyfold.proposition_6_4_11, Polyfold.IsGoodLeftProj.of_projLE,
  Polyfold.comp_comp_eq_of_projLE]
#rt_overlap RoundTrip.V6_14.B_to_A' [Polyfold.proposition_6_4_11,
  Polyfold.IsGoodLeftProj.of_projLE, Polyfold.comp_comp_eq_of_projLE]

end RoundTrip.V6_14
