import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_19

/-! Round trip for V6_19 (Definition 6.16, the determinant of a direct sum).

`A` is the conjunction of the types of the listed theorems `finrank_ker_prodMap`,
`finrank_coker_prodMap`, `isFredholm_prodMap`, `directSumVec_eq_smul`, `definition_6_4_16`,
`directSumDet_bijective` (universes at `0`); `kerInl`, `kerInr`, `cokerInl`, `cokerInr`,
`kerProdEquiv`, `cokerProdEquiv`, `directSumVec`, `directSumDet` are definitions (vocabulary; B uses
`kerInl` … `cokerInr` itself).

`A → B` (proved): `Ψ := directSumDet` (an equivalence by `directSumDet_bijective`); the formula is
`definition_6_4_16` (B's length proofs `hk`, `hc` agree with `directSumVec`'s by proof irrelevance).

`B → A` (proved): `T ⊕ S` Fredholm is B's first conjunct; the change-of-bases formula
`directSumVec_eq_smul` follows from B's basis-independent formula and the project lemma
`wedge_tmul_dualVec_eq_smul`; `directSumDet = Ψ` (both linear, equal on pure tensors since both
lines are spanned by the standard-basis vectors, where `directSumDet` is defined by the formula),
which gives `definition_6_4_16` and `directSumDet_bijective`.  The dimension identities
`finrank_ker_prodMap`, `finrank_coker_prodMap` are NOT in B (B takes them as hypotheses `hk`, `hc`
of its formula): they are proved directly here (`hk`, `hc`, two lines from `kerProdEquiv`,
`cokerProdEquiv`), without B.

Harness: A's statement mentions `directSumVec`, whose body passes the banned `finrank_ker_prodMap`,
`finrank_coker_prodMap` (not abstracted into a `_proof_N`) as the length proofs of its wedges, so
every term mentioning `A` fails `#rt_check` (recorded with `#guard_msgs`).  As in items V1_32 and
V2_24, a local `#rt_check_except_defs` runs the traversal with the body of `directSumVec` not
unfolded, and passes in both directions.
-/

namespace RoundTrip.V6_19
open Polyfold Module TensorProduct

/-- The project's statement (Definition 6.16 and its companions), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.finrank_ker_prodMap.{0, 0, 0, 0} ∧
  type_of% @Polyfold.finrank_coker_prodMap.{0, 0, 0, 0} ∧
  type_of% @Polyfold.isFredholm_prodMap.{0, 0, 0, 0} ∧
  type_of% @Polyfold.directSumVec_eq_smul.{0, 0, 0, 0} ∧
  type_of% @Polyfold.definition_6_4_16.{0, 0, 0, 0} ∧
  type_of% @Polyfold.directSumDet_bijective.{0, 0, 0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.finrank_ker_prodMap.{0, 0, 0, 0}, @Polyfold.finrank_coker_prodMap.{0, 0, 0, 0},
    @Polyfold.isFredholm_prodMap.{0, 0, 0, 0}, @Polyfold.directSumVec_eq_smul.{0, 0, 0, 0},
    @Polyfold.definition_6_4_16.{0, 0, 0, 0}, @Polyfold.directSumDet_bijective.{0, 0, 0, 0}⟩

/-- `A ⇒ B`: `Ψ` is the project's `directSumDet`, an equivalence by `directSumDet_bijective`. -/
theorem A_to_B : A → B := by
  intro hA E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS
  refine ⟨hA.2.2.1 T S hT hS, LinearEquiv.ofBijective (directSumDet hT hS)
    (hA.2.2.2.2.2 hT hS), fun a d a' d' hk hc => ?_⟩
  rw [LinearEquiv.ofBijective_apply, hA.2.2.2.2.1 hT hS a d a' d']
  rfl

section BtoA

variable {E F E' F' : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  (T : E →L[ℝ] F) (S : E' →L[ℝ] F')

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `dim ker T + dim ker S = dim ker(T ⊕ S)` (not in B, which takes it as the hypothesis `hk`;
proved directly from `kerProdEquiv`). -/
theorem hk (hT : T.IsFredholm) (hS : S.IsFredholm) :
    finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)) + finrank ℝ (LinearMap.ker (S : E' →ₗ[ℝ] F')) =
      finrank ℝ (LinearMap.ker ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F')) := by
  have := hT.finite_ker
  have := hS.finite_ker
  rw [← Module.finrank_prod, (kerProdEquiv T S).finrank_eq]

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `dim coker T + dim coker S = dim coker(T ⊕ S)` (not in B, which takes it as the hypothesis
`hc`; proved directly from `cokerProdEquiv`). -/
theorem hc (hT : T.IsFredholm) (hS : S.IsFredholm) :
    finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) +
        finrank ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')) =
      finrank ℝ ((F × F') ⧸ LinearMap.range
        ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F')) := by
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have : FiniteDimensional ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')) := hS.finite_coker
  rw [← Module.finrank_prod, (cokerProdEquiv T S).finrank_eq]

variable {T S}

set_option maxHeartbeats 1000000 in
/-- From B: a `Ψ` with `directSumVec a d a' d' = Ψ ((a ⊗ d*) ⊗ (a' ⊗ d'*))` for all bases, and
`directSumDet = Ψ` (both linear on the line `det T ⊗ det S`, equal at the standard bases, where
`directSumDet` is defined by the formula). -/
theorem exists_Psi (hB : B) (hT : T.IsFredholm) (hS : S.IsFredholm) :
    ∃ Ψ : TensorProduct ℝ (fredholmDet T) (fredholmDet S) ≃ₗ[ℝ] fredholmDet (T.prodMap S),
      (∀ (a : Module.Basis (Fin (Module.finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))) ℝ
              (LinearMap.ker (T : E →ₗ[ℝ] F)))
        (d : Module.Basis (Fin (Module.finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))) ℝ
              (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))
        (a' : Module.Basis (Fin (Module.finrank ℝ (LinearMap.ker (S : E' →ₗ[ℝ] F')))) ℝ
              (LinearMap.ker (S : E' →ₗ[ℝ] F')))
        (d' : Module.Basis (Fin (Module.finrank ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')))) ℝ
              (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F'))),
        directSumVec hT hS a d a' d' =
        Ψ ((wedge (⇑a) rfl ⊗ₜ[ℝ] dualVec (wedge (⇑d) rfl)) ⊗ₜ[ℝ]
          (wedge (⇑a') rfl ⊗ₜ[ℝ] dualVec (wedge (⇑d') rfl)))) ∧
      directSumDet hT hS = (Ψ : _ →ₗ[ℝ] _) := by
  obtain ⟨Ψ, hΨ⟩ := (hB T S hT hS).2
  have hΨ' : ∀ (a : Module.Basis (Fin (Module.finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))) ℝ
              (LinearMap.ker (T : E →ₗ[ℝ] F)))
        (d : Module.Basis (Fin (Module.finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))) ℝ
              (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))
        (a' : Module.Basis (Fin (Module.finrank ℝ (LinearMap.ker (S : E' →ₗ[ℝ] F')))) ℝ
              (LinearMap.ker (S : E' →ₗ[ℝ] F')))
        (d' : Module.Basis (Fin (Module.finrank ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')))) ℝ
              (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F'))), directSumVec hT hS a d a' d' =
      Ψ ((wedge (⇑a) rfl ⊗ₜ[ℝ] dualVec (wedge (⇑d) rfl)) ⊗ₜ[ℝ]
        (wedge (⇑a') rfl ⊗ₜ[ℝ] dualVec (wedge (⇑d') rfl))) :=
    fun a d a' d' => (hΨ a d a' d' (hk T S hT hS) (hc T S hT hS)).symm
  refine ⟨Ψ, hΨ', ?_⟩
  have := hT.finite_ker
  have := hS.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have : FiniteDimensional ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')) := hS.finite_coker
  let fa := Module.finBasis ℝ (LinearMap.ker (T : E →ₗ[ℝ] F))
  let fd := Module.finBasis ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))
  let fa' := Module.finBasis ℝ (LinearMap.ker (S : E' →ₗ[ℝ] F'))
  let fd' := Module.finBasis ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F'))
  have h0 : wedge fa rfl ⊗ₜ[ℝ] dualVec (wedge fd rfl) ≠ 0 :=
    tmul_ne_zero_of_ne_zero (wedge_basis_ne_zero fa)
      (dualVec_ne_zero finrank_maxPow (wedge_basis_ne_zero fd))
  have h0' : wedge fa' rfl ⊗ₜ[ℝ] dualVec (wedge fd' rfl) ≠ 0 :=
    tmul_ne_zero_of_ne_zero (wedge_basis_ne_zero fa')
      (dualVec_ne_zero finrank_maxPow (wedge_basis_ne_zero fd'))
  have hdet0 : directSumDet hT hS ((wedge fa rfl ⊗ₜ[ℝ] dualVec (wedge fd rfl)) ⊗ₜ[ℝ]
      (wedge fa' rfl ⊗ₜ[ℝ] dualVec (wedge fd' rfl))) = directSumVec hT hS fa fd fa' fd' := by
    simp only [directSumDet, TensorProduct.lift.tmul, LinearMap.compr₂_apply,
      LinearMap.compl₁₂_apply, LinearMap.mul_apply', LinearMap.toSpanSingleton_apply]
    rw [dualVec_self (finrank_fredholmDet hT) h0, dualVec_self (finrank_fredholmDet hS) h0',
      one_mul, one_smul]
  refine TensorProduct.ext' fun h h' => ?_
  obtain ⟨t, rfl⟩ := Polyfold.exists_smul_eq_of_finrank_eq_one (L := fredholmDet T)
    (finrank_fredholmDet hT) h0 h
  obtain ⟨t', rfl⟩ := Polyfold.exists_smul_eq_of_finrank_eq_one (L := fredholmDet S)
    (finrank_fredholmDet hS) h0' h'
  have h2 := hΨ' fa fd fa' fd'
  rw [TensorProduct.smul_tmul_smul, map_smul, map_smul, hdet0, h2]
  rfl

end BtoA

set_option maxHeartbeats 1000000 in
/-- `B ⇒ A`.  The dimension identities (`finrank_ker_prodMap`, `finrank_coker_prodMap`) are not in
B (B takes them as hypotheses `hk`, `hc`); they are proved directly (`hk`, `hc` above).  The rest
comes from B: `T ⊕ S` Fredholm; the change of bases from the basis-independence of B's formula;
`definition_6_4_16` and `directSumDet_bijective` from `directSumDet = Ψ`. -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun T S hT hS => hk T S hT hS, fun T S hT hS => hc T S hT hS,
    fun T S hT hS => (hB T S hT hS).1, ?_, ?_, ?_⟩
  · intro E F _ _ _ _ _ _ E' F' _ _ _ _ _ _ T S hT hS a a₀ d d₀ a' a₀' d' d₀'
    obtain ⟨Ψ, hΨ, -⟩ := exists_Psi hB hT hS
    have := hT.finite_ker
    have := hS.finite_ker
    have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
    have : FiniteDimensional ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')) := hS.finite_coker
    have e1 := wedge_tmul_dualVec_eq_smul a a₀ d d₀
    have e2 := wedge_tmul_dualVec_eq_smul a' a₀' d' d₀'
    have e3 : (wedge (⇑a) rfl ⊗ₜ[ℝ] dualVec (wedge (⇑d) rfl)) ⊗ₜ[ℝ]
        (wedge (⇑a') rfl ⊗ₜ[ℝ] dualVec (wedge (⇑d') rfl)) =
        ((a₀.det a * (d₀.det d)⁻¹) * (a₀'.det a' * (d₀'.det d')⁻¹)) •
          ((wedge (⇑a₀) rfl ⊗ₜ[ℝ] dualVec (wedge (⇑d₀) rfl)) ⊗ₜ[ℝ]
            (wedge (⇑a₀') rfl ⊗ₜ[ℝ] dualVec (wedge (⇑d₀') rfl))) := by
      rw [e1, e2, TensorProduct.smul_tmul_smul]
    have h1 := hΨ a d a' d'
    have h2 := hΨ a₀ d₀ a₀' d₀'
    have h3 := congrArg Ψ e3
    rw [map_smul] at h3
    refine h1.trans (h3.trans ?_)
    rw [← h2, mul_inv]
    congr 1
    ring
  · intro E F _ _ _ _ _ _ E' F' _ _ _ _ _ _ T S hT hS a d a' d'
    obtain ⟨Ψ, hΨ, hD⟩ := exists_Psi hB hT hS
    rw [hD, hΨ]
    rfl
  · intro E F _ _ _ _ _ _ E' F' _ _ _ _ _ _ T S hT hS
    obtain ⟨Ψ, -, hD⟩ := exists_Psi hB hT hS
    have h' : ⇑(directSumDet hT hS) = ⇑Ψ := congrArg DFunLike.coe hD
    rw [h']
    exact Ψ.bijective

open Lean Elab Command in
/-- `#rt_check_except_defs T [d₁, …] [n₁, …]` (as in items V1_32, V2_24): the harness traversal
`rtCollect` with the bodies of the definitions `dᵢ` not unfolded; fails if the proof of `T` reaches
some `nᵢ` elsewhere. -/
elab "#rt_check_except_defs " t:ident " [" ds:ident,* "]" " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let seen := ds.getElems.foldl (fun s d => s.insert d.getId) NameSet.empty
  let used := rtCollect env roots.toList seen
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do throwError "FAIL: {t.getId} uses {bad} outside the bodies of the definitions"
  logInfo m!"OK: {t.getId} reaches the banned declarations only through the bodies of the definitions {ds.getElems.toList.map (·.getId)}"

-- Neither direction can pass `#rt_check`: A's statement mentions `directSumVec`, whose body passes
-- the banned `finrank_ker_prodMap`, `finrank_coker_prodMap` (non-abstracted) as the length proofs of
-- its two wedges; `#rt_check_soft` does not help (not a `_proof_N`).
/-- error: rt_check FAIL: RoundTrip.V6_19.A_to_B uses [Polyfold.finrank_ker_prodMap, Polyfold.finrank_coker_prodMap] -/
#guard_msgs in
#rt_check RoundTrip.V6_19.A_to_B [Polyfold.finrank_ker_prodMap, Polyfold.finrank_coker_prodMap,
  Polyfold.isFredholm_prodMap, Polyfold.directSumVec_eq_smul, Polyfold.definition_6_4_16,
  Polyfold.directSumDet_bijective]
/-- error: rt_check FAIL: RoundTrip.V6_19.B_to_A uses [Polyfold.finrank_ker_prodMap, Polyfold.finrank_coker_prodMap] -/
#guard_msgs in
#rt_check RoundTrip.V6_19.B_to_A [Polyfold.finrank_ker_prodMap, Polyfold.finrank_coker_prodMap,
  Polyfold.isFredholm_prodMap, Polyfold.directSumVec_eq_smul, Polyfold.definition_6_4_16,
  Polyfold.directSumDet_bijective]
#rt_check_except_defs RoundTrip.V6_19.A_to_B [Polyfold.directSumVec] [Polyfold.finrank_ker_prodMap, Polyfold.finrank_coker_prodMap,
  Polyfold.isFredholm_prodMap, Polyfold.directSumVec_eq_smul, Polyfold.definition_6_4_16,
  Polyfold.directSumDet_bijective]
#rt_check_except_defs RoundTrip.V6_19.B_to_A [Polyfold.directSumVec] [Polyfold.finrank_ker_prodMap, Polyfold.finrank_coker_prodMap,
  Polyfold.isFredholm_prodMap, Polyfold.directSumVec_eq_smul, Polyfold.definition_6_4_16,
  Polyfold.directSumDet_bijective]
#rt_overlap RoundTrip.V6_19.B_to_A [Polyfold.finrank_ker_prodMap, Polyfold.finrank_coker_prodMap,
  Polyfold.isFredholm_prodMap, Polyfold.directSumVec_eq_smul, Polyfold.definition_6_4_16,
  Polyfold.directSumDet_bijective]

end RoundTrip.V6_19
