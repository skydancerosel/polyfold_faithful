import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_45

/-! Round trip for V6_45 (Lemma 6.33: adding sections does not change the push-forward).

A is the conjunction of the types of the project's theorems for the item (the linear algebra of
`AddSections.lean` and `IsStabKernels.push_append`), universes at `0`.  B is the blind reading:
appending sc⁺-sections `s̄₁, …, s̄_l` to choices with (P) does not change the unsigned push-forward
`Facts.push` (read in one chart).  `A ⇒ B` uses the conjunct `propagate_append`: the operators
`T_t` of the two readings are equal, the stabilization of the enlarged choices is
`appendStab φ_t ψ_t`, and the three side conditions of `propagate_append` (`(v, λ) ↦ (v, λ ++ 0)`
maps `L_t` into `L'_t`, the projection of `L'_t` to the added coordinates is onto, `dim L' =
dim L + l`) are checked from the surjectivity of `T_t ⊕ φ_t`.  The orientation steps
`orEquivRay` at the two end points are the same on both sides, so the missing sign of B is
irrelevant here.
-/

namespace RoundTrip.V6_45
open Polyfold

/-- The project's statement: the theorems of the item, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.wedgeExt_wedge.{0, 0} ∧
  type_of% @Polyfold.wedgeExt_congr.{0, 0} ∧
  type_of% @Polyfold.wedgeExt_bijective.{0, 0} ∧
  type_of% @Polyfold.detEquiv_stabIota_append.{0, 0} ∧
  type_of% @Polyfold.SubspaceFamily.exists_continuous_lifts.{0, 0} ∧
  type_of% @Polyfold.isLineOrientation_wedgeExt.{0, 0, 0} ∧
  type_of% @Polyfold.stabRayEquiv_append.{0, 0, 0} ∧
  type_of% @Polyfold.propagate_append.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.IsStabKernels.push_append.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.wedgeExt_wedge.{0, 0}, @Polyfold.wedgeExt_congr.{0, 0},
    @Polyfold.wedgeExt_bijective.{0, 0}, @Polyfold.detEquiv_stabIota_append.{0, 0},
    @Polyfold.SubspaceFamily.exists_continuous_lifts.{0, 0},
    @Polyfold.isLineOrientation_wedgeExt.{0, 0, 0}, @Polyfold.stabRayEquiv_append.{0, 0, 0},
    @Polyfold.propagate_append.{0, 0, 0, 0, 0, 0}, @Polyfold.IsStabKernels.push_append.{0, 0, 0}⟩

/-! ### Glue -/

/-- `μ ↦ 0 ++ μ`, `ℝˡ → ℝ^{k+l}`. -/
noncomputable def appendLeftZero (k l : ℕ) : (Fin l → ℝ) →L[ℝ] (Fin (k + l) → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    Fin.addCases (motive := fun _ => (Fin l → ℝ) →L[ℝ] ℝ) (fun _ => 0)
      (fun j => ContinuousLinearMap.proj j) i

theorem appendLeftZero_apply {k l : ℕ} (μ : Fin l → ℝ) :
    appendLeftZero k l μ = Fin.append 0 μ := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp [appendLeftZero]

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  {B : StrongBundle PX P} {hπ : SndSmooth PX} {f : X → Y} {γ : (Fin 1 → ℝ) → X}
  {c : StrongBundleChart PX P} {hc : B.IsChart c} {hγ : ∀ t : J, γ t ∈ c.φ.source}
  {z : J → c.φ.model.E.lvl 1}
  {hz : ∀ t, c.φ.model.E.toBase 1 (z t) = c.φ.toPartialEquiv (γ t)}

/-- The operators `T_t` of the enlarged choices are those of the original ones. -/
theorem T_eq {k l : ℕ} {D : Choices B hπ f γ k} (R : Reading c hc hγ z hz D)
    {sb : Fin l → (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    {hsb : ∀ j, (B.pullback (hπ 1)).IsScPlusSection (sb j)}
    (R' : Reading c hc hγ z hz (D.append sb hsb)) (t : J) : R'.T t = R.T t := by
  ext v
  exact (R'.hT t v).trans (R.hT t v).symm

/-- The stabilization of the enlarged choices is `appendStab φ_t ψ_t`. -/
theorem Φ_eq {k l : ℕ} {D : Choices B hπ f γ k} (R : Reading c hc hγ z hz D)
    {sb : Fin l → (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    {hsb : ∀ j, (B.pullback (hπ 1)).IsScPlusSection (sb j)}
    (R' : Reading c hc hγ z hz (D.append sb hsb)) (t : J) :
    R'.Φ t = appendStab (R.Φ t) ((R'.Φ t).comp (appendLeftZero k l)) := by
  ext μ
  simp only [appendStab, add_apply, ContinuousLinearMap.comp_apply,
    Submodule.coe_add, R'.hΦ, R.hΦ, appendLeftZero_apply]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp [Choices.append]

/-- **Adding sections, at the level of `Facts.push`**, from `propagate_append`. -/
theorem push_append_eq
    (hpa : type_of% @Polyfold.propagate_append.{0, 0, 0, 0, 0, 0})
    (hf : B.IsScFredholmSection f) {k l : ℕ} {D : Choices B hπ f γ k}
    {R : Reading c hc hγ z hz D} (F : Facts c hc hγ z hz R) {D' : Choices B hπ f γ (k + l)}
    {R' : Reading c hc hγ z hz D'} (F' : Facts c hc hγ z hz R')
    (ψ : ∀ t : J, (Fin l → ℝ) →L[ℝ] (cp c hc hγ z hz t).K)
    (hT : ∀ t, R'.T t = R.T t) (hΦ : ∀ t, R'.Φ t = appendStab (R.Φ t) (ψ t)) :
    F'.push hf = F.push hf := by
  obtain ⟨T', hT', Φ', hΦ'⟩ := R'
  obtain rfl : T' = R.T := funext hT
  obtain rfl : Φ' = fun t => appendStab (R.Φ t) (ψ t) := funext hΦ
  -- the side conditions of `propagate_append`
  have hM : ∀ q, ∀ v ∈ F.Λ.L q,
      ((v.1, Fin.append v.2 0) : c.φ.model.E.lvl 0 × (Fin (k + l) → ℝ)) ∈ F'.Λ.L q := by
    intro q v hv
    rw [F.hΛ q] at hv
    rw [F'.hΛ q]
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv
    refine Submodule.mem_map.2 ⟨(w.1, Fin.append w.2 0), ?_, rfl⟩
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coprod_apply] at hw ⊢
    rw [appendStab_append, map_zero, add_zero]
    exact hw
  have hp : ∀ q, (F'.Λ.L q).map (((restrictNatAdd k l).comp
      (ContinuousLinearMap.snd ℝ (c.φ.model.E.lvl 0) (Fin (k + l) → ℝ)) :
        c.φ.model.E.lvl 0 × (Fin (k + l) → ℝ) →L[ℝ] Fin l → ℝ) :
          c.φ.model.E.lvl 0 × (Fin (k + l) → ℝ) →ₗ[ℝ] Fin l → ℝ) = ⊤ := by
    intro q
    refine eq_top_iff.2 fun μ _ => ?_
    obtain ⟨w, hw⟩ := F.surj q (-(ψ q μ))
    refine ⟨((w.1 : c.φ.model.E.lvl 0), Fin.append w.2 μ), ?_, ?_⟩
    · rw [F'.hΛ q]
      refine Submodule.mem_map.2 ⟨(w.1, Fin.append w.2 μ), ?_, rfl⟩
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.coprod_apply] at hw ⊢
      rw [appendStab_append, ← add_assoc, hw, neg_add_cancel]
    · simp
  have hn : F.Λ.n + l = F'.Λ.n := by
    rw [← F.Λ.finrank_eq iccZero, ← F'.Λ.finrank_eq iccZero, F.hΛ iccZero, F'.hΛ iccZero]
    rw [← (Submodule.equivMapOfInjective _ (prodMap_id_injective
        (cp c hc hγ z hz iccZero).T.subtypeL Subtype.val_injective) _).finrank_eq,
      ← (Submodule.equivMapOfInjective _ (prodMap_id_injective
        (cp c hc hγ z hz iccZero).T.subtypeL Subtype.val_injective) _).finrank_eq]
    exact finrank_ker_appendStab (F.fred iccZero) (F.surj iccZero)
  refine Equiv.ext fun o => ?_
  simp only [Facts.push, Equiv.trans_apply]
  exact congrArg _ (hpa F.Λ F'.Λ hM hp hn iccZero iccOne (F.fred _) (F.surj _) _
    Subtype.val_injective (F.hΛ _) (F'.hΛ _) (F.fred _) (F.surj _) _ Subtype.val_injective
    (F.hΛ _) (F'.hΛ _) _)

end Glue

/-- `A ⇒ B`, from the conjunct `propagate_append` of A. -/
theorem A_to_B : A → B := by
  intro hA
  obtain ⟨-, -, -, -, -, -, -, hpa, -⟩ := hA
  intro X _ _ _ PX Y _ _ _ P _ _ _ _ B hπ _hX f hf γ _hγs c hc hγ z hz k D _hD R F l sb hsb R' F'
  exact (push_append_eq hpa hf F F' (fun t => (R'.Φ t).comp (appendLeftZero k l))
    (T_eq R R') (Φ_eq R R')).symm

/-! `B ⇒ A` is not proved.  A contains the general linear algebra of adding sections
(`wedgeExt` and its bijectivity, `detEquiv_stabIota_append`, `exists_continuous_lifts`,
`isLineOrientation_wedgeExt`, `stabRayEquiv_append`, `propagate_append` for arbitrary families
`Λ ⊆ V × ℝᵏ`, `Λ' ⊆ V × ℝ^{k+d}` over any simply connected, locally path-connected base) and the
version `IsStabKernels.push_append` for the signed push-forward along any parameter space; B is
the single application along `[0, 1]` in a chart.  Recovering A from B would mean re-proving that
linear algebra. -/

#rt_check RoundTrip.V6_45.A_to_B [Polyfold.wedgeExt_wedge, Polyfold.wedgeExt_congr,
  Polyfold.wedgeExt_bijective, Polyfold.detEquiv_stabIota_append,
  Polyfold.SubspaceFamily.exists_continuous_lifts, Polyfold.isLineOrientation_wedgeExt,
  Polyfold.stabRayEquiv_append, Polyfold.propagate_append, Polyfold.IsStabKernels.push_append]

end RoundTrip.V6_45
