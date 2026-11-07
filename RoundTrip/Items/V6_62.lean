import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_62

/-!
# V6_62 (Remark 6.42 at a point): B is false, and A ⇒ ¬B

* **A** is the conjunction of the sixteen theorems of the row (universes at `0`).  The project
  orients `DET(f̂, (t, x))` through the sign-normalized `extDetN = (−1)^{dim coker L} · extDet`
  (`existsUnique_prodOr`); `isLineOrientation_extPull` is the continuity of `extDetN`.
* **B** asks for an orientation `ô` of `DET(f̂, (t, x))` with `ô(L̂) = [extDet-conjugate of ω(L)]`
  for EVERY `L ∈ Lin(f, x)`, with the text's `h ↦ h̃` WITHOUT the sign.
* **`A_to_not_B : A → ¬ B`** (the blind author's prediction, made precise).  Counterexample: the
  trivial bundle `ℝ¹ × ℝ¹ → ℝ¹`, `f = 0` (sc-Fredholm, `isScFredholmSection_graphSection`), the
  translation chart at `x = 0`, `t = 0`, `S = 0`.  `Lin(f, 0)` contains `L₀ = 0` (from `s = 0`,
  `dim coker = 1`) and `L₁ = id` (from `s = graph id`, onto).  Given B's `ô`, conjugate it back
  (`LineOrientation.conj`) and pull it back along `extDetN` (`extPullRay`, an orientation by A's
  `isLineOrientation_extPull`): the result `Φ` has `Φ(L) = (−1)^{dim coker L} · ω(L)`
  (`conjDet ∘ conjDet⁻¹ = id`, `extDetN⁻¹ ∘ extDet = (−1)^{dim coker}`).  `Φ = ω` at `L₁`, so
  everywhere (`Lin(f, 0)` is convex), but `Φ(L₀) = −ω(L₀)`.
* `not_B := A_to_not_B A_holds`; `not_A_to_B`; `B_to_A` ex falso.
* What the refutation uses from A: only the continuity of `extDetN` (component 8, through `hA`).
  An A-free refutation would need the chart coordinates of `extDet` (`coord_extDet`, Proposition
  6.24 machinery), i.e. re-proving that continuity.
-/

namespace RoundTrip.V6_62
open Polyfold

/-- The project's statement (the theorems of the comparison row), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.isFredholm_extOp.{0, 0} ∧
  type_of% @Polyfold.finrank_ker_extOp.{0, 0} ∧
  type_of% @Polyfold.range_extOp.{0, 0} ∧
  type_of% @Polyfold.extDet_wedge_tmul.{0, 0} ∧
  type_of% @Polyfold.extDetN_eq_of_surjective.{0, 0} ∧
  type_of% @Polyfold.coord_extDet.{0, 0} ∧
  type_of% @Polyfold.coord_extDetN.{0, 0} ∧
  type_of% @Polyfold.isLineOrientation_extPull.{0, 0} ∧
  type_of% @Polyfold.existsUnique_extConjOr.{0, 0, 0, 0} ∧
  type_of% @Polyfold.ChartPoint.mem_prodPt_T_iff.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.mem_prodPt_K_iff.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.IsScPlusOp.prodPt.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.prodLin_mem_linSet.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.existsUnique_prodOr.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.prodOr_apply.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.prodOr_injective.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.isFredholm_extOp.{0, 0},
   @Polyfold.finrank_ker_extOp.{0, 0},
   @Polyfold.range_extOp.{0, 0},
   @Polyfold.extDet_wedge_tmul.{0, 0},
   @Polyfold.extDetN_eq_of_surjective.{0, 0},
   @Polyfold.coord_extDet.{0, 0},
   @Polyfold.coord_extDetN.{0, 0},
   @Polyfold.isLineOrientation_extPull.{0, 0},
   @Polyfold.existsUnique_extConjOr.{0, 0, 0, 0},
   @Polyfold.ChartPoint.mem_prodPt_T_iff.{0, 0},
   @Polyfold.ChartPoint.mem_prodPt_K_iff.{0, 0},
   @Polyfold.ChartPoint.IsScPlusOp.prodPt.{0, 0},
   @Polyfold.ChartPoint.prodLin_mem_linSet.{0, 0},
   @Polyfold.ChartPoint.existsUnique_prodOr.{0, 0},
   @Polyfold.ChartPoint.prodOr_apply.{0, 0},
   @Polyfold.ChartPoint.prodOr_injective.{0, 0}⟩

section General

variable {E F E' F' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']

/-- `det(A, Γ) ∘ det(A⁻¹, Γ⁻¹) = id`. -/
theorem conjDet_conjDet_symm (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F') {S : E →L[ℝ] F}
    {S' : E' →L[ℝ] F'} (h : ∀ v, S' (A v) = Γ (S v)) (h' : ∀ v, S (A.symm v) = Γ.symm (S' v))
    (x : fredholmDet S') : conjDet A Γ h (conjDet A.symm Γ.symm h' x) = x := by
  have h'' : ∀ v, S' ((A.symm.trans A) v) = (Γ.symm.trans Γ) (S' v) := fun v => by simp
  have e := conjDet_trans A.symm Γ.symm A Γ h' h h''
  rw [← LinearEquiv.trans_apply, e]
  have hr : ∀ v, S' (ContinuousLinearEquiv.refl ℝ E' v) =
      ContinuousLinearEquiv.refl ℝ F' (S' v) := fun _ => rfl
  rw [conjDet_congr (A₂ := ContinuousLinearEquiv.refl ℝ E') (Γ₂ := ContinuousLinearEquiv.refl ℝ F')
    (fun v => by simp) (fun y => by simp) h'' hr, conjDet_refl, linDetEquivOfEq_self]
  rfl

/-- `extDetN⁻¹ ∘ extDet = (−1)^{dim coker L}`. -/
theorem extDetFiber_symm_extDet {L : E →L[ℝ] F} (hL : L.IsFredholm) (hL' : (extOp L).IsFredholm)
    (y : fredholmDet L) :
    (extDetFiber (S := ⟨L, hL⟩) (S' := ⟨extOp L, hL'⟩) rfl).symm (extDet hL y) =
      ((stabSign L)⁻¹ : ℝˣ) • y := by
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  change extDet hL y = extDetFiber (S := ⟨L, hL⟩) (S' := ⟨extOp L, hL'⟩) rfl
    (((stabSign L)⁻¹ : ℝˣ) • y)
  rw [extDetFiber_rfl_apply, extDetN_apply, Units.smul_def]
  have e1 : extDet hL ((((stabSign L)⁻¹ : ℝˣ) : ℝ) • y) =
      (((stabSign L)⁻¹ : ℝˣ) : ℝ) • extDet hL y := (extDet hL).map_smul _ _
  rw [e1]
  have key : ∀ {M : Type} [AddCommGroup M] [Module ℝ M] (z : M) (u : ℝˣ),
      z = (u : ℝ) • ((u⁻¹ : ℝˣ) : ℝ) • z := fun z u => by
    rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  exact key (M := fredholmDet (extOp L)) _ _

/-- `Ray.map` of a scalar multiplication by a unit. -/
theorem ray_map_units_smul {M : Type} [AddCommMonoid M] [Module ℝ M] (e : M ≃ₗ[ℝ] M) (u : ℝˣ)
    (he : ∀ x, e x = u • x) (r : Module.Ray ℝ M) : Module.Ray.map e r = u • r := by
  induction r using Module.Ray.ind with
  | h v hv =>
    rw [Module.Ray.map_apply, smul_rayOfNeZero]
    congr 1
    exact he v

/-- A negative unit moves every ray (over a module given only as an `AddCommMonoid`). -/
theorem units_smul_ne_self {M : Type} [AddCommMonoid M] [Module ℝ M] (u : ℝˣ) (hu : (u : ℝ) < 0)
    (r : Module.Ray ℝ M) : u • r ≠ r := by
  induction r using Module.Ray.ind with
  | h v hv =>
    intro h
    have hu0 : u • v ≠ 0 := fun h0 => hv (by
      have := congrArg (fun w => (u⁻¹ : ℝˣ) • w) h0
      simpa using this)
    rw [smul_rayOfNeZero, ray_eq_iff hu0 hv] at h
    rcases h with h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩
    · exact hu0 h
    · exact hv h
    · rw [Units.smul_def, smul_smul] at h
      -- `(r₂ - r₁ u) • v = 0` with `r₂ - r₁ u > 0`
      have hpos : 0 < r₂ - r₁ * (u : ℝ) := by nlinarith
      have h0 : (r₂ - r₁ * (u : ℝ)) • v = 0 := by
        rw [sub_eq_add_neg, add_smul, ← h, ← add_smul, add_neg_cancel, zero_smul]
      have := congrArg (fun w => (r₂ - r₁ * (u : ℝ))⁻¹ • w) h0
      simp only [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul, smul_zero] at this
      exact hv this

/-- Three `Ray.map`s whose composite is a scalar multiplication by a unit. -/
theorem ray_map_map3 {M₁ M₂ M₃ : Type} [AddCommMonoid M₁] [Module ℝ M₁] [AddCommMonoid M₂]
    [Module ℝ M₂] [AddCommMonoid M₃] [Module ℝ M₃] (e₁ : M₁ ≃ₗ[ℝ] M₂) (e₂ : M₂ ≃ₗ[ℝ] M₃)
    (e₃ : M₃ ≃ₗ[ℝ] M₁) (u : ℝˣ) (h : ∀ y, e₃ (e₂ (e₁ y)) = u • y) (r : Module.Ray ℝ M₁) :
    Module.Ray.map e₃ (Module.Ray.map e₂ (Module.Ray.map e₁ r)) = u • r := by
  rw [ray_map_map, ray_map_map]
  exact ray_map_units_smul _ u h r

/-- **The abstract refutation.**  If `ô` over `Ĉ` takes the value `extDet` (the text's `h ↦ h̃`,
without the sign `(−1)^{dim coker L}`) at every `L̂ = Γ⁻¹ (L ⊕ 0) A`, `L ∈ C`, then pulling `ô` back
along the project's continuous `extDetN` gives an orientation `Φ` of `DET` over `C` with
`Φ(L) = (−1)^{dim coker L} · ω(L)`; over a preconnected `C` containing operators of both parities of
`dim coker`, this is impossible. -/
theorem abstract_false (A : E' ≃L[ℝ] E × (Fin 1 → ℝ)) (Γ : F' ≃L[ℝ] F)
    {C : Set (E →L[ℝ] F)} (hC : ∀ T ∈ C, T.IsFredholm) {Ĉ : Set (E' →L[ℝ] F')}
    (hĈ : ∀ T ∈ Ĉ, T.IsFredholm) (hmem : ∀ L ∈ C, extConjOp A Γ L ∈ Ĉ)
    (ω : LineOrientation (DetOn C hC)) (ô : LineOrientation (DetOn Ĉ hĈ))
    (h' : ∀ L : E →L[ℝ] F, ∀ v, extConjOp A Γ L (A.symm v) = Γ.symm (extOp L v))
    (hô : ∀ (L : E →L[ℝ] F) (hL : L ∈ C) (hLF : L.IsFredholm),
      ô ⟨extConjOp A Γ L, hmem L hL⟩ =
        Module.Ray.map ((extDet hLF).trans (conjDet A.symm Γ.symm (h' L))) (ω ⟨L, hL⟩))
    [PreconnectedSpace C] {L₀ L₁ : E →L[ℝ] F} (hL₀ : L₀ ∈ C) (hL₁ : L₁ ∈ C)
    (h₀ : stabSign L₀ = -1) (h₁ : stabSign L₁ = 1)
    (hPull : ∀ {C' : Set (E × (Fin 1 → ℝ) →L[ℝ] F)} {hC' : ∀ T ∈ C', T.IsFredholm}
      (hext : ∀ S ∈ C, extOp S ∈ C') (o' : LineOrientation (DetOn C' hC')),
      IsLineOrientation (DetOn C hC) (extPullRay hext o'.1)) : False := by
  set C' : Set (E × (Fin 1 → ℝ) →L[ℝ] F) :=
    {S' | (Γ.symm : F →L[ℝ] F') ∘L S' ∘L (A : E' →L[ℝ] E × (Fin 1 → ℝ)) ∈ Ĉ} with hC'def
  have hC' : ∀ S' ∈ C', S'.IsFredholm := fun S' hS' => isFredholm_of_conj A Γ (hĈ _ hS')
  have hmem' : ∀ S' ∈ C', (Γ.symm : F →L[ℝ] F') ∘L S' ∘L (A : E' →L[ℝ] E × (Fin 1 → ℝ)) ∈ Ĉ :=
    fun _ h => h
  have hext : ∀ L ∈ C, extOp L ∈ C' := hmem
  set ô' : LineOrientation (DetOn C' hC') := ô.conj (hC' := hC') A Γ hmem'
  set Φ : LineOrientation (DetOn C hC) := ⟨extPullRay hext ô'.1, hPull hext ô'⟩
  have hΦ : ∀ (L : E →L[ℝ] F) (hL : L ∈ C), Φ ⟨L, hL⟩ = ((stabSign L)⁻¹ : ℝˣ) • ω ⟨L, hL⟩ := by
    intro L hL
    change Module.Ray.map (extDetFiber (S := ⟨L, hC L hL⟩) (S' := ⟨extOp L, hC' _ (hext L hL)⟩)
      rfl).symm (ô' ⟨extOp L, hext L hL⟩) = _
    rw [ô.conj_apply_of_conj (hC' := hC') A Γ hmem'
      ⟨extConjOp A Γ L, hmem L hL⟩ ⟨extOp L, hext L hL⟩ (extConjOp_conj A Γ L),
      hô L hL (hC L hL)]
    apply ray_map_map3
    intro y
    change (extDetFiber (S := ⟨L, hC L hL⟩) (S' := ⟨extOp L, hC' _ (hext L hL)⟩) rfl).symm
      (conjDet A Γ (extConjOp_conj A Γ L) (conjDet A.symm Γ.symm (h' L) (extDet (hC L hL) y))) = _
    rw [conjDet_conjDet_symm]
    exact extDetFiber_symm_extDet _ _ _
  have e1 : Φ = ω := LineOrientation.eq_of_apply_eq ⟨L₁, hL₁⟩ (by
    rw [hΦ, h₁, inv_one, one_smul])
  have e0 := hΦ L₀ hL₀
  rw [e1, h₀] at e0
  exact units_smul_ne_self _ (by norm_num) _ e0.symm

end General


/-! ### The counterexample: the trivial bundle `ℝ¹ × ℝ¹ → ℝ¹`, `f = 0`, at `x = 0` -/

section Concrete

open TrivialBundle
open scoped ContDiff

abbrev V1 := Fin 1 → ℝ

/-- The zero section `x ↦ (x, 0)` of the trivial bundle `ℝ¹ × ℝ¹ → ℝ¹`. -/
noncomputable abbrev f0 : V1 → V1 × V1 := graphSection (fun _ : V1 => (0 : V1))

theorem hf0 : (bundle 1 1).IsScFredholmSection f0 :=
  isScFredholmSection_graphSection contDiff_const

theorem hx0 : (0 : V1) ∈ (rnPolyfold 1).smoothSet := by
  rw [rnPolyfold_smoothSet]; exact Set.mem_univ _

/-- The chart point of the translation chart at `0`, with `z = 0`. -/
noncomputable def p0 : ChartPoint (bundle 1 1) (0 : V1) where
  c := chart 0
  isChart := isChart_chart 0
  mem_source := Set.mem_univ _
  z := 0
  toBase_z := by
    change (ScBanach.const V1).toBase 1 0 = (0 : V1) - 0
    simp

/-- `T_0 = ℝ¹`. -/
theorem mem_p0_T (w : V1) : w ∈ p0.T := ⟨w, by
  change scDeriv (chart (k := 1) (0 : V1)).U (StrongRetr.r (chart (k := 1) (0 : V1)).R) 0 w = w
  rw [scDeriv_r]; rfl⟩

theorem sectionAdd_graph (φ ψ : V1 → V1) :
    sectionAdd (proj 1 1) (graphSection φ) (graphSection ψ) = graphSection (fun y => φ y + ψ y) := by
  funext y
  rw [sectionAdd_apply isSection_graphSection isSection_graphSection]
  rfl

/-- **The linearizations `(f + s)'(0) = Dψ(0)`** for the sc⁺-sections `s = graph ψ`. -/
theorem exists_mem_linSet (ψ : V1 → V1) (hψ : ContDiff ℝ ∞ ψ) (hψ0 : ψ 0 = 0) :
    ∃ L ∈ p0.linSet f0, ∀ v : p0.T,
      ((L v : p0.K) : p0.c.F 0) = fderiv ℝ ψ 0 (v : p0.c.φ.model.E 0) := by
  have hs := isScPlusSection_graphSection hψ
  have hgeq := sectionAdd_graph (fun _ : V1 => (0 : V1)) ψ
  have hzero : IsZeroAt (proj 1 1) (sectionAdd (proj 1 1) f0 (graphSection ψ)) 0 := by
    rw [hgeq, isZeroAt_graphSection_iff, hψ0, add_zero]
  have hg := hf0.isScSmooth.sectionAdd hs
  refine ⟨(linAt p0.c.U p0.c.R (p0.c.principal (sectionAdd (proj 1 1) f0 (graphSection ψ)))
    p0.z).codRestrict p0.K (fun v => p0.scDeriv_mem_K hg hzero v),
    ⟨_, hs, hzero, 0, p0.isScPlusOp_zero hx0, fun v => by
      rw [zero_apply, Submodule.coe_zero, add_zero]; rfl⟩, fun v => ?_⟩
  change scDeriv p0.c.U (p0.c.principal (sectionAdd (proj 1 1) f0 (graphSection ψ)) ∘
    StrongRetr.r p0.c.R) p0.z v = _
  have hfun : p0.c.principal (sectionAdd (proj 1 1) f0 (graphSection ψ)) ∘
      StrongRetr.r p0.c.R = ψ := by
    rw [hgeq]
    change (fun u : V1 => (0 : V1) + ψ (u + 0)) = ψ
    funext u
    rw [zero_add, add_zero]
  rw [hfun]
  exact congrArg (fun T : V1 →L[ℝ] V1 => T (v : p0.c.φ.model.E 0)) (scDeriv_univ_const hψ 0)

/-- `K_0 = ℝ¹` (every vector is a value of `L₁ = (f + graph id)'(0) = id`). -/
theorem mem_p0_K (k : p0.c.F 0) : k ∈ p0.K := by
  obtain ⟨L₁, -, hv₁⟩ := exists_mem_linSet id contDiff_id rfl
  have h := (L₁ ⟨k, mem_p0_T k⟩).2
  rwa [hv₁, fderiv_id] at h

theorem finrank_p0_K : Module.finrank ℝ p0.K = 1 := by
  rw [show p0.K = ⊤ from eq_top_iff.2 fun k _ => mem_p0_K k, finrank_top]
  exact Module.finrank_fin_fun ℝ

/-- `L = 0` has `dim coker L = 1`: sign `−1`. -/
theorem stabSign_of_zero {L : p0.T →L[ℝ] p0.K} (hL : ∀ v, ((L v : p0.K) : p0.c.F 0) = 0) :
    stabSign L = -1 := by
  have hr : LinearMap.range (L : p0.T →ₗ[ℝ] p0.K) = ⊥ := by
    refine eq_bot_iff.2 ?_
    rintro _ ⟨v, rfl⟩
    exact (Submodule.mem_bot ℝ).2 (Subtype.ext (hL v))
  rw [stabSign, (Submodule.quotEquivOfEqBot _ hr).finrank_eq, finrank_p0_K, pow_one]

/-- An onto `L` has `dim coker L = 0`: sign `+1`. -/
theorem stabSign_of_surjective {L : p0.T →L[ℝ] p0.K} (hs : Function.Surjective L) :
    stabSign L = 1 := by
  have : Subsingleton (p0.K ⧸ LinearMap.range (L : p0.T →ₗ[ℝ] p0.K)) :=
    Submodule.Quotient.subsingleton_iff.2 (LinearMap.range_eq_top.2 hs)
  rw [stabSign, Module.finrank_zero_of_subsingleton, pow_zero]

end Concrete

/-- **A ⇒ ¬B**: the trivial bundle `ℝ¹ × ℝ¹ → ℝ¹`, `f = 0`, `x = 0`, `t = 0`, `S = 0` is a
counterexample.  `Lin(f, 0)` contains `L₀ = 0` (`dim coker = 1`) and `L₁ = id` (onto), so the
rule "`L̃` is oriented by `h̃`" without the sign `(−1)^{dim coker L}` gives no orientation. -/
theorem A_to_not_B : A → ¬ B := by
  intro hA hB
  obtain ⟨L₀, hL₀, hv₀⟩ := exists_mem_linSet (fun _ => 0) contDiff_const rfl
  obtain ⟨L₁, hL₁, hv₁⟩ := exists_mem_linSet id contDiff_id rfl
  have hz : fderiv ℝ (fun _ : V1 => (0 : V1)) 0 = 0 := fderiv_const_apply _
  have h₀ : stabSign L₀ = -1 := stabSign_of_zero fun v => by rw [hv₀, hz]; rfl
  have h₁ : stabSign L₁ = 1 := stabSign_of_surjective fun k =>
    ⟨⟨(k.1 : V1), mem_p0_T k.1⟩, Subtype.ext (by rw [hv₁, fderiv_id]; rfl)⟩
  obtain ⟨ω, -⟩ := (proposition_6_26 (p0.convex_linSet hf0) ⟨L₀, hL₀⟩
    (p0.isFredholm_of_mem_linSet hf0)).2
  let q₀ : pullbackSpace (TrivialBundle.proj 1 1) (Prod.snd : V1 × V1 → V1) :=
    ⟨((0, 0), (0, 0)), rfl⟩
  have hS := StrongBundle.isScPlusSection_fiberZero
    (B := (TrivialBundle.bundle 1 1).pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) (rnPolyfold 1)))
  obtain ⟨hmem, ô, hô⟩ := hB (rnPolyfold 1) (TrivialBundle.proj 1 1) (TrivialBundle.bundle 1 1)
    (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) (rnPolyfold 1)) f0 hf0
    TrivialBundle.isSection_graphSection _ hS (theorem_3_15 hf0.param hS) 0 hx0 0
    (Set.left_mem_Icc.2 zero_le_one) p0 q₀ ω
  have : PreconnectedSpace (p0.linSet f0) :=
    isPreconnected_iff_preconnectedSpace.1 (p0.convex_linSet hf0).isPreconnected
  exact abstract_false (p0.prodT 0 q₀) (p0.prodK 0 q₀) (p0.isFredholm_of_mem_linSet hf0)
    ((p0.prodPt 0 q₀).isFredholm_of_mem_linSet (theorem_3_15 hf0.param hS)) hmem ω ô
    (fun L v => by simp [extConjOp]) (fun L hL hLF => hô L hL (hmem L hL) hLF)
    hL₀ hL₁ h₀ h₁ (fun hext o' => hA.2.2.2.2.2.2.2.1 hext o')

/-- **B is false**, since A holds. -/
theorem not_B : ¬ B := A_to_not_B A_holds

/-- `A ⇒ B` is false: `A` holds and `B` does not. -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B ⇒ A` holds only ex falso. -/
theorem B_to_A : B → A := fun h => (not_B h).elim

/-! ### The checks

No proof that mentions `B` can pass `#rt_check`: `B`'s own vocabulary `extDet` reaches
`finrank_ker_extOp` (in the body of `extKer`) and `range_extOp` (in the body of `extCoker`) as direct
arguments, not as abstracted `_proof_N` fields (`B_vocab`).  Likewise the statement `A` reaches
`isFredholm_extOp`, `mem_prodPt_T_iff`, `mem_prodPt_K_iff`, `IsScPlusOp.prodPt` and
`prodLin_mem_linSet` (they occur as proof terms inside the types of `existsUnique_prodOr`,
`prodOr_apply`, …).  The `#guard_msgs` below record that **`A_to_not_B` reaches exactly the banned
names that the bare statements `A → B → True` reach** (`AB_vocab`): its proof uses no banned theorem
beyond the vocabulary, and the continuity of `extDetN` (`isLineOrientation_extPull`) only through
the hypothesis `hA`.  `not_B` and `B_to_A` go through `A_holds` and reach every banned theorem. -/

/-- Any proof mentioning `B` reaches its vocabulary. -/
theorem B_vocab : B → True := fun _ => trivial

/-- Any proof mentioning `A` and `B` reaches their vocabulary. -/
theorem AB_vocab : A → B → True := fun _ _ => trivial

/-- error: rt_check_soft FAIL: RoundTrip.V6_62.B_vocab uses [Polyfold.finrank_ker_extOp, Polyfold.range_extOp] -/
#guard_msgs in
#rt_check_soft RoundTrip.V6_62.B_vocab [Polyfold.isFredholm_extOp,
    Polyfold.finrank_ker_extOp,
    Polyfold.range_extOp,
    Polyfold.extDet_wedge_tmul,
    Polyfold.extDetN_eq_of_surjective,
    Polyfold.coord_extDet,
    Polyfold.coord_extDetN,
    Polyfold.isLineOrientation_extPull,
    Polyfold.existsUnique_extConjOr,
    Polyfold.ChartPoint.mem_prodPt_T_iff,
    Polyfold.ChartPoint.mem_prodPt_K_iff,
    Polyfold.ChartPoint.IsScPlusOp.prodPt,
    Polyfold.ChartPoint.prodLin_mem_linSet,
    Polyfold.ChartPoint.existsUnique_prodOr,
    Polyfold.ChartPoint.prodOr_apply,
    Polyfold.ChartPoint.prodOr_injective]

/--
error: rt_check_soft FAIL: RoundTrip.V6_62.AB_vocab uses [Polyfold.isFredholm_extOp,
 Polyfold.finrank_ker_extOp,
 Polyfold.range_extOp,
 Polyfold.ChartPoint.mem_prodPt_T_iff,
 Polyfold.ChartPoint.mem_prodPt_K_iff,
 Polyfold.ChartPoint.IsScPlusOp.prodPt,
 Polyfold.ChartPoint.prodLin_mem_linSet]
-/
#guard_msgs in
#rt_check_soft RoundTrip.V6_62.AB_vocab [Polyfold.isFredholm_extOp,
    Polyfold.finrank_ker_extOp,
    Polyfold.range_extOp,
    Polyfold.extDet_wedge_tmul,
    Polyfold.extDetN_eq_of_surjective,
    Polyfold.coord_extDet,
    Polyfold.coord_extDetN,
    Polyfold.isLineOrientation_extPull,
    Polyfold.existsUnique_extConjOr,
    Polyfold.ChartPoint.mem_prodPt_T_iff,
    Polyfold.ChartPoint.mem_prodPt_K_iff,
    Polyfold.ChartPoint.IsScPlusOp.prodPt,
    Polyfold.ChartPoint.prodLin_mem_linSet,
    Polyfold.ChartPoint.existsUnique_prodOr,
    Polyfold.ChartPoint.prodOr_apply,
    Polyfold.ChartPoint.prodOr_injective]

/--
error: rt_check_soft FAIL: RoundTrip.V6_62.A_to_not_B uses [Polyfold.isFredholm_extOp,
 Polyfold.finrank_ker_extOp,
 Polyfold.range_extOp,
 Polyfold.ChartPoint.mem_prodPt_T_iff,
 Polyfold.ChartPoint.mem_prodPt_K_iff,
 Polyfold.ChartPoint.IsScPlusOp.prodPt,
 Polyfold.ChartPoint.prodLin_mem_linSet]
-/
#guard_msgs in
#rt_check_soft RoundTrip.V6_62.A_to_not_B [Polyfold.isFredholm_extOp,
    Polyfold.finrank_ker_extOp,
    Polyfold.range_extOp,
    Polyfold.extDet_wedge_tmul,
    Polyfold.extDetN_eq_of_surjective,
    Polyfold.coord_extDet,
    Polyfold.coord_extDetN,
    Polyfold.isLineOrientation_extPull,
    Polyfold.existsUnique_extConjOr,
    Polyfold.ChartPoint.mem_prodPt_T_iff,
    Polyfold.ChartPoint.mem_prodPt_K_iff,
    Polyfold.ChartPoint.IsScPlusOp.prodPt,
    Polyfold.ChartPoint.prodLin_mem_linSet,
    Polyfold.ChartPoint.existsUnique_prodOr,
    Polyfold.ChartPoint.prodOr_apply,
    Polyfold.ChartPoint.prodOr_injective]

#rt_overlap RoundTrip.V6_62.A_to_not_B [Polyfold.isFredholm_extOp,
    Polyfold.finrank_ker_extOp,
    Polyfold.range_extOp,
    Polyfold.extDet_wedge_tmul,
    Polyfold.extDetN_eq_of_surjective,
    Polyfold.coord_extDet,
    Polyfold.coord_extDetN,
    Polyfold.isLineOrientation_extPull,
    Polyfold.existsUnique_extConjOr,
    Polyfold.ChartPoint.mem_prodPt_T_iff,
    Polyfold.ChartPoint.mem_prodPt_K_iff,
    Polyfold.ChartPoint.IsScPlusOp.prodPt,
    Polyfold.ChartPoint.prodLin_mem_linSet,
    Polyfold.ChartPoint.existsUnique_prodOr,
    Polyfold.ChartPoint.prodOr_apply,
    Polyfold.ChartPoint.prodOr_injective]

end RoundTrip.V6_62
