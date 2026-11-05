import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_31

/-!
Round trip for V4_31 (Remark 4.14 in a chart).  `A` is the type of
`Polyfold.MPolyfold.SubmanifoldData.remark_4_14`, universe instantiated at `0`.

The two sides read Remark 4.14 in slightly different chart situations:
* A: a chart `φ` of `X` around `a`, the shrunken set `W = V ∩ dom φ ∩ s⁻¹(V ∩ dom φ)`, `T_aX` as
  `T_zO` (`O` the whole chart model), `Ts(a)` as the tangent map of `ρ = φ ∘ s ∘ φ⁻¹` between the
  retracts `φ(W) → φ(W)` (`retractTangentMap`), `T_aA = T_z(φ(W ∩ A))`; conclusions: `z` smooth,
  `Tρ(z)(T_zO) = T_aA`, `T_aA ⊆ T_zO`, `T_aA` finite-dimensional.
* B: the reduced situation `V ⊆ dom φ`, `r(U) = φ(V)` (item V4_30), `Ts(a) = Dt(z)` for
  `t = φ ∘ s ∘ φ⁻¹ ∘ r`; conclusions: `s(V) ⊆ X_∞`, `T_aA = Dt(z)(T_z(φ(V)))`, `T_aA = range Dt(z)`,
  `Dt(z)` an sc⁺-operator, `range Dt(z)` finite-dimensional.

Glue: `retractTangentMap_eqOn` (the tangent map between retracts is `D(ρ ∘ r)(z)` on `T_zO`),
`tangentSpace_inter_isOpen` (`T_z(O ∩ G) = T_zO`), the restricted chart `φ|_V` (A applied to it has
`W = V` and model `φ(V)`), and for B's extra conjuncts the sc⁺-retraction `t` of
`exists_chartRetraction` (a project lemma, not banned) with `scDeriv_eq_of_eqOn_relOpen`.
-/

namespace RoundTrip.V4_31
open Polyfold Set

def A : Prop := type_of% @Polyfold.MPolyfold.SubmanifoldData.remark_4_14.{0}

theorem A_holds : A := @Polyfold.MPolyfold.SubmanifoldData.remark_4_14.{0}

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- The project's sc⁺-retractions on open sets are B's (copied from V4_9). -/
theorem retractionOn_iff (P : MPolyfold X) (r : X → X) (V : Set X) :
    P.IsScPlusRetractionOn r V ↔ IsScPlusRetractionOnB P r V := by
  constructor
  · intro h
    refine ⟨h.isScSmoothOn.isOpen, h.isScSmoothOn, h.mapsTo, h.idem, h.mem_levelSet,
      fun g hg => ?_⟩
    rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
    · exact MPolyfold.IsScSmoothOn.of_exists_charts h.isScSmoothOn.isOpen
        (fun y _ => (IsEmpty.false y).elim) (fun y _ => (IsEmpty.false y).elim)
    · refine (h.isScSmoothOn_one (g x)).congr fun y hy => ?_
      change P.toLevelOne (g x) (r y) = g y
      rw [← hg y hy, MPolyfold.toLevelOne_levelVal]
  · rintro ⟨-, h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, fun x₀ =>
      h5 _ fun x hx => MPolyfold.levelVal_toLevelOne x₀ (h4 x hx)⟩

/-- Restriction of an sc⁺-retraction to an invariant open subset (V4_30). -/
theorem retractionOnB_restrict {P : MPolyfold X} {s : X → X} {V W : Set X}
    (h : IsScPlusRetractionOnB P s V) (hW : IsOpen W) (hWV : W ⊆ V) (hmaps : MapsTo s W W) :
    IsScPlusRetractionOnB P s W := by
  have h' := (retractionOn_iff P s V).2 h
  exact (retractionOn_iff P s W).1 ⟨h'.isScSmoothOn.mono hW hWV, hmaps,
    fun x hx => h'.idem x (hWV hx), fun x hx => h'.mem_levelSet x (hWV hx),
    fun x₀ => (h'.isScSmoothOn_one x₀).mono hW hWV⟩

end Glue

/-- The derivative of an sc⁺-retraction at a smooth level-`1` point of its domain is an
sc⁺-operator in B's sense. -/
theorem isScPlusOperatorB_of {E : ScBanach} {C : Set (E 0)} {T : ScRetraction E C}
    (hT : T.IsScPlus) {z : E 1} (hzU : z ∈ E.lvlSet T.U 1) (hzs : z ∈ E.smoothLvl 1) :
    IsScPlusOperatorB E (scDeriv T.U T z) := by
  obtain ⟨Sop, hS⟩ := IsScPlus.exists_scPlus_deriv T.isScDomain hT hzU hzs
  intro m
  refine ⟨Sop m, fun x => ?_⟩
  rw [← hS, E.shift_toBase, Sop.toBase_comm m x, ScPlus.toScOperator_apply]
  rfl

/-- In B's reduced situation, the sc⁺-retraction `t = φ ∘ s ∘ φ⁻¹ ∘ r` of the project's
`exists_chartRetraction` (applied to the restricted chart `φ|_V`), on all of `U`. -/
theorem chartT {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) {S : Set X} {s : X → X} {V : Set X} (hsP : P.IsScPlusRetractionOn s V)
    (himg : s '' V = S ∩ V) (hVo : IsOpen V) {φ : MChart X} (hφ : P.IsChart φ)
    (hVφ : V ⊆ φ.toPartialEquiv.source) (r : ScRetraction φ.model.E φ.model.C)
    (hr : r.retract = φ.toPartialEquiv '' V) (x₀ : P.Level 1) :
    ∃ T : ScRetraction φ.model.E φ.model.C, T.U = r.U ∧
      EqOn T.toFun (localRep φ s r) r.U ∧ T.IsScPlus ∧
      T.retract = φ.toPartialEquiv '' (S ∩ V) := by
  let d : P.SubmanifoldData S := ⟨V, s, hVo, hsP, himg⟩
  let ψ := φ.restrict hVφ hVo
  have hψ : P.IsChart ψ := MPolyfold.IsChart.restrict P hφ hVφ hVo
  have hshr : d.toSubData.shrink ψ = V := by
    ext x
    constructor
    · intro hx; exact hx.1.1
    · intro hx; exact ⟨⟨hx, hx⟩, hsP.mapsTo hx, hsP.mapsTo hx⟩
  obtain ⟨t, ht, htp, -, hteq, G, -, htU, hWG⟩ :=
    MPolyfold.SubmanifoldData.exists_chartRetraction d hψ x₀ r hr
  rw [hshr] at ht hWG
  have hUG : t.U = r.U := by
    rw [htU]
    refine inter_eq_left.2 fun u hu => ?_
    have h1 : r.toFun u ∈ ψ.toPartialEquiv '' V := hr ▸ r.apply_mem_retract hu
    rw [hWG] at h1
    exact h1.2
  refine ⟨t, hUG, fun x hx => hteq x (hUG ▸ hx), htp, ?_⟩
  exact ht.trans (by rw [inter_comm V S]; rfl)

/-- A in B's reduced situation (`V ⊆ dom φ`): applied to the restricted chart `φ|_V`, whose
shrunken set is `V` and whose model is `φ(V)`; stated in terms of `φ`. -/
theorem A_reduced (hA : A) {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) {S : Set X} {s : X → X} {V : Set X} (hsP : P.IsScPlusRetractionOn s V)
    (himg : s '' V = S ∩ V) (hVo : IsOpen V) {φ : MChart X} (hφ : P.IsChart φ)
    (hVφ : V ⊆ φ.toPartialEquiv.source) {a : X} (ha : a ∈ S ∩ V) {z : φ.model.E 1}
    (hz : φ.model.E.toBase 1 z = φ.toPartialEquiv a) :
    z ∈ φ.model.E.smoothLvl 1 ∧
      (fun h => (retractTangentMap φ.model.E φ.model.C (φ.toPartialEquiv '' V)
          (φ.toPartialEquiv ∘ s ∘ φ.symm) ((z, h) : φ.model.E.tangent 0)).2) ''
          tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' V) z =
        tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' (V ∩ S)) z ∧
      ∃ N : Submodule ℝ (φ.model.E 0), (N : Set (φ.model.E 0)) =
        tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' (V ∩ S)) z ∧
        FiniteDimensional ℝ N := by
  let d : P.SubmanifoldData S := ⟨V, s, hVo, hsP, himg⟩
  let ψ := φ.restrict hVφ hVo
  have hψ : P.IsChart ψ := MPolyfold.IsChart.restrict P hφ hVφ hVo
  have hshr : d.toSubData.shrink ψ = V := by
    ext x
    constructor
    · intro hx; exact hx.1.1
    · intro hx; exact ⟨⟨hx, hx⟩, hsP.mapsTo hx, hsP.mapsTo hx⟩
  have h := hA d hψ ha.1 ha.2 ha.2 (z := z) hz
  rw [hshr] at h
  exact ⟨h.1, h.2.1, h.2.2.2⟩

/-- `ρ = φ ∘ s ∘ φ⁻¹` is sc-smooth `φ(V) → φ(V)` (project lemma `SubData.rho_isScSmooth` for the
restricted chart). -/
theorem rho_reduced {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) {S : Set X} {s : X → X} {V : Set X} (hsP : P.IsScPlusRetractionOn s V)
    (himg : s '' V = S ∩ V) (hVo : IsOpen V) {φ : MChart X} (hφ : P.IsChart φ)
    (hVφ : V ⊆ φ.toPartialEquiv.source) :
    IsScSmoothRetractMap φ.model.E φ.model.C (φ.toPartialEquiv '' V) φ.model.E φ.model.C
      (φ.toPartialEquiv '' V) (φ.toPartialEquiv ∘ s ∘ φ.symm) := by
  let d : P.SubmanifoldData S := ⟨V, s, hVo, hsP, himg⟩
  let ψ := φ.restrict hVφ hVo
  have hψ : P.IsChart ψ := MPolyfold.IsChart.restrict P hφ hVφ hVo
  have hshr : d.toSubData.shrink ψ = V := by
    ext x
    constructor
    · intro hx; exact hx.1.1
    · intro hx; exact ⟨⟨hx, hx⟩, hsP.mapsTo hx, hsP.mapsTo hx⟩
  have h := d.toSubData.rho_isScSmooth ψ hψ
  rw [hshr] at h
  exact h

theorem A_to_B : A → B := by
  intro hA X _ _ _ P S s V hs himg
  have hsP := (retractionOn_iff P s V).2 hs
  let d : P.SubmanifoldData S := ⟨V, s, hs.1, hsP, himg⟩
  refine ⟨?_, ?_⟩
  · -- `s(V) ⊆ X_∞`, from A's first conclusion in a chart around `s(v)`
    rintro _ ⟨v, hv, rfl⟩
    have hxSV : s v ∈ S ∩ V := himg ▸ mem_image_of_mem s hv
    obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source (s v)
    obtain ⟨z, hz⟩ := (P.mem_levelSet_iff hφ hxφ).1 (hsP.mem_levelSet v hv)
    have h1 := (hA d hφ hxSV.1 hxSV.2 hxφ hz).1
    rw [MPolyfold.mem_smoothSet_iff hφ hxφ, ← hz]
    exact h1
  · intro φ r hφ hVφ hr a z ha hz
    obtain ⟨hzs, h2, N, hN, hNfin⟩ := A_reduced hA P hsP himg hs.1 hφ hVφ ha hz
    -- the sc⁺-retraction `t` onto `φ(A ∩ V)` (project lemma `exists_chartRetraction`)
    obtain ⟨T, hUG, heq, hTp, hTret⟩ := chartT P hsP himg hs.1 hφ hVφ r hr
      (P.levelMk 1 a (d.mem_levelSet_one ha.1 ha.2))
    have hzr : φ.model.E.toBase 1 z ∈ r.retract := by rw [hr, hz]; exact ⟨a, ha.2, rfl⟩
    have hzU : z ∈ φ.model.E.lvlSet r.U 1 := r.retract_subset hzr
    have hzT : z ∈ φ.model.E.lvlSet T.retract 1 := by
      rw [ScBanach.mem_lvlSet, hTret, hz]; exact ⟨a, ha, rfl⟩
    have hDt : scDeriv r.U (localRep φ s r) z = scDeriv T.U T z := by
      have h1 : IsSc1 r.U (localRep φ s r) := (hUG ▸ T.isSc1).congr heq
      exact scDeriv_eq_of_eqOn_relOpen r.relOpen h1 T.isSc1 subset_rfl hUG.ge heq.symm hzU
    -- B (b): `T_aA = range Dt(z)`
    have hb : tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' (S ∩ V)) z =
        range (scDeriv r.U (localRep φ s r) z) := by
      rw [hDt, ← tangentSpace_eq_range T hzT, hTret]
    refine ⟨?_, hb, ?_, ?_⟩
    · -- B (a), from A's `Tρ(z)(T_zO) = T_aA`
      have hρ := rho_reduced P hsP himg hs.1 hφ hVφ
      have hcongr : ∀ h ∈ tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' V) z,
          (retractTangentMap φ.model.E φ.model.C (φ.toPartialEquiv '' V)
            (φ.toPartialEquiv ∘ s ∘ φ.symm) ((z, h) : φ.model.E.tangent 0)).2 =
            scDeriv r.U (localRep φ s r) z h := by
        intro h hh
        rw [retractTangentMap_eqOn hρ r hr hh]
        rfl
      rw [← image_congr hcongr, h2, inter_comm]
    · rw [hDt]
      exact isScPlusOperatorB_of hTp (hUG ▸ hzU) hzs
    · -- finite-dimensional, from A's `N`
      have hNr : N = LinearMap.range
          (scDeriv r.U (localRep φ s r) z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) := by
        apply SetLike.coe_injective
        rw [hN, LinearMap.coe_range, ContinuousLinearMap.coe_coe, ← hb, inter_comm]
      rw [← hNr]
      exact hNfin

theorem B_to_A : B → A := by
  intro hB X _ _ _ P S d φ hφ a ha haV haφ z hz
  have hsB : IsScPlusRetractionOnB P d.s d.V :=
    (retractionOn_iff P d.s d.V).1 d.isScPlusRetractionOn
  obtain ⟨hsm, -⟩ := hB X P S d.s d.V hsB d.image
  -- the shrunken set `W` and a retraction onto `φ(W) = O ∩ G`
  set W := d.toSubData.shrink φ with hWdef
  have haW : a ∈ W := d.toSubData.mem_shrink φ ha haV haφ
  have hsW : IsScPlusRetractionOnB P d.s W :=
    retractionOnB_restrict hsB (d.toSubData.isOpen_shrink φ) (d.toSubData.shrink_subset_V φ)
      (d.toSubData.mapsTo_shrink φ)
  have himgW : d.s '' W = S ∩ W := by
    rw [show d.s '' W = d.toSubData.r '' d.toSubData.shrink φ from rfl,
      d.toSubData.image_shrink, inter_comm]
  obtain ⟨G, hG, hWG⟩ := φ.exists_isOpen_image_eq (d.toSubData.shrink_subset_source φ)
    (d.toSubData.isOpen_shrink φ)
  obtain ⟨R₀, hR₀⟩ := φ.model.isScRetract
  have hR' : (R₀.restrict hG).retract = φ.toPartialEquiv '' W := by
    rw [R₀.restrict_retract, hR₀, hWG]
  obtain ⟨-, hB2⟩ := hB X P S d.s W hsW himgW
  obtain ⟨ha', hb', -, hd'⟩ := hB2 φ (R₀.restrict hG) hφ (d.toSubData.shrink_subset_source φ) hR'
    a z ⟨ha, haW⟩ hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `z` is smooth: `a = s(a) ∈ s(V) ⊆ X_∞`
    have haS : a ∈ d.s '' d.V := ⟨a, haV, d.apply_eq_self ⟨ha, haV⟩⟩
    have := (MPolyfold.mem_smoothSet_iff hφ haφ).1 (hsm haS)
    rw [← hz] at this
    exact this
  · have hzW : φ.model.E.toBase 1 z ∈ φ.model.O ∩ G := by
      rw [← hWG, hz]; exact ⟨a, haW, rfl⟩
    have hTO : tangentSpace φ.model.E φ.model.C φ.model.O z =
        tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' W) z := by
      rw [hWG]; exact (tangentSpace_inter_isOpen φ.model.isScRetract hG hzW).symm
    rw [hTO]
    have hcongr : ∀ h ∈ tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' W) z,
        (retractTangentMap φ.model.E φ.model.C (φ.toPartialEquiv '' W)
          (φ.toPartialEquiv ∘ d.s ∘ φ.symm) ((z, h) : φ.model.E.tangent 0)).2 =
          scDeriv (R₀.restrict hG).U (localRep φ d.s (R₀.restrict hG)) z h := by
      intro h hh
      have hρ : IsScSmoothRetractMap φ.model.E φ.model.C (φ.toPartialEquiv '' W) φ.model.E
          φ.model.C (φ.toPartialEquiv '' W) (φ.toPartialEquiv ∘ d.s ∘ φ.symm) :=
        d.toSubData.rho_isScSmooth φ hφ
      rw [retractTangentMap_eqOn hρ (R₀.restrict hG) hR' hh]
      rfl
    rw [image_congr hcongr, ← ha', inter_comm]
  · -- `T_aA ⊆ T_aX`: tangent spaces of sub-retracts (general fact, not from B)
    have hzA : z ∈ φ.model.E.lvlSet (φ.toPartialEquiv '' (W ∩ S)) 1 := by
      rw [ScBanach.mem_lvlSet, hz]; exact ⟨a, ⟨haW, ha⟩, rfl⟩
    have := tangentSpace_subset_of_subset R₀ (d.toSubData.isScRetract_image φ hφ)
      (hR₀ ▸ φ.image_subset_model fun _ hx => d.toSubData.shrink_subset_source φ hx.1) hzA
    rwa [hR₀] at this
  · refine ⟨_, ?_, hd'⟩
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe, ← hb', inter_comm]

#rt_check RoundTrip.V4_31.A_to_B [Polyfold.MPolyfold.SubmanifoldData.remark_4_14]
#rt_check RoundTrip.V4_31.B_to_A [Polyfold.MPolyfold.SubmanifoldData.remark_4_14]
#rt_overlap RoundTrip.V4_31.B_to_A [Polyfold.MPolyfold.SubmanifoldData.remark_4_14]

end RoundTrip.V4_31
