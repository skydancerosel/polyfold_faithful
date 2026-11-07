import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_24

/-! Round trip for V6_24 (§6.4, p. 217: `DET(E, F)` and the charts `γ_(T,P,ε)`).

The listed declarations are the definitions `DetFiber`, `LocalDetChart.pretriv`,
`LocalDetChart.coord`, `detPrebundle` and the theorem `exists_localDetChart`, so
`A = type_of% exists_localDetChart` (universes at `0`): every Fredholm `T` is the centre of a
`LocalDetChart` (data `(T, P, Y, ε)` with the conclusions of Lemma 6.17).

* B's admissible triples `IsDetChart T P ε` are exactly the `(c.T, c.P, c.ε)` of the project's
  charts (`chartOf`, `hcOf`: same fields, `Y` existentially quantified in B).
* B (1) is A (`A_to_B` uses A); A is B (1) (`B_to_A` uses B).
* B (2) (`γ_(T,P,ε)` is a bijection for EVERY admissible triple) is not stated by A; it is proved
  here outright (`gammaChart_bijective`).  It needs that every `S` of the ball is Fredholm
  (`chart_isFredholm`: `ker S ⊆ ker(PS)`, `R(S) ⊇ S(Y)` closed via the left inverse `P` of
  `S ∘ (PS|_Y)⁻¹`, `F = R(S) + ker P`), which the project never states (its `DET(T, P, ε)` is
  only ever looked at over Fredholm `S`).
* The project's `pretriv` is B's `γ_(T,P,ε)` followed by the frame coordinate `ω(S)*` of
  `DET(T, P, ε)`: `gammaChart_eq` (`γ(x) = (S, coord_S(x) · ω(S))`).
-/

namespace RoundTrip.V6_24
open Polyfold Bundle

noncomputable section

/-- The project's statement: `exists_localDetChart`, universes at `0`. -/
def A : Prop := type_of% @Polyfold.exists_localDetChart.{0, 0}

theorem A_holds : A := @Polyfold.exists_localDetChart.{0, 0}

section Glue

set_option linter.unusedSectionVars false

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A project chart from an admissible triple of B. -/
def chartOf {T : E →L[ℝ] F} {P : F →L[ℝ] F} {ε : ℝ} (hc : IsDetChart T P ε) :
    LocalDetChart E F where
  T := T
  isFredholm := hc.1
  P := P
  isGoodLeftProj := hc.2.1
  Y := hc.2.2.2.2.choose
  isTopCompl := hc.2.2.2.2.choose_spec.1
  ε := ε
  ε_pos := hc.2.2.1
  isGoodLeftProj_of_lt := hc.2.2.2.1
  exists_equiv_of_lt S hS := by
    obtain ⟨e, he⟩ := hc.2.2.2.2.choose_spec.2 S hS
    exact ⟨e, ContinuousLinearMap.ext fun y =>
      Subtype.ext ((he y).trans (coe_projRestrict_apply _ _ _ y).symm)⟩

/-- The admissible triple of a project chart. -/
theorem hcOf (c : LocalDetChart E F) : IsDetChart c.T c.P c.ε := by
  refine ⟨c.isFredholm, c.isGoodLeftProj, c.ε_pos, c.isGoodLeftProj_of_lt, c.Y, c.isTopCompl,
    fun S hS => ?_⟩
  obtain ⟨e, he⟩ := c.exists_equiv_of_lt S hS
  exact ⟨e, fun y => by rw [← coe_projRestrict_apply, ← he]; rfl⟩

/-- Every `S` of the ball of a chart is Fredholm. -/
theorem chart_isFredholm (c : LocalDetChart E F) (S : E →L[ℝ] F) (hS : ‖S - c.T‖ < c.ε) :
    S.IsFredholm := by
  have hP := c.isGoodLeftProj_of_lt S hS
  have hK := c.finiteDimensional_ker S hS
  have hkP := hP.finiteDimensional_ker
  obtain ⟨e, he⟩ := c.exists_equiv_of_lt S hS
  have hey : ∀ y : c.Y, (e y : F) = c.P (S y) := fun y => by
    rw [← coe_projRestrict_apply, ← he]; rfl
  refine isFredholm_of_banach S ?_ ?_ ?_
  · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.ker
      ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) fun x hx => ?_
    change c.P (S x) = 0
    rw [show S x = 0 from hx, map_zero]
  · have hYfin : Module.Finite ℝ (E ⧸ c.Y) :=
      Module.Finite.equiv (Submodule.quotientEquivOfIsCompl c.Y c.K c.isTopCompl.isCompl.symm).symm
    have : c.Y.CoFG := hYfin
    refine LinearMap.isClosed_range_of_isClosed_map_of_finiteDimensional_quotient (s := c.Y) ?_
    let f : F →L[ℝ] LinearMap.range (c.P : F →ₗ[ℝ] F) :=
      c.P.codRestrict _ (fun x => LinearMap.mem_range_self _ x)
    let g : LinearMap.range (c.P : F →ₗ[ℝ] F) → F := fun r => S (e.symm r : E)
    have hfg : Function.LeftInverse f g := fun r => Subtype.ext <| by
      change c.P (S (e.symm r : E)) = r
      rw [← hey, e.apply_symm_apply]
    have hg : Continuous g := S.continuous.comp (continuous_subtype_val.comp e.symm.continuous)
    have hcl := hfg.isClosed_range f.continuous hg
    convert hcl using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨e ⟨y, hy⟩, by simp [g]⟩
    · rintro ⟨r, rfl⟩
      exact ⟨e.symm r, (e.symm r).2, rfl⟩
  · let φ : LinearMap.ker (c.P : F →ₗ[ℝ] F) →ₗ[ℝ] F ⧸ LinearMap.range (S : E →ₗ[ℝ] F) :=
      (LinearMap.range (S : E →ₗ[ℝ] F)).mkQ ∘ₗ (LinearMap.ker (c.P : F →ₗ[ℝ] F)).subtype
    refine Module.Finite.of_surjective φ fun q => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hx : c.P x ∈ LinearMap.range ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
      rw [hP.range_comp]; exact LinearMap.mem_range_self _ x
    obtain ⟨y, hy⟩ := hx
    have hy' : c.P (S y) = c.P x := hy
    refine ⟨⟨x - S y, by
      change c.P (x - S y) = 0
      rw [map_sub, hy', sub_self]⟩, ?_⟩
    change Submodule.Quotient.mk (x - S y) = Submodule.Quotient.mk x
    rw [Submodule.Quotient.eq]
    exact ⟨-y, by simp⟩

/-- Every `S` of the ball of an admissible triple is Fredholm. -/
theorem isFredholm_of_mem_ball {T : E →L[ℝ] F} {P : F →L[ℝ] F} {ε : ℝ} (hc : IsDetChart T P ε)
    {S : E →L[ℝ] F} (hS : ‖S - T‖ < ε) : S.IsFredholm :=
  chart_isFredholm (chartOf hc) S hS

/-- B (2): `γ_(T,P,ε)` is a bijection, for every admissible triple. -/
theorem gammaChart_bijective {T : E →L[ℝ] F} {P : F →L[ℝ] F} {ε : ℝ} (hc : IsDetChart T P ε) :
    Function.Bijective (gammaChart hc) := by
  constructor
  · rintro ⟨⟨⟨S, hS⟩, h⟩, hb⟩ ⟨⟨⟨S', hS'⟩, h'⟩, hb'⟩ heq
    simp only [gammaChart] at heq
    injection heq with h1 h2
    injection h1 with h3
    subst h3
    have h4 := (gammaProj hS (hc.2.2.2.1 _ (mem_ball_iff_norm.mp hb))).injective (eq_of_heq h2)
    subst h4
    rfl
  · rintro ⟨⟨S, hS⟩, g⟩
    have hF : S.IsFredholm := isFredholm_of_mem_ball hc (mem_ball_iff_norm.mp hS)
    refine ⟨⟨⟨⟨S, hF⟩, (gammaProj hF (hc.2.2.2.1 S (mem_ball_iff_norm.mp hS))).symm g⟩, hS⟩, ?_⟩
    exact congrArg (TotalSpace.mk _) (LinearEquiv.apply_symm_apply _ _)

/-- The project's `pretriv` read through B's `γ`: `γ_(T,P,ε)(x) = (S, coord_S(x) · ω(S))`, where
`(S, coord_S(x)) = c.pretriv x` (`LocalDetChart.pretriv_apply`). -/
theorem gammaChart_eq (c : LocalDetChart E F)
    (p : {p : TotalSpace ℝ (DETF (E := E) (F := F)) //
      (p.proj : E →L[ℝ] F) ∈ Metric.ball c.T c.ε}) :
    gammaChart (hcOf c) p = ⟨⟨p.1.proj.1, p.2⟩,
      c.coord p.1.proj p.1.2 • c.frame p.1.proj.1 (mem_ball_iff_norm.mp p.2)⟩ := by
  have hS : ‖p.1.proj.1 - c.T‖ < c.ε := mem_ball_iff_norm.mp p.2
  have h1 := finrank_fredholmDet ((c.isGoodLeftProj_of_lt _ hS).isFredholm_comp p.1.proj.2)
  refine congrArg (TotalSpace.mk _) ?_
  exact (dualVec_apply_smul h1 (c.frame_ne_zero _ hS) _).symm.trans
    (congrArg (· • c.frame p.1.proj.1 hS) (c.coord_apply hS p.1.2).symm)

end Glue

/-- `A ⇒ B`: B (1) from A; B (2) is proved outright (`gammaChart_bijective`). -/
theorem A_to_B : A → B := by
  intro hA E F _ _ _ _ _ _
  refine ⟨fun T hT => ?_, fun T P ε hc => gammaChart_bijective hc⟩
  obtain ⟨c, hcT⟩ := hA ⟨T, hT⟩
  refine ⟨c.P, c.ε, ?_⟩
  have := hcOf c
  rw [hcT] at this
  exact this

/-- `B ⇒ A`: B (1) gives `(P, ε)` and a complement `Y`, i.e. a project chart centred at `T`. -/
theorem B_to_A : B → A := by
  intro hB E F _ _ _ _ _ _ T
  obtain ⟨P, ε, hc⟩ := (hB (E := E) (F := F)).1 T.1 T.2
  exact ⟨chartOf hc, rfl⟩

#rt_check RoundTrip.V6_24.A_to_B [Polyfold.exists_localDetChart]
#rt_check RoundTrip.V6_24.B_to_A [Polyfold.exists_localDetChart]
#rt_overlap RoundTrip.V6_24.B_to_A [Polyfold.exists_localDetChart]
#rt_overlap RoundTrip.V6_24.A_to_B [Polyfold.exists_localDetChart]

end

end RoundTrip.V6_24
