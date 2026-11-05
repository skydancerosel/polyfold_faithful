import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_30

/-!
Round trip for V4_30 (the sc⁺-retraction `t = φ ∘ s ∘ φ⁻¹ ∘ r` of the proof of Theorem 4.18).
`A` is the conjunction of the types of `SubmanifoldData.isScSmoothRetractMap_lift`,
`SubmanifoldData.exists_chartRetraction`, `SubmanifoldData.isScPlusRetract_image` and
`SubmanifoldData.apply_mem_smooth` (namespace `Polyfold.MPolyfold`), universe `0`.

Glue:
* sc⁺-retractions on open sets: `retractionOn_iff` (V4_9); restriction to an `s`-invariant open
  subset (`retractionOnB_restrict`, through the project's form, whose last clause is monotone).
* sc⁺-retractions in a model: the project's `ScRetraction.IsScPlus` (canonical lift `E.liftOne ∘ r`
  sc-smooth into `E¹`) vs B's "`r(U_m) ⊆ E_{m+1}` and SOME sc-smooth lift" (`toB`, `fromB`;
  `IsScPlus.iff_exists`, `mem_lvlSet_succ`).
* `A → B` (2): B's reduced situation (`V ⊆ dom φ`, `r(U) = φ(V)`) is A's situation for the
  restricted chart `φ|_V` (`MChart.restrict`, same `E`, `C`, model `O = φ(V)`), whose shrunken
  set `W = V ∩ dom φ|_V ∩ s⁻¹(…)` is `V`; A's open `G` contains `φ(V) = r(U)`, so A's
  `t.U = U ∩ r⁻¹(G)` is `U`.  `exists_chartRetraction` needs a junk point `x₀ ∈ X₁`, taken as
  `s(v)` for `v ∈ V`; for `V = ∅` the retraction `r` itself (with `U = ∅`) works.
* `A → B` (1) is glue that does not use A: `V' = W` (the project's `SubData.shrink`) and `r'` the
  restriction of `r` to `r⁻¹(G)` with `φ(W) = O ∩ G`.
* `B → A`: every conjunct of A comes from B (2) applied to `V := W` and `r := R|_{R⁻¹(G)}` (a
  retraction onto `φ(W) = O ∩ G`); `apply_mem_smooth` then is Lemma 4.7 (i) (`lemma_4_7_i`).
-/

namespace RoundTrip.V4_30
open Polyfold Set

def A : Prop :=
  type_of% @Polyfold.MPolyfold.SubmanifoldData.isScSmoothRetractMap_lift.{0} ∧
    type_of% @Polyfold.MPolyfold.SubmanifoldData.exists_chartRetraction.{0} ∧
    type_of% @Polyfold.MPolyfold.SubmanifoldData.isScPlusRetract_image.{0} ∧
    type_of% @Polyfold.MPolyfold.SubmanifoldData.apply_mem_smooth.{0}

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.SubmanifoldData.isScSmoothRetractMap_lift.{0},
    @Polyfold.MPolyfold.SubmanifoldData.exists_chartRetraction.{0},
    @Polyfold.MPolyfold.SubmanifoldData.isScPlusRetract_image.{0},
    @Polyfold.MPolyfold.SubmanifoldData.apply_mem_smooth.{0}⟩

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

/-- Restriction of an sc⁺-retraction to an invariant open subset. -/
theorem retractionOnB_restrict {P : MPolyfold X} {s : X → X} {V W : Set X}
    (h : IsScPlusRetractionOnB P s V) (hW : IsOpen W) (hWV : W ⊆ V) (hmaps : MapsTo s W W) :
    IsScPlusRetractionOnB P s W := by
  have h' := (retractionOn_iff P s V).2 h
  exact (retractionOn_iff P s W).1 ⟨h'.isScSmoothOn.mono hW hWV, hmaps,
    fun x hx => h'.idem x (hWV hx), fun x hx => h'.mem_levelSet x (hWV hx),
    fun x₀ => (h'.isScSmoothOn_one x₀).mono hW hWV⟩

end Glue

section Model

variable {E : ScBanach} {C : Set (E.lvl 0)}

theorem toB {R : ScRetraction E C} (hR : R.IsScPlus) : IsScPlusRetractionB R :=
  ⟨fun m x hx => by
    obtain ⟨y, -, hy⟩ := hR.mem_lvlSet_succ m hx
    exact ⟨y, hy⟩, E.liftOne ∘ R, fun x hx => IsScPlus.toBase_lift hR hx, hR.isScSmooth_lift⟩

theorem fromB {R : ScRetraction E C} (hR : IsScPlusRetractionB R) : R.IsScPlus := by
  obtain ⟨-, g, hg, hgs⟩ := hR
  exact (IsScPlus.iff_exists R.isScDomain).2 ⟨g, hgs, hg⟩

/-- A retraction with empty domain is sc⁺. -/
theorem isScPlus_of_U_empty (R : ScRetraction E C) (hU : R.U = ∅) : R.IsScPlus :=
  (IsScPlus.iff_exists R.isScDomain).2
    ⟨fun _ => 0, fun k => IsSck.zero (Y := E.shift) R.isScDomain k, fun x hx => by
      rw [hU] at hx; exact hx.elim⟩

end Model

/-- B (1), the reduction (glue; does not use A). -/
theorem B1 : (∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (A : Set X) (s : X → X) (V : Set X) (φ : MChart X)
    (r : ScRetraction φ.model.E φ.model.C) (a : X),
    IsScPlusRetractionOnB P s V → s '' V = A ∩ V → P.IsChart φ → r.retract = φ.model.O →
    a ∈ A ∩ V → a ∈ φ.toPartialEquiv.source →
      ∃ V' : Set X, a ∈ V' ∧ V' ⊆ V ∩ φ.toPartialEquiv.source ∧
        IsScPlusRetractionOnB P s V' ∧ s '' V' = A ∩ V' ∧
        ∃ r' : ScRetraction φ.model.E φ.model.C, r'.U ⊆ r.U ∧
          (∀ x ∈ r'.U, r'.toFun x = r.toFun x) ∧ r'.retract = φ.toPartialEquiv '' V') := by
  intro X _ _ _ P S s V φ r a hs himg hφ hr ha haφ
  let dd : P.SubData S := ⟨V, s, hs.1, hs.2.2.1, hs.2.1, hs.2.2.2.1, himg⟩
  obtain ⟨G, hG, hWG⟩ := φ.exists_isOpen_image_eq (dd.shrink_subset_source φ)
    (dd.isOpen_shrink φ)
  refine ⟨dd.shrink φ, dd.mem_shrink φ ha.1 ha.2 haφ, fun x hx => hx.1,
    retractionOnB_restrict hs (dd.isOpen_shrink φ) (dd.shrink_subset_V φ) (dd.mapsTo_shrink φ),
    by rw [show s '' dd.shrink φ = dd.r '' dd.shrink φ from rfl, dd.image_shrink, inter_comm],
    r.restrict hG, inter_subset_left, fun x _ => rfl, ?_⟩
  rw [r.restrict_retract, hr, hWG]

theorem A_to_B : A → B := by
  rintro ⟨-, hA2, -, -⟩
  refine ⟨B1, ?_⟩
  intro X _ _ _ P S s V φ r hs himg hφ hVφ hr
  rcases V.eq_empty_or_nonempty with hV0 | ⟨v, hv⟩
  · -- `V = ∅`: then `U = ∅` and `r` itself works
    have hret : r.retract = ∅ := by rw [hr, hV0, image_empty]
    have hU : r.U = ∅ := eq_empty_of_forall_notMem fun x hx => by
      have := r.apply_mem_retract hx
      rw [hret] at this; exact this
    refine ⟨r, rfl, fun x hx => by rw [hU] at hx; exact hx.elim,
      toB (isScPlus_of_U_empty r hU), ?_⟩
    rw [hret, hV0, inter_empty, image_empty]
  · have hsP := (retractionOn_iff P s V).2 hs
    let d : P.SubmanifoldData S := ⟨V, s, hs.1, hsP, himg⟩
    let x₀ : P.Level 1 := P.levelMk 1 (s v) (hsP.mem_levelSet v hv)
    let ψ := φ.restrict hVφ hs.1
    have hψ : P.IsChart ψ := MPolyfold.IsChart.restrict P hφ hVφ hs.1
    have hshr : d.toSubData.shrink ψ = V := by
      ext x
      constructor
      · intro hx; exact hx.1.1
      · intro hx; exact ⟨⟨hx, hx⟩, hsP.mapsTo hx, hsP.mapsTo hx⟩
    obtain ⟨t, ht, htp, -, hteq, G, -, htU, hWG⟩ := hA2 d hψ x₀ r hr
    rw [hshr] at ht hWG
    have hUG : t.U = r.U := by
      rw [htU]
      refine inter_eq_left.2 fun u hu => ?_
      have h1 : r.toFun u ∈ ψ.toPartialEquiv '' V := hr ▸ r.apply_mem_retract hu
      rw [hWG] at h1
      exact h1.2
    refine ⟨t, hUG, fun x hx => hteq x (hUG ▸ hx), toB htp, ?_⟩
    exact ht.trans (by rw [inter_comm V S]; rfl)

/-- The common step of `B → A`: B (2) gives the chart retraction of `exists_chartRetraction`. -/
theorem chartRetraction_of_B (hB : B) {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] {P : MPolyfold X} {S : Set X} (d : P.SubmanifoldData S) {φ : MChart X}
    (hφ : P.IsChart φ) (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ.model.O) :
    ∃ t : ScRetraction φ.model.E φ.model.C,
      t.retract = φ.toPartialEquiv '' (d.toSubData.shrink φ ∩ S) ∧
      t.IsScPlus ∧ t.U ⊆ R.U ∧
      (∀ u ∈ t.U, t.toFun u = (φ.toPartialEquiv ∘ d.s ∘ φ.symm) (R.toFun u)) ∧
      ∃ G, IsOpen G ∧ t.U = R.U ∩ R.toFun ⁻¹' G ∧
        φ.toPartialEquiv '' d.toSubData.shrink φ = φ.model.O ∩ G := by
  obtain ⟨G, hG, hWG⟩ := φ.exists_isOpen_image_eq (d.toSubData.shrink_subset_source φ)
    (d.toSubData.isOpen_shrink φ)
  have hsB : IsScPlusRetractionOnB P d.s (d.toSubData.shrink φ) :=
    retractionOnB_restrict ((retractionOn_iff P d.s d.V).1 d.isScPlusRetractionOn)
      (d.toSubData.isOpen_shrink φ) (d.toSubData.shrink_subset_V φ)
      (d.toSubData.mapsTo_shrink φ)
  have himg : d.s '' d.toSubData.shrink φ = S ∩ d.toSubData.shrink φ := by
    rw [show d.s '' d.toSubData.shrink φ = d.toSubData.r '' d.toSubData.shrink φ from rfl,
      d.toSubData.image_shrink, inter_comm]
  have hR' : (R.restrict hG).retract = φ.toPartialEquiv '' d.toSubData.shrink φ := by
    rw [R.restrict_retract, hR, hWG]
  obtain ⟨T, hTU, hT, hTp, hTret⟩ := hB.2 X P S d.s (d.toSubData.shrink φ) φ (R.restrict hG)
    hsB himg hφ (d.toSubData.shrink_subset_source φ) hR'
  refine ⟨T, by rw [hTret, inter_comm], fromB hTp, ?_, fun u hu => ?_, G, hG, hTU, hWG⟩
  · rw [hTU]; exact inter_subset_left
  · rw [hT u (hTU ▸ hu)]
    rfl

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, fun {X} _ _ _ {P} {S} d {φ} hφ _ R hR => chartRetraction_of_B hB d hφ R hR, ?_, ?_⟩
  · intro X _ _ _ P S d φ hφ _
    rw [isScSmoothRetractMap_iff_exists (φ.isScRetract_image (d.toSubData.shrink_subset_source φ)
      (d.toSubData.isOpen_shrink φ))]
    obtain ⟨R₀, hR₀⟩ := φ.model.isScRetract
    obtain ⟨G, hG, hWG⟩ := φ.exists_isOpen_image_eq (d.toSubData.shrink_subset_source φ)
      (d.toSubData.isOpen_shrink φ)
    have hR' : (R₀.restrict hG).retract = φ.toPartialEquiv '' d.toSubData.shrink φ := by
      rw [R₀.restrict_retract, hR₀, hWG]
    have hsB : IsScPlusRetractionOnB P d.s (d.toSubData.shrink φ) :=
      retractionOnB_restrict ((retractionOn_iff P d.s d.V).1 d.isScPlusRetractionOn)
        (d.toSubData.isOpen_shrink φ) (d.toSubData.shrink_subset_V φ)
        (d.toSubData.mapsTo_shrink φ)
    have himg : d.s '' d.toSubData.shrink φ = S ∩ d.toSubData.shrink φ := by
      rw [show d.s '' d.toSubData.shrink φ = d.toSubData.r '' d.toSubData.shrink φ from rfl,
        d.toSubData.image_shrink, inter_comm]
    obtain ⟨T, hTU, hT, hTp, -⟩ := hB.2 X P S d.s (d.toSubData.shrink φ) φ (R₀.restrict hG)
      hsB himg hφ (d.toSubData.shrink_subset_source φ) hR'
    have hTp' := fromB hTp
    -- on `φ(W)`, `φ ∘ s ∘ φ⁻¹ = T`
    have hTW : ∀ z ∈ φ.toPartialEquiv '' d.toSubData.shrink φ,
        (φ.toPartialEquiv ∘ d.s ∘ φ.symm) z = T.toFun z := by
      intro z hz
      have hzU : z ∈ T.U := hTU ▸ (R₀.restrict hG).retract_subset (hR' ▸ hz)
      rw [hT z (hTU ▸ hzU)]
      change _ = φ.toPartialEquiv (d.s (φ.symm ((R₀.restrict hG).toFun z)))
      rw [(R₀.restrict hG).apply_eq_self_of_mem_retract (hR' ▸ hz)]
      rfl
    refine ⟨fun z hz => ?_, R₀.restrict hG, hR', ?_⟩
    · -- maps into `O₁`
      have hzU : z ∈ T.U := hTU ▸ (R₀.restrict hG).retract_subset (hR' ▸ hz)
      have hrange := hTp'.mem_range z hzU
      rw [← hTW z hz] at hrange
      rw [ScBanach.mem_lvlSet, Function.comp_apply, φ.model.E.toBase_liftOne hrange]
      obtain ⟨x, hx, rfl⟩ := hz
      change φ.toPartialEquiv (d.s (φ.symm (φ.toPartialEquiv x))) ∈ φ.model.O
      rw [φ.symm_apply_apply (d.toSubData.shrink_subset_source φ hx)]
      exact φ.mapsTo_model _ (d.toSubData.mapsTo_shrink φ hx).1.2
    · -- `(1₀¹ ∘ ρ) ∘ r = 1₀¹ ∘ T` on `U`
      have h := hTp'.isScSmooth_lift
      rw [hTU] at h
      refine h.congr (R₀.restrict hG).isScDomain fun u hu => ?_
      simp only [Function.comp_apply]
      rw [hT u hu]
      rfl
  · intro X _ _ _ P S d φ hφ _
    obtain ⟨R, hR⟩ := φ.model.isScRetract
    obtain ⟨t, ht, htp, -⟩ := chartRetraction_of_B hB d hφ R hR
    exact ⟨t, ht, htp⟩
  · intro X _ _ _ P S d φ hφ a ha haV haφ
    obtain ⟨R, hR⟩ := φ.model.isScRetract
    obtain ⟨t, ht, htp, -⟩ := chartRetraction_of_B hB d hφ R hR
    exact lemma_4_7_i htp (ht ▸ ⟨a, ⟨d.toSubData.mem_shrink φ ha haV haφ, ha⟩, rfl⟩)

#rt_check RoundTrip.V4_30.A_to_B [Polyfold.MPolyfold.SubmanifoldData.isScSmoothRetractMap_lift,
  Polyfold.MPolyfold.SubmanifoldData.exists_chartRetraction,
  Polyfold.MPolyfold.SubmanifoldData.isScPlusRetract_image,
  Polyfold.MPolyfold.SubmanifoldData.apply_mem_smooth]
#rt_check RoundTrip.V4_30.B_to_A [Polyfold.MPolyfold.SubmanifoldData.isScSmoothRetractMap_lift,
  Polyfold.MPolyfold.SubmanifoldData.exists_chartRetraction,
  Polyfold.MPolyfold.SubmanifoldData.isScPlusRetract_image,
  Polyfold.MPolyfold.SubmanifoldData.apply_mem_smooth]
#rt_overlap RoundTrip.V4_30.B_to_A [Polyfold.MPolyfold.SubmanifoldData.isScSmoothRetractMap_lift,
  Polyfold.MPolyfold.SubmanifoldData.exists_chartRetraction,
  Polyfold.MPolyfold.SubmanifoldData.isScPlusRetract_image,
  Polyfold.MPolyfold.SubmanifoldData.apply_mem_smooth]

end RoundTrip.V4_30
