import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_19

/-! Round trip for V3_19 (Lemma 3.17: fillers are stable under sc⁺-sections).
Refreshed 2026-11-02 against HEAD (new conjuncts: Lemma 3.17 for filling germs).

`A` is the conjunction of the types of `Polyfold.IsFillingGerm.add_section_germ`,
`Polyfold.IsFillingGerm.add_section`, `Polyfold.lemma_3_17` and `Polyfold.IsFillerOf.congr_left`
(no universe parameters).

* At the audit A only had the whole-chart filler `IsFillerOf` (no regularity of `g`, the fill
  defect `k(y) = [1 − ρ(r(y))]g(y)` sc¹ on all of `U`), which B's germ fillers do not satisfy.
  A now contains the germ reading: `IsFillingGerm.add_section` (`g` a filling germ, `ŝ`
  sc-smooth on `U` with the section property on `O` ⟹ `g + ŝ ∘ r` a filling germ of `f̂ + ŝ`) and
  `add_section_germ` (`ŝ` itself a germ).
* `A → B` is now PROVED FROM A (`A_to_B`, through `add_section`).  Glue: B's `IsFillingB` is an
  `IsFillingGerm` (`Dr(0) = scDeriv U r 0` by uniqueness; B's bijection with bounded inverse is a
  `≃L` of the kernels); B's sc⁺-section `s` enters as `ŝ'' = ι ∘ ŝ ∘ r`, sc-smooth on `U` (the
  retract-map chain rule) and a section on `O`; the resulting filling germ of `f̂ + ŝ''` with filler
  `g + ŝ'' ∘ r` is turned back into B's `IsFillingB` for `f̂ + ŝ` and `g + ŝ ∘ r` (both agree on
  `U` since `r ∘ r = r` there, and on `O` since `r = id` there; the `≃L` gives back a bijection
  with bounded inverse).  The audit's outright proof `B_holds` is kept.
* `B → A` fails genuinely: `lemma_3_17` and `IsFillerOf.congr_left` are about the whole-chart
  `IsFillerOf` with an arbitrary `s : E₀ → F₀` (no regularity), `add_section`/`add_section_germ`
  about an arbitrary `ŝ` sc-smooth on `U` (resp. a germ) with only the section property; B only
  covers the principal parts of sc⁺-sections of a tame bundle and sc-smooth `f`.
-/

namespace RoundTrip.V3_19
open Polyfold Set Filter Topology

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsFillingGerm.add_section_germ) ∧
  (type_of% @Polyfold.IsFillingGerm.add_section) ∧
  (type_of% @Polyfold.lemma_3_17) ∧ (type_of% @Polyfold.IsFillerOf.congr_left)

theorem A_holds : A :=
  ⟨@Polyfold.IsFillingGerm.add_section_germ, @Polyfold.IsFillingGerm.add_section,
    @Polyfold.lemma_3_17, @Polyfold.IsFillerOf.congr_left⟩

/-- **`B` holds** (outright; `lemma_3_17` cannot be applied to germ fillers). -/
theorem B_holds : B := by
  intro E F C U R hU hR _ h0 _ f s g _ hs hfill
  have hUd := hU.isScDomain
  have hC : IsQuadrantLike E C := hU.isPartialQuadrant.isQuadrantLike
  -- `s̃ = ι ∘ ŝ ∘ r`
  set st : E.lvl 0 → F.lvl 0 := fun u => F.toBase 1 (s ((R (u, 0)).1)).2 with hst
  -- (F1) `r = id` on `O`
  have hF1 : ∀ x ∈ (fun u => (R (u, 0)).1) '' U, (R (x, 0)).1 = x := fun x hx =>
    StrongRetr.r_eq_self hR hx
  -- (F2) `ρ(r(y)) s̃(y) = s̃(y)` on `U`
  have hF2 : ∀ y ∈ U, (R ((R (y, 0)).1, st y)).2 = st y := by
    intro y hy
    have hry : (R (y, 0)).1 ∈ (fun u => (R (u, 0)).1) '' U := ⟨y, hy, rfl⟩
    have hK := hs.mem hry
    rw [hs.fst_eq _ hry] at hK
    exact StrongRetr.ρ_eq_self_of_mem_K hR (StrongRetr.r_mem hR hy) hK
  -- (F3) linearity of `ρ(r(y))`
  have hF3 : ∀ y ∈ U, ∀ a b : F.lvl 0,
      (R ((R (y, 0)).1, a + b)).2 = (R ((R (y, 0)).1, a)).2 + (R ((R (y, 0)).1, b)).2 :=
    fun y hy a b => (StrongRetr.ρ_isLinear hR (StrongRetr.r_mem hR hy)).map_add a b
  -- (F4) the map `k` is unchanged on `U`
  have hF4 : EqOn (fun y => g y - (R ((R (y, 0)).1, g y)).2)
      (fun y => (g y + st y) - (R ((R (y, 0)).1, g y + st y)).2) U := by
    intro y hy
    simp only
    rw [hF3 y hy, hF2 y hy]
    abel
  obtain ⟨⟨G, hGU, hGs, Dk, hDk, Dr, hDr, hbij, c, hc⟩, h1, h2⟩ := hfill
  -- `s̃` is sc-smooth on `U`, hence an sc-smooth germ on `G`
  have hlift : IsScSmooth (F := F.shift) U fun u => (s ((R (u, 0)).1)).2 :=
    ((hs.isScSmooth.comp_isScSmooth (hR.baseRetraction hU) rfl).snd hUd).congr hUd
      fun _ _ => rfl
  have hsm : IsScSmooth U st := (hlift.toBase_shift hUd).congr hUd fun _ _ => rfl
  have hsG : IsScSmoothGerm G st :=
    (hsm.isScSmoothGerm hC hU.relOpen h0).mono hC fun m x hx => hGU _ (G.toBase_mem hx)
  have hgs : IsScSmoothGerm G fun u => g u + st u := fun k =>
    IsSckGerm.congr hC (fun _ _ => rfl) (((hGs.pair hC hsG) k).operator_comp hC F.addOp)
  refine ⟨⟨G, hGU, hgs, Dk, hDk.congr fun y hy => hF4 (hGU y hy), Dr, hDr, hbij, c, hc⟩, ?_, ?_⟩
  · filter_upwards [h1] with x hx hxO
    rw [hx hxO]
    rw [hF1 x hxO]
  · filter_upwards [h2] with y hy hyU hfix
    refine hy hyU ?_
    change g y + st y = (R ((R (y, 0)).1, g y + st y)).2 at hfix
    rw [hF3 y hyU, hF2 y hyU] at hfix
    exact add_right_cancel hfix

/-! ### A ⇒ B through A's `IsFillingGerm.add_section` -/

section Glue

/-- A bijection between kernels with a bounded inverse is a topological isomorphism. -/
theorem kerEquiv_of_bij {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (p : V →L[ℝ] V) (q : W →L[ℝ] W) (L : V →L[ℝ] W)
    (hbij : Set.BijOn L {v | p v = 0} {w | q w = 0}) (c : ℝ)
    (hc : ∀ v : V, p v = 0 → ‖v‖ ≤ c * ‖L v‖) :
    ∃ Φ : LinearMap.ker (p : V →ₗ[ℝ] V) ≃L[ℝ] LinearMap.ker (q : W →ₗ[ℝ] W),
      ∀ v, (Φ v : W) = L v := by
  have hmaps : ∀ v : LinearMap.ker (p : V →ₗ[ℝ] V), L v ∈ LinearMap.ker (q : W →ₗ[ℝ] W) :=
    fun v => hbij.1 v.2
  let φ : LinearMap.ker (p : V →ₗ[ℝ] V) →ₗ[ℝ] LinearMap.ker (q : W →ₗ[ℝ] W) :=
    ((L : V →ₗ[ℝ] W).domRestrict _).codRestrict _ hmaps
  have hφ : ∀ v, (φ v : W) = L v := fun v => rfl
  have hinj : Function.Injective φ := by
    intro v₁ v₂ heq
    have : L v₁ = L v₂ := by rw [← hφ, ← hφ, heq]
    exact Subtype.ext (hbij.2.1 v₁.2 v₂.2 this)
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨v, hv, hvw⟩ := hbij.2.2 w.2
    exact ⟨⟨v, hv⟩, Subtype.ext hvw⟩
  let e := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ v, (e v : W) = L v := fun v => rfl
  refine ⟨e.toContinuousLinearEquivOfBounds ‖L‖ c (fun v => ?_) (fun w => ?_), fun v => he v⟩
  · rw [show ‖e v‖ = ‖L v‖ from congrArg norm (he v)]
    exact L.le_opNorm _
  · have h3 := hc (e.symm w) (e.symm w).2
    have h4 : L (e.symm w) = w := by rw [← he, e.apply_symm_apply]
    rw [h4] at h3
    exact h3

/-- Conversely, a `≃L` of kernels given by `L` is a bijection with a bounded inverse. -/
theorem bij_of_kerEquiv {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (p : V →L[ℝ] V) (q : W →L[ℝ] W) (L : V →L[ℝ] W)
    (Φ : LinearMap.ker (p : V →ₗ[ℝ] V) ≃L[ℝ] LinearMap.ker (q : W →ₗ[ℝ] W))
    (hΦ : ∀ v, (Φ v : W) = L v) :
    Set.BijOn L {v | p v = 0} {w | q w = 0} ∧ ∃ c : ℝ, ∀ v, p v = 0 → ‖v‖ ≤ c * ‖L v‖ := by
  refine ⟨⟨fun v hv => ?_, fun v₁ hv₁ v₂ hv₂ heq => ?_, fun w hw => ?_⟩,
    ‖Φ.symm.toContinuousLinearMap‖, fun v hv => ?_⟩
  · have := (Φ ⟨v, hv⟩).2
    rw [hΦ ⟨v, hv⟩] at this
    exact this
  · have : Φ ⟨v₁, hv₁⟩ = Φ ⟨v₂, hv₂⟩ := by
      apply Subtype.ext
      rw [hΦ, hΦ]
      exact heq
    exact congrArg Subtype.val (Φ.injective this)
  · refine ⟨(Φ.symm ⟨w, hw⟩ : V), (Φ.symm ⟨w, hw⟩).2, ?_⟩
    have := hΦ (Φ.symm ⟨w, hw⟩)
    rw [ContinuousLinearEquiv.apply_symm_apply] at this
    exact this.symm
  · have e1 : (⟨v, hv⟩ : LinearMap.ker (p : V →ₗ[ℝ] V)) = Φ.symm (Φ ⟨v, hv⟩) :=
      (Φ.symm_apply_apply _).symm
    have e2 : ‖v‖ = ‖(⟨v, hv⟩ : LinearMap.ker (p : V →ₗ[ℝ] V))‖ := rfl
    have e3 : ‖Φ ⟨v, hv⟩‖ = ‖L v‖ := by rw [← hΦ ⟨v, hv⟩]; rfl
    rw [e2, e1, ← e3]
    exact Φ.symm.toContinuousLinearMap.le_opNorm _

end Glue

/-- **A ⇒ B** (germ reading), through A's `IsFillingGerm.add_section`. -/
theorem A_to_B : A → B := by
  rintro ⟨-, hadd, -⟩ E F C U R hU hR _ h0 hr0 f s g _ hs hfill
  have hUd := hU.isScDomain
  have hC : IsQuadrantLike E C := hU.isPartialQuadrant.isQuadrantLike
  obtain ⟨⟨G, hGU, hGs, Dk, hDk, Dr, hDr, hbij, c, hc⟩, h1, h2⟩ := hfill
  have h01 : (0 : E.lvl 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have hDr0 : Dr 0 = scDeriv U (StrongRetr.r R) 0 :=
    (IsSc1.scDeriv_eqOn hDr (hUd.uniqueDiffWithinAt 1) h01).symm
  rw [hDr0] at hbij hc
  -- B's filling is a filling germ
  obtain ⟨Φ₀, hΦ₀⟩ := kerEquiv_of_bij (scDeriv U (StrongRetr.r R) 0) (StrongRetr.ρCLM hR h0)
    (Dk 0) hbij c hc
  have hFG : IsFillingGerm hU hR h0 (fun x => (f x).2) g :=
    ⟨h1, h2, ⟨G, hGU, hGs, Dk, hDk, Φ₀, hΦ₀⟩⟩
  -- `ŝ'' = ι ∘ ŝ ∘ r`: sc-smooth on `U`, a section on `O`
  set st : E.lvl 0 → F.lvl 0 := fun u => F.toBase 1 (s (StrongRetr.r R u)).2 with hst
  have hlift : IsScSmooth (F := F.shift) U fun u => (s ((R (u, 0)).1)).2 :=
    ((hs.isScSmooth.comp_isScSmooth (hR.baseRetraction hU) rfl).snd hUd).congr hUd
      fun _ _ => rfl
  have hsm : IsScSmooth U st := (hlift.toBase_shift hUd).congr hUd fun _ _ => rfl
  have hsK : ∀ x ∈ StrongRetr.r R '' U, (x, st x) ∈ R '' (U ×ˢ univ) := by
    intro x hx
    have hK := hs.mem hx
    rw [hs.fst_eq _ hx] at hK
    show (x, F.toBase 1 (s (StrongRetr.r R x)).2) ∈ _
    rw [StrongRetr.r_eq_self hR hx]
    exact hK
  obtain ⟨e1, e2, G', hG'U, hG's, Dk', hDk', Φ', hΦ'⟩ := hadd hU hR h0 hFG hsm hsK
  -- back to B's notion, for `g + ŝ ∘ r` (equal to `g + ŝ'' ∘ r` on `U`)
  have heqU : ∀ y ∈ U, g y + st (StrongRetr.r R y) = g y + F.toBase 1 (s ((R (y, 0)).1)).2 := by
    intro y hy
    show g y + F.toBase 1 (s (StrongRetr.r R (StrongRetr.r R y))).2 = _
    rw [StrongRetr.r_r hR hy]
    rfl
  refine ⟨⟨G', hG'U, fun k => IsSckGerm.congr hC (fun y hy => heqU y (hG'U hy)) (hG's k), Dk',
    hDk'.congr fun y hy => ?_, Dr, hDr, ?_⟩, ?_, ?_⟩
  · simp only [fillDefect]
    rw [heqU y (hG'U hy)]
    rfl
  · rw [hDr0]
    exact bij_of_kerEquiv _ (StrongRetr.ρCLM hR h0) (Dk' 0) Φ' hΦ'
  · filter_upwards [e1] with x hx hxO
    have hrx : StrongRetr.r R x = x := StrongRetr.r_eq_self hR hxO
    have e := hx hxO
    change (f x).2 + F.toBase 1 (s (StrongRetr.r R x)).2 =
      g x + F.toBase 1 (s (StrongRetr.r R (StrongRetr.r R x))).2 at e
    rw [hrx, hrx] at e
    change _ = g x + F.toBase 1 (s (StrongRetr.r R x)).2
    rw [hrx]
    exact e
  · filter_upwards [e2] with y hy hyU hfix
    refine hy hyU ?_
    rw [heqU y hyU]
    exact hfix

#rt_check RoundTrip.V3_19.A_to_B [Polyfold.IsFillingGerm.add_section_germ,
  Polyfold.IsFillingGerm.add_section, Polyfold.lemma_3_17, Polyfold.IsFillerOf.congr_left]
#rt_check RoundTrip.V3_19.B_holds [Polyfold.IsFillingGerm.add_section_germ,
  Polyfold.IsFillingGerm.add_section, Polyfold.lemma_3_17, Polyfold.IsFillerOf.congr_left]
#rt_overlap RoundTrip.V3_19.B_holds [Polyfold.IsFillingGerm.add_section_germ,
  Polyfold.IsFillingGerm.add_section, Polyfold.lemma_3_17, Polyfold.IsFillerOf.congr_left]

end RoundTrip.V3_19
