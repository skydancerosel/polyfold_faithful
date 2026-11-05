import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_25

/-!
Round trip for V3_25 (Definition 3.28).  The listed declarations (`Polyfold.IsSc0ContractionGerm`,
`Polyfold.ContractionGerm`, `Polyfold.IsSc0ContractionGerm.toContractionGerm`,
`Polyfold.contractionMap`) are all definitions, so `A = True`.  B is the vocabulary check
"the project's `IsSc0ContractionGerm` is the text's Definition 3.28" (`IsSc0ContractionGermText`),
and it is proved here outright (`iff_text`, no partial-quadrant hypothesis needed):

* sc⁰ of `B` ⇔ sc⁰ of `f = w − B(a, w)`: `contractionMap` is an involution and preserves sc⁰.
* `B(0, 0) = 0` ⇔ `f(0, 0) = 0`.
* The project's estimate quantifies over `a ∈ C̃`, `|a|, |w|_m, |w'|_m < r` and *asserts* that
  `(a, w) ∈ U_m`; the text's quantifies over `(a, w), (a, w') ∈ U_m` near `0`.  The two agree
  because `U_m` is relatively open in `C̃ × W_m` and contains `0`, so it contains every such small
  `(a, w)`; the level-`m` values `B_m(a, w)` (project: `levelMap`, text: any preimage) agree on
  `U_m` because `B` is sc⁰.
-/

namespace RoundTrip.V3_25
open Polyfold

/-- The listed declarations are all definitions: the project's formal statement is `True`. -/
def A : Prop := True

theorem A_holds : A := trivial

section Glue

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}

/-- `x ↦ x.2 − g x` is an sc⁰-germ when `g` is. -/
theorem isSc0Germ_contractionMap {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ Set.univ)}
    {g : P × W.lvl 0 → W.lvl 0} (hg : IsSc0Germ (F := W) G g) :
    IsSc0Germ (F := W) G (contractionMap g) := by
  have hlev : ∀ m, ∀ x ∈ G.U m, levelMap (E := ScBanach.paramProd P W) (F := W)
      (contractionMap g) m x = x.2 - levelMap (E := ScBanach.paramProd P W) (F := W) g m x := by
    intro m x hx
    apply levelMap_eq_of_toBase_eq
    rw [map_sub, hg.toBase_levelMap hx, ScBanach.paramProd_toBase]
    rfl
  refine ⟨fun m x hx => ?_, fun m => ?_⟩
  · refine ⟨x.2 - levelMap (E := ScBanach.paramProd P W) (F := W) g m x, ?_⟩
    rw [map_sub, hg.toBase_levelMap hx, ScBanach.paramProd_toBase]
    rfl
  · exact (continuous_snd.continuousOn.sub (hg.continuousOn m)).congr fun x hx => hlev m x hx

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma contractionMap_contractionMap (g : P × W.lvl 0 → W.lvl 0) :
    contractionMap (contractionMap g) = g := by
  funext p
  change p.2 - (p.2 - g p) = g p
  abel

/-- The ball around `0` in `U_m`: `U_m` is relatively open in `C̃ × W_m` and contains `0`. -/
lemma exists_ball_sub (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ Set.univ)) (m : ℕ) :
    ∃ ρ > 0, ∀ a ∈ Ct, ‖a‖ < ρ → ∀ w : W.lvl m, ‖w‖ < ρ →
      ((a, w) : P × W.lvl m) ∈ G.U m := by
  obtain ⟨O, hO, hU⟩ := G.relOpen m
  have h0 : (0 : (ScBanach.paramProd P W) m) ∈ O := by
    have := G.zero_mem m; rw [hU] at this; exact this.1
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hO _ h0
  refine ⟨ρ, hρ, fun a ha har w hwr => ?_⟩
  rw [hU, ScBanach.paramProd_lvlSet]
  refine ⟨hball ?_, ha, Set.mem_univ _⟩
  rw [Metric.mem_ball, dist_zero_right]
  show ‖((a, w) : P × W.lvl m)‖ < ρ
  rw [Prod.norm_mk]
  exact max_lt har hwr

/-- **Definition 3.28**: the project's `IsSc0ContractionGerm` is the text's notion. -/
theorem iff_text (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ Set.univ))
    (Bm : P × W.lvl 0 → W.lvl 0) :
    IsSc0ContractionGerm Ct G Bm ↔ IsSc0ContractionGermText Ct G Bm := by
  constructor
  · intro h
    refine ⟨isSc0Germ_contractionMap h.isSc0, ?_, fun ε hε m => ?_⟩
    · change (0 : W.lvl 0) - Bm (0, 0) = 0
      rw [h.B_zero, sub_zero]
    obtain ⟨r, hr, H⟩ := h.contraction ε hε m
    refine ⟨r, hr, fun a w w' hw _ ha hwr hw'r y y' hy hy' => ?_⟩
    have haC : a ∈ Ct := by
      have := G.U_subset m hw
      rw [ScBanach.paramProd_lvlSet] at this
      exact this.1
    have ey : levelB Bm m (a, w) = y := levelMap_eq_of_toBase_eq (by
      rw [ScBanach.paramProd_toBase]; exact hy)
    have ey' : levelB Bm m (a, w') = y' := levelMap_eq_of_toBase_eq (by
      rw [ScBanach.paramProd_toBase]; exact hy')
    rw [← ey, ← ey']
    exact (H a haC ha w w' hwr hw'r).2
  · rintro ⟨h0, hz, H⟩
    have hB : IsSc0Germ (F := W) G Bm := by
      have := isSc0Germ_contractionMap h0
      rwa [contractionMap_contractionMap] at this
    refine ⟨hB, ?_, fun ε hε m => ?_⟩
    · change (0 : W.lvl 0) - Bm (0, 0) = 0 at hz
      exact (sub_eq_zero.1 hz).symm
    obtain ⟨r, hr, H'⟩ := H ε hε m
    obtain ⟨ρ, hρ, hball⟩ := exists_ball_sub G m
    refine ⟨min r ρ, lt_min hr hρ, fun a ha har w w' hwr hw'r => ?_⟩
    have hw : ((a, w) : P × W.lvl m) ∈ G.U m :=
      hball a ha (har.trans_le (min_le_right _ _)) w (hwr.trans_le (min_le_right _ _))
    have hw' : ((a, w') : P × W.lvl m) ∈ G.U m :=
      hball a ha (har.trans_le (min_le_right _ _)) w' (hw'r.trans_le (min_le_right _ _))
    refine ⟨hw, H' a w w' hw hw' (har.trans_le (min_le_left _ _))
      (hwr.trans_le (min_le_left _ _)) (hw'r.trans_le (min_le_left _ _)) _ _ ?_ ?_⟩
    · rw [hB.toBase_levelMap hw, ScBanach.paramProd_toBase]
    · rw [hB.toBase_levelMap hw', ScBanach.paramProd_toBase]

end Glue

/-- B holds outright (it is a statement about definitions). -/
theorem B_holds : B := fun _ _ _ _ _ Ct G Bm _ => iff_text (Ct := Ct) G Bm

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V3_25.A_to_B []
#rt_check RoundTrip.V3_25.B_to_A []
#rt_overlap RoundTrip.V3_25.B_to_A []

end RoundTrip.V3_25
