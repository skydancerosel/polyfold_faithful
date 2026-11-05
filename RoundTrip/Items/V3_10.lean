import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_10

/-! Round trip for V3_10 (Definition 3.7: basic germs).

The listed declarations `Polyfold.IsBasicGerm` and `Polyfold.IsSc0ContractionGerm` are both
definitions (structures), so `A = True`; the content of the audit is the comparison of the
project's definitions with B's notions, which is B itself, proved outright here (`B_holds`).

* project ⇒ B (`proj_to_B`): sc-smoothness and `f(0) = 0` are the same fields; `B(0,0) = 0` follows
  from `f(0) = 0`; the project's `B` agrees with `w − P_W f` on `U₀` (`snd_eq`), so its level-`m`
  values `levelB B m (a, w)` (which exist since `B` is an sc⁰-germ) are B's lifts `b`, and the
  project's contraction radius works for B's `δ` (points of `U_m` have `a ∈ C̃`).
* B ⇒ project (`B_to_proj`) with the project's `B := BB f = w − P_W f`: `snd_eq` holds everywhere;
  `BB f` is an sc⁰-germ because `f` is (level-`m` value `x.2 − (f_m x).2`); and the project's
  extra requirement that the points `(a, w)`, `a ∈ C̃`, `|a|, |w|_m < r`, lie in `U_m` holds for
  small `r` because `U_m` is relatively open in `C̃ × W_m` around `0` (the norm on `ℝⁿ × W_m` is
  the max norm).
-/

namespace RoundTrip.V3_10
open Polyfold Set

/-- Only definitions are listed: `A = True`. -/
def A : Prop := True

theorem A_holds : A := trivial

section Glue
variable {n k N : ℕ} {W : ScBanach} {G : ScNbhdGerm (EB n W) (CtB n k ×ˢ Set.univ)}
  {f : (Fin n → ℝ) × W.lvl 0 → (Fin N → ℝ) × W.lvl 0}

lemma fst_mem {m : ℕ} {a : Fin n → ℝ} {w : W.lvl m} (h : ((a, w) : (EB n W).lvl m) ∈ G.U m) :
    a ∈ CtB n k := by
  have := G.U_subset m h
  rw [ScBanach.paramProd_lvlSet] at this
  exact this.1

lemma BB_zero (hf0 : f 0 = 0) : BB f (0, 0) = 0 := by
  simp [BB, Prod.mk_zero_zero, hf0]

/-- Level-`m` value of `BB f` for an sc⁰-germ `f`. -/
lemma toBase_BB (hf : IsSc0Germ (F := EB N W) G f) {m : ℕ} {x : (EB n W).lvl m}
    (hx : x ∈ G.U m) :
    W.toBase m (x.2 - (levelMap (E := EB n W) (F := EB N W) f m x).2) =
      BB f ((EB n W).toBase m x) := by
  have h1 := hf.toBase_levelMap hx
  rw [ScBanach.paramProd_toBase, ScBanach.paramProd_toBase] at h1
  rw [ScBanach.paramProd_toBase, BB, map_sub, ← h1]

theorem proj_to_B {Bf : (Fin n → ℝ) × W.lvl 0 → W.lvl 0}
    (h : IsBasicGerm (CtB n k) G f Bf) : IsBasicGermB n k N W G f := by
  refine ⟨h.isScSmooth, h.f_zero, BB_zero h.f_zero, ?_⟩
  intro ε hε m
  obtain ⟨r, hr, hc⟩ := h.contraction.contraction ε hε m
  refine ⟨r, hr, fun a w w' hw hw' ha hwr hw'r => ?_⟩
  have haC := fst_mem hw
  obtain ⟨-, hest⟩ := hc a haC ha w w' hwr hw'r
  have key : ∀ v : W.lvl m, ((a, v) : (EB n W).lvl m) ∈ G.U m →
      W.toBase m (levelB Bf m (a, v)) = BB f (a, W.toBase m v) := by
    intro v hv
    rw [levelB, h.contraction.isSc0.toBase_levelMap hv, ScBanach.paramProd_toBase]
    have := h.snd_eq _ (G.toBase_mem hv)
    rw [ScBanach.paramProd_toBase] at this
    rw [BB, this]
    abel
  exact ⟨levelB Bf m (a, w), levelB Bf m (a, w'), key w hw, key w' hw', hest⟩

theorem B_to_proj (h : IsBasicGermB n k N W G f) : IsBasicGerm (CtB n k) G f (BB f) := by
  obtain ⟨hs, hf0, hB0, hc⟩ := h
  have hf : IsSc0Germ (F := EB N W) G f := (hs 0)
  refine ⟨hs, hf0, fun x _ => by simp [BB], ⟨⟨fun m x hx => ⟨_, toBase_BB hf hx⟩, fun m => ?_⟩,
    hB0, ?_⟩⟩
  · have hcont := hf.continuousOn m
    refine (continuous_snd.continuousOn.sub (continuous_snd.comp_continuousOn hcont)).congr ?_
    intro x hx
    exact levelMap_eq_of_toBase_eq (toBase_BB hf hx)
  · intro ε hε m
    obtain ⟨O, hO, hUO⟩ := G.relOpen m
    have h0O : (0 : (EB n W).lvl m) ∈ O := by
      have := G.zero_mem m; rw [hUO] at this; exact this.1
    obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO 0 h0O
    obtain ⟨δ, hδ, hcδ⟩ := hc ε hε m
    refine ⟨min ρ δ, lt_min hρ hδ, fun a ha har w w' hwr hw'r => ?_⟩
    have hmem : ∀ v : W.lvl m, ‖v‖ < min ρ δ → ((a, v) : (EB n W).lvl m) ∈ G.U m := by
      intro v hv
      rw [hUO]
      refine ⟨hρO ?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, Prod.norm_mk]
        exact max_lt (har.trans_le (min_le_left _ _)) (hv.trans_le (min_le_left _ _))
      · rw [ScBanach.paramProd_lvlSet]; exact ⟨ha, mem_univ _⟩
    refine ⟨hmem w hwr, ?_⟩
    obtain ⟨b, b', hb, hb', hest⟩ := hcδ a w w' (hmem w hwr) (hmem w' hw'r)
      (har.trans_le (min_le_right _ _)) (hwr.trans_le (min_le_right _ _))
      (hw'r.trans_le (min_le_right _ _))
    have e1 : levelB (BB f) m (a, w) = b :=
      levelMap_eq_of_toBase_eq (by rw [hb, ScBanach.paramProd_toBase])
    have e2 : levelB (BB f) m (a, w') = b' :=
      levelMap_eq_of_toBase_eq (by rw [hb', ScBanach.paramProd_toBase])
    rw [e1, e2]; exact hest

theorem B_holds : B := by
  intro n k N W _ G f
  exact ⟨fun ⟨Bf, h⟩ => proj_to_B h, fun h => ⟨BB f, B_to_proj h⟩⟩

end Glue

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V3_10.A_to_B []
#rt_check RoundTrip.V3_10.B_to_A []
#rt_overlap RoundTrip.V3_10.B_to_A []
#rt_check RoundTrip.V3_10.B_holds []

end RoundTrip.V3_10
