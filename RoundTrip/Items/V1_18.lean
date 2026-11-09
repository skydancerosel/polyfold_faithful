import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_18

/-! Round trip for V1_18 (Proposition 1.19: sc^{k+1} from `C^{l+1}` on `U_{m+l} → F_m`).

`A` is the conjunction of the types of the theorems in the item's declaration list:
`proposition_1_2_4_text`, `IsScSmooth.of_contDiffOn_levels_text`, `proposition_1_2_4_zero`,
`proposition_1_2_4`, `IsScSmooth.of_contDiffOn_levels`.  None has universe parameters.

Same notions: `B`'s `levelTo f (m+l) m` is `levelMap f m ∘ E.inclK m l` (pointwise, by
`toBase_inclK`); `B`'s "`f` induces `U_{m+l} → F_m`" (membership) for `l = 0` plus `C¹` on `U_m`
is the project's `IsSc0`; `sc^{k+1}` is `IsSck (k+1)`.

* `A → B`: `proposition_1_2_4_text` on the sc-domain `U`, with `IsSc0` assembled from `B`'s
  hypothesis at `l = 0`.
* `B → A` fails for a genuine reason: every conjunct of `A` is stated for an arbitrary
  `IsScDomain U`, `B` only for relatively open subsets of partial quadrants; and
  `proposition_1_2_4_zero` names the derivative family (`fderivWithin ℝ f U`), which `B` (an
  `IsSck` statement) does not.  On relatively open subsets of partial quadrants,
  `proposition_1_2_4_text`, `IsScSmooth.of_contDiffOn_levels_text`, `proposition_1_2_4` and
  `IsScSmooth.of_contDiffOn_levels` follow from `B` (`B_text_quadrant`, `B_smooth_text_quadrant`,
  `B_strong_quadrant`, `B_smooth_strong_quadrant`). -/

namespace RoundTrip.V1_18
open Polyfold Set
open scoped ContDiff

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.proposition_1_2_4_text) ∧
    (type_of% @Polyfold.IsScSmooth.of_contDiffOn_levels_text) ∧
    (type_of% @Polyfold.proposition_1_2_4_zero) ∧ (type_of% @Polyfold.proposition_1_2_4) ∧
    (type_of% @Polyfold.IsScSmooth.of_contDiffOn_levels)

theorem A_holds : A :=
  ⟨@Polyfold.proposition_1_2_4_text, @Polyfold.IsScSmooth.of_contDiffOn_levels_text,
    @Polyfold.proposition_1_2_4_zero, @Polyfold.proposition_1_2_4,
    @Polyfold.IsScSmooth.of_contDiffOn_levels⟩

/-- The blind `levelTo f (m+l) m` is the project's `levelMap f m ∘ ι`. -/
theorem levelTo_eq {E F : ScBanach} (f : E 0 → F 0) (m l : ℕ) :
    levelTo f (m + l) m = levelMap f m ∘ E.inclK m l := by
  funext x
  simp only [levelTo, levelMap, Function.comp_apply, E.toBase_inclK]

/-- `B`'s hypothesis at `l = 0` is `IsSc0`. -/
theorem isSc0_of_hyp {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0} {k : ℕ}
    (h : ∀ m l : ℕ, l ≤ k →
      (∀ x ∈ E.lvlSet U (m + l), f (E.toBase (m + l) x) ∈ Set.range (F.toBase m)) ∧
      ContDiffOn ℝ (l + 1) (levelTo f (m + l) m) (E.lvlSet U (m + l))) :
    IsSc0 E F U f :=
  ⟨fun m => (h m 0 (Nat.zero_le k)).1, fun m => (h m 0 (Nat.zero_le k)).2.continuousOn⟩

theorem A_to_B : A → B := by
  intro hA E F C U f k hU h
  refine hA.1 hU.isScDomain (isSc0_of_hyp h) fun m l hl => ?_
  rw [← levelTo_eq]
  exact (h m l hl).2

/-- The project's hypothesis (sc⁰, `C^{l+1}` on `U_{m+l} → F_m`) gives `B`'s. -/
theorem hyp_of_text {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0} {k : ℕ}
    (hf : IsSc0 E F U f)
    (h : ∀ m l, l ≤ k → ContDiffOn ℝ (l + 1) (levelMap f m ∘ E.inclK m l) (E.lvlSet U (m + l))) :
    ∀ m l : ℕ, l ≤ k →
      (∀ x ∈ E.lvlSet U (m + l), f (E.toBase (m + l) x) ∈ Set.range (F.toBase m)) ∧
      ContDiffOn ℝ (l + 1) (levelTo f (m + l) m) (E.lvlSet U (m + l)) := by
  intro m l hl
  refine ⟨fun x hx => ?_, by rw [levelTo_eq]; exact h m l hl⟩
  have := hf.mem_range m (E.inclK m l x) (E.inclK_mem_lvlSet hx)
  rwa [E.toBase_inclK] at this

/-- `B → A` on relatively open subsets of partial quadrants: `proposition_1_2_4_text`. -/
theorem B_text_quadrant (hB : B) {E F : ScBanach} {C U : Set (E 0)} {f : E 0 → F 0} {k : ℕ}
    (hU : IsRelOpenInQuadrant E C U) (hf : IsSc0 E F U f)
    (h : ∀ m l, l ≤ k → ContDiffOn ℝ (l + 1) (levelMap f m ∘ E.inclK m l) (E.lvlSet U (m + l))) :
    IsSck (k + 1) E F U f :=
  hB E F C U f k hU (hyp_of_text hf h)

/-- `B → A` on relatively open subsets of partial quadrants:
`IsScSmooth.of_contDiffOn_levels_text`. -/
theorem B_smooth_text_quadrant (hB : B) {E F : ScBanach} {C U : Set (E 0)} {f : E 0 → F 0}
    (hU : IsRelOpenInQuadrant E C U) (hf : IsSc0 E F U f)
    (h : ∀ m l : ℕ, ContDiffOn ℝ (l + 1) (levelMap f m ∘ E.inclK m l) (E.lvlSet U (m + l))) :
    IsScSmooth U f := by
  intro k
  cases k with
  | zero => exact hf
  | succ k => exact B_text_quadrant hB hU hf fun m l _ => h m l

/-- `C^{k+1}` on every level gives `C^{l+1}` on `U_{m+l} → F_m` for `l ≤ k`. -/
theorem text_of_strong {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0} {k : ℕ}
    (h : ∀ m, ContDiffOn ℝ (k + 1) (levelMap f m) (E.lvlSet U m)) :
    ∀ m l, l ≤ k → ContDiffOn ℝ (l + 1) (levelMap f m ∘ E.inclK m l) (E.lvlSet U (m + l)) := by
  intro m l hl
  refine ((h m).comp (E.inclK m l).contDiff.contDiffOn fun x hx => E.inclK_mem_lvlSet hx).of_le ?_
  exact_mod_cast Nat.add_le_add_right hl 1

/-- `B → A` on relatively open subsets of partial quadrants: `proposition_1_2_4`. -/
theorem B_strong_quadrant (hB : B) {E F : ScBanach} {C U : Set (E 0)} {f : E 0 → F 0} {k : ℕ}
    (hU : IsRelOpenInQuadrant E C U) (hf : IsSc0 E F U f)
    (h : ∀ m, ContDiffOn ℝ (k + 1) (levelMap f m) (E.lvlSet U m)) : IsSck (k + 1) E F U f :=
  B_text_quadrant hB hU hf (text_of_strong h)

/-- `B → A` on relatively open subsets of partial quadrants: `IsScSmooth.of_contDiffOn_levels`. -/
theorem B_smooth_strong_quadrant (hB : B) {E F : ScBanach} {C U : Set (E 0)} {f : E 0 → F 0}
    (hU : IsRelOpenInQuadrant E C U)
    (hmem : ∀ m, ∀ x ∈ E.lvlSet U m, f (E.toBase m x) ∈ range (F.toBase m))
    (h : ∀ m, ContDiffOn ℝ ∞ (levelMap f m) (E.lvlSet U m)) : IsScSmooth U f := by
  have hf : IsSc0 E F U f := ⟨hmem, fun m => (h m).continuousOn⟩
  intro k
  cases k with
  | zero => exact hf
  | succ k =>
    exact B_strong_quadrant hB hU hf fun m => (h m).of_le (by exact_mod_cast le_top)

/-- An sc¹ derivative family can be replaced by one agreeing with it on `U₁`. -/
theorem isSc1With_congr_deriv {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0}
    {D D' : E 1 → E 0 →L[ℝ] F 0} (h : IsSc1With U f D) (hD : ∀ x ∈ E.lvlSet U 1, D x = D' x) :
    IsSc1With U f D' where
  isSc0 := h.isSc0
  hasFDerivWithinAt x hx := by rw [← hD x hx]; exact h.hasFDerivWithinAt x hx
  tangent_isSc0 := h.tangent_isSc0.congr fun p hp => by
    change (levelMap f 1 p.1, D p.1 p.2) = (levelMap f 1 p.1, D' p.1 p.2)
    rw [hD p.1 hp]

/-- `B → A` on relatively open subsets of partial quadrants: `proposition_1_2_4_zero`, with its
derivative family `fderivWithin ℝ f U` (identified with the family given by `B` through the
uniqueness of derivatives on `U₁` and the density of `E₁` in `E₀`). -/
theorem B_zero_quadrant (hB : B) {E F : ScBanach} {C U : Set (E 0)} {f : E 0 → F 0}
    (hUC : IsRelOpenInQuadrant E C U) (hf : IsSc0 E F U f)
    (h : ∀ m, ContDiffOn ℝ 1 (levelMap f m) (E.lvlSet U m)) :
    IsSc1With U f fun x => fderivWithin ℝ f U (E.toBase 1 x) := by
  have hU := hUC.isScDomain
  have hk : ∀ m, ContDiffOn ℝ ((0 : ℕ) + 1) (levelMap f m) (E.lvlSet U m) := fun m => by
    simpa using h m
  obtain ⟨D, hD⟩ := (B_strong_quadrant (k := 0) hB hUC hf hk).1
  refine isSc1With_congr_deriv hD fun x hx => ?_
  have h0 : ContDiffOn ℝ 1 f U := by
    have := h 0
    rwa [funext (levelMap_zero f), ScBanach.lvlSet_zero] at this
  have hd : HasFDerivWithinAt f (fderivWithin ℝ f U (E.toBase 1 x)) U (E.toBase 1 x) :=
    (h0.differentiableOn one_ne_zero _ hx).hasFDerivWithinAt
  have h2 : HasFDerivWithinAt (f ∘ E.toBase 1) ((fderivWithin ℝ f U (E.toBase 1 x)).comp
      (E.toBase 1)) (E.lvlSet U 1) x :=
    hd.comp x (E.toBase 1).hasFDerivWithinAt (E.mapsTo_toBase_lvlSet U 1)
  have h1 := (hU.uniqueDiffWithinAt 1 x hx).eq (hD.hasFDerivWithinAt x hx) h2
  have hdense : Dense (Submodule.span ℝ (range (E.toBase 1)) : Set (E 0)) :=
    Dense.mono Submodule.subset_span (E.denseRange_inclK 0 1)
  refine ContinuousLinearMap.ext_on hdense ?_
  rintro _ ⟨y, rfl⟩
  exact congrArg (fun L : E 1 →L[ℝ] F 0 => L y) h1

#rt_check RoundTrip.V1_18.B_zero_quadrant [Polyfold.proposition_1_2_4_text,
  Polyfold.IsScSmooth.of_contDiffOn_levels_text, Polyfold.proposition_1_2_4_zero,
  Polyfold.proposition_1_2_4, Polyfold.IsScSmooth.of_contDiffOn_levels]
#rt_check RoundTrip.V1_18.A_to_B [Polyfold.proposition_1_2_4_text,
  Polyfold.IsScSmooth.of_contDiffOn_levels_text, Polyfold.proposition_1_2_4_zero,
  Polyfold.proposition_1_2_4, Polyfold.IsScSmooth.of_contDiffOn_levels]
#rt_check RoundTrip.V1_18.B_smooth_text_quadrant [Polyfold.proposition_1_2_4_text,
  Polyfold.IsScSmooth.of_contDiffOn_levels_text, Polyfold.proposition_1_2_4_zero,
  Polyfold.proposition_1_2_4, Polyfold.IsScSmooth.of_contDiffOn_levels]
#rt_check RoundTrip.V1_18.B_smooth_strong_quadrant [Polyfold.proposition_1_2_4_text,
  Polyfold.IsScSmooth.of_contDiffOn_levels_text, Polyfold.proposition_1_2_4_zero,
  Polyfold.proposition_1_2_4, Polyfold.IsScSmooth.of_contDiffOn_levels]

end RoundTrip.V1_18
