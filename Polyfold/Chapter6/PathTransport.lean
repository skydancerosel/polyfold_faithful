import Polyfold.Chapter6.ScHomotopy

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5, p. 228:
the proof of **Theorem 6.37** (the transport of orientations along sc-smooth paths by a finite
covering, and its independence of the homotopy class) *(book 2017: Theorem 6.2, p. 213; see
`BookConcordance.md`)*.

# Transport along sc-smooth paths from local push-forwards

## The text, paraphrased

(Theorem 6.37) For a strong bundle over a tame M-polyfold `X` and an sc-Fredholm section `f`
there is a uniquely determined functor `Γ_f` from the category `P_X` (smooth points, sc-smooth
homotopy classes `[φ]` of paths with end points fixed) to the sets `Or_x^f`, with the property
(∗): for an sc-smooth path `φ` in a neighbourhood `U` with the local propagation property,
`Γ_f([φ])` is the local propagation `φ_* : Or_{φ(0)}^f → Or_{φ(1)}^f`.  (Proof) For the
sc-smooth path `φ : [0, 1] → X` and `t₀ ∈ [0, 1]` choose an orientable neighbourhood
`U(φ(t₀))`; there is an open interval `I(t₀)` such that an orientation for `(f, φ(t))`,
`t ∈ I(t₀) ∩ [0, 1]`, determines one for all `s ∈ I(t₀) ∩ [0, 1]`.  By the compactness of
`[0, 1]` and a finite covering a given orientation `o₀` of `DET(f, φ(0))` is transported to an
orientation `o₁` of `DET(f, φ(1))`; this is `φ_*`.  By a covering argument `φ_*` only depends on
the homotopy class `[φ]` with fixed end points, and `Γ_f` is clearly unique.

## What is formalized

* `LocalTransport PX O`: the local data, for a family of types `O x` over the smooth points:
  good open sets covering `X_∞` and push-forwards `O x₀ ≃ O x₁` along the sc-smooth paths in a
  good set, which compose (`push_trans`, the model of `HasLocalPropagation.eq_trans`) and do not
  depend on the good set (`push_compat`).  Consequences: `push_eq_refl` (loops), `push_eq_push`
  (in a good set the push-forward depends only on the end points), `push_congr`.
* The dyadic transport `transportN n γ`: the push-forward in a chosen good set for `n = 0`, the
  composite along `leftHalf γ` and `rightHalf γ` for `n + 1`; `transportN_eq_push` (on a path in
  a good set it is the push-forward at every level), `transportN_congr`, `IsFine N γ` (the
  dyadic pieces of level `N` lie in good sets) and `transportN_eq_of_isFine` (from such an `N`
  on, the dyadic transport is constant); `IsLebesgueNumber`, `exists_isLebesgueNumber` (Lebesgue
  number lemma on `[0, 1]`) and `isFine_of_isLebesgueNumber`.
* `transport γ`: the dyadic transport at a level at which the dyadic pieces lie in good sets;
  `transport_eq_transportN_of_isFine`, `transport_eq_transportN`.
* **(∗)** `transport_eq_push`: on a path in a good set the transport is the push-forward.
* `transport_congr` (only the values on `[0, 1]` matter), `transport_const` (a path constant on
  `[0, 1]` gives the identity), `transport_halves`.
* **Homotopy invariance** `transport_eq_of_isScHomotopyRel`, by the square lemma
  `transportN_square` (for a rectangle of `[0, 1]²` with sides `< 2ⁿ δ`, `δ` a Lebesgue number of
  the homotopy, `exists_isSqLebesgueNumber`, the dyadic transports around its boundary commute;
  the segments `vSeg`, `hSeg`, `dSeg` and the pasting `equiv_paste_squares` of four commutative
  squares); `transport_reparam` (invariance under `γ ↦ γ ∘ θ`, `θ(0) = 0`, `θ(1) = 1`).
* **Functoriality** `transport_concatPath`: the transport along `concatPath γ₁ γ₂` is the
  composite.
* **Uniqueness** `transport_unique`: a homotopy invariant family with the concatenation rule
  which is the push-forward on paths in good sets is the transport.
* The tools: `mem_smoothSet_of_isScSmoothMap`, `contDiff_pt2_comp`,
  `IsScHomotopyRel.apply_zero_eq`, `IsScHomotopyRel.apply_one_eq`.

## Reading

The covering argument is done abstractly, for any local transport data; the instance given by
the orientable neighbourhoods of Theorem 6.35 and Definition 6.36 is not made here, and neither
is the passage to the homotopy classes of `P_X` (the transport is homotopy invariant, takes
`concatPath` to composites and constant paths to the identity).  Dyadic subdivisions of `[0, 1]`
are used in place of an arbitrary finite covering: the transport along `γ` is the composite of
the push-forwards along the `2ᴺ` dyadic pieces of `γ` for any `N` at which every piece lies in a
good set (such `N` exist by the Lebesgue number lemma), and the independence of the covering is
the stabilization `transportN_eq_of_isFine`.  "An orientation for `(f, φ(t))` determines one for
all `s ∈ I(t₀)`" is read as the push-forward in a good set.  "A covering argument" for the
homotopy is read as the dyadic subdivision of the square `[0, 1]²`, each sub-square in a good
set, where the push-forwards around a sub-square commute (`push_trans` through its diagonal).
"Γ_f is unique" is read as `transport_unique`, with (∗), homotopy invariance and the
concatenation rule as the hypotheses.  The fibres are assumed to be in bijection
(`LocalTransport.nonempty`, true for the two-element sets `Or_x^f`); this is used only for the
value of `transportN 0 γ` when `γ([0, 1])` lies in no good set, which `transport` never uses.
Paths are on `ℝ` and only `[0, 1]` matters (decision D2).
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

variable (PX) in
/-- **Local transport data** for a family of types `O x` over the smooth points `x ∈ X_∞` (in
Theorem 6.37, `O x = Or_x^f`, the orientations of `DET(f, x)`): a family of *good* open sets
covering `X_∞` (the orientable neighbourhoods), all fibres in bijection, and for every good set `U`
a push-forward `O x₀ ≃ O x₁` along every sc-smooth path `γ` with `γ([0, 1]) ⊆ U` from `x₀` to
`x₁`, such that push-forwards in one good set compose (`push_trans`) and do not depend on the good
set containing the path (`push_compat`). -/
structure LocalTransport (O : ∀ x : X, x ∈ PX.smoothSet → Type v) where
  /-- The good open sets. -/
  Good : Set X → Prop
  /-- Good sets are open. -/
  isOpen : ∀ {U}, Good U → IsOpen U
  /-- Good sets cover the smooth points. -/
  exists_good : ∀ x ∈ PX.smoothSet, ∃ U, Good U ∧ x ∈ U
  /-- Any two fibres are in bijection. -/
  nonempty : ∀ x₀ (hs₀ : x₀ ∈ PX.smoothSet) x₁ (hs₁ : x₁ ∈ PX.smoothSet),
    Nonempty (O x₀ hs₀ ≃ O x₁ hs₁)
  /-- The push-forward along an sc-smooth path in a good set. -/
  push : ∀ {U} (_ : Good U) (γ : (Fin 1 → ℝ) → X), (rnPolyfold 1).IsScSmoothMap PX γ →
    (∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U) → ∀ {x₀ x₁ : X}, γ (pt1 0) = x₀ → γ (pt1 1) = x₁ →
    ∀ (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet), O x₀ hs₀ ≃ O x₁ hs₁
  /-- Push-forwards in one good set compose: for `γ` from `x₀` to `x₂` and `γ₁` from `x₀` to `x₁`,
  `γ₂` from `x₁` to `x₂`, all in `U`, the push-forward along `γ` is the composite. -/
  push_trans : ∀ {U} (hU : Good U) {γ γ₁ γ₂ : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγ₁ : (rnPolyfold 1).IsScSmoothMap PX γ₁)
    (hγ₂ : (rnPolyfold 1).IsScSmoothMap PX γ₂) (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U)
    (hγ₁U : ∀ t ∈ Icc (0 : ℝ) 1, γ₁ (pt1 t) ∈ U) (hγ₂U : ∀ t ∈ Icc (0 : ℝ) 1, γ₂ (pt1 t) ∈ U)
    {x₀ x₁ x₂ : X} (h₀ : γ (pt1 0) = x₀) (h₂ : γ (pt1 1) = x₂) (h₁₀ : γ₁ (pt1 0) = x₀)
    (h₁₁ : γ₁ (pt1 1) = x₁) (h₂₀ : γ₂ (pt1 0) = x₁) (h₂₁ : γ₂ (pt1 1) = x₂)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) (hs₂ : x₂ ∈ PX.smoothSet),
    push hU γ hγ hγU h₀ h₂ hs₀ hs₂ =
      (push hU γ₁ hγ₁ hγ₁U h₁₀ h₁₁ hs₀ hs₁).trans (push hU γ₂ hγ₂ hγ₂U h₂₀ h₂₁ hs₁ hs₂)
  /-- The push-forward along a path does not depend on the good set containing it. -/
  push_compat : ∀ {U U'} (hU : Good U) (hU' : Good U') {γ : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U)
    (hγU' : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U') {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
    push hU γ hγ hγU h₀ h₁ hs₀ hs₁ = push hU' γ hγ hγU' h₀ h₁ hs₀ hs₁

namespace LocalTransport

variable {O : ∀ x : X, x ∈ PX.smoothSet → Type v} (L : LocalTransport PX O)

/-! ### Consequences of `push_trans` -/

/-- **The push-forward along a loop in a good set is the identity** (`push_trans` with
`γ = γ₁ = γ₂`). -/
theorem push_eq_refl {U : Set X} (hU : L.Good U) {γ : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U) {x : X}
    (h₀ : γ (pt1 0) = x) (h₁ : γ (pt1 1) = x) (hs : x ∈ PX.smoothSet) :
    L.push hU γ hγ hγU h₀ h₁ hs hs = Equiv.refl _ := by
  have h := L.push_trans hU hγ hγ hγ hγU hγU hγU h₀ h₁ h₀ h₁ h₀ h₁ hs hs hs
  ext a
  have ha := DFunLike.congr_fun h a
  rw [Equiv.trans_apply] at ha
  exact ((L.push hU γ hγ hγU h₀ h₁ hs hs).injective ha).symm

/-- **In a good set the push-forward depends only on the end points**: two sc-smooth paths in
`U` with the same end points have the same push-forward (`push_trans` with a constant path). -/
theorem push_eq_push {U : Set X} (hU : L.Good U) {γ γ' : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγ' : (rnPolyfold 1).IsScSmoothMap PX γ')
    (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U) (hγ'U : ∀ t ∈ Icc (0 : ℝ) 1, γ' (pt1 t) ∈ U)
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (h₀' : γ' (pt1 0) = x₀)
    (h₁' : γ' (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    L.push hU γ hγ hγU h₀ h₁ hs₀ hs₁ = L.push hU γ' hγ' hγ'U h₀' h₁' hs₀ hs₁ := by
  have hc : (rnPolyfold 1).IsScSmoothMap PX fun _ => γ' (pt1 1) :=
    isScSmoothMap_reparam hγ' (κ := fun _ => 1) contDiff_const
  have hcU : ∀ t ∈ Icc (0 : ℝ) 1, (fun _ => γ' (pt1 1)) (pt1 t) ∈ U := fun _ _ =>
    hγ'U 1 ⟨zero_le_one, le_rfl⟩
  rw [L.push_trans hU hγ hγ' hc hγU hγ'U hcU h₀ h₁ h₀' h₁' h₁' h₁' hs₀ hs₁ hs₁,
    L.push_eq_refl hU hc hcU h₁' h₁' hs₁, Equiv.trans_refl]

/-- Paths which agree on `[0, 1]` and lie in good sets `U`, `U'` have the same push-forward. -/
theorem push_congr {U U' : Set X} (hU : L.Good U) (hU' : L.Good U') {γ γ' : (Fin 1 → ℝ) → X}
    (e : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) = γ' (pt1 t)) (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγ' : (rnPolyfold 1).IsScSmoothMap PX γ') (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U)
    (hγ'U' : ∀ t ∈ Icc (0 : ℝ) 1, γ' (pt1 t) ∈ U') {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (h₀' : γ' (pt1 0) = x₀) (h₁' : γ' (pt1 1) = x₁)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    L.push hU γ hγ hγU h₀ h₁ hs₀ hs₁ = L.push hU' γ' hγ' hγ'U' h₀' h₁' hs₀ hs₁ := by
  have hγ'U : ∀ t ∈ Icc (0 : ℝ) 1, γ' (pt1 t) ∈ U := fun t ht => e t ht ▸ hγU t ht
  rw [L.push_eq_push hU hγ hγ' hγU hγ'U h₀ h₁ h₀' h₁', L.push_compat hU hU' hγ' hγ'U hγ'U']

/-! ### The dyadic transport -/

open scoped Classical in
/-- **The dyadic transport at level `n`** along an sc-smooth path `γ` from `x₀` to `x₁`: at level
`0` the push-forward in a chosen good set containing `γ([0, 1])` (an arbitrary bijection if there
is none), at level `n + 1` the composite of the transports at level `n` along the two halves
`leftHalf γ` and `rightHalf γ`. -/
def transportN (n : ℕ) (γ : (Fin 1 → ℝ) → X) (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) : O x₀ hs₀ ≃ O x₁ hs₁ :=
  match n with
  | 0 =>
    if h : ∃ U, L.Good U ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U then
      L.push h.choose_spec.1 γ hγ h.choose_spec.2 h₀ h₁ hs₀ hs₁
    else (L.nonempty x₀ hs₀ x₁ hs₁).some
  | n + 1 =>
    (transportN n (leftHalf γ) (isScSmoothMap_leftHalf hγ) (leftHalf_zero.trans h₀) leftHalf_one
      hs₀ (mem_smoothSet_of_isScSmoothMap hγ _)).trans
    (transportN n (rightHalf γ) (isScSmoothMap_rightHalf hγ) rightHalf_zero
      (rightHalf_one.trans h₁) (mem_smoothSet_of_isScSmoothMap hγ _) hs₁)

open scoped Classical in
/-- The transport at level `0`. -/
theorem transportN_zero {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) :
    L.transportN 0 γ hγ h₀ h₁ hs₀ hs₁ =
      if h : ∃ U, L.Good U ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U then
        L.push h.choose_spec.1 γ hγ h.choose_spec.2 h₀ h₁ hs₀ hs₁
      else (L.nonempty x₀ hs₀ x₁ hs₁).some :=
  rfl

/-- The transport at level `n + 1` is the composite of the transports at level `n` along the two
halves (with any name `xm` for the midpoint `γ(1/2)`). -/
theorem transportN_succ (n : ℕ) {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    {x₀ x₁ xm : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hm : γ (pt1 (1 / 2)) = xm)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) (hsm : xm ∈ PX.smoothSet) :
    L.transportN (n + 1) γ hγ h₀ h₁ hs₀ hs₁ =
      (L.transportN n (leftHalf γ) (isScSmoothMap_leftHalf hγ) (leftHalf_zero.trans h₀)
        (leftHalf_one.trans hm) hs₀ hsm).trans
      (L.transportN n (rightHalf γ) (isScSmoothMap_rightHalf hγ) (rightHalf_zero.trans hm)
        (rightHalf_one.trans h₁) hsm hs₁) := by
  subst hm
  rfl

/-- The transport depends on the path only (not on the proofs). -/
theorem transportN_congr_fun (n : ℕ) {γ γ' : (Fin 1 → ℝ) → X} (e : γ = γ')
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγ' : (rnPolyfold 1).IsScSmoothMap PX γ')
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (h₀' : γ' (pt1 0) = x₀)
    (h₁' : γ' (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    L.transportN n γ hγ h₀ h₁ hs₀ hs₁ = L.transportN n γ' hγ' h₀' h₁' hs₀ hs₁ := by
  subst e
  rfl

/-- **On a path in a good set** `U` the transport at every level is the push-forward in `U`. -/
theorem transportN_eq_push (n : ℕ) : ∀ {U : Set X} (hU : L.Good U) {γ : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U)
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet),
    L.transportN n γ hγ h₀ h₁ hs₀ hs₁ = L.push hU γ hγ hγU h₀ h₁ hs₀ hs₁ := by
  induction n with
  | zero =>
    intro U hU γ hγ hγU x₀ x₁ h₀ h₁ hs₀ hs₁
    have h : ∃ U, L.Good U ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U := ⟨U, hU, hγU⟩
    rw [transportN_zero, dif_pos h]
    exact L.push_compat _ _ _ _ _ _ _ _ _
  | succ n ih =>
    intro U hU γ hγ hγU x₀ x₁ h₀ h₁ hs₀ hs₁
    have hsm := mem_smoothSet_of_isScSmoothMap hγ (pt1 (1 / 2))
    rw [L.transportN_succ n hγ h₀ h₁ rfl hs₀ hs₁ hsm, ih hU _ (leftHalf_mem hγU),
      ih hU _ (rightHalf_mem hγU)]
    exact (L.push_trans hU hγ _ _ hγU (leftHalf_mem hγU) (rightHalf_mem hγU) _ _ _ _ _ _ _ _
      _).symm

/-- The transport at every level along a loop in a good set is the identity. -/
theorem transportN_eq_refl (n : ℕ) {U : Set X} (hU : L.Good U) {γ : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U) {x : X}
    (h₀ : γ (pt1 0) = x) (h₁ : γ (pt1 1) = x) (hs : x ∈ PX.smoothSet) :
    L.transportN n γ hγ h₀ h₁ hs hs = Equiv.refl _ := by
  rw [L.transportN_eq_push n hU hγ hγU, L.push_eq_refl]

/-- The transport at every level along a path constant on `[0, 1]` is the identity. -/
theorem transportN_const (n : ℕ) {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    {x : X} (hc : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) = x) (h₀ : γ (pt1 0) = x) (h₁ : γ (pt1 1) = x)
    (hs : x ∈ PX.smoothSet) : L.transportN n γ hγ h₀ h₁ hs hs = Equiv.refl _ := by
  obtain ⟨U, hU, hxU⟩ := L.exists_good x hs
  exact L.transportN_eq_refl n hU hγ (fun t ht => (hc t ht).symm ▸ hxU) h₀ h₁ hs

/-- The transport at level `n` depends only on the values of the path on `[0, 1]`. -/
theorem transportN_congr (n : ℕ) : ∀ {γ γ' : (Fin 1 → ℝ) → X}
    (_ : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) = γ' (pt1 t)) (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγ' : (rnPolyfold 1).IsScSmoothMap PX γ') {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (h₀' : γ' (pt1 0) = x₀) (h₁' : γ' (pt1 1) = x₁)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
    L.transportN n γ hγ h₀ h₁ hs₀ hs₁ = L.transportN n γ' hγ' h₀' h₁' hs₀ hs₁ := by
  induction n with
  | zero =>
    intro γ γ' e hγ hγ' x₀ x₁ h₀ h₁ h₀' h₁' hs₀ hs₁
    rw [transportN_zero, transportN_zero]
    by_cases h : ∃ U, L.Good U ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U
    · have h' : ∃ U, L.Good U ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ' (pt1 t) ∈ U :=
        let ⟨U, hU, hγU⟩ := h; ⟨U, hU, fun t ht => e t ht ▸ hγU t ht⟩
      rw [dif_pos h, dif_pos h']
      exact L.push_congr _ _ e _ _ _ _ _ _ _ _ _ _
    · have h' : ¬ ∃ U, L.Good U ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ' (pt1 t) ∈ U :=
        fun ⟨U, hU, hγU⟩ => h ⟨U, hU, fun t ht => (e t ht).symm ▸ hγU t ht⟩
      rw [dif_neg h, dif_neg h']
  | succ n ih =>
    intro γ γ' e hγ hγ' x₀ x₁ h₀ h₁ h₀' h₁' hs₀ hs₁
    have hm := e (1 / 2) ⟨by norm_num, by norm_num⟩
    have hsm := mem_smoothSet_of_isScSmoothMap hγ' (pt1 (1 / 2))
    rw [L.transportN_succ n hγ h₀ h₁ hm hs₀ hs₁ hsm,
      L.transportN_succ n hγ' h₀' h₁' rfl hs₀ hs₁ hsm]
    exact congrArg₂ Equiv.trans
      (ih (γ := leftHalf γ) (γ' := leftHalf γ')
        (fun t ht => e (t / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩) _ _ _ _ _ _ _ _)
      (ih (γ := rightHalf γ) (γ' := rightHalf γ')
        (fun t ht => e ((1 + t) / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩) _ _ _ _ _ _ _ _)

/-! ### Lebesgue numbers and the stabilization of the dyadic transport -/

/-- `δ` is a **Lebesgue number** for the path `γ`: every interval `[a, b] ⊆ [0, 1]` of length
`b − a < δ` is mapped by `γ` into a good set. -/
def IsLebesgueNumber (δ : ℝ) (γ : (Fin 1 → ℝ) → X) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → b - a < δ → ∃ U, L.Good U ∧ ∀ t ∈ Icc a b, γ (pt1 t) ∈ U

/-- For a Lebesgue number `δ > 1` the whole path lies in one good set. -/
theorem isLebesgueNumber_exists_good {δ : ℝ} {γ : (Fin 1 → ℝ) → X}
    (h : L.IsLebesgueNumber δ γ) (hδ : 1 < δ) :
    ∃ U, L.Good U ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U :=
  h 0 1 le_rfl zero_le_one le_rfl (by linarith)

/-- If `δ` is a Lebesgue number for `γ`, `2δ` is one for its first half. -/
theorem isLebesgueNumber_leftHalf {δ : ℝ} {γ : (Fin 1 → ℝ) → X} (h : L.IsLebesgueNumber δ γ) :
    L.IsLebesgueNumber (2 * δ) (leftHalf γ) := by
  intro a b ha hab hb hba
  obtain ⟨U, hU, hγU⟩ := h (a / 2) (b / 2) (by linarith) (by linarith) (by linarith) (by linarith)
  exact ⟨U, hU, fun t ht => hγU (t / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩

/-- If `δ` is a Lebesgue number for `γ`, `2δ` is one for its second half. -/
theorem isLebesgueNumber_rightHalf {δ : ℝ} {γ : (Fin 1 → ℝ) → X} (h : L.IsLebesgueNumber δ γ) :
    L.IsLebesgueNumber (2 * δ) (rightHalf γ) := by
  intro a b ha hab hb hba
  obtain ⟨U, hU, hγU⟩ := h ((1 + a) / 2) ((1 + b) / 2) (by linarith) (by linarith) (by linarith)
    (by linarith)
  exact ⟨U, hU, fun t ht => hγU ((1 + t) / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩

/-- Lebesgue numbers only depend on the values of the path on `[0, 1]`. -/
theorem isLebesgueNumber_congr {δ : ℝ} {γ γ' : (Fin 1 → ℝ) → X}
    (e : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) = γ' (pt1 t)) (h : L.IsLebesgueNumber δ γ) :
    L.IsLebesgueNumber δ γ' := by
  intro a b ha hab hb hba
  obtain ⟨U, hU, hγU⟩ := h a b ha hab hb hba
  exact ⟨U, hU, fun t ht => e t ⟨ha.trans ht.1, ht.2.trans hb⟩ ▸ hγU t ht⟩

/-- **Every sc-smooth path has a Lebesgue number** for the covering of `[0, 1]` by the preimages
of the good sets (compactness of `[0, 1]`). -/
theorem exists_isLebesgueNumber {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) :
    ∃ δ > 0, L.IsLebesgueNumber δ γ := by
  have hc : Continuous fun t : ℝ => γ (pt1 t) :=
    (continuousOn_univ.1 hγ.continuousOn).comp (continuous_pi fun _ => continuous_id)
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (c := fun U : {U : Set X // L.Good U} => (fun t : ℝ => γ (pt1 t)) ⁻¹' U.1) isCompact_Icc
    (fun U => (L.isOpen U.2).preimage hc) (fun t _ => by
      obtain ⟨U, hU, htU⟩ := L.exists_good _ (mem_smoothSet_of_isScSmoothMap hγ (pt1 t))
      exact mem_iUnion.2 ⟨⟨U, hU⟩, htU⟩)
  refine ⟨δ, hδ, fun a b ha hab hb hba => ?_⟩
  obtain ⟨⟨U, hU⟩, hsub⟩ := hball a ⟨ha, hab.trans hb⟩
  refine ⟨U, hU, fun t ht => @hsub t ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-- **The dyadic pieces of level `N` lie in good sets**: for `N = 0` the path lies in a good set,
for `N + 1` its two halves have this property at level `N` (so the `2ᴺ` pieces
`s ↦ γ((k + s)/2ᴺ)`, `k < 2ᴺ`, lie in good sets). -/
def IsFine : ℕ → ((Fin 1 → ℝ) → X) → Prop
  | 0, γ => ∃ U, L.Good U ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U
  | N + 1, γ => IsFine N (leftHalf γ) ∧ IsFine N (rightHalf γ)

/-- **The dyadic transport stabilizes**: if the dyadic pieces of level `N` lie in good sets, the
transports at all levels `n ≥ N` agree. -/
theorem transportN_eq_of_isFine (N : ℕ) : ∀ {γ : (Fin 1 → ℝ) → X} (_ : L.IsFine N γ) (n : ℕ)
    (_ : N ≤ n) (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
    L.transportN n γ hγ h₀ h₁ hs₀ hs₁ = L.transportN N γ hγ h₀ h₁ hs₀ hs₁ := by
  induction N with
  | zero =>
    intro γ hF n _ hγ x₀ x₁ h₀ h₁ hs₀ hs₁
    obtain ⟨U, hU, hγU⟩ := hF
    rw [L.transportN_eq_push n hU hγ hγU, L.transportN_eq_push 0 hU hγ hγU]
  | succ N ih =>
    intro γ hF n hn hγ x₀ x₁ h₀ h₁ hs₀ hs₁
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hsm := mem_smoothSet_of_isScSmoothMap hγ (pt1 (1 / 2))
    rw [L.transportN_succ m hγ h₀ h₁ rfl hs₀ hs₁ hsm, L.transportN_succ N hγ h₀ h₁ rfl hs₀ hs₁ hsm,
      ih hF.1 m (by omega), ih hF.2 m (by omega)]

/-- If `δ` is a Lebesgue number for `γ` and `2ᴺ δ > 1`, the dyadic pieces of level `N` lie in good
sets. -/
theorem isFine_of_isLebesgueNumber (N : ℕ) : ∀ {δ : ℝ} {γ : (Fin 1 → ℝ) → X},
    L.IsLebesgueNumber δ γ → 1 < 2 ^ N * δ → L.IsFine N γ := by
  induction N with
  | zero =>
    intro δ γ hδ hN
    rw [pow_zero, one_mul] at hN
    exact L.isLebesgueNumber_exists_good hδ hN
  | succ N ih =>
    intro δ γ hδ hN
    have hN' : 1 < 2 ^ N * (2 * δ) := by rw [pow_succ, mul_assoc] at hN; exact hN
    exact ⟨ih (L.isLebesgueNumber_leftHalf hδ) hN', ih (L.isLebesgueNumber_rightHalf hδ) hN'⟩

/-- The dyadic transport stabilizes from every level `N` with `2ᴺ δ > 1`, `δ` a Lebesgue number. -/
theorem transportN_eq_of_isLebesgueNumber (N : ℕ) {δ : ℝ} {γ : (Fin 1 → ℝ) → X}
    (hδ : L.IsLebesgueNumber δ γ) (hN : 1 < 2 ^ N * δ) (n : ℕ) (hn : N ≤ n)
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    L.transportN n γ hγ h₀ h₁ hs₀ hs₁ = L.transportN N γ hγ h₀ h₁ hs₀ hs₁ :=
  L.transportN_eq_of_isFine N (L.isFine_of_isLebesgueNumber N hδ hN) n hn hγ h₀ h₁ hs₀ hs₁

/-- Every sc-smooth path has a level `N` and a Lebesgue number `δ` with `2ᴺ δ > 1`. -/
theorem exists_level {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) :
    ∃ N : ℕ, ∃ δ : ℝ, L.IsLebesgueNumber δ γ ∧ 1 < 2 ^ N * δ := by
  obtain ⟨δ, hδ, h⟩ := L.exists_isLebesgueNumber hγ
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (1 / δ) (one_lt_two : (1 : ℝ) < 2)
  exact ⟨N, δ, h, (div_lt_iff₀ hδ).1 hN⟩

/-! ### The transport -/

/-- **The transport along an sc-smooth path** `γ` from `x₀` to `x₁` (the map `φ_*` of the proof
of Theorem 6.37): the dyadic transport at a level at which every dyadic piece of `γ` lies in a good
set. -/
def transport (γ : (Fin 1 → ℝ) → X) (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) {x₀ x₁ : X}
    (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) : O x₀ hs₀ ≃ O x₁ hs₁ :=
  L.transportN (L.exists_level hγ).choose γ hγ h₀ h₁ hs₀ hs₁

/-- The transport is the dyadic transport at every level `N` whose dyadic pieces lie in good
sets. -/
theorem transport_eq_transportN_of_isFine {N : ℕ} {γ : (Fin 1 → ℝ) → X} (hF : L.IsFine N γ)
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    L.transport γ hγ h₀ h₁ hs₀ hs₁ = L.transportN N γ hγ h₀ h₁ hs₀ hs₁ := by
  obtain ⟨δ₀, hδ₀, hN₀⟩ := (L.exists_level hγ).choose_spec
  change L.transportN (L.exists_level hγ).choose γ hγ h₀ h₁ hs₀ hs₁ = _
  rw [← L.transportN_eq_of_isLebesgueNumber _ hδ₀ hN₀ (max N (L.exists_level hγ).choose)
      (le_max_right _ _),
    L.transportN_eq_of_isFine N hF _ (le_max_left _ _)]

/-- The transport is the dyadic transport at every level `N` with `2ᴺ δ > 1` for a Lebesgue
number `δ`. -/
theorem transport_eq_transportN {δ : ℝ} {γ : (Fin 1 → ℝ) → X} (hδ : L.IsLebesgueNumber δ γ)
    {N : ℕ} (hN : 1 < 2 ^ N * δ) (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) {x₀ x₁ : X}
    (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) :
    L.transport γ hγ h₀ h₁ hs₀ hs₁ = L.transportN N γ hγ h₀ h₁ hs₀ hs₁ :=
  L.transport_eq_transportN_of_isFine (L.isFine_of_isLebesgueNumber N hδ hN) hγ h₀ h₁ hs₀ hs₁

/-- **Property (∗) of Theorem 6.37**: on a path in a good set `U` the transport is the
push-forward in `U`. -/
theorem transport_eq_push {U : Set X} (hU : L.Good U) {γ : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U)
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) :
    L.transport γ hγ h₀ h₁ hs₀ hs₁ = L.push hU γ hγ hγU h₀ h₁ hs₀ hs₁ :=
  L.transportN_eq_push _ hU hγ hγU h₀ h₁ hs₀ hs₁

/-- **The transport along a path constant on `[0, 1]` is the identity.** -/
theorem transport_const {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) {x : X}
    (hc : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) = x) (h₀ : γ (pt1 0) = x) (h₁ : γ (pt1 1) = x)
    (hs : x ∈ PX.smoothSet) : L.transport γ hγ h₀ h₁ hs hs = Equiv.refl _ :=
  L.transportN_const _ hγ hc h₀ h₁ hs

/-- **The transport depends only on the values of the path on `[0, 1]`.** -/
theorem transport_congr {γ γ' : (Fin 1 → ℝ) → X} (e : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) = γ' (pt1 t))
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγ' : (rnPolyfold 1).IsScSmoothMap PX γ')
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (h₀' : γ' (pt1 0) = x₀)
    (h₁' : γ' (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    L.transport γ hγ h₀ h₁ hs₀ hs₁ = L.transport γ' hγ' h₀' h₁' hs₀ hs₁ := by
  obtain ⟨N, δ, hδ, hN⟩ := L.exists_level hγ
  rw [L.transport_eq_transportN hδ hN, L.transport_eq_transportN (L.isLebesgueNumber_congr e hδ) hN]
  exact L.transportN_congr N e hγ hγ' h₀ h₁ h₀' h₁' hs₀ hs₁

/-- **The transport along a path is the composite of the transports along its two halves.** -/
theorem transport_halves {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    {x₀ x₁ xm : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hm : γ (pt1 (1 / 2)) = xm)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) (hsm : xm ∈ PX.smoothSet) :
    L.transport γ hγ h₀ h₁ hs₀ hs₁ =
      (L.transport (leftHalf γ) (isScSmoothMap_leftHalf hγ) (leftHalf_zero.trans h₀)
        (leftHalf_one.trans hm) hs₀ hsm).trans
      (L.transport (rightHalf γ) (isScSmoothMap_rightHalf hγ) (rightHalf_zero.trans hm)
        (rightHalf_one.trans h₁) hsm hs₁) := by
  obtain ⟨N, δ, hδ, hN⟩ := L.exists_level hγ
  have hN' : 1 < 2 ^ (N + 1) * δ := by
    have : 2 ^ (N + 1) * δ = 2 * (2 ^ N * δ) := by ring
    linarith
  have hN'' : 1 < 2 ^ N * (2 * δ) := by
    have : 2 ^ N * (2 * δ) = 2 * (2 ^ N * δ) := by ring
    linarith
  rw [L.transport_eq_transportN hδ hN', L.transportN_succ N hγ h₀ h₁ hm hs₀ hs₁ hsm,
    L.transport_eq_transportN (L.isLebesgueNumber_leftHalf hδ) hN'',
    L.transport_eq_transportN (L.isLebesgueNumber_rightHalf hδ) hN'']

end LocalTransport

/-! ### Segments in a square -/

/-- The vertical segment `s ↦ Φ(a, b + s (b' − b))` of a map `Φ : ℝ² → X`. -/
def vSeg (Φ : (Fin 2 → ℝ) → X) (a b b' : ℝ) : (Fin 1 → ℝ) → X :=
  fun s => Φ (pt2 a (b + s 0 * (b' - b)))

/-- The horizontal segment `s ↦ Φ(a + s (a' − a), b)` of a map `Φ : ℝ² → X`. -/
def hSeg (Φ : (Fin 2 → ℝ) → X) (a a' b : ℝ) : (Fin 1 → ℝ) → X :=
  fun s => Φ (pt2 (a + s 0 * (a' - a)) b)

/-- The diagonal segment `s ↦ Φ(a + s (a' − a), b + s (b' − b))` of a map `Φ : ℝ² → X`. -/
def dSeg (Φ : (Fin 2 → ℝ) → X) (a a' b b' : ℝ) : (Fin 1 → ℝ) → X :=
  fun s => Φ (pt2 (a + s 0 * (a' - a)) (b + s 0 * (b' - b)))

section Segments

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

variable {Φ : (Fin 2 → ℝ) → X} {a a' b b' : ℝ}

/-- The vertical segment starts at `Φ(a, b)`. -/
@[simp] theorem vSeg_zero : vSeg Φ a b b' (pt1 0) = Φ (pt2 a b) := by simp [vSeg]

/-- The vertical segment ends at `Φ(a, b')`. -/
@[simp] theorem vSeg_one : vSeg Φ a b b' (pt1 1) = Φ (pt2 a b') := by simp [vSeg]

/-- The horizontal segment starts at `Φ(a, b)`. -/
@[simp] theorem hSeg_zero : hSeg Φ a a' b (pt1 0) = Φ (pt2 a b) := by simp [hSeg]

/-- The horizontal segment ends at `Φ(a', b)`. -/
@[simp] theorem hSeg_one : hSeg Φ a a' b (pt1 1) = Φ (pt2 a' b) := by simp [hSeg]

/-- The diagonal segment starts at `Φ(a, b)`. -/
@[simp] theorem dSeg_zero : dSeg Φ a a' b b' (pt1 0) = Φ (pt2 a b) := by simp [dSeg]

/-- The diagonal segment ends at `Φ(a', b')`. -/
@[simp] theorem dSeg_one : dSeg Φ a a' b b' (pt1 1) = Φ (pt2 a' b') := by simp [dSeg]

/-- The midpoint of the vertical segment is `Φ(a, (b + b')/2)`. -/
theorem vSeg_half : vSeg Φ a b b' (pt1 (1 / 2)) = Φ (pt2 a ((b + b') / 2)) := by
  simp only [vSeg, pt1_apply]
  congr 2
  ring

/-- The midpoint of the horizontal segment is `Φ((a + a')/2, b)`. -/
theorem hSeg_half : hSeg Φ a a' b (pt1 (1 / 2)) = Φ (pt2 ((a + a') / 2) b) := by
  simp only [hSeg, pt1_apply]
  congr 2
  ring

/-- The first half of a vertical segment is the vertical segment to the midpoint. -/
theorem leftHalf_vSeg : leftHalf (vSeg Φ a b b') = vSeg Φ a b ((b + b') / 2) := by
  funext s
  simp only [leftHalf, vSeg, pt1_apply]
  congr 2
  ring

/-- The second half of a vertical segment is the vertical segment from the midpoint. -/
theorem rightHalf_vSeg : rightHalf (vSeg Φ a b b') = vSeg Φ a ((b + b') / 2) b' := by
  funext s
  simp only [rightHalf, vSeg, pt1_apply]
  congr 2
  ring

/-- The first half of a horizontal segment is the horizontal segment to the midpoint. -/
theorem leftHalf_hSeg : leftHalf (hSeg Φ a a' b) = hSeg Φ a ((a + a') / 2) b := by
  funext s
  simp only [leftHalf, hSeg, pt1_apply]
  congr 2
  ring

/-- The second half of a horizontal segment is the horizontal segment from the midpoint.
-/
theorem rightHalf_hSeg : rightHalf (hSeg Φ a a' b) = hSeg Φ ((a + a') / 2) a' b := by
  funext s
  simp only [rightHalf, hSeg, pt1_apply]
  congr 2
  ring

end Segments

/-- The vertical segments of an sc-smooth `Φ : ℝ² → X` are sc-smooth paths. -/
theorem isScSmoothMap_vSeg {Φ : (Fin 2 → ℝ) → X} (hΦ : (rnPolyfold 2).IsScSmoothMap PX Φ)
    (a b b' : ℝ) : (rnPolyfold 1).IsScSmoothMap PX (vSeg Φ a b b') :=
  hΦ.comp (isScSmoothMap_rn_rn_of_contDiff (contDiff_pt2_comp contDiff_const
    (contDiff_const.add ((contDiff_apply ℝ ℝ (0 : Fin 1)).mul contDiff_const))))

/-- The horizontal segments of an sc-smooth `Φ : ℝ² → X` are sc-smooth paths. -/
theorem isScSmoothMap_hSeg {Φ : (Fin 2 → ℝ) → X} (hΦ : (rnPolyfold 2).IsScSmoothMap PX Φ)
    (a a' b : ℝ) : (rnPolyfold 1).IsScSmoothMap PX (hSeg Φ a a' b) :=
  hΦ.comp (isScSmoothMap_rn_rn_of_contDiff (contDiff_pt2_comp
    (contDiff_const.add ((contDiff_apply ℝ ℝ (0 : Fin 1)).mul contDiff_const)) contDiff_const))

/-- The diagonal segments of an sc-smooth `Φ : ℝ² → X` are sc-smooth paths. -/
theorem isScSmoothMap_dSeg {Φ : (Fin 2 → ℝ) → X} (hΦ : (rnPolyfold 2).IsScSmoothMap PX Φ)
    (a a' b b' : ℝ) : (rnPolyfold 1).IsScSmoothMap PX (dSeg Φ a a' b b') :=
  hΦ.comp (isScSmoothMap_rn_rn_of_contDiff (contDiff_pt2_comp
    (contDiff_const.add ((contDiff_apply ℝ ℝ (0 : Fin 1)).mul contDiff_const))
    (contDiff_const.add ((contDiff_apply ℝ ℝ (0 : Fin 1)).mul contDiff_const))))

/-- **Pasting four commutative squares** of bijections (the subdivision of a square into four
quadrants): the interior edges `N₁, N₂, M₁, M₂` cancel. -/
theorem equiv_paste_squares {α β γ δ ε ζ η θ ι : Sort*} {A₁ : α ≃ β} {A₂ : β ≃ γ} {D₁ : γ ≃ δ}
    {D₂ : δ ≃ ε} {B₁ : α ≃ ζ} {B₂ : ζ ≃ η} {C₁ : η ≃ θ} {C₂ : θ ≃ ε} {N₁ : β ≃ ι} {N₂ : ι ≃ θ}
    {M₁ : ζ ≃ ι} {M₂ : ι ≃ δ} (h₀₀ : A₁.trans N₁ = B₁.trans M₁) (h₀₁ : A₂.trans D₁ = N₁.trans M₂)
    (h₁₀ : M₁.trans N₂ = B₂.trans C₁) (h₁₁ : M₂.trans D₂ = N₂.trans C₂) :
    (A₁.trans A₂).trans (D₁.trans D₂) = (B₁.trans B₂).trans (C₁.trans C₂) := by
  ext x
  have e₀₀ := DFunLike.congr_fun h₀₀ x
  have e₀₁ := DFunLike.congr_fun h₀₁ (A₁ x)
  have e₁₀ := DFunLike.congr_fun h₁₀ (B₁ x)
  have e₁₁ := DFunLike.congr_fun h₁₁ (M₁ (B₁ x))
  simp only [Equiv.trans_apply] at e₀₀ e₀₁ e₁₀ e₁₁ ⊢
  rw [e₀₁, e₀₀, e₁₁, e₁₀]

/-- The end points of the second path of a homotopy with end points fixed: `γ₁(0) = γ₀(0)`. -/
theorem IsScHomotopyRel.apply_zero_eq {γ₀ γ₁ : (Fin 1 → ℝ) → X} {Φ : (Fin 2 → ℝ) → X}
    (hΦ : IsScHomotopyRel PX γ₀ γ₁ Φ) : γ₁ (pt1 0) = γ₀ (pt1 0) :=
  (hΦ.one 0 ⟨le_rfl, zero_le_one⟩).symm.trans (hΦ.start 1 ⟨zero_le_one, le_rfl⟩)

/-- The end points of the second path of a homotopy with end points fixed: `γ₁(1) = γ₀(1)`. -/
theorem IsScHomotopyRel.apply_one_eq {γ₀ γ₁ : (Fin 1 → ℝ) → X} {Φ : (Fin 2 → ℝ) → X}
    (hΦ : IsScHomotopyRel PX γ₀ γ₁ Φ) : γ₁ (pt1 1) = γ₀ (pt1 1) :=
  (hΦ.one 1 ⟨zero_le_one, le_rfl⟩).symm.trans (hΦ.finish 1 ⟨zero_le_one, le_rfl⟩)

namespace LocalTransport

variable {O : ∀ x : X, x ∈ PX.smoothSet → Type v} (L : LocalTransport PX O)

/-! ### The square lemma -/

/-- `δ` is a **Lebesgue number** for the map `Φ : ℝ² → X`: every rectangle
`[a, a'] × [b, b'] ⊆ [0, 1]²` with sides `< δ` is mapped by `Φ` into a good set. -/
def IsSqLebesgueNumber (δ : ℝ) (Φ : (Fin 2 → ℝ) → X) : Prop :=
  ∀ a a' b b' : ℝ, 0 ≤ a → a ≤ a' → a' ≤ 1 → 0 ≤ b → b ≤ b' → b' ≤ 1 → a' - a < δ →
    b' - b < δ → ∃ U, L.Good U ∧ ∀ τ ∈ Icc a a', ∀ t ∈ Icc b b', Φ (pt2 τ t) ∈ U

/-- **Every sc-smooth map `ℝ² → X` has a Lebesgue number** for the covering of `[0, 1]²` by the
preimages of the good sets (compactness of `[0, 1]²`). -/
theorem exists_isSqLebesgueNumber {Φ : (Fin 2 → ℝ) → X}
    (hΦ : (rnPolyfold 2).IsScSmoothMap PX Φ) : ∃ δ > 0, L.IsSqLebesgueNumber δ Φ := by
  have hc : Continuous fun p : ℝ × ℝ => Φ (pt2 p.1 p.2) :=
    (continuousOn_univ.1 hΦ.continuousOn).comp continuous_pt2
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (c := fun U : {U : Set X // L.Good U} => (fun p : ℝ × ℝ => Φ (pt2 p.1 p.2)) ⁻¹' U.1)
    (isCompact_Icc.prod isCompact_Icc) (fun U => (L.isOpen U.2).preimage hc) (fun p _ => by
      obtain ⟨U, hU, hpU⟩ := L.exists_good _ (mem_smoothSet_of_isScSmoothMap hΦ (pt2 p.1 p.2))
      exact mem_iUnion.2 ⟨⟨U, hU⟩, hpU⟩)
  refine ⟨δ, hδ, fun a a' b b' ha haa' ha' hb hbb' hb' hδa hδb => ?_⟩
  obtain ⟨⟨U, hU⟩, hsub⟩ := hball (a, b) ⟨⟨ha, haa'.trans ha'⟩, ⟨hb, hbb'.trans hb'⟩⟩
  refine ⟨U, hU, fun τ hτ t ht => @hsub (τ, t) ?_⟩
  rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff, abs_lt, abs_lt]
  exact ⟨⟨by linarith [hτ.1], by linarith [hτ.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩

/-- The transport at level `n + 1` along a vertical segment, split at its midpoint. -/
theorem transportN_succ_vSeg {Φ : (Fin 2 → ℝ) → X} (hΦ : (rnPolyfold 2).IsScSmoothMap PX Φ)
    (n : ℕ) {a b b' : ℝ} {x₀ x₁ xm : X} (h₀ : Φ (pt2 a b) = x₀) (h₁ : Φ (pt2 a b') = x₁)
    (hm : Φ (pt2 a ((b + b') / 2)) = xm) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet)
    (hsm : xm ∈ PX.smoothSet) :
    L.transportN (n + 1) (vSeg Φ a b b') (isScSmoothMap_vSeg hΦ a b b') (vSeg_zero.trans h₀)
        (vSeg_one.trans h₁) hs₀ hs₁ =
      (L.transportN n (vSeg Φ a b ((b + b') / 2)) (isScSmoothMap_vSeg hΦ _ _ _)
        (vSeg_zero.trans h₀) (vSeg_one.trans hm) hs₀ hsm).trans
      (L.transportN n (vSeg Φ a ((b + b') / 2) b') (isScSmoothMap_vSeg hΦ _ _ _)
        (vSeg_zero.trans hm) (vSeg_one.trans h₁) hsm hs₁) := by
  rw [L.transportN_succ n _ _ _ (vSeg_half.trans hm) hs₀ hs₁ hsm]
  exact congrArg₂ Equiv.trans (L.transportN_congr_fun n leftHalf_vSeg _ _ _ _ _ _ _ _)
    (L.transportN_congr_fun n rightHalf_vSeg _ _ _ _ _ _ _ _)

/-- The transport at level `n + 1` along a horizontal segment, split at its midpoint. -/
theorem transportN_succ_hSeg {Φ : (Fin 2 → ℝ) → X} (hΦ : (rnPolyfold 2).IsScSmoothMap PX Φ)
    (n : ℕ) {a a' b : ℝ} {x₀ x₁ xm : X} (h₀ : Φ (pt2 a b) = x₀) (h₁ : Φ (pt2 a' b) = x₁)
    (hm : Φ (pt2 ((a + a') / 2) b) = xm) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet)
    (hsm : xm ∈ PX.smoothSet) :
    L.transportN (n + 1) (hSeg Φ a a' b) (isScSmoothMap_hSeg hΦ a a' b) (hSeg_zero.trans h₀)
        (hSeg_one.trans h₁) hs₀ hs₁ =
      (L.transportN n (hSeg Φ a ((a + a') / 2) b) (isScSmoothMap_hSeg hΦ _ _ _)
        (hSeg_zero.trans h₀) (hSeg_one.trans hm) hs₀ hsm).trans
      (L.transportN n (hSeg Φ ((a + a') / 2) a' b) (isScSmoothMap_hSeg hΦ _ _ _)
        (hSeg_zero.trans hm) (hSeg_one.trans h₁) hsm hs₁) := by
  rw [L.transportN_succ n _ _ _ (hSeg_half.trans hm) hs₀ hs₁ hsm]
  exact congrArg₂ Equiv.trans (L.transportN_congr_fun n leftHalf_hSeg _ _ _ _ _ _ _ _)
    (L.transportN_congr_fun n rightHalf_hSeg _ _ _ _ _ _ _ _)

/-- **The square lemma**: for a rectangle `[a, a'] × [b, b'] ⊆ [0, 1]²` with sides `< 2ⁿ δ`, `δ` a
Lebesgue number for `Φ`, the transports at level `n` around its boundary commute: left side then
top equals bottom then right side.  (Induction on `n`: the four quadrants, the interior edges
cancel; for `n = 0` the rectangle lies in one good set and both composites are the push-forward
along the diagonal.) -/
theorem transportN_square {Φ : (Fin 2 → ℝ) → X} (hΦ : (rnPolyfold 2).IsScSmoothMap PX Φ)
    {δ : ℝ} (hδ : L.IsSqLebesgueNumber δ Φ) (n : ℕ) :
    ∀ {a a' b b' : ℝ}, 0 ≤ a → a ≤ a' → a' ≤ 1 → 0 ≤ b → b ≤ b' → b' ≤ 1 → a' - a < 2 ^ n * δ →
      b' - b < 2 ^ n * δ → ∀ {x₀₀ x₀₁ x₁₀ x₁₁ : X} (h₀₀ : Φ (pt2 a b) = x₀₀)
      (h₀₁ : Φ (pt2 a b') = x₀₁) (h₁₀ : Φ (pt2 a' b) = x₁₀) (h₁₁ : Φ (pt2 a' b') = x₁₁)
      (hs₀₀ : x₀₀ ∈ PX.smoothSet) (hs₀₁ : x₀₁ ∈ PX.smoothSet) (hs₁₀ : x₁₀ ∈ PX.smoothSet)
      (hs₁₁ : x₁₁ ∈ PX.smoothSet),
      (L.transportN n (vSeg Φ a b b') (isScSmoothMap_vSeg hΦ a b b') (vSeg_zero.trans h₀₀)
          (vSeg_one.trans h₀₁) hs₀₀ hs₀₁).trans
        (L.transportN n (hSeg Φ a a' b') (isScSmoothMap_hSeg hΦ a a' b') (hSeg_zero.trans h₀₁)
          (hSeg_one.trans h₁₁) hs₀₁ hs₁₁) =
      (L.transportN n (hSeg Φ a a' b) (isScSmoothMap_hSeg hΦ a a' b) (hSeg_zero.trans h₀₀)
          (hSeg_one.trans h₁₀) hs₀₀ hs₁₀).trans
        (L.transportN n (vSeg Φ a' b b') (isScSmoothMap_vSeg hΦ a' b b') (vSeg_zero.trans h₁₀)
          (vSeg_one.trans h₁₁) hs₁₀ hs₁₁) := by
  induction n with
  | zero =>
    intro a a' b b' ha haa' ha' hb hbb' hb' hda hdb x₀₀ x₀₁ x₁₀ x₁₁ h₀₀ h₀₁ h₁₀ h₁₁ hs₀₀ hs₀₁
      hs₁₀ hs₁₁
    rw [pow_zero, one_mul] at hda hdb
    obtain ⟨U, hU, hΦU⟩ := hδ a a' b b' ha haa' ha' hb hbb' hb' hda hdb
    have hseg : ∀ s ∈ Icc (0 : ℝ) 1, ∀ {c c' : ℝ}, c ≤ c' → c + s * (c' - c) ∈ Icc c c' :=
      fun s hs c c' hcc' => ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
    have hvU : ∀ {τ}, τ ∈ Icc a a' → ∀ t ∈ Icc (0 : ℝ) 1, vSeg Φ τ b b' (pt1 t) ∈ U :=
      fun hτ t ht => hΦU _ hτ _ (hseg t ht hbb')
    have hhU : ∀ {t}, t ∈ Icc b b' → ∀ τ ∈ Icc (0 : ℝ) 1, hSeg Φ a a' t (pt1 τ) ∈ U :=
      fun ht τ hτ => hΦU _ (hseg τ hτ haa') _ ht
    have hdU : ∀ s ∈ Icc (0 : ℝ) 1, dSeg Φ a a' b b' (pt1 s) ∈ U :=
      fun s hs => hΦU _ (hseg s hs haa') _ (hseg s hs hbb')
    have hd := isScSmoothMap_dSeg hΦ a a' b b'
    rw [L.transportN_eq_push 0 hU _ (hvU (left_mem_Icc.2 haa')),
      L.transportN_eq_push 0 hU _ (hhU (right_mem_Icc.2 hbb')),
      L.transportN_eq_push 0 hU _ (hhU (left_mem_Icc.2 hbb')),
      L.transportN_eq_push 0 hU _ (hvU (right_mem_Icc.2 haa'))]
    exact (L.push_trans hU hd (isScSmoothMap_vSeg hΦ a b b') (isScSmoothMap_hSeg hΦ a a' b') hdU
      (hvU (left_mem_Icc.2 haa')) (hhU (right_mem_Icc.2 hbb')) (dSeg_zero.trans h₀₀)
      (dSeg_one.trans h₁₁) (vSeg_zero.trans h₀₀) (vSeg_one.trans h₀₁) (hSeg_zero.trans h₀₁)
      (hSeg_one.trans h₁₁) hs₀₀ hs₀₁ hs₁₁).symm.trans
      (L.push_trans hU hd (isScSmoothMap_hSeg hΦ a a' b) (isScSmoothMap_vSeg hΦ a' b b') hdU
      (hhU (left_mem_Icc.2 hbb')) (hvU (right_mem_Icc.2 haa')) (dSeg_zero.trans h₀₀)
      (dSeg_one.trans h₁₁) (hSeg_zero.trans h₀₀) (hSeg_one.trans h₁₀) (vSeg_zero.trans h₁₀)
      (vSeg_one.trans h₁₁) hs₀₀ hs₁₀ hs₁₁)
  | succ n ih =>
    intro a a' b b' ha haa' ha' hb hbb' hb' hda hdb x₀₀ x₀₁ x₁₀ x₁₁ h₀₀ h₀₁ h₁₀ h₁₁ hs₀₀ hs₀₁
      hs₁₀ hs₁₁
    have hs : ∀ τ t, Φ (pt2 τ t) ∈ PX.smoothSet := fun τ t => mem_smoothSet_of_isScSmoothMap hΦ _
    have hda₁ : (a + a') / 2 - a < 2 ^ n * δ := by rw [pow_succ] at hda; linarith
    have hda₂ : a' - (a + a') / 2 < 2 ^ n * δ := by rw [pow_succ] at hda; linarith
    have hdb₁ : (b + b') / 2 - b < 2 ^ n * δ := by rw [pow_succ] at hdb; linarith
    have hdb₂ : b' - (b + b') / 2 < 2 ^ n * δ := by rw [pow_succ] at hdb; linarith
    rw [L.transportN_succ_vSeg hΦ n h₀₀ h₀₁ rfl hs₀₀ hs₀₁ (hs _ _),
      L.transportN_succ_hSeg hΦ n h₀₁ h₁₁ rfl hs₀₁ hs₁₁ (hs _ _),
      L.transportN_succ_hSeg hΦ n h₀₀ h₁₀ rfl hs₀₀ hs₁₀ (hs _ _),
      L.transportN_succ_vSeg hΦ n h₁₀ h₁₁ rfl hs₁₀ hs₁₁ (hs _ _)]
    exact equiv_paste_squares
      (ih ha (by linarith) (by linarith) hb (by linarith) (by linarith) hda₁ hdb₁ h₀₀ rfl rfl rfl
        hs₀₀ (hs _ _) (hs _ _) (hs _ _))
      (ih ha (by linarith) (by linarith) (by linarith) (by linarith) hb' hda₁ hdb₂ rfl h₀₁ rfl rfl
        (hs _ _) hs₀₁ (hs _ _) (hs _ _))
      (ih (by linarith) (by linarith) ha' hb (by linarith) (by linarith) hda₂ hdb₁ rfl rfl h₁₀ rfl
        (hs _ _) (hs _ _) hs₁₀ (hs _ _))
      (ih (by linarith) (by linarith) ha' (by linarith) (by linarith) hb' hda₂ hdb₂ rfl rfl rfl h₁₁
        (hs _ _) (hs _ _) (hs _ _) hs₁₁)

/-! ### Homotopy invariance, functoriality and uniqueness -/

/-- **Homotopy invariance** (the covering argument of the proof of Theorem 6.37): the transports
along two sc-smooth paths which are sc-smoothly homotopic with end points fixed agree.  (A Lebesgue
number `δ` for the homotopy `Φ` on `[0, 1]²`, the square lemma at a level `n` with `2ⁿ δ > 1`, and
the two sides `τ ↦ Φ(τ, 0)`, `τ ↦ Φ(τ, 1)`, constant on `[0, 1]`, with trivial transport.) -/
theorem transport_eq_of_isScHomotopyRel {γ₀ γ₁ : (Fin 1 → ℝ) → X} {Φ : (Fin 2 → ℝ) → X}
    (hΦ : IsScHomotopyRel PX γ₀ γ₁ Φ) (hγ₀ : (rnPolyfold 1).IsScSmoothMap PX γ₀)
    (hγ₁ : (rnPolyfold 1).IsScSmoothMap PX γ₁) {x₀ x₁ : X} (h₀ : γ₀ (pt1 0) = x₀)
    (h₁ : γ₀ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    L.transport γ₀ hγ₀ h₀ h₁ hs₀ hs₁ =
      L.transport γ₁ hγ₁ (hΦ.apply_zero_eq.trans h₀) (hΦ.apply_one_eq.trans h₁) hs₀ hs₁ := by
  have hΦs := hΦ.isScSmoothMap
  obtain ⟨δ, hδ, hsq⟩ := L.exists_isSqLebesgueNumber hΦs
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / δ) (one_lt_two : (1 : ℝ) < 2)
  have hn' : 1 < 2 ^ n * δ := (div_lt_iff₀ hδ).1 hn
  have hn'' : (1 : ℝ) - 0 < 2 ^ n * δ := by rw [sub_zero]; exact hn'
  have I0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have I1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  have e₀₀ : Φ (pt2 0 0) = x₀ := (hΦ.zero 0 I0).trans h₀
  have e₀₁ : Φ (pt2 0 1) = x₁ := (hΦ.zero 1 I1).trans h₁
  have e₁₀ : Φ (pt2 1 0) = x₀ := (hΦ.start 1 I1).trans h₀
  have e₁₁ : Φ (pt2 1 1) = x₁ := (hΦ.finish 1 I1).trans h₁
  have hsq' := L.transportN_square hΦs hsq n le_rfl zero_le_one le_rfl le_rfl zero_le_one le_rfl
    hn'' hn'' e₀₀ e₀₁ e₁₀ e₁₁ hs₀ hs₁ hs₀ hs₁
  -- the sides `t = 0, 1` of the square are constant on `[0, 1]`
  have hc₀ : ∀ τ ∈ Icc (0 : ℝ) 1, hSeg Φ 0 1 0 (pt1 τ) = x₀ := fun τ hτ => by
    simp only [hSeg, pt1_apply, zero_add, sub_zero, mul_one]
    exact (hΦ.start τ hτ).trans h₀
  have hc₁ : ∀ τ ∈ Icc (0 : ℝ) 1, hSeg Φ 0 1 1 (pt1 τ) = x₁ := fun τ hτ => by
    simp only [hSeg, pt1_apply, zero_add, sub_zero, mul_one]
    exact (hΦ.finish τ hτ).trans h₁
  rw [L.transportN_const n (isScSmoothMap_hSeg hΦs 0 1 0) hc₀ _ _ hs₀,
    L.transportN_const n (isScSmoothMap_hSeg hΦs 0 1 1) hc₁ _ _ hs₁, Equiv.trans_refl,
    Equiv.refl_trans] at hsq'
  -- the sides `τ = 0, 1` are `γ₀` and `γ₁` on `[0, 1]`
  have hv₀ : ∀ t ∈ Icc (0 : ℝ) 1, γ₀ (pt1 t) = vSeg Φ 0 0 1 (pt1 t) := fun t ht => by
    simp only [vSeg, pt1_apply, zero_add, sub_zero, mul_one]
    exact (hΦ.zero t ht).symm
  have hv₁ : ∀ t ∈ Icc (0 : ℝ) 1, γ₁ (pt1 t) = vSeg Φ 1 0 1 (pt1 t) := fun t ht => by
    simp only [vSeg, pt1_apply, zero_add, sub_zero, mul_one]
    exact (hΦ.one t ht).symm
  have hL : ∀ {τ : ℝ} {γ : (Fin 1 → ℝ) → X}, τ ∈ Icc (0 : ℝ) 1 →
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (pt2 τ t) = γ (pt1 t)) → L.IsLebesgueNumber δ γ := by
    intro τ γ hτ hγΦ a b ha hab hb hba
    obtain ⟨U, hU, hΦU⟩ := hsq τ τ a b hτ.1 le_rfl hτ.2 ha hab hb (by rw [sub_self]; exact hδ) hba
    exact ⟨U, hU, fun t ht => hγΦ t ⟨ha.trans ht.1, ht.2.trans hb⟩ ▸
      hΦU τ ⟨le_rfl, le_rfl⟩ t ht⟩
  rw [L.transport_eq_transportN (hL I0 hΦ.zero) hn', L.transport_eq_transportN (hL I1 hΦ.one) hn',
    L.transportN_congr n hv₀ hγ₀ (isScSmoothMap_vSeg hΦs 0 0 1) h₀ h₁ (vSeg_zero.trans e₀₀)
      (vSeg_one.trans e₀₁),
    L.transportN_congr n hv₁ hγ₁ (isScSmoothMap_vSeg hΦs 1 0 1) _ _ (vSeg_zero.trans e₁₀)
      (vSeg_one.trans e₁₁)]
  exact hsq'

/-- **Invariance under reparametrization**: for a `C^∞` map `θ : ℝ → ℝ` with `θ(0) = 0` and
`θ(1) = 1`, the transport along `γ ∘ θ` is the transport along `γ`. -/
theorem transport_reparam {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (h0 : θ 0 = 0) (h1 : θ 1 = 1) {x₀ x₁ : X}
    (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) :
    L.transport (fun s => γ (pt1 (θ (s 0)))) (isScSmoothMap_reparam hγ hθ)
        ((congrArg (fun t => γ (pt1 t)) h0).trans h₀) ((congrArg (fun t => γ (pt1 t)) h1).trans h₁)
        hs₀ hs₁ =
      L.transport γ hγ h₀ h₁ hs₀ hs₁ :=
  L.transport_eq_of_isScHomotopyRel (isScHomotopyRel_reparam hγ hθ h0 h1) _ hγ _ _ hs₀ hs₁

/-- **Functoriality**: the transport along the concatenation `concatPath γ₁ γ₂` is the composite of
the transports along `γ₁` and `γ₂` (its two halves are reparametrizations of `γ₁` and `γ₂`). -/
theorem transport_concatPath {γ₁ γ₂ : (Fin 1 → ℝ) → X} (hγ₁ : (rnPolyfold 1).IsScSmoothMap PX γ₁)
    (hγ₂ : (rnPolyfold 1).IsScSmoothMap PX γ₂) {x₀ x₁ x₂ : X} (h₁₀ : γ₁ (pt1 0) = x₀)
    (h₁₁ : γ₁ (pt1 1) = x₁) (h₂₀ : γ₂ (pt1 0) = x₁) (h₂₁ : γ₂ (pt1 1) = x₂)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) (hs₂ : x₂ ∈ PX.smoothSet) :
    L.transport (concatPath γ₁ γ₂) (isScSmoothMap_concatPath hγ₁ hγ₂ (h₁₁.trans h₂₀.symm))
        (concatPath_zero.trans h₁₀) (concatPath_one.trans h₂₁) hs₀ hs₂ =
      (L.transport γ₁ hγ₁ h₁₀ h₁₁ hs₀ hs₁).trans (L.transport γ₂ hγ₂ h₂₀ h₂₁ hs₁ hs₂) := by
  have hm : concatPath γ₁ γ₂ (pt1 (1 / 2)) = x₁ := by
    rw [concatPath_of_le (s := pt1 (1 / 2)) le_rfl, pt1_apply,
      Real.smoothTransition.one_of_one_le (by norm_num), h₁₁]
  have hθ₁ : ContDiff ℝ ∞ fun t : ℝ => Real.smoothTransition (3 * t / 2) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).div_const 2)
  have hθ₂ : ContDiff ℝ ∞ fun t : ℝ => Real.smoothTransition ((3 * t - 1) / 2) :=
    Real.smoothTransition.contDiff.comp
      (((contDiff_const.mul contDiff_id).sub contDiff_const).div_const 2)
  have hθ₁0 : Real.smoothTransition (3 * 0 / 2) = 0 := by
    rw [mul_zero, zero_div, Real.smoothTransition.zero]
  have hθ₁1 : Real.smoothTransition (3 * 1 / 2) = 1 :=
    Real.smoothTransition.one_of_one_le (by norm_num)
  have hθ₂0 : Real.smoothTransition ((3 * 0 - 1) / 2) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by norm_num)
  have hθ₂1 : Real.smoothTransition ((3 * 1 - 1) / 2) = 1 :=
    Real.smoothTransition.one_of_one_le (by norm_num)
  rw [L.transport_halves _ _ _ hm hs₀ hs₂ hs₁]
  exact congrArg₂ Equiv.trans
    ((L.transport_congr (γ' := fun s => γ₁ (pt1 (Real.smoothTransition (3 * s 0 / 2))))
      (fun t ht => concatPath_half₁ (γ₁ := γ₁) (γ₂ := γ₂) t ht) _
      (isScSmoothMap_reparam hγ₁ hθ₁) _ _ ((congrArg (fun t => γ₁ (pt1 t)) hθ₁0).trans h₁₀)
      ((congrArg (fun t => γ₁ (pt1 t)) hθ₁1).trans h₁₁) hs₀ hs₁).trans
      (L.transport_reparam hγ₁ hθ₁ hθ₁0 hθ₁1 h₁₀ h₁₁ hs₀ hs₁))
    ((L.transport_congr (γ' := fun s => γ₂ (pt1 (Real.smoothTransition ((3 * s 0 - 1) / 2))))
      (fun t ht => concatPath_half₂ (γ₁ := γ₁) (γ₂ := γ₂) (h₁₁.trans h₂₀.symm) t ht) _
      (isScSmoothMap_reparam hγ₂ hθ₂) _ _ ((congrArg (fun t => γ₂ (pt1 t)) hθ₂0).trans h₂₀)
      ((congrArg (fun t => γ₂ (pt1 t)) hθ₂1).trans h₂₁) hs₁ hs₂).trans
      (L.transport_reparam hγ₂ hθ₂ hθ₂0 hθ₂1 h₂₀ h₂₁ hs₁ hs₂))

/-- **Uniqueness** ("it is obvious that `Γ_f` is unique"): a family of bijections `G γ` along the
sc-smooth paths which is invariant under sc-smooth homotopies with end points fixed, takes
concatenations to composites, and is the push-forward on paths in good sets, is the transport.
(`G γ = G(γ ∘ θ) = G(left half) ∘ G(right half)`, and induction on the dyadic level.) -/
theorem transport_unique
    (G : ∀ (γ : (Fin 1 → ℝ) → X), (rnPolyfold 1).IsScSmoothMap PX γ → ∀ {x₀ x₁ : X},
      γ (pt1 0) = x₀ → γ (pt1 1) = x₁ → ∀ (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
      O x₀ hs₀ ≃ O x₁ hs₁)
    (hG_hom : ∀ {γ₀ γ₁ : (Fin 1 → ℝ) → X} {Φ : (Fin 2 → ℝ) → X}
      (hΦ : IsScHomotopyRel PX γ₀ γ₁ Φ) (hγ₀ : (rnPolyfold 1).IsScSmoothMap PX γ₀)
      (hγ₁ : (rnPolyfold 1).IsScSmoothMap PX γ₁) {x₀ x₁ : X} (h₀ : γ₀ (pt1 0) = x₀)
      (h₁ : γ₀ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
      G γ₀ hγ₀ h₀ h₁ hs₀ hs₁ =
        G γ₁ hγ₁ (hΦ.apply_zero_eq.trans h₀) (hΦ.apply_one_eq.trans h₁) hs₀ hs₁)
    (hG_concat : ∀ {γ₁ γ₂ : (Fin 1 → ℝ) → X} (hγ₁ : (rnPolyfold 1).IsScSmoothMap PX γ₁)
      (hγ₂ : (rnPolyfold 1).IsScSmoothMap PX γ₂) {x₀ x₁ x₂ : X} (h₁₀ : γ₁ (pt1 0) = x₀)
      (h₁₁ : γ₁ (pt1 1) = x₁) (h₂₀ : γ₂ (pt1 0) = x₁) (h₂₁ : γ₂ (pt1 1) = x₂)
      (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) (hs₂ : x₂ ∈ PX.smoothSet),
      G (concatPath γ₁ γ₂) (isScSmoothMap_concatPath hγ₁ hγ₂ (h₁₁.trans h₂₀.symm))
          (concatPath_zero.trans h₁₀) (concatPath_one.trans h₂₁) hs₀ hs₂ =
        (G γ₁ hγ₁ h₁₀ h₁₁ hs₀ hs₁).trans (G γ₂ hγ₂ h₂₀ h₂₁ hs₁ hs₂))
    (hG_push : ∀ {U : Set X} (hU : L.Good U) {γ : (Fin 1 → ℝ) → X}
      (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U)
      {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
      (hs₁ : x₁ ∈ PX.smoothSet), G γ hγ h₀ h₁ hs₀ hs₁ = L.push hU γ hγ hγU h₀ h₁ hs₀ hs₁)
    {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) {x₀ x₁ : X}
    (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) :
    G γ hγ h₀ h₁ hs₀ hs₁ = L.transport γ hγ h₀ h₁ hs₀ hs₁ := by
  have hcongr : ∀ {γ γ' : (Fin 1 → ℝ) → X} (_ : γ = γ') (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
      (hγ' : (rnPolyfold 1).IsScSmoothMap PX γ') {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
      (h₁ : γ (pt1 1) = x₁) (h₀' : γ' (pt1 0) = x₀) (h₁' : γ' (pt1 1) = x₁)
      (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
      G γ hγ h₀ h₁ hs₀ hs₁ = G γ' hγ' h₀' h₁' hs₀ hs₁ := by
    intro γ γ' e
    subst e
    intros
    rfl
  -- `G` splits along the two halves
  have hsplit : ∀ {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) {x₀ x₁ : X}
      (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
      (hs₁ : x₁ ∈ PX.smoothSet),
      G γ hγ h₀ h₁ hs₀ hs₁ =
        (G (leftHalf γ) (isScSmoothMap_leftHalf hγ) (leftHalf_zero.trans h₀) leftHalf_one hs₀
          (mem_smoothSet_of_isScSmoothMap hγ _)).trans
        (G (rightHalf γ) (isScSmoothMap_rightHalf hγ) rightHalf_zero (rightHalf_one.trans h₁)
          (mem_smoothSet_of_isScSmoothMap hγ _) hs₁) := by
    intro γ hγ x₀ x₁ h₀ h₁ hs₀ hs₁
    have hr := hG_hom (isScHomotopyRel_reparam hγ contDiff_halvesReparam halvesReparam_zero
      halvesReparam_one) (isScSmoothMap_reparam hγ contDiff_halvesReparam) hγ
      ((congrArg (fun t => γ (pt1 t)) halvesReparam_zero).trans h₀)
      ((congrArg (fun t => γ (pt1 t)) halvesReparam_one).trans h₁) hs₀ hs₁
    exact hr.symm.trans ((hcongr concatPath_halves.symm _ (isScSmoothMap_concatPath
      (isScSmoothMap_leftHalf hγ) (isScSmoothMap_rightHalf hγ)
      (leftHalf_one.trans rightHalf_zero.symm)) _ _ (concatPath_zero.trans
      (leftHalf_zero.trans h₀)) (concatPath_one.trans (rightHalf_one.trans h₁)) hs₀ hs₁).trans
      (hG_concat (isScSmoothMap_leftHalf hγ) (isScSmoothMap_rightHalf hγ)
        (leftHalf_zero.trans h₀) leftHalf_one rightHalf_zero (rightHalf_one.trans h₁) hs₀
        (mem_smoothSet_of_isScSmoothMap hγ _) hs₁))
  -- induction on the dyadic level
  have key : ∀ (N : ℕ) {δ : ℝ} {γ : (Fin 1 → ℝ) → X} (_ : L.IsLebesgueNumber δ γ)
      (_ : 1 < 2 ^ N * δ) (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) {x₀ x₁ : X}
      (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
      (hs₁ : x₁ ∈ PX.smoothSet), G γ hγ h₀ h₁ hs₀ hs₁ = L.transportN N γ hγ h₀ h₁ hs₀ hs₁ := by
    intro N
    induction N with
    | zero =>
      intro δ γ hδ hN hγ x₀ x₁ h₀ h₁ hs₀ hs₁
      rw [pow_zero, one_mul] at hN
      obtain ⟨U, hU, hγU⟩ := L.isLebesgueNumber_exists_good hδ hN
      rw [hG_push hU hγ hγU, L.transportN_eq_push 0 hU hγ hγU]
    | succ N ih =>
      intro δ γ hδ hN hγ x₀ x₁ h₀ h₁ hs₀ hs₁
      have hN' : 1 < 2 ^ N * (2 * δ) := by rw [pow_succ, mul_assoc] at hN; exact hN
      rw [hsplit hγ h₀ h₁ hs₀ hs₁, L.transportN_succ N hγ h₀ h₁ rfl hs₀ hs₁
        (mem_smoothSet_of_isScSmoothMap hγ _), ih (L.isLebesgueNumber_leftHalf hδ) hN',
        ih (L.isLebesgueNumber_rightHalf hδ) hN']
  obtain ⟨N, δ, hδ, hN⟩ := L.exists_level hγ
  rw [key N hδ hN, L.transport_eq_transportN hδ hN]

end LocalTransport

end Polyfold
