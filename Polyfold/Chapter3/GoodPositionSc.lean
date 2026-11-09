import Polyfold.Chapter3.GlobalIFTNearbyOnto
import Polyfold.Chapter3.GoodComplementProjection

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1 and §3.6:
**Definition 3.1.24 (preprint 3.21) with the text's sc-complement**, Definition 3.6.6 (preprint 3.53) with it, and **Theorem 3.6.8 (preprint 3.54) (1)
with the text's notion of good position in the conclusion** (follow-ups of the round-trip audit,
items V3.20, V3.82, V3.85, V4.38).

# Good position with an sc-complement

## The text, paraphrased

(Definition 3.1.24 (preprint 3.21)) Let `C ⊆ E` be a partial quadrant in the sc-Banach space `E` and `N ⊆ E` a
finite-dimensional sc-subspace.  `N` is in good position to `C` if the interior of `N ∩ C` in `N` is
nonempty and `N` has an sc-complement `P`, `E = N ⊕ P`, with an `ε > 0` such that for
`(n, p) ∈ N × P` with `|p|₀ ≤ ε|n|₀` the statements `n ∈ C` and `n + p ∈ C` are equivalent; such a
`P` is a good complement.  (After the definition) By Proposition 1.1.7 (preprint 1.6) such an `N` is smooth; for a
finite-dimensional `N` which is not smooth "a (merely) topological complement" is allowed.
(Definition 3.6.6 (preprint 3.53)) An sc-Fredholm germ `(f, x)` of a tame strong bundle with `f(x) = 0` is in good
position if `f'(x) : T_xX → Y_x` is surjective and, if `d_X(x) ≥ 1`, `ker f'(x)` is in good
position to the partial cone `C_xX` in `T_xX`.  (Theorem 3.6.8 (preprint 3.54) (1)) At every zero `y` near `x` the
germ `(f, y)` is in good position.

## What is formalized

* `Polyfold.IsScGoodComplement E C N P`: **the good complement of Definition 3.1.24 (preprint 3.21) as written**:
  `E = N ⊕ P` is an sc-splitting (`ScBanach.IsScSplitting`, Definition 1.1.6 (preprint 1.5)), with the constant
  `ε`.  `Polyfold.IsInGoodPositionSc E C N`: **Definition 3.1.24 (preprint 3.21) as written** (nonempty interior and
  a good sc-complement).  The forgetful lemmas `IsScGoodComplement.toIsGoodComplement`,
  `IsInGoodPositionSc.toIsInGoodPosition` to the project's notions (an algebraic complement,
  Finding 19), and `IsScGoodComplement.isClosed`, `IsInGoodPositionSc.le_smooth` (Proposition
  1.6).
* `Polyfold.IsScGoodComplementIn E T C N P`, `Polyfold.IsInGoodPositionScIn E T C N`: the same
  **inside a subspace `T ⊆ E₀`** (`P ⊆ T` an sc-subspace with `T_m = N_m ⊕ P_m` on every level),
  the form of Definition 3.6.6 (preprint 3.53) (2) in a chart, `T = T₀O`;
  `IsInGoodPositionScIn.toIsInGoodPositionIn`, `isInGoodPositionScIn_top_iff` (`T = E₀`) and
  `isInGoodPositionScIn_inter_iff` (the cone `T ∩ C`, the text's `C₀O = T₀O ∩ C`, gives the same
  notion).
* **The upgrade lemmas.** `IsGoodComplement.isScGoodComplementIn`: a closed good complement `Y` in
  `E` of a smooth finite-dimensional `N ⊆ T`, `T` an sc-subspace, gives the good sc-complement
  `Y ∩ T` of `N` inside `T`, with the same `ε`.  `IsInGoodPosition.isInGoodPositionScIn`: a smooth
  finite-dimensional `N ⊆ T` in good position to a partial quadrant `C` (algebraic complement) is in
  good position with an sc-complement inside `T`.  The case `T = E₀`:
  `IsGoodComplement.isScGoodComplement`, `IsInGoodPosition.isInGoodPositionSc`, and the
  dictionaries `isScGoodComplement_iff` (for smooth `N` the text's good complements are the
  project's closed ones) and `isInGoodPositionSc_iff` (Definition 3.1.24 (preprint 3.21) as written is the project's
  good position together with `N ⊆ E_∞`).
* `Polyfold.IsSc1.scDeriv_mem_smooth`: the derivative of an sc¹ map at a smooth point maps smooth
  vectors to smooth vectors (the tangent map is sc⁰).
* `Polyfold.IsGoodPositionAtSc`, `Polyfold.StrongBundle.IsGoodPositionGermScWholeChart`: **Definition 3.6.6 (preprint 3.53)
  with the sc-complement**, in the chart (`IsGoodPositionAt` with `IsInGoodPositionScIn` for the
  kernel) and for a section in a tame chart (`IsGoodPositionGermTameWholeChart` with `IsGoodPositionAtSc`);
  the forgetful `IsGoodPositionGermScWholeChart.isGoodPositionGermTame`.
* `Polyfold.StrongBundle.IsGoodPositionGermTameWholeChart.isGoodPositionGermSc`: **at a zero of an
  sc-Fredholm section with tame germ data, good position with an algebraic complement gives good
  position with an sc-complement**, in the same tame chart; `isGoodPositionGermSc_iff_wholeChart`.
* `Polyfold.theorem_3_6_8_one_sc_wholeChart`, `theorem_3_6_8_one_sc_of_tame_wholeChart`, `theorem_3_6_8_sc_wholeChart`,
  `theorem_3_1_26_sc_wholeChart`: **Theorem 3.6.8 (preprint 3.54) (1)** (and (2), and Theorem 3.1.26 (preprint 3.23)) **with the text's notion**:
  every zero near `x₀` is in good position with an sc-complement.  `theorem_3_6_11_sc_wholeChart`,
  `corollary_3_1_27_sc_wholeChart`, `theorem_3_6_10_sc_wholeChart`: the global theorems with the hypothesis "every zero is in
  good position" in the text's sense; `forall_isGoodPositionGermSc_iff_wholeChart`: for an sc-Fredholm section
  with tame germ data that hypothesis is the project's.

## What the text leaves implicit, and the choices made (the findings)

* **The sc-structure of the good complement is available as a conclusion** (Findings, Chapter 3,
  items 210–214; item 19 said that it never matters).  As a hypothesis it is still not needed (the
  proofs use the algebraic splitting only); as a conclusion — "every nearby zero is in good
  position", Theorem 3.6.8 (preprint 3.54) (1) — the project's theorems gave the weaker algebraic form, and this
  file supplies the text's.
* **How the sc-complement is found.**  A good complement of a smooth finite-dimensional `N` need
  not be closed (round-trip item V3.20: a non-closed algebraic good complement exists in any
  infinite-dimensional `E` with `C = E₀`), so it cannot be upgraded as it stands.  On a partial
  quadrant there is always a *closed* good complement `Y` (`exists_goodComplement_projectsInto`,
  Finding 83), and a closed complement of a smooth finite-dimensional `N` is an sc-complement:
  the projection `x ↦ x − lift_m(π x)` onto `Y` along `N` acts on every level (`N ⊆ E_∞`), so it
  maps the smooth points of `T_m` onto smooth points of `(Y ∩ T)_m`, which are therefore dense.
  The constant `ε` is unchanged.
* **The kernel at a zero is smooth**: `ker Dg(0) = Dψ'(0)(ker D(h + t)(0))` for the conjugation
  of the germ data (`theorem_3_6_8_nearby_kernel_wholeChart` applied at the zero itself), the kernel of the
  basic germ's linearization is smooth, and `Dψ'(0)` maps smooth vectors to smooth vectors
  (`IsSc1.scDeriv_mem_smooth`).  `T₀O` is an sc-subspace by Proposition 2.5.3 (preprint 2.35) (tame retraction).
  The good position of the kernel in `E` (needed to get a closed good complement) comes from the
  transport lemma `IsInGoodPositionIn.isInGoodPosition`.
* **"sc-complement inside `T`"** is written in `E`: `T` carries the sc-structure `T_m = T ∩ E_m`
  (`ScBanach.ofSubspace`), whose sc-subspaces are the sc-subspaces of `E` contained in `T`, with
  the same levels; so `T = N ⊕ P` is an sc-splitting of `T` iff `N`, `P ⊆ T` are sc-subspaces of
  `E` with `T_m = N_m ⊕ P_m` for all `m` (`IsScGoodComplementIn`).  The equivalence with
  `IsScSplitting` in `E.ofSubspace` is not formalized; for `T = E₀` it is
  `isScGoodComplementIn_top_iff`.
* **Condition (2) of Definition 3.6.6 (preprint 3.53) is stated unconditionally**, as in the project's
  `IsGoodPositionAt` (at an interior point it holds anyway); the upgrade proves it at every zero.
* **The remark after Definition 3.1.24 (preprint 3.21)** (a topological complement for a non-smooth `N`) is not
  formalized separately; on a partial quadrant a closed good complement always exists
  (`exists_goodComplement_projectsInto`).
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

/-! ### Definition 3.1.24 (preprint 3.21) with the sc-complement -/

section ScLevel

variable {E : ScBanach}

/-- **Definition 3.1.24 (preprint 3.21), the good complement, as written**: `P` is a **good sc-complement** of `N`
with respect to `C ⊆ E₀`: `E = N ⊕ P` is an sc-splitting (Definition 1.1.6 (preprint 1.5): `N` and `P` are
sc-subspaces and `E_m = N_m ⊕ P_m` on every level) and there is `ε > 0` such that for `n ∈ N`,
`p ∈ P` with `|p|₀ ≤ ε|n|₀` the statements `n ∈ C` and `n + p ∈ C` are equivalent.  (The project's
`IsGoodComplement` asks only for the algebraic splitting `E₀ = N ⊕ P`; Finding 19.) -/
structure IsScGoodComplement (E : ScBanach) (C : Set (E 0)) (N P : Submodule ℝ (E 0)) : Prop where
  isScSplitting : E.IsScSplitting N P
  exists_eps : ∃ ε > 0, ∀ x ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖x‖ → (x ∈ C ↔ x + p ∈ C)

/-- **Definition 3.1.24 (preprint 3.21) as written**: the finite-dimensional sc-subspace `N` is **in good position**
to `C`: the interior of `N ∩ C` in `N` is nonempty and `N` has a good sc-complement
(`IsScGoodComplement`).  (That `N` is an sc-subspace is part of the sc-splitting.) -/
structure IsInGoodPositionSc (E : ScBanach) (C : Set (E 0)) (N : Submodule ℝ (E 0)) : Prop where
  interior_nonempty : (interior (Subtype.val ⁻¹' C : Set N)).Nonempty
  exists_scGoodComplement : ∃ P, IsScGoodComplement E C N P

variable {C : Set (E 0)} {N P T : Submodule ℝ (E 0)}

/-- A good sc-complement is a good complement (Definition 3.1.24 (preprint 3.21) ⟹ the project's
`IsGoodComplement`; round-trip item V3.20). -/
theorem IsScGoodComplement.toIsGoodComplement (h : IsScGoodComplement E C N P) :
    IsGoodComplement E C N P := by
  refine ⟨?_, h.exists_eps⟩
  have := h.isScSplitting.2.2 0
  rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this

/-- A good sc-complement is closed (it is an sc-subspace). -/
theorem IsScGoodComplement.isClosed (h : IsScGoodComplement E C N P) :
    IsClosed (P : Set (E 0)) :=
  h.isScSplitting.2.1.1

/-- A finite-dimensional subspace with a good sc-complement is smooth (Proposition 1.1.7 (preprint 1.6); the
remark after Definition 3.1.24 (preprint 3.21)). -/
theorem IsScGoodComplement.le_smooth [FiniteDimensional ℝ N] (h : IsScGoodComplement E C N P) :
    N ≤ E.smooth :=
  (E.proposition_1_1_7_iff N).1 h.isScSplitting.1

/-- **Definition 3.1.24 (preprint 3.21) as written gives the project's good position** (`IsInGoodPosition`, whose
good complement is only algebraic; round-trip item V3.20). -/
theorem IsInGoodPositionSc.toIsInGoodPosition (h : IsInGoodPositionSc E C N) :
    IsInGoodPosition E C N := by
  obtain ⟨hint, P, hP⟩ := h
  exact ⟨hint, P, hP.toIsGoodComplement⟩

/-- A finite-dimensional subspace in good position in the sense of Definition 3.1.24 (preprint 3.21) is smooth
(Proposition 1.1.7 (preprint 1.6)). -/
theorem IsInGoodPositionSc.le_smooth [FiniteDimensional ℝ N] (h : IsInGoodPositionSc E C N) :
    N ≤ E.smooth := by
  obtain ⟨-, P, hP⟩ := h
  exact hP.le_smooth

/-! ### Inside a subspace `T` -/

/-- **Definition 3.1.24 (preprint 3.21) inside a subspace `T ⊆ E₀`, the good sc-complement**: `N` and `P` are
sc-subspaces of `E`, `P ⊆ T`, and `T_m = N_m ⊕ P_m` on every level (so `T = N ⊕ P` is an
sc-splitting of `T` with its sc-structure `T_m = T ∩ E_m`), with the constant `ε` of Definition
3.21.  For `T = E₀` this is `IsScGoodComplement` (`isScGoodComplementIn_top_iff`). -/
structure IsScGoodComplementIn (E : ScBanach) (T : Submodule ℝ (E 0)) (C : Set (E 0))
    (N P : Submodule ℝ (E 0)) : Prop where
  isScSubspace_left : E.IsScSubspace N
  isScSubspace_right : E.IsScSubspace P
  le : P ≤ T
  levelSub_inf : ∀ m, E.levelSub N m ⊓ E.levelSub P m = ⊥
  levelSub_sup : ∀ m, E.levelSub N m ⊔ E.levelSub P m = E.levelSub T m
  exists_eps : ∃ ε > 0, ∀ x ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖x‖ → (x ∈ C ↔ x + p ∈ C)

/-- **Definition 3.1.24 (preprint 3.21) inside a subspace `T ⊆ E₀`, as written**: `N ⊆ T`, the interior of `N ∩ C` in
`N` is nonempty, and `N` has a good sc-complement in `T` (`IsScGoodComplementIn`).  For `T = T₀O`
and `C` the partial quadrant this is the text's "`ker f'(x)` is in good position to the partial
cone `C₀O = T₀O ∩ C` in `T₀O`" (Definition 3.6.6 (preprint 3.53) (2); `isInGoodPositionScIn_inter_iff`). -/
structure IsInGoodPositionScIn (E : ScBanach) (T : Submodule ℝ (E 0)) (C : Set (E 0))
    (N : Submodule ℝ (E 0)) : Prop where
  le : N ≤ T
  interior_nonempty : (interior (Subtype.val ⁻¹' C : Set N)).Nonempty
  exists_scGoodComplement : ∃ P, IsScGoodComplementIn E T C N P

/-- Good position inside `T` with an sc-complement gives the project's good position inside `T`
(`IsInGoodPositionIn`, algebraic complement). -/
theorem IsInGoodPositionScIn.toIsInGoodPositionIn (h : IsInGoodPositionScIn E T C N) :
    IsInGoodPositionIn E T C N := by
  obtain ⟨hNT, hint, P, hP⟩ := h
  have h1 := hP.levelSub_inf 0
  have h2 := hP.levelSub_sup 0
  simp only [ScBanach.levelSub_zero] at h1 h2
  exact ⟨hNT, hint, P, hP.le, h1, h2, hP.exists_eps⟩

/-- Good position inside `T` with an sc-complement: `N` is smooth. -/
theorem IsInGoodPositionScIn.le_smooth [FiniteDimensional ℝ N] (h : IsInGoodPositionScIn E T C N) :
    N ≤ E.smooth := by
  obtain ⟨-, -, P, hP⟩ := h
  exact (E.proposition_1_1_7_iff N).1 hP.isScSubspace_left

/-- A good sc-complement inside `E₀` is a good sc-complement. -/
theorem isScGoodComplementIn_top_iff :
    IsScGoodComplementIn E ⊤ C N P ↔ IsScGoodComplement E C N P := by
  constructor
  · rintro ⟨hN, hP, -, h1, h2, hε⟩
    refine ⟨⟨hN, hP, fun m => IsCompl.of_eq (h1 m) ?_⟩, hε⟩
    rw [h2 m, E.levelSub_top]
  · rintro ⟨⟨hN, hP, hc⟩, hε⟩
    exact ⟨hN, hP, le_top, fun m => (hc m).inf_eq_bot,
      fun m => by rw [(hc m).sup_eq_top, E.levelSub_top], hε⟩

/-- Good position inside `E₀` with an sc-complement is Definition 3.1.24 (preprint 3.21) as written. -/
theorem isInGoodPositionScIn_top_iff :
    IsInGoodPositionScIn E ⊤ C N ↔ IsInGoodPositionSc E C N := by
  constructor
  · rintro ⟨-, hint, P, hP⟩
    exact ⟨hint, P, isScGoodComplementIn_top_iff.1 hP⟩
  · rintro ⟨hint, P, hP⟩
    exact ⟨le_top, hint, P, isScGoodComplementIn_top_iff.2 hP⟩

/-- **The cone `T ∩ C`** (the text's partial cone `C₀O = T₀O ∩ C`) gives the same notion as the
cone `C`, inside `T`. -/
theorem isInGoodPositionScIn_inter_iff :
    IsInGoodPositionScIn E T ((T : Set (E 0)) ∩ C) N ↔ IsInGoodPositionScIn E T C N := by
  have key : N ≤ T → ∀ P : Submodule ℝ (E 0), P ≤ T → ∀ x ∈ N, ∀ p ∈ P,
      ((x ∈ (T : Set (E 0)) ∩ C ↔ x + p ∈ (T : Set (E 0)) ∩ C) ↔ (x ∈ C ↔ x + p ∈ C)) := by
    intro hNT P hPT x hx p hp
    have hxT : x ∈ T := hNT hx
    have hxpT : x + p ∈ T := T.add_mem hxT (hPT hp)
    simp only [Set.mem_inter_iff, SetLike.mem_coe, hxT, hxpT, true_and]
  have hpre : N ≤ T →
      (Subtype.val ⁻¹' ((T : Set (E 0)) ∩ C) : Set N) = Subtype.val ⁻¹' C := by
    intro hNT
    ext ⟨n, hn⟩
    simp only [Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨fun h => h.2, fun h => ⟨hNT hn, h⟩⟩
  constructor
  · rintro ⟨hNT, hint, P, hN, hP, hPT, h1, h2, ε, hε, hgood⟩
    rw [hpre hNT] at hint
    exact ⟨hNT, hint, P, hN, hP, hPT, h1, h2, ε, hε, fun x hx p hp hle =>
      (key hNT P hPT x hx p hp).1 (hgood x hx p hp hle)⟩
  · rintro ⟨hNT, hint, P, hN, hP, hPT, h1, h2, ε, hε, hgood⟩
    rw [← hpre hNT] at hint
    exact ⟨hNT, hint, P, hN, hP, hPT, h1, h2, ε, hε, fun x hx p hp hle =>
      (key hNT P hPT x hx p hp).2 (hgood x hx p hp hle)⟩

/-! ### The upgrade: a closed good complement of a smooth `N` is a good sc-complement -/

/-- **The upgrade lemma** (round-trip items V3.82, V4.38).  Let `T` be an sc-subspace of `E`, and
`N ⊆ T` a smooth finite-dimensional subspace with a **closed** good complement `Y` in `E`.  Then
`Y ∩ T` is a good sc-complement of `N` inside `T`, with the same `ε`: `T_m = N_m ⊕ (Y ∩ T)_m` on
every level (lift `π x ∈ N` to `E_m`, `π` the projection onto `N` along `Y`), and the smooth
points of `(Y ∩ T)_m` are dense, since `x ↦ x − lift_m(π x)` maps the smooth points of `T_m`, dense
in `T_m`, to smooth points of `(Y ∩ T)_m` and fixes `(Y ∩ T)_m`. -/
theorem IsGoodComplement.isScGoodComplementIn [FiniteDimensional ℝ N] {Y : Submodule ℝ (E 0)}
    (hY : IsGoodComplement E C N Y) (hYc : IsClosed (Y : Set (E 0))) (hT : E.IsScSubspace T)
    (hNT : N ≤ T) (hNs : N ≤ E.smooth) : IsScGoodComplementIn E T C N (Y ⊓ T) := by
  have htop : Submodule.IsTopCompl N Y :=
    (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hY.isCompl.symm hYc).symm
  set π : E 0 →L[ℝ] N := N.projectionOntoL Y htop with hπdef
  have hπN : ∀ x : N, π x = x := fun x => Submodule.projectionOntoL_apply_left htop x
  have hπY : ∀ {z : E 0}, z ∈ Y ↔ π z = 0 := fun {z} =>
    (Submodule.projectionOntoL_apply_eq_zero_iff htop).symm
  have hlift : ∀ m, ∀ n : N, ∃ y : E m, E.toBase m y = n := fun m n =>
    ⟨finSmoothLift hNs m n, toBase_finSmoothLift hNs m n⟩
  refine ⟨(E.proposition_1_1_7_iff N).2 hNs, ⟨hYc.inter hT.1, ?_⟩, inf_le_right, fun m => ?_,
    fun m => ?_, ?_⟩
  · -- the smooth points of `(Y ∩ T)_m` are dense in `(Y ∩ T)_m`
    intro m x hx
    let L : N →L[ℝ] E m := LinearMap.toContinuousLinearMap (finSmoothLift hNs m)
    have hL : ∀ n : N, E.toBase m (L n) = n := toBase_finSmoothLift hNs m
    let Φ : E m → E m := fun z => z - L (π (E.toBase m z))
    have hΦc : Continuous Φ :=
      continuous_id.sub (L.continuous.comp (π.continuous.comp (E.toBase m).continuous))
    have hΦx : Φ x = x := by
      have : π (E.toBase m x) = 0 := hπY.1 hx.1
      simp only [Φ, this, map_zero, sub_zero]
    have hΦS : Φ '' (E.levelSub T m ∩ E.smoothLvl m) ⊆
        E.levelSub (Y ⊓ T) m ∩ E.smoothLvl m := by
      rintro _ ⟨t, ⟨htT, hts⟩, rfl⟩
      have hb : E.toBase m (Φ t) = E.toBase m t - (π (E.toBase m t) : E 0) := by
        simp only [Φ, map_sub, hL]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · change E.toBase m (Φ t) ∈ Y
        rw [hb, hπY, map_sub, hπN, sub_self]
      · change E.toBase m (Φ t) ∈ T
        rw [hb]; exact T.sub_mem htT (hNT (π _).2)
      · change E.toBase m (Φ t) ∈ E.smooth
        rw [hb]; exact E.smooth.sub_mem hts (hNs (π _).2)
    have hxT : x ∈ (E.levelSub T m : Set (E m)) := hx.2
    have h1 := hT.2 m hxT
    rw [← hΦx]
    exact closure_mono hΦS (image_closure_subset_closure_image hΦc (mem_image_of_mem Φ h1))
  · -- `N_m ∩ (Y ∩ T)_m = 0`
    rw [eq_bot_iff]
    rintro x ⟨hxN, hxP⟩
    have h1 : E.toBase m x ∈ N ⊓ Y := ⟨hxN, hxP.1⟩
    rw [hY.isCompl.inf_eq_bot, Submodule.mem_bot] at h1
    exact (Submodule.mem_bot ℝ).2 (E.toBase_injective m (by rw [h1, map_zero]))
  · -- `N_m + (Y ∩ T)_m = T_m`
    apply le_antisymm
    · exact sup_le (fun x hx => hNT hx) (fun x hx => hx.2)
    · intro x hx
      obtain ⟨y, hy⟩ := hlift m (π (E.toBase m x))
      have hyN : y ∈ E.levelSub N m := show E.toBase m y ∈ N by rw [hy]; exact (π _).2
      have hxy : x - y ∈ E.levelSub (Y ⊓ T) m := by
        refine ⟨?_, ?_⟩
        · change E.toBase m (x - y) ∈ Y
          rw [hπY, map_sub, map_sub, hy, hπN, sub_self]
        · change E.toBase m (x - y) ∈ T
          rw [map_sub]; exact T.sub_mem hx (hNT hyN)
      have := Submodule.add_mem_sup hyN hxy
      rwa [add_sub_cancel] at this
  · -- the constant `ε` of `Y`
    obtain ⟨ε, hε, hgood⟩ := hY.exists_eps
    exact ⟨ε, hε, fun x hx p hp hle => hgood x hx p hp.1 hle⟩

/-- **The upgrade lemma, `T = E₀`** (round-trip item V3.20): a closed good complement of a smooth
finite-dimensional subspace is a good sc-complement. -/
theorem IsGoodComplement.isScGoodComplement [FiniteDimensional ℝ N] (hP : IsGoodComplement E C N P)
    (hPc : IsClosed (P : Set (E 0))) (hNs : N ≤ E.smooth) : IsScGoodComplement E C N P := by
  have h := hP.isScGoodComplementIn hPc E.isScSubspace_top le_top hNs
  rw [inf_top_eq] at h
  exact isScGoodComplementIn_top_iff.1 h

/-- **The text's good complement is the project's closed good complement** (round-trip item
V3.20, "the text's good complement = the project's + closed"), for a smooth finite-dimensional
`N`. -/
theorem isScGoodComplement_iff [FiniteDimensional ℝ N] (hNs : N ≤ E.smooth) :
    IsScGoodComplement E C N P ↔ IsGoodComplement E C N P ∧ IsClosed (P : Set (E 0)) :=
  ⟨fun h => ⟨h.toIsGoodComplement, h.isClosed⟩, fun ⟨h, hP⟩ => h.isScGoodComplement hP hNs⟩

/-- **The upgrade lemma for good position** (round-trip items V3.82, V4.38): a smooth
finite-dimensional subspace `N` of the sc-subspace `T`, in good position to the partial quadrant
`C` in `E` (`IsInGoodPosition`, algebraic complement), is in good position with an sc-complement
inside `T` (`IsInGoodPositionScIn`): the sc-complement is `Y ∩ T` for a closed good complement `Y`
(`exists_goodComplement_projectsInto`, Finding 83). -/
theorem IsInGoodPosition.isInGoodPositionScIn [FiniteDimensional ℝ N] (hC : IsPartialQuadrant E C)
    (hgp : IsInGoodPosition E C N) (hT : E.IsScSubspace T) (hNT : N ≤ T) (hNs : N ≤ E.smooth) :
    IsInGoodPositionScIn E T C N := by
  obtain ⟨Y, hY, hYc, -⟩ := exists_goodComplement_projectsInto hC hgp
  exact ⟨hNT, hgp.interior_nonempty, Y ⊓ T, hY.isScGoodComplementIn hYc hT hNT hNs⟩

/-- **The upgrade lemma for good position, `T = E₀`**: a smooth finite-dimensional subspace in good
position to a partial quadrant (`IsInGoodPosition`) is in good position in the sense of Definition
3.21 as written. -/
theorem IsInGoodPosition.isInGoodPositionSc [FiniteDimensional ℝ N] (hC : IsPartialQuadrant E C)
    (hgp : IsInGoodPosition E C N) (hNs : N ≤ E.smooth) : IsInGoodPositionSc E C N :=
  isInGoodPositionScIn_top_iff.1 (hgp.isInGoodPositionScIn hC E.isScSubspace_top le_top hNs)

/-- **Definition 3.1.24 (preprint 3.21) as written is the project's good position of a smooth subspace** (round-trip
item V3.20): on a partial quadrant, `N` is in good position with an sc-complement iff it is in good
position with an algebraic complement and `N ⊆ E_∞`. -/
theorem isInGoodPositionSc_iff [FiniteDimensional ℝ N] (hC : IsPartialQuadrant E C) :
    IsInGoodPositionSc E C N ↔ IsInGoodPosition E C N ∧ N ≤ E.smooth :=
  ⟨fun h => ⟨h.toIsInGoodPosition, h.le_smooth⟩, fun ⟨h, hNs⟩ => h.isInGoodPositionSc hC hNs⟩

end ScLevel

/-! ### The derivative of an sc¹ map preserves smooth vectors -/

/-- **The derivative at a smooth point maps smooth vectors to smooth vectors** (round-trip item
V3.82, `scDeriv_zero_mem_smooth`): for `f` sc¹ on `U`, `x ∈ U₁` with `x ∈ E_∞` and `h ∈ E_∞`,
`Df(x)h ∈ F_∞`, because the tangent map `Tf` is sc⁰ (Definition 1.1.15 (preprint 1.14) (3)) and `(x, h)` lies on
every level of `TU`. -/
theorem IsSc1.scDeriv_mem_smooth {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0}
    (hf : IsSc1 U f) {x : E 1} (hxU : E.toBase 1 x ∈ U) (hxs : E.toBase 1 x ∈ E.smooth)
    {h : E 0} (hh : h ∈ E.smooth) : scDeriv U f x h ∈ F.smooth := by
  rw [ScScale.mem_smooth_iff] at hh hxs ⊢
  intro m
  obtain ⟨hm, hhm⟩ := hh m
  obtain ⟨xm, hxm⟩ := hxs (m + 1)
  have hxm' : E.shift.toBase m xm = x := by
    apply E.toBase_injective 1
    rw [← E.shift_toBase m xm, hxm]
  have hp : ((xm, hm) : E.tangent m) ∈ E.tangent.lvlSet (E.tangentSet U) m := by
    rw [ScBanach.mem_lvlSet_tangentSet, ScBanach.mem_lvlSet, hxm]; exact hxU
  obtain ⟨q, hq⟩ := hf.tangentMap_isSc0.mem_range m _ hp
  refine ⟨q.2, ?_⟩
  have h2 := congrArg Prod.snd hq
  rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase] at h2
  refine h2.trans ?_
  change scDeriv U f (E.shift.toBase m xm) (E.toBase m hm) = _
  rw [hxm', hhm]

/-! ### Definition 3.6.6 (preprint 3.53) with the sc-complement -/

section Def353Sc

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- **Definition 3.6.6 (preprint 3.53) in the chart, with the text's sc-complement**: for the filled version `g` of
the principal part at the zero `0`, (1) `Tf̃(0) = Dg(0)|_{T₀O} : T₀O → K₀` is onto, and (2)
`ker Dg(0)` is in good position to the partial cone `C₀O = T₀O ∩ C` inside `T₀O = Dr(0)E` with an
sc-complement (`IsInGoodPositionScIn`, Definition 3.1.24 (preprint 3.21) as written).  As in `IsGoodPositionAt`,
(2) is stated without the case distinction `d_X(x) ≥ 1`. -/
structure IsGoodPositionAtSc (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (g : E 0 → F 0) : Prop where
  surj : ∀ y ∈ rangeS (ρCLM hR h0), ∃ x ∈ rangeS (scDeriv U (r R) 0), scDeriv U g 0 x = y
  kernel : IsInGoodPositionScIn E (rangeS (scDeriv U (r R) 0)) C
    (LinearMap.ker (scDeriv U g 0 : E 0 →ₗ[ℝ] F 0))

/-- Good position in the chart with an sc-complement is good position in the chart
(`IsGoodPositionAt`, algebraic complement). -/
theorem IsGoodPositionAtSc.isGoodPositionAt {hU : IsRelOpenInQuadrant E C U}
    {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U} {g : E 0 → F 0}
    (h : IsGoodPositionAtSc hU hR h0 g) : IsGoodPositionAt hU hR h0 g :=
  ⟨h.surj, h.kernel.toIsInGoodPositionIn⟩

end Def353Sc

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

namespace StrongBundle

variable (B) in
/-- **Definition 3.6.6 (preprint 3.53) with the text's sc-complement, in a tame chart**: `(f, x₀)` is an sc-Fredholm germ
in good position in the sense of the text: the data of `IsGoodPositionGermTameWholeChart` (a tame
strong bundle chart centred at `x₀`, a filled version `g` of `f̂`, a local sc⁺-section `s` with
`s(0) = g(0)`, `g − s` conjugated to a basic germ) with `Tf̃(0)` onto `K₀` and `ker Dg(0)` in good
position to `C₀O` inside `T₀O` with an **sc-complement** (`IsGoodPositionAtSc`). This is the
project's original whole-chart reading, stricter than the text (Findings, Chapter 3, items 220–221,
260–266); the text's germ reading is `IsGoodPositionGermSc` (`GoodPositionScG.lean`, phase 2, items
270–330). -/
def IsGoodPositionGermScWholeChart (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScSmooth (F := c.F.shift) c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)) ∧
    IsGoodPositionAtSc c.relOpen c.isRetraction h0 g

/-- Good position with an sc-complement is good position (`IsGoodPositionGermTameWholeChart`, algebraic
complement), in the same tame chart. -/
theorem IsGoodPositionGermScWholeChart.isGoodPositionGermTame {x : X} (h : B.IsGoodPositionGermScWholeChart f x) :
    B.IsGoodPositionGermTameWholeChart f x := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, hgp⟩ := h
  exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, hgp.isGoodPositionAt⟩

set_option maxHeartbeats 1600000 in
-- the destructuring of `theorem_3_6_8_nearby_kernel_wholeChart` is large
/-- **At a zero, good position (algebraic complement) gives good position with the text's
sc-complement** (round-trip items V3.82, V3.85, `isGoodPositionGermSc_of_tame`).  Let `f` be an
sc-Fredholm section with tame germ data and `(f, y)`, `f(y) = 0`, in good position in a tame chart
(`IsGoodPositionGermTameWholeChart`).  In the tame chart centred at `y` of `theorem_3_6_8_nearby_kernel_wholeChart`
(applied at `y` itself): `ker Dg(0) = Dψ'(0)(ker D(h + t)(0))` is finite-dimensional and smooth
(the kernel of the basic germ's linearization is smooth and `Dψ'(0)` preserves smooth vectors,
`IsSc1.scDeriv_mem_smooth`); `T₀O = Dr(0)E` is an sc-subspace and `(1 − Dr(0))E ⊆ E₀`
(Proposition 2.5.3 (preprint 2.35), tame retraction); so `ker Dg(0)` is in good position to `C` in `E` (the
transport lemma `IsInGoodPositionIn.isInGoodPosition`), and `IsInGoodPosition.isInGoodPositionScIn`
gives the sc-complement inside `T₀O`. -/
theorem IsGoodPositionGermTameWholeChart.isGoodPositionGermSc (hf : B.IsScFredholmSectionTameWholeChart f) {y : X}
    (hg : B.IsGoodPositionGermTameWholeChart f y) (hy : IsZeroAt P f y) : B.IsGoodPositionGermScWholeChart f y := by
  classical
  obtain ⟨c, hc, hyV, h0, h0U, g, t₀, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', Ψ, Ψ',
    hΨ, hψ0, 𝒮, h', Bc, hh'𝒮, hsurj, hpos, Yc, V', σ, Vx, n', Wq, T, Vx₂, hfill, ht₀, ht₀0, hconj,
    hgp, hYc, hYcc, hKsm, hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol, hlift, hVxo, hyVx, hVxsub,
    hinj, hzero, himage, hT, hVx₂o, hyVx₂, hVx₂Vx, hker⟩ :=
    theorem_3_6_8_nearby_kernel_wholeChart hf.isScSmooth.1 hg hy
  obtain ⟨-, -, v, hv, z₀₁, x₁, hz₀₁, -, hx₁, -, -, hψφ, hfred, -, -, -, -, hkerEq, -, -, -⟩ :=
    hker y hyVx₂ hy
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := by
    rw [c.r_image, ← h0]; exact c.φ.mapsTo_model y hyV
  -- the level-`1` points are `0`
  have hz0 : z₀₁ = 0 := c.φ.model.E.toBase_injective 1 (by rw [hz₀₁, h0, map_zero])
  have hx0 : x₁ = 0 := by
    apply (ScBanach.paramProd Pn W).toBase_injective 1
    rw [hx₁, ← hψφ, h0, hψ0, map_zero]
  subst hz0 hx0
  -- the kernel `N = ker Dg(0)`: finite-dimensional and smooth
  have hfinK := hfred.finite_ker
  have hNfin : FiniteDimensional ℝ
      (LinearMap.ker (scDeriv c.U g 0 : c.φ.model.E 0 →ₗ[ℝ] c.F 0)) := by
    rw [hkerEq]; infer_instance
  have h0U' : (0 : (ScBanach.paramProd Pn W) 0) ∈ U' := by
    have := (hΨ.toFun.mapsTo (show ((0 : c.φ.model.E 0), (0 : c.F 0)) ∈ c.U ×ˢ univ from
      ⟨h0U, mem_univ _⟩)).1
    rwa [show (Ψ (0, 0)).1 = IsStrongBundleMap.base Ψ 0 from rfl, hψ0] at this
  have hψ'1 : IsSc1 U' (IsStrongBundleMap.base Ψ') := (hΨ.invFun.base_isScSmooth hU').isSc1
  have hNs : LinearMap.ker (scDeriv c.U g 0 : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ≤
      c.φ.model.E.smooth := by
    rw [hkerEq]
    rintro _ ⟨w, hw, rfl⟩
    refine hψ'1.scDeriv_mem_smooth (by rw [map_zero]; exact h0U') ?_ (hKsm hw)
    rw [map_zero]; exact (ScBanach.paramProd Pn W).smooth.zero_mem
  -- `T₀O` is an sc-subspace and `(1 − Dr(0))E ⊆ E₀` (Proposition 2.5.3 (preprint 2.35))
  have hRtT := hc.2 n' Wq T hT
  have h01 : (0 : c.φ.model.E 1) ∈
      c.φ.model.E.lvlSet (c.isRetraction.baseRetraction c.relOpen).retract 1 := by
    rw [ScBanach.mem_lvlSet, map_zero, c.base_retract]; exact c.r_image ▸ h0O
  have hs : (0 : c.φ.model.E 1) ∈ c.φ.model.E.smoothLvl 1 := by
    change c.φ.model.E.toBase 1 0 ∈ (c.φ.model.E.smooth : Set (c.φ.model.E 0))
    rw [map_zero]; exact c.φ.model.E.smooth.zero_mem
  obtain ⟨hK, hsplit⟩ := proposition_2_5_3 hT hRtT h01 hs
  rw [map_zero] at hK
  have hTsc : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) 0)) := hsplit.1
  -- good position in `E`, then the sc-complement inside `T₀O`
  have hgpE : IsInGoodPosition c.φ.model.E c.φ.model.C
      (LinearMap.ker (scDeriv c.U g 0 : c.φ.model.E 0 →ₗ[ℝ] c.F 0)) :=
    hgp.kernel.isInGoodPosition T hT (scDeriv c.U (r c.R) 0)
      (StrongRetr.scDeriv_r_idem c.relOpen c.isRetraction h0O) hK
  exact ⟨hf.mem_smoothSet_of_isZeroAt hy, c, hc, hyV, h0, h0U, g, t₀, hfill, ht₀, ht₀0, hconj,
    ⟨hgp.surj, hgpE.isInGoodPositionScIn c.φ.model.isPartialQuadrant hTsc hgp.kernel.le hNs⟩⟩

/-- **At a zero of an sc-Fredholm section with tame germ data, the two notions of good position
agree**: Definition 3.6.6 (preprint 3.53) with the text's sc-complement (`IsGoodPositionGermScWholeChart`) and with an
algebraic complement (`IsGoodPositionGermTameWholeChart`). -/
theorem isGoodPositionGermSc_iff_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) {y : X}
    (hy : IsZeroAt P f y) : B.IsGoodPositionGermScWholeChart f y ↔ B.IsGoodPositionGermTameWholeChart f y :=
  ⟨fun h => h.isGoodPositionGermTame, fun h => h.isGoodPositionGermSc hf hy⟩

end StrongBundle

/-! ### Theorem 3.6.8 (preprint 3.54) (1) with the text's notion of good position -/

/-- **Theorem 3.6.8 (preprint 3.54) (1) with the text's notion in the conclusion, from the weaker hypothesis**: for
an sc-Fredholm section `f` with tame germ data (`IsScFredholmSectionTameWholeChart`), `f(x₀) = 0` and
`(f, x₀)` in good position in a tame chart with an algebraic complement (`IsGoodPositionGermTameWholeChart`),
there is an open `Vx ∋ x₀` such that at every zero `y ∈ Vx` the germ `(f, y)` is in good position
with the text's sc-complement (`IsGoodPositionGermScWholeChart`).  (`theorem_3_6_8_one'_wholeChart` and
`IsGoodPositionGermTameWholeChart.isGoodPositionGermSc`; round-trip item V3.82.) -/
theorem theorem_3_6_8_one_sc_of_tame_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) {x₀ : X}
    (hg : B.IsGoodPositionGermTameWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ Vx : Set X, IsOpen Vx ∧ x₀ ∈ Vx ∧
      ∀ y ∈ Vx, IsZeroAt P f y → B.IsGoodPositionGermScWholeChart f y := by
  obtain ⟨Vx, hVxo, hx₀Vx, hall⟩ := theorem_3_6_8_one'_wholeChart hf hg hx₀
  exact ⟨Vx, hVxo, hx₀Vx, fun y hy hy0 => (hall y hy hy0).isGoodPositionGermSc hf hy0⟩

/-- **Theorem 3.6.8 (preprint 3.54) (1) with the text's notion of good position** (Definition 3.6.6 (preprint 3.53) with the
sc-complement of Definition 3.1.24 (preprint 3.21), `IsGoodPositionGermScWholeChart`, in hypothesis and conclusion): for an
sc-Fredholm section with tame germ data, `f(x₀) = 0` and `(f, x₀)` in good position, there is an
open `Vx ∋ x₀` such that at every zero `y ∈ Vx` the germ `(f, y)` is in good position (round-trip
item V3.82). -/
theorem theorem_3_6_8_one_sc_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) {x₀ : X}
    (hg : B.IsGoodPositionGermScWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ Vx : Set X, IsOpen Vx ∧ x₀ ∈ Vx ∧
      ∀ y ∈ Vx, IsZeroAt P f y → B.IsGoodPositionGermScWholeChart f y :=
  theorem_3_6_8_one_sc_of_tame_wholeChart hf hg.isGoodPositionGermTame hx₀

/-- **Theorem 3.6.8 (preprint 3.54) (1) and (2) with the text's notion of good position**: as `theorem_3_6_8'_wholeChart`, with
(1) in the form "every zero `y ∈ Vx` is in good position with an sc-complement"
(`IsGoodPositionGermScWholeChart`); (2) the solution set has regular data of Definition 3.2.1 (preprint 3.25) (2) at `x₀` on a
chart with source in `Vx`, of locally constant dimension (round-trip item V3.85). -/
theorem theorem_3_6_8_sc_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) {x₀ : X}
    (hg : B.IsGoodPositionGermScWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ Vx : Set X, IsOpen Vx ∧ x₀ ∈ Vx ∧ (∀ y ∈ Vx, IsZeroAt P f y → B.IsGoodPositionGermScWholeChart f y) ∧
      ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x₀ d, D.IsRegular ∧ D.φ.source ⊆ Vx ∧
        ∀ y ∈ solutionSet P f ∩ D.φ.source,
          ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d := by
  obtain ⟨Vx, hVxo, hx₀Vx, hall, hrest⟩ := theorem_3_6_8'_wholeChart hf hg.isGoodPositionGermTame hx₀
  exact ⟨Vx, hVxo, hx₀Vx, fun y hy hy0 => (hall y hy hy0).isGoodPositionGermSc hf hy0, hrest⟩

/-- **Theorem 3.1.26 (preprint 3.23) (implicit function theorem, boundary case) with the text's notion of good
position**: as `theorem_3_1_26'_wholeChart`, with the hypothesis at `x` and the conclusion "every zero in `U` is
in good position" in the sense of Definition 3.6.6 (preprint 3.53) with the sc-complement
(`IsGoodPositionGermScWholeChart`). -/
theorem theorem_3_1_26_sc_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) {x : X} (hx : IsZeroAt P f x)
    (hg : B.IsGoodPositionGermScWholeChart f x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ (∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermScWholeChart f y) ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ d : ℕ, ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d := by
  obtain ⟨U, hUo, hxU, hall, hrest⟩ := theorem_3_1_26'_wholeChart hf hx hg.isGoodPositionGermTame
  exact ⟨U, hUo, hxU, fun y hy hy0 => (hall y hy hy0).isGoodPositionGermSc hf hy0, hrest⟩

/-! ### The global theorems with the text's notion of good position -/

/-- **"Every zero is in good position" in the text's sense is the project's hypothesis**, for an
sc-Fredholm section with tame germ data (`StrongBundle.isGoodPositionGermSc_iff_wholeChart`). -/
theorem forall_isGoodPositionGermSc_iff_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) :
    (∀ x, IsZeroAt P f x → B.IsGoodPositionGermScWholeChart f x) ↔
      ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTameWholeChart f x :=
  ⟨fun h x hx => (h x hx).isGoodPositionGermTame, fun h x hx => (h x hx).isGoodPositionGermSc hf hx⟩

/-- **Theorem 3.6.11 (preprint 3.57) with the text's notion of good position** (`theorem_3_6_11_wholeChart` with the hypothesis
`IsGoodPositionGermScWholeChart` at every zero): the solution set is a sub-M-polyfold whose induced
structure is tame and that of a manifold with boundary with corners of locally constant
dimension. -/
theorem theorem_3_6_11_sc_wholeChart (hf : B.IsScFredholmSectionWholeChart f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermScWholeChart f x) (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        ∀ x ∈ solutionSet P f, ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x d,
          D.IsRegular ∧ ∀ y ∈ solutionSet P f ∩ D.φ.source,
            ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d :=
  theorem_3_6_11_wholeChart hf (fun x hx => (hall x hx).isGoodPositionGermTame) hne

/-- **Corollary 3.1.27 (preprint 3.24) with the text's notion of good position** (`corollary_3_1_27_wholeChart` with the
hypothesis `IsGoodPositionGermScWholeChart` at every zero). -/
theorem corollary_3_1_27_sc_wholeChart (hf : B.IsScFredholmSectionWholeChart f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermScWholeChart f x) (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc :=
  corollary_3_1_27_wholeChart hf (fun x hx => (hall x hx).isGoodPositionGermTame) hne

/-- **Theorem 3.6.10 (preprint 3.56) with the text's notion of good position** (`theorem_3_6_10_wholeChart` with the hypothesis
`IsGoodPositionGermScWholeChart` at every zero; `∂X = ∅`). -/
theorem theorem_3_6_10_sc_wholeChart (hX : PX.IsWithoutBoundary) (hf : B.IsScFredholmSectionWholeChart f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermScWholeChart f x) (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        (MPolyfold.subPolyfold hsub).IsWithoutBoundary :=
  theorem_3_6_10_wholeChart hX hf (fun x hx => (hall x hx).isGoodPositionGermTame) hne

end Bundle

end Polyfold
