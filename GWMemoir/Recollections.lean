import Polyfold.Chapter2.TangentBundle
import Polyfold.Chapter2.Tame
import Polyfold.Chapter2.TameRetracts
import Polyfold.Chapter2.FibredProduct
import Polyfold.Chapter2.LevelsWeak
import Polyfold.Chapter7.Groupoid
import Polyfold.Chapter10.WeakFibredProduct

/-!
Hofer–Wysocki–Zehnder, *Applications of Polyfold Theory I: The Polyfolds of Gromov–Witten
Theory* (Memoirs AMS 248, no. 1179, 2017), §2.2 (pp. 29–38): **Definitions 2.20–2.22, 2.24,
2.25, 2.27, 2.31–2.34** and **Lemma 2.35**, and §2.6 **Proposition 2.53** (p. 55), in the memoir's
form, from the book *Polyfold and Fredholm Theory* (Springer 2021).

# The recollections of sc-calculus, retracts, M-polyfolds and strong bundles

## The text, paraphrased

(Definition 2.20) sc⁰, sc¹, sc^k and sc-smooth maps between relatively open subsets of partial
quadrants; the chain rule.  (Definition 2.21) An sc-smooth retraction `r = r ∘ r` on `U`, the
retract `O = r(U)`; `Tr` is again a retraction.  (Definition 2.22) A local M-polyfold model
`(O, C, E)`: (1) `O = r(U)` for an sc-smooth retraction on `U` relatively open in `C`; (2) at every
smooth `x ∈ O`, `ker(1 − Dr(x))` has an sc-complement contained in `C`; (3) every `x ∈ O` is a
limit of smooth points `x_k ∈ O` with `d_C(x_k) = d_C(x)`.  The memoir says it is a special case of
a tame retract; in the paper only `(O, E, E)` is used.  (Definition 2.24) `f : O → O'` is sc¹ if
`f ∘ r` is.  (Definition 2.25) An M-polyfold: a paracompact Hausdorff space with a maximal atlas of
charts on local models.  (Definition 2.27) Groupoids.  (Definitions 2.31–2.34) Strong bundle maps
and retractions on `U ◁ F`, local strong bundles `K → O`, sc-smooth and sc⁺-sections, strong
bundles.  (Lemma 2.35) For a local sc-diffeomorphism `f : X → Y` and an sc-smooth `g : Z → Y`, the
fibred product `X ₓ×_g Z` is an M-polyfold and `π₂` is a local sc-diffeomorphism.
(Proposition 2.53) If `f : U → F` is sc⁰ and the induced maps `U_{m+k} → F_m` are `C^{k+1}` for
all `m, k`, then `f` is sc-smooth.

## What is formalized

* Definitions 2.20, 2.21, 2.24, 2.25, 2.27, 2.31–2.34 coincide with the book's (Definitions 1.1.15,
  2.1.1, 2.1.14, 2.3.4, 7.1.1, 2.6.1–2.6.6); they are `abbrev`s of the book's Lean notions, with
  `memoir_definition_2_20_comp` (chain rule, Theorem 1.3.1), `memoir_definition_2_21_tangent`
  (`Tr` is a retraction onto `TO`), `memoir_definition_2_24_iff` (one retraction suffices,
  Proposition 2.1.13).
* `IsLocalMPolyfoldModel` (Definition 2.22) and:
  - `IsLocalMPolyfoldModel.complement_le_minimalSubspace`: the sc-complement of (2), being a
    linear subspace inside `C`, lies in `C ∩ −C ⊆ E_x`; so (2) gives condition (2) of the book's
    tameness (2021 Definition 2.5.2) for every presentation of `C`;
  - `memoir_definition_2_22_univ_iff`: for `C = E` (the only case used in the paper) a local
    M-polyfold model is exactly an sc-smooth retract, and every retraction onto it is tame
    (`isTame_of_univ`).
* `memoir_lemma_2_35` (Lemma 2.35): from the book's Proposition 2.5.20 in the form
  `MPolyfold.isSubMPolyfold_fibredProduct` and `MPolyfold.isLocalScDiffeo_snd_fibredProduct`.
* `memoir_proposition_2_53` (Proposition 2.53): the book's Proposition 1.2.4 for all `k`
  (`IsScSmooth.of_contDiffOn_levels_text`).

## What the text leaves implicit, and the choices made

* **Definition 2.22 (2)** is read literally: the sc-complement `A` of `T_xO = ker(1 − Dr(x))`
  satisfies `A ⊆ C` (as a set), at every smooth point of `O`, interior points included.  Then
  `A ⊆ C ∩ −C`, the smallest of the subspaces `E_x`.  This is condition (2) of tameness; condition
  (1) of tameness, `d_C(r(y)) = d_C(y)` for all `y ∈ U`, is about the retraction and is not part of
  Definition 2.22.  For `C = E` both definitions reduce to "sc-smooth retract".
* `ker(1 − Dr(x)) = Dr(x)E = T_xO` for the sc-projection `Dr(x)` (`ker_id_sub_eq_range`).
* **Definition 2.25.**  The memoir's charts take values in local M-polyfold models; the book's in
  sc-smooth retracts.  In the paper all models are `(O, E, E)`, where the two notions agree
  (`memoir_definition_2_22_univ_iff`); `MPolyfoldMemoir` is the book's `MPolyfold`.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace GWMemoir

open Polyfold

universe u v w

variable {E F : ScBanach}

/-! ### Definitions 2.20, 2.21, 2.24 -/

/-- **Memoir Definition 2.20, p. 29**: sc-smooth maps between relatively open subsets of partial
quadrants (2021 Definition 1.1.15, p. 8). -/
abbrev IsScSmoothMemoir (U : Set (E 0)) (f : E 0 → F 0) : Prop := IsScSmooth U f

/-- **Memoir Definition 2.20, the chain rule** (2021 Theorem 1.3.1, p. 30): compositions of
sc-smooth maps are sc-smooth. -/
theorem memoir_definition_2_20_comp {G : ScBanach} {U : Set (E 0)} {V : Set (F 0)} {f : E 0 → F 0}
    {g : F 0 → G 0} (hU : IsScDomain E U) (hV : IsScDomain F V) (hg : IsScSmoothMemoir V g)
    (hf : IsScSmoothMemoir U f) (hfV : MapsTo f U V) : IsScSmoothMemoir U (g ∘ f) :=
  IsScSmooth.comp hU hV hg hf hfV

/-- **Memoir Definition 2.21, p. 29**: an sc-smooth retraction `r : U → U`, `r ∘ r = r`, on a
relatively open subset `U` of the partial quadrant `C` (2021 Definition 2.1.1, p. 47). -/
abbrev ScRetractionMemoir (E : ScBanach) (C : Set (E 0)) : Type := ScRetraction E C

/-- **Memoir Definition 2.21, the remark after it**: `Tr : TU → TU` is an sc-smooth retraction
onto `TO` (2021 Definition 2.1.16 and the remark after it). -/
theorem memoir_definition_2_21_tangent {C : Set (E 0)} (R : ScRetractionMemoir E C) :
    ∃ R' : ScRetraction E.tangent (E.tangentSet C),
      R'.U = E.tangentSet R.U ∧ (∀ p, R' p = tangentMap R.U R p) ∧
        R'.retract = retractTangent E C R.retract :=
  ⟨R.tangentRetraction, rfl, fun _ => rfl, R.tangentRetraction_retract⟩

/-- **Memoir Definition 2.24, p. 31**: `f : O → O'` is sc-smooth between the retracts if `f ∘ r`
is sc-smooth (2021 Definition 2.1.14, p. 51). -/
abbrev IsScSmoothRetractMapMemoir (E : ScBanach) (C O : Set (E 0)) (E' : ScBanach)
    (C' O' : Set (E' 0)) (f : E 0 → E' 0) : Prop :=
  IsScSmoothRetractMap E C O E' C' O' f

/-- **Memoir Definition 2.24 as printed**: one retraction `r` onto `O` with `f ∘ r` sc-smooth
suffices (2021 Proposition 2.1.13). -/
theorem memoir_definition_2_24_iff {E' : ScBanach} {C O : Set (E 0)} {C' O' : Set (E' 0)}
    {f : E 0 → E' 0} (hO : IsScRetract E C O) :
    IsScSmoothRetractMapMemoir E C O E' C' O' f ↔
      MapsTo f O O' ∧ ∃ R : ScRetraction E C, R.retract = O ∧ IsScSmooth R.U (f ∘ R) :=
  isScSmoothRetractMap_iff_exists hO

/-! ### Definition 2.22: local M-polyfold models -/

section LocalModel

variable {C O : Set (E 0)}

/-- For an sc-smooth retraction and `x ∈ O₁`, `ker(1 − Dr(x)) = Dr(x)E`. -/
theorem ker_id_sub_eq_range (R : ScRetraction E C) {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) :
    LinearMap.ker (ContinuousLinearMap.id ℝ (E 0) - scDeriv R.U R x : E 0 →ₗ[ℝ] E 0) =
      LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0) := by
  set D := scDeriv R.U R x
  have hDD : ∀ v, D (D v) = D v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self hx)
  ext v
  constructor
  · intro hv
    have : v - D v = 0 := hv
    exact ⟨v, (sub_eq_zero.1 this).symm⟩
  · rintro ⟨u, rfl⟩
    change D u - D (D u) = 0
    rw [hDD, sub_self]

/-- **Memoir Definition 2.22, p. 30 (local M-polyfold model)**: `C` is a partial quadrant of `E`
and (1) `O = r(U)` for an sc-smooth retraction `r` on `U` relatively open in `C`, such that (2) at
every smooth point `x ∈ O`, `ker(1 − Dr(x))` has an sc-complement `A` with `A ⊆ C`; (3) every
`x ∈ O` is the limit of smooth points `x_k ∈ O` with `d_C(x_k) = d_C(x)`. -/
structure IsLocalMPolyfoldModel (E : ScBanach) (C O : Set (E 0)) : Prop where
  isPartialQuadrant : IsPartialQuadrant E C
  retraction : ∃ R : ScRetraction E C, R.retract = O ∧
    ∀ x : E 1, x ∈ E.lvlSet O 1 → x ∈ E.smoothLvl 1 → ∃ A : Submodule ℝ (E 0),
      E.IsScSplitting
        (LinearMap.ker (ContinuousLinearMap.id ℝ (E 0) - scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) A ∧
      (A : Set (E 0)) ⊆ C
  approx : ∀ x ∈ O, ∃ u : ℕ → E 0, (∀ k, u k ∈ O ∧ u k ∈ E.smooth) ∧
    Tendsto u atTop (𝓝 x) ∧ ∀ k, degIndex E C (u k) = degIndex E C x

/-- A linear subspace contained in the partial quadrant `C` lies in `E_x` for every `x` and every
presentation `T` of `C`: with `v` also `−v` lies in `C`, so the quadrant coordinates of `v`
vanish. -/
theorem submodule_le_minimalSubspace {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    {A : Submodule ℝ (E 0)} (hA : (A : Set (E 0)) ⊆ C) (x : E 0) :
    A ≤ minimalSubspaceWith T x := by
  intro v hv
  rw [mem_minimalSubspaceWith]
  intro i _
  have h1 : T 0 v ∈ quadrant n W 0 := by have := hA hv; rw [hT] at this; exact this
  have h2 : T 0 (-v) ∈ quadrant n W 0 := by
    have := hA (A.neg_mem hv); rw [hT] at this; exact this
  have a1 := h1 i
  have a2 := h2 i
  rw [map_neg] at a2
  change 0 ≤ -((T 0 v).1 i) at a2
  linarith

/-- **Memoir Definition 2.22 (2) gives condition (2) of tameness** (2021 Definition 2.5.2, p. 64):
for the retraction `r` of (1), at every smooth `x ∈ O` the tangent space `T_xO = Dr(x)E` has an
sc-complement inside `E_x`, for every presentation of `C`. -/
theorem IsLocalMPolyfoldModel.complement_le_minimalSubspace (h : IsLocalMPolyfoldModel E C O) :
    ∃ R : ScRetraction E C, R.retract = O ∧
      ∀ (n : ℕ) (W : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)),
        C = T 0 ⁻¹' quadrant n W 0 →
        ∀ x : E 1, x ∈ E.lvlSet R.retract 1 → x ∈ E.smoothLvl 1 → ∃ A : Submodule ℝ (E 0),
          E.IsScSplitting (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) A ∧
            A ≤ minimalSubspaceWith T (E.toBase 1 x) := by
  obtain ⟨R, hRO, h2⟩ := h.retraction
  refine ⟨R, hRO, fun n W T hT x hx hs => ?_⟩
  obtain ⟨A, hA, hAC⟩ := h2 x (hRO ▸ hx) hs
  rw [ker_id_sub_eq_range R hx] at hA
  exact ⟨A, hA, submodule_le_minimalSubspace T hT hAC _⟩

/-- **A retraction on an open subset of `E` (`C = E`) is tame** (2021 Definition 2.5.2): every
presentation of `E` as a partial quadrant has no quadrant coordinates, `d_E ≡ 0`, `E_x = E`. -/
theorem isTame_of_univ (R : ScRetraction E univ) : R.IsTame := by
  intro n W T hT
  have hn : n = 0 := by
    by_contra hn
    have hmem : (T 0).symm ((fun _ => (-1 : ℝ)), 0) ∈ (univ : Set (E 0)) := mem_univ _
    rw [hT] at hmem
    have := hmem ⟨0, Nat.pos_of_ne_zero hn⟩
    simp at this
    linarith
  subst hn
  refine ⟨fun x _ => ?_, fun x hx hs => ⟨_, R.isScSplitting_range_scDeriv hx hs, fun v _ => ?_⟩⟩
  · rw [degIndex_eq T hT (mem_univ _), degIndex_eq T hT (mem_univ _)]
    simp [degIndexWith, quadrantDeg]
  · rw [mem_minimalSubspaceWith]
    intro i
    exact i.elim0

/-- `d_E ≡ 0` on the partial quadrant `C = E`. -/
theorem degIndex_univ_eq (x y : E 0) : degIndex E univ x = degIndex E univ y := by
  obtain ⟨n, W, T, hT⟩ := isPartialQuadrant_univ E
  rw [degIndex_eq T hT (mem_univ _), degIndex_eq T hT (mem_univ _)]
  have hn : n = 0 := by
    by_contra hn
    have hmem : (T 0).symm ((fun _ => (-1 : ℝ)), 0) ∈ (univ : Set (E 0)) := mem_univ _
    rw [hT] at hmem
    have := hmem ⟨0, Nat.pos_of_ne_zero hn⟩
    simp at this
    linarith
  subst hn
  simp [degIndexWith, quadrantDeg]

/-- An sc⁰ map sends smooth points of `U` to smooth points. -/
theorem IsSc0.mem_smooth {U : Set (E 0)} {f : E 0 → F 0} (hf : IsSc0 E F U f) {x : E 0}
    (hxU : x ∈ U) (hx : x ∈ E.smooth) : f x ∈ F.smooth := by
  rw [ScScale.mem_smooth_iff] at hx ⊢
  intro m
  obtain ⟨y, rfl⟩ := hx m
  exact hf.1 m y (by rw [ScBanach.mem_lvlSet]; exact hxU)

/-- **Memoir Definition 2.22 for `C = E`** (the models `(O, E, E)` used in the paper): a local
M-polyfold model is the same as an sc-smooth retract.  Condition (2) holds with
`A = (1 − Dr(x))E`, condition (3) by density of the smooth points: `r(u_k) → r(x) = x` for smooth
`u_k → x`. -/
theorem memoir_definition_2_22_univ_iff : IsLocalMPolyfoldModel E univ O ↔ IsScRetract E univ O := by
  refine ⟨fun h => ?_, fun ⟨R, hRO⟩ => ⟨isPartialQuadrant_univ E, ⟨R, hRO, fun x hx hs => ?_⟩,
    fun x hx => ?_⟩⟩
  · obtain ⟨R, hRO, -⟩ := h.retraction
    exact ⟨R, hRO⟩
  · have hx' : x ∈ E.lvlSet R.retract 1 := hRO ▸ hx
    refine ⟨LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - scDeriv R.U R x : E 0 →ₗ[ℝ] E 0),
      ?_, subset_univ _⟩
    have := R.isScSplitting_range_scDeriv hx' hs
    rw [← ker_id_sub_eq_range R hx'] at this
    exact this
  · -- density of smooth points in `O`
    have hxO : x ∈ R.retract := hRO ▸ hx
    have hxU : x ∈ R.U := R.retract_subset hxO
    obtain ⟨Uo, hUo, hUeq⟩ := R.relOpen.relOpen
    have hUopen : IsOpen R.U := by rw [hUeq, inter_univ]; exact hUo
    have hdense : Dense (E.smooth : Set (E 0)) := by
      have := E.dense_smooth 0
      rwa [ScScale.smoothLvl_zero] at this
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (hdense x)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (hUopen.mem_nhds hxU))
    have hsc0 : IsSc0 E E R.U R := R.isScSmooth.isSc1.isSc0
    have hlim' : Tendsto (fun k => u (k + N)) atTop (𝓝 x) := (tendsto_add_atTop_iff_nat N).2 hlim
    have hcont : ContinuousWithinAt R R.U x := hsc0.continuousOn_base x hxU
    have hlimR : Tendsto (fun k => R (u (k + N))) atTop (𝓝 (R x)) :=
      hcont.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim', Eventually.of_forall fun k =>
        hN (k + N) (Nat.le_add_left N k)⟩)
    rw [R.apply_eq_self_of_mem_retract hxO] at hlimR
    refine ⟨fun k => R (u (k + N)), fun k => ⟨hRO ▸ R.apply_mem_retract (hN (k + N)
      (Nat.le_add_left N k)), hsc0.mem_smooth (hN (k + N) (Nat.le_add_left N k)) (hu (k + N))⟩,
      hlimR, fun k => degIndex_univ_eq _ _⟩

end LocalModel

/-! ### Definitions 2.25, 2.27, 2.31–2.34 -/

/-- **Memoir Definition 2.25, p. 32 (M-polyfold)**: a paracompact Hausdorff space with a maximal
atlas of sc-smoothly compatible charts (2021 Definitions 2.3.2–2.3.4).  The memoir's charts take
values in local M-polyfold models; in the paper these are `(O, E, E)`, where local models and
sc-smooth retracts agree (`memoir_definition_2_22_univ_iff`). -/
abbrev MPolyfoldMemoir (X : Type u) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] :
    Type _ :=
  MPolyfold X

/-- **Memoir Definition 2.27, p. 32 (groupoid)**: a small category with invertible morphisms,
given by its structure maps `s, t, m, u, i` (2021 Definition 7.1.1). -/
abbrev GroupoidMemoir (Obj Mor : Type u) : Type _ := GroupoidStr Obj Mor

section StrongBundles

variable {E' F' : ScBanach}

/-- **Memoir Definition 2.31, p. 35 (strong bundle map)**: `Φ : U ◁ F → U' ◁ F'` of the form
`(φ(u), Γ(u, h))`, `Γ` linear in `h`, preserving the double filtration and sc-smooth on `[0]`
and `[1]` (2021 Definition 2.6.1). -/
abbrev IsStrongBundleMapMemoir (U : Set (E 0)) (U' : Set (E' 0))
    (Φ : E 0 × F 0 → E' 0 × F' 0) : Prop :=
  IsStrongBundleMap U U' Φ

/-- **Memoir Definition 2.31 (strong bundle retraction)**: `R(u, h) = (r(u), ρ(u)h)` with
`R ∘ R = R` (2021 Definition 2.6.1). -/
abbrev IsStrongBundleRetractionMemoir (U : Set (E 0)) (R : E 0 × F 0 → E 0 × F 0) : Prop :=
  IsStrongBundleRetraction U R

/-- **Memoir Definition 2.32, p. 35 (strong local bundle `K → O`)**: `K = R(U ◁ F)` (2021
Definition 2.6.2). -/
abbrev IsStrongBundleRetractMemoir (C : Set (E 0)) (K : Set (E 0 × F 0)) : Prop :=
  IsStrongBundleRetract C K

/-- **Memoir Definition 2.33, p. 35 (sc-smooth section of `K → O`)** (2021 Definition 2.6.3). -/
abbrev IsScSmoothSectionMemoir (C O : Set (E 0)) (K : Set (E 0 × F 0)) (f : E 0 → E 0 × F 0) :
    Prop :=
  IsScSmoothSection C O K f

/-- **Memoir Definition 2.33 (sc⁺-section of `K → O`)**: sc-smooth into `K(1)` (2021
Definition 2.6.3). -/
abbrev IsScPlusSectionMemoir (C O : Set (E 0)) (K : Set (E 0 × F 0)) (f : E 0 → E 0 × F 1) :
    Prop :=
  IsScPlusSection C O K f

/-- **Memoir Definition 2.34, p. 36 (strong bundle over an M-polyfold)**: a surjection
`P : Y → X` with a maximal atlas of strong bundle charts with sc-smooth transition maps on
`K(0)` and `K(1)` (2021 Definitions 2.6.4–2.6.6); `Γ(P)`, `Γ⁺(P)` are
`StrongBundle.IsScSmoothSection`, `StrongBundle.IsScPlusSection`. -/
abbrev StrongBundleMemoir {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] : Type _ :=
  StrongBundle PX P

end StrongBundles

/-! ### Lemma 2.35: fibred products with a local sc-diffeomorphism -/

section Lemma235

variable {X : Type u} {Y : Type v} {Z : Type w} [TopologicalSpace X] [T2Space X]
  [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] [TopologicalSpace Z]
  [T2Space Z] [ParacompactSpace Z] {PX : MPolyfold X} {PY : MPolyfold Y} {PZ : MPolyfold Z}
  [ParacompactSpace (X × Z)]

/-- **Memoir Lemma 2.35, p. 36** ([24] Lemma 2.8): for a local sc-diffeomorphism `f : X → Y` and
an sc-smooth `g : Z → Y`, the fibred product `X ₓ×_g Z` is a sub-M-polyfold of `X × Z` (so an
M-polyfold with the induced structure), and `π₂ : X ₓ×_g Z → Z` is a local sc-diffeomorphism.
From the book's Proposition 2.5.20 (2021 p. 79) in the case of a local sc-diffeomorphism. -/
theorem memoir_lemma_2_35 {f : X → Y} {g : Z → Y} (hf : PX.IsLocalScDiffeo PY f)
    (hg : PZ.IsScSmoothMap PY g) :
    ∃ hA : (PX.prod PZ).IsSubMPolyfold (MPolyfold.fibredProduct f g),
      haveI := (PX.prod PZ).paracompactSpace_subtype (MPolyfold.fibredProduct f g)
      (MPolyfold.subPolyfold hA).IsLocalScDiffeo PZ
        fun a : MPolyfold.fibredProduct f g => a.1.2 := by
  have hA := MPolyfold.isSubMPolyfold_fibredProduct hf hg
  have := (PX.prod PZ).paracompactSpace_subtype (MPolyfold.fibredProduct f g)
  exact ⟨hA, MPolyfold.isLocalScDiffeo_snd_fibredProduct hA hf hg⟩

end Lemma235

/-! ### Proposition 2.53 -/

/-- **Memoir Proposition 2.53, p. 55** ([28] Proposition 2.4): if `f : U → F` is sc⁰ on a
relatively open `U ⊆ C ⊆ E` and the induced maps `f : U_{m+k} → F_m` are of class `C^{k+1}` for
all `m, k ≥ 0`, then `f` is sc-smooth.  The book's Proposition 1.2.4 (2021 p. 15) for every `k`
(`IsScSmooth.of_contDiffOn_levels_text`). -/
theorem memoir_proposition_2_53 {U : Set (E 0)} {f : E 0 → F 0} (hU : IsScDomain E U)
    (hf : IsSc0 E F U f)
    (h : ∀ m k : ℕ, ContDiffOn ℝ (k + 1) (levelMap f m ∘ E.inclK m k) (E.lvlSet U (m + k))) :
    IsScSmooth U f :=
  IsScSmooth.of_contDiffOn_levels_text hU hf h

end GWMemoir
