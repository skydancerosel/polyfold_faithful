import Polyfold.Chapter3.IndexAlongPathsLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.1, p. 201:
**Definition 6.1** (the space `Lin(f, x)` of linearizations of an sc-Fredholm section at a smooth
point), and the facts stated with it: its members differ by sc⁺-operators, are Fredholm with one
index, and (p. 219, before Proposition 6.26) `Lin(f, x)` is convex *(book 2017: Definition 6.1;
see `BookConcordance.md`)*.

# The space of linearizations `Lin(f, x)`

## The text, paraphrased

At a smooth point `x` take a local sc⁺-section `s` with `s(x) = f(x)`; then
`(f − s)'(x) : T_xX → Y_x` is well defined.  (Definition 6.1)
`Lin(f, x) = {(f − s)'(x) + a | a : T_xX → Y_x an sc⁺-operator}`.  The operators in `Lin(f, x)`
differ by sc⁺-operators and are sc-Fredholm of one index `ind(f, x)`.  (p. 219) `Lin(f, x)` is a
convex subset of the Fredholm operators `T_xX → Y_x` with the metric of the operator norm.

## What is formalized

* `Polyfold.ChartPoint B x`: a strong bundle chart `c` of `B` around `x` and the level-`1` point `z`
  over `φ(x)`; `p.T = T_zO = Dr(z)E` (the text's `T_xX` read in the chart) and `p.K = K_z = ρ(z)F`
  (the text's `Y_x`), closed, hence complete.
* `ChartPoint.IsScPlusOp p a`: `a : T_zO → K_z` is level `0` of an sc⁺-operator between the
  sc-subspaces `T_zO` and `K_z`.
* `ChartPoint.linSet p f` (**Definition 6.1**): the operators `(f + s)'(x) + a` for an
  sc⁺-section `s` with `(f + s)(x) = 0` and an sc⁺-operator `a`; `mem_linSet_iff`: for one such
  `s` it is `(f + s)'(x) + {sc⁺-operators}`, as in the text.
* `linSet_nonempty`, `isScPlusOp_sub_of_mem_linSet` (members differ by sc⁺-operators),
  `exists_index_linSet` (members are Fredholm of one index), `convex_linSet`.

## Reading

The text's `f − s` with `s(x) = f(x)` is the project's `f + s` with `(f + s)(x) = 0` (`sectionAdd`,
as in `StrongBundle.IsIndexAt`).  `T_xX` and `Y_x` have no intrinsic linear structure in the project
(gaps G.6, G.7, G.13), so `Lin(f, x)` is made in a chart; the operators are their level-`0` maps
`T_zO → K_z`, which is where the operator-norm metric of p. 219 lives.  The sections `s` are global
sc⁺-sections; that one exists through `−f(x)` is the hypothesis `B.HasScPlusSectionsThrough` of
`linSet_nonempty` (true with sc-smooth bump functions, which the text assumes from §6.2 on, and for
a bundle with a chart over the whole base, as in the local constructions of §6.5).  "sc-Fredholm" is
proved on level `0`, which is what the determinant lines use.

## Proofs

* **Two sections differ by an sc⁺-operator** (`exists_isScPlusOp_linAt_eq`): for sc⁺-sections
  `s, s'` with `f + s`, `f + s'` vanishing at `x`, put `d = s' − s`; then `f + s' = (f + s) + d`, so
  on `U` the principal parts satisfy `(f + s')^ ∘ r = (f + s)^ ∘ r + ι ∘ d̂₁ ∘ r` with the lift
  `d̂₁ : O → F₁` (`principal_sectionAdd`, `toBase_principalLift`), and
  `D((f + s')^ ∘ r)(z) = D((f + s)^ ∘ r)(z) + ι ∘ D(d̂₁ ∘ r)(z)` (`scDeriv_add_toBase_one_apply`).
  At the smooth point `z`, `D(d̂₁ ∘ r)(z) : E → F¹` is an sc-operator (`scOperator_deriv`), and its
  values on `T_zO` lie in `K_z` (a difference of two linearizations at a zero,
  `rho_scDeriv_comp_r`), so its restriction is an sc⁺-operator `T_zO → K_z`
  (`isScPlusOp_of_shift`).
* **Fredholm of one index**: `(f + s)'(x)` is Fredholm of index `ind(f, x)` (the germ data of the
  sc-Fredholm section `f + s`, Theorem 3.15, `isLinOfIndex_of_conjugationData`), an sc⁺-operator is
  compact on level `0` (`ScPlus.isCompactOperator`, `IsScPlusOp.isCompactOperator`), and compact
  perturbations keep the Fredholm property and the index (`isFredholm_add_isCompactOperator`,
  `fredholmIndex_add_isCompactOperator`); `IsIndexAt.unique` makes the index independent of `s`.
* **Convexity**: by `mem_linSet_iff` with one `s`, `Lin(f, x)` is `(f + s)'(x)` plus the
  sc⁺-operators, which are closed under sums and scalar multiples (`IsScPlusOp.add`,
  `IsScPlusOp.smul`).
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f s : X → Y}

open StrongRetr

/-- **The sum rule for `g + ι ∘ h` at a level-`1` point**: if `g' = g + ι ∘ h` on `U` for sc¹ maps
`g, g' : U → F` and `h : U → F¹`, then `Dg'(z) = Dg(z) + ι ∘ Dh(z)` (uniqueness of the derivative
within `U₁` and the density of `E₁` in `E₀`). -/
theorem scDeriv_add_toBase_one_apply {E F : ScBanach} {C U : Set (E 0)}
    (hU : IsRelOpenInQuadrant E C U)
    {g g' : E 0 → F 0} {h : E 0 → F.shift 0} (hg : IsSc1 U g) (hg' : IsSc1 U g')
    (hh : IsSc1 (F := F.shift) U h) (heq : ∀ u ∈ U, g' u = g u + F.toBase 1 (h u)) {z : E 1}
    (hz : z ∈ E.lvlSet U 1) (v : E 0) :
    scDeriv U g' z v = scDeriv U g z v + F.toBase 1 (scDeriv (F := F.shift) U h z v) := by
  have d1 := hg.isSc1With_scDeriv.hasFDerivWithinAt z hz
  have d2 := hh.isSc1With_scDeriv.hasFDerivWithinAt z hz
  have d3 := hg'.isSc1With_scDeriv.hasFDerivWithinAt z hz
  set L : E 0 →L[ℝ] F 0 := scDeriv U g z + (F.toBase 1).comp (scDeriv (F := F.shift) U h z)
    with hL
  have d4 : HasFDerivWithinAt (g' ∘ E.toBase 1) (L.comp (E.toBase 1)) (E.lvlSet U 1) z := by
    have := d1.add ((F.toBase 1).hasFDerivAt.comp_hasFDerivWithinAt z d2)
    refine (this.congr_fderiv ?_).congr (fun y hy => ?_) ?_
    · ext w
      simp [hL]
    · exact heq _ hy
    · exact heq _ hz
  have heq' := ContinuousLinearMap.ext_of_comp_toBase_one
    ((hU.isScDomain.uniqueDiffWithinAt 1 z hz).eq d3 d4)
  rw [heq', hL]
  rfl

variable (B) in
/-- **A point read in a strong bundle chart**: a chart `c` of `B` around `x` and the level-`1`
point `z` of the model over `φ(x)`. -/
structure ChartPoint (x : X) where
  /-- The chart. -/
  c : StrongBundleChart PX P
  isChart : B.IsChart c
  mem_source : x ∈ c.φ.source
  /-- The level-`1` point over `φ(x)`. -/
  z : c.φ.model.E 1
  toBase_z : c.φ.model.E.toBase 1 z = c.φ x

namespace ChartPoint

variable {x : X} (p : ChartPoint B x)

theorem mem_O : p.c.φ.model.E.toBase 1 p.z ∈ r p.c.R '' p.c.U := by
  rw [p.toBase_z, p.c.r_image]
  exact p.c.φ.mapsTo_model x p.mem_source

theorem mem_U : p.c.φ.model.E.toBase 1 p.z ∈ p.c.U := mem_U_of_mem_O p.c.isRetraction p.mem_O

/-- `T_xX` in the chart: `T_zO = Dr(z)E`. -/
abbrev T : Submodule ℝ (p.c.φ.model.E 0) := rangeS (scDeriv p.c.U (r p.c.R) p.z)

/-- `Y_x` in the chart: `K_z = ρ(z)F`. -/
abbrev K : Submodule ℝ (p.c.F 0) := rangeS (ρCLM p.c.isRetraction p.mem_U)

instance : CompleteSpace ↥p.T :=
  (isClosed_range_of_idem _
    (scDeriv_r_idem_at p.c.relOpen p.c.isRetraction p.mem_O)).completeSpace_coe

instance : CompleteSpace ↥p.K :=
  (isClosed_range_of_idem _ fun k => ρ_ρ p.c.isRetraction p.mem_O k).completeSpace_coe

/-- `a : T_zO → K_z` **is an sc⁺-operator** `T_xX → Y_x`: `T_zO` and `K_z` are sc-subspaces and
`a` is level `0` of an sc⁺-operator between them. -/
def IsScPlusOp (a : ↥p.T →L[ℝ] ↥p.K) : Prop :=
  ∃ (hT : p.c.φ.model.E.IsScSubspace p.T) (hK : p.c.F.IsScSubspace p.K)
    (S : ScPlus (p.c.φ.model.E.ofSubspace hT) (p.c.F.ofSubspace hK)),
    ∀ v : (p.c.φ.model.E.ofSubspace hT) 0,
      ((S.toScOperator 0 v).1 : p.c.F 0) = (a ⟨v.1, v.2⟩ : p.c.F 0)

variable (f) in
/-- **Definition 6.1**: `Lin(f, x)` in the chart point `p`: the operators
`(f + s)'(x) + a : T_zO → K_z` for an sc⁺-section `s` with `(f + s)(x) = 0` (the text's
`(f − s)'(x)` with `s(x) = f(x)`) and an sc⁺-operator `a`. -/
def linSet : Set (↥p.T →L[ℝ] ↥p.K) :=
  {L | ∃ s : X → Y, B.IsScPlusSection s ∧ IsZeroAt P (sectionAdd P f s) x ∧
    ∃ a : ↥p.T →L[ℝ] ↥p.K, p.IsScPlusOp a ∧
      ∀ v, (L v : p.c.F 0) =
        linAt p.c.U p.c.R (p.c.principal (sectionAdd P f s)) p.z v + (a v : p.c.F 0)}

/-! ### Sc⁺-operators `T_zO → K_z` -/

/-- `z` is a smooth point of `E` when `x` is a smooth point of `X`. -/
theorem z_mem_smoothLvl (hx : x ∈ PX.smoothSet) : p.z ∈ p.c.φ.model.E.smoothLvl 1 := by
  change p.c.φ.model.E.toBase 1 p.z ∈ p.c.φ.model.E.smooth
  rw [p.toBase_z, ScScale.mem_smooth_iff]
  intro m
  exact (PX.mem_levelSet_iff p.c.isChart p.mem_source).1 (Set.mem_iInter.1 hx m)

/-- `T_zO` is an sc-subspace at a smooth point. -/
theorem isScSubspace_T (hx : x ∈ PX.smoothSet) : p.c.φ.model.E.IsScSubspace p.T :=
  isScSubspace_range_scDeriv_r_at p.c.relOpen p.c.isRetraction p.mem_O (p.z_mem_smoothLvl hx)

/-- `K_z` is an sc-subspace at a smooth point. -/
theorem isScSubspace_K (hx : x ∈ PX.smoothSet) : p.c.F.IsScSubspace p.K :=
  isScSubspace_range_ρCLM_of_mem_smooth p.c.isRetraction p.mem_U p.mem_O (p.z_mem_smoothLvl hx)

variable {p} in
/-- The sum of two sc⁺-operators `T_zO → K_z` is one. -/
theorem IsScPlusOp.add {a b : ↥p.T →L[ℝ] ↥p.K} (ha : p.IsScPlusOp a) (hb : p.IsScPlusOp b) :
    p.IsScPlusOp (a + b) := by
  obtain ⟨hT, hK, S, hS⟩ := ha
  obtain ⟨hT', hK', S', hS'⟩ := hb
  refine ⟨hT, hK, S + S', fun v => ?_⟩
  have h1 := hS v
  have h2 := hS' v
  simp only [ScPlus.toScOperator_apply, ScOperator.add_apply, map_add] at h1 h2 ⊢
  simp only [Submodule.coe_add, add_apply]
  rw [← h1, ← h2]
  rfl

variable {p} in
/-- A scalar multiple of an sc⁺-operator `T_zO → K_z` is one. -/
theorem IsScPlusOp.smul {a : ↥p.T →L[ℝ] ↥p.K} (ha : p.IsScPlusOp a) (t : ℝ) :
    p.IsScPlusOp (t • a) := by
  obtain ⟨hT, hK, S, hS⟩ := ha
  refine ⟨hT, hK, ⟨fun m => t • S m, fun m y => ?_⟩, fun v => ?_⟩
  · simp only [smul_apply, map_smul]
    rw [S.incl_comm]
  · have h1 := hS v
    simp only [ScPlus.toScOperator_apply] at h1 ⊢
    change (((p.c.F.ofSubspace hK).incl 0 (t • S 0 v)).1 : p.c.F 0) = _
    rw [map_smul]
    change t • (((p.c.F.ofSubspace hK).incl 0 (S 0 v)).1 : p.c.F 0) = _
    rw [h1]
    rfl

/-- `0 : T_zO → K_z` is an sc⁺-operator at a smooth point. -/
theorem isScPlusOp_zero (hx : x ∈ PX.smoothSet) : p.IsScPlusOp 0 := by
  refine ⟨p.isScSubspace_T hx, p.isScSubspace_K hx, ⟨fun _ => 0, fun _ _ => by simp⟩, fun v => ?_⟩
  simp
  rfl

variable {p} in
/-- **An sc⁺-operator `T_zO → K_z` is compact** (the remark after Definition 1.4,
`ScPlus.isCompactOperator`, on level `0`, read through `(T_zO)₀ = T_zO` and `(K_z)₀ = K_z`). -/
theorem IsScPlusOp.isCompactOperator {a : ↥p.T →L[ℝ] ↥p.K} (ha : p.IsScPlusOp a) :
    IsCompactOperator a := by
  obtain ⟨hT, hK, S, hS⟩ := ha
  have hc := S.isCompactOperator 0
  let e₁ : ↥p.T →L[ℝ] (p.c.φ.model.E.ofSubspace hT) 0 :=
    (p.c.φ.model.E.levelSubZeroEquiv p.T).symm.toContinuousLinearMap
  let g : (p.c.F.ofSubspace hK) 0 → ↥p.K := fun w => ⟨w.1, w.2⟩
  have hg : Continuous g := continuous_subtype_val.subtype_mk _
  have e : (a : ↥p.T → ↥p.K) = g ∘ (S.toScOperator 0) ∘ e₁ := by
    funext v
    exact Subtype.ext (hS (e₁ v)).symm
  rw [e]
  exact (hc.comp_clm e₁).continuous_comp hg

/-- **An sc-operator `D : E → F¹` with values in `K_z` on `T_zO` restricts to an sc⁺-operator**
`T_zO → K_z`: level `m` is `D_m : (T_zO)_m → (K_z)_{m+1}`. -/
theorem isScPlusOp_of_shift (hT : p.c.φ.model.E.IsScSubspace p.T) (hK : p.c.F.IsScSubspace p.K)
    {D : p.c.φ.model.E 0 →L[ℝ] p.c.F.shift 0}
    (hD : IsScOperator (E := p.c.φ.model.E) (F := p.c.F.shift) D)
    (hDK : ∀ v ∈ p.T, p.c.F.toBase 1 (D v) ∈ p.K) {a : ↥p.T →L[ℝ] ↥p.K}
    (ha : ∀ v : p.T, (a v : p.c.F 0) = p.c.F.toBase 1 (D v)) : p.IsScPlusOp a := by
  refine ⟨hT, hK, ⟨fun m => ((hD.toScOperator m).comp
    (p.c.φ.model.E.levelSub p.T m).subtypeL).codRestrict (p.c.F.levelSub p.K (m + 1)) fun y => ?_,
    fun m y => ?_⟩, fun v => ?_⟩
  · rw [ScBanach.mem_levelSub, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      p.c.F.shift_toBase, hD.toScOperator.toBase_comm, hD.toScOperator_zero]
    exact hDK _ y.2
  · exact Subtype.ext (hD.toScOperator.incl_comm m y.1)
  · rw [ha]
    change p.c.F.incl 0 (hD.toScOperator 0 v.1) = p.c.F.toBase 1 (D v.1)
    rw [hD.toScOperator_zero]
    rfl

/-- At a zero `x` of an sc-smooth section `g`, `D(ĝ ∘ r)(z)` takes values in `K_z`
(`rho_scDeriv_comp_r`). -/
theorem scDeriv_mem_K {g : X → Y} (hg : B.IsScSmoothSection g) (hx : IsZeroAt P g x)
    (v : p.c.φ.model.E 0) : scDeriv p.c.U (p.c.principal g ∘ r p.c.R) p.z v ∈ p.K :=
  ⟨_, rho_scDeriv_comp_r p.c.relOpen p.c.isRetraction (hg.isSc1_principal_comp_r p.isChart)
    (fun y hy => p.c.principal_mem_K hg.1 (p.c.r_image ▸ hy)) p.mem_O
    (by rw [p.toBase_z]; exact (p.c.isZeroAt_iff hg.1 p.mem_source).1 hx) v⟩

/-- **Two sections through the zero give linearizations differing by an sc⁺-operator**: for
sc⁺-sections `s, s'` with `(f + s)(x) = 0 = (f + s')(x)`,
`(f + s')'(x) = (f + s)'(x) + b` with `b : T_zO → K_z` an sc⁺-operator (`b = ι ∘ D(d̂₁ ∘ r)(z)` for
`d = s' − s`; module docstring). -/
theorem exists_isScPlusOp_linAt_eq (hf : B.IsScFredholmSection f) {s s' : X → Y}
    (hs : B.IsScPlusSection s) (hs' : B.IsScPlusSection s')
    (hx : IsZeroAt P (sectionAdd P f s) x) (hx' : IsZeroAt P (sectionAdd P f s') x) :
    ∃ b : ↥p.T →L[ℝ] ↥p.K, p.IsScPlusOp b ∧ ∀ v,
      linAt p.c.U p.c.R (p.c.principal (sectionAdd P f s')) p.z v =
        linAt p.c.U p.c.R (p.c.principal (sectionAdd P f s)) p.z v + (b v : p.c.F 0) := by
  have hfs := hf.isScSmooth
  have hg := hfs.sectionAdd hs
  have hg' := hfs.sectionAdd hs'
  have hxs : x ∈ PX.smoothSet := (theorem_3_15 hf hs).mem_smoothSet_of_isZeroAt hx
  set d := sectionDiff P s' s with hd_def
  have hd : B.IsScPlusSection d := hs'.add (hs.smul_left (isScSmoothMap_real_const (-1)))
  have hsec : sectionAdd P (sectionAdd P f s) d = sectionAdd P f s' :=
    sectionAdd_sectionAdd_sectionDiff hfs.1 hs.1 hs'.1
  have hlift : IsScSmooth (F := p.c.F.shift) p.c.U (p.c.principalLift d ∘ r p.c.R) :=
    (((hd.isScSmoothRetractMap_one p.isChart).comp_isScSmooth
      (p.c.isRetraction.baseRetraction p.c.relOpen) p.c.base_retract).snd
      p.c.relOpen.isScDomain).congr p.c.relOpen.isScDomain fun _ _ => rfl
  have hder : ∀ v, scDeriv p.c.U (p.c.principal (sectionAdd P f s') ∘ r p.c.R) p.z v =
      scDeriv p.c.U (p.c.principal (sectionAdd P f s) ∘ r p.c.R) p.z v +
        p.c.F.toBase 1 (scDeriv (F := p.c.F.shift) p.c.U (p.c.principalLift d ∘ r p.c.R) p.z v) :=
    scDeriv_add_toBase_one_apply p.c.relOpen (hg.isSc1_principal_comp_r p.isChart)
      (hg'.isSc1_principal_comp_r p.isChart) hlift.isSc1 (fun u hu => by
        have hO := p.c.r_mem_O hu
        simp only [Function.comp_apply]
        rw [← hsec, p.c.principal_sectionAdd hg.1 hd.1 hO, hd.toBase_principalLift p.isChart hO])
      p.mem_U
  set D := scDeriv (F := p.c.F.shift) p.c.U (p.c.principalLift d ∘ r p.c.R) p.z with hD_def
  have hDop : IsScOperator (E := p.c.φ.model.E) (F := p.c.F.shift) D :=
    hlift.isSc1.isSc1With_scDeriv.scOperator_deriv p.mem_U (p.z_mem_smoothLvl hxs)
  have hDK : ∀ v, p.c.F.toBase 1 (D v) ∈ p.K := fun v => by
    have h := hder v
    have e : p.c.F.toBase 1 (D v) =
        scDeriv p.c.U (p.c.principal (sectionAdd P f s') ∘ r p.c.R) p.z v -
          scDeriv p.c.U (p.c.principal (sectionAdd P f s) ∘ r p.c.R) p.z v := by
      rw [h]; abel
    rw [e]
    exact sub_mem (p.scDeriv_mem_K hg' hx' v) (p.scDeriv_mem_K hg hx v)
  let b : ↥p.T →L[ℝ] ↥p.K :=
    (((p.c.F.toBase 1).comp D).comp p.T.subtypeL).codRestrict p.K fun v => hDK v
  refine ⟨b, p.isScPlusOp_of_shift (p.isScSubspace_T hxs) (p.isScSubspace_K hxs) hDop
    (fun v _ => hDK v) (fun v => rfl), fun v => ?_⟩
  rw [linAt_apply, linAt_apply, hder]
  rfl

/-! ### `Lin(f, x)` -/

/-- **`Lin(f, x)` for one section**: for a fixed sc⁺-section `s` with `(f + s)(x) = 0`, `Lin(f, x)`
is `(f + s)'(x) + {sc⁺-operators}`, as in Definition 6.1 (the choice of `s` does not matter). -/
theorem mem_linSet_iff (hf : B.IsScFredholmSection f) (hs : B.IsScPlusSection s)
    (hx : IsZeroAt P (sectionAdd P f s) x) (L : ↥p.T →L[ℝ] ↥p.K) :
    L ∈ p.linSet f ↔ ∃ a : ↥p.T →L[ℝ] ↥p.K, p.IsScPlusOp a ∧
      ∀ v, (L v : p.c.F 0) =
        linAt p.c.U p.c.R (p.c.principal (sectionAdd P f s)) p.z v + (a v : p.c.F 0) := by
  constructor
  · rintro ⟨s', hs', hx', a', ha', hL⟩
    obtain ⟨b, hb, hbv⟩ := p.exists_isScPlusOp_linAt_eq hf hs hs' hx hx'
    refine ⟨b + a', hb.add ha', fun v => ?_⟩
    rw [hL, hbv, add_apply, Submodule.coe_add, add_assoc]
  · rintro ⟨a, ha, hL⟩
    exact ⟨s, hs, hx, a, ha, hL⟩

/-- `Lin(f, x)` is not empty when there is an sc⁺-section through `−f(x)`. -/
theorem linSet_nonempty (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    (hsec : B.HasScPlusSectionsThrough) : (p.linSet f).Nonempty := by
  have hfs : IsSection P f := hf.isScSmooth.1
  have he : f x ∈ B.toMPolyfold0.smoothSet :=
    mem_iInter.2 fun m => hf.isScSmooth.2.mapsTo_levelSet m (mem_iInter.1 hx m)
  obtain ⟨s₀, hs₀, hs₀x⟩ := hsec x hx (f x) he (hfs x)
  set s := sectionSmul P (fun _ => (-1 : ℝ)) s₀ with hsdef
  have hs : B.IsScPlusSection s := hs₀.smul_left (isScSmoothMap_real_const (-1))
  have hzero : IsZeroAt P (sectionAdd P f s) x := by
    unfold IsZeroAt
    rw [sectionAdd_apply hfs hs.1]
    have h1 : (⟨s x, hs.1 x⟩ : P ⁻¹' {x}) = (-1 : ℝ) • ⟨s₀ x, hs₀.1 x⟩ :=
      Subtype.ext (sectionSmul_apply (f := fun _ => (-1 : ℝ)) hs₀.1 x)
    have h2 : (⟨s₀ x, hs₀.1 x⟩ : P ⁻¹' {x}) = ⟨f x, hfs x⟩ := Subtype.ext hs₀x
    rw [h1, h2, neg_one_smul, add_neg_cancel]
    rfl
  have hg := hf.isScSmooth.sectionAdd hs
  let L : ↥p.T →L[ℝ] ↥p.K :=
    (linAt p.c.U p.c.R (p.c.principal (sectionAdd P f s)) p.z).codRestrict p.K
      fun v => p.scDeriv_mem_K hg hzero v
  refine ⟨L, s, hs, hzero, 0, p.isScPlusOp_zero hx, fun v => ?_⟩
  rw [zero_apply, Submodule.coe_zero, add_zero]
  rfl

/-- **The members of `Lin(f, x)` differ by sc⁺-operators.** -/
theorem isScPlusOp_sub_of_mem_linSet (hf : B.IsScFredholmSection f) {L L' : ↥p.T →L[ℝ] ↥p.K}
    (hL : L ∈ p.linSet f) (hL' : L' ∈ p.linSet f) : p.IsScPlusOp (L - L') := by
  obtain ⟨s, hs, hx, a, ha, hLv⟩ := hL
  obtain ⟨a', ha', hL'v⟩ := (p.mem_linSet_iff hf hs hx L').1 hL'
  have e : L - L' = a - a' := by
    refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
    simp only [sub_apply, Submodule.coe_sub, hLv, hL'v]
    abel
  rw [e, sub_eq_add_neg, ← neg_one_smul ℝ a']
  exact ha.add (ha'.smul (-1))

/-- **A member of `Lin(f, x)` is Fredholm, and its index is an index of `(f, x)`**
(Definition 6.1, `IsIndexAt`): for `L = (f + s)'(x) + a`, `(f + s)'(x)` is Fredholm of the index of
the germ data of `f + s` (Theorem 3.15, `isLinOfIndex_of_conjugationData`) and `a` is compact. -/
theorem isFredholm_isIndexAt_of_mem_linSet (hf : B.IsScFredholmSection f)
    {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) :
    L.IsFredholm ∧ B.IsIndexAt f x (fredholmIndex L) := by
  obtain ⟨s, hs, hx, a, ha, hLv⟩ := hL
  have hF := theorem_3_15 hf hs
  have hxs := hF.mem_smoothSet_of_isZeroAt hx
  obtain ⟨-, c, hc, hxV, hφ0, h0U, g, t₀, hfill, ht₀, ht₀0, hconj⟩ := hF.germ x hxs
  obtain ⟨dc⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  have hlin := StrongBundle.isLinOfIndex_of_conjugationData hF.isScSmooth hx hc hxV hφ0 h0U
    hfill ht₀ ht₀0 dc
  have hg := hf.isScSmooth.sectionAdd hs
  let L₁ : ↥p.T →L[ℝ] ↥p.K :=
    (linAt p.c.U p.c.R (p.c.principal (sectionAdd P f s)) p.z).codRestrict p.K
      fun v => p.scDeriv_mem_K hg hx v
  obtain ⟨hL₁F, hL₁i⟩ := hlin p.c p.isChart p.mem_source p.z p.toBase_z p.mem_U L₁ fun _ => rfl
  have e : L = L₁ + a := by
    refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
    rw [hLv]
    rfl
  have hac := ha.isCompactOperator
  rw [e]
  refine ⟨isFredholm_add_isCompactOperator hL₁F hac, ?_⟩
  rw [fredholmIndex_add_isCompactOperator hL₁F hac, hL₁i]
  exact ⟨s, hs, hx, hlin⟩

/-- **The members of `Lin(f, x)` are Fredholm operators of one index** (`ind(f, x)`). -/
theorem exists_index_linSet (hf : B.IsScFredholmSection f) :
    ∃ i : ℤ, ∀ L ∈ p.linSet f, L.IsFredholm ∧ fredholmIndex L = i := by
  rcases (p.linSet f).eq_empty_or_nonempty with h | ⟨L₀, hL₀⟩
  · exact ⟨0, fun L hL => by rw [h] at hL; exact absurd hL (notMem_empty L)⟩
  · refine ⟨fredholmIndex L₀, fun L hL => ?_⟩
    obtain ⟨hF, hi⟩ := p.isFredholm_isIndexAt_of_mem_linSet hf hL
    exact ⟨hF, hi.unique hf (p.isFredholm_isIndexAt_of_mem_linSet hf hL₀).2⟩

/-- The index of the members of `Lin(f, x)` is the index of Definition 6.1 (`IsIndexAt`). -/
theorem fredholmIndex_of_mem_linSet (hf : B.IsScFredholmSection f) {i : ℤ}
    (hi : B.IsIndexAt f x i) {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) :
    L.IsFredholm ∧ fredholmIndex L = i := by
  obtain ⟨hF, hi'⟩ := p.isFredholm_isIndexAt_of_mem_linSet hf hL
  exact ⟨hF, hi'.unique hf hi⟩

/-- **`Lin(f, x)` is convex** (p. 219). -/
theorem convex_linSet (hf : B.IsScFredholmSection f) : Convex ℝ (p.linSet f) := by
  intro L₁ hL₁ L₂ hL₂ t₁ t₂ _ _ ht
  obtain ⟨s, hs, hx, a₁, ha₁, hL₁v⟩ := hL₁
  obtain ⟨a₂, ha₂, hL₂v⟩ := (p.mem_linSet_iff hf hs hx L₂).1 hL₂
  refine (p.mem_linSet_iff hf hs hx _).2
    ⟨t₁ • a₁ + t₂ • a₂, (ha₁.smul t₁).add (ha₂.smul t₂), fun v => ?_⟩
  obtain rfl : t₂ = 1 - t₁ := by linarith
  simp only [add_apply, smul_apply, Submodule.coe_add, Submodule.coe_smul, hL₁v, hL₂v]
  module

end ChartPoint

end Polyfold
