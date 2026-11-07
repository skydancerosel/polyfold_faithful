import Polyfold.Chapter7.OrbitTopology

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II, §7.3–7.4:
**Proposition 7.11** (index lifting, p. 247, proof p. 248), **Definition 7.15** (p. 249), the
sentence before **Remark 7.1** and Remark 7.1 (p. 249), and **Proposition 7.12** (paracompactness
under lifts, p. 249, proof pp. 249–250).  There is no 2014 preprint of Part II; numbers and pages
are the 2017 text's.  Part I items carry their 2017 numbers, with the preprint number of the Lean
name in brackets: Theorem 2.2 [2.16] (`MPolyfold.paracompactSpace_level`), Definition 2.19 [2.37]
(`MPolyfold.IsTame`), Proposition 2.15 [2.46] (the fibred product), Lemma 2.7 [2.56] (Michael).
Definition 7.15 itself (`HasParacompactOrbitSpace`) is in `EpGroupoid.lean`.

# Index lifting and paracompact orbit spaces

## The text, paraphrased

(p. 247) One can raise the index of an M-polyfold `X` to obtain `X¹`.  (Proposition 7.11) If
`X = (X, 𝐗)` is an ep-groupoid, so is `X¹ = (X¹, 𝐗¹)`; if `X` is tame, so is `X¹`.  *Proof*:
`X¹` satisfies (1), (2) and (4) of Definition 7.3 trivially.  For (3) take `x ∈ X₁` and `V(x)` with
`t : s⁻¹(cl_X V(x)) → X` proper (7.4); `W(x) = V(x) ∩ X₁` is open in `X₁` and `cl_{X₁} W(x) ⊆
cl_X V(x)`.  For `t : s⁻¹(cl_{X₁} W(x)) → X₁` (7.5) take `(φ_k)` with `(t(φ_k))` in a compact
subset of `X₁`; after a subsequence (a) `φ_k → φ` in `𝐗₀`, (b) `s(φ_k) → s(φ)`, `t(φ_k) → t(φ)` in
`X₀`, (c) `t(φ_k) → t(φ)` in `X₁`; since `t` is a local sc-diffeomorphism, (d) `φ ∈ 𝐗₁`.  With
`t : U(φ) → U(t(φ))` an sc-diffeomorphism, `φ_k = (t|U(φ))⁻¹(t(φ_k))` for large `k`, and since
`(t|U(φ))⁻¹` is sc⁰, `φ_k → φ` in `𝐗¹`.  The tameness of `X¹` is trivial.  (§7.4, p. 249)
(Definition 7.15) An ep-groupoid with paracompact orbit space satisfies in addition (5) `|X|` is
paracompact (not required to be Hausdorff).  It is not known whether (5) follows from (1)–(4); if
`X` has a second countable topology, (1)–(4) imply (5).  (Remark 7.1) In [38] the M-polyfolds were
second countable; (5) is the better requirement.  (Proposition 7.12) If `X` has paracompact orbit
space, so has `X¹`.  *Proof*: by Lemma 2.7 a regular Hausdorff space is paracompact iff every open
cover has a locally finite closed refinement.  The cover `(|U(x)|)` of `|X|`, `U(x)` with the
natural `G_x`-action, has a locally finite closed refinement `(A_x)`, `A_x ⊆ |U(x)|`; `A_{x,1} =
A_x ∩ |X₁|` is the preimage of `A_x` under `|X₁| → |X|`, so `(A_{x,1})` is a locally finite closed
cover of `|X₁|`.  `G_x` acts on `U(x)₁`; as in Lemma 7.4 a `G_x`-invariant metric on `U(x)₁`
passes to `|U(x)|₁ = |U(x)₁|`, so `A_{x,1}` is metrizable, hence paracompact, and `|X₁|` is a
locally finite union of closed paracompact sets.

## What is formalized (namespace `Polyfold.EpGroupoid`)

* **The structure maps on level `1`**: `liftSrc`, `liftTgt`, `liftUnit`, `liftInv` (Part I's
  `levelOneMap`; sc-smooth maps preserve the levels), `liftComp` (with `comp_mem_levelSet`:
  composites of composable pairs stay on the level), the groupoid `liftGroupoidStr`, and
  `levelVal_liftSrc`, …, `levelVal_liftComp`.
* **Proposition 7.11**: (1) `isLocalScDiffeo_liftSrc`, `isLocalScDiffeo_liftTgt`; (2)
  `isScSmoothMap_liftUnit`, `isScSmoothMap_liftInv`; (3) `exists_isProperMap_lift` (the text's
  sequence argument); (4) `isScSmoothCompSheet_lift` (sheet form) and `isScSmoothComp_lift`; the
  ep-groupoid `liftOne : EpGroupoid (X.PObj.Level 1) (X.PMor.Level 1)` (`PObj = X.PObj.shift`,
  `PMor = X.PMor.shift`, paracompactness by the instance `MPolyfold.paracompactSpace_level`), with
  `liftOne_src_val`, …, `liftOne_comp_val`; **tameness**: `MPolyfold.IsTame.levelOne` (the index
  lift of a tame M-polyfold is tame) and `isTame_liftOne`; `proposition_7_11` (all of it).
* **The orbit spaces**: the inclusion functor `liftIncl : X¹ → X` and the natural map
  `orbitIncl : |X¹| → |X|` (`orbitIncl_π`), `continuous_orbitIncl`, `orbitIncl_injective`
  (`ml(s φ) = ml(t φ)`), `range_orbitIncl` (`|X₁| = π(X₁)`, p. 228) and `preimage_orbitIncl_image`
  (the preimage of `π(U)` is `π₁(U ∩ X₁)`).
* **The natural action on level `1`** (Proposition 7.12's proof): `NaturalRep.liftU` (`U(x)₁`),
  the action `NaturalRep.liftMulAction` (`levelVal_liftSmul`), `continuous_liftSmul`,
  `liftOne_π_eq_iff` (the fibres of `π₁` on `U(x)₁` are the `G_x`-orbits),
  `liftOrbitQuotientMap` (`G_x\U(x)₁ → |X¹|`), `isOpenEmbedding_liftOrbitQuotientMap`,
  `range_liftOrbitQuotientMap` (`|U(x)|₁ = |U(x)₁|`) and `metrizableSpace_preimage_orbitIncl`.
* **Definition 7.15**: `hasParacompactOrbitSpace_iff_metrizableSpace` (Theorem 7.2),
  `hasParacompactOrbitSpace_of_secondCountableTopology` (second countable `|X|`, Corollary 7.1).
* **The sentence before Remark 7.1**: `remark_7_1` (second countable object space ⇒ (5)).
* **Proposition 7.12**: `metrizableSpace_liftOne_orbitSpace` (`|X¹|` is even metrizable) and
  `proposition_7_12`.

## Reading

* **The structure maps of `X¹`.**  The text restricts `s, t, u, ι, m` to level `1` without
  comment.  That `s, t, u, ι` map level `1` to level `1` is Part I's `mapsTo_levelSet` (sc-smooth
  maps preserve the levels); that `m(φ, ψ)` is on level `1` for composable `φ, ψ ∈ 𝐗₁` uses
  `ml(t(φ ∘ ψ)) = ml(t φ) = ml(φ)` (pp. 227–228; `comp_mem_levelSet`).  `liftComp` of a
  non-composable pair is a junk value, as in `GroupoidStr`.
* **"(1), (2) and (4) trivially"** (PLAN II.6, 7).  (1) is the level-`1` lift of a local
  sc-diffeomorphism (`IsLocalScDiffeo.levelOne`, `LocalDiffeo.lean`); (2) is Part I's
  `IsScSmoothMap.levelOne` (Proposition 1.17 in charts).  For (4) the text's "trivially", as we read
  it, uses `(𝐗 ₛ×ₜ 𝐗)¹ = 𝐗¹ ₛ×ₜ 𝐗¹` as M-polyfolds (the fibred product of Proposition 2.15 [2.46]
  for `X¹` against the level of the one for `X`).  This identification is not proved here; it is
  avoided through the sheet form of (4) (`isScSmoothComp_iff_sheet`, `EpGroupoid.lean`): a sheet
  `σ₁` of `s₁` agrees near each point with the level-`1` lift of a sheet `σ` of `s` (both invert
  `s` near that point), and `ψ ↦ m(σ(t ψ), ψ)` lifts by `IsScSmoothOn.levelOne`.
* **(3)** follows the text.  "`(t(φ_k))` belongs to a compact subset of `X₁`" is replaced by
  "`t(φ_k)` converges in `X₁`" (the sequential criterion `isProperMap_domRestrict_iff_of_isClosed`
  of `ProperMaps.lean`; `X¹` and `𝐗¹` are metrizable, Theorem 2.2 [2.16]); `cl_{X₁} W(x) ⊆
  cl_X V(x)` is the continuity of `X₁ → X`; (b) is not needed; "(t|U(φ))⁻¹ is sc⁰" is used as the
  continuity on level `1` of its level-`1` lift.  The displayed map (7.5) has an unbalanced
  parenthesis, "`s⁻¹(cl_{X₁}(W(x)) → X₁`" (possible misprint).
* **Tameness** ("trivial").  Definition 7.6 asks the object M-polyfold `X¹` to be tame
  (Definition 2.19 [2.37]: an equivalent atlas of tame retracts exists; PLAN II.5, 1).  As we read
  it, this needs that the index lift of a tame retraction is tame, which Part I left open
  (`Findings.md`, Chapter 5, item 145; `LocalDiffeo.lean`).  It is proved here
  (`MPolyfold.IsTame.levelOne`): for a tame `r` with presentation `T : E ≅ ℝⁿ ⊕ W` of `C`, the
  presentation `T¹ : E¹ ≅ ℝⁿ ⊕ W¹` of `C¹` has the same `ℝⁿ`-coordinates, so `d_{C¹} = d_C` on
  `C¹` and `E_x` for `T¹` is `E_x ∩ E₁`; `Dr¹(x) = Dr(x)|E₁` (Proposition 1.17), whose range is
  `T_xO ∩ E₁` since `Dr(x)` is a projection; and an sc-complement `A` of `T_xO` gives the
  sc-complement `A ∩ E₁` of `T_xO¹` (the sc-splitting shifts).  Tameness for `T¹` is tameness
  (Part I's presentation independence, `ScRetraction.IsTameWith.isTame`), and the level charts of
  tame charts form the tame atlas of `X¹`.
* **`|X¹| → |X|`.**  The text writes `|X₁|` for the orbit space of `X¹` and treats it as the
  subset `|X₁| ⊆ |X|` (p. 250, "`A_x ∩ |X₁|`"), with the topology of `|X¹|`.  Here `|X¹|` keeps its
  own quotient topology and `orbitIncl` is the continuous injection onto `|X₁| = π(X₁)`; the
  injectivity is `ml(s φ) = ml(t φ)`: a morphism between points of `X₁` lies in `𝐗₁`.
* **Definition 7.15** is `ParacompactSpace X.OrbitSpace` (Mathlib's notion without Hausdorff, as
  the text stipulates).
* **"In case `X` has a second countable topology"** (the sentence before Remark 7.1, to which the
  remark refers) is read with `X` the object space: `|X|` is then second countable (`π` is open and
  surjective, Proposition 7.1), hence metrizable by Corollary 7.1 ("we have already seen"), hence
  paracompact (Stone).  Remark 7.1 itself (on the requirement of [38]) has no formal content.
  "It is presently not known whether (5) is a consequence of (1)–(4)" is not formalized.
* **Proposition 7.12, the route** (PLAN II.6, 7).  The text's route (Lemma 2.7, a locally finite
  closed refinement `(A_x)`, Michael's union of closed paracompact sets) is replaced by Smirnov's
  theorem pulled back along `|X¹| → |X|` (Part I's `metrizableSpace_of_pullback`): `|X|` is
  paracompact and Hausdorff, and every point has the open neighbourhood `|U(x)| = π(U(x))` whose
  preimage `|U(x)|₁` is metrizable, so `|X¹|` is metrizable, hence paracompact.  The step shared
  with the text is the metrizability of `|U(x)|₁ = |U(x)₁|`: `G_x` acts on `U(x)₁ = U(x) ∩ X₁` by
  the level-`1` lifts of the `Φ(g)` (homeomorphisms of `U(x)₁`), `G_x\U(x)₁` is metrizable by the
  text's metric `ρ̂` (the argument of Lemma 7.4, repeated here for any finite group acting by
  homeomorphisms on a metrizable space, since `OrbitTopology.lean`'s version is private), and
  `G_x\U(x)₁ → |X¹|` is an open embedding onto the preimage (the argument of Proposition 7.6 on
  level `1`).  "`U(x)₁` has the natural `G_x`-action" is read as the restricted action only:
  `U(x)₁` need not be connected in `X¹`, so it is not a `NaturalRep` of `X¹`.  `theorem_7_2`'s
  regularity of `|X¹|` is not needed on this route.
* **Hypotheses.**  No hypothesis "for all …" is added.  The hypotheses `X.IsTame`,
  `X.HasParacompactOrbitSpace`, `SecondCountableTopology Obj` and `SecondCountableTopology
  X.OrbitSpace` are satisfiable: the trivial ep-groupoid of `ℝⁿ` is tame (`isTame_trivial_rn`) and
  has paracompact orbit space (`hasParacompactOrbitSpace_trivial`), homeomorphic to the second
  countable `ℝⁿ` (`trivialOrbitHomeomorph`).
-/

open Set Function Topology Filter TopologicalSpace

noncomputable section

namespace Polyfold

universe u

/-! ### Tameness on level `1` -/

section TameShift

variable {E : ScBanach}

/-- `(A ∩ E₁)_m = A ∩ E_{m+1}`: the filtration of `A ∩ E₁` in `E¹`. -/
private theorem levelSub_shift_levelSub (A : Submodule ℝ (E 0)) (m : ℕ) :
    E.shift.levelSub (E.levelSub A 1) m = E.levelSub A (m + 1) := by
  ext v
  change E.toBase 1 (E.shift.toBase m v) ∈ A ↔ E.toBase (m + 1) v ∈ A
  rw [E.shift_toBase m v]

/-- An sc-subspace `A ⊆ E` gives the sc-subspace `A ∩ E₁ ⊆ E¹`. -/
private theorem isScSubspace_levelSub_one {A : Submodule ℝ (E 0)} (h : E.IsScSubspace A) :
    E.shift.IsScSubspace (E.levelSub A 1) := by
  refine ⟨E.isClosed_levelSub h.1 1, fun m => ?_⟩
  rw [levelSub_shift_levelSub, E.shift_smoothLvl]
  exact h.2 (m + 1)

/-- **The sc-splitting shifts**: `E = F ⊕ G` gives `E¹ = F¹ ⊕ G¹`. -/
private theorem isScSplitting_levelSub_one {F G : Submodule ℝ (E 0)} (h : E.IsScSplitting F G) :
    E.shift.IsScSplitting (E.levelSub F 1) (E.levelSub G 1) :=
  ⟨isScSubspace_levelSub_one h.1, isScSubspace_levelSub_one h.2.1, fun m => by
    rw [levelSub_shift_levelSub, levelSub_shift_levelSub]
    exact h.2.2 (m + 1)⟩

variable {n : ℕ} {W : ScBanach}

/-- The shifted presentation `T¹ : E¹ ≅ ℝⁿ ⊕ W¹` of `C¹` (as in `IsPartialQuadrant.shift`). -/
private def shiftPres (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) :
    ScIso E.shift ((ScBanach.const (Fin n → ℝ)).prod W.shift) :=
  T.shift

/-- The `ℝⁿ`-coordinates of the shifted presentation `T¹` are those of `T`. -/
private theorem shift_apply_fst (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (w : E 1) :
    (shiftPres T 0 w).1 = (T 0 (E.toBase 1 w)).1 := by
  rw [← T.toBase_comm, ScBanach.prod_toBase, ScBanach.const_toBase]
  rfl

private theorem shift_presentation {C : Set (E 0)}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : C = T 0 ⁻¹' quadrant n W 0) :
    E.lvlSet C 1 = shiftPres T 0 ⁻¹' quadrant n W.shift 0 := by
  rw [hT, IsPartialQuadrant.lvlSet_eq T 1]
  rfl

/-- `d_{C¹}(y) = d_C(y)` for `y ∈ C¹`. -/
private theorem degIndex_shift {C : Set (E 0)}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : C = T 0 ⁻¹' quadrant n W 0)
    {y : E 1} (hy : y ∈ E.lvlSet C 1) :
    degIndex E.shift (E.lvlSet C 1) y = degIndex E C (E.toBase 1 y) := by
  rw [degIndex_eq (shiftPres T) (shift_presentation hT) hy,
    degIndex_eq T hT (x := E.toBase 1 y) hy, degIndexWith,
    degIndexWith, quadrantDeg, quadrantDeg, shift_apply_fst]

/-- `E_x` for `T¹` at `y ∈ E₁` is `E_y ∩ E₁` for `T`. -/
private theorem mem_minimalSubspaceWith_shift
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) {y v : E 1} :
    v ∈ minimalSubspaceWith (shiftPres T) y ↔
      E.toBase 1 v ∈ minimalSubspaceWith T (E.toBase 1 y) := by
  rw [mem_minimalSubspaceWith, mem_minimalSubspaceWith, shift_apply_fst, shift_apply_fst]

/-- **The level shift of a tame retraction is tame** (with respect to `T¹`): (1) `d_{C¹} = d_C`
on `C¹`; (2) `A ∩ E₁` is an sc-complement of `T_xO¹ = T_xO ∩ E₁` inside `E_x ∩ E₁`. -/
private theorem isTameWith_shift {C : Set (E 0)} {R : ScRetraction E C}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : C = T 0 ⁻¹' quadrant n W 0)
    (h : R.IsTameWith T) : R.shift.IsTameWith (shiftPres T) := by
  refine ⟨fun x hx => ?_, fun x hx hs => ?_⟩
  · have hxC : x ∈ E.lvlSet C 1 := R.shift.U_subset_C hx
    have hrxC : R.shift x ∈ E.lvlSet C 1 := R.shift.U_subset_C (R.shift.mapsTo hx)
    rw [degIndex_shift hT hxC, degIndex_shift hT hrxC, ScRetraction.shift_apply,
      R.isSc1.isSc0.toBase_levelMap hx]
    exact h.degIndex_apply _ hx
  · have hy2 : E.toBase 1 (E.shift.toBase 1 x) = E.toBase 2 x := (E.shift_toBase 1 x).symm
    have hyO : E.shift.toBase 1 x ∈ E.lvlSet R.retract 1 := by
      have : E.shift.toBase 1 x ∈ R.shift.retract := hx
      rwa [R.shift_retract] at this
    have hys : E.shift.toBase 1 x ∈ E.smoothLvl 1 := by
      have : x ∈ E.smoothLvl 2 := by
        rw [← E.shift_smoothLvl 1]
        exact hs
      change E.toBase 1 (E.shift.toBase 1 x) ∈ E.smooth
      rw [hy2]
      exact this
    obtain ⟨A, hA, hAE⟩ := h.exists_complement _ hyO hys
    -- `Dr¹(x) = Dr(x)|E₁` (Proposition 1.17)
    have hD := R.isSc1.isSc1With_scDeriv
    have hxU : x ∈ E.shift.lvlSet R.shift.U 1 := R.shift.lvlSet_retract_subset 1 hx
    have heq : scDeriv R.shift.U R.shift x = levelDeriv (scDeriv R.U R) 1 x :=
      IsSc1.scDeriv_eqOn (hD.shift R.isScDomain) (R.isScDomain.shift.uniqueDiffWithinAt 1) hxU
    have hxU2 : x ∈ E.lvlSet R.U 2 := by
      change E.toBase 2 x ∈ R.U
      rw [← hy2]
      exact hxU
    have hbase : ∀ v : E 1, E.toBase 1 (scDeriv R.shift.U R.shift x v) =
        scDeriv R.U R (E.shift.toBase 1 x) (E.toBase 1 v) := fun v => by
      rw [heq]
      exact hD.toBase_levelDeriv hxU2 v
    -- `T_xO¹ = T_xO ∩ E₁`, since `Dr(x)` is a projection
    have hrange : LinearMap.range (scDeriv R.shift.U R.shift x : E 1 →ₗ[ℝ] E 1) =
        E.levelSub (LinearMap.range (scDeriv R.U R (E.shift.toBase 1 x) : E 0 →ₗ[ℝ] E 0))
          1 := by
      ext v
      rw [ScBanach.mem_levelSub, LinearMap.mem_range, LinearMap.mem_range]
      simp only [ContinuousLinearMap.coe_coe]
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨E.toBase 1 w, (hbase w).symm⟩
      · rintro ⟨w, hw⟩
        refine ⟨v, E.toBase_injective 1 ?_⟩
        rw [hbase, ← hw]
        exact congrArg (fun L : E 0 →L[ℝ] E 0 => L w) (R.scDeriv_comp_self hyO)
    refine ⟨E.levelSub A 1, ?_, fun v hv => (mem_minimalSubspaceWith_shift T).2 (hAE hv)⟩
    rw [hrange]
    exact isScSplitting_levelSub_one hA

/-- **The level shift of a tame retract is tame**: `(O¹, C¹, E¹)` is a tame retract if
`(O, C, E)` is (Definition 2.34, presentation independent by `ScRetraction.IsTameWith.isTame`). -/
private theorem isTameRetract_shift {C O : Set (E 0)} (h : IsTameRetract E C O) :
    IsTameRetract E.shift (E.lvlSet C 1) (E.lvlSet O 1) := by
  obtain ⟨R, rfl, hR⟩ := h
  obtain ⟨n, W, T, hT⟩ := R.relOpen.isPartialQuadrant
  exact ⟨R.shift, R.shift_retract,
    (isTameWith_shift hT (hR n W T hT)).isTame (shift_presentation hT)⟩

end TameShift

/-- **The index lift of a tame M-polyfold is tame** (Definition 2.19 [2.37] for `X¹`): the level
charts `(V₁, φ, (O¹, C¹, E¹))` of tame charts are tame. -/
theorem MPolyfold.IsTame.levelOne {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] {P : MPolyfold Z} (hP : P.IsTame) : P.shift.IsTame :=
  MPolyfold.isTame_of_forall_exists_chart P.shift fun x => by
    obtain ⟨φ, hφ, hx, ht⟩ := MPolyfold.IsTame.exists_chart P hP (P.levelVal 1 x)
    exact ⟨MPolyfold.levelChart hφ x, P.shift_isChart hφ x, hx, isTameRetract_shift ht⟩

/-! ### The text's metrics `ρ` and `ρ̂` (Lemma 7.4), for a finite group

Repeated from `OrbitTopology.lean`, where they are private; used for `G_x\U(x)₁`. -/

section QuotientMetric

variable (G : Type*) {U : Type*} [Group G] [Fintype G] [MulAction G U] [PseudoMetricSpace U]

/-- `ρ(y, z) = max_g d(g y, g z)` (Lemma 7.4). -/
private def lvMaxDist (y z : U) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun g : G => dist (g • y) (g • z)

variable {G}

private theorem dist_smul_le_lvMaxDist (g : G) (y z : U) :
    dist (g • y) (g • z) ≤ lvMaxDist G y z :=
  Finset.le_sup' (fun g : G => dist (g • y) (g • z)) (Finset.mem_univ g)

private theorem dist_le_lvMaxDist (y z : U) : dist y z ≤ lvMaxDist G y z := by
  simpa only [one_smul] using dist_smul_le_lvMaxDist (1 : G) y z

private theorem lvMaxDist_lt_iff {y z : U} {ε : ℝ} :
    lvMaxDist G y z < ε ↔ ∀ g : G, dist (g • y) (g • z) < ε := by
  simp only [lvMaxDist, Finset.sup'_lt_iff, Finset.mem_univ, forall_const]

private theorem lvMaxDist_self (y : U) : lvMaxDist G y y = 0 :=
  le_antisymm (Finset.sup'_le _ _ fun _ _ => (dist_self _).le)
    (dist_nonneg.trans (dist_le_lvMaxDist y y))

private theorem lvMaxDist_comm (y z : U) : lvMaxDist G y z = lvMaxDist G z y := by
  simp only [lvMaxDist, dist_comm]

private theorem lvMaxDist_triangle (y z w : U) :
    lvMaxDist G y w ≤ lvMaxDist G y z + lvMaxDist G z w :=
  Finset.sup'_le _ _ fun g _ => (dist_triangle _ (g • z) _).trans
    (add_le_add (dist_smul_le_lvMaxDist g y z) (dist_smul_le_lvMaxDist g z w))

/-- **`ρ` is invariant** (Lemma 7.4): `ρ(h y, h z) = ρ(y, z)`. -/
private theorem lvMaxDist_smul (h : G) (y z : U) :
    lvMaxDist G (h • y) (h • z) = lvMaxDist G y z := by
  refine le_antisymm (Finset.sup'_le _ _ fun g _ => ?_) (Finset.sup'_le _ _ fun g _ => ?_)
  · rw [smul_smul, smul_smul]
    exact dist_smul_le_lvMaxDist (g * h) y z
  · have := dist_smul_le_lvMaxDist (g * h⁻¹) (h • y) (h • z)
    rwa [smul_smul, smul_smul, inv_mul_cancel_right] at this

variable (G) in
/-- `min_h ρ(y, h z)`, the quotient distance before passing to the quotient. -/
private def lvQuotDistAux (y z : U) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun h : G => lvMaxDist G y (h • z)

private theorem lvQuotDistAux_le (h : G) (y z : U) : lvQuotDistAux G y z ≤ lvMaxDist G y (h • z) :=
  Finset.inf'_le (fun h : G => lvMaxDist G y (h • z)) (Finset.mem_univ h)

private theorem exists_lvQuotDistAux_eq (y z : U) :
    ∃ h : G, lvQuotDistAux G y z = lvMaxDist G y (h • z) := by
  obtain ⟨h, -, hh⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := G))
    fun h : G => lvMaxDist G y (h • z)
  exact ⟨h, hh⟩

private theorem lvQuotDistAux_smul_right (k : G) (y z : U) :
    lvQuotDistAux G y (k • z) = lvQuotDistAux G y z := by
  refine le_antisymm (Finset.le_inf' _ _ fun h _ => ?_) (Finset.le_inf' _ _ fun h _ => ?_)
  · have := lvQuotDistAux_le (h * k⁻¹) y (k • z)
    rwa [smul_smul, inv_mul_cancel_right] at this
  · rw [smul_smul]
    exact lvQuotDistAux_le (h * k) y z

private theorem lvQuotDistAux_smul_left (k : G) (y z : U) :
    lvQuotDistAux G (k • y) z = lvQuotDistAux G y z := by
  refine le_antisymm (Finset.le_inf' _ _ fun h _ => ?_) (Finset.le_inf' _ _ fun h _ => ?_)
  · rw [← lvMaxDist_smul k, smul_smul]
    exact lvQuotDistAux_le (k * h) (k • y) z
  · have := lvQuotDistAux_le (k⁻¹ * h) y z
    rwa [← lvMaxDist_smul k, smul_smul, mul_inv_cancel_left] at this

private theorem lvQuotDistAux_comm_le (y z : U) : lvQuotDistAux G y z ≤ lvQuotDistAux G z y := by
  refine Finset.le_inf' _ _ fun h _ => ?_
  have := lvQuotDistAux_le h⁻¹ y z
  rwa [← lvMaxDist_smul h, smul_inv_smul, lvMaxDist_comm] at this

private theorem lvQuotDistAux_comm (y z : U) : lvQuotDistAux G y z = lvQuotDistAux G z y :=
  le_antisymm (lvQuotDistAux_comm_le y z) (lvQuotDistAux_comm_le z y)

private theorem lvQuotDistAux_triangle (y z w : U) :
    lvQuotDistAux G y w ≤ lvQuotDistAux G y z + lvQuotDistAux G z w := by
  obtain ⟨h, hh⟩ := exists_lvQuotDistAux_eq (G := G) y z
  obtain ⟨k, hk⟩ := exists_lvQuotDistAux_eq (G := G) z w
  rw [hh, hk, ← lvMaxDist_smul h z, smul_smul]
  exact (lvQuotDistAux_le (h * k) y w).trans (lvMaxDist_triangle _ _ _)

variable (G U) in
/-- **The quotient distance** `ρ̂([y], [z]) = min_{g, h} ρ(g y, h z) = min_h ρ(y, h z)` on `G\U`
(Lemma 7.4). -/
private def lvQuotDist :
    MulAction.orbitRel.Quotient G U → MulAction.orbitRel.Quotient G U → ℝ :=
  Quotient.lift₂ (lvQuotDistAux G) <| by
    rintro a₁ b₁ a₂ b₂ ⟨g, rfl⟩ ⟨h, rfl⟩
    exact (lvQuotDistAux_smul_left g _ _).trans (lvQuotDistAux_smul_right h _ _)

private theorem lvQuotDist_mk (y z : U) :
    lvQuotDist G U (Quotient.mk _ y) (Quotient.mk _ z) = lvQuotDistAux G y z := rfl

end QuotientMetric

/-- **The quotient of a metrizable space by a finite group of homeomorphisms is metrizable**, by
the text's metric `ρ̂` (the argument of Lemma 7.4). -/
private theorem metrizableSpace_orbitRel_quotient_of_finite {G U : Type*} [Group G] [Finite G]
    [MulAction G U] [TopologicalSpace U] [MetrizableSpace U]
    (hc : ∀ g : G, Continuous fun y : U => g • y) :
    MetrizableSpace (MulAction.orbitRel.Quotient G U) := by
  let _ := Fintype.ofFinite G
  let _ := metrizableSpaceMetric U
  have hmk : ∀ q : MulAction.orbitRel.Quotient G U, ∃ y : U, Quotient.mk _ y = q :=
    Quotient.exists_rep
  -- `ρ̂` defines the quotient topology.
  have hH : ∀ s : Set (MulAction.orbitRel.Quotient G U), IsOpen s ↔
      ∀ q ∈ s, ∃ ε > 0, ∀ q', lvQuotDist G U q q' < ε → q' ∈ s := by
    intro s
    rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
    constructor
    · intro hs q hq
      obtain ⟨y, rfl⟩ := hmk q
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hs y hq
      refine ⟨ε, hε, fun q' hq' => ?_⟩
      obtain ⟨z, rfl⟩ := hmk q'
      obtain ⟨h, hh⟩ := exists_lvQuotDistAux_eq (G := G) y z
      rw [lvQuotDist_mk, hh] at hq'
      have hmem : h • z ∈ Quotient.mk (MulAction.orbitRel G U) ⁻¹' s :=
        hball (lt_of_le_of_lt (by rw [dist_comm]; exact dist_le_lvMaxDist _ _) hq')
      have hq : Quotient.mk (MulAction.orbitRel G U) (h • z) = Quotient.mk _ z :=
        Quotient.sound ⟨h, rfl⟩
      rwa [mem_preimage, hq] at hmem
    · intro hs
      refine isOpen_iff_mem_nhds.2 fun y hy => ?_
      obtain ⟨ε, hε, hball⟩ := hs _ hy
      have hN : (⋂ g : G, (fun z => g • z) ⁻¹' Metric.ball (g • y) ε) ∈ 𝓝 y :=
        (isOpen_iInter_of_finite fun g => Metric.isOpen_ball.preimage (hc g)).mem_nhds
          (mem_iInter.2 fun g => Metric.mem_ball_self hε)
      refine mem_of_superset hN fun z hz => hball _ ?_
      have hz' : lvMaxDist G y z < ε := lvMaxDist_lt_iff.2 fun g => by
        rw [dist_comm]
        exact mem_iInter.1 hz g
      have := lvQuotDistAux_le (1 : G) y z
      rw [one_smul] at this
      exact lt_of_le_of_lt this hz'
  let _ : MetricSpace (MulAction.orbitRel.Quotient G U) :=
    MetricSpace.ofDistTopology (lvQuotDist G U) (fun q => ?_) (fun q q' => ?_)
      (fun q q' q'' => ?_) hH fun q q' hqq' => ?_
  · infer_instance
  · obtain ⟨y, rfl⟩ := hmk q
    refine le_antisymm ?_ ?_
    · have := lvQuotDistAux_le (1 : G) y y
      rwa [one_smul, lvMaxDist_self] at this
    · obtain ⟨h, hh⟩ := exists_lvQuotDistAux_eq (G := G) y y
      rw [lvQuotDist_mk, hh]
      exact dist_nonneg.trans (dist_le_lvMaxDist _ _)
  · obtain ⟨y, rfl⟩ := hmk q
    obtain ⟨z, rfl⟩ := hmk q'
    exact lvQuotDistAux_comm y z
  · obtain ⟨y, rfl⟩ := hmk q
    obtain ⟨z, rfl⟩ := hmk q'
    obtain ⟨w, rfl⟩ := hmk q''
    exact lvQuotDistAux_triangle y z w
  · obtain ⟨y, rfl⟩ := hmk q
    obtain ⟨z, rfl⟩ := hmk q'
    obtain ⟨h, hh⟩ := exists_lvQuotDistAux_eq (G := G) y z
    rw [lvQuotDist_mk, hh] at hqq'
    have h0 : dist y (h • z) = 0 :=
      le_antisymm (hqq' ▸ dist_le_lvMaxDist _ _) dist_nonneg
    rw [dist_eq_zero] at h0
    rw [h0]
    exact Quotient.sound ⟨h, rfl⟩

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### The structure maps on level `1` -/

/-- `s₁ : 𝐗₁ → X₁`. -/
def liftSrc : X.PMor.Level 1 → X.PObj.Level 1 :=
  MPolyfold.levelOneMap X.PMor X.PObj X.src (X.isScSmoothMap_src.mapsTo_levelSet 1)

/-- `t₁ : 𝐗₁ → X₁`. -/
def liftTgt : X.PMor.Level 1 → X.PObj.Level 1 :=
  MPolyfold.levelOneMap X.PMor X.PObj X.tgt (X.isScSmoothMap_tgt.mapsTo_levelSet 1)

/-- `u₁ : X₁ → 𝐗₁`. -/
def liftUnit : X.PObj.Level 1 → X.PMor.Level 1 :=
  MPolyfold.levelOneMap X.PObj X.PMor X.unit (X.isScSmoothMap_unit.mapsTo_levelSet 1)

/-- `ι₁ : 𝐗₁ → 𝐗₁`. -/
def liftInv : X.PMor.Level 1 → X.PMor.Level 1 :=
  MPolyfold.levelOneMap X.PMor X.PMor X.inv (X.isScSmoothMap_inv.mapsTo_levelSet 1)

/-- The composite of composable morphisms of level `m` is of level `m` (`ml(t(φ ∘ ψ)) = ml(t φ) =
ml(φ)`, pp. 227–228). -/
theorem comp_mem_levelSet {φ ψ : Mor} {m : ℕ} (hφ : φ ∈ X.PMor.levelSet m)
    (h : X.src φ = X.tgt ψ) : X.comp φ ψ ∈ X.PMor.levelSet m := by
  rw [← X.mem_levelSet_tgt_iff, X.tgt_comp _ _ h, X.mem_levelSet_tgt_iff]
  exact hφ

open scoped Classical in
/-- `m₁`: the composite on level `1` (a junk value `φ` for pairs whose composite is not on level
`1`, which are never composable). -/
def liftComp (φ ψ : X.PMor.Level 1) : X.PMor.Level 1 :=
  if h : X.comp (X.PMor.levelVal 1 φ) (X.PMor.levelVal 1 ψ) ∈ X.PMor.levelSet 1 then
    X.PMor.levelMk 1 _ h
  else φ

@[simp] theorem levelVal_liftSrc (φ : X.PMor.Level 1) :
    X.PObj.levelVal 1 (X.liftSrc φ) = X.src (X.PMor.levelVal 1 φ) := rfl

@[simp] theorem levelVal_liftTgt (φ : X.PMor.Level 1) :
    X.PObj.levelVal 1 (X.liftTgt φ) = X.tgt (X.PMor.levelVal 1 φ) := rfl

@[simp] theorem levelVal_liftUnit (x : X.PObj.Level 1) :
    X.PMor.levelVal 1 (X.liftUnit x) = X.unit (X.PObj.levelVal 1 x) := rfl

@[simp] theorem levelVal_liftInv (φ : X.PMor.Level 1) :
    X.PMor.levelVal 1 (X.liftInv φ) = X.inv (X.PMor.levelVal 1 φ) := rfl

theorem levelVal_liftComp {φ ψ : X.PMor.Level 1}
    (h : X.src (X.PMor.levelVal 1 φ) = X.tgt (X.PMor.levelVal 1 ψ)) :
    X.PMor.levelVal 1 (X.liftComp φ ψ) = X.comp (X.PMor.levelVal 1 φ) (X.PMor.levelVal 1 ψ) := by
  rw [liftComp, dif_pos (X.comp_mem_levelSet (MPolyfold.levelVal_mem φ) h)]
  rfl

private theorem src_eq_tgt_of_lift {φ ψ : X.PMor.Level 1} (h : X.liftSrc φ = X.liftTgt ψ) :
    X.src (X.PMor.levelVal 1 φ) = X.tgt (X.PMor.levelVal 1 ψ) :=
  congrArg (X.PObj.levelVal 1) h

/-- The groupoid `(X₁, 𝐗₁)`: the structure maps of `X` restricted to level `1`. -/
def liftGroupoidStr : GroupoidStr (X.PObj.Level 1) (X.PMor.Level 1) where
  src := X.liftSrc
  tgt := X.liftTgt
  comp := X.liftComp
  unit := X.liftUnit
  inv := X.liftInv
  src_comp φ ψ h := MPolyfold.level_ext <| by
    simp only [levelVal_liftSrc, X.levelVal_liftComp (X.src_eq_tgt_of_lift h)]
    exact X.src_comp _ _ (X.src_eq_tgt_of_lift h)
  tgt_comp φ ψ h := MPolyfold.level_ext <| by
    simp only [levelVal_liftTgt, X.levelVal_liftComp (X.src_eq_tgt_of_lift h)]
    exact X.tgt_comp _ _ (X.src_eq_tgt_of_lift h)
  comp_assoc φ ψ χ h h' := MPolyfold.level_ext <| by
    have h₁ := X.src_eq_tgt_of_lift h
    have h₂ := X.src_eq_tgt_of_lift h'
    have h₃ : X.src (X.PMor.levelVal 1 (X.liftComp φ ψ)) = X.tgt (X.PMor.levelVal 1 χ) := by
      rw [X.levelVal_liftComp h₁, X.src_comp _ _ h₁, h₂]
    have h₄ : X.src (X.PMor.levelVal 1 φ) = X.tgt (X.PMor.levelVal 1 (X.liftComp ψ χ)) := by
      rw [X.levelVal_liftComp h₂, X.tgt_comp _ _ h₂, h₁]
    rw [X.levelVal_liftComp h₃, X.levelVal_liftComp h₄, X.levelVal_liftComp h₁,
      X.levelVal_liftComp h₂, X.comp_assoc _ _ _ h₁ h₂]
  src_unit x := MPolyfold.level_ext (X.src_unit _)
  tgt_unit x := MPolyfold.level_ext (X.tgt_unit _)
  comp_unit φ := MPolyfold.level_ext <| by
    rw [X.levelVal_liftComp (by simp only [levelVal_liftUnit, levelVal_liftSrc, X.tgt_unit])]
    exact X.comp_unit _
  unit_comp φ := MPolyfold.level_ext <| by
    rw [X.levelVal_liftComp (by simp only [levelVal_liftUnit, levelVal_liftTgt, X.src_unit])]
    exact X.unit_comp _
  src_inv φ := MPolyfold.level_ext (X.src_inv _)
  tgt_inv φ := MPolyfold.level_ext (X.tgt_inv _)
  comp_inv φ := MPolyfold.level_ext <| by
    rw [X.levelVal_liftComp (by simp only [levelVal_liftInv, X.tgt_inv])]
    exact X.comp_inv _
  inv_comp φ := MPolyfold.level_ext <| by
    rw [X.levelVal_liftComp (by simp only [levelVal_liftInv, X.src_inv])]
    exact X.inv_comp _

/-! ### Conditions (1), (2) of Definition 7.3 for `X¹` -/

/-- **(1) on level `1`**: `s₁` is a local sc-diffeomorphism (`IsLocalScDiffeo.levelOne`). -/
theorem isLocalScDiffeo_liftSrc : X.PMor.shift.IsLocalScDiffeo X.PObj.shift X.liftSrc :=
  X.isLocalScDiffeo_src.levelOne

/-- **(1) on level `1`**: `t₁` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_liftTgt : X.PMor.shift.IsLocalScDiffeo X.PObj.shift X.liftTgt :=
  X.isLocalScDiffeo_tgt.levelOne

/-- **(2) on level `1`**: `u₁` is sc-smooth (Part I's `IsScSmoothMap.levelOne`). -/
theorem isScSmoothMap_liftUnit : X.PObj.shift.IsScSmoothMap X.PMor.shift X.liftUnit :=
  MPolyfold.IsScSmoothMap.levelOne X.isScSmoothMap_unit fun _ => rfl

/-- **(2) on level `1`**: `ι₁` is sc-smooth. -/
theorem isScSmoothMap_liftInv : X.PMor.shift.IsScSmoothMap X.PMor.shift X.liftInv :=
  MPolyfold.IsScSmoothMap.levelOne X.isScSmoothMap_inv fun _ => rfl

/-! ### Condition (3) -/

/-- **(3) on level `1`** (the text's sequence argument): `W(x) = V(x) ∩ X₁` for `V(x)` of (3) at
`x ∈ X₁`.  A subsequence of `(φ_k)` converges in `𝐗` (properness on level `0`, (a)), its limit
`φ` lies in `𝐗₁` ((d)), and `φ_k = (t|U(φ))⁻¹(t(φ_k)) → φ` in `𝐗¹`. -/
theorem exists_isProperMap_lift (x : X.PObj.Level 1) : ∃ V : Set (X.PObj.Level 1), IsOpen V ∧
    x ∈ V ∧ IsProperMap ((X.liftSrc ⁻¹' closure V).domRestrict X.liftTgt) := by
  obtain ⟨V, hVo, hxV, hV⟩ := X.exists_isProperMap (X.PObj.levelVal 1 x)
  have hc := MPolyfold.continuous_levelVal (P := X.PObj) 1
  refine ⟨X.PObj.levelVal 1 ⁻¹' V, hVo.preimage hc, hxV, ?_⟩
  rw [MPolyfold.isProperMap_domRestrict_iff_of_isClosed X.PMor.shift X.PObj.shift
    X.isLocalScDiffeo_liftSrc.continuous X.isLocalScDiffeo_liftTgt.continuous isClosed_closure]
  intro φ y hφ hy
  have hφ' : ∀ n, X.src (X.PMor.levelVal 1 (φ n)) ∈ closure V := fun n =>
    hc.closure_preimage_subset V (hφ n)
  have hy' : Tendsto (X.tgt ∘ fun n => X.PMor.levelVal 1 (φ n)) atTop
      (𝓝 (X.PObj.levelVal 1 y)) :=
    (hc.tendsto y).comp hy
  -- (a): properness on level `0`
  obtain ⟨φ₀, -, hφ₀t, ψ, hψ, hlim⟩ :=
    MPolyfold.exists_tendsto_subseq_of_isProperMap_domRestrict X.PMor hV hφ' hy'
  -- (d): `φ ∈ 𝐗₁`
  have hφ₀1 : φ₀ ∈ X.PMor.levelSet 1 := by
    rw [← X.mem_levelSet_tgt_iff, hφ₀t]
    exact MPolyfold.levelVal_mem y
  -- `t : U(φ) → U(t(φ))` and the level-`1` lift `τ₁` of its inverse
  obtain ⟨W, V', τ, hφ₀W, hd⟩ := X.isLocalScDiffeo_tgt φ₀
  classical
  let τ₁ : X.PObj.Level 1 → X.PMor.Level 1 := fun z =>
    if hz : τ (X.PObj.levelVal 1 z) ∈ X.PMor.levelSet 1 then X.PMor.levelMk 1 _ hz
    else X.PMor.levelMk 1 φ₀ hφ₀1
  have hτ₁ : ∀ z, X.PObj.levelVal 1 z ∈ V' →
      X.PMor.levelVal 1 (τ₁ z) = τ (X.PObj.levelVal 1 z) := fun z hz => by
    simp only [τ₁, dif_pos (hd.isScSmoothOn_inv.mapsTo_levelSet 1 ⟨hz, MPolyfold.levelVal_mem z⟩),
      MPolyfold.levelVal_levelMk]
  have hsm := hd.isScSmoothOn_inv.levelOne hτ₁
  have hyV : X.PObj.levelVal 1 y ∈ V' := by
    rw [← hφ₀t]
    exact hd.mapsTo hφ₀W
  have hcont : ContinuousAt τ₁ y := hsm.continuousOn.continuousAt (hsm.isOpen.mem_nhds hyV)
  refine ⟨τ₁ y, ψ, hψ, ?_⟩
  have h1 : Tendsto (τ₁ ∘ X.liftTgt ∘ φ ∘ ψ) atTop (𝓝 (τ₁ y)) :=
    hcont.tendsto.comp (hy.comp hψ.tendsto_atTop)
  refine h1.congr' ?_
  filter_upwards [hlim (hd.isScSmoothOn.isOpen.mem_nhds hφ₀W)] with n hn
  have hn' : X.PMor.levelVal 1 (φ (ψ n)) ∈ W := hn
  refine MPolyfold.level_ext ?_
  simp only [Function.comp_apply]
  rw [hτ₁ (X.liftTgt (φ (ψ n))) (hd.mapsTo hn'), levelVal_liftTgt, hd.left_inv _ hn']

/-! ### Condition (4) -/

/-- **(4) on level `1`, sheet form**: a sheet `σ₁` of `s₁` agrees near each point with the lift of
a sheet `σ` of `s`, and `ψ ↦ m(σ(t ψ), ψ)` lifts. -/
theorem isScSmoothCompSheet_lift :
    IsScSmoothCompSheet X.PObj.shift X.PMor.shift X.liftSrc X.liftTgt X.liftComp := by
  intro σ₁ W₁ V₁ hd₁
  have hc := MPolyfold.continuous_levelVal (P := X.PMor) 1
  have ht₁ := X.isLocalScDiffeo_liftTgt.continuous
  have hU₁ : IsOpen (X.liftTgt ⁻¹' V₁) := hd₁.isScSmoothOn_inv.isOpen.preimage ht₁
  refine MPolyfold.IsScSmoothOn.of_locally hU₁ fun ψ₀ hψ₀ => ?_
  obtain ⟨W, V, σ, hW, hd⟩ := X.isLocalScDiffeo_src (X.PMor.levelVal 1 (σ₁ (X.liftTgt ψ₀)))
  have hcN : ContinuousOn (fun ψ => X.PMor.levelVal 1 (σ₁ (X.liftTgt ψ))) (X.liftTgt ⁻¹' V₁) :=
    hc.comp_continuousOn (hd₁.isScSmoothOn_inv.continuousOn.comp ht₁.continuousOn
      (mapsTo_preimage _ _))
  have hN := hcN.isOpen_inter_preimage hU₁ hd.isScSmoothOn.isOpen
  refine ⟨_, hN, ⟨hψ₀, hW⟩, inter_subset_left, ?_⟩
  have hsrc : ∀ ψ ∈ X.liftTgt ⁻¹' V₁,
      X.src (X.PMor.levelVal 1 (σ₁ (X.liftTgt ψ))) = X.tgt (X.PMor.levelVal 1 ψ) :=
    fun ψ hψ => congrArg (X.PObj.levelVal 1) (hd₁.right_inv _ hψ)
  classical
  let g₁ : X.PMor.Level 1 → X.PMor.Level 1 := fun ψ =>
    if h : X.comp (σ (X.tgt (X.PMor.levelVal 1 ψ))) (X.PMor.levelVal 1 ψ) ∈ X.PMor.levelSet 1
    then X.PMor.levelMk 1 _ h else ψ
  have hg₁ : ∀ ψ, X.PMor.levelVal 1 ψ ∈ X.tgt ⁻¹' V → X.PMor.levelVal 1 (g₁ ψ) =
      X.comp (σ (X.tgt (X.PMor.levelVal 1 ψ))) (X.PMor.levelVal 1 ψ) := by
    intro ψ hψ
    have hs : X.src (σ (X.tgt (X.PMor.levelVal 1 ψ))) = X.tgt (X.PMor.levelVal 1 ψ) :=
      hd.right_inv _ hψ
    have hσ1 : σ (X.tgt (X.PMor.levelVal 1 ψ)) ∈ X.PMor.levelSet 1 := by
      rw [← X.mem_levelSet_src_iff, hs, X.mem_levelSet_tgt_iff]
      exact MPolyfold.levelVal_mem ψ
    simp only [g₁, dif_pos (X.comp_mem_levelSet hσ1 hs), MPolyfold.levelVal_levelMk]
  have hsm := (X.isScSmoothCompSheet σ W V hd).levelOne hg₁
  have hNV : ∀ ψ ∈ X.liftTgt ⁻¹' V₁ ∩ (fun ψ => X.PMor.levelVal 1 (σ₁ (X.liftTgt ψ))) ⁻¹' W,
      X.PMor.levelVal 1 ψ ∈ X.tgt ⁻¹' V := fun ψ hψ => by
    rw [mem_preimage, ← hsrc ψ hψ.1]
    exact hd.mapsTo hψ.2
  refine (hsm.mono hN hNV).congr fun ψ hψ => MPolyfold.level_ext ?_
  have he : σ (X.tgt (X.PMor.levelVal 1 ψ)) = X.PMor.levelVal 1 (σ₁ (X.liftTgt ψ)) := by
    rw [← hsrc ψ hψ.1, hd.left_inv _ hψ.2]
  rw [hg₁ ψ (hNV ψ hψ), X.levelVal_liftComp (hsrc ψ hψ.1), he]

/-- **(4) on level `1`**, literally (on the M-polyfold `𝐗¹ ₛ×ₜ 𝐗¹`). -/
theorem isScSmoothComp_lift :
    IsScSmoothComp X.PObj.shift X.PMor.shift X.liftSrc X.liftTgt X.liftComp
      X.isLocalScDiffeo_liftSrc X.isLocalScDiffeo_liftTgt.isScSmoothMap :=
  (isScSmoothComp_iff_sheet _ _).2 X.isScSmoothCompSheet_lift

/-! ### Proposition 7.11 -/

/-- **Proposition 7.11 (index lifting), the structure**: the ep-groupoid `X¹ = (X¹, 𝐗¹)`, with
the M-polyfolds `X¹`, `𝐗¹` (paracompact by Theorem 2.2 [2.16], the instance
`MPolyfold.paracompactSpace_level`) and the structure maps of `X` restricted to level `1`. -/
def liftOne : EpGroupoid (X.PObj.Level 1) (X.PMor.Level 1) where
  toGroupoidStr := X.liftGroupoidStr
  PObj := X.PObj.shift
  PMor := X.PMor.shift
  isLocalScDiffeo_src := X.isLocalScDiffeo_liftSrc
  isLocalScDiffeo_tgt := X.isLocalScDiffeo_liftTgt
  isScSmoothMap_unit := X.isScSmoothMap_liftUnit
  isScSmoothMap_inv := X.isScSmoothMap_liftInv
  exists_isProperMap := X.exists_isProperMap_lift
  isScSmoothComp := X.isScSmoothComp_lift

@[simp]
theorem liftOne_src_val (φ : X.PMor.Level 1) :
    X.PObj.levelVal 1 (X.liftOne.src φ) = X.src (X.PMor.levelVal 1 φ) := rfl

@[simp]
theorem liftOne_tgt_val (φ : X.PMor.Level 1) :
    X.PObj.levelVal 1 (X.liftOne.tgt φ) = X.tgt (X.PMor.levelVal 1 φ) := rfl

@[simp]
theorem liftOne_unit_val (x : X.PObj.Level 1) :
    X.PMor.levelVal 1 (X.liftOne.unit x) = X.unit (X.PObj.levelVal 1 x) := rfl

@[simp]
theorem liftOne_inv_val (φ : X.PMor.Level 1) :
    X.PMor.levelVal 1 (X.liftOne.inv φ) = X.inv (X.PMor.levelVal 1 φ) := rfl

theorem liftOne_comp_val {φ ψ : X.PMor.Level 1} (h : X.liftOne.src φ = X.liftOne.tgt ψ) :
    X.PMor.levelVal 1 (X.liftOne.comp φ ψ) =
      X.comp (X.PMor.levelVal 1 φ) (X.PMor.levelVal 1 ψ) :=
  X.levelVal_liftComp (X.src_eq_tgt_of_lift h)

/-- **Proposition 7.11, tameness**: if `X` is tame, so is `X¹` (`MPolyfold.IsTame.levelOne`). -/
theorem isTame_liftOne (h : X.IsTame) : X.liftOne.IsTame :=
  MPolyfold.IsTame.levelOne h

/-- **Proposition 7.11 (index lifting)**: `X¹ = (X¹, 𝐗¹)` is an ep-groupoid (`liftOne`) whose
object and morphism M-polyfolds are `X¹` and `𝐗¹` and whose structure maps are those of `X`
restricted to level `1`; if `X` is tame, so is `X¹`. -/
theorem proposition_7_11 :
    X.liftOne.PObj = X.PObj.shift ∧ X.liftOne.PMor = X.PMor.shift ∧
      (∀ φ, X.PObj.levelVal 1 (X.liftOne.src φ) = X.src (X.PMor.levelVal 1 φ)) ∧
      (∀ φ, X.PObj.levelVal 1 (X.liftOne.tgt φ) = X.tgt (X.PMor.levelVal 1 φ)) ∧
      (∀ x, X.PMor.levelVal 1 (X.liftOne.unit x) = X.unit (X.PObj.levelVal 1 x)) ∧
      (∀ φ, X.PMor.levelVal 1 (X.liftOne.inv φ) = X.inv (X.PMor.levelVal 1 φ)) ∧
      (∀ φ ψ, X.liftOne.src φ = X.liftOne.tgt ψ → X.PMor.levelVal 1 (X.liftOne.comp φ ψ) =
        X.comp (X.PMor.levelVal 1 φ) (X.PMor.levelVal 1 ψ)) ∧
      (X.IsTame → X.liftOne.IsTame) :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ h => X.liftOne_comp_val h, X.isTame_liftOne⟩

/-! ### The orbit spaces: `|X¹| → |X|` -/

/-- The inclusion `X¹ → X` as a functor of groupoids. -/
def liftIncl : GroupoidFunctor X.liftOne.toGroupoidStr X.toGroupoidStr where
  obj := X.PObj.levelVal 1
  mor := X.PMor.levelVal 1
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ h := X.levelVal_liftComp (X.src_eq_tgt_of_lift h)
  mor_unit _ := rfl

/-- **The natural map `|X¹| → |X|`**, `|x|₁ ↦ |x|`. -/
def orbitIncl : X.liftOne.OrbitSpace → X.OrbitSpace := X.liftIncl.orbitMap

@[simp]
theorem orbitIncl_π (x : X.PObj.Level 1) :
    X.orbitIncl (X.liftOne.π x) = X.π (X.PObj.levelVal 1 x) := rfl

theorem continuous_orbitIncl : Continuous X.orbitIncl :=
  (X.continuous_π.comp (MPolyfold.continuous_levelVal 1)).quotient_lift _

/-- A morphism of `X` with source or target on level `1` is a morphism of `X¹`. -/
private theorem liftOne_π_eq_of_mor {a b : X.PObj.Level 1} {φ : Mor}
    (hs : X.src φ = X.PObj.levelVal 1 a) (ht : X.tgt φ = X.PObj.levelVal 1 b) :
    X.liftOne.π a = X.liftOne.π b := by
  have hφ1 : φ ∈ X.PMor.levelSet 1 := by
    rw [← X.mem_levelSet_src_iff, hs]
    exact MPolyfold.levelVal_mem a
  exact (X.liftOne.π_eq_π_iff).2
    ⟨X.PMor.levelMk 1 φ hφ1, MPolyfold.level_ext hs, MPolyfold.level_ext ht⟩

/-- **`|X¹| → |X|` is injective**: `ml(s φ) = ml(t φ)`, so a morphism between points of `X₁` is a
morphism of `X¹`. -/
theorem orbitIncl_injective : Injective X.orbitIncl := by
  intro a b h
  induction a using Quotient.inductionOn with | h a => ?_
  induction b using Quotient.inductionOn with | h b => ?_
  obtain ⟨φ, hφs, hφt⟩ := (X.π_eq_π_iff).1 h
  exact X.liftOne_π_eq_of_mor hφs hφt

/-- The preimage of `π(U)` under `|X¹| → |X|` is `π₁(U ∩ X₁)`. -/
theorem preimage_orbitIncl_image (U : Set Obj) :
    X.orbitIncl ⁻¹' (X.π '' U) = X.liftOne.π '' (X.PObj.levelVal 1 ⁻¹' U) := by
  ext w
  induction w using Quotient.inductionOn with | h a => ?_
  constructor
  · rintro ⟨u, hu, hua⟩
    obtain ⟨φ, hφs, hφt⟩ := (X.π_eq_π_iff).1 hua
    have hφ1 : φ ∈ X.PMor.levelSet 1 := by
      rw [← X.mem_levelSet_tgt_iff, hφt]
      exact MPolyfold.levelVal_mem a
    have hu1 : u ∈ X.PObj.levelSet 1 := by
      rw [← hφs, X.mem_levelSet_src_iff]
      exact hφ1
    exact ⟨X.PObj.levelMk 1 u hu1, hu, X.liftOne_π_eq_of_mor hφs hφt⟩
  · rintro ⟨b, hb, hba⟩
    refine ⟨X.PObj.levelVal 1 b, hb, ?_⟩
    rw [← orbitIncl_π, hba]

/-- The range of `|X¹| → |X|` is `|X₁| = π(X₁)` (p. 228). -/
theorem range_orbitIncl : range X.orbitIncl = X.orbitLevel 1 := by
  ext w
  constructor
  · rintro ⟨w, rfl⟩
    induction w using Quotient.inductionOn with | h a => ?_
    exact ⟨X.PObj.levelVal 1 a, MPolyfold.levelVal_mem a, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨X.liftOne.π (X.PObj.levelMk 1 y hy), rfl⟩

namespace NaturalRep

variable {X} {x : Obj} (R : X.NaturalRep x)

/-- `U(x)₁ = U(x) ∩ X₁`, an open subset of `X¹`. -/
def liftU : Set (X.PObj.Level 1) := X.PObj.levelVal 1 ⁻¹' R.U

theorem isOpen_liftU : IsOpen R.liftU := R.isOpen_U.preimage (MPolyfold.continuous_levelVal 1)

theorem Φ_mem_levelSet (g : X.Isotropy x) {y : Obj} (hy : y ∈ R.U)
    (hy1 : y ∈ X.PObj.levelSet 1) : R.Φ g y ∈ X.PObj.levelSet 1 :=
  (R.isScDiffeoOn_Φ g).isScSmoothOn.mapsTo_levelSet 1 ⟨hy, hy1⟩

/-- The natural action restricted to `U(x)₁`. -/
def liftΦ (g : X.Isotropy x) (y : R.liftU) : R.liftU :=
  ⟨X.PObj.levelMk 1 (R.Φ g (X.PObj.levelVal 1 y.1))
    (R.Φ_mem_levelSet g y.2 (MPolyfold.levelVal_mem _)), R.mapsTo_Φ g y.2⟩

/-- The action of `G_x` on `U(x)₁` ("the same is true for `U(x)₁ ⊂ X₁`", p. 250). -/
instance liftMulAction : MulAction (X.Isotropy x) R.liftU where
  smul := R.liftΦ
  one_smul y := Subtype.ext (MPolyfold.level_ext (R.Φ_one _ y.2))
  mul_smul g h y := Subtype.ext (MPolyfold.level_ext (R.Φ_mul g h _ y.2))

@[simp]
theorem levelVal_liftSmul (g : X.Isotropy x) (y : R.liftU) :
    X.PObj.levelVal 1 (g • y : R.liftU).1 = R.Φ g (X.PObj.levelVal 1 y.1) := rfl

/-- `G_x` acts on `U(x)₁` by homeomorphisms (the level-`1` lift of `Φ(g)`). -/
theorem continuous_liftSmul (g : X.Isotropy x) : Continuous fun y : R.liftU => g • y := by
  classical
  let f₁ : X.PObj.Level 1 → X.PObj.Level 1 := fun z =>
    if hz : R.Φ g (X.PObj.levelVal 1 z) ∈ X.PObj.levelSet 1 then X.PObj.levelMk 1 _ hz else z
  have hf₁ : ∀ z, X.PObj.levelVal 1 z ∈ R.U →
      X.PObj.levelVal 1 (f₁ z) = R.Φ g (X.PObj.levelVal 1 z) := fun z hz => by
    simp only [f₁, dif_pos (R.Φ_mem_levelSet g hz (MPolyfold.levelVal_mem z)),
      MPolyfold.levelVal_levelMk]
  have hc := ((R.isScDiffeoOn_Φ g).isScSmoothOn.levelOne hf₁).continuousOn
  refine continuous_induced_rng.2 (hc.domRestrict.congr fun y => ?_)
  exact MPolyfold.level_ext (hf₁ y.1 y.2)

/-- `|g ∗ y|₁ = |y|₁`: `Γ(g, y)` is a morphism of `X¹`. -/
theorem liftOne_π_smul (g : X.Isotropy x) (y : R.liftU) :
    X.liftOne.π (g • y : R.liftU).1 = X.liftOne.π y.1 :=
  (X.liftOne_π_eq_of_mor (b := (g • y : R.liftU).1) (R.src_Γ g _ y.2)
    (R.tgt_Γ g _ y.2)).symm

/-- **`|y|₁ = |z|₁` for `y, z ∈ U(x)₁` iff `z = g ∗ y`** (Theorem 7.1 (3)). -/
theorem liftOne_π_eq_iff {y z : R.liftU} :
    X.liftOne.π y.1 = X.liftOne.π z.1 ↔ ∃ g : X.Isotropy x, g • y = z := by
  constructor
  · intro h
    obtain ⟨φ, hφs, hφt⟩ := (X.liftOne.π_eq_π_iff).1 h
    have hs : X.src (X.PMor.levelVal 1 φ) = X.PObj.levelVal 1 y.1 :=
      congrArg (X.PObj.levelVal 1) hφs
    have ht : X.tgt (X.PMor.levelVal 1 φ) = X.PObj.levelVal 1 z.1 :=
      congrArg (X.PObj.levelVal 1) hφt
    obtain ⟨g, hg, -⟩ := R.existsUnique_Γ (X.PMor.levelVal 1 φ) (by rw [hs]; exact y.2)
      (by rw [ht]; exact z.2)
    refine ⟨g, Subtype.ext (MPolyfold.level_ext ?_)⟩
    rw [levelVal_liftSmul, ← R.tgt_Γ g _ y.2, ← hs, hg, ht]
  · rintro ⟨g, rfl⟩
    exact (R.liftOne_π_smul g y).symm

private theorem liftOrbitRel_iff (y z : R.liftU) :
    MulAction.orbitRel (X.Isotropy x) R.liftU y z ↔ X.liftOne.π y.1 = X.liftOne.π z.1 := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, eq_comm, R.liftOne_π_eq_iff]

/-- `G_x\U(x)₁ → |X¹|`, `G_x ∗ y ↦ |y|₁`. -/
def liftOrbitQuotientMap :
    MulAction.orbitRel.Quotient (X.Isotropy x) R.liftU → X.liftOne.OrbitSpace :=
  Quotient.lift (fun y : R.liftU => X.liftOne.π y.1) fun y z h => (R.liftOrbitRel_iff y z).1 h

/-- `G_x\U(x)₁ → |X¹|` is an open embedding (the argument of Proposition 7.6 on level `1`). -/
theorem isOpenEmbedding_liftOrbitQuotientMap : IsOpenEmbedding R.liftOrbitQuotientMap := by
  refine .of_continuous_injective_isOpenMap
    ((X.liftOne.continuous_π.comp continuous_subtype_val).quotient_lift _) (fun q q' h => ?_)
    fun S hS => ?_
  · induction q using Quotient.inductionOn with | h y => ?_
    induction q' using Quotient.inductionOn with | h z => ?_
    exact Quotient.sound ((R.liftOrbitRel_iff y z).2 h)
  · have himage : R.liftOrbitQuotientMap '' S =
        X.liftOne.π '' (Subtype.val '' (Quotient.mk _ ⁻¹' S)) := by
      ext w
      constructor
      · rintro ⟨q, hq, rfl⟩
        induction q using Quotient.inductionOn with | h y => ?_
        exact ⟨y, ⟨y, hq, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨Quotient.mk _ y, hy, rfl⟩
    rw [himage]
    exact X.liftOne.proposition_7_1 _ (R.isOpen_liftU.isOpenMap_subtype_val _
      (hS.preimage continuous_quotient_mk'))

theorem range_liftOrbitQuotientMap :
    range R.liftOrbitQuotientMap = X.orbitIncl ⁻¹' (X.π '' R.U) := by
  rw [X.preimage_orbitIncl_image]
  ext w
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quotient.inductionOn with | h y => ?_
    exact ⟨y.1, y.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Quotient.mk _ ⟨y, hy⟩, rfl⟩

/-- **`|U(x)|₁ = |U(x)₁|` is metrizable** (Proposition 7.12's proof: the argument of Lemma 7.4
on level `1`): the preimage of `|U(x)| = π(U(x))` under `|X¹| → |X|` is metrizable. -/
theorem metrizableSpace_preimage_orbitIncl : MetrizableSpace (X.orbitIncl ⁻¹' (X.π '' R.U)) := by
  have := X.PObj.metrizableSpace_level 1
  have := metrizableSpace_orbitRel_quotient_of_finite R.continuous_liftSmul
  exact (R.isOpenEmbedding_liftOrbitQuotientMap.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr R.range_liftOrbitQuotientMap)).symm.isEmbedding.metrizableSpace

end NaturalRep

/-! ### Definition 7.15 and Remark 7.1 -/

/-- **Definition 7.15 and Theorem 7.2**: `X` has paracompact orbit space iff `|X|` is metrizable
(Smirnov's theorem one way, Stone's theorem the other). -/
theorem hasParacompactOrbitSpace_iff_metrizableSpace :
    X.HasParacompactOrbitSpace ↔ MetrizableSpace X.OrbitSpace :=
  ⟨X.theorem_7_2_metrizable, fun _ => paracompactSpace_of_metrizableSpace _⟩

/-- A second countable orbit space is paracompact (Corollary 7.1 and Stone's theorem). -/
theorem hasParacompactOrbitSpace_of_secondCountableTopology
    [SecondCountableTopology X.OrbitSpace] : X.HasParacompactOrbitSpace :=
  have := X.corollary_7_1
  paracompactSpace_of_metrizableSpace _

/-- **The sentence before Remark 7.1** (p. 249), "in case `X` has a second countable topology
… (1)–(4) imply (5)": a second countable object space gives a second countable orbit space (`π`
is open, Proposition 7.1), hence (5). -/
theorem remark_7_1 [SecondCountableTopology Obj] : X.HasParacompactOrbitSpace :=
  have : SecondCountableTopology X.OrbitSpace :=
    Quotient.secondCountableTopology X.proposition_7_1
  X.hasParacompactOrbitSpace_of_secondCountableTopology

/-! ### Proposition 7.12 -/

/-- **`|X¹|` is metrizable** if `|X|` is paracompact: Smirnov's theorem pulled back along
`|X¹| → |X|` (`metrizableSpace_of_pullback`), the preimages of the `|U(x)|` being metrizable. -/
theorem metrizableSpace_liftOne_orbitSpace (h : X.HasParacompactOrbitSpace) :
    MetrizableSpace X.liftOne.OrbitSpace := by
  have : ParacompactSpace X.OrbitSpace := h
  refine metrizableSpace_of_pullback X.orbitIncl X.continuous_orbitIncl fun z => ?_
  obtain ⟨x, rfl⟩ := X.surjective_π z
  obtain ⟨R, -⟩ := theorem_7_1 X x isOpen_univ (mem_univ x)
  exact ⟨X.π '' R.U, X.proposition_7_1 _ R.isOpen_U, mem_image_of_mem _ R.mem_U,
    R.metrizableSpace_preimage_orbitIncl⟩

/-- **Proposition 7.12 (paracompactness under lifts)**: if `X` has paracompact orbit space, so
has `X¹` (with Proposition 7.11, `X¹` is an ep-groupoid with paracompact orbit space). -/
theorem proposition_7_12 (h : X.HasParacompactOrbitSpace) : X.liftOne.HasParacompactOrbitSpace :=
  have := X.metrizableSpace_liftOne_orbitSpace h
  paracompactSpace_of_metrizableSpace _

end EpGroupoid

end Polyfold
