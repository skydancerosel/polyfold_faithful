import Polyfold.Chapter15.RelativeLocalFamilies

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, **Theorem 15.3.9
(Transversal Extension Theorem)**, p. 694 (2017: Theorem 15.5): the hypothesis on the boundary
data, "`T(f|∂X, Λ)(x)` is surjective with respect to the intersections of local faces".

# The boundary hypothesis does not depend on the extension

## The text, paraphrased

The hypothesis is stated for `Λ : W|∂X → ℚ⁺` alone: at a smooth `x ∈ ∂X` the operators
`(f − sᵢ)'(x)`, restricted to the tangent space of the intersection of the local faces through
`x`, only involve the values of the local sections `sᵢ` on these faces.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `exists_mem_closure_interior_of_finite_cover`: for a finite closed cover of a topological space
  every point lies in the closure of the interior of one of the sets.
* `continuousOn_scDeriv_apply`: `z ↦ Dg(z)v` is continuous on `U₁` for an sc¹ map `g`.
* `scDeriv_eq_of_eqOn_level_one`, `exists_scDeriv_eq_on_of_cover`: for sc¹ maps `g`, `g'ᵢ` on a
  relatively open `U ⊆ C` and a subspace `K ⊆ C` whose level-`1` vectors are dense in it, if at
  every point of `U ∩ K` the value of `g` is one of the values `g'ᵢ`, then at every `z₀ ∈ U₁ ∩ K`
  some `g'ᵢ` has `g'ᵢ(z₀) = g(z₀)` and `Dg'ᵢ(z₀) = Dg(z₀)` on `K`.
* `mem_closure_level_one_minimalSubspace`: in the minimal subspace at the centre of a partial
  quadrant the level-`1` vectors are dense.
* **`exists_linearization_eqOn_reduced`**: at a smooth `x ∈ ∂X`, if two sc⁺-multisections agree
  over `∂X` near `x`, every operator of `T(f, Λ₂)(x)` agrees on `T^R_xX` with an operator of
  `T(f, Λ₁)(x)`.  In a tame chart centred at `x` the retraction maps the minimal subspace `K`
  into the stratum of `x`, which lies over `∂X`; there the branches of `Λ₂` are branches of `Λ₁`.
* **`isReducedOntoAtPt_of_eqOn_boundary`**, `isReducedOntoAtPt_of_eq_boundary`: general position
  at `x` is the same for both.
* **`isBoundaryFaceOnto_iff`**: `IsBoundaryFaceOnto f Λ` (the condition for every sc⁺ extension)
  holds iff it holds for one sc⁺ extension of `Λ`.
* **`theorem_15_3_9_of_one_extension`**: Theorem 15.3.9 with the boundary hypothesis checked on
  one extension.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

/-! ### Finite closed covers -/

/-- **For a finite closed cover, every point lies in the closure of the interior of one of the
sets** (a finite union of closed sets with empty interior has empty interior). -/
theorem exists_mem_closure_interior_of_finite_cover {Z : Type*} [TopologicalSpace Z]
    {ι : Type*} [Finite ι] {C : ι → Set Z} (hC : ∀ i, IsClosed (C i))
    (hcov : ⋃ i, C i = univ) (x : Z) : ∃ i, x ∈ closure (interior (C i)) := by
  classical
  have := Fintype.ofFinite ι
  by_contra hne
  push Not at hne
  have key : ∀ (s : Finset ι) (V : Set Z), IsOpen V → V ⊆ ⋃ i ∈ s, C i →
      (∀ i ∈ s, V ∩ interior (C i) = ∅) → V = ∅ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro V _ hV _
      refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
      obtain ⟨i, hi, -⟩ := mem_iUnion₂.1 (hV hz)
      exact absurd hi (Finset.notMem_empty i)
    | insert i s _ ih =>
      intro V hVo hV hdis
      have h' : V \ C i = ∅ := by
        refine ih (V \ C i) (hVo.sdiff (hC i)) (fun z hz => ?_) (fun j hj => ?_)
        · obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.1 (hV hz.1)
          rcases Finset.mem_insert.1 hj with rfl | hj
          · exact absurd hzj hz.2
          · exact mem_iUnion₂.2 ⟨j, hj, hzj⟩
        · refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
          have h0 := hdis j (Finset.mem_insert_of_mem hj)
          rw [eq_empty_iff_forall_notMem] at h0
          exact h0 z ⟨hz.1.1, hz.2⟩
      have hVC : V ⊆ C i := sdiff_eq_empty.1 h'
      have hVi : V ⊆ interior (C i) := interior_maximal hVC hVo
      have h0 := hdis i (Finset.mem_insert_self i s)
      rw [inter_eq_left.2 hVi] at h0
      exact h0
  set V : Set Z := ⋂ i, (closure (interior (C i)))ᶜ with hVdef
  have hVo : IsOpen V := isOpen_iInter_of_finite fun i => isClosed_closure.isOpen_compl
  have hxV : x ∈ V := mem_iInter.2 hne
  have hV := key Finset.univ V hVo (by simp [hcov]) (fun i _ => by
    refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
    exact mem_iInter.1 hz.1 i (subset_closure hz.2))
  rw [hV] at hxV
  exact hxV

/-! ### Derivatives of sc¹ maps along a subspace -/

section Model

variable {E F : ScBanach} {C U : Set (E 0)}

/-- **`z ↦ Dg(z)v` is continuous on `U₁`** for an sc¹ map `g` and `v ∈ E₀` (the tangent map is
sc⁰, Definition 1.1.15 (3)). -/
theorem continuousOn_scDeriv_apply {g : E 0 → F 0} (hg : IsSc1 U g) (v : E 0) :
    ContinuousOn (fun z : E 1 => scDeriv U g z v) (E.lvlSet U 1) := by
  have h := hg.isSc1With_scDeriv.tangent_isSc0.continuousOn_base
  have h2 : ContinuousOn (fun p : E.tangent 0 => scDeriv U g p.1 p.2) (E.tangentSet U) :=
    continuous_snd.comp_continuousOn h
  have hc : Continuous (fun z : E 1 => ((z, v) : E.tangent 0)) :=
    continuous_id.prodMk continuous_const
  exact h2.comp hc.continuousOn (fun z hz => hz)

/-- **Two sc¹ maps which agree on `U ∩ K` near `z` in the level-`1` topology have the same
derivative at `z` in the level-`1` directions of `K`**, for a subspace `K ⊆ C`. -/
theorem scDeriv_eq_of_eqOn_level_one (hU : IsRelOpenInQuadrant E C U) {g₁ g₂ : E 0 → F 0}
    (h₁ : IsSc1 U g₁) (h₂ : IsSc1 U g₂) {K : Submodule ℝ (E 0)} (hKC : (K : Set (E 0)) ⊆ C)
    {z : E 1} (hzU : E.toBase 1 z ∈ U) (hzK : E.toBase 1 z ∈ K) {G : Set (E 1)} (hG : IsOpen G)
    (hzG : z ∈ G)
    (heq : ∀ z' ∈ G, E.toBase 1 z' ∈ U → E.toBase 1 z' ∈ K →
      g₁ (E.toBase 1 z') = g₂ (E.toBase 1 z'))
    {v₁ : E 1} (hv : E.toBase 1 v₁ ∈ K) :
    scDeriv U g₁ z (E.toBase 1 v₁) = scDeriv U g₂ z (E.toBase 1 v₁) := by
  obtain ⟨O', hO', hUeq⟩ := hU.relOpen
  set γ : ℝ → E 1 := fun t => z + t • v₁ with hγdef
  have hγc : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hγ0 : γ 0 = z := by simp [hγdef]
  set S : Set ℝ := γ ⁻¹' (G ∩ E.toBase 1 ⁻¹' O') with hSdef
  have hS : IsOpen S := (hG.inter (hO'.preimage (E.toBase 1).continuous)).preimage hγc
  have h0S : (0 : ℝ) ∈ S := by
    change γ 0 ∈ G ∩ E.toBase 1 ⁻¹' O'
    rw [hγ0]
    exact ⟨hzG, by rw [hUeq] at hzU; exact hzU.1⟩
  have hγK : ∀ t, E.toBase 1 (γ t) ∈ K := fun t => by
    rw [hγdef]
    simp only [map_add, map_smul]
    exact K.add_mem hzK (K.smul_mem t hv)
  have hγU : ∀ t ∈ S, E.toBase 1 (γ t) ∈ U := fun t ht => by
    rw [hUeq]
    exact ⟨ht.2, hKC (hγK t)⟩
  have hmaps : MapsTo γ S (E.lvlSet U 1) := fun t ht => hγU t ht
  have hγd : HasDerivWithinAt γ v₁ S 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v₁).const_add z
    simp only [one_smul] at h
    exact h.hasDerivWithinAt
  have hd₁ := h₁.isSc1With_scDeriv.hasFDerivWithinAt z hzU
  have hd₂ := h₂.isSc1With_scDeriv.hasFDerivWithinAt z hzU
  rw [← hγ0] at hd₁ hd₂
  have hk₁ := hd₁.comp_hasDerivWithinAt (0 : ℝ) hγd hmaps
  have hk₂ := hd₂.comp_hasDerivWithinAt (0 : ℝ) hγd hmaps
  have hk₂' := hk₂.congr (fun t ht => heq (γ t) ht.1 (hγU t ht) (hγK t))
    (heq (γ 0) h0S.1 (hγU 0 h0S) (hγK 0))
  have e := (hS.uniqueDiffWithinAt h0S).eq_deriv _ hk₁ hk₂'
  rw [hγ0] at e
  exact e

/-- **Derivatives along a subspace for a finite cover**: let `g` and finitely many `g'ᵢ` be sc¹ on
the relatively open `U ⊆ C`, and `K ⊆ C` a subspace in which the level-`1` vectors are dense.  If
at every point of `U ∩ K` the value of `g` is one of the `g'ᵢ`, then at every `z₀ ∈ U₁` over `K`
there is `i` with `g(z₀) = g'ᵢ(z₀)` and `Dg(z₀) = Dg'ᵢ(z₀)` on `K`. -/
theorem exists_scDeriv_eq_on_of_cover (hU : IsRelOpenInQuadrant E C U) {g : E 0 → F 0}
    (hg : IsSc1 U g) {ι : Type*} [Finite ι] {g' : ι → E 0 → F 0} (hg' : ∀ i, IsSc1 U (g' i))
    {K : Submodule ℝ (E 0)} (hKC : (K : Set (E 0)) ⊆ C)
    (hdense : ∀ v ∈ K, v ∈ closure (E.toBase 1 '' {v₁ | E.toBase 1 v₁ ∈ K}))
    (hcov : ∀ u ∈ U, u ∈ K → ∃ i, g u = g' i u) {z₀ : E 1} (hz₀U : E.toBase 1 z₀ ∈ U)
    (hz₀K : E.toBase 1 z₀ ∈ K) :
    ∃ i, g (E.toBase 1 z₀) = g' i (E.toBase 1 z₀) ∧
      ∀ v ∈ K, scDeriv U g z₀ v = scDeriv U (g' i) z₀ v := by
  let Z := {z : E 1 // E.toBase 1 z ∈ U ∧ E.toBase 1 z ∈ K}
  have hcont : ∀ h : E 0 → F 0, IsSc1 U h → Continuous (fun z : Z => h (E.toBase 1 z.1)) :=
    fun h hh => hh.isSc0.continuousOn_base.comp_continuous
      ((E.toBase 1).continuous.comp continuous_subtype_val) (fun z => z.2.1)
  set Cset : ι → Set Z := fun i => {z : Z | g (E.toBase 1 z.1) = g' i (E.toBase 1 z.1)}
    with hCdef
  have hC : ∀ i, IsClosed (Cset i) := fun i => isClosed_eq (hcont g hg) (hcont _ (hg' i))
  have hcovZ : ⋃ i, Cset i = univ :=
    eq_univ_of_forall fun z => mem_iUnion.2 (hcov _ z.2.1 z.2.2)
  obtain ⟨i, hi⟩ := exists_mem_closure_interior_of_finite_cover hC hcovZ ⟨z₀, hz₀U, hz₀K⟩
  refine ⟨i, ?_, fun v hv => ?_⟩
  · have hm : (⟨z₀, hz₀U, hz₀K⟩ : Z) ∈ Cset i :=
      (hC i).closure_subset_iff.2 interior_subset hi
    exact hm
  · have hint : ∀ z ∈ interior (Cset i), scDeriv U g z.1 v = scDeriv U (g' i) z.1 v := by
      intro z hz
      obtain ⟨G, hGo, hG⟩ := isOpen_induced_iff.1 (isOpen_interior (s := Cset i))
      have hzG : z.1 ∈ G := by
        have : z ∈ Subtype.val ⁻¹' G := by rw [hG]; exact hz
        exact this
      have hlvl : ∀ v₁ : E 1, E.toBase 1 v₁ ∈ K →
          scDeriv U g z.1 (E.toBase 1 v₁) = scDeriv U (g' i) z.1 (E.toBase 1 v₁) :=
        fun v₁ hv₁ => scDeriv_eq_of_eqOn_level_one hU hg (hg' i) hKC z.2.1 z.2.2 hGo hzG
          (fun z' hz'G hz'U hz'K => by
            have hmem : (⟨z', hz'U, hz'K⟩ : Z) ∈ interior (Cset i) := by
              rw [← hG]; exact hz'G
            exact (interior_subset hmem : (⟨z', hz'U, hz'K⟩ : Z) ∈ Cset i)) hv₁
      have hcl : IsClosed {w : E 0 | scDeriv U g z.1 w = scDeriv U (g' i) z.1 w} :=
        isClosed_eq (scDeriv U g z.1).continuous (scDeriv U (g' i) z.1).continuous
      exact hcl.closure_subset_iff.2 (by rintro _ ⟨v₁, hv₁, rfl⟩; exact hlvl v₁ hv₁)
        (hdense v hv)
    have hc1 : Continuous (fun z : Z => scDeriv U g z.1 v) :=
      (continuousOn_scDeriv_apply hg v).comp_continuous continuous_subtype_val fun z => z.2.1
    have hc2 : Continuous (fun z : Z => scDeriv U (g' i) z.1 v) :=
      (continuousOn_scDeriv_apply (hg' i) v).comp_continuous continuous_subtype_val
        fun z => z.2.1
    have hcl : IsClosed {z : Z | scDeriv U g z.1 v = scDeriv U (g' i) z.1 v} :=
      isClosed_eq hc1 hc2
    exact hcl.closure_subset_iff.2 hint hi

end Model

/-! ### The minimal subspace at the centre of a chart -/

/-- **The level-`1` vectors are dense in the minimal subspace at `0`** (`W₁` is dense in `W₀`). -/
theorem mem_closure_level_one_minimalSubspace {E : ScBanach} {n : ℕ} {Wq : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)) {v : E 0}
    (hv : v ∈ minimalSubspaceWith T 0) :
    v ∈ closure (E.toBase 1 '' {v₁ | E.toBase 1 v₁ ∈ minimalSubspaceWith T 0}) := by
  let ψ : Wq 0 → E 0 := fun w => (T 0).symm ((0 : Fin n → ℝ), w)
  have hψ : Continuous ψ := (T 0).symm.continuous.comp (continuous_const.prodMk continuous_id)
  have hvψ : v = ψ (T 0 v).2 := by
    change v = (T 0).symm (0, (T 0 v).2)
    rw [ContinuousLinearEquiv.eq_symm_apply]
    exact Prod.ext (funext fun i => (mem_minimalSubspaceWith_zero T).1 hv i) rfl
  have hd : (T 0 v).2 ∈ closure (range (Wq.incl 0)) := by
    rw [(Wq.denseRange_incl 0).closure_range]
    exact mem_univ _
  rw [hvψ]
  refine closure_mono ?_ (image_closure_subset_closure_image hψ ⟨_, hd, rfl⟩)
  rintro _ ⟨_, ⟨w', rfl⟩, rfl⟩
  have e : E.toBase 1 ((T 1).symm (((0 : Fin n → ℝ), w') :
      ((ScBanach.const (Fin n → ℝ)).prod Wq) 1)) = ψ (Wq.incl 0 w') := by
    rw [T.symm_toBase_comm, ScBanach.prod_toBase]
    simp only [map_zero]
    rfl
  refine ⟨(T 1).symm (((0 : Fin n → ℝ), w') : ((ScBanach.const (Fin n → ℝ)).prod Wq) 1), ?_, e⟩
  change E.toBase 1 _ ∈ minimalSubspaceWith T 0
  rw [e, mem_minimalSubspaceWith_zero]
  intro i
  simp [ψ]

/-! ### The operators of `T(f, Λ)(x)` on `T^R_xX` at a boundary point -/

section Bundle

variable {A : SEP.{u}}

set_option maxHeartbeats 1600000 in
-- the chart reading at a tame chart centred at `x` and the finite cover argument
/-- **On `T^R_xX` the operators of `T(f, Λ)(x)` at a smooth `x ∈ ∂X` only depend on `Λ` over
`∂X` near `x`**: if two sc⁺-multisections `Λ₁`, `Λ₂` agree over `∂X ∩ Q` for an open `Q ∋ x`,
every operator of `T(f, Λ₂)(x)` agrees on the reduced tangent space with an operator of
`T(f, Λ₁)(x)`.  *Proof*: in a tame chart
centred at `x` the points of `U` in the minimal subspace `K` are mapped by the retraction to
points of the retract with the degeneracy index of `x`, so they lie over `∂X`, where the branches
of `Λ₂` are branches of `Λ₁`; `exists_scDeriv_eq_on_of_cover` gives a branch of `Λ₁` through
`f(x)` with the same derivative on `K ⊇ T^R`. -/
theorem exists_linearization_eqOn_reduced {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ₁ Λ₂ : A.W → ℚ≥0} (h₁ : IsScPlusMultisection A Λ₁) (h₂ : IsScPlusMultisection A Λ₂)
    {Q : Set A.Obj} (hQ : IsOpen Q)
    (hagree : ∀ w, A.P w ∈ A.X.PObj.boundary → A.P w ∈ Q → Λ₁ w = Λ₂ w)
    {x : A.X.PObj.Level 1} (hxQ : A.X.PObj.levelVal 1 x ∈ Q)
    (hxb : A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary)
    (hxs : A.X.PObj.levelVal 1 x ∈ A.X.PObj.smoothSet) :
    ∀ L₂ ∈ (linearization f Λ₂ x).support, ∃ L₁ ∈ (linearization f Λ₁ x).support,
      ∀ (φ : MChart A.Obj) (hφ : A.X.PObj.IsChart φ)
        (hx : A.X.PObj.levelVal 1 x ∈ φ.source) (m : ℕ) (V : ScBanach)
        (T : ScIso φ.model.E ((ScBanach.const (Fin m → ℝ)).prod V)),
        φ.model.C = T 0 ⁻¹' quadrant m V 0 →
          ∀ u ∈ reducedTangentFiber hφ hx T, L₁ u = L₂ u := by
  classical
  have hsecf : IsSection A.P f := hft.isScSmooth.1
  set y₀ := A.X.PObj.levelVal 1 x with hy₀
  obtain ⟨O₁, k₁, s₁', σ₁, hO₁, hxO₁, hrep₁'⟩ := h₁.exists_isLocalRepOn y₀
  obtain ⟨O₂, k₂, s₂', σ₂, hO₂, hxO₂, hrep₂'⟩ := h₂.exists_isLocalRepOn y₀
  set O := (O₁ ∩ O₂) ∩ Q with hOdef
  have hO : IsOpen O := (hO₁.inter hO₂).inter hQ
  set s₁ : Fin k₁ → A.Obj → A.W := fun a => extendZero O₁ (s₁' a) with hs₁def
  set s₂ : Fin k₂ → A.Obj → A.W := fun b => extendZero O₂ (s₂' b) with hs₂def
  have hs₁ : ∀ a, IsSection A.P (s₁ a) := fun a => isSection_extendZero O₁ _
  have hs₂ : ∀ b, IsSection A.P (s₂ b) := fun b => isSection_extendZero O₂ _
  have hrep₁ : IsLocalRepOn A Λ₁ O s₁ σ₁ :=
    hrep₁'.extendZero.mono hO (inter_subset_left.trans inter_subset_left)
  have hrep₂ : IsLocalRepOn A Λ₂ O s₂ σ₂ :=
    hrep₂'.extendZero.mono hO (inter_subset_left.trans inter_subset_right)
  obtain ⟨-, c₀, hc₀, hxc₀, hφ0, -⟩ := hft.germTame y₀ hxs
  set c := c₀.restrictInter hO with hcdef
  have hc : A.B.IsTameChart c := hc₀.restrictInter hO
  have hsub : c.φ.source ⊆ O := c₀.restrictInter_source_subset hO
  have hxc : y₀ ∈ c.φ.source := ⟨hxc₀, ⟨hxO₁, hxO₂⟩, hxQ⟩
  have hφ0c : c.φ y₀ = 0 := hφ0
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  intro L₂ hL₂
  let d₂ : LocalLinData A Λ₂ x := ⟨O, hO, k₂, s₂, σ₂, hrep₂, c, hc.1, hsub, hxc⟩
  rw [linearization_eq hf d₂] at hL₂
  obtain ⟨b, hb, rfl⟩ := (mem_support_linSumIntr_iff hsecf hrep₂.1
    (fun j => (hrep₂.2.1 j).1) hsub hxc L₂).1 hL₂
  set K := minimalSubspaceWith T (0 : c.φ.model.E 0) with hKdef
  have hKC : (K : Set (c.φ.model.E 0)) ⊆ c.φ.model.C := fun v hv => by
    rw [hT]
    intro i
    rw [(mem_minimalSubspaceWith_zero T).1 hv i]
  set z₀ := levelLift c.φ 1 y₀ with hz₀def
  have hz₀ : c.φ.model.E.toBase 1 z₀ = 0 := by
    rw [hz₀def, A.X.PObj.toBase_levelLift c.isChart hxc (levelVal_mem x), hφ0c]
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0c ▸ c.φ.mapsTo_model _ hxc
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  have hg : IsSc1 c.U ((fun y => c.principal f y - c.principal (s₂ b) y) ∘ r c.R) :=
    isSc1_sub_comp_r hft.isScSmooth (hrep₂.2.1 b) hc.1 hsub
  have hg' : ∀ a, IsSc1 c.U ((fun y => c.principal f y - c.principal (s₁ a) y) ∘ r c.R) :=
    fun a => isSc1_sub_comp_r hft.isScSmooth (hrep₁.2.1 a) hc.1 hsub
  have htame := hc.2 n Wq T hT
  have htr : IsTameRetract c.φ.model.E c.φ.model.C c.φ.model.O :=
    ⟨c.isRetraction.baseRetraction c.relOpen, c.base_retract, hc.2⟩
  have hdegx : A.X.PObj.degIndex y₀ = degIndexWith T (0 : c.φ.model.E 0) := by
    rw [A.X.PObj.degIndex_eq_chartDegIndex_of_isTameRetract c.isChart htr hxc]
    change degIndex c.φ.model.E c.φ.model.C (c.φ y₀) = _
    rw [hφ0c, degIndex_eq T hT (hKC K.zero_mem)]
  have hcov : ∀ u ∈ c.U, u ∈ K → ∃ a,
      ((fun y => c.principal f y - c.principal (s₂ b) y) ∘ r c.R) u =
        ((fun y => c.principal f y - c.principal (s₁ a) y) ∘ r c.R) u := by
    intro u hu huK
    have hrO := c.r_mem_O hu
    have hy : c.φ.symm (r c.R u) ∈ c.φ.source := c.φ.symm_mapsTo hrO
    have hyb : c.φ.symm (r c.R u) ∈ A.X.PObj.boundary := by
      change 1 ≤ A.X.PObj.degIndex (c.φ.symm (r c.R u))
      rw [A.X.PObj.degIndex_eq_chartDegIndex_of_isTameRetract c.isChart htr hy]
      change 1 ≤ degIndex c.φ.model.E c.φ.model.C (c.φ (c.φ.symm (r c.R u)))
      rw [c.φ.apply_symm_apply hrO]
      have e1 : degIndex c.φ.model.E c.φ.model.C (r c.R u) =
          degIndex c.φ.model.E c.φ.model.C u := htame.degIndex_apply u hu
      have e2 : degIndexWith T u = degIndexWith T (0 : c.φ.model.E 0) := by
        have hiff : ∀ i, (T 0 u).1 i = 0 ↔ (T 0 (0 : c.φ.model.E 0)).1 i = 0 :=
          fun i => ⟨fun _ => by simp, fun _ => (mem_minimalSubspaceWith_zero T).1 huK i⟩
        simp only [degIndexWith, quadrantDeg, hiff]
      rw [e1, degIndex_eq T hT (hKC huK), e2, ← hdegx]
      exact hxb
    have hyO : c.φ.symm (r c.R u) ∈ O := hsub hy
    have hmem : s₂ b (c.φ.symm (r c.R u)) ∈ suppAt Λ₁ (c.φ.symm (r c.R u)) := by
      have h2 : s₂ b (c.φ.symm (r c.R u)) ∈ suppAt Λ₂ (c.φ.symm (r c.R u)) := by
        rw [hrep₂.suppAt_eq hyO]; exact ⟨b, rfl⟩
      refine ⟨h2.1, ?_⟩
      rw [hagree _ (by rw [h2.1]; exact hyb) (by rw [h2.1]; exact hyO.2)]
      exact h2.2
    rw [hrep₁.suppAt_eq hyO] at hmem
    obtain ⟨a, ha⟩ := hmem
    refine ⟨a, ?_⟩
    change c.principal f (r c.R u) - c.principal (s₂ b) (r c.R u) =
      c.principal f (r c.R u) - c.principal (s₁ a) (r c.R u)
    congr 1
    have ha' : s₁ a (c.φ.symm (r c.R u)) = s₂ b (c.φ.symm (r c.R u)) := ha
    unfold StrongBundleChart.principal
    rw [ha']
  obtain ⟨a, hga, hD⟩ := exists_scDeriv_eq_on_of_cover c.relOpen hg hg' hKC
    (fun v hv => mem_closure_level_one_minimalSubspace T hv) hcov (z₀ := z₀)
    (by rw [hz₀]; exact h0U) (by rw [hz₀]; exact K.zero_mem)
  have hax : s₁ a y₀ = f y₀ := by
    rw [hz₀] at hga
    have hr0 : r c.R (0 : c.φ.model.E 0) = 0 :=
      StrongRetr.r_eq_self c.isRetraction (c.r_image ▸ h0O)
    change c.principal f (r c.R 0) - c.principal (s₂ b) (r c.R 0) =
      c.principal f (r c.R 0) - c.principal (s₁ a) (r c.R 0) at hga
    rw [hr0] at hga
    have h3 : c.principal (s₂ b) 0 = c.principal (s₁ a) 0 := sub_right_injective hga
    have e1 := principal_eq_fiberLin hxc (hs₁ a y₀)
    have e2 := principal_eq_fiberLin hxc (hs₂ b y₀)
    rw [hφ0c] at e1 e2
    have h4 : c.fiberLin hxc ⟨s₁ a y₀, hs₁ a y₀⟩ = c.fiberLin hxc ⟨s₂ b y₀, hs₂ b y₀⟩ := by
      rw [← e1, ← e2, h3]
    exact (congrArg Subtype.val (c.fiberLin_injective hxc h4)).trans hb
  let d₁ : LocalLinData A Λ₁ x := ⟨O, hO, k₁, s₁, σ₁, hrep₁, c, hc.1, hsub, hxc⟩
  refine ⟨toIntr c hxc (subDeriv c f (s₁ a) z₀), ?_, ?_⟩
  · rw [linearization_eq hf d₁]
    exact (mem_support_linSumIntr_iff hsecf hrep₁.1 (fun j => (hrep₁.2.1 j).1) hsub hxc
      _).2 ⟨a, hax, rfl⟩
  · intro φ hφ hxφ m V Tφ hTφ u hu
    rw [reducedTangentFiber_eq (hφ := hφ) (hx := hxφ) (T := Tφ) (hψ := c.isChart)
      (hx' := hxc) (T' := T) hTφ hT] at hu
    have huK : (tangentFiberEquiv c.isChart hxc u : c.φ.model.E 0) ∈ K := by
      have h := hu
      rw [reducedTangentFiber, Submodule.mem_comap, fiberCoord_eq_coe, hφ0c] at h
      exact h
    apply c.fiberLin_injective hxc
    rw [fiberLin_toIntr_subDeriv hft.isScSmooth (hrep₁.2.1 a) hc.1 hsub hxc hax.symm,
      fiberLin_toIntr_subDeriv hft.isScSmooth (hrep₂.2.1 b) hc.1 hsub hxc hb.symm]
    exact (hD _ huK).symm

/-- **General position at a smooth boundary point only depends on the multisection over `∂X`
near the point**: if `Λ₁`, `Λ₂` are sc⁺-multisections which agree over `∂X ∩ Q` for an open
`Q ∋ x` and every operator of `T(f, Λ₁)(x)` is onto on `T^R_xX`, the same holds for `Λ₂`. -/
theorem isReducedOntoAtPt_of_eqOn_boundary {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ₁ Λ₂ : A.W → ℚ≥0} (h₁ : IsScPlusMultisection A Λ₁) (h₂ : IsScPlusMultisection A Λ₂)
    {Q : Set A.Obj} (hQ : IsOpen Q)
    (hagree : ∀ w, A.P w ∈ A.X.PObj.boundary → A.P w ∈ Q → Λ₁ w = Λ₂ w)
    {x : A.X.PObj.Level 1} (hxQ : A.X.PObj.levelVal 1 x ∈ Q)
    (hxb : A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary)
    (hxs : A.X.PObj.levelVal 1 x ∈ A.X.PObj.smoothSet) (H : IsReducedOntoAtPt f Λ₁ x) :
    IsReducedOntoAtPt f Λ₂ x := by
  intro L₂ hL₂ φ hφ hxφ k V T hT w
  obtain ⟨L₁, hL₁, he⟩ :=
    exists_linearization_eqOn_reduced hf hft h₁ h₂ hQ hagree hxQ hxb hxs L₂ hL₂
  obtain ⟨u, hu⟩ := H L₁ hL₁ φ hφ hxφ k V T hT w
  refine ⟨u, ?_⟩
  rw [LinearMap.domRestrict_apply] at hu ⊢
  rw [← he φ hφ hxφ k V T hT u u.2]
  exact hu

/-- **General position at a smooth boundary point only depends on the multisection over `∂X`**:
`isReducedOntoAtPt_of_eqOn_boundary` for multisections which agree over all of `∂X`. -/
theorem isReducedOntoAtPt_of_eq_boundary {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ₁ Λ₂ : A.W → ℚ≥0} (h₁ : IsScPlusMultisection A Λ₁) (h₂ : IsScPlusMultisection A Λ₂)
    (hagree : ∀ w, A.P w ∈ A.X.PObj.boundary → Λ₁ w = Λ₂ w) {x : A.X.PObj.Level 1}
    (hxb : A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary)
    (hxs : A.X.PObj.levelVal 1 x ∈ A.X.PObj.smoothSet) (H : IsReducedOntoAtPt f Λ₁ x) :
    IsReducedOntoAtPt f Λ₂ x :=
  isReducedOntoAtPt_of_eqOn_boundary hf hft h₁ h₂ isOpen_univ (fun w hw _ => hagree w hw)
    (mem_univ _) hxb hxs H

/-- **The boundary hypothesis of Theorem 15.3.9 does not depend on the extension**: for an
sc⁺-multisection `Λ'` on `W` which agrees with `Λ` over `∂X`, `IsBoundaryFaceOnto f Λ` holds iff
`(f, Λ')` is in general position at the smooth points of `supp(Λ ∘ f) ∩ ∂X`. -/
theorem isBoundaryFaceOnto_iff {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ Λ' : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection A Λ')
    (hext : ∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ w) :
    IsBoundaryFaceOnto f Λ ↔
      ∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary →
        A.X.PObj.levelVal 1 x ∈ A.X.PObj.smoothSet → 0 < Λ (f (A.X.PObj.levelVal 1 x)) →
          IsReducedOntoAtPt f Λ' x :=
  ⟨fun H => H Λ' hΛ' hext, fun H _ hΛ'' hext'' x hxb hxs hpos =>
    isReducedOntoAtPt_of_eq_boundary hf hft hΛ' hΛ''
      (fun w hw => (hext w hw).trans (hext'' w hw).symm) hxb hxs (H x hxb hxs hpos)⟩

/-- **Theorem 15.3.9 (Transversal Extension Theorem), p. 694, with the boundary hypothesis for
one extension**: as `theorem_15_3_9`, with "`T(f|∂X, Λ)` onto with respect to the intersections
of local faces" checked on one sc⁺-multisection `Λᵉ` on `W` which agrees with `Λ` over `∂X`
(general position of `(f, Λᵉ)` at the smooth points of `supp(Λ ∘ f) ∩ ∂X`). -/
theorem theorem_15_3_9_of_one_extension (hX : A.X.IsTame) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.PObj.AdmitsScPartitionsOfUnity) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) {Λ : A.W → ℚ≥0} (hΛ : IsBoundaryStructurable A Λ)
    (hdomU : boundaryDomSupp Λ ⊆ U) (hN1 : ∀ x ∈ A.X.PObj.boundary, pointwiseNorm N Λ x ≤ 1)
    {h : A.Obj → ℝ} (hc : Continuous h) (hfun : ∀ φ, h (A.X.src φ) = h (A.X.tgt φ))
    (hh : ∀ x, 0 < h x ∧ h x ≤ 1) (hNh : ∀ x ∈ A.X.PObj.boundary, pointwiseNorm N Λ x < h x)
    {Λe : A.W → ℚ≥0} (hΛe : IsScPlusMultisection A Λe)
    (hext : ∀ w, A.P w ∈ A.X.PObj.boundary → Λe w = Λ w)
    (hon : ∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary →
      A.X.PObj.levelVal 1 x ∈ A.X.PObj.smoothSet → 0 < Λ (f (A.X.PObj.levelVal 1 x)) →
        IsReducedOntoAtPt f Λe x) :
    ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧ (∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ w) ∧
      domSupp Λ' ⊆ U ∧ (∀ x, pointwiseNorm N Λ' x < h x) ∧ IsAdmissible A f N U Λ' ∧
      IsTransversal f Λ' ∧ A.X.IsBranchedEpSubgroupoid (fun z => (Λ' (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ' (f z) : ℚ)) :=
  theorem_15_3_9 hX hpara hPU f hf hft hS N U hcc Λ hΛ hdomU hN1 h hc hfun hh hNh
    ((isBoundaryFaceOnto_iff hf hft hΛe hext).2 hon)

end Bundle

end SBLocalization

end Polyfold
