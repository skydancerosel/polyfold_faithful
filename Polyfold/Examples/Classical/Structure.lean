import Polyfold.Examples.Classical.Setup
import Polyfold.Chapter16.CircleSectionPolyfold
import Polyfold.Chapter17.BundleModelStructure
import Polyfold.Chapter18.OrientationWitness
import Polyfold.Chapter16.OrientationNonEffectiveWitness
import Polyfold.Chapter16.CircleSectionCobordism
import Polyfold.Chapter16.IndexZeroNoBumpsUnconditional

/-!
# The classical reduction: the structure of `G ⋉ ℝⁿ`

Setting for the comparison of Theorem 16.6.6, 2021 p. 739 (index `0`) with the classical count
of a proper equivariant map in finite dimensions, for a finite group `G` acting linearly on
`ℝⁿ`, not necessarily faithfully.  `K = ker ρ` (`baseKernel G n`) is the subgroup acting as the
identity on `ℝⁿ`; `σ` is an arbitrary linear fibre action, with no condition on `σ|K`.

## What is formalized (namespace `Polyfold.Examples.Classical`)

* `isEffective_XG` (Definition 7.2.1), `trivialSubgroup_XG`: for a faithful action
  (`[FaithfulSMul G (Fin n → ℝ)]`) the ep-groupoid is effective and every `T_x` is trivial.

* `Γ_eq`, `Φ_eq`: in every natural representation of `G_x` in `G ⋉ ℝⁿ`,
  `Γ(g, y) = (g, y)` and `Φ(g)(y) = g • y` (`U(x)` is connected and `G` is discrete).
* `mem_trivialSubgroup_iff`: `T_x = {g ∈ G_x | g ∈ K}` (2021 p. 241); `card_trivialSubgroup`,
  and `card_effIsotropy`: `♯G_x^eff · ♯K = ♯Stab_G(x)`.
* `isZhou_XG` (Definition 7.4.5, 2021 p. 331): an isotropy acting as the identity on `T_xℝⁿ`
  lies in `K`, hence in `T_x`.  (LR) of `G ⋉ ℝⁿ` follows by Proposition 7.4.22.
* **`isLRLocal_EG`** (Definition 8.4.2, 2021 p. 382, `EpStrongBundle.IsLRLocal`), proved
  directly, without Proposition 8.4.3 and with no condition on `σ|K`: an orbit-preserving strong
  bundle isomorphism `Φ` of `W|U(x)` covers `y ↦ g₀ • y` (by (LR) of the base); at a point
  `y₀ ∈ U(x)` with stabilizer `K` (`exists_regular_mem`) its fibre map is a linear map whose
  value at every vector is `σ(g₀ k) v` for some `k ∈ K`, hence `σ(g₀ k)` for one `k`
  (`exists_eq_forall_of_forall_exists`, Baire); for every `v` the second component
  `y ↦ (Φ(y, v))₂` is continuous with values in the finite set `{σ(h) v}`, hence constant on the
  connected `U(x)`.  So `Φ = (g₀ k) ∗ ·` on `W|U(x)`.
* `clStructure σ`, `clBundle σ`, `clRep`, `clFredholmSection`, `clBundle_boundary_eq_empty` and
  the standing data of Theorem 16.6.6.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical

open TrivialBundle EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure StrongBundleEquivalenceExamples
  StrongBundleLocalizationExamples

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]

/-! ### The kernel `K` of the action -/

variable (G n) in
/-- **`K = ker ρ`**: the elements of `G` acting as the identity on `ℝⁿ`. -/
def baseKernel : Subgroup G where
  carrier := {g | ∀ z : Fin n → ℝ, g • z = z}
  mul_mem' {g h} hg hh z := by
    rw [mul_smul, hh z, hg z]
  one_mem' z := one_smul G z
  inv_mem' {g} hg z := by
    conv_lhs => rw [← hg z]
    exact inv_smul_smul g z

theorem mem_baseKernel {g : G} : g ∈ baseKernel G n ↔ ∀ z : Fin n → ℝ, g • z = z := Iff.rfl

/-- The fixed vectors of `g` as a submodule. -/
def fixSubmodule (g : G) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker ((rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) - LinearMap.id)

theorem mem_fixSubmodule {g : G} {z : Fin n → ℝ} : z ∈ fixSubmodule g ↔ g • z = z := by
  change (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) z - z = 0 ↔ _
  rw [sub_eq_zero]
  rfl

/-- An element fixing every point of a nonempty open set lies in `K`. -/
theorem mem_baseKernel_of_isOpen {g : G} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hne : U.Nonempty) (h : ∀ y ∈ U, g • y = y) : g ∈ baseKernel G n := by
  have hsub : U ⊆ (fixSubmodule (n := n) g : Set (Fin n → ℝ)) := fun y hy =>
    mem_fixSubmodule.2 (h y hy)
  have htop := (fixSubmodule (n := n) g).eq_top_of_nonempty_interior'
    (hne.mono (interior_maximal hsub hU))
  intro z
  exact mem_fixSubmodule.1 (htop ▸ Submodule.mem_top : z ∈ fixSubmodule (n := n) g)

/-- **Points with stabilizer `K` are dense**: every nonempty open set contains a point `y` with
`h • y = y → h ∈ K`. -/
theorem exists_regular_mem {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ y ∈ U, ∀ h : G, h • y = y → h ∈ baseKernel G n := by
  let F : {h : G // h ∉ baseKernel G n} → Set (Fin n → ℝ) :=
    fun h => (fixSubmodule (n := n) h.1 : Set (Fin n → ℝ))ᶜ
  have hclosed : ∀ h : G, IsClosed (fixSubmodule (n := n) h : Set (Fin n → ℝ)) := fun h => by
    have : (fixSubmodule (n := n) h : Set (Fin n → ℝ)) = {z | (rhoL h) z = z} :=
      Set.ext fun z => mem_fixSubmodule
    rw [this]
    exact isClosed_eq (rhoL h).continuous continuous_id
  have hopen : ∀ h, IsOpen (F h) := fun h => (hclosed h.1).isOpen_compl
  have hdense : ∀ h, Dense (F h) := fun h => by
    refine interior_eq_empty_iff_dense_compl.1 ?_
    by_contra hne'
    refine h.2 fun z => ?_
    have htop := (fixSubmodule (n := n) h.1).eq_top_of_nonempty_interior'
      (nonempty_iff_ne_empty.2 hne')
    exact mem_fixSubmodule.1 (htop ▸ Submodule.mem_top : z ∈ fixSubmodule (n := n) h.1)
  obtain ⟨y, hyU, hyD⟩ := (dense_iInter_of_isOpen hopen hdense).inter_open_nonempty U hU hne
  refine ⟨y, hyU, fun h hh => ?_⟩
  by_contra hk
  exact (mem_iInter.1 hyD ⟨h, hk⟩) (mem_fixSubmodule.2 hh)

/-- **A linear map of `ℝⁿ` whose value at every vector is the value of one of finitely many
continuous linear maps is one of them** (`ℝⁿ` is not a finite union of proper subspaces). -/
theorem exists_eq_forall_of_forall_exists {ι : Type*} [Finite ι]
    (ℓ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (A : ι → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (h : ∀ v, ∃ i, ℓ v = A i v) : ∃ i, ∀ v, ℓ v = A i v := by
  let S : ι → Submodule ℝ (Fin n → ℝ) := fun i =>
    LinearMap.ker (ℓ - (A i : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
  have hmem : ∀ i v, v ∈ S i ↔ ℓ v = A i v := fun i v => by
    change ℓ v - A i v = 0 ↔ _
    rw [sub_eq_zero]
  have hℓ : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  have hclosed : ∀ i, IsClosed (S i : Set (Fin n → ℝ)) := fun i => by
    have : (S i : Set (Fin n → ℝ)) = {v | ℓ v = A i v} := Set.ext fun v => hmem i v
    rw [this]
    exact isClosed_eq hℓ (A i).continuous
  have hcov : ⋃ i, (S i : Set (Fin n → ℝ)) = univ :=
    eq_univ_of_forall fun v => let ⟨i, hi⟩ := h v; mem_iUnion.2 ⟨i, (hmem i v).2 hi⟩
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcov
  have htop := (S i).eq_top_of_nonempty_interior' hi
  exact ⟨i, fun v => (hmem i v).1 (htop ▸ Submodule.mem_top)⟩

/-! ### Natural representations of `G ⋉ ℝⁿ` -/

/-- **In a natural representation of `G_x`, `Γ(g, y) = (g, y)`**: `y ↦ Γ(g, y)₁` is continuous
with values in the discrete `G` on the connected `U(x)`, and `Γ(g, x) = g`. -/
theorem Γ_eq {x : Fin n → ℝ} (R : (XG G n).NaturalRep x) (g : (XG G n).Isotropy x)
    {y : Fin n → ℝ} (hy : y ∈ R.U) : R.Γ g y = (g.val.1, y) := by
  have hc : ContinuousOn (fun y => (R.Γ g y).1) R.U :=
    continuous_fst.comp_continuousOn (R.isScSmoothOn_Γ g).continuousOn
  have h1 : (R.Γ g y).1 = (R.Γ g x).1 :=
    R.isConnected_U.isPreconnected.constant hc hy R.mem_U
  rw [R.Γ_self] at h1
  exact Prod.ext h1 (R.src_Γ g y hy)

/-- In a natural representation of `G_x`, `Φ(g)(y) = g • y`. -/
theorem Φ_eq {x : Fin n → ℝ} (R : (XG G n).NaturalRep x) (g : (XG G n).Isotropy x)
    {y : Fin n → ℝ} (hy : y ∈ R.U) : R.Φ g y = g.val.1 • y := by
  rw [← R.tgt_Γ g y hy, Γ_eq R g hy]
  rfl

/-- The group element of an isotropy morphism of `x` fixes `x`. -/
theorem fst_smul_eq {x : Fin n → ℝ} (g : (XG G n).Isotropy x) : g.val.1 • x = x := by
  have h2 : g.val.2 = x := g.src_val
  have ht : g.val.1 • g.val.2 = x := g.tgt_val
  rwa [h2] at ht

/-- **`T_x = {g ∈ G_x | g ∈ K}`** (2021 p. 241). -/
theorem mem_trivialSubgroup_iff {x : Fin n → ℝ} (g : (XG G n).Isotropy x) :
    g ∈ (XG G n).trivialSubgroup x ↔ g.val.1 ∈ baseKernel G n := by
  constructor
  · rintro ⟨R, hR⟩
    exact mem_baseKernel_of_isOpen R.isOpen_U ⟨x, R.mem_U⟩ fun y hy =>
      (Φ_eq R g hy).symm.trans (hR y hy)
  · intro hk
    obtain ⟨R, -⟩ := (XG G n).theorem_7_1_13 x isOpen_univ (mem_univ x)
    exact ⟨R, fun y hy => (Φ_eq R g hy).trans (hk y)⟩

variable (G) in
/-- `T_x ≃ K`, `g ↦ g₁`. -/
def trivialSubgroupEquiv (x : Fin n → ℝ) : (XG G n).trivialSubgroup x ≃ baseKernel G n where
  toFun g := ⟨g.1.val.1, (mem_trivialSubgroup_iff g.1).1 g.2⟩
  invFun k := ⟨⟨(k.1, x), rfl, k.2 x⟩, (mem_trivialSubgroup_iff _).2 k.2⟩
  left_inv g := Subtype.ext (GroupoidStr.Isotropy.ext (Prod.ext rfl g.1.src_val.symm))
  right_inv _ := rfl

variable (G) in
/-- `♯T_x = ♯K`. -/
theorem card_trivialSubgroup (x : Fin n → ℝ) :
    Nat.card ((XG G n).trivialSubgroup x) = Nat.card (baseKernel G n) :=
  Nat.card_congr (trivialSubgroupEquiv G x)

variable (G) in
/-- `♯G_x = ♯Stab_G(x)`. -/
theorem card_isotropy (x : Fin n → ℝ) :
    Nat.card ((XG G n).Isotropy x) = Nat.card (MulAction.stabilizer G x) :=
  Nat.card_congr (isotropyEquivStabilizer (isScSmoothMap_smul (G := G)) x).toEquiv

variable (G) in
/-- **`♯G_x^eff · ♯K = ♯Stab_G(x)`**, `G_x^eff = G_x / T_x`. -/
theorem card_effIsotropy (x : Fin n → ℝ) :
    Nat.card ((XG G n).EffIsotropy x) * Nat.card (baseKernel G n) =
      Nat.card (MulAction.stabilizer G x) := by
  rw [← card_isotropy G x, ← card_trivialSubgroup G x,
    Subgroup.card_eq_card_quotient_mul_card_subgroup ((XG G n).trivialSubgroup x),
    Nat.card_congr ((XG G n).effIsotropyEquiv x).toEquiv]

/-! ### (ZHOU) -/

/-- The vector `(0, w)` of `T_xℝⁿ` in the chart `y ↦ y − x`. -/
def baseVec (x w : Fin n → ℝ) : (rnChart n x).model.E.tangent 0 := ((0 : Fin n → ℝ), w)

theorem baseVec_mem (x w : Fin n → ℝ) :
    baseVec x w ∈ retractTangent (rnChart n x).model.E (rnChart n x).model.C
      (rnChart n x).model.O := by
  change baseVec x w ∈ retractTangent (rnSc n) univ univ
  rw [retractTangent_univ]
  exact mem_univ _

/-- `[x, y ↦ y − x, w] ∈ T_xℝⁿ`. -/
def baseTangent (x w : Fin n → ℝ) : (rnPolyfold n).TangentSpace :=
  TangentSpace.mk (TangentPre.ofVec (isChart_rnChart x) (baseVec_mem x w))

theorem levelVal_tangentProj_baseTangent (x w : Fin n → ℝ) :
    (rnPolyfold n).levelVal 1 ((rnPolyfold n).tangentProj (baseTangent x w)) = x := by
  change (rnChart n x).symm ((rnChart n x).model.E.toBase 1 0) = x
  rw [map_zero]
  exact zero_add x

theorem tangentChartMap_baseTangent (x w : Fin n → ℝ) :
    tangentChartMap (isChart_rnChart x) (baseTangent x w) = baseVec x w :=
  tangentChartMap_mk_ofVec _ (baseVec_mem x w)

/-- For `g • x = x`, `T(g •)` sends `(0, w)` to `(0, g • w)` in the chart `y ↦ y − x`. -/
theorem tangentChartMap_tangentMap_smul {g : G} {x : Fin n → ℝ} (hgx : g • x = x)
    (w : Fin n → ℝ) :
    tangentChartMap (isChart_rnChart x)
        (MPolyfold.tangentMap (isScSmoothMap_smul g) (baseTangent x w)) =
      ((0 : Fin n → ℝ), g • w) := by
  rw [tangentChartMap_tangentMap_of_linear (isScSmoothMap_smul g) (isChart_rnChart x)
    (isChart_rnChart x) (ScOperator.ofConst (rhoL g))
    (fun _ _ => mem_univ _) (fun y _ => ?_) (mem_univ _), tangentChartMap_baseTangent]
  · refine Prod.ext ?_ rfl
    change rhoL g (0 : Fin n → ℝ) = 0
    exact map_zero _
  · change g • y - x = rhoL g (y - x)
    rw [rhoL_apply, smul_sub, hgx]

/-- **(ZHOU) for `G ⋉ ℝⁿ`** (2021 Definition 7.4.5, p. 331), for an action that need not be
faithful: an isotropy `g` of `x` acting as the identity on `T_xℝⁿ` fixes every vector (its
tangent map is the linear map `g •`), so `g ∈ K`, and `K ⊆ T_x`. -/
theorem isZhou_XG : (XG G n).IsZhou := by
  intro y g hg
  rw [mem_trivialSubgroup_iff]
  intro w
  set x := (rnPolyfold n).smoothVal y with hxdef
  have h2 : g.val.2 = x := g.src_val
  have ht : g.val.1 • x = x := fst_smul_eq g
  have hv : baseTangent x w ∈
      (rnPolyfold n).tangentFiber ((rnPolyfold n).smoothIncl y 1) := by
    change (rnPolyfold n).tangentProj (baseTangent x w) = _
    refine level_ext ?_
    exact levelVal_tangentProj_baseTangent x w
  have e1 := hg (baseTangent x w) hv
  have hval : g.val = (g.val.1, (rnPolyfold n).levelVal 1
      ((rnPolyfold n).tangentProj (baseTangent x w))) :=
    Prod.ext rfl (h2.trans (levelVal_tangentProj_baseTangent x w).symm)
  rw [hval] at e1
  replace e1 : MPolyfold.tangentMap (isScSmoothMap_smul g.val.1) (baseTangent x w) =
      baseTangent x w :=
    (tangentMor_actionEpGroupoid isScSmoothMap_smul
      (φ := (g.val.1, (rnPolyfold n).levelVal 1 ((rnPolyfold n).tangentProj (baseTangent x w))))
      (((XG G n).mem_levelSet_src_iff _ 1).1 (MPolyfold.levelVal_mem _))
      (α := baseTangent x w) rfl).symm.trans e1
  have h4 := congrArg (tangentChartMap (isChart_rnChart x)) e1
  rw [tangentChartMap_tangentMap_smul ht, tangentChartMap_baseTangent] at h4
  exact congrArg Prod.snd h4

/-! ### The local regularity of the bundle -/

/-- `|G ⋉ ℝⁿ| = ℝⁿ/G` is paracompact. -/
theorem hasParacompactOrbitSpace_XG : (XG G n).HasParacompactOrbitSpace :=
  hasParacompactOrbitSpace_action isScSmoothMap_smul

variable (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))

/-- `g ∗ w = (g₁ • w₁, σ(g₁) w₂)` in every natural representation. -/
theorem natLift_eq {x : Fin n → ℝ} (R : (XG G n).NaturalRep x) (g : (XG G n).Isotropy x)
    (w : (Fin n → ℝ) × (Fin n → ℝ)) (hw : proj n n w ∈ R.U) :
    (EG σ).natLift R g w hw = actW σ g.val.1 w := by
  change actW σ (R.Γ g (proj n n w)).1 w = _
  rw [Γ_eq R g hw]

/-- Two points of `ℝⁿ × ℝⁿ` with the same orbit differ by the action of an element of `G`. -/
theorem exists_eq_actW_of_π_eq {w w' : (Fin n → ℝ) × (Fin n → ℝ)}
    (h : (EG σ).toGroupoidStr.π w' = (EG σ).toGroupoidStr.π w) :
    ∃ k : G, w' = actW σ k w := by
  obtain ⟨q, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 h
  refine ⟨(q : (G × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ))).1.1⁻¹, ?_⟩
  have hs' : (q : (G × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ))).2 = w' := hs
  have ht' : actW σ (q : (G × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ))).1.1
      (q : (G × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ))).2 = w := ht
  rw [← ht', hs', actW_inv_actW]

/-- **The local regularity property of `ℝⁿ × ℝⁿ → ℝⁿ` over `G ⋉ ℝⁿ`** (2021 Definition 8.4.2,
p. 382, in the form `EpStrongBundle.IsLRLocal`), for an action that need not be faithful and an
arbitrary fibre action `σ`.  Proved directly: no effectiveness and no Proposition 8.4.3. -/
theorem isLRLocal_EG : (EG σ).IsLRLocal := by
  intro x O hO hxO
  obtain ⟨R, hRO, hR⟩ := (XG G n).proposition_7_4_22_of_isZhou isZhou_XG x O hO hxO
  refine ⟨R, hRO, fun β Φ hΦ hπ => ?_⟩
  have hmor : ∀ w, proj n n w ∈ R.U → ∃ k : G, Φ w = actW σ k w := fun w hw =>
    exists_eq_actW_of_π_eq σ (hπ w hw)
  have hcov : ∀ w, proj n n w ∈ R.U → (Φ w).1 = β w.1 := fun w hw => hΦ.covers hw
  -- `β` preserves orbits, so `β = g₀ •` on `U(x)` by (LR) of `G ⋉ ℝⁿ`
  have hβk : ∀ y ∈ R.U, ∃ k : G, β y = k • y := fun y hy => by
    obtain ⟨k, hk⟩ := hmor (y, 0) hy
    exact ⟨k, (hcov (y, 0) hy).symm.trans (congrArg Prod.fst hk)⟩
  have hβπ : ∀ y ∈ R.U, (XG G n).π (β y) = (XG G n).π y := fun y hy => by
    obtain ⟨k, hk⟩ := hβk y hy
    refine (action_π_eq_π_iff isScSmoothMap_smul).2 ⟨k⁻¹, ?_⟩
    rw [hk, inv_smul_smul]
  obtain ⟨β', hβ⟩ := hΦ.isScDiffeoOn_base
  obtain ⟨g₀, hg₀⟩ := hR β β' hβ hβπ
  have hβg : ∀ y ∈ R.U, β y = g₀.val.1 • y := fun y hy => (hg₀ y hy).trans (Φ_eq R g₀ hy)
  -- the fibre map at a point `y₀` with stabilizer `K` is `σ(g₀ k)` for one `k ∈ K`
  obtain ⟨y₀, hy₀, hreg⟩ := exists_regular_mem (G := G) R.isOpen_U ⟨x, R.mem_U⟩
  obtain ⟨L, hL⟩ := hΦ.fiber_linear y₀ hy₀
  let ℓ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    ((fibEquiv (n := n) (k := n) (β y₀)).linearEquiv ℝ).toLinearMap ∘ₗ L ∘ₗ
      ((fibEquiv (n := n) (k := n) y₀).linearEquiv ℝ).symm.toLinearMap
  have hℓ : ∀ v, ℓ v = (Φ (y₀, v)).2 := fun v => by
    have h := hL ((fibEquiv (n := n) (k := n) y₀).symm v)
    change ((L ((fibEquiv (n := n) (k := n) y₀).symm v) : (Fin n → ℝ) × (Fin n → ℝ))).2 = _
    rw [h]
    rfl
  have hex : ∀ v, ∃ k : baseKernel G n, ℓ v = σ (g₀.val.1 * k) v := fun v => by
    obtain ⟨h, hh⟩ := hmor (y₀, v) hy₀
    have h1 : h • y₀ = g₀.val.1 • y₀ :=
      (congrArg Prod.fst hh).symm.trans ((hcov (y₀, v) hy₀).trans (hβg y₀ hy₀))
    have hk : g₀.val.1⁻¹ * h ∈ baseKernel G n := hreg _ (by rw [mul_smul, h1, inv_smul_smul])
    refine ⟨⟨_, hk⟩, ?_⟩
    rw [hℓ, hh, mul_inv_cancel_left]
    rfl
  obtain ⟨k, hkℓ⟩ := exists_eq_forall_of_forall_exists ℓ
    (fun k : baseKernel G n => σ (g₀.val.1 * k)) hex
  set a := g₀.val.1 * (k : G) with ha
  have hax : ∀ z : Fin n → ℝ, a • z = g₀.val.1 • z := fun z => by
    rw [ha, mul_smul, k.2 z]
  -- `Φ = a ∗ ·` on `W|U(x)`
  have hΦc : ContinuousOn Φ (proj n n ⁻¹' R.U) := by
    obtain ⟨Ψ, hΨ⟩ := hΦ.isScDiffeoOn_zero
    exact hΨ.isScSmoothOn.continuousOn
  have hsnd : ∀ y ∈ R.U, ∀ v, (Φ (y, v)).2 = σ a v := fun y hy v => by
    have hc : ContinuousOn (fun y' => (Φ (y', v)).2) R.U :=
      continuous_snd.comp_continuousOn
        (hΦc.comp (continuous_id.prodMk continuous_const).continuousOn fun y' hy' => hy')
    have hmaps : MapsTo (fun y' => (Φ (y', v)).2) R.U (range fun h : G => σ h v) :=
      fun y' hy' => by
        obtain ⟨h, hh⟩ := hmor (y', v) hy'
        exact ⟨h, (congrArg Prod.snd hh).symm⟩
    have hd : IsDiscrete (range fun h : G => σ h v) := (finite_range _).isDiscrete
    refine (R.isConnected_U.isPreconnected.constant_of_mapsTo hd hc hmaps hy hy₀).trans ?_
    rw [← hℓ, hkℓ]
  have hgx : a • x = x := by rw [hax]; exact fst_smul_eq g₀
  refine ⟨⟨(a, x), rfl, hgx⟩, fun w hw => ?_⟩
  rw [natLift_eq σ R _ w hw]
  refine Prod.ext ?_ ?_
  · change (Φ w).1 = a • w.1
    rw [hcov w hw, hβg w.1 hw, hax]
  · change (Φ w).2 = σ a w.2
    exact hsnd w.1 hw w.2

/-! ### The structure -/

/-- **The strong polyfold bundle structure** `((P : ℝⁿ × ℝⁿ → ℝⁿ, μ), id, id)` over `G ⋉ ℝⁿ`
(Definition 16.3.1), for `p = |P|`, for an action that need not be faithful. -/
def clStructure : StrongPolyfoldBundleStructure (AG σ).E.projFunctor.orbitMap where
  A := AG σ
  isZhou := isZhou_XG
  paracompact := hasParacompactOrbitSpace_XG
  isLRLocal := isLRLocal_EG σ
  Γ := Homeomorph.refl _
  γ := Homeomorph.refl _
  comm := rfl

/-- **The strong polyfold bundle `|ℝⁿ × ℝⁿ| → ℝⁿ/G`** (Definition 16.3.4). -/
def clBundle : StrongPolyfoldBundle (AG σ).E.projFunctor.orbitMap := ⟦clStructure σ⟧

variable {σ}

/-- `|f|` is well defined on `ℝⁿ/G`. -/
theorem π_fSec_eq {φ : (Fin n → ℝ) → (Fin n → ℝ)} (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    {x y : Fin n → ℝ} (h : (XG G n).π x = (XG G n).π y) :
    (AG σ).E.toEpGroupoid.π (fSec φ x) = (AG σ).E.toEpGroupoid.π (fSec φ y) := by
  obtain ⟨k, rfl⟩ := (action_π_eq_π_iff isScSmoothMap_smul).1 h
  refine (GroupoidStr.π_eq_π_iff _).2 ⟨⟨((k, x), fSec φ x), rfl⟩, rfl, ?_⟩
  exact (fSec_smul heq k x).symm

variable (σ) in
/-- **The representative `(clStructure σ, f)`** of the section `|x| ↦ |(x, φ x)|`
(Definition 16.3.18). -/
def clRep {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) : SectionRep (clBundle σ) where
  S := clStructure σ
  hS := rfl
  F := fSec φ
  hF := (isScFredholmSectionFunctor_fSec hφ heq).1
  f := Quotient.lift (fun x : Fin n → ℝ => (AG σ).E.toEpGroupoid.π (fSec φ x))
    fun _ _ h => π_fSec_eq heq (Quotient.sound h)
  continuous_f := Continuous.quotient_lift ((AG σ).E.toEpGroupoid.continuous_π.comp
    (continuous_id.prodMk hφ.continuous)) _
  isSection z := Quotient.inductionOn z fun _ => rfl
  comm _ := rfl

variable (σ) in
/-- **The sc-Fredholm section `|x| ↦ |(x, φ x)|`** of `clBundle σ` (Definition 16.6.1). -/
def clFredholmSection {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) : FredholmSection (clBundle σ) :=
  ⟨⟦clRep σ hφ heq⟧, clRep σ hφ heq, rfl, isScFredholmSectionFunctor_fSec hφ heq⟩

variable (σ) in
/-- **`ℝⁿ/G` has no boundary.** -/
theorem clBundle_boundary_eq_empty : (clBundle σ).polyfold.boundary = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
  obtain ⟨x, rfl⟩ := (clStructure σ).surjective_γπ z
  have hx := (mem_boundary_iff_obj (c := clBundle σ) rfl x).1 hz
  have h : (0 : ℕ) < (rnPolyfold n).degIndex x := hx
  have h0 : (rnPolyfold n).degIndex x = 0 := MPolyfold.degIndex_rn x
  omega

/-! ### The standing data of Theorem 16.6.6 -/

variable (σ) in
theorem mem_smoothSet_AG (x : (AG σ).Obj) : x ∈ (AG σ).X.PObj.smoothSet := by
  have h : (rnPolyfold n).smoothSet = univ := rnPolyfold_smoothSet
  exact h ▸ mem_univ x

variable (σ) in
theorem isTame_AG : (AG σ).X.PObj.IsTame := rnPolyfold_isTame

variable (σ) in
theorem admitsBumpFunctions_AG : (AG σ).X.PObj.AdmitsBumpFunctions := admitsBumpFunctions_rn n

variable (σ) in
theorem hasScPlusSectionsThrough_AG : (AG σ).B.HasScPlusSectionsThrough :=
  hasScPlusSectionsThrough_epSEP n n

variable (σ) in
/-- `f` has tame germ data (Definition 3.6.4). -/
theorem isScFredholmSectionTame_fSec {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ) :
    (AG σ).B.IsScFredholmSectionTame (fSec φ) :=
  isScFredholmSectionTame_graphSection hφ

variable (σ) in
/-- **The Fredholm index of `f` is `0`** at every point. -/
theorem isIndexAt_fSec {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ) (x : (AG σ).Obj) :
    (AG σ).B.IsIndexAt (fSec φ) x 0 := by
  have h := isIndexAt_graphSection_epSEP (n := n) (k := n) hφ x
  have h0 : ((n : ℕ) : ℤ) - ((n : ℕ) : ℤ) = 0 := by omega
  rw [h0] at h
  exact h

/-! ### Faithful actions: effectiveness -/

section Faithful

variable [FaithfulSMul G (Fin n → ℝ)]

/-- For `g ≠ 1` some vector is moved by `g`. -/
theorem exists_smul_ne {g : G} (hg : g ≠ 1) : ∃ w : Fin n → ℝ, g • w ≠ w := by
  by_contra h
  push Not at h
  exact hg (eq_of_smul_eq_smul fun w => by rw [h w, one_smul])

/-- The group element of an isotropy morphism `≠ 1` is `≠ 1`. -/
theorem fst_ne_one_of_isotropy {x : Fin n → ℝ} (g : (XG G n).Isotropy x) (hg : g ≠ 1) :
    g.val.1 ≠ 1 := fun h =>
  hg (GroupoidStr.Isotropy.ext (Prod.ext h (g.src_val : g.val.2 = x)))

/-- **`G ⋉ ℝⁿ` is effective** (Definition 7.2.1): near `(g, x)`, `g ≠ 1`, there are
`(g, x + t w)`, `t ≠ 0`, with `g • w ≠ w`, and these move their source. -/
theorem isEffective_XG : (XG G n).IsEffective := by
  intro x g hg W hW hgW
  have h2 : g.val.2 = x := g.src_val
  have ht : g.val.1 • g.val.2 = x := g.tgt_val
  rw [h2] at ht
  have h1 := fst_ne_one_of_isotropy g hg
  obtain ⟨w, hw⟩ := exists_smul_ne (n := n) h1
  have hc : Continuous fun t : ℝ => (g.val.1, x + t • w) :=
    continuous_const.prodMk (continuous_const.add (continuous_id.smul continuous_const))
  have hS : IsOpen ((fun t : ℝ => (g.val.1, x + t • w)) ⁻¹' W) := hW.preimage hc
  have h0S : (0 : ℝ) ∈ (fun t : ℝ => (g.val.1, x + t • w)) ⁻¹' W := by
    change (g.val.1, x + (0 : ℝ) • w) ∈ W
    rw [zero_smul, add_zero]
    have hg0 : g.val = (g.val.1, x) := Prod.ext rfl h2
    rw [← hg0]
    exact hgW
  have hN : (fun t : ℝ => (g.val.1, x + t • w)) ⁻¹' W ∈ 𝓝[≠] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (hS.mem_nhds h0S)
  obtain ⟨t, htW, ht0⟩ := Filter.nonempty_of_mem (inter_mem hN self_mem_nhdsWithin)
  refine ⟨(g.val.1, x + t • w), htW, ?_⟩
  change x + t • w ≠ g.val.1 • (x + t • w)
  intro h
  rw [smul_add, ht, smul_comm] at h
  exact hw (smul_right_injective _ (ht0 : t ≠ 0) (add_left_cancel h).symm)

/-- Every `T_x` is trivial. -/
theorem trivialSubgroup_XG (x : Fin n → ℝ) : (XG G n).trivialSubgroup x = ⊥ :=
  (XG G n).isEffective_iff_trivialSubgroup_eq_bot.1 (isEffective_XG (G := G) (n := n)) x

end Faithful

end Polyfold.Examples.Classical
