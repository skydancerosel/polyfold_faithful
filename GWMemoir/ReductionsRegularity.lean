import GWMemoir.Reductions
import GWMemoir.RecollectionsFredholm
import Polyfold.Chapter19.BasicConstructionExamples
import Polyfold.Chapter17.BundleModelStructure
import Polyfold.Chapter19.MetrizabilityExamples

/-!
# (ZHOU), effectiveness and tameness for uniformizers with faithful actions

Memoir Chapter 3 (the polyfold structure on `Z`), read against 2021 Definitions 19.5.6 (ZHOU for
a basic construction), 7.2.1 (effective ep-groupoids) and 2.5.2/2.5.7 (tame retracts and tame
M-polyfolds).

## What is proved

* `GWMemoir.IsTangentFaithfulAt Ψ y`: `g ∗ ō = ō` and `Tg = id` on `T_ōO` force `g = 1`;
  `isZhouAt_of_isTangentFaithfulAt` (it gives (ZHOU) at `ō`, Definition 19.5.6) and
  `isZhou_of_isTangentFaithfulAt` (for the basic construction).
* `isTangentFaithfulAt_of_separating`: the GW situation.  `G` acts on a set `S` (the domain
  surface) faithfully, a set `E` of maps `S → W` (the space `E_u`) separates the points of `S`
  and is stable under `η ↦ η ∘ g⁻¹`, and an injective map `ι : E → T_ōO` intertwines
  `η ↦ η ∘ g⁻¹` with `Tg`.  Then `Ψ` is tangent-faithful at `ō`.
* `GWMemoir.IsLocallyFaithful Ψ`: no `g ≠ 1` is the identity near a point.
  `isEffective_model`: the model `X_Ψ` of a family of locally faithful uniformizers is effective
  (Definition 7.2.1), and `isEffective_toPolyfoldConstruction`: the polyfold construction of a
  basic construction all of whose uniformizers are locally faithful is effective.
* `isTame_of_forall_C_eq_univ`: an M-polyfold whose charts are modelled on open subsets of
  sc-Banach spaces (`C = E`, so `d ≡ 0`) is tame (Definition 2.5.7, through
  `GWMemoir.isTame_of_eq_univ`).
* Witnesses: the hypotheses of `GWMemoir.reduction_3_13` for every translation groupoid
  `G ⋉ O` (`thm313_keyCS`, `csClosed_keyCS`, `pointFinite_translationUnif`); for `ℤ/2 ⋉ ℝ`
  (`ℤ/2` acting by reflection) tangent-faithfulness at every smooth point, (ZHOU) for the basic
  construction, local faithfulness and effectiveness, and tameness of `ℝ`.

## Readings

* (ZHOU) at `ō` asks only that `g` be the identity near `ō`; tangent-faithfulness gives `g = 1`,
  which is the form the memoir's argument yields.
* Effectiveness is read for the polyfold construction (`S.IsEffective`, some model `X_Ψ` is
  effective).  Local faithfulness is stated directly; in the GW case it follows from the faithful
  action of the automorphism group on the domain, as for tangent-faithfulness.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter
open Polyfold Polyfold.GroupoidalCategory

noncomputable section

namespace GWMemoir

universe u

open GroupoidStr (TransitionSet)

/-! ### Tangent-faithfulness and (ZHOU) -/

section Zhou

variable {C : GroupoidalCategory.{u}} (Ψ : C.Uniformizer)

/-- `Ψ` is **tangent-faithful at `ō`**: an element of `G` fixing `ō` with `Tg = id` on `T_ōO` is
the identity. -/
def IsTangentFaithfulAt (y : Ψ.P.SmoothLevel) : Prop :=
  ∀ g : Ψ.G, g • Ψ.P.smoothVal y = Ψ.P.smoothVal y →
    (∀ v ∈ Ψ.P.tangentFiber (Ψ.P.smoothIncl y 1), Ψ.tangentSmul g v = v) → g = 1

variable {Ψ}

/-- Tangent-faithfulness at `ō` gives (ZHOU) at `ō` (2021 Definition 19.5.6). -/
theorem isZhouAt_of_isTangentFaithfulAt {y : Ψ.P.SmoothLevel} (h : IsTangentFaithfulAt Ψ y) :
    Ψ.IsZhouAt y := fun g hg hT => by
  rw [h g hg hT]
  exact Eventually.of_forall fun q => one_smul _ q

/-- **The GW form of tangent-faithfulness**: `G` acts faithfully on `S`, the maps `η ∈ E`
separate the points of `S`, `E` is stable under `η ↦ η ∘ g⁻¹`, and `ι : E → T_ōO` is injective
and intertwines `η ↦ η ∘ g⁻¹` with `Tg` for `g` fixing `ō`. -/
theorem isTangentFaithfulAt_of_separating {y : Ψ.P.SmoothLevel} {S W : Type*}
    [MulAction Ψ.G S] [FaithfulSMul Ψ.G S] (E : Set (S → W))
    (hsep : ∀ x x' : S, x ≠ x' → ∃ η ∈ E, η x ≠ η x')
    (hE : ∀ (g : Ψ.G), ∀ η ∈ E, (fun x => η (g⁻¹ • x)) ∈ E)
    (ι : (S → W) → Ψ.P.TangentSpace) (hι : ∀ η ∈ E, ι η ∈ Ψ.P.tangentFiber (Ψ.P.smoothIncl y 1))
    (hinj : InjOn ι E)
    (hequiv : ∀ g : Ψ.G, g • Ψ.P.smoothVal y = Ψ.P.smoothVal y → ∀ η ∈ E,
      Ψ.tangentSmul g (ι η) = ι fun x => η (g⁻¹ • x)) :
    IsTangentFaithfulAt Ψ y := by
  intro g hg hT
  have hη : ∀ η ∈ E, (fun x => η (g⁻¹ • x)) = η := fun η hη =>
    hinj (hE g η hη) hη ((hequiv g hg η hη).symm.trans (hT _ (hι η hη)))
  have hfix : ∀ x : S, g⁻¹ • x = x := fun x => by
    by_contra hx
    obtain ⟨η, hηE, hne⟩ := hsep _ _ hx
    exact hne (congrFun (hη η hηE) x)
  have h1 : g⁻¹ = 1 := eq_of_smul_eq_smul fun x : S => by rw [hfix x, one_smul]
  exact inv_eq_one.1 h1

/-- **(ZHOU) for a basic construction from tangent-faithfulness** (2021 Definition 19.5.6): every
smooth class has a uniformizer through it that is tangent-faithful there. -/
theorem isZhou_of_isTangentFaithfulAt (B : C.BasicConstruction)
    (h : ∀ z, B.IsSmoothClass z → ∃ (α : C.Obj) (Ψ : C.Uniformizer) (_ : Ψ ∈ B.U.F α)
      (y : Ψ.P.SmoothLevel), C.π α = z ∧ Ψ.obj (Ψ.P.smoothVal y) = α ∧ IsTangentFaithfulAt Ψ y) :
    B.IsZhou := fun z hz => by
  obtain ⟨α, Ψ, hΨ, y, h1, h2, h3⟩ := h z hz
  exact ⟨α, Ψ, hΨ, y, h1, h2, isZhouAt_of_isTangentFaithfulAt h3⟩

/-- **(ZHOU) for a basic construction** when every uniformizer of the family is tangent-faithful at
every smooth point and every class meets a uniformizer (Proposition 3.10): the point of `Ψ'`
over a smooth class is smooth, since levels do not depend on the uniformizer. -/
theorem isZhou_of_forall_isTangentFaithfulAt (B : C.BasicConstruction)
    (hB : B.U.HasClassUniformizers)
    (h : ∀ (α : C.Obj), ∀ Ψ ∈ B.U.F α, ∀ y : Ψ.P.SmoothLevel, IsTangentFaithfulAt Ψ y) :
    B.IsZhou := by
  refine isZhou_of_isTangentFaithfulAt B fun z hz => ?_
  obtain ⟨Ψ₀, q, hq, hz⟩ := hz
  obtain ⟨α, hα, Ψ, hΨ⟩ := hB z
  obtain ⟨o, ho⟩ := B.U.isAt α Ψ hΨ
  have hπ : C.π (Ψ₀.1.obj q) = C.π ((⟨Ψ, α, hΨ⟩ : B.U.Unif).1.obj o) := by
    rw [hz, ← hα]
    exact congrArg C.π ho.symm
  have hos : o ∈ Ψ.P.smoothSet := mem_iInter.2 fun m =>
    (B.mem_levelSet_iff_of_π_eq hπ m).1 (mem_iInter.1 hq m)
  exact ⟨α, Ψ, hΨ, ⟨o, hos⟩, hα, ho, h α Ψ hΨ _⟩

end Zhou

/-! ### Local faithfulness and effectiveness -/

section Effective

/-- `Ψ` is **locally faithful**: no `g ≠ 1` is the identity near a point. -/
def IsLocallyFaithful {C : GroupoidalCategory.{u}} (Ψ : C.Uniformizer) : Prop :=
  ∀ (g : Ψ.G) (q : Ψ.O), (∀ᶠ p in 𝓝 q, g • p = p) → g = 1

open GCT.PolyfoldConstruction in
/-- **The model `X_Ψ` of a family of locally faithful uniformizers is effective** (2021
Definition 7.2.1): an isotropy element `g ≠ 1` at `q_λ` is `Ψ̂_λ(k, q)` with `k ≠ 1`
(fullness of `G_λ ⋉ O_λ → X_Ψ`), and every neighbourhood of it contains `Ψ̂_λ(k, p)` with
`k ∗ p ≠ p`. -/
theorem isEffective_model {C : GCT.{u}} {S : C.PolyfoldConstruction} {ι : Type u}
    (Ψ : ι → S.Unif) (hc : ∀ i, Continuous (S.hat (Ψ i)))
    (hf : ∀ i, IsLocallyFaithful (Ψ i).1.toUniformizer) : (S.modelEP Ψ).X.IsEffective := by
  rintro ⟨i, q⟩ g hg W hW hgW
  set F := pieceFunctor Ψ i (hc i)
  obtain ⟨φ, hφs, hφt, hφ⟩ := (GroupoidFunctor.full_iff F.toGroupoidFunctor).1
    (full_pieceFunctor Ψ i (hc i)) q q g.val g.src_val g.tgt_val
  obtain ⟨k, q₁⟩ := φ
  change q₁ = q at hφs
  subst hφs
  have hk : k ≠ 1 := by
    rintro rfl
    apply hg
    refine GroupoidStr.Isotropy.ext ?_
    rw [← hφ]
    exact F.mor_unit q₁
  have hcont : Continuous F.mor := continuousOn_univ.1 F.isScSmoothMap_mor.continuousOn
  have hN : IsOpen ((fun p => F.mor (k, p)) ⁻¹' W) :=
    hW.preimage (hcont.comp (Continuous.prodMk continuous_const continuous_id))
  have hq : q₁ ∈ (fun p => F.mor (k, p)) ⁻¹' W := by
    change F.mor (k, q₁) ∈ W
    rw [hφ]
    exact hgW
  have hex : ∃ p ∈ (fun p => F.mor (k, p)) ⁻¹' W, k • p ≠ p := by
    by_contra hn
    push Not at hn
    exact hk (hf i k q₁ (Filter.mem_of_superset (hN.mem_nhds hq) hn))
  obtain ⟨p, hpW, hp⟩ := hex
  refine ⟨F.mor (k, p), hpW, fun he => hp ?_⟩
  have he' : (⟨i, p⟩ : S.ModelObj Ψ) = ⟨i, k • p⟩ := he
  exact (eq_of_heq (Sigma.mk.inj he').2).symm

open BasicConstruction GCT.PolyfoldConstruction in
/-- **Effectiveness of the polyfold `(S, F, M)`** (Definition 17.1.22 with Definition 7.2.1): if
every uniformizer of the basic construction is locally faithful, the model of the covering family
of Proposition 19.5.7 is effective. -/
theorem isEffective_toPolyfoldConstruction {C : GroupoidalCategory.{u}} {B : C.BasicConstruction}
    {hB : B.U.HasClassUniformizers}
    (hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace (B.natTop hB))
    (hf : ∀ (α : C.Obj), ∀ Ψ ∈ B.U.F α, IsLocallyFaithful Ψ) :
    (toPolyfoldConstruction hm).IsEffective := by
  set S := toPolyfoldConstruction hm
  have key : ∀ z : C.OrbitSpace, ∃ (α : C.Obj) (Ψ : C.Uniformizer) (_ : Ψ ∈ B.U.F α),
      C.π α = z := fun z => by
    obtain ⟨α, hα, Ψ, hΨ⟩ := hB z
    exact ⟨α, Ψ, hΨ, hα⟩
  choose α Ψ hΨ hα using key
  let Φ : C.OrbitSpace → S.Unif := fun z => ⟨toLocalUniformizer hm (hΨ z), α z, hΨ z⟩
  have hcov : ⋃ z, (Φ z).1.footprint = univ := eq_univ_of_forall fun z => mem_iUnion.2
    ⟨z, by
      obtain ⟨-, hz⟩ := B.theorem_19_2_2_three hB (hΨ z)
      rw [hα z] at hz
      exact hz⟩
  exact ⟨⟨C.OrbitSpace, Φ, hcov⟩, isEffective_model Φ (fun z => continuous_hat hm (Φ z))
    fun z => hf _ _ (hΨ z)⟩

end Effective

/-! ### Tameness -/

/-- **An M-polyfold modelled on open subsets of sc-Banach spaces is tame** (2021 Definitions
2.5.2 and 2.5.7): with `C = E` every retraction is tame (`d ≡ 0`). -/
theorem isTame_of_forall_C_eq_univ {X : Type*} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] (P : MPolyfold X) (h : ∀ φ ∈ P.atlas.charts, φ.model.C = univ) :
    P.IsTame :=
  ⟨P.atlas, MAtlas.Equiv.refl _, fun φ hφ =>
    let ⟨R, hR⟩ := φ.model.isScRetract
    ⟨R, hR, isTame_of_eq_univ R (h φ hφ)⟩⟩

/-! ### Witnesses -/

section WitnessTranslation

open GroupoidalCategory.UniformizerConstruction EpGroupoid.Examples

variable {G O : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O] {P : MPolyfold O}
  (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y)

/-- Core-smoothness for `G ⋉ O`: the group element of `φ_q` is constant on `V`. -/
def keyCS : CSPred (translationUnif P hP) := fun _ _ Φ V =>
  ∀ p ∈ V, ∀ q ∈ V, (Φ p).mor.1 = (Φ q).mor.1

/-- **Theorem 3.13 holds for `G ⋉ O`** with `keyCS`: `Φ(q) = (q, g, g ∗ q)` for `h = (o, g, g ∗ o)`,
and two germs with constant group element agree on the intersection of their domains. -/
theorem thm313_keyCS : Thm313 (translationUnif P hP) (keyCS hP) := by
  intro Ψ Ψ' h
  obtain ⟨Ψ₁, -, h₁⟩ := Ψ; obtain ⟨Ψ₂, -, h₂⟩ := Ψ'
  rw [mem_singleton_iff] at h₁ h₂; subst h₁ h₂
  have hs : P.IsScDiffeoOn P (fun y => h.mor.1 • y) (fun y => h.mor.1⁻¹ • y) univ univ :=
    ⟨hP _, hP _, mapsTo_univ _ _, mapsTo_univ _ _, fun x _ => inv_smul_smul _ x,
      fun y _ => smul_inv_smul _ y⟩
  refine ⟨⟨univ, fun q => (tautUniformizer P hP).hat (h.mor.1, q), isOpen_univ, mem_univ _,
    taut_trans_ext hP _ _ rfl rfl, fun q _ => rfl, ⟨fun y => h.mor.1⁻¹ • y, ?_⟩,
    fun _ _ _ _ => rfl⟩, ?_⟩
  · have e : (fun q => ((tautUniformizer P hP).hat (h.mor.1, q)).tgt) '' univ = univ :=
      hs.image_eq
    rw [e]
    exact hs
  · intro V₁ Φ₁ V₂ Φ₂ g₁ g₂
    refine ⟨V₁ ∩ V₂, g₁.1.inter g₂.1, ⟨g₁.2.1, g₂.2.1⟩, subset_rfl, fun q hq => ?_⟩
    refine taut_trans_ext hP _ _ ((g₁.2.2.2.1 q hq.1).trans (g₂.2.2.2.1 q hq.2).symm) ?_
    rw [g₁.2.2.2.2.2 q hq.1 h.src g₁.2.1, g₂.2.2.2.2.2 q hq.2 h.src g₂.2.1, g₁.2.2.1, g₂.2.2.1]

/-- `keyCS` is closed under the operations on germs. -/
theorem csClosed_keyCS : CSClosed (translationUnif P hP) (keyCS hP) where
  hat Ψ g := by
    obtain ⟨Ψ₁, a₁, h₁⟩ := Ψ
    rw [mem_singleton_iff] at h₁; subst h₁
    intro _ _ _ _; rfl
  transl Ψ Ψ' Φ V g hΦ := by
    obtain ⟨Ψ₁, a₁, h₁⟩ := Ψ; obtain ⟨Ψ₂, a₂, h₂⟩ := Ψ'
    rw [mem_singleton_iff] at h₁ h₂; subst h₁ h₂
    intro p hp q hq
    change g * (Φ p).mor.1 = g * (Φ q).mor.1
    rw [hΦ p hp q hq]
  inv Ψ Ψ' Φ V ginv hΦ _ _ hd := by
    obtain ⟨Ψ₁, a₁, h₁⟩ := Ψ; obtain ⟨Ψ₂, a₂, h₂⟩ := Ψ'
    rw [mem_singleton_iff] at h₁ h₂; subst h₁ h₂
    intro p hp q hq
    change ((Φ (ginv p)).mor.1)⁻¹ = ((Φ (ginv q)).mor.1)⁻¹
    rw [hΦ _ (hd.mapsTo_inv hp) _ (hd.mapsTo_inv hq)]
  comp Ψ Ψ' Ψ'' Φ Φ' V V' d hΦ hΦ' _ _ _ h4' _ := by
    obtain ⟨Ψ₁, a₁, h₁⟩ := Ψ; obtain ⟨Ψ₂, a₂, h₂⟩ := Ψ'; obtain ⟨Ψ₃, a₃, h₃⟩ := Ψ''
    rw [mem_singleton_iff] at h₁ h₂ h₃; subst h₁ h₂ h₃
    intro p hp q hq
    rw [compGerm_eq _ _ _ _ _ (TransitionSet.mor_composable_of_src_eq_tgt (h4' _ hp.2)),
      compGerm_eq _ _ _ _ _ (TransitionSet.mor_composable_of_src_eq_tgt (h4' _ hq.2))]
    change (Φ' (Φ p).tgt).mor.1 * (Φ p).mor.1 = (Φ' (Φ q).tgt).mor.1 * (Φ q).mor.1
    rw [hΦ p hp.1 q hq.1, hΦ' _ hp.2 _ hq.2]

/-- The family `F(x) = {Ψ₀}` of `G ⋉ O` is point-finite. -/
theorem pointFinite_translationUnif : PointFinite (translationUnif P hP) := fun Ψ _ =>
  (Set.finite_singleton Ψ).subset fun Ψ' _ => mem_singleton_iff.2
    (Subtype.ext ((translationUnif_eq hP Ψ').trans (translationUnif_eq hP Ψ).symm))

/-- **Non-degenerate witness for `reduction_3_13`**: its hypotheses hold for `ℤ/2 ⋉ ℝ`, where
`−1` acts by reflection and `M(Ψ₀, Ψ₀)` contains the non-unit `(0, −1, 0)`. -/
theorem reduction_3_13_reflection :
    Nonempty (translationUnif (G := ℤˣ) (rnPolyfold 1) isScSmoothMap_units_smul).TransitionData ∧
      ((-1 : ℤˣ) • (fun _ => 1 : Fin 1 → ℝ)) ≠ fun _ => 1 :=
  ⟨reduction_3_13 (thm313_keyCS _) (csClosed_keyCS _) (pointFinite_translationUnif _), by
    intro h
    have := congrFun h 0
    rw [units_smul_rn_neg_one] at this
    norm_num at this⟩

end WitnessTranslation

section WitnessReflection

open EpGroupoid.Examples

/-- The tautological uniformizer of `ℤ/2 ⋉ ℝ`. -/
abbrev reflUnif : (GroupoidalCategory.translation ℤˣ (Fin 1 → ℝ)).Uniformizer :=
  tautUniformizer (rnPolyfold 1) isScSmoothMap_units_smul

/-- **`ℤ/2 ⋉ ℝ` is tangent-faithful at every smooth point**: at `0`, `T(−1)` reverses the
tangent vector `(0, 1)` (`isZhou_reflection`). -/
theorem isTangentFaithfulAt_reflUnif (y : (rnPolyfold 1).SmoothLevel) :
    IsTangentFaithfulAt reflUnif y := by
  intro g hg hT
  have h1 : (rnPolyfold 1).smoothVal y ∈ (rnPolyfold 1).levelSet 1 :=
    mem_iInter.1 ((rnPolyfold 1).smoothVal_mem y) 1
  let k : reflectionEpGroupoid.Isotropy ((rnPolyfold 1).smoothVal y) :=
    ⟨(g, (rnPolyfold 1).smoothVal y), rfl, hg⟩
  have hk := isZhou_reflection y k fun v hv => by
    have hv' : (rnPolyfold 1).levelVal 1 ((rnPolyfold 1).tangentProj v) =
        (rnPolyfold 1).smoothVal y := by
      rw [show (rnPolyfold 1).tangentProj v = (rnPolyfold 1).smoothIncl y 1 from hv]; rfl
    exact (reflUnif.tangentMor_ep_eq g h1 hv').trans (hT v hv)
  have hk1 : k = 1 := (Subgroup.eq_bot_iff_forall _).1 (trivialSubgroup_reflection _) k hk
  exact congrArg (fun a => a.val.1) hk1

/-- **(ZHOU) for the basic construction of `ℤ/2 ⋉ ℝ`** (2021 Definition 19.5.6), from
tangent-faithfulness. -/
theorem reflectionBasic_isZhou : reflectionBasic.IsZhou := by
  refine isZhou_of_isTangentFaithfulAt _ fun z hz => ?_
  obtain ⟨⟨Ψ₁, a₁, h₁⟩, q, hq, hz⟩ := hz
  have h₁' : Ψ₁ = reflUnif := h₁
  subst h₁'
  exact ⟨q, reflUnif, rfl, ⟨q, hq⟩, hz, rfl, isTangentFaithfulAt_reflUnif _⟩

/-- `ℤ/2` acting on `ℝ` by reflection is locally faithful. -/
theorem isLocallyFaithful_reflUnif : IsLocallyFaithful reflUnif := by
  intro g q hq
  rcases Int.units_eq_one_or g with rfl | rfl
  · rfl
  · exfalso
    have hq' : ∀ᶠ p in 𝓝 q, p = 0 := hq.mono fun p hp => by
      rw [units_smul_rn_neg_one] at hp
      funext i
      have := congrFun hp i
      simp only [Pi.neg_apply] at this
      change p i = 0
      linarith
    have hq0 : q = 0 := hq'.self_of_nhds
    subst hq0
    have hc : Tendsto (fun t : ℝ => (fun _ => t : Fin 1 → ℝ)) (𝓝[≠] 0) (𝓝 0) :=
      ((continuous_pi fun _ => continuous_id).tendsto' 0 0 rfl).mono_left nhdsWithin_le_nhds
    obtain ⟨t, ht, ht0⟩ := ((hc.eventually hq').and self_mem_nhdsWithin).exists
    exact ht0 (congrFun ht 0)

/-- `ℝ` is tame through `isTame_of_forall_C_eq_univ`. -/
theorem rnPolyfold_isTame' : (rnPolyfold 1).IsTame :=
  isTame_of_forall_C_eq_univ _ fun φ hφ => by
    rw [mem_singleton_iff.1 hφ]
    rfl

end WitnessReflection

/-! ### The polyfold structure on `Z` -/

section Final

open BasicConstruction

/-- **The polyfold structure from a basic construction** (2021 Theorem 19.5.3 (2), Proposition
19.5.7, Definition 17.1.22): with a metrizable natural topology, Proposition 3.10, and
uniformizers that are tangent-faithful at smooth points and locally faithful, the polyfold
`(S, F, M)` has (ZHOU) and is effective, and carries its polyfold class. -/
theorem polyfold_isZhou_isEffective {C : GroupoidalCategory.{u}} (B : C.BasicConstruction)
    (hB : B.U.HasClassUniformizers)
    (hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace (B.natTop hB))
    (hTF : ∀ (α : C.Obj), ∀ Ψ ∈ B.U.F α, ∀ y : Ψ.P.SmoothLevel, IsTangentFaithfulAt Ψ y)
    (hLF : ∀ (α : C.Obj), ∀ Ψ ∈ B.U.F α, IsLocallyFaithful Ψ) :
    B.IsZhou ∧ (toPolyfoldConstruction hm).IsZhou ∧
      (toPolyfoldConstruction hm).IsEffective ∧
      Nonempty (PolyfoldClass ((B.toGCTOfMetrizable hB hm).toGroupoidStr.OrbitSpace)) := by
  have hz := isZhou_of_forall_isTangentFaithfulAt B hB hTF
  exact ⟨hz, proposition_19_5_7 hm hz, isEffective_toPolyfoldConstruction hm hLF,
    ⟨(toPolyfoldConstruction hm).polyfoldClass (proposition_19_5_7 hm hz)⟩⟩

/-- The non-degenerate witness: the basic construction of `ℤ/2 ⋉ ℝ`. -/
theorem polyfold_isZhou_isEffective_reflection :
    reflectionBasic.IsZhou ∧
      (toPolyfoldConstruction reflectionBasic_metrizableSpace).IsZhou ∧
      (toPolyfoldConstruction reflectionBasic_metrizableSpace).IsEffective ∧
      Nonempty (PolyfoldClass ((reflectionBasic.toGCTOfMetrizable reflectionBasic_hB
        reflectionBasic_metrizableSpace).toGroupoidStr.OrbitSpace)) :=
  polyfold_isZhou_isEffective reflectionBasic reflectionBasic_hB reflectionBasic_metrizableSpace
    (fun _ Ψ hΨ y => by
      have h : Ψ = reflUnif := hΨ
      subst h
      exact isTangentFaithfulAt_reflUnif y)
    fun _ Ψ hΨ => by
      have h : Ψ = reflUnif := hΨ
      subst h
      exact isLocallyFaithful_reflUnif

variable {C : GroupoidalCategory.{1}} {U : C.UniformizerConstruction} {CS : CSPred U}

/-- The transition data of Theorem 3.13 (`reduction_3_13_skeleton`). -/
def gwTransitionData (H : Theorem_3_13 U CS) (hCS : CSClosed U CS) (hPF : PointFinite U) :
    U.TransitionData :=
  (reduction_3_13_skeleton hCS hPF H).some

/-- **Named propositions ⇒ the polyfold structure on `Z`** (memoir Theorem 1.6, read through
2021 §§19.2–19.5): Proposition 3.10 (`U.HasClassUniformizers`), Theorem 3.13 with the
closure and finiteness conditions of `reduction_3_13`, Theorem 3.22 and the second countability
of Theorem 1.6 for the resulting transition data, and the faithfulness of the actions give a
metrizable `Z` whose polyfold structure has (ZHOU) and is effective. -/
theorem memoir_polyfold_structure (h310 : U.HasClassUniformizers) (H : Theorem_3_13 U CS)
    (hCS : CSClosed U CS) (hPF : PointFinite U)
    (h322 : Theorem_3_22 U (gwTransitionData H hCS hPF))
    (h16 : Theorem_1_6_sc U (gwTransitionData H hCS hPF) h310)
    (hTF : ∀ (α : C.Obj), ∀ Ψ ∈ U.F α, ∀ y : Ψ.P.SmoothLevel, IsTangentFaithfulAt Ψ y)
    (hLF : ∀ (α : C.Obj), ∀ Ψ ∈ U.F α, IsLocallyFaithful Ψ) :
    ∃ (hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace
        ((basicOf U (gwTransitionData H hCS hPF)).natTop h310)),
      (basicOf U (gwTransitionData H hCS hPF)).IsZhou ∧
      (toPolyfoldConstruction hm).IsZhou ∧ (toPolyfoldConstruction hm).IsEffective ∧
        Nonempty (PolyfoldClass ((basicOf U (gwTransitionData H hCS hPF)).toGCTOfMetrizable
          h310 hm).toGroupoidStr.OrbitSpace) := by
  have hm := metrizable_of_theorem_3_22 U _ h310 h322 h16
  obtain ⟨hz, h1, h2, -⟩ := polyfold_isZhou_isEffective _ h310 hm hTF hLF
  exact ⟨hm, hz, h1, h2, ⟨gwPolyfoldClass U _ h310 hm hz⟩⟩

end Final

end GWMemoir
