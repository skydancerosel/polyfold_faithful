import Polyfold.Chapter17.TransitionProperness
import Polyfold.Chapter9.DescentPolyfold

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (pp. 746–752): witnesses for **Definitions 17.1.6 and 17.1.8**, for **Lemma 17.1.9**,
**Lemma 17.1.10**, **Proposition 17.1.11** and **Definition 17.1.12**, the statement
`not_lemma_17_1_9`, and the condition `F(α) ≠ ∅`.  Numbers and pages are the 2021 text's.

# Polyfold structures on translation GCTs

## The construction

For a translation GCT `C = K ⋉ U` (Definition 17.1.2) take `F(x) = {Ψ₀}` for every `x`, with
`Ψ₀` the tautological uniformizer (the identity of `K ⋉ U`).  Its transition set `M(Ψ₀, Ψ₀)` is in
bijection with `K × U`; given an automorphism `β` of the groupoid `K ⋉ U` over the identity of `U`
(`TranslationTwist`), transport the M-polyfold structure of `K × U` along
`e_β : (g, p) ↦ (p, β(g, p), g ∗ p)` (`MPolyfold.transport`, through the descent of Chapter 9).
Then (a)–(c) of Definition 17.1.8 hold, since `s, t, u, ι, m` are, through `e_β`, those of the
ep-groupoid `K ⋉ U` (`twistConstruction`).  `Ψ̂ = e_β ∘ β⁻¹`.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `MPolyfold.transport`, `MPolyfold.isScDiffeoOn_transport`: an M-polyfold structure moved
  along a homeomorphism, for which the homeomorphism is an sc-diffeomorphism.
* `TranslationTwist`, `TranslationTwist.refl`, `twistConstruction` (a polyfold structure, tame if
  `U` is), `twistConstruction_hasUniformizers`, `twist_hat_eq`, `twist_continuous_hat`,
  `twist_not_continuous_hat`.
* **The non-degenerate witness** `reflectionConstruction` on `ℤ/2 ⋉ ℝ` (reflection): tame, every
  `F(x) ≠ ∅`, `Ψ̂` continuous; the conclusions of Lemma 17.1.9 (`reflection_lemma_17_1_9`) and of
  Proposition 17.1.11 (`reflection_hasPropernessProperty`) hold for it, and the sheet of the
  non-trivial automorphism of `0` is not the unit sheet (`reflection_hatSheet_ne`).
* **`not_lemma_17_1_9`**: on `ℤ/3 ⋉ ℝ` (trivial action) with the twist `β(g, p) = (g, p)` for
  `p ≤ 0`, `(g⁻¹, p)` for `p > 0` (`z3Construction`), Definition 17.1.8 holds, the uniformizer is
  centred at `0` with `G = G_0 = ℤ/3` (`z3_isCentredAt`), and `Ψ̂` is not continuous, so not an
  sc-diffeomorphism.
* **`F(α) ≠ ∅`**: `emptyConstruction` (`F ≡ ∅`) satisfies Definition 17.1.8 as printed;
  `not_hasUniformizers_empty`, `not_hasCoveringUniformizers_empty`.

## Readings

* Lemma 17.1.9 ("`Ψ̂` is an sc-diffeomorphism") does not hold as we read Definition 17.1.8:
  (a)–(c) do not tie the topology of `M(Ψ, Ψ)` to that of `G × O` along `Ψ̂`.  The proof's step
  "`Ψ̂` is a local sc-diffeomorphism" holds when `Ψ̂` is continuous
  (`lemma_17_1_9_of_continuous`), as in `reflectionConstruction`; Lemma 17.1.10 and
  Proposition 17.1.11 are proved without it.
* Definition 17.1.8 puts no condition `F(α) ≠ ∅`; the text uses it implicitly (Lemma 17.1.9 takes
  some `Ψ ∈ F(α)`, and p. 752 chooses a covering family).  It is the predicate `HasUniformizers`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u v

/-! ### Transport of an M-polyfold structure along a homeomorphism -/

namespace MPolyfold

variable {A : Type u} [TopologicalSpace A] [T2Space A] [ParacompactSpace A] (PA : MPolyfold A)
  {B : Type v} [TopologicalSpace B]

/-- A homeomorphism is a descent map (Chapter 9). -/
theorem isDescentMap_homeomorph (e : A ≃ₜ B) : PA.IsDescentMap e where
  continuous := e.continuous
  isOpenMap := e.isOpenMap
  surjective := e.surjective
  locInj a := ⟨univ, isOpen_univ, mem_univ a, e.injective.injOn⟩
  trans a _ h := ⟨univ, id, isOpen_univ, mem_univ a, isScSmoothMap_id, e.injective h,
    fun _ _ => rfl⟩

variable [T2Space B] [ParacompactSpace B]

/-- **The M-polyfold structure transported along a homeomorphism `e : A ≃ₜ B`** (descended along
`e`, Chapter 9). -/
def transport (e : A ≃ₜ B) : MPolyfold B := descend (PA.isDescentMap_homeomorph e)

/-- `e : A → B` is an sc-diffeomorphism for the transported structure. -/
theorem isScDiffeoOn_transport (e : A ≃ₜ B) :
    PA.IsScDiffeoOn (PA.transport e) e e.symm univ univ := by
  have hl := isLocalScDiffeo_descend (PA.isDescentMap_homeomorph e)
  refine ⟨hl.isScSmoothMap, ?_, mapsTo_univ _ _, mapsTo_univ _ _,
    fun x _ => e.symm_apply_apply x, fun y _ => e.apply_symm_apply y⟩
  refine IsScSmoothOn.of_locally isOpen_univ fun z _ => ?_
  obtain ⟨W, V, g, hx, hd⟩ := hl (e.symm z)
  have hz : z ∈ V := by
    have := hd.mapsTo hx
    rwa [e.apply_symm_apply] at this
  refine ⟨V, hd.isOpen_target, hz, subset_univ _, hd.isScSmoothOn_inv.congr fun y hy => ?_⟩
  exact (e.symm_apply_eq.2 (hd.right_inv y hy).symm).symm

end MPolyfold

namespace GCT

namespace PolyfoldConstruction

/-! ### Twisted polyfold structures on a translation GCT -/

section Twist

variable (K U : Type u) [Group K] [MulAction K U]

/-- **An automorphism `β` of the translation groupoid `K ⋉ U` over the identity of `U`**: a
bijection of `K × U` commuting with `s` and `t` and preserving units, inverses and
compositions. -/
structure TranslationTwist where
  /-- The bijection `β` of the morphisms. -/
  toEquiv : K × U ≃ K × U
  snd_apply : ∀ x, (toEquiv x).2 = x.2
  smul_apply : ∀ x : K × U, (toEquiv x).1 • x.2 = x.1 • x.2
  apply_one : ∀ y : U, toEquiv (1, y) = (1, y)
  apply_inv : ∀ x : K × U, toEquiv (x.1⁻¹, x.1 • x.2) = ((toEquiv x).1⁻¹, x.1 • x.2)
  apply_mul : ∀ x y : K × U, x.2 = y.1 • y.2 →
    toEquiv (x.1 * y.1, y.2) = ((toEquiv x).1 * (toEquiv y).1, y.2)

/-- The identity twist. -/
def TranslationTwist.refl : TranslationTwist K U where
  toEquiv := Equiv.refl _
  snd_apply _ := rfl
  smul_apply _ := rfl
  apply_one _ := rfl
  apply_inv _ := rfl
  apply_mul _ _ _ := rfl

variable {K U} [Finite K] [TopologicalSpace K] [DiscreteTopology K]
  [TopologicalSpace U] [T2Space U] [ParacompactSpace U] {P : MPolyfold U}
  (hP : ∀ k : K, P.IsScSmoothMap P fun y => k • y) (β : TranslationTwist K U)

/-- The transition set `M(Ψ₀, Ψ₀)` of the tautological uniformizer. -/
abbrev TautTrans : Type u :=
  (LocalUniformizer.tautological P hP).Trans (LocalUniformizer.tautological P hP)

/-- `e_β : K × U → M(Ψ₀, Ψ₀)`, `(g, p) ↦ (p, β(g, p), g ∗ p)`. -/
def twistMap (x : K × U) : TautTrans hP :=
  ⟨x.2, β.toEquiv x, x.1 • x.2, β.snd_apply x, by
    change (β.toEquiv x).1 • (β.toEquiv x).2 = x.1 • x.2
    rw [β.snd_apply]
    exact β.smul_apply x⟩

/-- `e_β` as a bijection. -/
def twistEquiv : K × U ≃ TautTrans hP where
  toFun := twistMap hP β
  invFun a := β.toEquiv.symm a.mor
  left_inv x := β.toEquiv.symm_apply_apply x
  right_inv a := by
    set z := β.toEquiv.symm a.mor
    have hz : β.toEquiv z = a.mor := β.toEquiv.apply_symm_apply _
    have hs : a.mor.2 = a.src := a.src_mor
    have ht : a.mor.1 • a.mor.2 = a.tgt := a.tgt_mor
    refine GroupoidStr.TransitionSet.ext ?_ hz ?_
    · change z.2 = a.src
      rw [← β.snd_apply z, hz, hs]
    · change z.1 • z.2 = a.tgt
      rw [← β.smul_apply z, ← β.snd_apply z, hz, ht]

/-- **The twisted transition M-polyfold** `M(Ψ₀, Ψ₀)`, a type synonym carrying the topology
transported along `e_β`. -/
@[nolint unusedArguments]
def TwistTrans (_β : TranslationTwist K U) : Type u := TautTrans hP

instance : TopologicalSpace (TwistTrans hP β) :=
  TopologicalSpace.coinduced (twistEquiv hP β) inferInstance

/-- `e_β` as a homeomorphism. -/
def twistHomeomorph : K × U ≃ₜ TwistTrans hP β where
  toEquiv := twistEquiv hP β
  continuous_toFun := continuous_coinduced_rng
  continuous_invFun := continuous_coinduced_dom.2
    (continuous_id.congr fun x => ((twistEquiv hP β).symm_apply_apply x).symm)

instance : T2Space (TwistTrans hP β) := (twistHomeomorph hP β).t2Space

instance : ParacompactSpace (TwistTrans hP β) :=
  (twistHomeomorph hP β).paracompactSpace_iff.1 inferInstance

/-- The M-polyfold structure of `M(Ψ₀, Ψ₀)`, transported from `K × U` along `e_β`. -/
def twistM : MPolyfold (TwistTrans hP β) :=
  (EpGroupoid.Examples.actionMorPolyfold K P).transport (twistHomeomorph hP β)

theorem isScDiffeoOn_twist : (EpGroupoid.Examples.actionMorPolyfold K P).IsScDiffeoOn
    (twistM hP β) (twistHomeomorph hP β) (twistHomeomorph hP β).symm univ univ :=
  MPolyfold.isScDiffeoOn_transport _ _

theorem twist_symm_snd (a : TwistTrans hP β) : ((twistHomeomorph hP β).symm a).2 = a.src :=
  congrArg GroupoidStr.TransitionSet.src ((twistHomeomorph hP β).apply_symm_apply a)

theorem twist_symm_smul (a : TwistTrans hP β) :
    ((twistHomeomorph hP β).symm a).1 • ((twistHomeomorph hP β).symm a).2 = a.tgt :=
  congrArg GroupoidStr.TransitionSet.tgt ((twistHomeomorph hP β).apply_symm_apply a)

theorem isLocalScDiffeo_twist_symm :
    (twistM hP β).IsLocalScDiffeo (EpGroupoid.Examples.actionMorPolyfold K P)
      (twistHomeomorph hP β).symm := fun _ =>
  ⟨univ, univ, twistHomeomorph hP β, mem_univ _, (isScDiffeoOn_twist hP β).symm⟩

/-- **(a)** for the twisted structure: `s` is a local sc-diffeomorphism. -/
theorem twist_isLocalScDiffeo_src :
    (twistM hP β).IsLocalScDiffeo P fun a : TwistTrans hP β => a.src := by
  have h : (fun a : TwistTrans hP β => a.src) =
      (GroupoidStr.translation K U).src ∘ (twistHomeomorph hP β).symm :=
    funext fun a => (twist_symm_snd hP β a).symm
  rw [h]
  exact EpGroupoid.Examples.action_isLocalScDiffeo_src.comp (isLocalScDiffeo_twist_symm hP β)

/-- **(a)** for the twisted structure: `t` is a local sc-diffeomorphism. -/
theorem twist_isLocalScDiffeo_tgt :
    (twistM hP β).IsLocalScDiffeo P fun a : TwistTrans hP β => a.tgt := by
  have h : (fun a : TwistTrans hP β => a.tgt) =
      (GroupoidStr.translation K U).tgt ∘ (twistHomeomorph hP β).symm :=
    funext fun a => (twist_symm_smul hP β a).symm
  rw [h]
  exact (EpGroupoid.Examples.action_isLocalScDiffeo_tgt hP).comp (isLocalScDiffeo_twist_symm hP β)

theorem twist_unit (q : U) :
    twistMap hP β (1, q) = (GroupoidStr.TransitionSet.unit q : TautTrans hP) :=
  GroupoidStr.TransitionSet.ext rfl (β.apply_one q) (one_smul K q)

/-- **(b)** for the twisted structure: the unit map is sc-smooth. -/
theorem twist_isScSmoothMap_unit :
    P.IsScSmoothMap (twistM hP β) fun q => (GroupoidStr.TransitionSet.unit q : TwistTrans hP β) :=
  ((isScDiffeoOn_twist hP β).isScSmoothOn.comp
    (EpGroupoid.Examples.actionEpGroupoid hP).isScSmoothMap_unit (mapsTo_univ _ _)).congr
    fun q _ => twist_unit hP β q

theorem twist_inv (x : K × U) :
    GroupoidStr.TransitionSet.inv (twistMap hP β x) = twistMap hP β (x.1⁻¹, x.1 • x.2) := by
  refine GroupoidStr.TransitionSet.ext rfl ?_ (inv_smul_smul x.1 x.2).symm
  change ((β.toEquiv x).1⁻¹, (β.toEquiv x).1 • (β.toEquiv x).2) = β.toEquiv (x.1⁻¹, x.1 • x.2)
  rw [β.apply_inv, β.snd_apply, β.smul_apply]

/-- **(b)** for the twisted structure: the inversion is sc-smooth. -/
theorem twist_isScSmoothMap_inv :
    (twistM hP β).IsScSmoothMap (twistM hP β)
      fun a : TwistTrans hP β => (GroupoidStr.TransitionSet.inv a : TwistTrans hP β) := by
  have h1 := (EpGroupoid.Examples.actionEpGroupoid hP).isScSmoothMap_inv.comp
    (isScDiffeoOn_twist hP β).isScSmoothOn_inv
  refine ((isScDiffeoOn_twist hP β).isScSmoothOn.comp h1 (mapsTo_univ _ _)).congr fun a _ => ?_
  change twistMap hP β _ = _
  conv_rhs => rw [← (twistHomeomorph hP β).apply_symm_apply a]
  exact (twist_inv hP β _).symm

theorem twist_comp (a b : TautTrans hP) (h) (x y : K × U) (ha : a = twistMap hP β x)
    (hb : b = twistMap hP β y) :
    GroupoidStr.TransitionSet.comp a b h = twistMap hP β (x.1 * y.1, y.2) := by
  subst ha hb
  have hxy : x.2 = y.1 • y.2 := by
    have := h
    change (β.toEquiv x).2 = (β.toEquiv y).1 • (β.toEquiv y).2 at this
    rwa [β.snd_apply, β.snd_apply, β.smul_apply] at this
  refine GroupoidStr.TransitionSet.ext rfl ?_ ?_
  · change ((β.toEquiv x).1 * (β.toEquiv y).1, (β.toEquiv y).2) = β.toEquiv (x.1 * y.1, y.2)
    rw [β.apply_mul x y hxy, β.snd_apply]
  · change x.1 • x.2 = (x.1 * y.1) • y.2
    rw [mul_smul, hxy]

/-- **(c)** for the twisted structure: the multiplication is sc-smooth. -/
theorem twist_isScSmoothMap_mul :
    MPolyfold.IsScSmoothOnFibredProduct (twistM hP β) (twistM hP β) (twistM hP β)
      (twist_isLocalScDiffeo_src hP β) (twist_isLocalScDiffeo_tgt hP β).isScSmoothMap
      fun p => (GroupoidStr.TransitionSet.mul p : TwistTrans hP β) := by
  set X := EpGroupoid.Examples.actionEpGroupoid hP
  set PM := EpGroupoid.Examples.actionMorPolyfold K P
  set e := twistHomeomorph hP β
  set Mt := twistM hP β
  have := MPolyfold.paracompactSpace_prod Mt Mt
  have := (Mt.prod Mt).paracompactSpace_subtype (MPolyfold.fibredProduct
    (fun a : TwistTrans hP β => a.src) (fun a : TwistTrans hP β => a.tgt))
  have := MPolyfold.paracompactSpace_prod PM PM
  have := (PM.prod PM).paracompactSpace_subtype (MPolyfold.fibredProduct X.src X.tgt)
  have hA := MPolyfold.isSubMPolyfold_fibredProduct (twist_isLocalScDiffeo_src hP β)
    (twist_isLocalScDiffeo_tgt hP β).isScSmoothMap
  have hB := MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src
    X.isLocalScDiffeo_tgt.isScSmoothMap
  have hc : (MPolyfold.subPolyfold hB).IsScSmoothMap PM fun p => X.comp p.1.1 p.1.2 :=
    X.isScSmoothComp
  -- `Φ = e⁻¹ × e⁻¹` on the fibred products
  let Φ : MPolyfold.fibredProduct (fun a : TwistTrans hP β => a.src)
      (fun a : TwistTrans hP β => a.tgt) → MPolyfold.fibredProduct X.src X.tgt :=
    fun p => ⟨(e.symm p.1.1, e.symm p.1.2), by
      change (e.symm p.1.1).2 = (e.symm p.1.2).1 • (e.symm p.1.2).2
      rw [twist_symm_snd, twist_symm_smul]
      exact p.2⟩
  have hval := MPolyfold.subPolyfold_inclusion_isScSmooth hA
  have hΦ : (MPolyfold.subPolyfold hA).IsScSmoothMap (MPolyfold.subPolyfold hB) Φ := by
    refine MPolyfold.isScSmoothOn_subPolyfold_of_val hB ?_
    refine MPolyfold.IsScSmoothOn.prodMk ?_ ?_
    · exact (isScDiffeoOn_twist hP β).isScSmoothOn_inv.comp
        ((MPolyfold.isScSmoothMap_fst Mt Mt).comp hval) (mapsTo_univ _ _)
    · exact (isScDiffeoOn_twist hP β).isScSmoothOn_inv.comp
        ((MPolyfold.isScSmoothMap_snd Mt Mt).comp hval) (mapsTo_univ _ _)
  have h2 := (isScDiffeoOn_twist hP β).isScSmoothOn.comp (hc.comp hΦ)
    (mapsTo_univ _ _)
  change (MPolyfold.subPolyfold hA).IsScSmoothMap Mt _
  refine h2.congr fun p _ => ?_
  change twistMap hP β _ = GroupoidStr.TransitionSet.comp p.1.1 p.1.2 _
  exact (twist_comp hP β _ _ _ _ _ (e.apply_symm_apply p.1.1).symm
    (e.apply_symm_apply p.1.2).symm).symm

/-- The uniformizer construction `F(x) = {Ψ₀}`. -/
abbrev tautF : (GCT.translation K U hP).Obj → Set (GCT.translation K U hP).LocalUniformizer :=
  fun _ => {LocalUniformizer.tautological P hP}

theorem tautF_eq (Ψ : GCT.Unif (tautF hP)) : Ψ.1 = LocalUniformizer.tautological P hP := by
  obtain ⟨_, _, h⟩ := Ψ
  exact h

/-- The topology of `M(L, L')` for `L = L' = Ψ₀`. -/
@[instance_reducible]
def twistTopOf : ∀ L L' : (GCT.translation K U hP).LocalUniformizer,
    L = LocalUniformizer.tautological P hP → L' = LocalUniformizer.tautological P hP →
    TopologicalSpace (L.Trans L')
  | _, _, rfl, rfl => (inferInstance : TopologicalSpace (TwistTrans hP β))

theorem twistT2Of : ∀ (L L' : (GCT.translation K U hP).LocalUniformizer)
    (h : L = LocalUniformizer.tautological P hP) (h' : L' = LocalUniformizer.tautological P hP),
    @T2Space (L.Trans L') (twistTopOf hP β L L' h h')
  | _, _, rfl, rfl => (inferInstance : T2Space (TwistTrans hP β))

theorem twistParaOf : ∀ (L L' : (GCT.translation K U hP).LocalUniformizer)
    (h : L = LocalUniformizer.tautological P hP) (h' : L' = LocalUniformizer.tautological P hP),
    @ParacompactSpace (L.Trans L') (twistTopOf hP β L L' h h')
  | _, _, rfl, rfl => (inferInstance : ParacompactSpace (TwistTrans hP β))

/-- The M-polyfold `M(L, L')` for `L = L' = Ψ₀`. -/
def twistMOf : ∀ (L L' : (GCT.translation K U hP).LocalUniformizer)
    (h : L = LocalUniformizer.tautological P hP) (h' : L' = LocalUniformizer.tautological P hP),
    @MPolyfold (L.Trans L') (twistTopOf hP β L L' h h') (twistT2Of hP β L L' h h')
      (twistParaOf hP β L L' h h')
  | _, _, rfl, rfl => twistM hP β

/-- **A polyfold structure on the translation GCT `K ⋉ U`** (Definition 17.1.8): `F(x) = {Ψ₀}`
and `M(Ψ₀, Ψ₀) = K × U` transported along `e_β`. -/
def twistConstruction : (GCT.translation K U hP).PolyfoldConstruction where
  F := tautF hP
  isAt x Ψ hΨ := by
    rw [Set.mem_singleton_iff.1 hΨ]
    exact LocalUniformizer.tautological_isAt hP x
  topM Ψ Ψ' := twistTopOf hP β Ψ.1 Ψ'.1 (tautF_eq hP Ψ) (tautF_eq hP Ψ')
  t2M Ψ Ψ' := twistT2Of hP β Ψ.1 Ψ'.1 (tautF_eq hP Ψ) (tautF_eq hP Ψ')
  paraM Ψ Ψ' := twistParaOf hP β Ψ.1 Ψ'.1 (tautF_eq hP Ψ) (tautF_eq hP Ψ')
  M Ψ Ψ' := twistMOf hP β Ψ.1 Ψ'.1 (tautF_eq hP Ψ) (tautF_eq hP Ψ')
  isLocalScDiffeo_src := by
    rintro ⟨L, x, hL⟩ ⟨L', x', hL'⟩
    obtain rfl : L = _ := hL
    obtain rfl : L' = _ := hL'
    exact twist_isLocalScDiffeo_src hP β
  isLocalScDiffeo_tgt := by
    rintro ⟨L, x, hL⟩ ⟨L', x', hL'⟩
    obtain rfl : L = _ := hL
    obtain rfl : L' = _ := hL'
    exact twist_isLocalScDiffeo_tgt hP β
  isScSmoothMap_unit := by
    rintro ⟨L, x, hL⟩
    obtain rfl : L = _ := hL
    exact twist_isScSmoothMap_unit hP β
  isScSmoothMap_inv := by
    rintro ⟨L, x, hL⟩ ⟨L', x', hL'⟩
    obtain rfl : L = _ := hL
    obtain rfl : L' = _ := hL'
    exact twist_isScSmoothMap_inv hP β
  isScSmoothMap_mul := by
    rintro ⟨L, x, hL⟩ ⟨L', x', hL'⟩ ⟨L'', x'', hL''⟩
    obtain rfl : L = _ := hL
    obtain rfl : L' = _ := hL'
    obtain rfl : L'' = _ := hL''
    exact twist_isScSmoothMap_mul hP β

/-- Every `F(x)` is non-empty. -/
theorem twistConstruction_hasUniformizers : (twistConstruction hP β).HasUniformizers :=
  fun _ => singleton_nonempty _

/-- The construction is tame if `U` is. -/
theorem twistConstruction_isTame (hT : P.IsTame) : (twistConstruction hP β).IsTame := by
  intro x Ψ hΨ
  rw [Set.mem_singleton_iff.1 hΨ]
  exact hT

/-- `Ψ₀` as a uniformizer of the construction. -/
abbrev tautUnif (x : U) : (twistConstruction hP β).Unif :=
  ⟨LocalUniformizer.tautological P hP, x, rfl⟩

/-- `Ψ̂ ∘ β = e_β`. -/
theorem twist_hat_comp (x : U) (y : K × U) :
    (twistConstruction hP β).hat (tautUnif hP β x) (β.toEquiv y) = twistMap hP β y := by
  refine GroupoidStr.TransitionSet.ext (β.snd_apply y) rfl ?_
  change (β.toEquiv y).1 • (β.toEquiv y).2 = y.1 • y.2
  rw [β.snd_apply, β.smul_apply]

/-- `Ψ̂ = e_β ∘ β⁻¹`. -/
theorem twist_hat_eq (x : U) (z : K × U) :
    (twistConstruction hP β).hat (tautUnif hP β x) z =
      twistHomeomorph hP β (β.toEquiv.symm z) := by
  conv_lhs => rw [← β.toEquiv.apply_symm_apply z]
  exact twist_hat_comp hP β x _

/-- If `β⁻¹` is continuous, `Ψ̂` is continuous. -/
theorem twist_continuous_hat (x : U) (hβ : Continuous β.toEquiv.symm) :
    Continuous ((twistConstruction hP β).hat (tautUnif hP β x)) := by
  have h : (twistConstruction hP β).hat (tautUnif hP β x) =
      fun z => twistHomeomorph hP β (β.toEquiv.symm z) := funext (twist_hat_eq hP β x)
  rw [h]
  exact (twistHomeomorph hP β).continuous.comp hβ

/-- If `β⁻¹` is not continuous, `Ψ̂` is not continuous. -/
theorem twist_not_continuous_hat (x : U) (hβ : ¬ Continuous β.toEquiv.symm) :
    ¬ Continuous ((twistConstruction hP β).hat (tautUnif hP β x)) := by
  intro hc
  refine hβ ?_
  have h : (β.toEquiv.symm : K × U → K × U) =
      fun z => (twistHomeomorph hP β).symm ((twistConstruction hP β).hat (tautUnif hP β x) z) :=
    funext fun z => by rw [twist_hat_eq, Homeomorph.symm_apply_apply]
  rw [h]
  exact (twistHomeomorph hP β).symm.continuous.comp hc

end Twist

/-! ### The reflection witness -/

section Reflection

open EpGroupoid.Examples

/-- **The non-degenerate witness of Definition 17.1.8**: the polyfold structure on `ℤ/2 ⋉ ℝ`
(reflection) with `F(x) = {Ψ₀}` and `M(Ψ₀, Ψ₀) = ℤ/2 × ℝ` along `Ψ̂`. -/
abbrev reflectionConstruction : GCT.reflection.PolyfoldConstruction :=
  twistConstruction isScSmoothMap_units_smul (TranslationTwist.refl ℤˣ (Fin 1 → ℝ))

/-- The tautological uniformizer of the reflection witness, at `0`. -/
abbrev reflectionUnif : reflectionConstruction.Unif := tautUnif _ _ 0

theorem reflectionConstruction_hasUniformizers : reflectionConstruction.HasUniformizers :=
  twistConstruction_hasUniformizers _ _

theorem reflectionConstruction_isTame : reflectionConstruction.IsTame :=
  twistConstruction_isTame _ _ isTame_reflection

theorem reflection_continuous_hat : Continuous (reflectionConstruction.hat reflectionUnif) :=
  twist_continuous_hat _ _ 0 continuous_id

/-- **Lemma 17.1.9 for the reflection witness**: `Ψ̂ : ℤ/2 × ℝ → M(Ψ₀, Ψ₀)` is an
sc-diffeomorphism, the sheets are open, and `s` is an sc-diffeomorphism on each of them. -/
theorem reflection_lemma_17_1_9 :
    (reflectionConstruction.morPolyfold reflectionUnif).IsScDiffeoOn
      (reflectionConstruction.transPolyfold reflectionUnif reflectionUnif)
      (reflectionConstruction.hat reflectionUnif) (reflectionConstruction.hatInv reflectionUnif)
      univ univ ∧
    (∀ g, IsOpen (reflectionConstruction.hatSheet reflectionUnif g)) ∧
    ∀ g, (reflectionConstruction.transPolyfold reflectionUnif reflectionUnif).IsScDiffeoOn
        reflectionUnif.1.P (fun a => a.src)
        (fun p => reflectionConstruction.hat reflectionUnif (g, p))
        (reflectionConstruction.hatSheet reflectionUnif g) univ :=
  reflectionConstruction.lemma_17_1_9_of_continuous reflectionUnif reflection_continuous_hat

/-- In the reflection witness, the sheet of the automorphism `−1` of `0` is not the unit
sheet. -/
theorem reflection_hatSheet_ne :
    reflectionConstruction.hatSheet reflectionUnif (-1) ≠
      reflectionConstruction.hatSheet reflectionUnif 1 := by
  intro h
  have h1 := (reflectionConstruction.lemma_17_1_9_decomposition reflectionUnif).2.2.2 (-1) 0
  rw [h] at h1
  obtain ⟨p, hp, he⟩ := h1
  have := congrArg Prod.fst ((reflectionConstruction.lemma_17_1_9_bijective reflectionUnif).1 he)
  rw [show p.1 = 1 from hp.1] at this
  exact absurd this (by decide)

/-- **The properness property of the reflection witness** (Proposition 17.1.11, Definition
17.1.12). -/
theorem reflection_hasPropernessProperty : reflectionConstruction.HasPropernessProperty :=
  reflectionConstruction.proposition_17_1_11

end Reflection

/-! ### Lemma 17.1.9 does not hold as we read it -/

section Z3

open EpGroupoid.Examples

/-- `β(g, p) = (g, p)` for `p ≤ 0` and `(g⁻¹, p)` for `p > 0`. -/
def z3TwistFun (x : Multiplicative (ZMod 3) × (Fin 1 → ℝ)) :
    Multiplicative (ZMod 3) × (Fin 1 → ℝ) :=
  (if x.2 0 ≤ 0 then x.1 else x.1⁻¹, x.2)

theorem z3TwistFun_involutive : Involutive z3TwistFun := by
  rintro ⟨g, p⟩
  unfold z3TwistFun
  split_ifs <;> simp

/-- **The twist of `ℤ/3 ⋉ ℝ`** (trivial action): inversion of `ℤ/3` over `p > 0`. -/
def z3Twist : TranslationTwist (Multiplicative (ZMod 3)) (Fin 1 → ℝ) where
  toEquiv := z3TwistFun_involutive.toPerm _
  snd_apply _ := rfl
  smul_apply _ := rfl
  apply_one y := by
    change z3TwistFun (1, y) = (1, y)
    unfold z3TwistFun
    split_ifs <;> simp
  apply_inv x := by
    change z3TwistFun (x.1⁻¹, x.2) = ((z3TwistFun x).1⁻¹, x.2)
    unfold z3TwistFun
    split_ifs <;> simp
  apply_mul x y hxy := by
    change x.2 = y.2 at hxy
    change z3TwistFun (x.1 * y.1, y.2) = ((z3TwistFun x).1 * (z3TwistFun y).1, y.2)
    unfold z3TwistFun
    rw [hxy]
    split_ifs <;> simp [mul_comm]

theorem not_continuous_z3Twist : ¬ Continuous z3Twist.toEquiv.symm := by
  intro hc
  have hs : (z3Twist.toEquiv.symm : _ → _) = z3TwistFun := by
    change ((z3TwistFun_involutive.toPerm _).symm : _ → _) = _
    rw [Function.Involutive.toPerm_symm]
    rfl
  rw [hs] at hc
  have hf : Continuous fun t : ℝ =>
      (z3TwistFun (Multiplicative.ofAdd (1 : ZMod 3), fun _ => t)).1 :=
    continuous_fst.comp (hc.comp (continuous_const.prodMk (continuous_pi fun _ => continuous_id)))
  have h01 := PreconnectedSpace.constant inferInstance hf (x := 0) (y := 1)
  simp only [z3TwistFun, le_refl, if_true] at h01
  rw [if_neg (by norm_num)] at h01
  exact absurd h01 (by decide)

/-- **The twisted polyfold structure on `ℤ/3 ⋉ ℝ`** (trivial action): Definition 17.1.8 holds. -/
abbrev z3Construction : (GCT.translation (Multiplicative (ZMod 3)) (Fin 1 → ℝ)
    isScSmoothMap_z3_smul).PolyfoldConstruction :=
  twistConstruction isScSmoothMap_z3_smul z3Twist

/-- The tautological uniformizer of `z3Construction`, at `0`. -/
abbrev z3Unif : z3Construction.Unif := tautUnif _ _ 0

/-- The uniformizer of `z3Construction` is centred at `0`: `G = ℤ/3` fixes `0`, so
`G ≅ G_0`; every `F(x)` is non-empty and the construction is tame. -/
theorem z3_isCentredAt : z3Unif.1.toUniformizer.IsCentredAt (0 : Fin 1 → ℝ) ∧
    z3Construction.HasUniformizers ∧ z3Construction.IsTame :=
  ⟨⟨0, rfl, fun _ => rfl⟩, twistConstruction_hasUniformizers _ _,
    twistConstruction_isTame _ _ rnPolyfold_isTame⟩

theorem z3_not_continuous_hat : ¬ Continuous (z3Construction.hat z3Unif) :=
  twist_not_continuous_hat _ _ 0 not_continuous_z3Twist

/-- **2021 Lemma 17.1.9, p. 748, does not hold as we read it**: there are a GCT with a polyfold
structure (Definition 17.1.8) and a uniformizer `Ψ` (centred, with `G = G_α`, `z3_isCentredAt`)
for which `Ψ̂ : G ⋉ O → M(Ψ, Ψ)` is not an sc-diffeomorphism.  Under the continuity of `Ψ̂`
the statement holds (`lemma_17_1_9_of_continuous`). -/
theorem not_lemma_17_1_9 : ¬ ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (Ψ : S.Unif),
    (S.morPolyfold Ψ).IsScDiffeoOn (S.transPolyfold Ψ Ψ) (S.hat Ψ) (S.hatInv Ψ) univ univ :=
  fun h => z3_not_continuous_hat
    (continuousOn_univ.1 (h _ z3Construction z3Unif).isScSmoothOn.continuousOn)

end Z3

/-! ### The condition `F(α) ≠ ∅` -/

section Empty

variable (C : GCT.{u})

theorem emptyUnif_false (Ψ : GCT.Unif fun _ : C.Obj => (∅ : Set C.LocalUniformizer)) : False := by
  obtain ⟨_, _, h⟩ := Ψ
  exact h

/-- **The empty polyfold structure** `F ≡ ∅`: Definition 17.1.8 as printed holds vacuously. -/
def emptyConstruction : C.PolyfoldConstruction where
  F _ := ∅
  isAt _ _ h := h.elim
  topM Ψ _ := (emptyUnif_false C Ψ).elim
  t2M Ψ _ := (emptyUnif_false C Ψ).elim
  paraM Ψ _ := (emptyUnif_false C Ψ).elim
  M Ψ _ := (emptyUnif_false C Ψ).elim
  isLocalScDiffeo_src Ψ _ := (emptyUnif_false C Ψ).elim
  isLocalScDiffeo_tgt Ψ _ := (emptyUnif_false C Ψ).elim
  isScSmoothMap_unit Ψ := (emptyUnif_false C Ψ).elim
  isScSmoothMap_inv Ψ _ := (emptyUnif_false C Ψ).elim
  isScSmoothMap_mul Ψ _ _ := (emptyUnif_false C Ψ).elim

/-- **`F(α) ≠ ∅` is not implied by Definition 17.1.8**: the empty structure on the reflection
GCT has no uniformizers. -/
theorem not_hasUniformizers_empty : ¬ (emptyConstruction GCT.reflection).HasUniformizers :=
  fun h => (h 0).ne_empty rfl

/-- **The covering condition of p. 752 is not implied by Definition 17.1.8**: the footprints of
the empty structure do not cover `|C| ≠ ∅`. -/
theorem not_hasCoveringUniformizers_empty :
    ¬ (emptyConstruction GCT.reflection).HasCoveringUniformizers := by
  intro h
  obtain ⟨Ψ, -⟩ := mem_iUnion.1 (h.symm ▸ mem_univ (GCT.reflection.toGroupoidStr.π 0))
  exact emptyUnif_false _ Ψ

end Empty

end PolyfoldConstruction

end GCT

end Polyfold
