import Polyfold.Chapter19.StrongBundleTopology
import Polyfold.Chapter19.BasicConstructionExamples
import Polyfold.Chapter16.FibreNegationStructure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.6 "A Strong Bundle Version" (pp. 890–899): the non-degenerate witness for Definitions
19.6.1–19.6.6 and the hypotheses of Theorem 19.6.8, Proposition 19.6.9, Theorem 19.6.11 and
Lemma 19.6.12.  Numbers and pages are the 2021 text's.

# The reflection bundle `ℤ/2 ⋉ (ℝ × ℝ) → ℤ/2 ⋉ ℝ`

`S = ℤ/2 ⋉ ℝ` (`ℤ/2 = ℤˣ` acting by `x ↦ ±x`, the groupoidal category of `reflectionBasic`),
`μ(x) = {x} × ℝ` and `μ(g, x) : (x, v) ↦ (g x, g v)`: the group acts on the fibres by `±1`, so
non-trivially (`reflBan_lift_neg`, `reflBan_lift_ne`).  The strong bundle uniformizer is the
identity of the trivial bundle `K = ℝ × ℝ → O = ℝ` (Chapter 3's `TrivialBundle.bundle 1 1`) with
the diagonal action; the transition data are `F_h(q) = (q, g, g q)` for `h = (o, g, g o)`, with
lifts `f̄_h(x, v) = (g x, g v)`, strong bundle isomorphisms (Definition 19.6.4 (A)).

* `reflBan` (`μ`), `reflBanUnif` (`Ψ̄`), `reflBanStr` (its structure (1) of Definition 19.6.1),
  `reflBanU` (Definition 19.6.3), `reflBanTD`, `reflBanBTD` (Definition 19.6.4),
  `reflBanBasic` (Definition 19.6.6).
* `reflBanBasic_hB` (`HasClassUniformizers`), `reflBanBasic_metrizable` (`T` and `T̄` are
  metrizable), `reflBan_fmapBar_neg` (`f̄_h = -Id` for `h = (o, -1, -o)`), and
  `reflBanBasic_witness`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid.Examples TrivialBundle

/-- The groupoidal category `ℤ/2 ⋉ ℝ`. -/
abbrev ReflCat : GroupoidalCategory.{0} := GroupoidalCategory.translation ℤˣ (Fin 1 → ℝ)

/-- The fibre `{x} × ℝ ≅ ℝ` of the trivial bundle, as a topological linear isomorphism. -/
def reflFibCLE (x : Fin 1 → ℝ) : proj 1 1 ⁻¹' {x} ≃L[ℝ] (Fin 1 → ℝ) :=
  { toLinearEquiv := (fibEquiv (n := 1) (k := 1) x).linearEquiv ℝ
    continuous_toFun := continuous_snd.comp continuous_subtype_val
    continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk fun _ => rfl }

theorem reflFibCLE_symm_apply (x v : Fin 1 → ℝ) :
    ((reflFibCLE x).symm v : (Fin 1 → ℝ) × (Fin 1 → ℝ)) = (x, v) := rfl

theorem reflFibCLE_apply (x : Fin 1 → ℝ) (w : proj 1 1 ⁻¹' {x}) :
    reflFibCLE x w = (w : (Fin 1 → ℝ) × (Fin 1 → ℝ)).2 := rfl

/-- `v ↦ g v` for `g ∈ ℤˣ = {±1}`, as a bounded linear operator. -/
def unitsCLM (g : ℤˣ) : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ) :=
  ((g : ℤ) : ℝ) • ContinuousLinearMap.id ℝ (Fin 1 → ℝ)

theorem unitsCLM_apply (g : ℤˣ) (v : Fin 1 → ℝ) : unitsCLM g v = g • v := by
  change ((g : ℤ) : ℝ) • v = g • v
  rw [Units.smul_def, Int.cast_smul_eq_zsmul]

/-- `μ(g, x) : {x} × ℝ → {g x} × ℝ`, `(x, v) ↦ (g x, g v)`. -/
def reflLift (φ : ReflCat.Mor) :
    proj 1 1 ⁻¹' {ReflCat.toGroupoidStr.src φ} →L[ℝ] proj 1 1 ⁻¹' {ReflCat.toGroupoidStr.tgt φ} :=
  ((reflFibCLE (ReflCat.toGroupoidStr.tgt φ)).symm : (Fin 1 → ℝ) →L[ℝ] _).comp
    ((unitsCLM φ.1).comp (reflFibCLE (ReflCat.toGroupoidStr.src φ) : _ →L[ℝ] (Fin 1 → ℝ)))

theorem reflLift_apply (φ : ReflCat.Mor) (v : proj 1 1 ⁻¹' {ReflCat.toGroupoidStr.src φ}) :
    (reflLift φ v : (Fin 1 → ℝ) × (Fin 1 → ℝ)) =
      (φ.1 • φ.2, φ.1 • (v : (Fin 1 → ℝ) × (Fin 1 → ℝ)).2) := by
  change (ReflCat.toGroupoidStr.tgt φ, unitsCLM φ.1 (v : (Fin 1 → ℝ) × (Fin 1 → ℝ)).2) = _
  rw [unitsCLM_apply]
  rfl

theorem reflLift_unit (e : (Fin 1 → ℝ) × (Fin 1 → ℝ))
    (h : proj 1 1 e = ReflCat.toGroupoidStr.src (ReflCat.toGroupoidStr.unit (proj 1 1 e))) :
    (reflLift (ReflCat.toGroupoidStr.unit (proj 1 1 e)) ⟨e, h⟩ :
      (Fin 1 → ℝ) × (Fin 1 → ℝ)) = e := by
  rw [reflLift_apply]
  change ((1 : ℤˣ) • e.1, (1 : ℤˣ) • e.2) = e
  rw [one_smul, one_smul]

theorem reflLift_comp (φ' φ : ReflCat.Mor)
    (hc : ReflCat.toGroupoidStr.src φ' = ReflCat.toGroupoidStr.tgt φ)
    (e : (Fin 1 → ℝ) × (Fin 1 → ℝ)) (h : proj 1 1 e = ReflCat.toGroupoidStr.src φ) :
    (reflLift (ReflCat.toGroupoidStr.comp φ' φ)
        ⟨e, h.trans (ReflCat.toGroupoidStr.src_comp φ' φ hc).symm⟩ :
          (Fin 1 → ℝ) × (Fin 1 → ℝ)) =
      reflLift φ' ⟨reflLift φ ⟨e, h⟩,
        (show proj 1 1 (reflLift φ ⟨e, h⟩ : (Fin 1 → ℝ) × (Fin 1 → ℝ)) =
          ReflCat.toGroupoidStr.tgt φ from (reflLift φ ⟨e, h⟩).2).trans hc.symm⟩ := by
  rw [reflLift_apply, reflLift_apply, reflLift_apply]
  have hc' : φ'.2 = φ.1 • φ.2 := hc
  change ((φ'.1 * φ.1) • φ.2, (φ'.1 * φ.1) • e.2) = (φ'.1 • φ'.2, φ'.1 • φ.1 • e.2)
  rw [mul_smul, mul_smul, hc']

/-- **The functor `μ : ℤ/2 ⋉ ℝ → Ban`**, `μ(x) = {x} × ℝ`, `μ(g, x)(x, v) = (g x, g v)`. -/
abbrev reflBan : ReflCat.BanFunctor where
  E := (Fin 1 → ℝ) × (Fin 1 → ℝ)
  P := proj 1 1
  banachable x := (bundle 1 1).banachable x
  lift := reflLift
  lift_unit := reflLift_unit
  lift_comp := reflLift_comp

theorem reflBan_act (q : pullbackSpace reflBan.P ReflCat.toGroupoidStr.src) :
    reflBan.act q = (q : ReflCat.Mor × reflBan.E).1.1 • (q : ReflCat.Mor × reflBan.E).2 := by
  obtain ⟨⟨⟨g, x⟩, e⟩, hq⟩ := q
  have hx : e.1 = x := hq
  change (reflLift (g, x) ⟨e, hq⟩ : (Fin 1 → ℝ) × (Fin 1 → ℝ)) = g • e
  rw [reflLift_apply]
  change (g • x, g • e.2) = (g • e.1, g • e.2)
  rw [hx]

/-- **The group acts on the fibres by `-1`**: `μ(-1, 0)(0, v) = (0, -v)`. -/
theorem reflBan_lift_neg (v : Fin 1 → ℝ) :
    (reflBan.lift ((-1 : ℤˣ), 0) ⟨(0, v), rfl⟩ : (Fin 1 → ℝ) × (Fin 1 → ℝ)) = (0, -v) := by
  change (reflLift ((-1 : ℤˣ), 0) ⟨(0, v), rfl⟩ : (Fin 1 → ℝ) × (Fin 1 → ℝ)) = _
  rw [reflLift_apply]
  change ((-1 : ℤˣ) • (0 : Fin 1 → ℝ), (-1 : ℤˣ) • v) = _
  rw [units_smul_rn_neg_one, units_smul_rn_neg_one, neg_zero]

/-- **The action on the fibres is non-trivial.** -/
theorem reflBan_lift_ne :
    (reflBan.lift ((-1 : ℤˣ), 0) ⟨(0, 1), rfl⟩ : (Fin 1 → ℝ) × (Fin 1 → ℝ)) ≠ (0, 1) := by
  rw [reflBan_lift_neg]
  intro h
  have := congrFun (congrArg Prod.snd h) 0
  simp only [Pi.neg_apply, Pi.one_apply] at this
  linarith

/-! ### The strong bundle uniformizer -/

/-- `x ↦ g x` on `ℝ` is `C^∞`. -/
theorem contDiff_units_smul (g : ℤˣ) : ContDiff ℝ ∞ fun x : Fin 1 → ℝ => g • x := by
  have : (fun x : Fin 1 → ℝ => g • x) = unitsCLM g := funext fun x => (unitsCLM_apply g x).symm
  rw [this]
  exact (unitsCLM g).contDiff

theorem smul_eq_prodLinMap (g : ℤˣ) :
    (fun a : (Fin 1 → ℝ) × (Fin 1 → ℝ) => g • a) = prodLinMap (fun x => g • x) (unitsCLM g) :=
  funext fun a => Prod.ext rfl (unitsCLM_apply g a.2).symm

/-- **`g ∗ ·` is a strong bundle map of `ℝ × ℝ → ℝ` covering `g ∗ ·`.** -/
theorem reflHmap (g : ℤˣ) :
    (bundle 1 1).IsStrongBundleMap (bundle 1 1) (fun x => g • x) (fun a => g • a) := by
  rw [smul_eq_prodLinMap]
  exact isStrongBundleMap_prodLinMap (contDiff_units_smul g) (unitsCLM g)

theorem reflBan_act_mk (g : ℤˣ) (a : (Fin 1 → ℝ) × (Fin 1 → ℝ)) :
    reflBan.act ⟨((g, a.1), a), rfl⟩ = g • a := reflBan_act _

/-- The functor `Ψ̄ : ℤ/2 ⋉ (ℝ × ℝ) → E_μ`, `a ↦ a`, `(g, a) ↦ ((g, a₁), a)`. -/
def reflBanFunctor :
    GroupoidFunctor (GroupoidStr.translation ℤˣ ((Fin 1 → ℝ) × (Fin 1 → ℝ)))
      reflBan.cat.toGroupoidStr where
  obj a := a
  mor q := ⟨((q.1, q.2.1), q.2), rfl⟩
  src_mor _ := rfl
  tgt_mor q := reflBan_act_mk q.1 q.2
  mor_comp φ ψ h := by
    have hc : ((⟨((φ.1, φ.2.1), φ.2), rfl⟩ : reflBan.cat.Mor) : ReflCat.Mor × reflBan.E).2 =
        reflBan.act ⟨((ψ.1, ψ.2.1), ψ.2), rfl⟩ := h.trans (reflBan_act_mk ψ.1 ψ.2).symm
    exact Subtype.ext (BanFunctor.morComp_val hc).symm
  mor_unit _ := rfl

/-- **The strong bundle uniformizer `Ψ̄`** (as a functor into `E_μ`): the identity of
`K = ℝ × ℝ` with the diagonal action of `ℤ/2`. -/
abbrev reflBanUnif : reflBan.cat.Uniformizer where
  O := (Fin 1 → ℝ) × (Fin 1 → ℝ)
  P := (bundle 1 1).toMPolyfold0
  G := ℤˣ
  smooth_smul g := (reflHmap g).isScSmoothMap
  functor := reflBanFunctor
  injective_obj := injective_id
  full := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => by
    obtain ⟨⟨⟨g, y⟩, e⟩, hψ⟩ := ψ
    have he : e = x := hs
    subst he
    have hy : e.1 = y := hψ
    subst hy
    exact ⟨(g, e), rfl, (reflBan_act_mk g e).symm.trans ht, rfl⟩
  faithful := (GroupoidFunctor.faithful_iff _).2 fun φ φ' _ _ he =>
    Prod.ext (congrArg (fun q : reflBan.cat.Mor => (q : ReflCat.Mor × reflBan.E).1.1) he)
      (congrArg (fun q : reflBan.cat.Mor => (q : ReflCat.Mor × reflBan.E).2) he)

/-- **The structure (1) of Definition 19.6.1 on `Ψ̄`**: `p : ℝ × ℝ → ℝ` the trivial bundle,
`Ψ : ℤ/2 ⋉ ℝ → S` the identity, `Ψ̄ : K_o → μ(o)` the identity. -/
abbrev reflBanStr : StrongBundleStr reflBan reflBanUnif where
  O := Fin 1 → ℝ
  PO := rnPolyfold 1
  smooth_smul := isScSmoothMap_units_smul
  functor := GroupoidFunctor.id _
  injective_obj := injective_id
  full := (GroupoidFunctor.full_iff _).2 fun _ _ ψ hs ht => ⟨ψ, hs, ht, rfl⟩
  faithful := (GroupoidFunctor.faithful_iff _).2 fun _ _ _ _ h => h
  p := proj 1 1
  B := bundle 1 1
  toMPolyfold0_eq := rfl
  p_smul _ _ := rfl
  isStrongBundleMap_smul := reflHmap
  P_obj _ := rfl
  mor_fst _ _ := rfl
  fiberCLE _ := ContinuousLinearEquiv.refl ℝ _
  fiberCLE_apply _ _ := rfl

/-- **The strong bundle uniformizer construction** `F̄(x) = {Ψ̄}` (Definition 19.6.3). -/
abbrev reflBanU : StrongBundleUniformizerConstruction reflBan where
  F _ := {reflBanUnif}
  str Ψe h := (mem_singleton_iff.1 h.choose_spec).symm ▸ reflBanStr
  isAt α Ψe h := by
    have h' : Ψe = reflBanUnif := h
    subst h'
    exact ⟨α, rfl⟩

/-- The member `Ψ̄` of `F̄`. -/
abbrev reflΨ : reflBanU.Unif := ⟨reflBanUnif, 0, rfl⟩

theorem reflBanU_unif_eq (Ψ : reflBanU.Unif) : Ψ = reflΨ := by
  obtain ⟨Ψe, α, h⟩ := Ψ
  exact Subtype.ext (mem_singleton_iff.1 h)

theorem reflBanU_base_eq (Ψ : reflBanU.base.Unif) : Ψ.1 = reflBanStr.toBase := by
  obtain ⟨Ψ₁, α, Ψe, hΨe, rfl⟩ := Ψ
  have hΨe' : Ψe = reflBanUnif := hΨe
  subst hΨe'
  rfl

/-- Elements of `M(Ψ, Ψ)` are determined by their source and group element. -/
theorem reflBase_trans_ext (h₁ h₂ : reflBanStr.toBase.Trans reflBanStr.toBase)
    (hs : h₁.src = h₂.src) (hk : h₁.mor.1 = h₂.mor.1) : h₁ = h₂ := by
  have a₁ : h₁.mor.2 = h₁.src := h₁.src_mor
  have a₂ : h₂.mor.2 = h₂.src := h₂.src_mor
  have hm : h₁.mor = h₂.mor := Prod.ext hk (by rw [a₁, a₂, hs])
  have b₁ : h₁.mor.1 • h₁.mor.2 = h₁.tgt := h₁.tgt_mor
  have b₂ : h₂.mor.1 • h₂.mor.2 = h₂.tgt := h₂.tgt_mor
  exact TransitionSet.ext hs hm (by rw [← b₁, ← b₂, hm])

/-- **The transition data of the underlying construction**: `F_h(q) = (q, g, g q)` for
`h = (o, g, g o)` (keyed by the group element, `V(o) = ℝ`). -/
def reflBanTD : reflBanU.base.TransitionData :=
  UniformizerConstruction.TransitionData.ofKey (U := reflBanU.base)
    (Prod.fst : ℤˣ × (Fin 1 → ℝ) → ℤˣ) (fun _ _ _ => univ)
    (fun Ψ Ψ' => by
      obtain ⟨Ψ₁, hΨ₁⟩ := Ψ; obtain ⟨Ψ₂, hΨ₂⟩ := Ψ'
      obtain rfl : Ψ₁ = reflBanStr.toBase := reflBanU_base_eq ⟨Ψ₁, hΨ₁⟩
      obtain rfl : Ψ₂ = reflBanStr.toBase := reflBanU_base_eq ⟨Ψ₂, hΨ₂⟩
      exact reflBase_trans_ext)
    (fun Ψ Ψ' => by
      obtain ⟨Ψ₁, hΨ₁⟩ := Ψ; obtain ⟨Ψ₂, hΨ₂⟩ := Ψ'
      obtain rfl : Ψ₁ = reflBanStr.toBase := reflBanU_base_eq ⟨Ψ₁, hΨ₁⟩
      obtain rfl : Ψ₂ = reflBanStr.toBase := reflBanU_base_eq ⟨Ψ₂, hΨ₂⟩
      intro h q
      exact ⟨fun _ => ⟨reflBanStr.toBase.hat (h.mor.1, q), rfl, rfl⟩, fun _ => mem_univ _⟩)
    (fun _ _ _ => isOpen_univ)
    (fun Ψ Ψ' => by
      obtain ⟨Ψ₁, hΨ₁⟩ := Ψ; obtain ⟨Ψ₂, hΨ₂⟩ := Ψ'
      obtain rfl : Ψ₁ = reflBanStr.toBase := reflBanU_base_eq ⟨Ψ₁, hΨ₁⟩
      obtain rfl : Ψ₂ = reflBanStr.toBase := reflBanU_base_eq ⟨Ψ₂, hΨ₂⟩
      intro h
      refine ⟨fun q => h.mor.1 • q, fun q => h.mor.1⁻¹ • q, univ,
        ⟨isScSmoothMap_units_smul _, isScSmoothMap_units_smul _, mapsTo_univ _ _,
          mapsTo_univ _ _, fun x _ => inv_smul_smul _ x, fun y _ => smul_inv_smul _ y⟩,
        fun h' hk => ?_⟩
      have a : h'.mor.2 = h'.src := h'.src_mor
      have b : h'.mor.1 • h'.mor.2 = h'.tgt := h'.tgt_mor
      change h.mor.1 • h'.src = h'.tgt
      rw [← hk, ← a, b])
    (fun _ _ => rfl)
    (fun _ _ h => congrArg (·⁻¹) h)
    (fun _ _ _ _ _ _ h₁ h₂ => congrArg₂ (· * ·) h₁ h₂)
    (fun Ψ => by
      obtain ⟨Ψ₁, hΨ₁⟩ := Ψ
      obtain rfl : Ψ₁ = reflBanStr.toBase := reflBanU_base_eq ⟨Ψ₁, hΨ₁⟩
      intro _ _ _; rfl)

/-- `F_h(q) = (q, g, g q)`. -/
theorem reflBanTD_map (k : (reflBanU.baseUnif reflΨ).1.Trans (reflBanU.baseUnif reflΨ).1)
    (q : Fin 1 → ℝ) :
    reflBanTD.map _ _ k q = reflBanStr.toBase.hat (k.mor.1, q) := by
  change keyMap (Prod.fst : ℤˣ × (Fin 1 → ℝ) → ℤˣ) k q = _
  exact keyMap_eq (Ψ := reflBanStr.toBase) (Ψ' := reflBanStr.toBase)
    (Prod.fst : ℤˣ × (Fin 1 → ℝ) → ℤˣ) reflBase_trans_ext (h := k) (q := q)
    (reflBanStr.toBase.hat (k.mor.1, q)) rfl rfl

/-- `f_h(q) = g q`. -/
theorem reflBanTD_fmap (k : (reflBanU.baseUnif reflΨ).1.Trans (reflBanU.baseUnif reflΨ).1) :
    reflBanTD.fmap _ _ k = fun q : Fin 1 → ℝ => k.mor.1 • q :=
  funext fun q => by
    rw [UniformizerConstruction.TransitionData.fmap, reflBanTD_map]
    rfl

/-- **`f̄_h(x, v) = (g x, g v)`.** -/
theorem reflBan_fmapBar
    (k : (reflBanU.baseUnif reflΨ).1.Trans (reflBanU.baseUnif reflΨ).1) :
    reflBanU.fmapBar reflBanTD reflΨ reflΨ k = fun a : (Fin 1 → ℝ) × (Fin 1 → ℝ) => k.mor.1 • a :=
  funext fun a => by
    have hq : (reflBanU.strU reflΨ).p a ∈ reflBanTD.dom _ _ k := mem_univ _
    have e := StrongBundleUniformizerConstruction.obj_fmapBar hq
    change reflBanU.fmapBar reflBanTD reflΨ reflΨ k a = reflBan.act _ at e
    rw [e, reflBan_act]
    change (reflBanTD.map _ _ k a.1).mor.1 • a = _
    rw [reflBanTD_map]
    rfl

/-- **Definition 19.6.4 (A) for the reflection bundle**: `f̄_h = g ∗ ·` is a strong bundle
isomorphism covering `f_h = g ∗ ·`. -/
def reflBanBTD : reflBanU.BundleTransitionData where
  toTD := reflBanTD
  diffeo_bar Ψ Ψ' k := by
    obtain rfl := reflBanU_unif_eq Ψ
    obtain rfl := reflBanU_unif_eq Ψ'
    rw [reflBanTD_fmap, reflBan_fmapBar]
    have hiso := StrongBundle.isStrongBundleIsoOn_univ_of_inverse (reflHmap k.mor.1)
      (reflHmap k.mor.1⁻¹) (isScSmoothMap_units_smul _) (isScSmoothMap_units_smul _)
      (fun x => inv_smul_smul _ x) (fun x => smul_inv_smul _ x) (fun y => inv_smul_smul _ y)
      (fun y => smul_inv_smul _ y)
    obtain ⟨g, Φinv, hL⟩ := StrongBundle.IsStrongBundleIsoOn.exists_isLocalIso₂ hiso
    refine ⟨g, Φinv, ?_⟩
    have hdom : reflBanTD.dom (reflBanU.baseUnif reflΨ) (reflBanU.baseUnif reflΨ) k = univ := rfl
    rw [hdom, image_univ_of_surjective fun y => ⟨k.mor.1⁻¹ • y, smul_inv_smul _ y⟩]
    exact hL

/-- **The basic strong bundle construction** of the reflection bundle (Definition 19.6.6). -/
abbrev reflBanBasic : ReflCat.BasicStrongBundleConstruction reflBan := ⟨reflBanU, ⟦reflBanBTD⟧⟩

/-- Every class of `S` meets `F` (the hypothesis of Theorem 19.6.8). -/
theorem reflBanBasic_hB : reflBanBasic.base.U.HasClassUniformizers := fun z =>
  Quotient.inductionOn z fun α => ⟨α, rfl, reflBanStr.toBase, reflBanUnif, rfl, rfl⟩

/-- **The natural topologies `T` on `|S|` and `T̄` on `|E|` are metrizable** (the first since
`|Ψ|` is onto, the second by Proposition 19.6.9). -/
theorem reflBanBasic_metrizable :
    @MetrizableSpace _ (reflBanBasic.topS reflBanBasic_hB) ∧
      @MetrizableSpace _ (reflBanBasic.topE reflBanBasic_hB) := by
  have hS : @MetrizableSpace _ (reflBanBasic.topS reflBanBasic_hB) :=
    reflBanBasic.base.metrizableSpace_natTop_of_surjective reflBanBasic_hB (α := 0)
      (Ψ := reflBanStr.toBase) ⟨reflBanUnif, rfl, rfl⟩ fun z => by
        obtain ⟨x, rfl⟩ := ReflCat.toGroupoidStr.surjective_π z
        exact ⟨x, rfl⟩
  exact ⟨hS, (reflBanBasic.proposition_19_6_9 reflBanBasic_hB).1 hS⟩

/-- **The lift for `h = (o, -1, -o)` is `f̄_h = -Id`** (a non-trivial strong bundle
isomorphism). -/
theorem reflBan_fmapBar_neg :
    reflBanU.fmapBar reflBanTD reflΨ reflΨ ((reflBanU.baseUnif reflΨ).1.hat (-1, 0)) =
      fun a => -a := by
  rw [reflBan_fmapBar]
  funext a
  change (-1 : ℤˣ) • a = -a
  rw [Units.neg_smul, one_smul]

/-- **The non-degenerate witness for §19.6**: every class of `S` meets `F`; `ℤ/2` acts on the
fibres non-trivially; the transition data have a lift `f̄_h = -Id`; `T` and `T̄` are metrizable;
the transition sets `M(Ψ̄, Ψ̄)` are metrizable. -/
theorem reflBanBasic_witness :
    reflBanBasic.base.U.HasClassUniformizers ∧
      (reflBan.lift ((-1 : ℤˣ), 0) ⟨(0, 1), rfl⟩ : (Fin 1 → ℝ) × (Fin 1 → ℝ)) ≠ (0, 1) ∧
      reflBanU.fmapBar reflBanTD reflΨ reflΨ ((reflBanU.baseUnif reflΨ).1.hat (-1, 0)) =
        (fun a => -a) ∧
      @MetrizableSpace _ (reflBanBasic.topS reflBanBasic_hB) ∧
      @MetrizableSpace _ (reflBanBasic.topE reflBanBasic_hB) ∧
      MetrizableSpace (reflBanBasic.MBar (reflBanU.toEUnif reflΨ) (reflBanU.toEUnif reflΨ)) :=
  ⟨reflBanBasic_hB, reflBan_lift_ne, reflBan_fmapBar_neg, reflBanBasic_metrizable.1,
    reflBanBasic_metrizable.2, reflBanBasic.lemma_19_6_12 _ _⟩

end GroupoidalCategory

end Polyfold
