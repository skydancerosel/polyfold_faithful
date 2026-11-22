import Polyfold.Chapter17.BundleModelComparison
import Polyfold.Chapter17.ModelExamples
import Polyfold.Chapter16.FibreNegationStructure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.7 "Strong Bundle Structures", pp. 824–828: the non-degenerate witness for **Definitions
17.7.1, 17.7.2, 17.7.3 and 17.7.4**, and for the strong bundle analogues of **Theorem 17.1.14**,
**Lemma 17.1.15** and **Theorem 17.1.18** (the bundle model `W_Ψ̄ → X_Ψ` and the comparison maps
`f̄_{Ψ̄,Ψ̄'}`).  Numbers and pages are the 2021 text's.

# The reflection bundle over `ℤ/2 ⋉ ℝ`

`C = ℤ/2 ⋉ ℝ` (`GCT.reflection`, `ℤ/2 = ℤˣ` acting by `x ↦ ±x`) with the polyfold structure
`reflectionConstruction` (`F(x) = {Ψ}`, `Ψ` the identity uniformizer).

* **Definition 17.7.1**: `reflMu`, the functor `μ(x) = ℝ`, `μ(g, x) = g · : ℝ → ℝ`; `reflV`, with
  the topology `T` on `|E_μ|` transported from `|ℤ/2 ⋉ (ℝ × ℝ)|` along the bijection
  `|kFunctor|` (`orbitHomeomorph`), metrizable by Definition 17.1.2.  `|P|` is surjective,
  continuous and open (`continuous_orbitProj`, `isOpenMap_orbitProj`).
* **Definition 17.7.2**: `reflUnif`, `Ψ̄ : ℤ/2 ⋉ K → E_μ` over `Ψ`, for the trivial strong bundle
  `K = ℝ × ℝ → ℝ` (Chapter 3's `TrivialBundle.bundle 1 1`) with the diagonal action
  `g ∗ (x, v) = (g x, g v)` (strong bundle maps by `isStrongBundleMap_prodLinMap`) and the fibre
  maps `(x, v) ↦ v`; `|Ψ̄|` is the homeomorphism `orbitHomeomorph` onto `|E_μ| = |P|⁻¹(|C|)`.
* **Definition 17.7.3**: `reflUC`, `F̄(x) = {Ψ̄}`.
* **Definition 17.7.4**: `reflQ`.  On the sheet `{a = (q, (g, q), g q)}` of `M(Ψ, Ψ)` the map
  `t̄(a, k) = g ∗ k` (`transT_eq`) is `(g ∗ ·) ∘ s̄`; so it is a strong bundle map
  (`isStrongBundleMap_transT`, by `StrongBundle.isStrongBundleMap_of_locally_eqOn`: being a
  strong bundle map is local over the base) and a local strong bundle isomorphism
  (`isLocalStrongBundleIso_transT`, the composite of the local isomorphism `s̄` over a sheet of `s`
  with the strong bundle isomorphism `g ∗ ·`, `StrongBundle.isStrongBundleIsoOn_of_eqOn`).
* **Non-degeneracy**: the fibres are `ℝ ≠ 0` (`reflV_fiber_ne_zero`); the generator `−1` acts on
  them by `v ↦ −v ≠ v` (`reflV_map_neg`, `reflV_map_ne`); in `|E_μ|` the classes of `(0, v)` and
  `(0, −v)` agree (`π_objMk_neg`) and differ from that of `(0, 0)` for `v ≠ 0`
  (`π_objMk_ne_zero`); `reflUnif_witness` collects Definition 17.7.2 for `Ψ̄`.
* **The models**: `reflSingle` (one copy of `Ψ̄`) and `reflPair` (two copies) are
  `BundleCoveringFamily`s.  `reflPair_bundleModel`: in `W_Ψ̄ → X_Ψ` for two copies, the structure
  map `μ = t̄` sends `(0, 1)` in the piece `false` along `(0, (−1, 0), 0)` to `(0, −1)` in the piece
  `true`, and the conclusions of the bundle analogue of Lemma 17.1.15 hold.
  `refl_bundleComparison`: the conclusions of the bundle analogue of Theorem 17.1.18 for one and
  two copies, and `|f̄|` separates the classes of `(0, 1)` and of `(0, 0)`.

## Readings and choices

* Definition 17.7.1 asks for some metrizable topology `T` on `|E_μ|`; we take the one for which
  `|ℤ/2 ⋉ K| → |E_μ|`, `|(x, v)| ↦ |(x, v)|`, is a homeomorphism, so that `|Ψ̄|` is one, as
  Definition 17.7.2 (3) requires.
* The strong bundle structure on `M(Ψ̄, Ψ̄)` is the pull-back `s*K` of
  `StrongBundleStructures.lean`.  No hypothesis beyond the text is used.
* Chapter 19 has the same bundle in its own setting (`reflBan`, §19.6); Chapter 17 cannot import
  it, so the few helpers it needs (`unitsCLE`, `fibCLE`) are stated here.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### Strong bundle maps that are locally strong bundle maps -/

/-- Two fibre maps with the same values into equal fibres: linearity of one gives that of the
other. -/
theorem isLinearMap_fiber_of_eq {X Y X' Y' : Type*} {P : Y → X} {P' : Y' → X'}
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
    {x : X} {z z' : X'} (hz : z = z') (F : P ⁻¹' {x} → P' ⁻¹' {z})
    (F' : P ⁻¹' {x} → P' ⁻¹' {z'}) (hF : ∀ v, (F v : Y') = F' v) (h' : IsLinearMap ℝ F') :
    IsLinearMap ℝ F := by
  subst hz
  obtain rfl : F = F' := funext fun v => Subtype.ext (hF v)
  exact h'

namespace StrongBundle

section Local

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  {B : StrongBundle PX P} {B' : StrongBundle PX' P'}

/-- **Being a strong bundle map is local over the base**: a map `Φ : Y → Y'` covering `f` which
agrees over an open neighbourhood of every point with a strong bundle map is one. -/
theorem isStrongBundleMap_of_locally_eqOn {f : X → X'} {Φ : Y → Y'}
    (hcov : ∀ y, P' (Φ y) = f (P y))
    (hloc : ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ (f₁ : X → X') (Φ₁ : Y → Y'),
      B.IsStrongBundleMap B' f₁ Φ₁ ∧ EqOn Φ Φ₁ (P ⁻¹' V)) :
    B.IsStrongBundleMap B' f Φ := by
  choose V hVo hxV f₁ Φ₁ h₁ hEq using hloc
  have hmem : ∀ y, y ∈ P ⁻¹' V (P y) := fun y => hxV (P y)
  have hmo : MapsTo Φ B.oneSet B'.oneSet := fun y hy => by
    rw [hEq (P y) (hmem y)]; exact (h₁ (P y)).mapsTo_oneSet hy
  refine ⟨hcov, fun x => ?_, ?_, hmo, ?_⟩
  · have hv : P ((0 : P ⁻¹' {x}) : Y) = x := (0 : P ⁻¹' {x}).2
    have hm0 : ((0 : P ⁻¹' {x}) : Y) ∈ P ⁻¹' V x := by
      change P _ ∈ V x; rw [hv]; exact hxV x
    have hz : f x = f₁ x x := by
      have h0 := hcov ((0 : P ⁻¹' {x}) : Y)
      rw [hEq x hm0, (h₁ x).covers, hv] at h0
      exact h0.symm
    refine isLinearMap_fiber_of_eq hz _ _ (fun v => ?_) ((h₁ x).fiber_linear x)
    exact hEq x (show P v ∈ V x by rw [show P v = x from v.2]; exact hxV x)
  · refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun y _ =>
      ⟨P ⁻¹' V (P y), (hVo _).preimage B.continuous, hmem y, subset_univ _, ?_⟩
    exact ((h₁ (P y)).isScSmoothMap.mono ((hVo _).preimage B.continuous)
      (subset_univ _)).congr fun y' hy' => (hEq _ hy').symm
  · refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun u _ => ?_
    have hU' : IsOpen ((P ∘ B.oneVal) ⁻¹' V (P (B.oneVal u))) :=
      (hVo _).preimage (B.continuous.comp B.continuous_oneVal)
    refine ⟨_, hU', hxV _, subset_univ _, ?_⟩
    refine ((h₁ (P (B.oneVal u))).isScSmoothMap_one.mono hU' (subset_univ _)).congr
      fun u' hu' => B'.oneVal_injective ?_
    simp only [StrongBundle.oneVal_oneRestrict]
    exact (hEq _ hu').symm

/-- A local strong bundle isomorphism stays one when the map and its base map are changed
outside `P⁻¹(U)` and `U`. -/
theorem isStrongBundleIsoOn_of_eqOn {f f₁ : X → X'} {Φ Φ₁ : Y → Y'}
    {h : B.IsStrongBundleMap B' f Φ} {h₁ : B.IsStrongBundleMap B' f₁ Φ₁} {U : Set X}
    {U' : Set X'} (hi : B.IsStrongBundleIsoOn B' h₁ U U') (hf : EqOn f₁ f U)
    (hΦ : EqOn Φ₁ Φ (P ⁻¹' U)) : B.IsStrongBundleIsoOn B' h U U' := by
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨Ψ, hΨ⟩ := hi.isScDiffeoOn_zero
  obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
  refine ⟨⟨g, hg.congr hf⟩, ⟨Ψ, hΨ.congr hΦ⟩, ⟨Ψ₁, hΨ₁.congr fun u hu => ?_⟩⟩
  apply B'.oneVal_injective
  simp only [StrongBundle.oneVal_oneRestrict]
  exact hΦ hu

end Local

end StrongBundle

namespace GCT.VectorBundle.ReflectionBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor EpGroupoid.Examples TrivialBundle
  StrongBundle

/-- `v ↦ g v` on `ℝ`, `g ∈ ℤˣ = {±1}`, as a topological linear isomorphism. -/
def unitsCLE (g : ℤˣ) : (Fin 1 → ℝ) ≃L[ℝ] (Fin 1 → ℝ) where
  toFun v := g • v
  invFun v := g⁻¹ • v
  map_add' := smul_add g
  map_smul' a v := smul_comm g a v
  left_inv := inv_smul_smul g
  right_inv := smul_inv_smul g
  continuous_toFun := continuous_const_smul g
  continuous_invFun := continuous_const_smul g⁻¹

@[simp] theorem unitsCLE_apply (g : ℤˣ) (v : Fin 1 → ℝ) : unitsCLE g v = g • v := rfl

/-- **The functor `μ : ℤ/2 ⋉ ℝ → Ban`**: `μ(x) = ℝ`, `μ(g, x) = g · : ℝ → ℝ`. -/
def reflMu : BanachFunctor GCT.reflection.toGroupoidalCategory where
  V _ := Fin 1 → ℝ
  map φ := unitsCLE φ.1
  act_unit e h := by
    obtain ⟨α, v⟩ := e
    change (⟨(1 : ℤˣ) • α, (1 : ℤˣ) • v⟩ : Σ _ : Fin 1 → ℝ, Fin 1 → ℝ) = ⟨α, v⟩
    rw [one_smul, one_smul]
  act_comp φ ψ hφψ e h := by
    obtain ⟨α, v⟩ := e
    change (⟨(φ.1 * ψ.1) • ψ.2, (φ.1 * ψ.1) • v⟩ : Σ _ : Fin 1 → ℝ, Fin 1 → ℝ) =
      ⟨φ.1 • φ.2, φ.1 • ψ.1 • v⟩
    have : φ.2 = ψ.1 • ψ.2 := hφψ
    rw [mul_smul, mul_smul, this]

/-- The total space `K = ℝ × ℝ` of the trivial bundle over `O = ℝ`. -/
abbrev K : Type := (Fin 1 → ℝ) × (Fin 1 → ℝ)

/-- `(α, e) ↦ (α, e)`: an object of `E_μ` as a point of `K`. -/
def toPair (e : reflMu.EObj) : K := (e.1, e.2)

@[simp] theorem toPair_objMk (k : K) : toPair (reflMu.objMk k.1 k.2) = k := rfl

@[simp] theorem objMk_toPair (e : reflMu.EObj) : reflMu.objMk (toPair e).1 (toPair e).2 = e := rfl

/-- `μ(φ)(e) = φ.1 • e` read in `K`. -/
theorem toPair_act (φ : GCT.reflection.Mor) (e : reflMu.EObj)
    (h : reflMu.base e = GCT.reflection.toGroupoidStr.src φ) :
    toPair (reflMu.act φ e h) = φ.1 • toPair e := by
  obtain ⟨α, v⟩ := e
  obtain ⟨g, x⟩ := φ
  change α = x at h
  subst h
  rfl

/-- The functor `ℤ/2 ⋉ K → E_μ`, `k ↦ (k₁, k₂)`, `(g, k) ↦ ((g, k₁), (k₁, k₂))`. -/
def kFunctor : GroupoidFunctor (GroupoidStr.translation ℤˣ K) reflMu.groupoid where
  obj k := reflMu.objMk k.1 k.2
  mor x := ⟨((x.1, x.2.1), reflMu.objMk x.2.1 x.2.2), rfl⟩
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp x y h := by
    have hy : x.2 = y.1 • y.2 := h
    have hc : reflMu.groupoid.src (⟨((x.1, x.2.1), reflMu.objMk x.2.1 x.2.2), rfl⟩ : reflMu.EMor) =
        reflMu.groupoid.tgt (⟨((y.1, y.2.1), reflMu.objMk y.2.1 y.2.2), rfl⟩ : reflMu.EMor) := by
      change reflMu.objMk x.2.1 x.2.2 = reflMu.objMk (y.1 • y.2).1 (y.1 • y.2).2
      rw [hy]
    obtain ⟨h1, h2⟩ := groupoid_comp_of hc
    refine EMor.ext ?_ ?_
    · rw [h1]
      change ((x.1 * y.1, y.2.1) : ℤˣ × (Fin 1 → ℝ)) = (x.1 * y.1, y.2.1)
      rfl
    · rw [h2]; rfl
  mor_unit _ := rfl

theorem kFunctor_orbitMap_bijective : Bijective kFunctor.orbitMap := by
  refine ⟨fun z z' hz => ?_, fun z => ?_⟩
  · induction z using Quotient.inductionOn with | h k => ?_
    induction z' using Quotient.inductionOn with | h k' => ?_
    obtain ⟨a, ha, hb⟩ := (GroupoidStr.π_eq_π_iff _).1 hz
    have ha' : a.e = reflMu.objMk k.1 k.2 := ha
    have hb' : reflMu.act a.φ a.e a.2 = reflMu.objMk k'.1 k'.2 := hb
    have e := congrArg toPair hb'
    rw [toPair_act, ha', toPair_objMk, toPair_objMk] at e
    exact (GroupoidStr.π_eq_π_iff _).2 ⟨(a.φ.1, k), rfl, e⟩
  · induction z using Quotient.inductionOn with | h e => ?_
    exact ⟨(GroupoidStr.translation ℤˣ K).π (toPair e), rfl⟩

/-- `|ℤ/2 ⋉ K| ≃ |E_μ|`. -/
def orbitEquiv : (GroupoidStr.translation ℤˣ K).OrbitSpace ≃ reflMu.groupoid.OrbitSpace :=
  Equiv.ofBijective _ kFunctor_orbitMap_bijective

/-- **The topology `T` on `|E_μ|`**: the one making `|ℤ/2 ⋉ K| ≃ |E_μ|` a homeomorphism. -/
instance reflTopE : TopologicalSpace reflMu.groupoid.OrbitSpace :=
  TopologicalSpace.coinduced kFunctor.orbitMap inferInstance

/-- `|ℤ/2 ⋉ K| ≃ₜ |E_μ|`. -/
def orbitHomeomorph : (GroupoidStr.translation ℤˣ K).OrbitSpace ≃ₜ reflMu.groupoid.OrbitSpace where
  toEquiv := orbitEquiv
  continuous_toFun := continuous_coinduced_rng
  continuous_invFun := continuous_coinduced_dom.2
    (continuous_id.congr fun x => (orbitEquiv.symm_apply_apply x).symm)

/-- `ℝ ∋ x ↦ g x` is `C^∞`. -/
theorem contDiff_units_smul (g : ℤˣ) : ContDiff ℝ ∞ fun x : Fin 1 → ℝ => g • x :=
  (unitsCLE g : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ)).contDiff

theorem smul_eq_prodLinMap (g : ℤˣ) :
    (fun a : K => g • a) = prodLinMap (fun x => g • x) (unitsCLE g : (Fin 1 → ℝ) →L[ℝ] _) :=
  rfl

/-- **`g ∗ ·` is a strong bundle map of `K = ℝ × ℝ → ℝ` covering `g ∗ ·`.** -/
theorem isStrongBundleMap_smul (g : ℤˣ) :
    (bundle 1 1).IsStrongBundleMap (bundle 1 1) (fun x => g • x) (fun a : K => g • a) := by
  rw [smul_eq_prodLinMap]
  exact isStrongBundleMap_prodLinMap (contDiff_units_smul g) _

theorem isScSmoothMap_smul_K (g : ℤˣ) :
    (bundle 1 1).toMPolyfold0.IsScSmoothMap (bundle 1 1).toMPolyfold0 fun a : K => g • a :=
  (isStrongBundleMap_smul g).isScSmoothMap

instance metrizable_orbitK : MetrizableSpace (GroupoidStr.translation ℤˣ K).OrbitSpace :=
  metrizableSpace_translation_orbitSpace isScSmoothMap_smul_K

instance reflMetrizableE : MetrizableSpace reflMu.groupoid.OrbitSpace :=
  orbitHomeomorph.symm.isEmbedding.metrizableSpace

theorem orbitProj_orbitMap (k : K) :
    reflMu.proj.orbitMap (kFunctor.orbitMap ((GroupoidStr.translation ℤˣ K).π k)) =
      GCT.reflection.toGroupoidStr.π k.1 := rfl

theorem continuous_πK : Continuous (GroupoidStr.translation ℤˣ K).π := continuous_quot_mk

theorem continuous_orbitProj : Continuous reflMu.proj.orbitMap := by
  refine continuous_coinduced_dom.2 (continuous_coinduced_dom.2 ?_)
  exact (continuous_quot_mk.comp continuous_fst :
    Continuous fun k : K => GCT.reflection.toGroupoidStr.π k.1)

theorem surjective_πE : Surjective (kFunctor.orbitMap ∘ (GroupoidStr.translation ℤˣ K).π) :=
  kFunctor_orbitMap_bijective.2.comp (GroupoidStr.surjective_π _)

theorem isOpenMap_orbitProj : IsOpenMap reflMu.proj.orbitMap := by
  intro U hU
  have hU' : IsOpen ((kFunctor.orbitMap ∘ (GroupoidStr.translation ℤˣ K).π) ⁻¹' U) :=
    hU.preimage (orbitHomeomorph.continuous.comp continuous_πK)
  have he : reflMu.proj.orbitMap '' U = (GCT.reflection.toGroupoidStr.π ∘ Prod.fst) ''
      ((kFunctor.orbitMap ∘ (GroupoidStr.translation ℤˣ K).π) ⁻¹' U) := by
    conv_lhs => rw [← image_preimage_eq U surjective_πE]
    rw [image_image]
    rfl
  rw [he]
  have hc : ∀ g : ℤˣ, Continuous fun y : Fin 1 → ℝ => g • y := fun g => continuous_const_smul g
  exact (GroupoidStr.isOpenMap_π_translation hc).comp isOpenMap_fst _ hU'

/-- **The non-degenerate witness of 2021 Definition 17.7.1**: `μ(x) = ℝ`, `μ(g, x) = g ·`, with
the topology of `|E_μ| ≅ |ℤ/2 ⋉ (ℝ × ℝ)|`. -/
def reflV : GCT.reflection.VectorBundle where
  toBanachFunctor := reflMu
  topE := reflTopE
  metrizableE := reflMetrizableE
  continuous_fiber α := orbitHomeomorph.continuous.comp
    (continuous_πK.comp (continuous_const.prodMk continuous_id))
  surjective_orbitProj z := by
    induction z using Quotient.inductionOn with | h x => ?_
    exact ⟨reflMu.groupoid.π (reflMu.objMk x 0), rfl⟩
  continuous_orbitProj := continuous_orbitProj
  isOpenMap_orbitProj := isOpenMap_orbitProj

/-- The topology `T` of `|E_μ|` (Definition 17.7.1), as an instance for `reflV`. -/
instance topE_reflV : TopologicalSpace reflV.groupoid.OrbitSpace := reflV.topE

/-! ### The strong bundle uniformizer -/

/-- The fibre `{x} × ℝ ≅ ℝ` of the trivial bundle, as a topological linear isomorphism. -/
def fibCLE (x : Fin 1 → ℝ) : proj 1 1 ⁻¹' {x} ≃L[ℝ] (Fin 1 → ℝ) :=
  { toLinearEquiv := (fibEquiv (n := 1) (k := 1) x).linearEquiv ℝ
    continuous_toFun := continuous_snd.comp continuous_subtype_val
    continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk fun _ => rfl }

@[simp] theorem fibCLE_apply (x : Fin 1 → ℝ) (w : proj 1 1 ⁻¹' {x}) :
    fibCLE x w = (w : K).2 := rfl

/-- **The data of a strong bundle uniformizer `Ψ̄ : ℤ/2 ⋉ K → E_μ`** (Definition 17.7.2 (1), (2)):
over the identity uniformizer `Ψ` of `ℤ/2 ⋉ ℝ`, the trivial bundle `K = ℝ × ℝ → ℝ` with the
diagonal action `g ∗ (x, v) = (g x, g v)` and the fibre maps `(x, v) ↦ v`. -/
def reflUnifData : reflV.StrongBundleUniformizerData where
  base := LocalUniformizer.reflection
  K := K
  p := proj 1 1
  B := bundle 1 1
  p_smul _ _ := rfl
  isStrongBundleMap_smul := isStrongBundleMap_smul
  fiber q := fibCLE q
  obj_smul _ _ := rfl

theorem reflUnifData_obj (k : K) : reflUnifData.obj k = reflMu.objMk k.1 k.2 := rfl

theorem reflUnifData_orbitMap : reflUnifData.functor.orbitMap = orbitHomeomorph := by
  funext z
  induction z using Quotient.inductionOn with | h k => rfl

/-- **The non-degenerate witness of 2021 Definition 17.7.2**: `Ψ̄ : ℤ/2 ⋉ (ℝ × ℝ) → E_μ`;
`|Ψ̄|` is a homeomorphism onto `|E_μ| = |P|⁻¹(|C|)`. -/
def reflUnif : reflV.StrongBundleUniformizer where
  toStrongBundleUniformizerData := reflUnifData
  isOpenEmbedding_orbitMap := by
    rw [reflUnifData_orbitMap]
    exact orbitHomeomorph.isOpenEmbedding
  range_orbitMap := by
    rw [reflUnifData_orbitMap]
    change range orbitHomeomorph = _
    rw [Homeomorph.range_coe]
    change univ = reflV.proj.orbitMap ⁻¹' LocalUniformizer.reflection.footprint
    rw [LocalUniformizer.tautological_footprint, preimage_univ]

/-- **The non-degenerate witness of 2021 Definition 17.7.3**: `F̄(x) = {Ψ̄}` over the polyfold
structure `reflectionConstruction` (`F(x) = {Ψ}`). -/
def reflUC : reflV.StrongBundleUniformizerConstruction
    PolyfoldConstruction.reflectionConstruction where
  F _ := {reflUnif}
  base_mem α Ψ h := by
    rw [mem_singleton_iff.1 h]
    exact mem_singleton _

/-! ### The strong polyfold bundle construction -/

open PolyfoldConstruction StrongBundleUniformizerConstruction StrongBundleUniformizerData

/-- The member `Ψ̄` of `F̄`. -/
abbrev reflΨ : reflUC.Unif := ⟨reflUnif, 0, rfl⟩

theorem unif_eq (Ψ : reflUC.Unif) : Ψ = reflΨ := by
  obtain ⟨Ψ, α, h⟩ := Ψ
  exact Subtype.ext h

/-- The transition M-polyfold `M(Ψ, Ψ)` of the base. -/
abbrev Tr : Type := reflectionConstruction.Tr (reflUC.baseUnif reflΨ) (reflUC.baseUnif reflΨ)

/-- The sheet `{a | a.mor = (g, ·)}` of `M(Ψ, Ψ)`. -/
def sheet (g : ℤˣ) : Set Tr := {a | a.mor.1 = g}

theorem continuous_mor_fst : Continuous fun a : Tr => a.mor.1 :=
  continuous_fst.comp (twistHomeomorph isScSmoothMap_units_smul
    (TranslationTwist.refl ℤˣ (Fin 1 → ℝ))).symm.continuous

theorem isOpen_sheet (g : ℤˣ) : IsOpen (sheet g) :=
  (isOpen_discrete {g}).preimage continuous_mor_fst

theorem tgt_eq_smul_src (a : Tr) :
    (show Fin 1 → ℝ from a.tgt) = a.mor.1 • (show Fin 1 → ℝ from a.src) := by
  have h1 : a.mor.2 = a.src := a.src_mor
  have h2 : a.mor.1 • a.mor.2 = a.tgt := a.tgt_mor
  rw [← h2, h1]

/-- **`t̄(a, k) = g ∗ k`** for `a = (q, (g, q), g q)`. -/
theorem transT_eq (x : reflUC.TransSpace reflΨ reflΨ) :
    (show K from reflUC.transT reflΨ reflΨ x) = x.1.1.mor.1 • (show K from x.1.2) := by
  have h := obj_transAct (Ψ := reflUnifData) (Ψ' := reflUnifData) x.1.1 x.1.2 x.2
  exact (congrArg toPair h).trans (toPair_act x.1.1.mor (reflUnifData.obj x.1.2) _)

instance paracompactSpace_transSpace :
    ParacompactSpace (pullbackSpace reflΨ.1.p fun a : Tr => a.src) :=
  reflΨ.1.B.paracompactSpace_pullback
    (reflectionConstruction.transPolyfold (reflUC.baseUnif reflΨ) (reflUC.baseUnif reflΨ)) _

/-- `g ∗ pr₂ : s*K → K`, a strong bundle map covering `g ∗ s`. -/
theorem isStrongBundleMap_smul_pullbackProj' (g : ℤˣ) :
    (reflUC.transBundle reflΨ reflΨ).IsStrongBundleMap reflΨ.1.B
      ((fun x : Fin 1 → ℝ => g • x) ∘ fun a : Tr => a.src)
      ((fun k : K => g • k) ∘ pullbackProj' reflΨ.1.p fun a : Tr => a.src) :=
  (isStrongBundleMap_smul g).comp
    (reflΨ.1.B.isStrongBundleMap_pullbackProj' (reflUC.isScSmoothMap_trSrc reflΨ reflΨ))

theorem transT_eqOn_sheet (g : ℤˣ) :
    EqOn (reflUC.transT reflΨ reflΨ)
      ((fun k : K => g • k) ∘ pullbackProj' reflΨ.1.p fun a : Tr => a.src)
      (pullbackProj reflΨ.1.p (fun a : Tr => a.src) ⁻¹' sheet g) := by
  intro x hx
  have hx' : x.1.1.mor.1 = g := hx
  refine (transT_eq x).trans ?_
  rw [hx']
  rfl

/-- **`t̄ : M(Ψ̄, Ψ̄) → K` is a strong bundle map covering `t`** (Definition 17.7.4). -/
theorem isStrongBundleMap_transT :
    (reflUC.transBundle reflΨ reflΨ).IsStrongBundleMap reflΨ.1.B (fun a => a.tgt)
      (reflUC.transT reflΨ reflΨ) :=
  isStrongBundleMap_of_locally_eqOn (fun x => p_transAct x.1.1 x.1.2 x.2) fun a =>
    ⟨sheet a.mor.1, isOpen_sheet _, rfl, _, _, isStrongBundleMap_smul_pullbackProj' a.mor.1,
      transT_eqOn_sheet a.mor.1⟩

/-- `g ∗ · : K → K` is a strong bundle isomorphism over `ℝ`. -/
theorem isStrongBundleIsoOn_smul (g : ℤˣ) :
    (bundle 1 1).IsStrongBundleIsoOn (bundle 1 1) (isStrongBundleMap_smul g) univ univ :=
  StrongBundle.isStrongBundleIsoOn_univ_of_inverse (isStrongBundleMap_smul g)
    (isStrongBundleMap_smul g⁻¹) (isScSmoothMap_units_smul g) (isScSmoothMap_units_smul g⁻¹)
    (fun x => inv_smul_smul g x) (fun x => smul_inv_smul g x) (fun y => inv_smul_smul g y)
    (fun y => smul_inv_smul g y)

theorem isScDiffeoOn_units_smul (g : ℤˣ) :
    (rnPolyfold 1).IsScDiffeoOn (rnPolyfold 1) (fun x => g • x) (fun x => g⁻¹ • x) univ univ :=
  ⟨isScSmoothMap_units_smul g, isScSmoothMap_units_smul g⁻¹, mapsTo_univ _ _, mapsTo_univ _ _,
    fun x _ => inv_smul_smul g x, fun x _ => smul_inv_smul g x⟩

/-- **`t̄` is a local strong bundle isomorphism** (Definition 17.7.4): over `W ∩ sheet g`, where
`s` is an sc-diffeomorphism, `t̄ = (g ∗ ·) ∘ s̄`. -/
theorem isLocalStrongBundleIso_transT (a : Tr) :
    ∃ (W : Set Tr) (W' : Set (Fin 1 → ℝ)), a ∈ W ∧
      (reflUC.transBundle reflΨ reflΨ).IsStrongBundleIsoOn reflΨ.1.B isStrongBundleMap_transT
        W W' := by
  obtain ⟨W, W', σ, ha, hd⟩ := reflectionConstruction.isLocalScDiffeo_trSrc
    (reflUC.baseUnif reflΨ) (reflUC.baseUnif reflΨ) a
  have hW₀ : IsOpen (W ∩ sheet a.mor.1) := hd.isOpen_source.inter (isOpen_sheet _)
  have hd₀ := hd.restrict hW₀ inter_subset_left
  have hi₁ := reflΨ.1.B.isStrongBundleIsoOn_pullbackProj'
    (reflUC.isScSmoothMap_trSrc reflΨ reflΨ) hd₀ a
  have hi₂ := (isStrongBundleIsoOn_smul a.mor.1).restrict (isScDiffeoOn_units_smul a.mor.1)
    hd₀.isOpen_target (subset_univ _)
  refine ⟨W ∩ sheet a.mor.1, _, ⟨ha, rfl⟩, isStrongBundleIsoOn_of_eqOn (hi₂.comp hi₁) ?_ ?_⟩
  · intro a' ha'
    have h' : a'.mor.1 = a.mor.1 := ha'.2
    refine Eq.trans ?_ (tgt_eq_smul_src a').symm
    rw [h']
    rfl
  · exact fun x hx => (transT_eqOn_sheet a.mor.1 (show x.1.1.mor.1 = a.mor.1 from hx.2)).symm

/-- **The non-degenerate witness of 2021 Definition 17.7.4**: `F̄(x) = {Ψ̄}` with the pull-back
structures `s*K` on `M(Ψ̄, Ψ̄)`; `t̄(a, k) = g ∗ k` for `a = (q, (g, q), g q)` (`transT_eq`). -/
def reflQ : reflV.StrongPolyfoldBundleConstruction reflectionConstruction where
  toStrongBundleUniformizerConstruction := reflUC
  isStrongBundleMap_trans Ψ Ψ' := by
    obtain rfl := unif_eq Ψ
    obtain rfl := unif_eq Ψ'
    exact isStrongBundleMap_transT
  isLocalStrongBundleIso_trans Ψ Ψ' a := by
    obtain rfl := unif_eq Ψ
    obtain rfl := unif_eq Ψ'
    exact isLocalStrongBundleIso_transT a

/-! ### Non-degeneracy of the fibre action and of `|E_μ|` -/

/-- **The generator `−1` acts on the fibres by `v ↦ −v`**: `μ(−1, x) = −1`. -/
theorem reflV_map_neg (x : Fin 1 → ℝ) (v : Fin 1 → ℝ) :
    reflV.map ((-1 : ℤˣ), x) v = -v :=
  units_smul_rn_neg_one v

/-- **The fibre action is non-trivial**: `μ(−1, x) v ≠ v` for `v ≠ 0`. -/
theorem reflV_map_ne (x : Fin 1 → ℝ) {v : Fin 1 → ℝ} (hv : v ≠ 0) :
    reflV.map ((-1 : ℤˣ), x) v ≠ v := by
  rw [reflV_map_neg]
  intro h
  refine hv (funext fun i => ?_)
  have := congrFun h i
  simp only [Pi.neg_apply] at this
  simp only [Pi.zero_apply]
  linarith

/-- **The fibres are non-zero**: `μ(x) = ℝ`. -/
theorem reflV_fiber_ne_zero (x : Fin 1 → ℝ) : ∃ v : reflV.V x, v ≠ 0 :=
  ⟨fun _ => 1, fun h => by
    have := congrFun h 0
    exact one_ne_zero this⟩

/-- In `|E_μ|`, `(0, v)` and `(0, −v)` are the same point (the morphism `(−1, 0)`). -/
theorem π_objMk_neg (v : Fin 1 → ℝ) :
    reflV.groupoid.π (reflV.objMk 0 v) = reflV.groupoid.π (reflV.objMk 0 (-v)) := by
  refine (GroupoidStr.π_eq_π_iff _).2 ⟨⟨(((-1 : ℤˣ), 0), reflV.objMk 0 v), rfl⟩, rfl, ?_⟩
  change reflMu.objMk ((-1 : ℤˣ) • (0 : Fin 1 → ℝ)) ((-1 : ℤˣ) • v) = reflMu.objMk 0 (-v)
  rw [units_smul_rn_neg_one, units_smul_rn_neg_one, neg_zero]

/-- In `|E_μ|`, a non-zero vector is not in the class of the zero vector. -/
theorem π_objMk_ne_zero {v : Fin 1 → ℝ} (hv : v ≠ 0) :
    reflV.groupoid.π (reflV.objMk 0 v) ≠ reflV.groupoid.π (reflV.objMk 0 0) := by
  intro h
  obtain ⟨a, ha, hb⟩ := (GroupoidStr.π_eq_π_iff _).1 h
  have ha' : a.e = reflMu.objMk 0 v := ha
  have hb' : reflMu.act a.φ a.e a.2 = reflMu.objMk 0 0 := hb
  have e₀ := (toPair_act a.φ a.e a.2).symm.trans (congrArg toPair hb')
  rw [ha'] at e₀
  have e : a.φ.1 • v = 0 := congrArg Prod.snd e₀
  exact hv (by rw [← inv_smul_smul a.φ.1 v, e, smul_zero])

/-- **Definition 17.7.2 for `Ψ̄`, collected**: `Ψ̄ ∈ F̄(0)`, `Ψ̄` is full and faithful, `|Ψ̄|` is a
homeomorphism onto `|E_μ|`, the zero `(0, 0)` is in the image, and the action of `−1` on `K` moves
every non-zero fibre vector over `0`. -/
theorem reflUnif_witness :
    reflUnif ∈ reflUC.F 0 ∧ reflUnif.functor.toFunctor.Full ∧
      reflUnif.functor.toFunctor.Faithful ∧ IsHomeomorph reflUnif.functor.orbitMap ∧
      reflUnif.footprint = univ ∧ (∃ k, reflUnif.obj k = reflV.objMk 0 0) ∧
      ∀ v : Fin 1 → ℝ, v ≠ 0 →
        (-1 : ℤˣ) • ((0 : Fin 1 → ℝ), v) ≠ ((0 : Fin 1 → ℝ), v) := by
  refine ⟨rfl, reflUnifData.full, reflUnifData.faithful, ?_, ?_,
    reflUnif.exists_obj_eq_zero ⟨(0 : Fin 1 → ℝ), rfl⟩, fun v hv h => ?_⟩
  · rw [show reflUnif.functor.orbitMap = orbitHomeomorph from reflUnifData_orbitMap]
    exact orbitHomeomorph.isHomeomorph
  · rw [StrongBundleUniformizer.footprint_eq]
    change reflV.proj.orbitMap ⁻¹' LocalUniformizer.reflection.footprint = univ
    rw [LocalUniformizer.tautological_footprint, preimage_univ]
  · exact reflV_map_ne 0 hv (congrArg Prod.snd h)

/-! ### The strong bundle models `W_Ψ̄ → X_Ψ` and their comparison -/

theorem reflΨ_footprint : (reflQ.baseUnif reflΨ).1.footprint = univ :=
  reflectionUnif_footprint

/-- **One copy of `Ψ̄`**, a covering family indexed by `Unit`. -/
def reflSingle : reflQ.BundleCoveringFamily where
  ι := Unit
  Ψ _ := reflΨ
  cover := eq_univ_of_forall fun z => mem_iUnion.2 ⟨(), by
    change z ∈ (reflQ.baseUnif reflΨ).1.footprint
    rw [reflΨ_footprint]
    exact mem_univ z⟩

/-- **Two copies of `Ψ̄`**, a covering family indexed by `Bool`. -/
def reflPair : reflQ.BundleCoveringFamily where
  ι := Bool
  Ψ _ := reflΨ
  cover := eq_univ_of_forall fun z => mem_iUnion.2 ⟨true, by
    change z ∈ (reflQ.baseUnif reflΨ).1.footprint
    rw [reflΨ_footprint]
    exact mem_univ z⟩

/-- The element `((0, (−1, 0), 0), (0, 1))` of `M(Ψ̄_false, Ψ̄_true) = s*K` in the pair model. -/
def pairTrans : reflQ.TransSpace (reflPair.Ψ false) (reflPair.Ψ true) :=
  ⟨(⟨(0 : Fin 1 → ℝ), ((-1 : ℤˣ), 0), (0 : Fin 1 → ℝ), rfl, smul_zero _⟩,
    ((0 : Fin 1 → ℝ), fun _ => 1)), rfl⟩

/-- **The non-degenerate witness of the strong bundle analogues of Theorem 17.1.14 and
Lemma 17.1.15** (two copies of `Ψ̄`): the structure map `μ = t̄` of `W_Ψ̄ → X_Ψ` sends `(0, 1)`
in the piece `false`, along the morphism `(0, (−1, 0), 0)` from the piece `false` to the piece
`true`, to `(0, −1)` in the piece `true`; `Γ̄_Ψ̄` covers `Γ_Ψ`, is an equivalence of categories,
and `|Γ̄_Ψ̄|` is a homeomorphism covering `|Γ_Ψ|`. -/
theorem reflPair_bundleModel :
    (pullbackSigmaIncl (p := fun i => (reflPair.Ψ i).1.p) (s := reflQ.modelSrcPiece reflPair.Ψ)
        (false, true) pairTrans).1.2 = ⟨false, ((0 : Fin 1 → ℝ), fun _ => (1 : ℝ))⟩ ∧
      (reflQ.modelEpStrongBundle reflPair.Ψ).μ
          (pullbackSigmaIncl (p := fun i => (reflPair.Ψ i).1.p)
            (s := reflQ.modelSrcPiece reflPair.Ψ) (false, true) pairTrans) =
        ⟨true, ((0 : Fin 1 → ℝ), -fun _ => (1 : ℝ))⟩ ∧
      reflV.proj.comp (reflQ.bundleModelFunctor reflPair.Ψ) =
        (reflectionConstruction.modelFunctor (reflQ.modelBase reflPair.Ψ)).comp
          (reflQ.modelEpStrongBundle reflPair.Ψ).projFunctor.toGroupoidFunctor ∧
      (reflQ.bundleModelFunctor reflPair.Ψ).toFunctor.IsEquivalence ∧
      IsHomeomorph (reflQ.bundleModelFunctor reflPair.Ψ).orbitMap ∧
      reflV.proj.orbitMap ∘ (reflQ.bundleModelFunctor reflPair.Ψ).orbitMap =
        (reflectionConstruction.modelFunctor (reflQ.modelBase reflPair.Ψ)).orbitMap ∘
          (reflQ.modelEpStrongBundle reflPair.Ψ).projFunctor.toGroupoidFunctor.orbitMap := by
  obtain ⟨h₁, -, h₃, h₄, h₅⟩ := reflQ.lemma_17_1_15_bundle reflPair.cover
  refine ⟨rfl, ?_, h₁, h₃, h₄, h₅⟩
  rw [(reflQ.theorem_17_1_14_bundle reflPair.Ψ).2.2 (false, true) pairTrans]
  refine congrArg (Sigma.mk true) ((transT_eq pairTrans).trans ?_)
  change (((-1 : ℤˣ) • (0 : Fin 1 → ℝ)), (-1 : ℤˣ) • fun _ => (1 : ℝ)) = _
  rw [units_smul_rn_neg_one, units_smul_rn_neg_one, neg_zero]

open SBLocalization SBLocalization.SEPLoc CategoryTheory in
/-- **The non-degenerate witness of the strong bundle analogue of Theorem 17.1.18** (one and two
copies of `Ψ̄`): `f̄ = f̄_{Ψ̄,Ψ̄'}` is a generalized strong bundle isomorphism covering
`f_{Ψ,Ψ'}`, `f̄_{Ψ̄,Ψ̄} = 1`, `f̄_{Ψ̄',Ψ̄} ∘ f̄_{Ψ̄,Ψ̄'} = f̄_{Ψ̄,Ψ̄}`,
`|Γ̄_Ψ̄'| ∘ |f̄| = |Γ̄_Ψ̄|` and `|f̄|` is a homeomorphism; `|f̄|` sends the class of `(0, 1)`
to a point over `|(0, 1)| ∈ |E_μ|`, and it separates the classes of `(0, 1)` and of the zero
vector `(0, 0)`. -/
theorem refl_bundleComparison :
    GenSBMap.IsGeneralizedIso (reflQ.bundleComparison reflSingle reflPair) ∧
      baseFunctor.map (reflQ.bundleComparison reflSingle reflPair) =
        reflectionConstruction.comparison reflSingle.base reflPair.base ∧
      reflQ.bundleComparison reflSingle reflSingle = 𝟙 _ ∧
      reflQ.bundleComparison reflSingle reflPair ≫ reflQ.bundleComparison reflPair reflSingle =
        reflQ.bundleComparison reflSingle reflSingle ∧
      (reflQ.bundleModelFunctor reflPair.Ψ).orbitMap ∘
          GenSBMap.orbitMap (reflQ.bundleComparison reflSingle reflPair) =
        (reflQ.bundleModelFunctor reflSingle.Ψ).orbitMap ∧
      IsHomeomorph (GenSBMap.orbitMap (reflQ.bundleComparison reflSingle reflPair)) ∧
      (reflQ.bundleModelFunctor reflPair.Ψ).orbitMap
          (GenSBMap.orbitMap (reflQ.bundleComparison reflSingle reflPair)
            ((reflQ.modelEpStrongBundle reflSingle.Ψ).toGroupoidStr.π
              ⟨(), ((0 : Fin 1 → ℝ), fun _ => (1 : ℝ))⟩)) =
        reflV.groupoid.π (reflV.objMk 0 fun _ => (1 : ℝ)) ∧
      GenSBMap.orbitMap (reflQ.bundleComparison reflSingle reflPair)
          ((reflQ.modelEpStrongBundle reflSingle.Ψ).toGroupoidStr.π
            ⟨(), ((0 : Fin 1 → ℝ), fun _ => (1 : ℝ))⟩) ≠
        GenSBMap.orbitMap (reflQ.bundleComparison reflSingle reflPair)
          ((reflQ.modelEpStrongBundle reflSingle.Ψ).toGroupoidStr.π
            ⟨(), ((0 : Fin 1 → ℝ), 0)⟩) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := reflQ.theorem_17_1_18_bundle reflSingle reflPair reflSingle
  have hv : (reflQ.bundleModelFunctor reflPair.Ψ).orbitMap
      (GenSBMap.orbitMap (reflQ.bundleComparison reflSingle reflPair)
        ((reflQ.modelEpStrongBundle reflSingle.Ψ).toGroupoidStr.π
          ⟨(), ((0 : Fin 1 → ℝ), fun _ => (1 : ℝ))⟩)) =
      reflV.groupoid.π (reflV.objMk 0 fun _ => (1 : ℝ)) := congrFun h₅ _
  refine ⟨h₁, h₂, reflQ.bundleComparison_self reflSingle, h₄, h₅, h₆, hv, fun h => ?_⟩
  have h0 := congrArg (reflQ.bundleModelFunctor reflPair.Ψ).orbitMap h
  rw [hv] at h0
  have h0' : reflV.groupoid.π (reflV.objMk 0 fun _ => (1 : ℝ)) =
      reflV.groupoid.π (reflV.objMk 0 0) := h0.trans (congrFun h₅ _)
  exact π_objMk_ne_zero (fun h => one_ne_zero (congrFun h 0)) h0'

end GCT.VectorBundle.ReflectionBundle

end Polyfold
