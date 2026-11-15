import Polyfold.Chapter6.ChartPropagation
import Polyfold.Chapter6.OrientationFunctor

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6,
pp. 227–229: **Theorem 6.6.13** (the functor `Γ_f`) and Definitions 6.6.14–6.6.16 for a strong
bundle with a chart over the whole base, without sc-smooth bump functions.

# The orientation functor in a chart over the whole base

## The text, paraphrased

(Theorem 6.6.13) For an sc-Fredholm section `f` there is a uniquely determined functor
`Γ_f : PX → O_f`, `x ↦ Or_x^f`, on the category of smooth points and classes of sc-smooth paths,
which on paths in the neighbourhoods `U(x)` of Theorem 6.6.11 is the local propagation (property
(∗)).  (Definitions 6.6.14–6.6.16) `f` is orientable if `Γ_f([φ])` depends only on the end
points; an orientation is a map `y ↦ o_y` which is locally a continuous orientation.

## What is formalized

With `hch : ∃ c ∈ B.atlas.charts, c.φ.source = univ` (a chart of the atlas over the whole base)
in place of sc-smooth bump functions, the declarations of the section `Transport` of
`OrientationFunctor.lean`, built on `theorem_6_6_11_of_chart`:

* `exists_isOrientableNbhd_of_chart`: orientable neighbourhoods exist.
* `orLocalTransportOfChart`: the local transport data of `f`; `orFunctorMapOfChart`,
  `orFunctorOfChart`: the functor `Γ_f`.
* `theorem_6_6_13_hyp_of_chart`: **Theorem 6.6.13**, existence and uniqueness of `Γ_f`.
* `IsOrientableSectionOfChart` (Definition 6.6.14) and its characterizations
  (`isOrientableSection_iff_of_chart`, `isSectionOrientation_iff_of_chart`,
  `IsSectionOrientation.exists_two_of_chart`).
-/

set_option maxSynthPendingDepth 3

open Set CategoryTheory

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

section Push

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **Orientable neighbourhoods exist** (Theorem 6.6.11, `exists_nhds_scPath`). -/
theorem exists_isOrientableNbhd_of_chart
    [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
    [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
    (hX : PX.IsTame) (hch : ∃ c ∈ B.atlas.charts, c.φ.source = univ)
    (hf : B.IsScFredholmSectionTame f) {x : X} (hx : x ∈ PX.smoothSet) :
    ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c) (U V : Set X),
      IsOrientableNbhd f hf.toIsScFredholmSection c hc U V x := by
  obtain ⟨c, hc, U, hUo, hxU, hU⟩ := theorem_6_6_11_of_chart hX hch hf hx
  obtain ⟨V, hVo, hxV, hVU, hpath⟩ := exists_nhds_scPath hc hUo hU.subset hxU
  exact ⟨c, hc, U, V, ⟨hU, hUo, hVo, hVU, hxV, hpath⟩⟩

section Transport

variable [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

variable (hX : PX.IsTame) (hch : ∃ c ∈ B.atlas.charts, c.φ.source = univ)
  (hf : B.IsScFredholmSectionTame f)
  (hsec : B.HasScPlusSectionsThrough)

include hX hch hf hsec

/-- **The local transport data of `f`** (the proof of Theorem 6.6.13): the good sets are the open
sets with the local propagation property in some chart (they cover `X_∞` by Theorem 6.6.11), the
push-forwards are `orPush`; any two `Or_x^f` are in bijection (two elements each). -/
def orLocalTransportOfChart :
    LocalTransport PX (fun x hs => Orx f hf.toIsScFredholmSection x hs) where
  Good := IsPropagationNbhd f hf.toIsScFredholmSection
  isOpen hU := hU.choose_spec.choose_spec.1
  exists_good _ hx :=
    let ⟨c, hc, U, hUo, hxU, hU⟩ := theorem_6_6_11_of_chart hX hch hf hx
    ⟨U, ⟨c, hc, hUo, hU⟩, hxU⟩
  nonempty _ hs₀ _ hs₁ :=
    let ⟨_, _, ha, ha'⟩ := exists_two_orx hf.toIsScFredholmSection hs₀ hsec
    let ⟨_, _, hb, hb'⟩ := exists_two_orx hf.toIsScFredholmSection hs₁ hsec
    nonempty_equiv_of_two ha ha' hb hb'
  push hU γ hγs hγU _ _ h₀ h₁ hs₀ hs₁ := orPush hU γ hγs hγU h₀ h₁ hs₀ hs₁
  push_trans hU _ _ _ hγ hγ₁ hγ₂ hγU hγ₁U hγ₂U _ _ _ h₀ h₂ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂ :=
    orPush_trans hU hγ hγ₁ hγ₂ hγU hγ₁U hγ₂U h₀ h₂ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂
  push_compat hU hU' _ hγ hγU hγU' _ _ h₀ h₁ hs₀ hs₁ :=
    orPush_compat hU hU' hγ hγU hγU' h₀ h₁ hs₀ hs₁

/-- **Property (∗) for the transport along a path**: on an sc-smooth path in an open `U` with the
local propagation property in a chart `c`, the transport is every push-forward `e` along the path
in `c`, read in the chosen charts. -/
theorem orLocalTransportOfChart_transport_eq {c : StrongBundleChart PX P} {hc : B.IsChart c}
    {U : Set X} (hU : HasLocalPropagation f hf.toIsScFredholmSection c hc U) (hUo : IsOpen U)
    {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγU : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet)
    (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source)
    {e : (chartPtOf c hc hx₀ hs₀).Or f hf.toIsScFredholmSection ≃
      (chartPtOf c hc hx₁ hs₁).Or f hf.toIsScFredholmSection}
    (he : IsPush f hf.toIsScFredholmSection c hc γ (fun q hq => hU.subset (hγU q hq)) h₀ h₁ hx₀
      hx₁ hs₀ hs₁ e) :
    (orLocalTransportOfChart hX hch hf hsec).transport γ hγs h₀ h₁ hs₀ hs₁ =
      (toChartOr hf.toIsScFredholmSection hs₀ c hc hx₀).trans
        (e.trans (toChartOr hf.toIsScFredholmSection hs₁ c hc hx₁).symm) :=
  ((orLocalTransportOfChart hX hch hf hsec).transport_eq_push (U := U) ⟨c, hc, hUo, hU⟩ hγs
    (fun _ ht => hγU _ (pt1_mem_Icc ht)) h₀ h₁ hs₀ hs₁).trans
    (orPush_eq _ hγs (fun _ ht => hγU _ (pt1_mem_Icc ht)) h₀ h₁ hs₀ hs₁ hU hγU hx₀ hx₁ he)

/-- **The functor `Γ_f` on morphisms** (Theorem 6.6.13): `Γ_f([φ]) : Or_x^f ≃ Or_y^f` is the
transport along `φ` (`LocalTransport.transport`), which depends only on the class `[φ]`
(`transport_eq_of_isScHomotopyRel`). -/
def orFunctorMapOfChart {x y : PathCat PX} (a : x ⟶ y) :
    Orx f hf.toIsScFredholmSection x.pt x.smooth ≃ Orx f hf.toIsScFredholmSection y.pt y.smooth :=
  Quotient.lift (s := ScPath.setoid PX x.pt y.pt)
    (fun φ => (orLocalTransportOfChart hX hch hf hsec).transport φ.toFun φ.isScSmoothMap φ.source
      φ.target x.smooth y.smooth)
    (fun φ ψ h => by
      obtain ⟨Φ, hΦ⟩ := h
      exact (orLocalTransportOfChart hX hch hf hsec).transport_eq_of_isScHomotopyRel hΦ
        φ.isScSmoothMap ψ.isScSmoothMap φ.source φ.target x.smooth y.smooth)
    a

/-- `Γ_f([φ])` is the transport along `φ`. -/
theorem orFunctorMapOfChart_mk {x y : PathCat PX} (φ : ScPath PX x.pt y.pt) :
    orFunctorMapOfChart hX hch hf hsec (PathCat.homMk φ) =
      (orLocalTransportOfChart hX hch hf hsec).transport φ.toFun φ.isScSmoothMap φ.source φ.target
        x.smooth y.smooth :=
  rfl

/-- **`Γ_f` takes identities to identities** (`transport_const`). -/
theorem orFunctorMapOfChart_id (x : PathCat PX) :
    orFunctorMapOfChart hX hch hf hsec (𝟙 x) = Equiv.refl _ :=
  (orLocalTransportOfChart hX hch hf hsec).transport_const _ (fun _ _ => rfl) _ _ x.smooth

/-- **`Γ_f` takes compositions to composites** (`transport_concatPath`). -/
theorem orFunctorMapOfChart_comp {x y z : PathCat PX} (a : x ⟶ y) (b : y ⟶ z) :
    orFunctorMapOfChart hX hch hf hsec (a ≫ b) =
      (orFunctorMapOfChart hX hch hf hsec a).trans (orFunctorMapOfChart hX hch hf hsec b) := by
  obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
  obtain ⟨ψ, rfl⟩ := PathCat.exists_eq_mk b
  exact (orLocalTransportOfChart hX hch hf hsec).transport_concatPath φ.isScSmoothMap
    ψ.isScSmoothMap
    φ.source φ.target ψ.source ψ.target x.smooth y.smooth z.smooth

/-- **The functor `Γ_f : PX → O_f`** (Theorem 6.6.13) into the category of types: `x ↦ Or_x^f`,
`[φ] ↦ Γ_f([φ])`. -/
def orFunctorOfChart : PathCat PX ⥤ Type where
  obj x := Orx f hf.toIsScFredholmSection x.pt x.smooth
  map a := ↾(orFunctorMapOfChart hX hch hf hsec a)
  map_id x := by
    rw [orFunctorMapOfChart_id]
    rfl
  map_comp a b := by
    rw [orFunctorMapOfChart_comp]
    rfl

/-- The functor `Γ_f` on objects: `x ↦ Or_x^f`. -/
theorem orFunctorOfChart_obj (x : PathCat PX) :
    (orFunctorOfChart hX hch hf hsec).obj x = Orx f hf.toIsScFredholmSection x.pt x.smooth :=
  rfl

/-- The functor `Γ_f` on morphisms is `orFunctorMapOfChart`. -/
theorem orFunctorOfChart_map_apply {x y : PathCat PX} (a : x ⟶ y)
    (o : Orx f hf.toIsScFredholmSection x.pt x.smooth) :
    (orFunctorOfChart hX hch hf hsec).map a o = orFunctorMapOfChart hX hch hf hsec a o :=
  rfl

/-- **`Γ_f` has property (∗)** (`orLocalTransportOfChart_transport_eq`). -/
theorem orFunctorMapOfChart_isStarProperty :
    IsStarProperty f hf.toIsScFredholmSection fun _ _ a => orFunctorMapOfChart hX hch hf hsec a :=
  fun _ _ _ hUo hU x y φ hφ hx hy _ he =>
    orLocalTransportOfChart_transport_eq hX hch hf hsec hU hUo φ.isScSmoothMap hφ φ.source φ.target
      x.smooth y.smooth hx hy he

/-- **Uniqueness of `Γ_f`, for (∗) on a covering**: a family of maps on the morphisms of `PX`
taking compositions to composites and with property (∗) on the members of a family `W` of open
sets with the local propagation property covering `X_∞` is `Γ_f` (`transport_unique` for the
local transport data restricted to `W`, which both the family and the transport of
`orLocalTransportOfChart` satisfy; homotopy invariance holds on classes). -/
theorem orFunctorMapOfChart_unique_of_cover (W : Set X → Prop) (hWo : ∀ {U}, W U → IsOpen U)
    (hWc : ∀ x ∈ PX.smoothSet, ∃ U, W U ∧ x ∈ U ∧ ∃ (c : StrongBundleChart PX P)
      (hc : B.IsChart c), HasLocalPropagation f hf.toIsScFredholmSection c hc U)
    (G : ∀ x y : PathCat PX, (x ⟶ y) →
      (Orx f hf.toIsScFredholmSection x.pt x.smooth ≃ Orx f hf.toIsScFredholmSection y.pt y.smooth))
    (hG_comp : ∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
      G x z (a ≫ b) = (G x y a).trans (G y z b))
    (hG : IsStarPropertyOn f hf.toIsScFredholmSection W G) :
    G = fun _ _ a => orFunctorMapOfChart hX hch hf hsec a := by
  let L := orLocalTransportOfChart hX hch hf hsec
  let W' : Set X → Prop := fun U => W U ∧ ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c),
    HasLocalPropagation f hf.toIsScFredholmSection c hc U
  have hWs : ∀ {U}, W' U → ∃ U', L.Good U' ∧ U ⊆ U' := fun {_} ⟨hU, c, hc, hLP⟩ =>
    ⟨_, ⟨c, hc, hWo hU, hLP⟩, subset_rfl⟩
  let L' := L.restrict W' (fun hU => hWo hU.1)
    (fun x hx =>
      let ⟨U, hU, hxU, hLP⟩ := hWc x hx
      ⟨U, ⟨hU, hLP⟩, hxU⟩) hWs
  -- on a path in a member of `W'`, the push-forward of `L'` is every push-forward in its chart
  have hpush : ∀ {U : Set X} (hU : L'.Good U) {γ : (Fin 1 → ℝ) → X}
      (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U)
      {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
      (hs₁ : x₁ ∈ PX.smoothSet) {c : StrongBundleChart PX P} {hc : B.IsChart c}
      (hLP : HasLocalPropagation f hf.toIsScFredholmSection c hc U) (hx₀ : x₀ ∈ c.φ.source)
      (hx₁ : x₁ ∈ c.φ.source)
      {e : (chartPtOf c hc hx₀ hs₀).Or f hf.toIsScFredholmSection ≃
        (chartPtOf c hc hx₁ hs₁).Or f hf.toIsScFredholmSection},
      IsPush f hf.toIsScFredholmSection c hc γ
        (fun q hq => hLP.subset (forall_mem_of_forall_pt1_mem hγU q hq)) h₀ h₁ hx₀ hx₁ hs₀ hs₁ e →
      L'.push hU γ hγ hγU h₀ h₁ hs₀ hs₁ =
        (toChartOr hf.toIsScFredholmSection hs₀ c hc hx₀).trans
          (e.trans (toChartOr hf.toIsScFredholmSection hs₁ c hc hx₁).symm) :=
    fun {_} hU {_} hγ hγU {_ _} h₀ h₁ hs₀ hs₁ {_ _} hLP hx₀ hx₁ {_} he =>
      orPush_eq (hWs hU).choose_spec.1 hγ (fun t ht => (hWs hU).choose_spec.2 (hγU t ht)) h₀ h₁
        hs₀ hs₁ hLP (forall_mem_of_forall_pt1_mem hγU) hx₀ hx₁ he
  funext x y a
  obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
  refine (L'.transport_unique
    (fun γ hγ {x₀ x₁} h₀ h₁ hs₀ hs₁ => G ⟨x₀, hs₀⟩ ⟨x₁, hs₁⟩ (PathCat.homMk ⟨γ, hγ, h₀, h₁⟩))
    ?_ ?_ ?_ φ.isScSmoothMap φ.source φ.target x.smooth y.smooth).trans
    (L'.transport_unique L.transport ?_ ?_ ?_ φ.isScSmoothMap φ.source φ.target x.smooth
      y.smooth).symm
  · intro _ _ _ hΦ _ _ _ _ _ _ _ _
    exact congrArg (G _ _) (PathCat.mk_eq_mk_iff.2 ⟨_, hΦ⟩)
  · intro _ _ hγ₁ hγ₂ _ _ _ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂
    exact hG_comp ⟨_, hs₀⟩ ⟨_, hs₁⟩ ⟨_, hs₂⟩ (PathCat.homMk ⟨_, hγ₁, h₁₀, h₁₁⟩)
      (PathCat.homMk ⟨_, hγ₂, h₂₀, h₂₁⟩)
  · intro U hU γ hγ hγU x₀ x₁ h₀ h₁ hs₀ hs₁
    obtain ⟨hWU, c, hc, hLP⟩ := id hU
    have hγ' := forall_mem_of_forall_pt1_mem hγU
    have hx₀ : x₀ ∈ c.φ.source := hLP.subset (h₀ ▸ hγ' _ (pt1_mem_Icc ⟨le_rfl, zero_le_one⟩))
    have hx₁ : x₁ ∈ c.φ.source := hLP.subset (h₁ ▸ hγ' _ (pt1_mem_Icc ⟨zero_le_one, le_rfl⟩))
    obtain ⟨e, he⟩ := hLP.exists_isPush γ hγ hγ' h₀ h₁ hx₀ hx₁ hs₀ hs₁
    exact (hG c hc U hWU hLP ⟨x₀, hs₀⟩ ⟨x₁, hs₁⟩ ⟨γ, hγ, h₀, h₁⟩ hγ' hx₀ hx₁ e he).trans
      (hpush hU hγ hγU h₀ h₁ hs₀ hs₁ hLP hx₀ hx₁ he).symm
  · intro _ _ _ hΦ hγ₀ hγ₁ _ _ h₀ h₁ hs₀ hs₁
    exact L.transport_eq_of_isScHomotopyRel hΦ hγ₀ hγ₁ h₀ h₁ hs₀ hs₁
  · intro _ _ hγ₁ hγ₂ _ _ _ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂
    exact L.transport_concatPath hγ₁ hγ₂ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂
  · intro U hU γ hγ hγU x₀ x₁ h₀ h₁ hs₀ hs₁
    obtain ⟨hWU, c, hc, hLP⟩ := id hU
    have hγ' := forall_mem_of_forall_pt1_mem hγU
    have hx₀ : x₀ ∈ c.φ.source := hLP.subset (h₀ ▸ hγ' _ (pt1_mem_Icc ⟨le_rfl, zero_le_one⟩))
    have hx₁ : x₁ ∈ c.φ.source := hLP.subset (h₁ ▸ hγ' _ (pt1_mem_Icc ⟨zero_le_one, le_rfl⟩))
    obtain ⟨e, he⟩ := hLP.exists_isPush γ hγ hγ' h₀ h₁ hx₀ hx₁ hs₀ hs₁
    exact (orLocalTransportOfChart_transport_eq hX hch hf hsec hLP (hWo hWU) hγ hγ' h₀ h₁
      hs₀ hs₁ hx₀
      hx₁ he).trans (hpush hU hγ hγU h₀ h₁ hs₀ hs₁ hLP hx₀ hx₁ he).symm

/-- **Uniqueness of `Γ_f`** ("it is obvious that `Γ_f` is unique"): a family of maps on the
morphisms of `PX` taking compositions to composites and with property (∗) is `Γ_f`
(`orFunctorMapOfChart_unique_of_cover` for the open sets, which cover `X_∞` by Theorem 6.6.11). -/
theorem orFunctorMapOfChart_unique
    (G : ∀ x y : PathCat PX, (x ⟶ y) →
      (Orx f hf.toIsScFredholmSection x.pt x.smooth ≃ Orx f hf.toIsScFredholmSection y.pt y.smooth))
    (hG_comp : ∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
      G x z (a ≫ b) = (G x y a).trans (G y z b))
    (hG : IsStarProperty f hf.toIsScFredholmSection G) :
    G = fun _ _ a => orFunctorMapOfChart hX hch hf hsec a :=
  orFunctorMapOfChart_unique_of_cover hX hch hf hsec IsOpen id
    (fun _ hx =>
      let ⟨c, hc, U, hUo, hxU, hU⟩ := theorem_6_6_11_of_chart hX hch hf hx
      ⟨U, hUo, hxU, c, hc, hU⟩) G hG_comp hG

/-- **Theorem 6.6.13**: there is a unique family of maps `Γ_f([φ]) : Or_x^f ≃ Or_y^f` on the
morphisms `[φ] : x ⟶ y` of `PX` which is a functor (identities to identities, compositions to
composites) and has property (∗); it is `orFunctorMapOfChart` (packaged as `orFunctorOfChart`). -/
theorem theorem_6_6_13_hyp_of_chart :
    ∃! G : ∀ x y : PathCat PX, (x ⟶ y) →
        (Orx f hf.toIsScFredholmSection x.pt x.smooth ≃
          Orx f hf.toIsScFredholmSection y.pt y.smooth),
      (∀ x, G x x (𝟙 x) = Equiv.refl _) ∧
      (∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
        G x z (a ≫ b) = (G x y a).trans (G y z b)) ∧
      IsStarProperty f hf.toIsScFredholmSection G :=
  ⟨fun _ _ a => orFunctorMapOfChart hX hch hf hsec a,
    ⟨orFunctorMapOfChart_id hX hch hf hsec, fun _ _ _ => orFunctorMapOfChart_comp hX hch hf hsec,
      orFunctorMapOfChart_isStarProperty hX hch hf hsec⟩,
    fun G ⟨_, hG_comp, hG⟩ => orFunctorMapOfChart_unique hX hch hf hsec G hG_comp hG⟩

/-! ### Orientability (Definitions 6.6.14 and 6.6.15) and orientations (Definition 6.6.16) -/

/-- **Definition 6.6.14, orientability**: for every pair of smooth points `x`, `y` and any two
morphisms `[φ], [ψ] : x ⟶ y` of `PX` (classes of sc-smooth paths from `x` to `y`),
`Γ_f([φ]) = Γ_f([ψ])`. -/
def IsOrientableSectionOfChart : Prop :=
  ∀ (x y : PathCat PX) (a b : x ⟶ y),
    orFunctorMapOfChart hX hch hf hsec a = orFunctorMapOfChart hX hch hf hsec b

/-- **A map `y ↦ o_y` which is a continuous orientation over an orientable neighbourhood of every
smooth point is carried along by `Γ_f`**: `Γ_f([φ]) o_x = o_y` for every `[φ] : x ⟶ y`
(`transport_apply_eq_of_local` for the covering by the sets `V` of these orientable
neighbourhoods; on a path in `V`, (∗) and the continuity). -/
theorem orFunctorMapOfChart_apply_eq_of_local
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy)
    (ho : ∀ x ∈ PX.smoothSet, ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c) (U V : Set X)
      (hN : IsOrientableNbhd f hf.toIsScFredholmSection c hc U V x),
      IsContinuousOrientation f hf.toIsScFredholmSection c hc hN.hasLocalPropagation.subset
        hN.subset (restrictOr o hN))
    {x y : PathCat PX} (a : x ⟶ y) :
    orFunctorMapOfChart hX hch hf hsec a (o x.pt x.smooth) = o y.pt y.smooth := by
  obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
  rw [orFunctorMapOfChart_mk]
  refine (orLocalTransportOfChart hX hch hf hsec).transport_apply_eq_of_local o
    (fun V => ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c) (U : Set X) (x : X)
      (hN : IsOrientableNbhd f hf.toIsScFredholmSection c hc U V x),
      IsContinuousOrientation f hf.toIsScFredholmSection c hc hN.hasLocalPropagation.subset
        hN.subset (restrictOr o hN))
    (fun ⟨_, _, _, _, hN, _⟩ => hN.isOpen_V)
    (fun x hx =>
      let ⟨c, hc, U, V, hN, hcont⟩ := ho x hx
      ⟨V, ⟨c, hc, U, x, hN, hcont⟩, hN.mem⟩)
    (fun ⟨c, hc, U, _, hN, _⟩ => ⟨U, ⟨c, hc, hN.isOpen_U, hN.hasLocalPropagation⟩, hN.subset⟩)
    ?_ φ.isScSmoothMap φ.source φ.target x.smooth y.smooth
  rintro V ⟨c, hc, U, x', hN, hcont⟩ γ hγ hγV x₀ x₁ h₀ h₁ hs₀ hs₁
  have hγU := forall_mem_of_forall_pt1_mem fun t ht => hN.subset (hγV t ht)
  have hx₀ : x₀ ∈ V := h₀ ▸ hγV 0 ⟨le_rfl, zero_le_one⟩
  have hx₁ : x₁ ∈ V := h₁ ▸ hγV 1 ⟨zero_le_one, le_rfl⟩
  have hUc := hN.hasLocalPropagation.subset
  obtain ⟨e, he⟩ := hN.hasLocalPropagation.exists_isPush γ hγ hγU h₀ h₁ (hUc (hN.subset hx₀))
    (hUc (hN.subset hx₁)) hs₀ hs₁
  rw [orLocalTransportOfChart_transport_eq hX hch hf hsec hN.hasLocalPropagation
    hN.isOpen_U hγ hγU h₀
    h₁ hs₀ hs₁ _ _ he]
  exact (equiv_conj_apply_eq_iff _ _ _ _ _).2 (hcont γ hγ hγU hx₀ hx₁ hs₀ hs₁ h₀ h₁ e he)

/-- **A map `y ↦ o_y` carried along by `Γ_f` is a continuous orientation over every orientable
neighbourhood** ((∗) for the paths in `U`). -/
theorem isContinuousOrientation_of_apply_eq_of_chart
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy)
    (ho : ∀ (x y : PathCat PX) (a : x ⟶ y),
      orFunctorMapOfChart hX hch hf hsec a (o x.pt x.smooth) = o y.pt y.smooth)
    {c : StrongBundleChart PX P} {hc : B.IsChart c} {U V : Set X} {x : X}
    (hN : IsOrientableNbhd f hf.toIsScFredholmSection c hc U V x) :
    IsContinuousOrientation f hf.toIsScFredholmSection c hc hN.hasLocalPropagation.subset
      hN.subset (restrictOr o hN) := by
  intro γ hγs hγ y₁ y₂ _ _ hs₁ hs₂ h₀ h₁ e he
  have h := ho ⟨y₁, hs₁⟩ ⟨y₂, hs₂⟩ (PathCat.homMk ⟨γ, hγs, h₀, h₁⟩)
  rw [orFunctorMapOfChart_mk,
    orLocalTransportOfChart_transport_eq hX hch hf hsec hN.hasLocalPropagation
    hN.isOpen_U hγs hγ h₀ h₁ hs₁ hs₂ _ _ he] at h
  exact (equiv_conj_apply_eq_iff _ _ _ _ _).1 h

/-- **From Definition 6.6.14 to a map `y ↦ o_y` carried along by `Γ_f`**: in each class of smooth
points joined by sc-smooth paths a base point `b` (`Quotient.out` for `scPathSetoid`) and an
orientation `o_b` are chosen, and `o_y = Γ_f([φ_y]) o_b` for a path `φ_y` from `b` to `y`. -/
theorem exists_apply_eq_of_isOrientableSection_of_chart
    (h : IsOrientableSectionOfChart hX hch hf hsec) :
    ∃ o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy,
      ∀ (x y : PathCat PX) (a : x ⟶ y),
        orFunctorMapOfChart hX hch hf hsec a (o x.pt x.smooth) = o y.pt y.smooth := by
  let base : PathCat PX → PathCat PX := fun y => (Quotient.mk (scPathSetoid PX) y).out
  have hbase : ∀ y, Nonempty (base y ⟶ y) := fun y => Quotient.mk_out (s := scPathSetoid PX) y
  let ob : ∀ z : PathCat PX, Orx f hf.toIsScFredholmSection z.pt z.smooth := fun z =>
    (exists_two_orx hf.toIsScFredholmSection z.smooth hsec).choose
  refine ⟨fun y hy => orFunctorMapOfChart hX hch hf hsec (hbase ⟨y, hy⟩).some (ob (base ⟨y, hy⟩)),
    fun x y a => ?_⟩
  have hb : base x = base y := congrArg Quotient.out (Quotient.sound (s := scPathSetoid PX) ⟨a⟩)
  have key : ∀ b₁ b₂ : PathCat PX, b₁ = b₂ → ∀ (p₁ : b₁ ⟶ x) (p₂ : b₂ ⟶ y),
      orFunctorMapOfChart hX hch hf hsec a (orFunctorMapOfChart hX hch hf hsec p₁ (ob b₁)) =
        orFunctorMapOfChart hX hch hf hsec p₂ (ob b₂) := by
    rintro b _ rfl p₁ p₂
    rw [← Equiv.trans_apply, ← orFunctorMapOfChart_comp, h _ _ (p₁ ≫ a) p₂]
  exact key _ _ hb _ _

/-- **From a map `y ↦ o_y` carried along by `Γ_f` to Definition 6.6.14**: `Γ_f([φ])` and
`Γ_f([ψ])` agree at `o_x`, and a bijection onto the two-element set `Or_y^f` is determined by
one value. -/
theorem isOrientableSection_of_apply_eq_of_chart
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy)
    (ho : ∀ (x y : PathCat PX) (a : x ⟶ y),
      orFunctorMapOfChart hX hch hf hsec a (o x.pt x.smooth) = o y.pt y.smooth) :
    IsOrientableSectionOfChart hX hch hf hsec := fun x y a b =>
  let ⟨_, _, _, hall⟩ := exists_two_orx hf.toIsScFredholmSection y.smooth hsec
  equiv_eq_of_apply_eq_of_two ((ho x y a).trans (ho x y b).symm) hall

/-- **Definition 6.6.14 in terms of maps `y ↦ o_y`**: `f` is orientable iff there is a map
`y ↦ o_y ∈ Or_y^f` on the smooth points with `Γ_f([φ]) o_x = o_y` for every `[φ] : x ⟶ y`. -/
theorem isOrientableSection_iff_exists_of_chart :
    IsOrientableSectionOfChart hX hch hf hsec ↔
      ∃ o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy,
        ∀ (x y : PathCat PX) (a : x ⟶ y),
          orFunctorMapOfChart hX hch hf hsec a (o x.pt x.smooth) = o y.pt y.smooth :=
  ⟨exists_apply_eq_of_isOrientableSection_of_chart hX hch hf hsec,
    fun ⟨o, ho⟩ => isOrientableSection_of_apply_eq_of_chart hX hch hf hsec o ho⟩

/-- **Definition 6.6.15 in terms of maps `y ↦ o_y`**: there is a map `y ↦ o_y` which is a continuous
orientation over an orientable neighbourhood of every smooth point iff there is one with
`Γ_f([φ]) o_x = o_y` for every `[φ] : x ⟶ y` (orientable neighbourhoods exist,
`exists_isOrientableNbhd_of_chart`). -/
theorem isOrientableSection'_iff_exists_of_chart :
    IsOrientableSection' f hf.toIsScFredholmSection ↔
      ∃ o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy,
        ∀ (x y : PathCat PX) (a : x ⟶ y),
          orFunctorMapOfChart hX hch hf hsec a (o x.pt x.smooth) = o y.pt y.smooth :=
  ⟨fun ⟨o, ho⟩ => ⟨o, fun _ _ a => orFunctorMapOfChart_apply_eq_of_local hX hch hf hsec o ho a⟩,
    fun ⟨o, ho⟩ => ⟨o, fun _ hx =>
      let ⟨c, hc, U, V, hN⟩ := exists_isOrientableNbhd_of_chart hX hch hf hx
      ⟨c, hc, U, V, hN, isContinuousOrientation_of_apply_eq_of_chart hX hch hf hsec o ho hN⟩⟩⟩

/-- **Definitions 6.6.14 and 6.6.15 are equivalent** ("an equivalent version"). -/
theorem isOrientableSection_iff_of_chart :
    IsOrientableSectionOfChart hX hch hf hsec ↔ IsOrientableSection' f hf.toIsScFredholmSection :=
  (isOrientableSection_iff_exists_of_chart hX hch hf hsec).trans
    (isOrientableSection'_iff_exists_of_chart hX hch hf hsec).symm

/-- **Definition 6.6.16 in terms of `Γ_f`**: `y ↦ o_y` is an orientation of `f` iff
`Γ_f([φ]) o_x = o_y` for every morphism `[φ] : x ⟶ y` of `PX`. -/
theorem isSectionOrientation_iff_of_chart
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy) :
    IsSectionOrientation f hf.toIsScFredholmSection o ↔
      ∀ (x y : PathCat PX) (a : x ⟶ y),
        orFunctorMapOfChart hX hch hf hsec a (o x.pt x.smooth) = o y.pt y.smooth :=
  ⟨fun h _ _ a => orFunctorMapOfChart_apply_eq_of_local hX hch hf hsec o (fun _ hx =>
      let ⟨c, hc, U, V, hN⟩ := exists_isOrientableNbhd_of_chart hX hch hf hx
      ⟨c, hc, U, V, hN, h _ hx c hc U V hN⟩) a,
    fun ho _ _ _ _ _ _ hN => isContinuousOrientation_of_apply_eq_of_chart hX hch hf hsec o ho hN⟩

/-- **`f` has an orientation (Definition 6.6.16) iff it is orientable (Definition 6.6.14).** -/
theorem exists_isSectionOrientation_iff_of_chart :
    (∃ o, IsSectionOrientation f hf.toIsScFredholmSection o) ↔
      IsOrientableSectionOfChart hX hch hf hsec :=
  (exists_congr (isSectionOrientation_iff_of_chart hX hch hf hsec)).trans
    (isOrientableSection_iff_exists_of_chart hX hch hf hsec).symm

/-- **Two orientations which agree at a point agree on its path component**: for a morphism
`[φ] : x ⟶ y`, `o_x = o'_x` iff `o_y = o'_y`. -/
theorem IsSectionOrientation.apply_eq_iff_of_chart
    {o o' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy}
    (ho : IsSectionOrientation f hf.toIsScFredholmSection o)
    (ho' : IsSectionOrientation f hf.toIsScFredholmSection o') {x y : PathCat PX} (a : x ⟶ y) :
    o x.pt x.smooth = o' x.pt x.smooth ↔ o y.pt y.smooth = o' y.pt y.smooth := by
  rw [← (isSectionOrientation_iff_of_chart hX hch hf hsec o).1 ho x y a,
    ← (isSectionOrientation_iff_of_chart hX hch hf hsec o').1 ho' x y a]
  exact (orFunctorMapOfChart hX hch hf hsec a).apply_eq_iff_eq.symm

/-- **On the path component of a point there are exactly two orientations**: for an orientation
`o` and a smooth point `x` there is an orientation `o'` which differs from `o` at every point
joined to `x` by an sc-smooth path and agrees with `o` at the other points, and on the path
component of `x` every orientation agrees with `o` or with `o'`. -/
theorem IsSectionOrientation.exists_two_of_chart
    {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy}
    (ho : IsSectionOrientation f hf.toIsScFredholmSection o) (x : PathCat PX) :
    ∃ o' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy,
      IsSectionOrientation f hf.toIsScFredholmSection o' ∧
      (∀ y : PathCat PX, Nonempty (x ⟶ y) → o' y.pt y.smooth ≠ o y.pt y.smooth) ∧
      (∀ y : PathCat PX, IsEmpty (x ⟶ y) → o' y.pt y.smooth = o y.pt y.smooth) ∧
      ∀ o'' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy,
        IsSectionOrientation f hf.toIsScFredholmSection o'' →
        (∀ y : PathCat PX, Nonempty (x ⟶ y) → o'' y.pt y.smooth = o y.pt y.smooth) ∨
        (∀ y : PathCat PX, Nonempty (x ⟶ y) → o'' y.pt y.smooth = o' y.pt y.smooth) := by
  classical
  have htwo := fun (y : X) (hy : y ∈ PX.smoothSet) =>
    exists_two_orx hf.toIsScFredholmSection hy hsec
  -- the other orientation at `y`
  have hne : ∀ y (hy : y ∈ PX.smoothSet) (p : Orx f hf.toIsScFredholmSection y hy), ∃ q, q ≠ p :=
    fun y hy p =>
      let ⟨a₁, a₂, ha, _⟩ := htwo y hy
      if hp : p = a₁ then ⟨a₂, hp ▸ ha.symm⟩ else ⟨a₁, Ne.symm hp⟩
  let flip : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy →
      Orx f hf.toIsScFredholmSection y hy := fun y hy p => (hne y hy p).choose
  have hflip : ∀ y hy p, flip y hy p ≠ p := fun y hy p => (hne y hy p).choose_spec
  have hother : ∀ y hy (p q : Orx f hf.toIsScFredholmSection y hy), q ≠ p → q = flip y hy p :=
    fun y hy p q hq =>
      let ⟨_, _, _, hall⟩ := htwo y hy
      eq_of_ne_of_ne_of_two hall hq (hflip y hy p)
  have hΓ := (isSectionOrientation_iff_of_chart hX hch hf hsec o).1 ho
  let o' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy := fun y hy =>
    if Nonempty (x ⟶ ⟨y, hy⟩) then flip y hy (o y hy) else o y hy
  have e₁ : ∀ y : PathCat PX, Nonempty (x ⟶ y) →
      o' y.pt y.smooth = flip y.pt y.smooth (o y.pt y.smooth) := fun _ h => if_pos h
  have e₂ : ∀ y : PathCat PX, IsEmpty (x ⟶ y) → o' y.pt y.smooth = o y.pt y.smooth :=
    fun _ h => if_neg (not_nonempty_iff.2 h)
  have ho' : IsSectionOrientation f hf.toIsScFredholmSection o' := by
    refine (isSectionOrientation_iff_of_chart hX hch hf hsec o').2 fun y z a => ?_
    by_cases hy : Nonempty (x ⟶ y)
    · rw [e₁ y hy, e₁ z ⟨hy.some ≫ a⟩]
      refine hother _ _ _ _ fun h => hflip _ _ (o y.pt y.smooth) ?_
      exact (orFunctorMapOfChart hX hch hf hsec a).injective (h.trans (hΓ y z a).symm)
    · have hz : IsEmpty (x ⟶ z) := not_nonempty_iff.1 fun ⟨b⟩ => hy ⟨b ≫ Groupoid.inv a⟩
      rw [e₂ y (not_nonempty_iff.1 hy), e₂ z hz]
      exact hΓ y z a
  refine ⟨o', ho', fun y hy => (e₁ y hy).symm ▸ hflip _ _ _, e₂, fun o'' ho'' => ?_⟩
  by_cases hx : o'' x.pt x.smooth = o x.pt x.smooth
  · exact Or.inl fun y ⟨a⟩ => (ho''.apply_eq_iff_of_chart hX hch hf hsec ho a).1 hx
  · have hx' : o'' x.pt x.smooth = o' x.pt x.smooth :=
      (hother _ _ _ _ hx).trans (e₁ x ⟨𝟙 x⟩).symm
    exact Or.inr fun y ⟨a⟩ => (ho''.apply_eq_iff_of_chart hX hch hf hsec ho' a).1 hx'

end Transport

end Push

end Polyfold
