import Polyfold.Chapter15.ProductEp
import Polyfold.Chapter6.CubeFredholm
import Polyfold.Chapter10.StrongBundleWeakFibredProduct
import Polyfold.Chapter12.BumpEp
import Polyfold.Chapter12.CompactnessEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Corollary 15.3.10 (2)
(p. 699) and its proof (pp. 699–700): **the tame ep-groupoid `[0, 1] × X`, the pulled-back strong
bundle `W̃ = [0, 1] × W → [0, 1] × X` and the section `f̃(t, x) = (t, f(x))`**.  Part III plan,
missing prerequisite (e).

# `[0, 1]ⁿ × X` as an ep-groupoid

## Reading

The text's `X̃ = [0, 1] × X` is the product (`EpGroupoid.prod`, `ProductEp`) of the trivial
ep-groupoid of the M-polyfold `[0, 1]` with `X`; the strong bundle `W̃` is the pull-back of `W`
along the projection functor `X̃ → X` (`SEP.pullbackAlong`, Chapter 10), with fibre `W_x` over
`(t, x)`; and `f̃(t, x) = ((t, x), f(x))`.  We use Part I's cube `[0, 1]ⁿ = Fin n → [0, 1]`
(`cubePolyfold`, gap G.65), for which the sc-Fredholm property of `f̃` is proved
(`StrongBundle.IsScFredholmSectionTame.paramCube`); the text's `[0, 1]` is `n = 1`.

## What is formalized

* `EpGroupoid.cubeProd n X = [0, 1]ⁿ × X`; `cubeProj` (the projection functor to `X`),
  `cubeIncl q` (the inclusion `x ↦ (q, x)`), `cubeProj_comp_cubeIncl`.
* `isTame_cubeProd`, `degIndex_cubeProd`: `X̃` is tame for tame `X`, with
  `d(q, x) = #{i | qᵢ ∈ {0, 1}} + d_X(x)`; **`degIndex_cubeProd_one_of_degIndex_eq_zero`**: for
  `n = 1` and `d_X ≡ 0`, `d(t, x) = 1` if `t ∈ {0, 1}` and `0` otherwise, so `∂X̃ = {0, 1} × X`.
* `cubeProd_π_eq_π_iff`: `(q, x) ≅ (q', x')` iff `q = q'` and `x ≅ x'`;
  `isSaturated_prod_cubeProd`: `S × U` is saturated for saturated `U`.
* `cubeOrbitMap`, `continuous_cubeOrbitMap`: the continuous map `[0, 1]ⁿ × |X| → |X̃|`.
* `admitsBumpFunctionsPointwise_cubeProd`: `X̃` admits sc-smooth bump functions if `X` does.
* `SEP.cubeSEP A n`: `W̃ → X̃`; `SEP.cubeLiftEp f`: `f̃`;
  `isScSmoothSectionFunctor_cubeLiftEp`, **`isScFredholmSectionFunctor_cubeLiftEp`** (for an
  sc-Fredholm section functor with Part I's tame germ data);
  `solutionSet_cubeLiftEp` (`S_{f̃} = [0, 1]ⁿ × S_f`) and
  **`hasCompactSolutionSetEp_cubeLiftEp`** (`|S_{f̃}|` is compact if `|S_f|` is).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

/-! ### Constant maps into smooth points -/

namespace MPolyfold

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}

/-- **A constant map with a smooth value is sc-smooth** (any source M-polyfold; source and target in
independent universes, unlike `Chapter9/Boundary`'s `isScSmoothMap_const_of_mem_smoothSet'`). -/
theorem isScSmoothMap_const_of_mem_smoothSet_poly {z : Z} (hz : z ∈ Q.smoothSet) :
    P.IsScSmoothMap Q fun _ => z := by
  refine MPolyfold.isScSmoothMap_of_local fun x => ?_
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source x
  obtain ⟨ψ, hψ, hzψ⟩ := Q.exists_isChart_mem_source z
  have hsm : ψ z ∈ ψ.model.E.smooth := ψ.model.E.mem_smooth_iff.2 fun k =>
    (Q.mem_levelSet_iff hψ hzψ).1 (mem_iInter.1 hz k)
  refine ⟨φ, ψ, φ.source, hφ, hψ, φ.isOpen_source, hx, subset_rfl, fun _ _ => hzψ,
    ⟨fun _ _ => ψ.mapsTo_model z hzψ, fun R _ => ?_⟩⟩
  exact isScSmooth_const_of_mem_smooth R.isScDomain hsm

end MPolyfold

/-- Every point of the cube `[0, 1]ⁿ` is smooth. -/
theorem cubePolyfold_mem_smoothSet {n : ℕ} (q : Fin n → unitInterval) :
    q ∈ (cubePolyfold n).smoothSet :=
  mem_iInter.2 fun k => ((cubePolyfold n).mem_levelSet_iff (UnitCube.isChart_chart
    (UnitCube.corner q)) (UnitCube.mem_chart_corner q)).2
      ((ScScale.mem_smooth_iff _).1 (UnitCube.mem_smooth_rnSc _) k)

/-! ### The ep-groupoid `[0, 1]ⁿ × X` -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
  (n : ℕ) [ParacompactSpace ((Fin n → unitInterval) × Obj)]
  [ParacompactSpace ((Fin n → unitInterval) × Mor)]

/-- **`[0, 1]ⁿ × X`** (Corollary 15.3.10, p. 699, for `n = 1`): the product of the trivial
ep-groupoid of the M-polyfold `[0, 1]ⁿ` with `X`. -/
def cubeProd : EpGroupoid ((Fin n → unitInterval) × Obj) ((Fin n → unitInterval) × Mor) :=
  (trivial (cubePolyfold n)).prod X

@[simp] theorem cubeProd_src (φ : (Fin n → unitInterval) × Mor) :
    (X.cubeProd n).src φ = (φ.1, X.src φ.2) := rfl
@[simp] theorem cubeProd_tgt (φ : (Fin n → unitInterval) × Mor) :
    (X.cubeProd n).tgt φ = (φ.1, X.tgt φ.2) := rfl
theorem cubeProd_PObj : (X.cubeProd n).PObj = (cubePolyfold n).prod X.PObj := rfl
theorem cubeProd_PMor : (X.cubeProd n).PMor = (cubePolyfold n).prod X.PMor := rfl

/-- The projection `[0, 1]ⁿ × X → X`, an sc-smooth functor. -/
def cubeProj : EpFunctor (X.cubeProd n) X := prodSnd (trivial (cubePolyfold n)) X

@[simp] theorem cubeProj_obj : (X.cubeProj n).obj = Prod.snd := rfl
@[simp] theorem cubeProj_mor : (X.cubeProj n).mor = Prod.snd := rfl

/-- The inclusion `x ↦ (q, x)`, `φ ↦ (q, φ)`, an sc-smooth functor `X → [0, 1]ⁿ × X`. -/
def cubeIncl (q : Fin n → unitInterval) : EpFunctor X (X.cubeProd n) where
  obj x := (q, x)
  mor φ := (q, φ)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl
  isScSmoothMap_obj :=
    (MPolyfold.isScSmoothMap_const_of_mem_smoothSet_poly (cubePolyfold_mem_smoothSet q)).prodMk
      MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor :=
    (MPolyfold.isScSmoothMap_const_of_mem_smoothSet_poly (cubePolyfold_mem_smoothSet q)).prodMk
      MPolyfold.isScSmoothMap_id

/-- `pr ∘ i_q = id`. -/
theorem cubeProj_comp_cubeIncl (q : Fin n → unitInterval) :
    (X.cubeProj n).comp (X.cubeIncl n q) = EpFunctor.id X :=
  EpFunctor.ext rfl rfl

/-- **`[0, 1]ⁿ × X` is tame if `X` is.** -/
theorem isTame_cubeProd (hX : X.IsTame) : (X.cubeProd n).IsTame :=
  prod_cube_isTame hX

/-- **The degeneracy index of `[0, 1]ⁿ × X`**: `d(q, x) = #{i | qᵢ ∈ {0, 1}} + d_X(x)`. -/
theorem degIndex_cubeProd (hX : X.IsTame) (q : Fin n → unitInterval) (x : Obj) :
    (X.cubeProd n).PObj.degIndex (q, x) =
      (Finset.univ.filter fun i => (q i : ℝ) = 0 ∨ (q i : ℝ) = 1).card + X.PObj.degIndex x := by
  rw [← cubePolyfold_degIndex q]
  exact (MPolyfold.isTame_prod (cubePolyfold n) X.PObj (cubePolyfold_isTame n) hX).2 q x

/-- **`∂([0, 1] × X) = {0, 1} × X` when `d_X ≡ 0`** (the setting of Corollary 15.3.10): the
degeneracy index of `[0, 1] × X` at `(t, x)` is `1` for `t ∈ {0, 1}` and `0` otherwise. -/
theorem degIndex_cubeProd_one_of_degIndex_eq_zero (hX : X.IsTame)
    (hd : ∀ x, X.PObj.degIndex x = 0) (t : Fin 1 → unitInterval) (x : Obj) :
    (X.cubeProd 1).PObj.degIndex (t, x) = if (t 0 : ℝ) = 0 ∨ (t 0 : ℝ) = 1 then 1 else 0 := by
  rw [degIndex_cubeProd X 1 hX, hd x, add_zero]
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨0, Finset.eq_singleton_iff_unique_mem.2 ⟨by simpa using h, fun i _ => ?_⟩⟩
    exact Subsingleton.elim i 0
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    rwa [Subsingleton.elim i 0]

/-- **The isomorphism classes of `[0, 1]ⁿ × X`**: `(q, x) ≅ (q', x')` iff `q = q'` and
`x ≅ x'`. -/
theorem cubeProd_π_eq_π_iff (p p' : (Fin n → unitInterval) × Obj) :
    (X.cubeProd n).π p = (X.cubeProd n).π p' ↔ p.1 = p'.1 ∧ X.π p.2 = X.π p'.2 := by
  rw [cubeProd, prod_π_eq_π_iff]
  refine and_congr_left' ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨φ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 h
    exact hs.symm.trans ht
  · exact (GroupoidStr.π_eq_π_iff _).2 ⟨p.1, rfl, h⟩

/-- `S × U` is saturated in `[0, 1]ⁿ × X` if `U` is saturated in `X`. -/
theorem isSaturated_prod_cubeProd (S : Set (Fin n → unitInterval)) {U : Set Obj}
    (hU : X.IsSaturated U) : (X.cubeProd n).IsSaturated (S ×ˢ U) := by
  refine subset_antisymm ?_ (subset_preimage_image _ _)
  rintro p ⟨p', hp', hpp'⟩
  rw [cubeProd_π_eq_π_iff] at hpp'
  refine ⟨hpp'.1 ▸ hp'.1, ?_⟩
  rw [← hU]
  exact ⟨p'.2, hp'.2, hpp'.2⟩

/-! #### The orbit space -/

/-- The map `[0, 1]ⁿ × |X| → |[0, 1]ⁿ × X|`, `(q, |x|) ↦ |(q, x)|`. -/
def cubeOrbitMap : (Fin n → unitInterval) × X.OrbitSpace → (X.cubeProd n).OrbitSpace :=
  fun p => Quotient.liftOn p.2 (fun x => (X.cubeProd n).π (p.1, x)) fun _ _ h =>
    ((X.cubeProd n).π_eq_π_iff).2 ⟨(p.1, h.choose), Prod.ext rfl h.choose_spec.1,
      Prod.ext rfl h.choose_spec.2⟩

@[simp] theorem cubeOrbitMap_mk (q : Fin n → unitInterval) (x : Obj) :
    X.cubeOrbitMap n (q, X.π x) = (X.cubeProd n).π (q, x) := rfl

/-- `(q, |x|) ↦ |(q, x)|` is continuous: `id × π` is an open quotient map
(Proposition 7.1.8). -/
theorem continuous_cubeOrbitMap : Continuous (X.cubeOrbitMap n) := by
  have hq : IsOpenQuotientMap (Prod.map (id : (Fin n → unitInterval) → _) X.π) :=
    IsOpenQuotientMap.id.prodMap X.proposition_7_1_8_isOpenQuotientMap
  refine hq.isQuotientMap.continuous_iff.2 ?_
  have : X.cubeOrbitMap n ∘ Prod.map id X.π = (X.cubeProd n).π := funext fun _ => rfl
  rw [this]
  exact (X.cubeProd n).continuous_π

/-- `|[0, 1]ⁿ × A| = cubeOrbitMap([0, 1]ⁿ × |A|)`. -/
theorem image_π_cubeProd (S : Set (Fin n → unitInterval)) (A : Set Obj) :
    (X.cubeProd n).π '' (S ×ˢ A) = X.cubeOrbitMap n '' (S ×ˢ (X.π '' A)) := by
  ext o
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
    exact ⟨(p.1, X.π p.2), ⟨h1, p.2, h2, rfl⟩, rfl⟩
  · rintro ⟨⟨q, _⟩, ⟨h1, x, hx, rfl⟩, rfl⟩
    exact ⟨(q, x), ⟨h1, hx⟩, rfl⟩

/-- `|[0, 1]ⁿ × A|` is compact if `|A|` is. -/
theorem isCompact_image_π_cubeProd {A : Set Obj} (hA : IsCompact (X.π '' A)) :
    IsCompact ((X.cubeProd n).π '' (univ ×ˢ A)) := by
  rw [image_π_cubeProd]
  exact (isCompact_univ.prod hA).image (X.continuous_cubeOrbitMap n)

/-! #### Bump functions -/

/-- **`[0, 1]ⁿ × X` admits sc-smooth bump functions if `X` does** (Definition 12.3.1, pointwise
reading; Theorem 12.3.2 (1) and Part I's `admitsBumpFunctions_prod_cube`). -/
theorem admitsBumpFunctionsPointwise_cubeProd (h : X.AdmitsBumpFunctionsPointwise) :
    (X.cubeProd n).AdmitsBumpFunctionsPointwise :=
  (X.cubeProd n).theorem_12_3_2_1.2 (admitsBumpFunctions_prod_cube
    (X.theorem_12_3_2_1.1 h))

end EpGroupoid

/-! ### The strong bundle `W̃ = [0, 1]ⁿ × W` and the section `f̃` -/

namespace SEP

variable (A : SEP.{u}) (n : ℕ)

/-- `[0, 1]ⁿ × X` as an object of `EP`. -/
def cubeEP : EP.{u} :=
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PMor
  ⟨_, _, A.X.cubeProd n⟩

/-- **`W̃ → [0, 1]ⁿ × X`** (Corollary 15.3.10 (2), p. 699, `n = 1`): the pull-back of `W` along
the projection `[0, 1]ⁿ × X → X`; its fibre over `(q, x)` is `W_x`. -/
def cubeSEP : SEP.{u} :=
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PMor
  A.pullbackAlong (A.cubeEP n) (A.X.cubeProj n)

theorem cubeSEP_Obj : (A.cubeSEP n).Obj = ((Fin n → unitInterval) × A.Obj) := rfl
theorem cubeSEP_W : (A.cubeSEP n).W =
    pullbackSpace A.P (Prod.snd : (Fin n → unitInterval) × A.Obj → A.Obj) := rfl
variable {A n} in
/-- The point `((q, x), w)` of `W̃`. -/
def cubeVal (w : (A.cubeSEP n).W) : ((Fin n → unitInterval) × A.Obj) × A.W :=
  Subtype.val (show pullbackSpace A.P (Prod.snd : (Fin n → unitInterval) × A.Obj → A.Obj) from w)

theorem cubeSEP_P (w : (A.cubeSEP n).W) : (A.cubeSEP n).P w = (cubeVal w).1 := rfl

variable {A n}

/-- **`f̃(q, x) = ((q, x), f(x))`** (Corollary 15.3.10 (2): `f̃(t, x) = (t, f(x))`). -/
def cubeLiftEp (f : A.Obj → A.W) (hf : IsSection A.P f) : (A.cubeSEP n).Obj → (A.cubeSEP n).W :=
  pullbackLift (Prod.snd : (Fin n → unitInterval) × A.Obj → A.Obj) (f ∘ Prod.snd)
    fun z => hf z.2

theorem cubeLiftEp_val {f : A.Obj → A.W} (hf : IsSection A.P f) (z : (A.cubeSEP n).Obj) :
    cubeVal (cubeLiftEp (n := n) f hf z) = (z, f z.2) := rfl

theorem isSection_cubeLiftEp {f : A.Obj → A.W} (hf : IsSection A.P f) :
    IsSection (A.cubeSEP n).P (cubeLiftEp (n := n) f hf) :=
  isSection_pullbackLift _

/-- `f̃` is functorial if `f` is: `f̃(t(q, φ)) = μ̃((q, φ), f̃(s(q, φ)))`. -/
theorem isFunctorialSection_cubeLiftEp {f : A.Obj → A.W} (hf : IsSection A.P f)
    (hfun : A.E.IsFunctorialSection hf) :
    (A.cubeSEP n).E.IsFunctorialSection (isSection_cubeLiftEp (n := n) hf) := by
  intro φ
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change f (A.X.tgt φ.2) = A.E.μ ⟨(φ.2, f (A.X.src φ.2)), _⟩
  exact hfun φ.2

/-- **`f̃` is an sc-smooth section functor** if `f` is (Part I's
`StrongBundle.IsScSmoothSection.pullback`). -/
theorem isScSmoothSectionFunctor_cubeLiftEp {f : A.Obj → A.W}
    (hf : A.E.IsScSmoothSectionFunctor f) :
    (A.cubeSEP n).E.IsScSmoothSectionFunctor (cubeLiftEp (n := n) f hf.1.1) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold n).prod A.X.PObj) (A.X.cubeProj n).obj
  obtain ⟨hsm, hfun⟩ := hf
  exact ⟨hsm.pullback (A.X.cubeProj n).isScSmoothMap_obj,
    isFunctorialSection_cubeLiftEp hsm.1 hfun⟩

/-- **`f̃` is an sc-Fredholm section functor** if `f` is one and has Part I's tame germ data
(`StrongBundle.IsScFredholmSectionTame.paramCube`, gap G.65 (a)). -/
theorem isScFredholmSectionFunctor_cubeLiftEp {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f) :
    (A.cubeSEP n).E.IsScFredholmSectionFunctor (cubeLiftEp (n := n) f hf.1.1.1) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold n).prod A.X.PObj)
    (Prod.snd : (Fin n → unitInterval) × A.Obj → A.Obj)
  exact ⟨isScSmoothSectionFunctor_cubeLiftEp hf.1,
    (StrongBundle.IsScFredholmSectionTame.paramCube (n := n) hft).toIsScFredholmSection⟩

/-- **`S_{f̃} = [0, 1]ⁿ × S_f`.** -/
theorem solutionSet_cubeLiftEp {f : A.Obj → A.W} (hf : IsSection A.P f) :
    solutionSet (A.cubeSEP n).P (cubeLiftEp (n := n) f hf) = univ ×ˢ solutionSet A.P f := by
  ext z
  constructor
  · intro h
    exact ⟨mem_univ _, congrArg (fun q : (A.cubeSEP n).W => (cubeVal q).2) h⟩
  · rintro ⟨-, h⟩
    exact Subtype.ext (Prod.ext rfl h)

/-- **`|S_{f̃}|` is compact if `|S_f|` is** (Corollary 15.3.10 (2): `f̃` has a compact solution
set). -/
theorem hasCompactSolutionSetEp_cubeLiftEp {f : A.Obj → A.W} (hf : IsSection A.P f)
    (hS : A.E.HasCompactSolutionSetEp f) :
    (A.cubeSEP n).E.HasCompactSolutionSetEp (cubeLiftEp (n := n) f hf) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PMor
  have := A.B.paracompactSpace_pullback ((cubePolyfold n).prod A.X.PObj)
    (Prod.snd : (Fin n → unitInterval) × A.Obj → A.Obj)
  unfold EpStrongBundle.HasCompactSolutionSetEp
  rw [solutionSet_cubeLiftEp]
  exact A.X.isCompact_image_π_cubeProd n hS

end SEP

end Polyfold
