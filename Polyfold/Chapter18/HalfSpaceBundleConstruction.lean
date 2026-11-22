import Polyfold.Chapter17.StrongBundleStructuresExamples
import Polyfold.Chapter14.HalfSpaceBundle
import Polyfold.Chapter17.PolyfoldLevels

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 and §17.7 (Definitions 17.1.2, 17.1.8, 17.1.30, 17.7.1–17.7.4, pp. 776–825): **a strong
polyfold bundle construction with non-empty boundary and non-trivial isotropy**, the base of the
boundary witnesses for Chapter 18 (`HalfSpaceWitnesses.lean`).  Numbers and pages are the 2021
text's.

# `ℤ/2` acting on the half-plane `[0, ∞) × ℝ`

* The GCT `C = ℤ/2 ⋉ H` (`halfC`), `H = [0, ∞) × ℝ` the quadrant M-polyfold of Chapter 3
  (`HalfSpaceBundle.basePoly 1`), `ℤ/2 = ℤˣ` acting by `(a, y) ↦ (a, ±y)`; the polyfold
  construction `F(x) = {Ψ₀}` with the identity uniformizer (`halfS`, tame).
* `∂C = {(0, y)}` (`mem_boundarySet_iff`), non-empty: the corner `(0, 0)` lies in `∂C`
  (`corner_mem_boundarySet`) and has the non-trivial automorphism `(−1, (0, 0))`
  (`exists_ne_unit_corner`); every `(a, 0)` has isotropy `ℤ/2`.
* The vector bundle GCT `P : E → C` (`halfV`): `μ(x) = ℝ`, `μ(g, x) = 1`, with the topology of
  `|E| ≅ |ℤ/2 ⋉ (H × ℝ)|`.  The fibre action is trivial: an equivariant section is then a function
  even in `y`, and sections with compact zero sets crossing `∂C` exist (the half circle).
* The strong bundle uniformizer `Ψ̄ : ℤ/2 ⋉ (H × ℝ) → E` (`halfUnif`) over the half-space bundle
  `H × ℝ → H` of Chapter 14 (`HalfSpaceBundle.bundle 1 1`), `g ∗ (x, v) = (g x, v)`, and the
  strong polyfold bundle construction `F̄(x) = {Ψ̄}` (`halfQ`), with the transition maps
  `t̄(a, k) = g ∗ k` strong bundle maps and local strong bundle isomorphisms
  (`isStrongBundleMap_transT`, `isLocalStrongBundleIso_transT`), as in the reflection bundle
  of `StrongBundleStructuresExamples.lean`; the covering family with one copy of `Ψ̄`
  (`halfSingle`).
* The strong bundle maps used there: `(x, v) ↦ (G(x), L v)` between half-space bundles, for a
  `C^∞` map `G` with `G(H) ⊆ H'` and a linear `L` (`HalfSpaceBundle.isStrongBundleMap_halfProdMap`,
  through `HalfSpaceBundle.isScSmoothMap_basePoly_of_contDiff`).

The action on `K = H × ℝ` is the one of Definition 17.7.2 (1) with trivial fibre action; it is
declared as the field `actK` and, locally, preferred over the product action of `ℤˣ` on
`H × ℝ`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

open StrongBundle

variable {m m' k k' : ℕ}

/-- **A `C^∞` map `ℝ ⊕ ℝᵐ → ℝ ⊕ ℝᵐ'` mapping `H` into `H` is sc-smooth `H → H`** (in the one
chart of each side it is the map itself on the partial quadrant `H`). -/
theorem isScSmoothMap_basePoly_of_contDiff {G : Pm m → Pm m'} (hG : ContDiff ℝ ∞ G)
    (hH : ∀ x : H m, G (x : Pm m) ∈ H m') :
    (basePoly m).IsScSmoothMap (basePoly m') (fun x => (⟨G (x : Pm m), hH x⟩ : H m')) := by
  refine MPolyfold.isScSmoothMap_of_local fun x => ⟨baseChart m, baseChart m', univ,
    (basePoly m).isChart_of_mem (mem_singleton _), (basePoly m').isChart_of_mem (mem_singleton _),
    isOpen_univ, mem_univ x, subset_univ _, mapsTo_univ _ _, ?_⟩
  have himg : (baseChart m) '' univ = H m := by
    rw [image_univ]; exact Subtype.range_coe
  rw [himg]
  change IsScSmoothRetractMap (halfSpaceSc m) (H m) (H m)
    (halfSpaceSc m') (H m') (H m') (fun u => G (((baseChart m).symm u : H m) : Pm m))
  refine (isScSmoothRetractMap_iff_exists (relOpen_H m).isScRetract).2
    ⟨fun u hu => ?_, ScRetraction.id (relOpen_H m), image_id _, ?_⟩
  · exact hH _
  · refine (isScSmooth_of_bijective_toBase bijective_toBase_E bijective_toBase_E
      (relOpen_H m).isScDomain (f := G) hG.contDiffOn).congr (relOpen_H m).isScDomain
        fun u hu => ?_
    change G u = G (((baseChart m).symm u : H m) : Pm m)
    rw [baseChart_symm_val hu]

/-- `(x, v) ↦ (G(x), L v)` between half-space bundles. -/
def halfProdMap (G : Pm m → Pm m') (hH : ∀ x : H m, G (x : Pm m) ∈ H m')
    (L : (Fin k → ℝ) →L[ℝ] (Fin k' → ℝ)) (w : H m × (Fin k → ℝ)) : H m' × (Fin k' → ℝ) :=
  (⟨G (w.1 : Pm m), hH w.1⟩, L w.2)

theorem chart₀_K : (chart₀ (m := m) (k := k)).K = H m ×ˢ univ := image_id _

theorem image_toMChart_chart₀ :
    (chart₀ (m := m) (k := k)).toMChart (bundle m k).continuous '' univ = H m ×ˢ univ := by
  ext ⟨u, v⟩
  constructor
  · rintro ⟨y, -, hy⟩
    rw [← hy]
    exact ⟨y.1.2, mem_univ _⟩
  · rintro ⟨hu, -⟩
    exact ⟨(⟨u, hu⟩, v), mem_univ _, rfl⟩

theorem chart₀_symm_apply {p : Pm m × (Fin k → ℝ)} (hp : p ∈ H m ×ˢ (univ : Set (Fin k → ℝ))) :
    (((chart₀ (m := m) (k := k)).toPartialEquiv.symm p).1 : Pm m) = p.1 ∧
      ((chart₀ (m := m) (k := k)).toPartialEquiv.symm p).2 = p.2 :=
  ⟨baseChart_symm_val hp.1, rfl⟩

variable {G : Pm m → Pm m'} (hG : ContDiff ℝ ∞ G) (hH : ∀ x : H m, G (x : Pm m) ∈ H m')
  (L : (Fin k → ℝ) →L[ℝ] (Fin k' → ℝ))

include hG in
/-- `(x, v) ↦ (G(x), L v)` is sc-smooth `W[0] → W'[0]`: in the one chart it is
`(u, v) ↦ (G(u), L v)` on `H × ℝᵏ`. -/
theorem isScSmoothMap_zero_halfProdMap :
    (bundle m k).toMPolyfold0.IsScSmoothMap (bundle m' k').toMPolyfold0 (halfProdMap G hH L) := by
  refine MPolyfold.isScSmoothMap_of_local fun w => ⟨chart₀.toMChart (bundle m k).continuous,
    chart₀.toMChart (bundle m' k').continuous, univ,
    (bundle m k).isChart_toMChart (mem_singleton _),
    (bundle m' k').isChart_toMChart (mem_singleton _), isOpen_univ, mem_univ w,
    fun _ _ => ⟨mem_univ _, mem_univ _⟩, fun _ _ => ⟨mem_univ _, mem_univ _⟩, ?_⟩
  rw [image_toMChart_chart₀]
  change IsScSmoothRetractMap ((halfSpaceSc m).prod (rnSc k)) (H m ×ˢ univ) (H m ×ˢ univ)
    ((halfSpaceSc m').prod (rnSc k')) (H m' ×ˢ univ) ((chart₀ (m := m') (k := k')).K)
    (fun p => chart₀ (halfProdMap G hH L ((chart₀ (m := m) (k := k)).toPartialEquiv.symm p)))
  rw [chart₀_K]
  have hU := (relOpen_H m).prod_univ (rnSc k)
  refine (isScSmoothRetractMap_iff_exists hU.isScRetract).2
    ⟨fun p hp => ⟨hH _, mem_univ _⟩, ScRetraction.id hU, image_id _, ?_⟩
  refine (isScSmooth_of_bijective_toBase
    (bijective_toBase_prod bijective_toBase_E (bijective_toBase_const _))
    (bijective_toBase_prod bijective_toBase_E (bijective_toBase_const _))
    hU.isScDomain (f := fun p : Pm m × (Fin k → ℝ) => (G p.1, L p.2))
    ((hG.comp contDiff_fst).prodMk (L.contDiff.comp contDiff_snd)).contDiffOn).congr
      hU.isScDomain fun p hp => ?_
  obtain ⟨h1, h2⟩ := chart₀_symm_apply (k := k) hp
  change (G p.1, L p.2) = (G (((chart₀ (m := m) (k := k)).toPartialEquiv.symm p).1 : Pm m),
    L ((chart₀ (m := m) (k := k)).toPartialEquiv.symm p).2)
  rw [h1, h2]

/-- `(x, v) ↦ (G(x), L v)` maps `W_{0,1}` into `W'_{0,1}` (every point lies in `W_{0,1}`). -/
theorem mapsTo_oneSet_halfProdMap :
    MapsTo (halfProdMap G hH L) (bundle m k).oneSet (bundle m' k').oneSet := by
  rintro y - c hc -
  rw [mem_singleton_iff.1 hc]
  exact (bijective_toBase_const _ 1).2 _

include hG in
/-- `(x, v) ↦ (G(x), L v)` is sc-smooth `W[1] → W'[1]`: in the charts `Φ[1]` it is again
`(u, v) ↦ (G(u), L v)`. -/
theorem isScSmoothMap_one_halfProdMap :
    (bundle m k).toMPolyfold1.IsScSmoothMap (bundle m' k').toMPolyfold1
      (oneRestrict (bundle m k) (bundle m' k') (halfProdMap G hH L)
        (mapsTo_oneSet_halfProdMap hH L)) := by
  have hc : chart₀ ∈ (bundle m k).atlas.charts := mem_singleton _
  have hc' : chart₀ ∈ (bundle m' k').atlas.charts := mem_singleton _
  have hK : ∀ (n j : ℕ), strongShiftOne (chart₀ (m := n) (k := j)).K = H n ×ˢ univ :=
    fun n j => by
      ext p
      change (p.1, _) ∈ (chart₀ (m := n) (k := j)).K ↔ _
      rw [chart₀_K]
      exact ⟨fun h => ⟨h.1, mem_univ _⟩, fun h => ⟨h.1, mem_univ _⟩⟩
  refine MPolyfold.isScSmoothMap_of_local fun y => ⟨oneChart hc y,
    oneChart hc' (oneRestrict (bundle m k) (bundle m' k') (halfProdMap G hH L)
        (mapsTo_oneSet_halfProdMap hH L) y), univ,
    (bundle m k).isChart_oneChart hc y, (bundle m' k').isChart_oneChart hc' _, isOpen_univ,
    mem_univ y, fun _ _ => ⟨mem_univ _, mem_univ _⟩, fun _ _ => ⟨mem_univ _, mem_univ _⟩, ?_⟩
  have himg : (oneChart hc y) '' univ = H m ×ˢ univ := by
    rw [image_univ, ← hK m k]
    ext z
    constructor
    · rintro ⟨y', rfl⟩
      exact (oneChart hc y).toPartialEquiv.map_source (x := y') ⟨mem_univ _, mem_univ _⟩
    · intro hz
      exact ⟨(oneChart hc y).symm z, (oneChart hc y).toPartialEquiv.right_inv hz⟩
  rw [himg]
  change IsScSmoothRetractMap ((halfSpaceSc m).prod (rnSc k).shift) (H m ×ˢ univ) (H m ×ˢ univ)
    ((halfSpaceSc m').prod (rnSc k').shift) (H m' ×ˢ univ)
    (strongShiftOne (chart₀ (m := m') (k := k')).K) _
  have hU := (relOpen_H m).prod_univ (rnSc k).shift
  have hb : ∀ (n j : ℕ) (i : ℕ), Bijective (((halfSpaceSc n).prod (rnSc j).shift).toBase i) :=
    fun n j => bijective_toBase_prod bijective_toBase_E
      (bijective_toBase_shift (bijective_toBase_const _))
  have e : ∀ (j : ℕ) (v : Fin j → ℝ), invFun ((rnSc j).toBase 1) v = v := fun j v => by
    conv_lhs => rw [← ScBanach.const_toBase (Fin j → ℝ) 1 v]
    exact leftInverse_invFun ((rnSc j).toBase_injective 1) v
  refine (isScSmoothRetractMap_iff_exists hU.isScRetract).2
    ⟨fun p hp => ?_, ScRetraction.id hU, image_id _, ?_⟩
  · have := (oneChart hc' (oneRestrict (bundle m k) (bundle m' k') (halfProdMap G hH L)
        (mapsTo_oneSet_halfProdMap hH L) y)).toPartialEquiv.map_source
          (x := oneRestrict (bundle m k) (bundle m' k') (halfProdMap G hH L)
            (mapsTo_oneSet_halfProdMap hH L) ((oneChart hc y).symm p)) ⟨mem_univ _, mem_univ _⟩
    exact this
  refine (isScSmooth_of_bijective_toBase (hb m k) (hb m' k') hU.isScDomain
    (f := fun p : Pm m × (Fin k → ℝ) => (G p.1, L p.2))
    ((hG.comp contDiff_fst).prodMk (L.contDiff.comp contDiff_snd)).contDiffOn).congr
      hU.isScDomain fun p hp => ?_
  have hp' : p ∈ strongShiftOne (chart₀ (m := m) (k := k)).K := by rw [hK]; exact hp
  have hs := oneChart_symm_apply (B := bundle m k) hc y hp'
  change (G p.1, L p.2) = (chart₀ (m := m') (k := k')).liftOne (halfProdMap G hH L
    ((bundle m k).oneVal ((oneChart hc y).symm p)))
  rw [hs]
  unfold StrongBundleChart.liftOne
  refine Prod.ext ?_ ?_
  · change G p.1 = G (((chart₀ (m := m) (k := k)).toPartialEquiv.symm
      (p.1, (rnSc k).toBase 1 p.2)).1 : Pm m)
    exact congrArg G (chart₀_symm_apply (m := m) (k := k)
      (p := (p.1, (rnSc k).toBase 1 p.2)) ⟨hp.1, mem_univ _⟩).1.symm
  · change L p.2 = invFun ((rnSc k').toBase 1) (L ((rnSc k).toBase 1 p.2))
    rw [e, ScBanach.const_toBase]

include hG in
/-- **`(x, v) ↦ (G(x), L v)` is a strong bundle map** of half-space bundles covering
`x ↦ G(x)`, for a `C^∞` map `G` with `G(H) ⊆ H'` and a linear map `L`. -/
theorem isStrongBundleMap_halfProdMap :
    (bundle m k).IsStrongBundleMap (bundle m' k') (fun x => (⟨G (x : Pm m), hH x⟩ : H m'))
      (halfProdMap G hH L) where
  covers _ := rfl
  fiber_linear x := by
    let e := (fibEquiv (m := m) (k := k) x).linearEquiv ℝ
    let e' := (fibEquiv (m := m') (k := k') (⟨G (x : Pm m), hH x⟩ : H m')).linearEquiv ℝ
    have h : fiberRestrict (proj m k) (proj m' k') (fun x => (⟨G (x : Pm m), hH x⟩ : H m'))
        (halfProdMap G hH L) (fun _ => rfl) x =
        e'.symm.toLinearMap.comp (L.toLinearMap.comp e.toLinearMap) := by
      funext v
      apply Subtype.ext
      change ((⟨G ((v : H m × (Fin k → ℝ)).1 : Pm m), hH _⟩ : H m'),
          L (v : H m × (Fin k → ℝ)).2) =
        ((⟨G (x : Pm m), hH x⟩ : H m'), L (v : H m × (Fin k → ℝ)).2)
      rw [show (v : H m × (Fin k → ℝ)).1 = x from v.2]
    rw [h]; exact LinearMap.isLinear _
  isScSmoothMap := isScSmoothMap_zero_halfProdMap hG hH L
  mapsTo_oneSet := mapsTo_oneSet_halfProdMap hH L
  isScSmoothMap_one := isScSmoothMap_one_halfProdMap hG hH L

end HalfSpaceBundle

namespace GCT.VectorBundle.HalfSpaceReflection

open GroupoidalCategory GroupoidalCategory.BanachFunctor HalfSpaceBundle StrongBundle
  PolyfoldConstruction

/-! ### The GCT `ℤ/2 ⋉ H` and its polyfold structure -/

/-- `(a, y) ↦ (a, g y)` on `ℝ ⊕ ℝ`, `g ∈ ℤˣ = {±1}`. -/
def reflPm (g : ℤˣ) (p : Pm 1) : Pm 1 := (p.1, g • p.2)

theorem reflPm_mem (g : ℤˣ) (x : H 1) : reflPm g (x : Pm 1) ∈ H 1 := x.2

/-- **The reflection `(a, y) ↦ (a, g y)` of the half-plane `H = [0, ∞) × ℝ`**, `g ∈ ℤˣ`. -/
instance halfReflAction : MulAction ℤˣ (H 1) where
  smul g x := ⟨reflPm g x, reflPm_mem g x⟩
  one_smul x := Subtype.ext (Prod.ext rfl (one_smul ℤˣ (x : Pm 1).2))
  mul_smul g h x := Subtype.ext (Prod.ext rfl (mul_smul g h (x : Pm 1).2))

theorem smul_val (g : ℤˣ) (x : H 1) :
    ((g • x : H 1) : Pm 1) = ((x : Pm 1).1, g • (x : Pm 1).2) := rfl

theorem contDiff_reflPm (g : ℤˣ) : ContDiff ℝ ∞ (reflPm g) :=
  contDiff_fst.prodMk ((ReflectionBundle.contDiff_units_smul g).comp contDiff_snd)

/-- `g ∗ · : H → H` is sc-smooth. -/
theorem isScSmoothMap_halfSmul (g : ℤˣ) :
    (basePoly 1).IsScSmoothMap (basePoly 1) fun x : H 1 => g • x :=
  isScSmoothMap_basePoly_of_contDiff (contDiff_reflPm g) (reflPm_mem g)

theorem continuous_halfSmul (g : ℤˣ) : Continuous fun x : H 1 => g • x :=
  ((contDiff_reflPm g).continuous.comp continuous_subtype_val).subtype_mk _

/-- **The GCT `C = ℤ/2 ⋉ H`**, `H = [0, ∞) × ℝ`, `ℤ/2 = ℤˣ` acting by `(a, y) ↦ (a, ±y)`
(Definition 17.1.2). -/
abbrev halfC : GCT.{0} := GCT.translation ℤˣ (H 1) isScSmoothMap_halfSmul

/-- **The polyfold structure on `ℤ/2 ⋉ H`** (Definition 17.1.8): `F(x) = {Ψ₀}`, `Ψ₀` the identity
uniformizer. -/
abbrev halfS : halfC.PolyfoldConstruction :=
  twistConstruction isScSmoothMap_halfSmul (TranslationTwist.refl ℤˣ (H 1))

theorem halfS_hasUniformizers : halfS.HasUniformizers :=
  twistConstruction_hasUniformizers _ _

theorem halfS_isTame : halfS.IsTame :=
  twistConstruction_isTame _ _ (isTame_halfSEP 1 1)

/-- The corner `(0, 0)` of `H`. -/
def corner : H 1 := ⟨0, fun _ => le_rfl⟩

/-! ### The vector bundle GCT -/

/-- **The functor `μ : ℤ/2 ⋉ H → Ban`**: `μ(x) = ℝ`, `μ(g, x) = 1`. -/
def halfMu : BanachFunctor halfC.toGroupoidalCategory where
  V _ := Fin 1 → ℝ
  map _ := ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ)
  act_unit e h := by
    obtain ⟨α, v⟩ := e
    change (⟨(1 : ℤˣ) • α, v⟩ : Σ _ : H 1, Fin 1 → ℝ) = ⟨α, v⟩
    rw [one_smul]
  act_comp φ ψ hφψ e h := by
    obtain ⟨α, v⟩ := e
    change (⟨(φ.1 * ψ.1) • ψ.2, v⟩ : Σ _ : H 1, Fin 1 → ℝ) = ⟨φ.1 • φ.2, v⟩
    have : φ.2 = ψ.1 • ψ.2 := hφψ
    rw [mul_smul, this]

/-- The total space `K = H × ℝ` of the trivial bundle over `O = H`. -/
abbrev K : Type := H 1 × (Fin 1 → ℝ)

/-- **The action `g ∗ (x, v) = (g x, v)` on `K`** (trivial on the fibre; not the product action,
which would also act on the fibre). -/
@[reducible] def halfActK : MulAction ℤˣ K where
  smul g k := (g • k.1, k.2)
  one_smul k := Prod.ext (one_smul ℤˣ k.1) rfl
  mul_smul g h k := Prod.ext (mul_smul g h k.1) rfl

attribute [local instance high] halfActK

/-- The scalar action of `halfActK`, preferred over the product action on `K`. -/
@[reducible] def halfSMulK : SMul ℤˣ K := halfActK.toSMul

attribute [local instance 20000] halfSMulK

theorem smulK_eq (g : ℤˣ) (k : K) : g • k = (g • k.1, k.2) := rfl

/-- `(α, e) ↦ (α, e)`: an object of `E_μ` as a point of `K`. -/
def toPair (e : halfMu.EObj) : K := (e.1, e.2)

@[simp] theorem toPair_objMk (k : K) : toPair (halfMu.objMk k.1 k.2) = k := rfl

/-- `μ(φ)(e) = φ.1 ∗ e` read in `K`. -/
theorem toPair_act (φ : halfC.Mor) (e : halfMu.EObj)
    (h : halfMu.base e = halfC.toGroupoidStr.src φ) :
    toPair (halfMu.act φ e h) = φ.1 • toPair e := by
  obtain ⟨α, v⟩ := e
  obtain ⟨g, x⟩ := φ
  change α = x at h
  subst h
  rfl

/-- The functor `ℤ/2 ⋉ K → E_μ`, `k ↦ (k₁, k₂)`, `(g, k) ↦ ((g, k₁), (k₁, k₂))`. -/
def kFunctor : GroupoidFunctor (GroupoidStr.translation ℤˣ K) halfMu.groupoid where
  obj k := halfMu.objMk k.1 k.2
  mor x := ⟨((x.1, x.2.1), halfMu.objMk x.2.1 x.2.2), rfl⟩
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp x y h := by
    have hy : x.2 = y.1 • y.2 := h
    have hc : halfMu.groupoid.src
        (⟨((x.1, x.2.1), halfMu.objMk x.2.1 x.2.2), rfl⟩ : halfMu.EMor) =
        halfMu.groupoid.tgt (⟨((y.1, y.2.1), halfMu.objMk y.2.1 y.2.2), rfl⟩ : halfMu.EMor) := by
      change halfMu.objMk x.2.1 x.2.2 = halfMu.objMk (y.1 • y.2).1 (y.1 • y.2).2
      rw [hy]
    obtain ⟨h1, h2⟩ := groupoid_comp_of hc
    refine EMor.ext ?_ ?_
    · rw [h1]
      change ((x.1 * y.1, y.2.1) : ℤˣ × H 1) = (x.1 * y.1, y.2.1)
      rfl
    · rw [h2]; rfl
  mor_unit _ := rfl

theorem kFunctor_orbitMap_bijective : Bijective kFunctor.orbitMap := by
  refine ⟨fun z z' hz => ?_, fun z => ?_⟩
  · induction z using Quotient.inductionOn with | h k => ?_
    induction z' using Quotient.inductionOn with | h k' => ?_
    obtain ⟨a, ha, hb⟩ := (GroupoidStr.π_eq_π_iff _).1 hz
    have ha' : a.e = halfMu.objMk k.1 k.2 := ha
    have hb' : halfMu.act a.φ a.e a.2 = halfMu.objMk k'.1 k'.2 := hb
    have e := congrArg toPair hb'
    rw [toPair_act, ha', toPair_objMk, toPair_objMk] at e
    exact (GroupoidStr.π_eq_π_iff _).2 ⟨(a.φ.1, k), rfl, e⟩
  · induction z using Quotient.inductionOn with | h e => ?_
    exact ⟨(GroupoidStr.translation ℤˣ K).π (toPair e), rfl⟩

/-- `|ℤ/2 ⋉ K| ≃ |E_μ|`. -/
def orbitEquiv : (GroupoidStr.translation ℤˣ K).OrbitSpace ≃ halfMu.groupoid.OrbitSpace :=
  Equiv.ofBijective _ kFunctor_orbitMap_bijective

/-- **The topology `T` on `|E_μ|`**: the one making `|ℤ/2 ⋉ K| ≃ |E_μ|` a homeomorphism. -/
instance halfTopE : TopologicalSpace halfMu.groupoid.OrbitSpace :=
  TopologicalSpace.coinduced kFunctor.orbitMap inferInstance

/-- `|ℤ/2 ⋉ K| ≃ₜ |E_μ|`. -/
def orbitHomeomorph :
    (GroupoidStr.translation ℤˣ K).OrbitSpace ≃ₜ halfMu.groupoid.OrbitSpace where
  toEquiv := orbitEquiv
  continuous_toFun := continuous_coinduced_rng
  continuous_invFun := continuous_coinduced_dom.2
    (continuous_id.congr fun x => (orbitEquiv.symm_apply_apply x).symm)

/-- **`g ∗ · : K → K` is a strong bundle map of `H × ℝ → H` covering `g ∗ ·`.** -/
theorem isStrongBundleMap_smulK (g : ℤˣ) :
    (bundle 1 1).IsStrongBundleMap (bundle 1 1) (fun x : H 1 => g • x) (fun k : K => g • k) :=
  isStrongBundleMap_halfProdMap (contDiff_reflPm g) (reflPm_mem g)
    (ContinuousLinearMap.id ℝ (Fin 1 → ℝ))

theorem isScSmoothMap_smulK (g : ℤˣ) :
    (bundle 1 1).toMPolyfold0.IsScSmoothMap (bundle 1 1).toMPolyfold0 fun k : K => g • k :=
  (isStrongBundleMap_smulK g).isScSmoothMap

instance metrizable_orbitK : MetrizableSpace (GroupoidStr.translation ℤˣ K).OrbitSpace :=
  metrizableSpace_translation_orbitSpace isScSmoothMap_smulK

instance halfMetrizableE : MetrizableSpace halfMu.groupoid.OrbitSpace :=
  orbitHomeomorph.symm.isEmbedding.metrizableSpace

theorem continuous_πK : Continuous (GroupoidStr.translation ℤˣ K).π := continuous_quot_mk

theorem continuous_orbitProj : Continuous halfMu.proj.orbitMap := by
  refine continuous_coinduced_dom.2 (continuous_coinduced_dom.2 ?_)
  exact (continuous_quot_mk.comp continuous_fst :
    Continuous fun k : K => halfC.toGroupoidStr.π k.1)

theorem surjective_πE : Surjective (kFunctor.orbitMap ∘ (GroupoidStr.translation ℤˣ K).π) :=
  kFunctor_orbitMap_bijective.2.comp (GroupoidStr.surjective_π _)

theorem isOpenMap_orbitProj : IsOpenMap halfMu.proj.orbitMap := by
  intro U hU
  have hU' : IsOpen ((kFunctor.orbitMap ∘ (GroupoidStr.translation ℤˣ K).π) ⁻¹' U) :=
    hU.preimage (orbitHomeomorph.continuous.comp continuous_πK)
  have he : halfMu.proj.orbitMap '' U = (halfC.toGroupoidStr.π ∘ Prod.fst) ''
      ((kFunctor.orbitMap ∘ (GroupoidStr.translation ℤˣ K).π) ⁻¹' U) := by
    conv_lhs => rw [← image_preimage_eq U surjective_πE]
    rw [image_image]
    rfl
  rw [he]
  exact (GroupoidStr.isOpenMap_π_translation continuous_halfSmul).comp isOpenMap_fst _ hU'

/-- **The vector bundle GCT `P : E → ℤ/2 ⋉ H`** (Definition 17.7.1): `μ(x) = ℝ`, `μ(g, x) = 1`,
with the topology of `|E_μ| ≅ |ℤ/2 ⋉ (H × ℝ)|`. -/
def halfV : halfC.VectorBundle where
  toBanachFunctor := halfMu
  topE := halfTopE
  metrizableE := halfMetrizableE
  continuous_fiber α := orbitHomeomorph.continuous.comp
    (continuous_πK.comp (continuous_const.prodMk continuous_id))
  surjective_orbitProj z := by
    induction z using Quotient.inductionOn with | h x => ?_
    exact ⟨halfMu.groupoid.π (halfMu.objMk x 0), rfl⟩
  continuous_orbitProj := continuous_orbitProj
  isOpenMap_orbitProj := isOpenMap_orbitProj

instance topE_halfV : TopologicalSpace halfV.groupoid.OrbitSpace := halfV.topE

/-! ### The strong bundle uniformizer and the strong polyfold bundle construction -/

/-- The fibre `{x} × ℝ ≅ ℝ`, as a topological linear isomorphism. -/
def fibCLE (x : H 1) : proj 1 1 ⁻¹' {x} ≃L[ℝ] (Fin 1 → ℝ) :=
  { toLinearEquiv := (fibEquiv (m := 1) (k := 1) x).linearEquiv ℝ
    continuous_toFun := continuous_snd.comp continuous_subtype_val
    continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk fun _ => rfl }

@[simp] theorem fibCLE_apply (x : H 1) (w : proj 1 1 ⁻¹' {x}) : fibCLE x w = (w : K).2 := rfl

/-- **The data of the strong bundle uniformizer `Ψ̄ : ℤ/2 ⋉ K → E_μ`** (Definition 17.7.2 (1),
(2)): over the identity uniformizer of `ℤ/2 ⋉ H`, the trivial bundle `K = H × ℝ → H` with the
action `g ∗ (x, v) = (g x, v)` and the fibre maps `(x, v) ↦ v`. -/
def halfUnifData : halfV.StrongBundleUniformizerData where
  base := LocalUniformizer.tautological (basePoly 1) isScSmoothMap_halfSmul
  K := K
  p := proj 1 1
  B := bundle 1 1
  actK := halfActK
  p_smul _ _ := rfl
  isStrongBundleMap_smul := isStrongBundleMap_smulK
  fiber q := fibCLE q
  obj_smul _ _ := rfl

theorem halfUnifData_orbitMap : halfUnifData.functor.orbitMap = orbitHomeomorph := by
  funext z
  induction z using Quotient.inductionOn with | h k => rfl

/-- **Definition 17.7.2**: `Ψ̄ : ℤ/2 ⋉ (H × ℝ) → E_μ`; `|Ψ̄|` is a homeomorphism onto
`|E_μ| = |P|⁻¹(|C|)`. -/
def halfUnif : halfV.StrongBundleUniformizer where
  toStrongBundleUniformizerData := halfUnifData
  isOpenEmbedding_orbitMap := by
    rw [halfUnifData_orbitMap]
    exact orbitHomeomorph.isOpenEmbedding
  range_orbitMap := by
    rw [halfUnifData_orbitMap]
    change range orbitHomeomorph = _
    rw [Homeomorph.range_coe]
    change univ = halfV.proj.orbitMap ⁻¹'
      (LocalUniformizer.tautological (basePoly 1) isScSmoothMap_halfSmul).footprint
    rw [LocalUniformizer.tautological_footprint, preimage_univ]

/-- **Definition 17.7.3**: `F̄(x) = {Ψ̄}` over `halfS`. -/
def halfUC : halfV.StrongBundleUniformizerConstruction halfS where
  F _ := {halfUnif}
  base_mem α Ψ h := by
    rw [mem_singleton_iff.1 h]
    exact mem_singleton _

open StrongBundleUniformizerConstruction StrongBundleUniformizerData

/-- The member `Ψ̄` of `F̄`. -/
abbrev halfΨ : halfUC.Unif := ⟨halfUnif, corner, rfl⟩

theorem unif_eq (Ψ : halfUC.Unif) : Ψ = halfΨ := by
  obtain ⟨Ψ, α, h⟩ := Ψ
  exact Subtype.ext h

/-- The transition M-polyfold `M(Ψ, Ψ)` of the base. -/
abbrev Tr : Type := halfS.Tr (halfUC.baseUnif halfΨ) (halfUC.baseUnif halfΨ)

/-- The sheet `{a | a.mor = (g, ·)}` of `M(Ψ, Ψ)`. -/
def sheet (g : ℤˣ) : Set Tr := {a | a.mor.1 = g}

theorem continuous_mor_fst : Continuous fun a : Tr => a.mor.1 :=
  continuous_fst.comp (twistHomeomorph isScSmoothMap_halfSmul
    (TranslationTwist.refl ℤˣ (H 1))).symm.continuous

theorem isOpen_sheet (g : ℤˣ) : IsOpen (sheet g) :=
  (isOpen_discrete {g}).preimage continuous_mor_fst

theorem tgt_eq_smul_src (a : Tr) :
    (show H 1 from a.tgt) = a.mor.1 • (show H 1 from a.src) := by
  have h1 : a.mor.2 = a.src := a.src_mor
  have h2 : a.mor.1 • a.mor.2 = a.tgt := a.tgt_mor
  rw [← h2, h1]

/-- **`t̄(a, k) = g ∗ k`** for `a = (q, (g, q), g q)`. -/
theorem transT_eq (x : halfUC.TransSpace halfΨ halfΨ) :
    (show K from halfUC.transT halfΨ halfΨ x) = x.1.1.mor.1 • (show K from x.1.2) := by
  have h := obj_transAct (Ψ := halfUnifData) (Ψ' := halfUnifData) x.1.1 x.1.2 x.2
  exact (congrArg toPair h).trans (toPair_act x.1.1.mor (halfUnifData.obj x.1.2) _)

instance paracompactSpace_transSpace :
    ParacompactSpace (pullbackSpace halfΨ.1.p fun a : Tr => a.src) :=
  halfΨ.1.B.paracompactSpace_pullback
    (halfS.transPolyfold (halfUC.baseUnif halfΨ) (halfUC.baseUnif halfΨ)) _

/-- `g ∗ pr₂ : s*K → K`, a strong bundle map covering `g ∗ s`. -/
theorem isStrongBundleMap_smul_pullbackProj' (g : ℤˣ) :
    (halfUC.transBundle halfΨ halfΨ).IsStrongBundleMap halfΨ.1.B
      ((fun x : H 1 => g • x) ∘ fun a : Tr => a.src)
      ((fun k : K => g • k) ∘ pullbackProj' halfΨ.1.p fun a : Tr => a.src) :=
  (isStrongBundleMap_smulK g).comp
    (halfΨ.1.B.isStrongBundleMap_pullbackProj' (halfUC.isScSmoothMap_trSrc halfΨ halfΨ))

theorem transT_eqOn_sheet (g : ℤˣ) :
    EqOn (halfUC.transT halfΨ halfΨ)
      ((fun k : K => g • k) ∘ pullbackProj' halfΨ.1.p fun a : Tr => a.src)
      (pullbackProj halfΨ.1.p (fun a : Tr => a.src) ⁻¹' sheet g) := by
  intro x hx
  have hx' : x.1.1.mor.1 = g := hx
  refine (transT_eq x).trans ?_
  rw [hx']
  rfl

/-- **`t̄ : M(Ψ̄, Ψ̄) → K` is a strong bundle map covering `t`** (Definition 17.7.4). -/
theorem isStrongBundleMap_transT :
    (halfUC.transBundle halfΨ halfΨ).IsStrongBundleMap halfΨ.1.B (fun a => a.tgt)
      (halfUC.transT halfΨ halfΨ) :=
  StrongBundle.isStrongBundleMap_of_locally_eqOn (fun x => p_transAct x.1.1 x.1.2 x.2)
    fun a => ⟨sheet a.mor.1, isOpen_sheet _, rfl, _, _,
      isStrongBundleMap_smul_pullbackProj' a.mor.1, transT_eqOn_sheet a.mor.1⟩

/-- `g ∗ · : K → K` is a strong bundle isomorphism over `H`. -/
theorem isStrongBundleIsoOn_smul (g : ℤˣ) :
    (bundle 1 1).IsStrongBundleIsoOn (bundle 1 1) (isStrongBundleMap_smulK g) univ univ :=
  StrongBundle.isStrongBundleIsoOn_univ_of_inverse (isStrongBundleMap_smulK g)
    (isStrongBundleMap_smulK g⁻¹) (isScSmoothMap_halfSmul g) (isScSmoothMap_halfSmul g⁻¹)
    (fun x => inv_smul_smul g x) (fun x => smul_inv_smul g x) (fun y => inv_smul_smul g y)
    (fun y => smul_inv_smul g y)

theorem isScDiffeoOn_halfSmul (g : ℤˣ) :
    (basePoly 1).IsScDiffeoOn (basePoly 1) (fun x : H 1 => g • x) (fun x => g⁻¹ • x) univ univ :=
  ⟨isScSmoothMap_halfSmul g, isScSmoothMap_halfSmul g⁻¹, mapsTo_univ _ _, mapsTo_univ _ _,
    fun x _ => inv_smul_smul g x, fun x _ => smul_inv_smul g x⟩

/-- **`t̄` is a local strong bundle isomorphism** (Definition 17.7.4): over `W ∩ sheet g`, where
`s` is an sc-diffeomorphism, `t̄ = (g ∗ ·) ∘ s̄`. -/
theorem isLocalStrongBundleIso_transT (a : Tr) :
    ∃ (W : Set Tr) (W' : Set (H 1)), a ∈ W ∧
      (halfUC.transBundle halfΨ halfΨ).IsStrongBundleIsoOn halfΨ.1.B isStrongBundleMap_transT
        W W' := by
  obtain ⟨W, W', σ, ha, hd⟩ := halfS.isLocalScDiffeo_trSrc
    (halfUC.baseUnif halfΨ) (halfUC.baseUnif halfΨ) a
  have hW₀ : IsOpen (W ∩ sheet a.mor.1) := hd.isOpen_source.inter (isOpen_sheet _)
  have hd₀ := hd.restrict hW₀ inter_subset_left
  have hi₁ := halfΨ.1.B.isStrongBundleIsoOn_pullbackProj'
    (halfUC.isScSmoothMap_trSrc halfΨ halfΨ) hd₀ a
  have hi₂ := (isStrongBundleIsoOn_smul a.mor.1).restrict (isScDiffeoOn_halfSmul a.mor.1)
    hd₀.isOpen_target (subset_univ _)
  refine ⟨W ∩ sheet a.mor.1, _, ⟨ha, rfl⟩,
    StrongBundle.isStrongBundleIsoOn_of_eqOn (hi₂.comp hi₁) ?_ ?_⟩
  · intro a' ha'
    have h' : a'.mor.1 = a.mor.1 := ha'.2
    refine Eq.trans ?_ (tgt_eq_smul_src a').symm
    rw [h']
    rfl
  · exact fun x hx => (transT_eqOn_sheet a.mor.1 (show x.1.1.mor.1 = a.mor.1 from hx.2)).symm

/-- **The strong polyfold bundle construction over `ℤ/2 ⋉ H`** (Definition 17.7.4): `F̄(x) = {Ψ̄}`
with the pull-back structures `s*K` on `M(Ψ̄, Ψ̄)`; `t̄(a, k) = g ∗ k`. -/
def halfQ : halfV.StrongPolyfoldBundleConstruction halfS where
  toStrongBundleUniformizerConstruction := halfUC
  isStrongBundleMap_trans Ψ Ψ' := by
    obtain rfl := unif_eq Ψ
    obtain rfl := unif_eq Ψ'
    exact isStrongBundleMap_transT
  isLocalStrongBundleIso_trans Ψ Ψ' a := by
    obtain rfl := unif_eq Ψ
    obtain rfl := unif_eq Ψ'
    exact isLocalStrongBundleIso_transT a

theorem halfΨ_footprint : (halfQ.baseUnif halfΨ).1.footprint = univ :=
  LocalUniformizer.tautological_footprint _

/-- **One copy of `Ψ̄`**, a covering family indexed by `Unit`. -/
def halfSingle : halfQ.BundleCoveringFamily where
  ι := Unit
  Ψ _ := halfΨ
  cover := eq_univ_of_forall fun z => mem_iUnion.2 ⟨(), by
    change z ∈ (halfQ.baseUnif halfΨ).1.footprint
    rw [halfΨ_footprint]
    exact mem_univ z⟩

/-! ### The boundary and the isotropy -/

/-- **`∂C = {(0, y)}`** (Definition 17.1.30): `d_C(α) = d_H(α)` through the identity
uniformizer, and `∂H = {a = 0}` (Corollary 2.4.13). -/
theorem mem_boundarySet_iff (α : H 1) : α ∈ halfS.boundarySet ↔ (α : Pm 1).1 0 = 0 := by
  change 1 ≤ halfS.degIndex α ↔ _
  rw [halfS.definition_17_1_30 (α := α)
    (Ψ := LocalUniformizer.tautological (basePoly 1) isScSmoothMap_halfSmul) rfl (q := α) rfl]
  exact mem_boundary_halfSEP_iff 1 1 α

/-- **`∂C ≠ ∅`**: the corner `(0, 0)` lies in `∂C`. -/
theorem corner_mem_boundarySet : corner ∈ halfS.boundarySet :=
  (mem_boundarySet_iff corner).2 rfl

/-- **Non-trivial isotropy on the boundary**: the corner `(0, 0) ∈ ∂C` has the automorphism
`(−1, (0, 0)) ≠ 1`. -/
theorem exists_ne_unit_corner :
    ∃ φ ∈ halfC.toGroupoidStr.mor corner corner, φ ≠ halfC.toGroupoidStr.unit corner :=
  ⟨((-1 : ℤˣ), corner), ⟨rfl, Subtype.ext (Prod.ext rfl (smul_zero _))⟩,
    fun h => absurd (congrArg Prod.fst h) (by decide)⟩

/-- Every point `(a, 0)` is fixed by `−1`. -/
theorem neg_one_smul_of_snd_eq_zero {x : H 1} (hx : (x : Pm 1).2 = 0) : (-1 : ℤˣ) • x = x :=
  Subtype.ext (Prod.ext rfl (by rw [smul_val, hx, smul_zero]))

end GCT.VectorBundle.HalfSpaceReflection

end Polyfold
