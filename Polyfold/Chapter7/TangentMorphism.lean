import Polyfold.Chapter9.Tangent

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §7.1, Definition 7.1.4
and the paragraph before it, p. 289 (2017: Definition 7.4, p. 227): the tangent `Tφ` of a
morphism.

# The tangent `Tφ : T_xX → T_yX` of a morphism

## The text, paraphrased

(2021 p. 289) For a morphism `φ : x → y` there are open neighbourhoods `𝐔(φ)`, `U(x)`, `U(y)` with
`s : 𝐔(φ) → U(x)`, `t : 𝐔(φ) → U(y)` sc-diffeomorphisms, and `φ̂ = t ∘ (s|𝐔(φ))⁻¹`.  For smooth
`φ` there is an associated sc-isomorphism `Tφ : T_{s(φ)}X → T_{t(φ)}X`, `Tφ := Tφ̂(x)`.  `Tφ` can
be defined for `φ` on level at least `1` and is then a bounded linear isomorphism on level `0`;
only for smooth `φ` is it an sc-operator.  (Definition 7.1.4) A smooth morphism `φ` has the
associated local sc-diffeomorphism `φ̂` and its tangent `Tφ`.  The linear structure of `T_xX` is
that of Part I, Definition 2.3.14 (2021 p. 39): `T_xX` is a vector space through one chart
`(V, ϕ, (O, C, E))`, the chart tangent map `Tϕ : T_xV → T_{ϕ(x)}O` being a linear isomorphism,
and `T_xX` inherits the Banach space structure of `T_{ϕ(x)}O ⊆ E`.

## What is formalized (namespace `Polyfold.EpGroupoid`)

`Tφ` is Chapter 7's `tangentMor φ` (`Tt ∘ (Ts|T_φ𝐗)⁻¹`).  Already in the project: well defined and
`Tφ(Ts h) = Tt h`, `T(ψ ∘ φ) = Tψ ∘ Tφ` (Chapter 8, `tangentMor_tSrc`, `tangentMor_comp`);
`Tφ` maps `T_{s(φ)}X` into `T_{t(φ)}X`, `T(1_x) = id`, `T(φ⁻¹) ∘ Tφ = id`, `Tφ` injective and
**`Tφ = Tφ̂(s(φ))`** (Chapter 9, `levelVal_tangentProj_tangentMor`, `tangentMor_unit_of_eq`,
`tangentMor_inv_tangentMor`, `tangentMor_injOn`, `tangentMor_eq_tangentMapOn_hat`).  Added here:

* `tangentFiberAt x` (`T_xX`, the vectors with base point `x`), `inv_mem_levelSet_one`.
* `invOn_tangentMor`: `T(φ⁻¹)` is a two-sided inverse of `Tφ` between `T_{s(φ)}X` and
  `T_{t(φ)}X`; **`bijOn_tangentMor`**: `Tφ` is a bijection `T_{s(φ)}X → T_{t(φ)}X` for `φ ∈ 𝐗₁`.
* `retractTangentMap_eq_clm` (namespace `Polyfold`): every tangent map between retracts acts on
  the fibre over a point by a continuous linear map `E → E'`.
* `MPolyfold.tangentChartMap_fiber`, `MPolyfold.exists_tangentChartMap_eq`: for a chart `χ`
  around `x ∈ X₁`, `Tχ` maps `T_xX` onto `{χ(x)} × T_{χ(x)}O`; `MPolyfold.chart_invOn`: mutually
  inverse fibre maps represented in charts by linear maps give mutually inverse linear maps
  between the tangent spaces of the retracts.
* **`tangentMor_chart`**: in charts `χ` around `s(φ)` and `ψ` around `t(φ)`, `Tφ` is a continuous
  linear map `L : E → E'` on the fibres.
* **`tangentMor_chart_iso`**: `L` maps `T_{χ(s φ)}O` bijectively onto `T_{ψ(t φ)}O'`, with inverse
  the restriction of the continuous linear map `L'` representing `T(φ⁻¹)`.  This is the text's
  "bounded linear isomorphism on level `0`" in the linear structure of Definition 2.3.14.
* `definition_7_1_4`: the bundle of these statements.

## What the text leaves implicit, and the choices made

* **The linear structure of `T_xX` is not in the project** (Part I's `T_xX` is a set of classes,
  `MPolyfold.tangentFiber`, with no vector space instance: gap G.7).  The text defines it through
  one chart, as the structure transported by `Tϕ : T_xV → T_{ϕ(x)}O`; that it does not depend on
  the chart is the linearity of the transition maps, which the text leaves implicit.  The
  linearity of `Tφ` is therefore stated as the text defines it, in charts: for every chart `χ`
  around `s(φ)` and `ψ` around `t(φ)`, `Tψ ∘ Tφ ∘ (Tχ)⁻¹` is the restriction of a continuous linear
  map, with a continuous linear inverse on the tangent spaces of the retracts.  As the charts are
  arbitrary, this holds for whichever chart is used to define the linear structures.
* `Tφ` is stated for `φ ∈ 𝐗₁`, as the text allows ("defined for `φ` on level at least `1`").
* The text's `Tφ := Tφ̂(x)` depends on the choice of `𝐔(φ)`; Chapter 9's
  `tangentMor_eq_tangentMapOn_hat` shows that for the chosen sheet it agrees with
  `Tt ∘ (Ts|T_φ𝐗)⁻¹`, which involves no choice.
* **Not formalized**: that `Tφ` is an sc-operator (an sc-isomorphism) for smooth `φ`, which needs
  the sc-structure of `T_xX` at smooth `x` (gap G.7 again), and the restatement of the facts (3),
  (4) on sub-M-polyfolds after Definition 7.1.21 (row V7.30), which concern the linear structure of
  `T_aA ⊆ T_aX` and are proved in a chart in Part I (`Polyfold.proposition_2_3_19_three`,
  `Polyfold.proposition_2_3_19_four`).
-/

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

/-! ### Tangent maps of retracts are linear on fibres -/

/-- Every tangent map `Tf` between retracts (Part I's `retractTangentMap`) acts on the fibre over a
point `a ∈ E₁` by a continuous linear map `E → E'`: `Tf(a, h) = (g(a), L(a) h)`. -/
theorem retractTangentMap_eq_clm {E E' : ScBanach} (C O : Set (E 0)) (f : E 0 → E' 0) :
    ∃ (g : E 1 → E' 1) (L : E 1 → E 0 →L[ℝ] E' 0),
      ∀ p : E.tangent 0, retractTangentMap E C O f p = (g p.1, L p.1 p.2) := by
  unfold retractTangentMap
  split_ifs with h
  · exact ⟨_, _, fun p => rfl⟩
  · exact ⟨0, 0, fun p => rfl⟩

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- For a chart `χ` around `x`, `Tχ` maps `T_xX` into `{χ(x)} × T_{χ(x)}O`. -/
theorem tangentChartMap_fiber {χ : MChart X} (hχ : P.IsChart χ) {x : X} (hx : x ∈ χ.source)
    {α : P.TangentSpace} (hα : P.levelVal 1 (P.tangentProj α) = x) :
    (tangentChartMap hχ α).1 = levelLift χ 1 x ∧
      (tangentChartMap hχ α).2 ∈
        Polyfold.tangentSpace χ.model.E χ.model.C χ.model.O (levelLift χ 1 x) := by
  have hαχ : α ∈ tangentChartSet χ := by
    change P.levelVal 1 (P.tangentProj α) ∈ χ.source
    rw [hα]; exact hx
  have h1 : (tangentChartMap hχ α).1 = levelLift χ 1 x := by
    rw [tangentChartMap_fst hχ hαχ, hα]
  refine ⟨h1, ?_⟩
  show ((levelLift χ 1 x, (tangentChartMap hχ α).2) : χ.model.E.tangent 0) ∈
    retractTangent χ.model.E χ.model.C χ.model.O
  rw [← h1]
  exact tangentChartMap_mem hχ hαχ

/-- For a chart `χ` around `x ∈ X₁`, `Tχ` maps `T_xX` onto `{χ(x)} × T_{χ(x)}O`. -/
theorem exists_tangentChartMap_eq {χ : MChart X} (hχ : P.IsChart χ) {x : X} (hx : x ∈ χ.source)
    (hx1 : x ∈ P.levelSet 1) {v : χ.model.E 0}
    (hv : v ∈ Polyfold.tangentSpace χ.model.E χ.model.C χ.model.O (levelLift χ 1 x)) :
    ∃ α : P.TangentSpace, P.levelVal 1 (P.tangentProj α) = x ∧
      tangentChartMap hχ α = (levelLift χ 1 x, v) := by
  refine ⟨TangentSpace.mk (TangentPre.ofVec hχ hv), ?_, tangentChartMap_mk_ofVec hχ hv⟩
  change χ.symm (χ.model.E.toBase 1 (levelLift χ 1 x)) = x
  rw [P.toBase_levelLift hχ hx hx1, χ.symm_apply_apply hx]

/-- If maps `F : T_xX → T_yX` and `G : T_yX → T_xX` are mutually inverse and are represented in
charts `χ` around `x`, `ψ` around `y` by linear maps `L`, `L'` on the fibres, then `L` and `L'`
restrict to mutually inverse maps `T_{χ(x)}O ⇄ T_{ψ(y)}O'`. -/
theorem chart_invOn {F G : P.TangentSpace → P.TangentSpace} {x y : X} {χ ψ : MChart X}
    (hχ : P.IsChart χ) (hψ : P.IsChart ψ) (hx : x ∈ χ.source) (hx1 : x ∈ P.levelSet 1)
    (hy : y ∈ ψ.source) (hy1 : y ∈ P.levelSet 1)
    (hF : ∀ a, P.levelVal 1 (P.tangentProj a) = x → P.levelVal 1 (P.tangentProj (F a)) = y)
    (hG : ∀ b, P.levelVal 1 (P.tangentProj b) = y → P.levelVal 1 (P.tangentProj (G b)) = x)
    (hGF : ∀ a, P.levelVal 1 (P.tangentProj a) = x → G (F a) = a)
    (hFG : ∀ b, P.levelVal 1 (P.tangentProj b) = y → F (G b) = b)
    (L : χ.model.E 0 →L[ℝ] ψ.model.E 0) (L' : ψ.model.E 0 →L[ℝ] χ.model.E 0)
    (hL : ∀ a, P.levelVal 1 (P.tangentProj a) = x →
      tangentChartMap hψ (F a) = (levelLift ψ 1 y, L (tangentChartMap hχ a).2))
    (hL' : ∀ b, P.levelVal 1 (P.tangentProj b) = y →
      tangentChartMap hχ (G b) = (levelLift χ 1 x, L' (tangentChartMap hψ b).2)) :
    MapsTo L (Polyfold.tangentSpace χ.model.E χ.model.C χ.model.O (levelLift χ 1 x))
        (Polyfold.tangentSpace ψ.model.E ψ.model.C ψ.model.O (levelLift ψ 1 y)) ∧
      MapsTo L' (Polyfold.tangentSpace ψ.model.E ψ.model.C ψ.model.O (levelLift ψ 1 y))
        (Polyfold.tangentSpace χ.model.E χ.model.C χ.model.O (levelLift χ 1 x)) ∧
      InvOn L' L (Polyfold.tangentSpace χ.model.E χ.model.C χ.model.O (levelLift χ 1 x))
        (Polyfold.tangentSpace ψ.model.E ψ.model.C ψ.model.O (levelLift ψ 1 y)) := by
  refine ⟨fun v hv => ?_, fun w hw => ?_, fun v hv => ?_, fun w hw => ?_⟩
  · obtain ⟨α, hα, hαv⟩ := exists_tangentChartMap_eq hχ hx hx1 hv
    have h := (tangentChartMap_fiber hψ hy (hF α hα)).2
    rwa [hL α hα, hαv] at h
  · obtain ⟨β, hβ, hβw⟩ := exists_tangentChartMap_eq hψ hy hy1 hw
    have h := (tangentChartMap_fiber hχ hx (hG β hβ)).2
    rwa [hL' β hβ, hβw] at h
  · obtain ⟨α, hα, hαv⟩ := exists_tangentChartMap_eq hχ hx hx1 hv
    have h := hL' (F α) (hF α hα)
    rw [hGF α hα, hL α hα, hαv] at h
    exact (congrArg Prod.snd h).symm
  · obtain ⟨β, hβ, hβw⟩ := exists_tangentChartMap_eq hψ hy hy1 hw
    have h := hL (G β) (hG β hβ)
    rw [hFG β hβ, hL' β hβ, hβw] at h
    exact (congrArg Prod.snd h).symm

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### `Tφ` is a bijection `T_{s(φ)}X → T_{t(φ)}X` -/

/-- `T_xX`: the tangent vectors of `X` with base point `x` (empty unless `x ∈ X₁`). -/
def tangentFiberAt (x : Obj) : Set X.PObj.TangentSpace :=
  {a | X.PObj.levelVal 1 (X.PObj.tangentProj a) = x}

theorem mem_tangentFiberAt {x : Obj} {a : X.PObj.TangentSpace} :
    a ∈ X.tangentFiberAt x ↔ X.PObj.levelVal 1 (X.PObj.tangentProj a) = x := Iff.rfl

/-- `φ ∈ 𝐗₁ ⟹ φ⁻¹ ∈ 𝐗₁`. -/
theorem inv_mem_levelSet_one {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) :
    X.inv φ ∈ X.PMor.levelSet 1 := by
  rw [← X.mem_levelSet_src_iff, X.src_inv, X.mem_levelSet_tgt_iff]
  exact hφ

/-- `T(φ⁻¹)` is a two-sided inverse of `Tφ` between `T_{s(φ)}X` and `T_{t(φ)}X`, for `φ ∈ 𝐗₁`. -/
theorem invOn_tangentMor {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) :
    InvOn (X.tangentMor (X.inv φ)) (X.tangentMor φ) (X.tangentFiberAt (X.src φ))
      (X.tangentFiberAt (X.tgt φ)) := by
  refine ⟨fun a ha => X.tangentMor_inv_tangentMor hφ ha, fun b hb => ?_⟩
  have hb' : X.PObj.levelVal 1 (X.PObj.tangentProj b) = X.src (X.inv φ) := by
    rw [X.src_inv]; exact hb
  have h := X.tangentMor_inv_tangentMor (X.inv_mem_levelSet_one hφ) hb'
  rwa [X.inv_inv] at h

/-- `T(φ⁻¹)` maps `T_{t(φ)}X` into `T_{s(φ)}X`, for `φ ∈ 𝐗₁`. -/
theorem tangentMor_inv_mapsTo {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) :
    MapsTo (X.tangentMor (X.inv φ)) (X.tangentFiberAt (X.tgt φ)) (X.tangentFiberAt (X.src φ)) :=
  fun b hb => by
    have h := X.levelVal_tangentProj_tangentMor (X.inv_mem_levelSet_one hφ)
      (show X.PObj.levelVal 1 (X.PObj.tangentProj b) = X.src (X.inv φ) by
        rw [X.src_inv]; exact hb)
    rwa [X.tgt_inv] at h

/-- **2021 p. 289 (2017 p. 227), gap G.70**: for `φ ∈ 𝐗₁`, `Tφ` is a bijection
`T_{s(φ)}X → T_{t(φ)}X`, with inverse `T(φ⁻¹)`. -/
theorem bijOn_tangentMor {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) :
    BijOn (X.tangentMor φ) (X.tangentFiberAt (X.src φ)) (X.tangentFiberAt (X.tgt φ)) :=
  (X.invOn_tangentMor hφ).bijOn (fun _ ha => X.levelVal_tangentProj_tangentMor hφ ha)
    (X.tangentMor_inv_mapsTo hφ)

/-! ### `Tφ` is a bounded linear isomorphism on level `0`, in charts -/

/-- **`Tφ` is linear in charts**: for `φ ∈ 𝐗₁` and charts `χ` around `s(φ)`, `ψ` around `t(φ)`,
there is a continuous linear `L : E → E'` with `Tψ(Tφ(a)) = (ψ(t φ), L(Tχ(a)))` for
`a ∈ T_{s(φ)}X`. -/
theorem tangentMor_chart {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) {χ ψ : MChart Obj}
    (hχ : X.PObj.IsChart χ) (hψ : X.PObj.IsChart ψ) (hx : X.src φ ∈ χ.source)
    (hy : X.tgt φ ∈ ψ.source) :
    ∃ L : χ.model.E 0 →L[ℝ] ψ.model.E 0, ∀ a ∈ X.tangentFiberAt (X.src φ),
      MPolyfold.tangentChartMap hψ (X.tangentMor φ a) =
        (MPolyfold.levelLift ψ 1 (X.tgt φ), L (MPolyfold.tangentChartMap hχ a).2) := by
  have hf := (X.isScDiffeoOn_hat φ).isScSmoothOn
  obtain ⟨g, L, hL⟩ := retractTangentMap_eq_clm χ.model.C
    (χ '' MPolyfold.TangentPre.fdomOn (X.sheetAt φ).srcSet χ (X.hat φ) ψ)
    (ψ ∘ X.hat φ ∘ χ.symm)
  refine ⟨L (MPolyfold.levelLift χ 1 (X.src φ)), fun a ha => ?_⟩
  have ha' : X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src φ := ha
  have hβ : X.PObj.levelVal 1 (X.PObj.tangentProj (X.tangentMor φ a)) = X.tgt φ :=
    X.levelVal_tangentProj_tangentMor hφ ha'
  have hmem : a ∈ X.PObj.tangentPreimage
      (MPolyfold.TangentPre.fdomOn (X.sheetAt φ).srcSet χ (X.hat φ) ψ) := by
    rw [MPolyfold.mem_tangentPreimage, ha']
    refine ⟨⟨X.src_mem_sheetAt φ, hx⟩, ?_⟩
    change X.hat φ (X.src φ) ∈ ψ.source
    rw [X.hat_src]; exact hy
  refine Prod.ext ?_ ?_
  · exact (MPolyfold.tangentChartMap_fiber hψ hy hβ).1
  · rw [X.tangentMor_eq_tangentMapOn_hat hφ ha',
      MPolyfold.tangentChartMap_tangentMapOn hf hχ hψ hmem, hL,
      (MPolyfold.tangentChartMap_fiber hχ hx ha').1]

/-- **2021 p. 289 (2017 p. 227), gap G.70: `Tφ` is a bounded linear isomorphism on level `0`**,
in the linear structure of Part I's Definition 2.3.14 (read in charts): for `φ ∈ 𝐗₁` and charts
`χ` around `x = s(φ)`, `ψ` around `y = t(φ)`, `Tφ` and `T(φ⁻¹)` are represented on the fibres by
continuous linear maps `L : E → E'`, `L' : E' → E`, which restrict to mutually inverse maps
`T_{χ(x)}O ⇄ T_{ψ(y)}O'`. -/
theorem tangentMor_chart_iso {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) {χ ψ : MChart Obj}
    (hχ : X.PObj.IsChart χ) (hψ : X.PObj.IsChart ψ) (hx : X.src φ ∈ χ.source)
    (hy : X.tgt φ ∈ ψ.source) :
    ∃ (L : χ.model.E 0 →L[ℝ] ψ.model.E 0) (L' : ψ.model.E 0 →L[ℝ] χ.model.E 0),
      (∀ a ∈ X.tangentFiberAt (X.src φ),
        MPolyfold.tangentChartMap hψ (X.tangentMor φ a) =
          (MPolyfold.levelLift ψ 1 (X.tgt φ), L (MPolyfold.tangentChartMap hχ a).2)) ∧
      (∀ b ∈ X.tangentFiberAt (X.tgt φ),
        MPolyfold.tangentChartMap hχ (X.tangentMor (X.inv φ) b) =
          (MPolyfold.levelLift χ 1 (X.src φ), L' (MPolyfold.tangentChartMap hψ b).2)) ∧
      MapsTo L
        (Polyfold.tangentSpace χ.model.E χ.model.C χ.model.O (MPolyfold.levelLift χ 1 (X.src φ)))
        (Polyfold.tangentSpace ψ.model.E ψ.model.C ψ.model.O (MPolyfold.levelLift ψ 1 (X.tgt φ))) ∧
      MapsTo L'
        (Polyfold.tangentSpace ψ.model.E ψ.model.C ψ.model.O (MPolyfold.levelLift ψ 1 (X.tgt φ)))
        (Polyfold.tangentSpace χ.model.E χ.model.C χ.model.O (MPolyfold.levelLift χ 1 (X.src φ))) ∧
      InvOn L' L
        (Polyfold.tangentSpace χ.model.E χ.model.C χ.model.O (MPolyfold.levelLift χ 1 (X.src φ)))
        (Polyfold.tangentSpace ψ.model.E ψ.model.C ψ.model.O
          (MPolyfold.levelLift ψ 1 (X.tgt φ))) := by
  obtain ⟨L, hL⟩ := X.tangentMor_chart hφ hχ hψ hx hy
  obtain ⟨L', hL'⟩ := X.tangentMor_chart (X.inv_mem_levelSet_one hφ) hψ hχ
    (by rw [X.src_inv]; exact hy) (by rw [X.tgt_inv]; exact hx)
  rw [X.src_inv, X.tgt_inv] at hL'
  have hx1 : X.src φ ∈ X.PObj.levelSet 1 := (X.mem_levelSet_src_iff φ 1).2 hφ
  have hy1 : X.tgt φ ∈ X.PObj.levelSet 1 := (X.mem_levelSet_tgt_iff φ 1).2 hφ
  have hinv := X.invOn_tangentMor hφ
  obtain ⟨h1, h2, h3⟩ := MPolyfold.chart_invOn hχ hψ hx hx1 hy hy1
    (fun a ha => X.levelVal_tangentProj_tangentMor hφ ha)
    (fun b hb => X.tangentMor_inv_mapsTo hφ hb)
    (fun a ha => hinv.1 ha) (fun b hb => hinv.2 hb) L L' hL hL'
  exact ⟨L, L', hL, hL', h1, h2, h3⟩

/-- **2021 Definition 7.1.4 and the paragraph before it, p. 289 (2017: Definition 7.4, p. 227)**:
for `φ ∈ 𝐗₁`, `φ̂(s φ) = t φ`; `Tφ = Tφ̂(s(φ))` on `T_{s(φ)}X`; `Tφ` is a bijection
`T_{s(φ)}X → T_{t(φ)}X` with inverse `T(φ⁻¹)`; `T(ψ ∘ φ) = Tψ ∘ Tφ`; and in any charts `Tφ` is a
bounded linear isomorphism `T_{χ(s φ)}O → T_{ψ(t φ)}O'` (`tangentMor_chart_iso`). -/
theorem definition_7_1_4 {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) :
    X.hat φ (X.src φ) = X.tgt φ ∧
      (∀ a ∈ X.tangentFiberAt (X.src φ),
        MPolyfold.tangentMapOn (X.isScDiffeoOn_hat φ).isScSmoothOn a = X.tangentMor φ a) ∧
      BijOn (X.tangentMor φ) (X.tangentFiberAt (X.src φ)) (X.tangentFiberAt (X.tgt φ)) ∧
      InvOn (X.tangentMor (X.inv φ)) (X.tangentMor φ) (X.tangentFiberAt (X.src φ))
        (X.tangentFiberAt (X.tgt φ)) ∧
      (∀ ψ, X.src ψ = X.tgt φ → ∀ a ∈ X.tangentFiberAt (X.src φ),
        X.tangentMor (X.comp ψ φ) a = X.tangentMor ψ (X.tangentMor φ a)) :=
  ⟨X.hat_src φ, fun _ ha => (X.tangentMor_eq_tangentMapOn_hat hφ ha).symm, X.bijOn_tangentMor hφ,
    X.invOn_tangentMor hφ, fun _ hψφ _ ha => X.tangentMor_comp hφ hψφ ha⟩

end EpGroupoid

end Polyfold
