import Polyfold.Chapter2.TameBoundaryTopology

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, Appendix §2.7.4:
**Theorem 2.7.13 (2)–(4)** and its closing characterization (pp. 83–84), the sc-part of
**Proposition 2.7.12** (p. 83), **Definition 2.7.14** and the iterated boundaries
**(2.45)–(2.47)** (p. 84), all new in the 2021 edition.  The sets `bX`, `U(x, V, θ)`, the maps
`Φ_{(x,V,θ)}`, `B` and the topology `T_{bX}` are those of `Polyfold/Chapter2/TameBoundary.lean`
and `Polyfold/Chapter2/TameBoundaryTopology.lean`.

# The tame M-polyfold structure of the tame boundary `bX`

## The text, paraphrased

(Before Proposition 2.7.12) Where `U(x, V, θ)` and `U(x', V', θ')` meet at `[y, U, σ]`, the face
`σ` sits in `θ` and in `θ'` through open sc-embeddings, so the transition map
`Φ_{(x',V',θ')} ∘ Φ_{(x,V,θ)}⁻¹` is sc-smooth near every point, in both directions.
(Proposition 2.7.12) The two images of `U ∩ U'` are open in `θ`, `θ'` and the transition map is an
sc-diffeomorphism.  (Theorem 2.7.13) For a tame M-polyfold `X`: (2) `(bX, T_{bX})` admits a
natural tame M-polyfold structure; (3) for it `B : bX → X`, `[x, V, θ] ↦ x`, is sc-smooth;
(4) `d_X(B([x, V, θ])) − 1 = d_{bX}([x, V, θ])`.  Topology and structure are characterized by:
every `U(x, V, θ)` is open and every `Φ_{(x,V,θ)}` is a homeomorphism and an sc-diffeomorphism onto
`θ`, the face with the structure induced from `V`.  (Definition 2.7.14) The tame boundary of `X` is
`B : bX → X`, sc-smooth with image `∂X`.  ((2.45)–(2.47)) Iterating, `b⁰X = X`,
`bᵏX = b(bᵏ⁻¹X)`, and `Bᵏ = B_X ∘ B_{bX} ∘ ⋯ ∘ B_{bᵏ⁻¹X}` (`B⁰ = Id`) is sc-smooth with image the
points of degeneracy index at least `k`.

## What is formalized

* Charts of `bX` (`MPolyfold.BChartData`, `BChartData.chart`): for a triple `t = (x, V, θ)` with
  `V` centred at `x`, a tame chart `φ` of `X` and an open `V₁ ⊆ dom φ` on which `θ` is the zero set
  of the coordinate `i` of a tame model `T`, the chart `p ↦ π(φ(B p))` on `U(t) ∩ B⁻¹(V₁)`, with
  values in a tame retract of `[0,∞)ᵏ ⊕ W` (`π`, `ι` the face projection and inclusion of
  Proposition 2.5.15 (preprint Proposition 2.43)).  Transition maps are `π' ∘ (φ' ∘ φ⁻¹) ∘ ι`
  (`BChartData.chart_compatible`);
  the charts cover `bX` (`exists_bChartData`, through `exists_localFace_of_faceIn`).
* **Theorem 2.7.13 (2)**: `MPolyfold.tameBoundaryPolyfold` on `bX` with the topology `T_{bX}`
  (`paracompactSpace_tameBoundarySpace` from Proposition 2.7.16), tame
  (`tameBoundaryPolyfold_isTame`).  **(3)**: `tameBoundaryMap_isScSmooth`.  **(4)**:
  `degIndex_tameBoundaryMap` (`d_X(B p) = d_{bX}(p) + 1`) and, as printed,
  `degIndex_tameBoundaryMap_sub_one`.
* **The characterization**: `isSubMPolyfold_of_isFaceIn` and `facePolyfold` (a face of a
  face-structured open `V` is a sub-M-polyfold of `X`); `phi_isScDiffeoOn` (`Φ_{(x,V,θ)}` is an
  sc-diffeomorphism of `U(x, V, θ)` onto `θ`, `V` centred); `tameBoundaryPolyfold_unique` (every
  M-polyfold structure on `bX` with this property is equivalent to ours), with the satisfiability
  witness `tameBoundaryPolyfold_satisfies`.
* **Proposition 2.7.12**, sc-part: `proposition_2_7_12_scDiffeo_2021` (centred `V`, `V'`).
* `theorem_2_7_13_structure_2021` bundles (2)–(4), the characterization and uniqueness.
* **Definition 2.7.14**: `definition_2_7_14_2021`, `TameMPolyfoldBundle.b`.
  **(2.45)–(2.47)**: `TameMPolyfoldBundle.iter`, `iterMap`, `iterMap_isScSmooth`,
  `degIndex_iterMap` (`d_X(Bᵏ p) = d_{bᵏX}(p) + k`), `range_iterMap`.
* Witnesses: `quadrantPolyfold_bChartData_nonempty` (chart data exist for `[0,∞)ⁿ ⊕ W`, `n ≥ 1`)
  and `quadrantPolyfold_degIndex_tameBoundary` (over the corner `d_{bX} = n − 1`).

## What the text leaves implicit, and the choices made

* "The structure induced from `V`" on `θ` is read as the sub-M-polyfold structure of `θ` in `X`
  (`facePolyfold`); `θ` is a face of the open `V`, and its local faces are found as in
  Theorem 2.5.17 (`exists_localFace_of_faceIn`, `isSubMPolyfold_of_isFaceIn`).
* The characterization and Proposition 2.7.12 are proved for representatives with `V` centred at
  `x`: as we read it, for other representatives `Φ_{(x,V,θ)}` need not be onto `θ`
  (`phi_not_surjective_2021`, `TameBoundaryExample.lean`); every class has a centred
  representative (`TameBoundary.BSpace.exists_centred_rep`).  For every representative, `Φ` is an
  sc-diffeomorphism onto the open part `θ ∩ V^x` of `θ`, and Proposition 2.7.12 holds as printed:
  `Chapter2/TameBoundaryNonCentred.lean` (`phi_isScDiffeoOn_nonCentred_2021`,
  `proposition_2_7_12_scDiffeo_nonCentred_2021`, `tameBoundaryPolyfold_unique_allReps_2021`).
* "Uniquely characterized" is read as: any M-polyfold structure with the stated property has an
  equivalent atlas.
* `bᵏX` needs a bundled tame M-polyfold (`TameMPolyfoldBundle`) so that `b` can be iterated.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace TameBoundary

universe u

variable {X : Type u} [TopologicalSpace X] {d : X → ℕ} (hd : IsCornerIndex d)

/-- Every class `[x, V, θ]` has a representative with `V` centred at `x` (`V^x`, `reach`). -/
theorem BSpace.exists_centred_rep (p : BSpace hd) :
    ∃ t : BTriple hd, t.cls = p ∧ IsCenteredAt d t.x t.V := by
  obtain ⟨s, rfl⟩ := BSpace.exists_rep hd p
  have hV' := reach_mem_faceStructuredNbhdsAt hd s.mem
  obtain ⟨θ', hθ', he⟩ := exists_face_restrict hd s.mem hV'.1.1.1 hV'.2.1 (reach_subset _ _)
    s.mem_faces
  refine ⟨⟨⟨s.x, reach d s.V s.x, hV', s.one_le⟩, θ', hθ'⟩, ?_,
    isCenteredAt_reach hd s.mem.1.1.1 s.mem.2.1⟩
  rw [BTriple.cls_eq_cls]
  exact ⟨rfl, reach d s.V s.x, hV', fun z hz => ⟨hz, reach_subset _ _ hz⟩, θ', hθ',
    faceExt_self hd hV'.1.1.1 hθ'.1, he⟩

variable {hd}

/-- `Φ⁻¹(B(p)) = p` on `U(x, V, θ)`, `V` centred. -/
lemma phiHomeomorph_symm_bMap {t : BTriple hd} (h : IsCenteredAt d t.x t.V) {p : BSpace hd}
    (hp : p ∈ uSet hd t) :
    ((phiHomeomorph hd h).symm ⟨bMap hd p, bMap_mem_of_mem_uSet hd hp⟩ : BSpace hd) = p := by
  have : (phiHomeomorph hd h).symm ⟨bMap hd p, bMap_mem_of_mem_uSet hd hp⟩ = ⟨p, hp⟩ := by
    rw [Homeomorph.symm_apply_eq]; rfl
  rw [this]

lemma bMap_phiHomeomorph_symm {t : BTriple hd} (h : IsCenteredAt d t.x t.V) (y : t.θ) :
    bMap hd ((phiHomeomorph hd h).symm y : BSpace hd) = y := by
  have := (phiHomeomorph hd h).apply_symm_apply y
  exact congrArg Subtype.val this

lemma phiHomeomorph_symm_mem {t : BTriple hd} (h : IsCenteredAt d t.x t.V) (y : t.θ) :
    ((phiHomeomorph hd h).symm y : BSpace hd) ∈ uSet hd t :=
  ((phiHomeomorph hd h).symm y).2

end TameBoundary

namespace MPolyfold

open TameBoundary

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
  (hP : P.IsTame)

/-- A tame chart around `x` whose domain lies in a given open `V ∋ x` (the restriction of a tame
chart; the restricted retraction is tame, `ScRetraction.IsTameWith.restrict`). -/
theorem exists_tame_chart_subset (hP : P.IsTame) {V : Set X} (hV : IsOpen V) {x : X}
    (hx : x ∈ V) :
    ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧ φ.source ⊆ V ∧
      ∃ R : ScRetraction φ.model.E φ.model.C, R.retract = φ.model.O ∧
      ∃ (n : ℕ) (W : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
        φ.model.C = T 0 ⁻¹' quadrant n W 0 ∧ R.IsTameWith T := by
  obtain ⟨φ, hφ, hxφ, R, hRO, hRt⟩ := IsTame.exists_chart P hP x
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hs : φ.source ∩ V ⊆ φ.source := inter_subset_left
  have hso : IsOpen (φ.source ∩ V) := φ.isOpen_source.inter hV
  obtain ⟨W₀, hW₀, hWs⟩ := φ.exists_isOpen_image_eq hs hso
  refine ⟨φ.restrict hs hso, hφ.restrict P hs hso, ⟨hxφ, hx⟩, inter_subset_right,
    R.restrict hW₀, ?_, n, W, T, hT, (hRt n W T hT).restrict hW₀⟩
  have h : (R.restrict hW₀).retract = φ '' (φ.source ∩ V) := by
    rw [R.restrict_retract, hRO, hWs]
  exact h

/-- **The local shape of a face of an open set** (the argument of 2021 Theorem 2.5.17 (preprint
Theorem 2.45), for the open set `V` with the induced structure): let `V` be open, `x` lie in
exactly `d_X(x)` faces of `V`, and `θ` be a face of `V` through `x`.  In a tame chart `φ` around
`x` with domain in `V`, the image `φ(θ ∩ dom φ)` agrees on a ball `B` around `φ(x)` with a face
`F_loc` of the retract `O`. -/
theorem exists_localFace_of_faceIn {V : Set X} {x : X}
    (hVx : (facesThrough P.degIndex V x).encard = P.degIndex x) {θ : Set X}
    (hθ : θ ∈ facesThrough P.degIndex V x)
    {φ : MChart X} (hφ : P.IsChart φ) (hx : x ∈ φ.source) (hsrc : φ.source ⊆ V)
    (R : ScRetraction φ.model.E φ.model.C) (hRO : R.retract = φ.model.O)
    {n : ℕ} {W : ScBanach} {T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)}
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T) :
    ∃ Floc : Set (φ.model.E 0), R.IsRetractFace Floc ∧
      ∃ B : Set (φ.model.E 0), IsOpen B ∧ φ x ∈ B ∧ φ '' (θ ∩ φ.source) ∩ B = Floc ∩ B := by
  classical
  obtain ⟨⟨y₀, -, -, rfl⟩, hxθ⟩ := hθ
  set D := V ∩ {y | P.degIndex y = 1} with hD
  set G := connectedComponentIn D y₀ with hG
  have hxcl : x ∈ closure G := hxθ.2
  have hdeg : ∀ y ∈ φ.source, P.degIndex y = degIndexWith T (φ y) := fun y hy => by
    rw [P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR hy, chartDegIndex,
      degIndex_eq T hT (φ.apply_mem_C hy)]
  set o := φ x with ho
  have hoO' : o ∈ φ.model.O := φ.mapsTo_model x hx
  have hoO : o ∈ R.retract := by rw [hRO]; exact hoO'
  have hsubO : ∀ q, connectedComponentIn R.faceStratum q ⊆ φ.model.O := fun q z hz => by
    rw [← hRO]; exact (connectedComponentIn_subset _ _ hz).1
  have hφc : ContinuousAt φ x := φ.continuousOn_toFun.continuousAt (φ.isOpen_source.mem_nhds hx)
  set J := zeroSet T o with hJ
  -- `J` is nonempty: points of `G` near `x` have `I = {i} ⊆ J`
  have hJne : ∃ i, i ∈ J := by
    obtain ⟨y, ⟨hyV, hysub⟩, hyG⟩ := mem_closure_iff_nhds.1 hxcl _
      ((show ∀ᶠ y in 𝓝 x, y ∈ φ.source from φ.isOpen_source.mem_nhds hx).and
        (hφc.eventually (eventually_zeroSet_subset T o)))
    have hy1 : degIndexWith T (φ y) = 1 :=
      (hdeg y hyV).symm.trans (connectedComponentIn_subset D y₀ hyG).2
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 ((degIndexWith_eq_card_zeroSet T _).symm.trans hy1)
    exact ⟨i, hysub (by rw [hi]; exact Finset.mem_singleton_self i)⟩
  have : Nonempty (Fin n) := ⟨hJne.choose⟩
  -- the components `F̂_i` of Lemma 4.C at `o`
  have key : ∀ i : Fin n, (T 0 o).1 i = 0 → ∃ p ∈ R.faceStratum,
      o ∈ closure (connectedComponentIn R.faceStratum p) ∧ ∀ᶠ z in 𝓝 o, z ∈ φ.model.C →
        zeroSet T z = {i} → R z ∈ connectedComponentIn R.faceStratum p := by
    intro i hi
    obtain ⟨ε, hε, p, hpS, -, -, -, -, hB, hcl⟩ := local_face_structure hT hR hoO hi
    refine ⟨p, hpS, ?_, Filter.mem_of_superset (Metric.ball_mem_nhds o hε) fun z hz hzC hzI =>
      hB z ⟨hz, hzC⟩ hzI⟩
    have := hcl o ⟨Metric.mem_ball_self hε, R.retract_subset_C hoO⟩ hi
    rwa [R.apply_eq_self_of_mem_retract hoO] at this
  choose! p hpS hpcl hp using key
  have hev : ∀ᶠ z in 𝓝 o, zeroSet T z ⊆ J ∧ ∀ i ∈ J, z ∈ φ.model.C →
      zeroSet T z = {i} → R z ∈ connectedComponentIn R.faceStratum (p i) :=
    (eventually_zeroSet_subset T o).and
      ((Filter.eventually_all_finset _).2 fun i hi => hp i ((mem_zeroSet T).1 hi))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hev
  -- `K_i = φ⁻¹(F̂_i)`, inside `V ∩ {d = 1}`
  set K : Fin n → Set X := fun i => φ.symm '' connectedComponentIn R.faceStratum (p i) with hKdef
  have hK : ∀ i ∈ J, IsPreconnected (K i) ∧ K i ⊆ D ∧ φ.symm (p i) ∈ K i := by
    intro i hi
    have hpi := hpS i ((mem_zeroSet T).1 hi)
    refine ⟨isPreconnected_connectedComponentIn.image _ (φ.continuousOn_invFun.mono (hsubO _)),
      ?_, ⟨p i, mem_connectedComponentIn hpi, rfl⟩⟩
    rintro _ ⟨z, hz, rfl⟩
    have hzS := connectedComponentIn_subset _ _ hz
    refine ⟨hsrc (φ.symm_mapsTo (hsubO _ hz)), ?_⟩
    change P.degIndex (φ.symm z) = 1
    rw [hdeg _ (φ.symm_mapsTo (hsubO _ hz)), φ.apply_symm_apply (hsubO _ hz)]
    exact faceStratum_degIndexWith hT hzS
  have hKc : ∀ i ∈ J, K i ⊆ connectedComponentIn D (φ.symm (p i)) := fun i hi =>
    (hK i hi).1.subset_connectedComponentIn (hK i hi).2.2 (hK i hi).2.1
  set f : Fin n → Set X := fun i => faceAt P.degIndex V (φ.symm (p i)) with hfdef
  -- every component of `D` whose closure contains `x` is one of the `cc(φ⁻¹ p_i)`
  have hsurj : ∀ y₁, x ∈ closure (connectedComponentIn D y₁) →
      ∃ i ∈ J, connectedComponentIn D y₁ = connectedComponentIn D (φ.symm (p i)) := by
    intro y₁ hx₁
    obtain ⟨y, ⟨hyV, hyB⟩, hyG⟩ := mem_closure_iff_nhds.1 hx₁ _
      ((show ∀ᶠ y in 𝓝 x, y ∈ φ.source from φ.isOpen_source.mem_nhds hx).and
        (hφc.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))))
    obtain ⟨hysub, hyR⟩ := hball hyB
    have hy1 : degIndexWith T (φ y) = 1 :=
      (hdeg y hyV).symm.trans (connectedComponentIn_subset D y₁ hyG).2
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 ((degIndexWith_eq_card_zeroSet T _).symm.trans hy1)
    have hiJ : i ∈ J := hysub (by rw [hi]; exact Finset.mem_singleton_self i)
    have hφyO : φ y ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model y hyV
    have hRy := hyR i hiJ (φ.apply_mem_C hyV) hi
    rw [R.apply_eq_self_of_mem_retract hφyO] at hRy
    have hyK : y ∈ K i := ⟨φ y, hRy, φ.symm_apply_apply hyV⟩
    refine ⟨i, hiJ, ?_⟩
    rw [connectedComponentIn_eq hyG, connectedComponentIn_eq (hKc i hiJ hyK)]
  -- the faces of `V` through `x` are the `f i`, and there are `#J` of them
  have hFx : facesThrough P.degIndex V x = f '' (J : Set (Fin n)) := by
    ext F'
    constructor
    · rintro ⟨⟨y₁, -, -, rfl⟩, hx₁⟩
      obtain ⟨i, hiJ, hi⟩ := hsurj y₁ hx₁.2
      refine ⟨i, hiJ, ?_⟩
      change V ∩ closure (connectedComponentIn D (φ.symm (p i))) =
        V ∩ closure (connectedComponentIn D y₁)
      rw [hi]
    · rintro ⟨i, hiJ, rfl⟩
      refine ⟨⟨φ.symm (p i), ((hK i hiJ).2.1 (hK i hiJ).2.2).1,
        ((hK i hiJ).2.1 (hK i hiJ).2.2).2, rfl⟩, hsrc hx, ?_⟩
      have hcw : ContinuousWithinAt φ.symm (connectedComponentIn R.faceStratum (p i)) o :=
        (φ.continuousOn_invFun o hoO').mono (hsubO _)
      have := hcw.mem_closure_image (hpcl i ((mem_zeroSet T).1 hiJ))
      rw [show φ.symm o = x from φ.symm_apply_apply hx] at this
      exact closure_mono (hKc i hiJ) this
  have hinj : Set.InjOn f (J : Set (Fin n)) := by
    have hcard := hVx
    rw [hFx, ← Finset.coe_image, Set.encard_coe_eq_coe_finsetCard, hdeg x hx,
      degIndexWith_eq_card_zeroSet] at hcard
    exact Finset.card_image_iff.1 (by exact_mod_cast hcard)
  -- our face is `f j`
  obtain ⟨j, hjJ, hGj⟩ := hsurj y₀ hxcl
  have hK' : ∀ g ∈ G, g ∈ φ.source → φ g ∈ Metric.ball o δ →
      φ g ∈ connectedComponentIn R.faceStratum (p j) := by
    intro g hgG hgV hgB
    obtain ⟨hgsub, hgR⟩ := hball hgB
    have hg1 : degIndexWith T (φ g) = 1 :=
      (hdeg g hgV).symm.trans (connectedComponentIn_subset D y₀ hgG).2
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 ((degIndexWith_eq_card_zeroSet T _).symm.trans hg1)
    have hiJ : i ∈ J := hgsub (by rw [hi]; exact Finset.mem_singleton_self i)
    have hφgO : φ g ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model g hgV
    have hRg := hgR i hiJ (φ.apply_mem_C hgV) hi
    rw [R.apply_eq_self_of_mem_retract hφgO] at hRg
    have hgK : g ∈ K i := ⟨φ g, hRg, φ.symm_apply_apply hgV⟩
    have hij : i = j := by
      apply hinj hiJ hjJ
      change V ∩ closure (connectedComponentIn D (φ.symm (p i))) =
        V ∩ closure (connectedComponentIn D (φ.symm (p j)))
      rw [connectedComponentIn_eq (hKc i hiJ hgK), ← hGj, ← connectedComponentIn_eq hgG]
    rw [← hij]; exact hRg
  refine ⟨closure (connectedComponentIn R.faceStratum (p j)) ∩ R.retract,
    ⟨p j, hpS j ((mem_zeroSet T).1 hjJ), rfl⟩, Metric.ball o δ, Metric.isOpen_ball,
    Metric.mem_ball_self hδ, ?_⟩
  apply Subset.antisymm
  · rintro _ ⟨⟨g, ⟨hgF, hgV⟩, rfl⟩, hgB⟩
    set U₀ := φ.source ∩ φ ⁻¹' Metric.ball o δ with hU₀
    have hU₀o : IsOpen U₀ :=
      φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source Metric.isOpen_ball
    have hgcl : g ∈ closure (U₀ ∩ G) := hU₀o.inter_closure ⟨⟨hgV, hgB⟩, hgF.2⟩
    have hcw : ContinuousWithinAt φ (U₀ ∩ G) g :=
      (φ.continuousOn_toFun g hgV).mono fun z hz => hz.1.1
    have h1 := hcw.mem_closure_image hgcl
    refine ⟨⟨closure_mono ?_ h1, by rw [hRO]; exact φ.mapsTo_model g hgV⟩, hgB⟩
    rintro _ ⟨g', ⟨⟨hg'V, hg'B⟩, hg'G⟩, rfl⟩
    exact hK' g' hg'G hg'V hg'B
  · rintro z ⟨⟨hzcl, hzO⟩, hzB⟩
    have hzO' : z ∈ φ.model.O := by rw [← hRO]; exact hzO
    have hcw : ContinuousWithinAt φ.symm (connectedComponentIn R.faceStratum (p j)) z :=
      (φ.continuousOn_invFun z hzO').mono (hsubO _)
    have h1 := hcw.mem_closure_image hzcl
    have hFj : φ.symm z ∈ faceAt P.degIndex V y₀ := by
      refine ⟨hsrc (φ.symm_mapsTo hzO'), ?_⟩
      change φ.symm z ∈ closure G
      rw [hG, hGj]; exact closure_mono (hKc j hjJ) h1
    exact ⟨⟨φ.symm z, ⟨hFj, φ.symm_mapsTo hzO'⟩, φ.apply_symm_apply hzO'⟩, hzB⟩

/-- The data of a chart of `bX` around the classes of `U(x, V, θ)` lying over `V₁`. -/
structure BChartData where
  t : BTriple (P.isCornerIndex_degIndex hP)
  centred : IsCenteredAt P.degIndex t.x t.V
  φ : MChart X
  isChart : P.IsChart φ
  V₁ : Set X
  isOpen_V₁ : IsOpen V₁
  V₁_subset : V₁ ⊆ φ.source
  k : ℕ
  W : ScBanach
  T : ScIso φ.model.E ((ScBanach.const (Fin (k + 1) → ℝ)).prod W)
  i : Fin (k + 1)
  coord_eq : ∀ y ∈ t.θ ∩ V₁, (T 0 (φ y)).1 i = 0
  isTameRetract : IsTameRetract ((ScBanach.const (Fin k → ℝ)).prod W) (quadrant k W 0)
    (faceProj T i 0 '' (φ '' (t.θ ∩ V₁)))
  degIndex_eq : ∀ y ∈ t.θ ∩ V₁, P.degIndex y =
    Polyfold.degIndex ((ScBanach.const (Fin k → ℝ)).prod W) (quadrant k W 0)
      (faceProj T i 0 (φ y)) + 1

namespace BChartData

variable {P hP} (D : P.BChartData hP)

/-- The model `π(φ(θ ∩ V₁))`. -/
def O : Set (((ScBanach.const (Fin D.k → ℝ)).prod D.W) 0) :=
  faceProj D.T D.i 0 '' (D.φ '' (D.t.θ ∩ D.V₁))

lemma incl_proj {y : X} (hy : y ∈ D.t.θ ∩ D.V₁) :
    faceIncl D.T D.i 0 (faceProj D.T D.i 0 (D.φ y)) = D.φ y :=
  faceIncl_faceProj D.T D.i (D.coord_eq y hy)

lemma mem_O_iff {z : ((ScBanach.const (Fin D.k → ℝ)).prod D.W) 0} :
    z ∈ D.O ↔ D.φ.symm (faceIncl D.T D.i 0 z) ∈ D.t.θ ∩ D.V₁ ∧
      faceProj D.T D.i 0 (D.φ (D.φ.symm (faceIncl D.T D.i 0 z))) = z := by
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [D.incl_proj hy, D.φ.symm_apply_apply (D.V₁_subset hy.2)]
    exact ⟨hy, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, ⟨_, h1, rfl⟩, h2⟩

lemma symm_incl_mem {z : ((ScBanach.const (Fin D.k → ℝ)).prod D.W) 0} (hz : z ∈ D.O) :
    D.φ.symm (faceIncl D.T D.i 0 z) ∈ D.t.θ ∩ D.V₁ := (D.mem_O_iff.1 hz).1

lemma incl_mem_model {z : ((ScBanach.const (Fin D.k → ℝ)).prod D.W) 0} (hz : z ∈ D.O) :
    faceIncl D.T D.i 0 z ∈ D.φ.model.O := by
  obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hz
  rw [D.incl_proj hy]; exact D.φ.mapsTo_model y (D.V₁_subset hy.2)

lemma apply_symm_incl {z : ((ScBanach.const (Fin D.k → ℝ)).prod D.W) 0} (hz : z ∈ D.O) :
    D.φ (D.φ.symm (faceIncl D.T D.i 0 z)) = faceIncl D.T D.i 0 z :=
  D.φ.apply_symm_apply (D.incl_mem_model hz)

open scoped Classical in
/-- The inverse of the chart: `z ↦ Φ⁻¹(φ⁻¹(ι z))`, with the junk value `[x, V, θ]`. -/
def invFun (z : ((ScBanach.const (Fin D.k → ℝ)).prod D.W) 0) : P.TameBoundarySpace hP :=
  if h : D.φ.symm (faceIncl D.T D.i 0 z) ∈ D.t.θ then
    ((phiHomeomorph _ D.centred).symm ⟨_, h⟩ : P.TameBoundarySpace hP)
  else D.t.cls

lemma invFun_eq {z : ((ScBanach.const (Fin D.k → ℝ)).prod D.W) 0} (hz : z ∈ D.O) :
    D.invFun z = ((phiHomeomorph _ D.centred).symm ⟨_, (D.symm_incl_mem hz).1⟩ :
      P.TameBoundarySpace hP) := by
  rw [invFun, dif_pos (D.symm_incl_mem hz).1]

lemma bMap_invFun {z : ((ScBanach.const (Fin D.k → ℝ)).prod D.W) 0} (hz : z ∈ D.O) :
    bMap _ (D.invFun z) = D.φ.symm (faceIncl D.T D.i 0 z) := by
  rw [D.invFun_eq hz, bMap_phiHomeomorph_symm]

lemma invFun_mem_uSet {z : ((ScBanach.const (Fin D.k → ℝ)).prod D.W) 0} (hz : z ∈ D.O) :
    D.invFun z ∈ uSet _ D.t := by
  rw [D.invFun_eq hz]; exact phiHomeomorph_symm_mem _ _

/-- **The chart of `bX`** `[y, V', θ'] ↦ π(φ(y))`, defined on the classes of `U(x, V, θ)` over
`V₁`, onto `π(φ(θ ∩ V₁))`: the chart `π ∘ φ` of the face `θ` composed with `Φ_{(x,V,θ)}`. -/
def chart : MChart (P.TameBoundarySpace hP) where
  model := ⟨(ScBanach.const (Fin D.k → ℝ)).prod D.W, quadrant D.k D.W 0, D.O,
    D.isTameRetract.isScRetract⟩
  toPartialEquiv :=
    { toFun := fun p => faceProj D.T D.i 0 (D.φ (bMap _ p))
      invFun := D.invFun
      source := {p | p ∈ uSet _ D.t ∧ bMap _ p ∈ D.V₁}
      target := D.O
      map_source' := fun p hp => ⟨_, ⟨_, ⟨bMap_mem_of_mem_uSet _ hp.1, hp.2⟩, rfl⟩, rfl⟩
      map_target' := fun z hz => ⟨D.invFun_mem_uSet hz, by
        rw [D.bMap_invFun hz]; exact (D.symm_incl_mem hz).2⟩
      left_inv' := fun p hp => by
        have hz : faceProj D.T D.i 0 (D.φ (bMap _ p)) ∈ D.O :=
          ⟨_, ⟨_, ⟨bMap_mem_of_mem_uSet _ hp.1, hp.2⟩, rfl⟩, rfl⟩
        rw [D.invFun_eq hz]
        have h1 : D.φ.symm (faceIncl D.T D.i 0 (faceProj D.T D.i 0 (D.φ (bMap _ p)))) =
            bMap _ p := by
          rw [D.incl_proj ⟨bMap_mem_of_mem_uSet _ hp.1, hp.2⟩,
            D.φ.symm_apply_apply (D.V₁_subset hp.2)]
        have : (⟨_, (D.symm_incl_mem hz).1⟩ : D.t.θ) =
            ⟨bMap _ p, bMap_mem_of_mem_uSet _ hp.1⟩ := Subtype.ext h1
        rw [this, phiHomeomorph_symm_bMap _ hp.1]
      right_inv' := fun z hz => by
        change faceProj D.T D.i 0 (D.φ (bMap _ (D.invFun z))) = z
        rw [D.bMap_invFun hz]
        exact (D.mem_O_iff.1 hz).2 }
  isOpen_source := by
    change IsOpen (uSet _ D.t ∩ bMap _ ⁻¹' D.V₁)
    exact (isOpen_uSet _ D.t).inter (D.isOpen_V₁.preimage (continuous_bMap _))
  target_eq := rfl
  continuousOn_toFun := by
    refine (faceProj D.T D.i 0).continuous.comp_continuousOn
      (D.φ.continuousOn_toFun.comp (continuous_bMap _).continuousOn fun p hp => D.V₁_subset hp.2)
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h1 : Continuous fun z : D.O => (⟨D.φ.symm (faceIncl D.T D.i 0 z),
        (D.symm_incl_mem z.2).1⟩ : D.t.θ) :=
      (D.φ.continuousOn_invFun.comp_continuous
        ((faceIncl D.T D.i 0).continuous.comp continuous_subtype_val)
        fun z => D.incl_mem_model z.2).subtype_mk _
    have h2 := continuous_subtype_val.comp ((phiHomeomorph _ D.centred).symm.continuous.comp h1)
    refine h2.congr fun z => ?_
    exact (D.invFun_eq z.2).symm

@[simp] lemma chart_apply (p : P.TameBoundarySpace hP) :
    D.chart p = faceProj D.T D.i 0 (D.φ (bMap _ p)) := rfl

lemma chart_source : D.chart.source = {p | p ∈ uSet _ D.t ∧ bMap _ p ∈ D.V₁} := rfl

lemma chart_model_O : D.chart.model.O = D.O := rfl

lemma chart_symm_apply {z : ((ScBanach.const (Fin D.k → ℝ)).prod D.W) 0} :
    D.chart.symm z = D.invFun z := rfl

lemma incl_chart {p : P.TameBoundarySpace hP} (hp : p ∈ D.chart.source) :
    faceIncl D.T D.i 0 (D.chart p) = D.φ (bMap _ p) :=
  D.incl_proj ⟨bMap_mem_of_mem_uSet _ hp.1, hp.2⟩

lemma bMap_mem_source {p : P.TameBoundarySpace hP} (hp : p ∈ D.chart.source) :
    bMap _ p ∈ D.φ.source := D.V₁_subset hp.2

/-- One transition map: on the overlap, `χ' ∘ χ⁻¹ = π' ∘ (φ' ∘ φ⁻¹) ∘ ι`. -/
theorem chart_transition_isScSmooth (D' : P.BChartData hP) :
    IsScSmoothRetractMap D.chart.model.E D.chart.model.C (D.chart.overlap D'.chart)
      D'.chart.model.E D'.chart.model.C (D'.chart.overlap D.chart)
      (D.chart.transition D'.chart) := by
  have hc := (D.isChart.compatible P D'.isChart).1
  have h1 : IsScSmoothRetractMap D.chart.model.E D.chart.model.C (D.chart.overlap D'.chart)
      D.φ.model.E D.φ.model.C (D.φ.overlap D'.φ) (faceIncl D.T D.i 0) := by
    refine (faceIncl D.T D.i).isScSmoothRetractMap (D.chart.isScRetract_overlap D'.chart) ?_
    rintro _ ⟨p, hp, rfl⟩
    rw [D.incl_chart hp.1]
    exact ⟨bMap _ p, ⟨D.bMap_mem_source hp.1, D'.bMap_mem_source hp.2⟩, rfl⟩
  have h3 : IsScSmoothRetractMap D'.φ.model.E D'.φ.model.C (D'.φ.overlap D.φ)
      D'.chart.model.E D'.chart.model.C univ (faceProj D'.T D'.i 0) :=
    (faceProj D'.T D'.i).isScSmoothRetractMap (D'.φ.isScRetract_overlap D.φ) (mapsTo_univ _ _)
  have h := h3.comp (hc.comp h1 (D.φ.isScRetract_overlap D'.φ)) (D'.φ.isScRetract_overlap D.φ)
  have heq : ∀ p ∈ D.chart.source ∩ D'.chart.source,
      (faceProj D'.T D'.i 0 ∘ (D.φ.transition D'.φ ∘ faceIncl D.T D.i 0)) (D.chart p) =
        D'.chart p := by
    intro p hp
    change faceProj D'.T D'.i 0 (D.φ.transition D'.φ (faceIncl D.T D.i 0 (D.chart p))) = _
    rw [D.incl_chart hp.1, D.φ.transition_apply D'.φ (D.bMap_mem_source hp.1)]
    rfl
  refine (h.mono_target ?_).congr ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact (heq p hp).symm ▸ ⟨p, ⟨hp.2, hp.1⟩, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (heq p hp).trans (D.chart.transition_apply D'.chart hp.1).symm

/-- **Proposition 2.7.12** for the charts of `bX`: any two of them are sc-smoothly compatible. -/
theorem chart_compatible (D' : P.BChartData hP) : D.chart.Compatible D'.chart :=
  ⟨D.chart_transition_isScSmooth D', D'.chart_transition_isScSmooth D⟩

end BChartData

/-- **The charts of `bX` cover `U(x, V, θ)`** (`V` centred at `x`): every `y ∈ θ` lies in `V₁` for
a chart datum with the triple `(x, V, θ)` (the local face of `θ` at `y` in a tame chart inside
`V`, `exists_localFace_of_faceIn`, and the tame model of Proposition 2.5.15 (preprint 2.43),
`proposition_2_43_tameModel`). -/
theorem exists_bChartData (hP : P.IsTame) (t : BTriple (P.isCornerIndex_degIndex hP))
    (ht : IsCenteredAt P.degIndex t.x t.V) {y : X} (hy : y ∈ t.θ) :
    ∃ D : P.BChartData hP, D.t = t ∧ y ∈ D.V₁ := by
  classical
  have hyV : y ∈ t.V := t.mem_faces.1.subset hy
  obtain ⟨φ, hφ, hyφ, hsrc, R, hRO, n, W, T, hT, hR⟩ :=
    P.exists_tame_chart_subset hP t.mem.1.1.1 hyV
  obtain ⟨Floc, hFloc, B, hB, hyB, hEq⟩ := P.exists_localFace_of_faceIn (t.mem.1.1.2 y hyV)
    ⟨t.mem_faces.1, hy⟩ hφ hyφ hsrc R hRO hT hR
  obtain ⟨i₀, -⟩ := proposition_2_43 hT hR hFloc
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := i₀.pos; omega⟩
  obtain ⟨i, hFi, R', hR'tame, hR'ret, hdeg'⟩ := proposition_2_43_tameModel hT hR hFloc
  have hT' : quadrant k W 0 = (ScIso.refl ((ScBanach.const (Fin k → ℝ)).prod W)) 0 ⁻¹'
      quadrant k W 0 := by ext; rfl
  set V₁ := φ.source ∩ φ ⁻¹' B with hV₁def
  have hV₁ : IsOpen V₁ := φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source hB
  have hFV : φ '' (t.θ ∩ V₁) = Floc ∩ B := by
    rw [← hEq]
    ext z
    constructor
    · rintro ⟨y, ⟨hyF, hyV, hyB⟩, rfl⟩; exact ⟨⟨y, ⟨hyF, hyV⟩, rfl⟩, hyB⟩
    · rintro ⟨⟨y, ⟨hyF, hyV⟩, rfl⟩, hyB⟩; exact ⟨y, ⟨hyF, hyV, hyB⟩, rfl⟩
  have hmemF : ∀ y' ∈ t.θ ∩ V₁, φ y' ∈ Floc := fun y' hy' => by
    have : φ y' ∈ φ '' (t.θ ∩ V₁) := ⟨y', hy', rfl⟩
    rw [hFV] at this; exact this.1
  set ι := faceIncl T i with hι
  set π := faceProj T i with hπ
  set Wι := ι 0 ⁻¹' B with hWι
  have hWιo : IsOpen Wι := hB.preimage (ι 0).continuous
  have hret_eq : (R'.restrict hWιo).retract = π 0 '' (φ '' (t.θ ∩ V₁)) := by
    rw [R'.restrict_retract, hR'ret, hFV]
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hyB⟩
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      have : ι 0 (π 0 y) = y := faceIncl_faceProj T i (hFi hy)
      rw [← this]; exact hyB
    · rintro ⟨y, ⟨hy, hyB⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, ?_⟩
      change ι 0 (π 0 y) ∈ B
      rw [faceIncl_faceProj T i (hFi hy)]; exact hyB
  refine ⟨⟨t, ht, φ, hφ, V₁, hV₁, fun _ h => h.1, k, W, T, i, fun y' hy' => hFi (hmemF y' hy'),
    ⟨R'.restrict hWιo, hret_eq, (hR'tame.restrict hWιo).isTame hT'⟩, fun y' hy' => ?_⟩, rfl,
    ⟨hyφ, hyB⟩⟩
  rw [P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR hy'.2.1, chartDegIndex]
  exact (hdeg' _ (hmemF y' hy')).symm

/-- `bX` is paracompact (it is metrizable, 2021 Proposition 2.7.16). -/
instance paracompactSpace_tameBoundarySpace (hP : P.IsTame) :
    ParacompactSpace (P.TameBoundarySpace hP) := by
  have := P.metrizableSpace
  have := proposition_2_7_16 (P.isCornerIndex_degIndex hP)
  exact paracompactSpace_of_metrizableSpace _

/-- The atlas of `bX`: the charts `χ_D` of all chart data. -/
def bAtlas (hP : P.IsTame) : MAtlas (P.TameBoundarySpace hP) where
  charts := {χ | ∃ D : P.BChartData hP, χ = D.chart}
  compatible := by
    rintro _ ⟨D, rfl⟩ _ ⟨D', rfl⟩
    exact D.chart_compatible D'
  cover p := by
    obtain ⟨t, rfl, ht⟩ := BSpace.exists_centred_rep _ p
    obtain ⟨D, rfl, hy⟩ := P.exists_bChartData hP t ht t.mem_faces.2
    exact ⟨D.chart, ⟨D, rfl⟩, cls_mem_uSet _ D.t, hy⟩

/-- **2021 Theorem 2.7.13 (2)**: the M-polyfold structure of `bX`. -/
def tameBoundaryPolyfold (hP : P.IsTame) : MPolyfold (P.TameBoundarySpace hP) := ⟨P.bAtlas hP⟩

lemma isChart_chart {hP : P.IsTame} (D : P.BChartData hP) :
    (P.tameBoundaryPolyfold hP).IsChart D.chart :=
  (P.tameBoundaryPolyfold hP).isChart_of_mem ⟨D, rfl⟩

/-- Every point of `bX` lies in the domain of a chart `χ_D`. -/
lemma exists_bChartData_mem (hP : P.IsTame) (p : P.TameBoundarySpace hP) :
    ∃ D : P.BChartData hP, p ∈ D.chart.source := by
  obtain ⟨χ, ⟨D, rfl⟩, hp⟩ := (P.bAtlas hP).cover p
  exact ⟨D, hp⟩

/-- **2021 Theorem 2.7.13 (2)**: the structure of `bX` is tame. -/
theorem tameBoundaryPolyfold_isTame (hP : P.IsTame) : (P.tameBoundaryPolyfold hP).IsTame :=
  ⟨P.bAtlas hP, MAtlas.Equiv.refl _, by rintro _ ⟨D, rfl⟩; exact D.isTameRetract⟩

/-- **2021 Theorem 2.7.13 (3)**: `B : bX → X` is sc-smooth (in the chart `χ_D` and `φ` it is the
sc-operator `ι`). -/
theorem tameBoundaryMap_isScSmooth (hP : P.IsTame) :
    (P.tameBoundaryPolyfold hP).IsScSmoothMap P (P.tameBoundaryMap hP) := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ (continuous_bMap _).continuousOn
    fun p _ => ?_
  obtain ⟨D, hp⟩ := P.exists_bChartData_mem hP p
  refine ⟨D.chart, D.φ, D.chart.source, P.isChart_chart D, D.isChart, D.chart.isOpen_source, hp,
    fun q hq => ⟨mem_univ _, hq⟩, fun q hq => D.bMap_mem_source hq, ?_⟩
  rw [D.chart.image_source]
  refine ((faceIncl D.T D.i).isScSmoothRetractMap D.isTameRetract.isScRetract
    (fun z hz => D.incl_mem_model hz)).congr fun z hz => ?_
  change faceIncl D.T D.i 0 z = D.φ (bMap _ (D.invFun z))
  rw [D.bMap_invFun hz, D.apply_symm_incl hz]

/-- **2021 Theorem 2.7.13 (4)**: `d_X(B(p)) = d_{bX}(p) + 1`. -/
theorem degIndex_tameBoundaryMap (hP : P.IsTame) (p : P.TameBoundarySpace hP) :
    P.degIndex (P.tameBoundaryMap hP p) = (P.tameBoundaryPolyfold hP).degIndex p + 1 := by
  obtain ⟨D, hp⟩ := P.exists_bChartData_mem hP p
  obtain ⟨R, hRO, hRt⟩ := D.isTameRetract
  have hT' : D.chart.model.C = (ScIso.refl ((ScBanach.const (Fin D.k → ℝ)).prod D.W)) 0 ⁻¹'
      quadrant D.k D.W 0 := by ext; rfl
  rw [(P.tameBoundaryPolyfold hP).degIndex_eq_chartDegIndex_of_isTameWith (P.isChart_chart D) R
    hRO hT' (hRt _ _ _ hT') hp, chartDegIndex]
  exact D.degIndex_eq _ ⟨bMap_mem_of_mem_uSet _ hp.1, hp.2⟩

/-! ### The characterization: `Φ_{(x,V,θ)}` is an sc-diffeomorphism onto the face `θ` -/

/-- A face of a face-structured open set `V` is a sub-M-polyfold of `X` (the argument of 2021
Theorem 2.5.17 (preprint Theorem 2.45) for `V` with the induced structure:
`exists_localFace_of_faceIn` and the retraction onto the local face, Proposition 2.5.15
(preprint 2.43)). -/
theorem isSubMPolyfold_of_isFaceIn (hP : P.IsTame) {V θ : Set X}
    (hV : IsFaceStructuredOpen P.degIndex V) (hθ : IsFaceIn P.degIndex V θ) :
    P.IsSubMPolyfold θ := by
  refine P.isSubMPolyfold_of_local fun y hy => ?_
  have hyV := hθ.subset hy
  obtain ⟨φ, hφ, hyφ, hsrc, R, hRO, n, W, T, hT, hR⟩ := P.exists_tame_chart_subset hP hV.1 hyV
  obtain ⟨Floc, hFloc, B, hB, hyB, hEq⟩ :=
    P.exists_localFace_of_faceIn (hV.2 y hyV) ⟨hθ, hy⟩ hφ hyφ hsrc R hRO hT hR
  have hFlocO : Floc ⊆ R.retract := by
    obtain ⟨_, _, h⟩ := hFloc; rw [h]; exact inter_subset_right
  obtain ⟨-, -, S', -, -, hS'ret, -⟩ := proposition_2_43 hT hR hFloc
  refine ⟨φ, hφ, hyφ, S', B, hB, hyB, ?_, ?_⟩
  · rw [hS'ret, ← hRO]; exact hFlocO
  · rw [hS'ret, hEq]

/-- The natural M-polyfold structure of a face `θ` of a face-structured open `V` (the face of `V`
with its induced structure, as a sub-M-polyfold of `X`, 2021 Proposition 2.3.19 (preprint
Proposition 2.21)). -/
def facePolyfold (hP : P.IsTame) {V θ : Set X} (hV : IsFaceStructuredOpen P.degIndex V)
    (hθ : IsFaceIn P.degIndex V θ) :
    letI := P.paracompactSpace_subtype θ
    MPolyfold θ :=
  letI := P.paracompactSpace_subtype θ
  subPolyfold (P.isSubMPolyfold_of_isFaceIn hP hV hθ)

namespace BChartData

variable {P hP} (D : P.BChartData hP)

lemma incl_proj' : ∀ y ∈ D.φ '' (D.t.θ ∩ D.V₁),
    faceIncl D.T D.i 0 (faceProj D.T D.i 0 y) = y := by
  rintro _ ⟨y, hy, rfl⟩; exact D.incl_proj hy

/-- The chart `π ∘ φ : θ ∩ V₁ → π(φ(θ ∩ V₁))` of the face `θ` (`MPolyfold.faceChart`). -/
def faceChart' : MChart D.t.θ :=
  faceChart ⟨D.t.x, D.t.mem_faces.2⟩ D.φ D.V₁ (quadrant D.k D.W 0) (faceIncl D.T D.i)
    (faceProj D.T D.i) D.isOpen_V₁ D.V₁_subset D.incl_proj' (faceProj_faceIncl D.T D.i)
    D.isTameRetract.isScRetract

lemma faceChart'_apply (y : D.t.θ) : D.faceChart' y = faceProj D.T D.i 0 (D.φ y) := rfl

lemma faceChart'_source : D.faceChart'.source = {y : D.t.θ | (y : X) ∈ D.V₁} := rfl

lemma faceChart'_symm_spec {z : ((ScBanach.const (Fin D.k → ℝ)).prod D.W) 0} (hz : z ∈ D.O) :
    ((D.faceChart'.symm z : D.t.θ) : X) ∈ D.V₁ ∧
      D.φ (D.faceChart'.symm z : X) = faceIncl D.T D.i 0 z :=
  faceChartInv_spec _ D.φ D.V₁ _ _ D.incl_proj' hz

lemma faceChart'_symm_val {z : ((ScBanach.const (Fin D.k → ℝ)).prod D.W) 0} (hz : z ∈ D.O) :
    ((D.faceChart'.symm z : D.t.θ) : X) = D.φ.symm (faceIncl D.T D.i 0 z) := by
  rw [← (D.faceChart'_symm_spec hz).2,
    D.φ.symm_apply_apply (D.V₁_subset (D.faceChart'_symm_spec hz).1)]

/-- `faceChart'` is a chart of the face `θ` with its induced structure. -/
theorem isChart_faceChart' :
    letI := P.paracompactSpace_subtype D.t.θ
    (P.facePolyfold hP D.t.mem.1.1 D.t.mem_faces.1).IsChart D.faceChart' := by
  let _ := P.paracompactSpace_subtype D.t.θ
  exact isChart_subPolyfold_of_compatible _ D.isChart (fun _ hy => D.V₁_subset hy) fun d b₀ =>
    faceChart_compatible_subChart D.isChart D.isOpen_V₁ D.V₁_subset D.incl_proj'
      (faceProj_faceIncl D.T D.i) D.isTameRetract.isScRetract d b₀

end BChartData

open scoped Classical in
/-- `Φ_{(x,V,θ)}` as a total map `bX → θ` (with the junk value `x` off `U(x, V, θ)`). -/
def phiTot (hP : P.IsTame) (t : BTriple (P.isCornerIndex_degIndex hP))
    (p : P.TameBoundarySpace hP) : t.θ :=
  if h : p ∈ uSet _ t then ⟨bMap _ p, bMap_mem_of_mem_uSet _ h⟩ else ⟨t.x, t.mem_faces.2⟩

variable {hP} in
lemma phiTot_of_mem {t : BTriple (P.isCornerIndex_degIndex hP)} {p : P.TameBoundarySpace hP}
    (hp : p ∈ uSet _ t) : P.phiTot hP t p = ⟨bMap _ p, bMap_mem_of_mem_uSet _ hp⟩ := by
  rw [phiTot, dif_pos hp]

/-- **The characterization in 2021 Theorem 2.7.13**: for `V` centred at `x`, the map
`Φ_{(x,V,θ)} : U(x, V, θ) → θ` is an sc-diffeomorphism of the open subset `U(x, V, θ)` of `bX`
onto the face `θ` with its natural M-polyfold structure (its inverse is `Φ⁻¹`).  In the charts
`χ_D` of `bX` and `π ∘ φ` of `θ` both maps are the identity. -/
theorem phi_isScDiffeoOn (hP : P.IsTame) (t : BTriple (P.isCornerIndex_degIndex hP))
    (ht : IsCenteredAt P.degIndex t.x t.V) :
    letI := P.paracompactSpace_subtype t.θ
    (P.tameBoundaryPolyfold hP).IsScDiffeoOn (P.facePolyfold hP t.mem.1.1 t.mem_faces.1)
      (P.phiTot hP t) (fun y => ((phiHomeomorph _ ht).symm y : P.TameBoundarySpace hP))
      (uSet _ t) univ := by
  let _ := P.paracompactSpace_subtype t.θ
  have hg : Continuous fun y : t.θ => ((phiHomeomorph _ ht).symm y : P.TameBoundarySpace hP) :=
    continuous_subtype_val.comp (phiHomeomorph _ ht).symm.continuous
  refine ⟨?_, ?_, fun _ _ => mem_univ _, fun y _ => phiHomeomorph_symm_mem _ y,
    fun p hp => ?_, fun y _ => ?_⟩
  · -- `Φ` is sc-smooth
    have hcont : ContinuousOn (P.phiTot hP t) (uSet _ t) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact (isOpenEmbedding_phi _ t).continuous.congr fun p => (P.phiTot_of_mem p.2).symm
    refine IsScSmoothOn.of_exists_charts (isOpen_uSet _ t) hcont fun p hp => ?_
    obtain ⟨D, rfl, hy⟩ := P.exists_bChartData hP t ht (bMap_mem_of_mem_uSet _ hp)
    refine ⟨D.chart, D.faceChart', D.chart.source, P.isChart_chart D, D.isChart_faceChart',
      D.chart.isOpen_source, ⟨hp, hy⟩, fun q hq => ⟨hq.1, hq⟩, fun q hq => ?_, ?_⟩
    · change ((P.phiTot hP D.t q : D.t.θ) : X) ∈ D.V₁
      rw [P.phiTot_of_mem hq.1]; exact hq.2
    · rw [D.chart.image_source]
      refine (isScSmoothRetractMap_id D.O).congr fun z hz => ?_
      change z = faceProj D.T D.i 0 (D.φ (P.phiTot hP D.t (D.invFun z) : X))
      rw [P.phiTot_of_mem (D.invFun_mem_uSet hz)]
      change z = faceProj D.T D.i 0 (D.φ (bMap _ (D.invFun z)))
      rw [D.bMap_invFun hz]
      exact (D.mem_O_iff.1 hz).2.symm
  · -- `Φ⁻¹` is sc-smooth
    refine IsScSmoothOn.of_exists_charts isOpen_univ hg.continuousOn fun y _ => ?_
    obtain ⟨D, rfl, hy⟩ := P.exists_bChartData hP t ht y.2
    refine ⟨D.faceChart', D.chart, D.faceChart'.source, D.isChart_faceChart', P.isChart_chart D,
      D.faceChart'.isOpen_source, hy, fun q hq => ⟨mem_univ _, hq⟩, fun q hq => ?_, ?_⟩
    · refine ⟨phiHomeomorph_symm_mem _ q, ?_⟩
      rw [bMap_phiHomeomorph_symm]; exact hq
    · rw [D.faceChart'.image_source]
      refine (isScSmoothRetractMap_id D.O).congr fun z hz => ?_
      change z = faceProj D.T D.i 0 (D.φ (bMap _ ((phiHomeomorph _ D.centred).symm
        (D.faceChart'.symm z) : P.TameBoundarySpace hP)))
      rw [bMap_phiHomeomorph_symm, (D.faceChart'_symm_spec hz).2]
      exact (faceProj_faceIncl D.T D.i z).symm
  · rw [P.phiTot_of_mem hp, phiHomeomorph_symm_bMap _ hp]
  · have hm := phiHomeomorph_symm_mem ht y
    rw [P.phiTot_of_mem hm]
    exact Subtype.ext (bMap_phiHomeomorph_symm _ y)

namespace BChartData

variable {P hP} (D : P.BChartData hP)

lemma chart_mem_O {p : P.TameBoundarySpace hP} (hp : p ∈ D.chart.source) : D.chart p ∈ D.O :=
  D.chart.toPartialEquiv.map_source hp

/-- `Φ⁻¹ ∘ (π ∘ φ)⁻¹ ∘ χ_D = id` on the domain of `χ_D`. -/
lemma phi_symm_faceChart'_symm_chart {p : P.TameBoundarySpace hP} (hp : p ∈ D.chart.source) :
    ((phiHomeomorph _ D.centred).symm (D.faceChart'.symm (D.chart p)) :
      P.TameBoundarySpace hP) = p := by
  have hval : D.faceChart'.symm (D.chart p) = ⟨bMap _ p, bMap_mem_of_mem_uSet _ hp.1⟩ := by
    apply Subtype.ext
    rw [D.faceChart'_symm_val (D.chart_mem_O hp), D.incl_chart hp,
      D.φ.symm_apply_apply (D.bMap_mem_source hp)]
  rw [hval, phiHomeomorph_symm_bMap _ hp.1]

end BChartData

/-- **The uniqueness in 2021 Theorem 2.7.13**: an M-polyfold structure `Q'` on `bX` (with the
topology `T_{bX}`) for which every `Φ_{(x,V,θ)}`, `V` centred at `x`, is an sc-diffeomorphism of
`U(x, V, θ)` onto the face `θ` with its natural structure, is equivalent to
`tameBoundaryPolyfold` (the union of the two atlases is an atlas, so both have the same charts,
`isChart_congr`).  The hypothesis is satisfied by `tameBoundaryPolyfold` (`phi_isScDiffeoOn`). -/
theorem tameBoundaryPolyfold_unique (hP : P.IsTame) (Q' : MPolyfold (P.TameBoundarySpace hP))
    (h : ∀ (t : BTriple (P.isCornerIndex_degIndex hP)) (ht : IsCenteredAt P.degIndex t.x t.V),
      letI := P.paracompactSpace_subtype t.θ
      Q'.IsScDiffeoOn (P.facePolyfold hP t.mem.1.1 t.mem_faces.1) (P.phiTot hP t)
        (fun y => ((phiHomeomorph _ ht).symm y : P.TameBoundarySpace hP)) (uSet _ t) univ) :
    Q'.atlas.Equiv (P.tameBoundaryPolyfold hP).atlas := by
  rw [MAtlas.equiv_iff]
  rintro ψ hψ _ ⟨D, rfl⟩
  let _ := P.paracompactSpace_subtype D.t.θ
  have hD := h D.t D.centred
  have hψc : Q'.IsChart ψ := Q'.isChart_of_mem hψ
  constructor
  · -- `χ_D ∘ ψ⁻¹ = (π ∘ φ) ∘ Φ ∘ ψ⁻¹`
    have hV : IsOpen (ψ.source ∩ D.chart.source) := ψ.isOpen_source.inter D.chart.isOpen_source
    have h1 := hD.isScSmoothOn.smooth ψ D.faceChart' hψc D.isChart_faceChart'
      (ψ.source ∩ D.chart.source) hV (fun q hq => ⟨hq.2.1, hq.1⟩) fun q hq => by
        change ((P.phiTot hP D.t q : D.t.θ) : X) ∈ D.V₁
        rw [P.phiTot_of_mem hq.2.1]; exact hq.2.2
    have hval : ∀ q ∈ ψ.source ∩ D.chart.source,
        (D.faceChart' ∘ P.phiTot hP D.t ∘ ψ.symm) (ψ q) = D.chart q := by
      intro q hq
      change D.faceChart' (P.phiTot hP D.t (ψ.symm (ψ q))) = D.chart q
      rw [ψ.symm_apply_apply hq.1, P.phiTot_of_mem hq.2.1]
      rfl
    refine (h1.mono_target ?_).congr ?_
    · rintro _ ⟨q, hq, rfl⟩
      exact (hval q hq).symm ▸ ⟨q, ⟨hq.2, hq.1⟩, rfl⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact (hval q hq).trans (ψ.transition_apply D.chart hq.1).symm
  · -- `ψ ∘ χ_D⁻¹ = ψ ∘ Φ⁻¹ ∘ (π ∘ φ)⁻¹`
    set g := fun y : D.t.θ => ((phiHomeomorph _ D.centred).symm y : P.TameBoundarySpace hP)
      with hgdef
    have hgc : Continuous g :=
      continuous_subtype_val.comp (phiHomeomorph _ D.centred).symm.continuous
    set V' := D.faceChart'.source ∩ g ⁻¹' ψ.source with hV'def
    have hV' : IsOpen V' := D.faceChart'.isOpen_source.inter (ψ.isOpen_source.preimage hgc)
    have h2 := hD.isScSmoothOn_inv.smooth D.faceChart' ψ D.isChart_faceChart' hψc V' hV'
      (fun y hy => ⟨mem_univ _, hy.1⟩) fun y hy => hy.2
    have hset : D.faceChart' '' V' = D.chart.overlap ψ := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨g y, ⟨⟨phiHomeomorph_symm_mem _ y, ?_⟩, hy.2⟩, ?_⟩
        · rw [hgdef, bMap_phiHomeomorph_symm]; exact hy.1
        · change faceProj D.T D.i 0 (D.φ (bMap _ (g y))) = faceProj D.T D.i 0 (D.φ y)
          rw [hgdef, bMap_phiHomeomorph_symm]
      · rintro ⟨q, hq, rfl⟩
        refine ⟨⟨bMap _ q, bMap_mem_of_mem_uSet _ hq.1.1⟩, ⟨hq.1.2, ?_⟩, rfl⟩
        change g ⟨bMap _ q, bMap_mem_of_mem_uSet _ hq.1.1⟩ ∈ ψ.source
        rw [hgdef]; simp only
        rw [phiHomeomorph_symm_bMap _ hq.1.1]; exact hq.2
    rw [hset] at h2
    have hval : ∀ q ∈ D.chart.source ∩ ψ.source,
        (ψ ∘ g ∘ D.faceChart'.symm) (D.chart q) = ψ q := by
      intro q hq
      change ψ (g (D.faceChart'.symm (D.chart q))) = ψ q
      rw [hgdef]; simp only
      rw [D.phi_symm_faceChart'_symm_chart hq.1]
    refine (h2.mono_target ?_).congr ?_
    · rintro _ ⟨q, hq, rfl⟩
      exact (hval q hq).symm ▸ ⟨q, ⟨hq.2, hq.1⟩, rfl⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact (hval q hq).trans (D.chart.transition_apply ψ hq.1).symm

/-- **2021 Proposition 2.7.12**, the sc-part: for two triples with centred neighbourhoods, the
transition map `Φ_{(x',V',θ')} ∘ Φ_{(x,V,θ)}⁻¹` (the identity of the underlying points of `X`) is an
sc-diffeomorphism between the open subsets `Φ_{(x,V,θ)}(U ∩ U')` of `θ` and
`Φ_{(x',V',θ')}(U ∩ U')` of `θ'` (with the natural structures of the faces). -/
theorem proposition_2_7_12_scDiffeo_2021 (hP : P.IsTame)
    (t t' : BTriple (P.isCornerIndex_degIndex hP))
    (ht : IsCenteredAt P.degIndex t.x t.V) (ht' : IsCenteredAt P.degIndex t'.x t'.V) :
    letI := P.paracompactSpace_subtype t.θ
    letI := P.paracompactSpace_subtype t'.θ
    (P.facePolyfold hP t.mem.1.1 t.mem_faces.1).IsScDiffeoOn
      (P.facePolyfold hP t'.mem.1.1 t'.mem_faces.1)
      (fun y => P.phiTot hP t' ((phiHomeomorph _ ht).symm y))
      (fun y => P.phiTot hP t ((phiHomeomorph _ ht').symm y))
      {y | ((phiHomeomorph _ ht).symm y : P.TameBoundarySpace hP) ∈ uSet _ t'}
      {y | ((phiHomeomorph _ ht').symm y : P.TameBoundarySpace hP) ∈ uSet _ t} ∧
    ∀ y : t.θ, ((phiHomeomorph _ ht).symm y : P.TameBoundarySpace hP) ∈ uSet _ t' →
      (P.phiTot hP t' ((phiHomeomorph _ ht).symm y) : X) = y := by
  let _ := P.paracompactSpace_subtype t.θ
  let _ := P.paracompactSpace_subtype t'.θ
  have h := P.phi_isScDiffeoOn hP t ht
  have h' := P.phi_isScDiffeoOn hP t' ht'
  have hgc : ∀ (s : BTriple (P.isCornerIndex_degIndex hP)) (hs : IsCenteredAt P.degIndex s.x s.V),
      Continuous fun y : s.θ => ((phiHomeomorph _ hs).symm y : P.TameBoundarySpace hP) :=
    fun s hs => continuous_subtype_val.comp (phiHomeomorph _ hs).symm.continuous
  have hA : IsOpen {y : t.θ | ((phiHomeomorph _ ht).symm y : P.TameBoundarySpace hP) ∈ uSet _ t'} :=
    (isOpen_uSet _ t').preimage (hgc t ht)
  have hA' : IsOpen {y : t'.θ | ((phiHomeomorph _ ht').symm y : P.TameBoundarySpace hP) ∈
      uSet _ t} := (isOpen_uSet _ t).preimage (hgc t' ht')
  -- the underlying point is preserved
  have hpt : ∀ y : t.θ, ((phiHomeomorph _ ht).symm y : P.TameBoundarySpace hP) ∈ uSet _ t' →
      (P.phiTot hP t' ((phiHomeomorph _ ht).symm y) : X) = y := fun y hy => by
    rw [P.phiTot_of_mem hy]; exact bMap_phiHomeomorph_symm _ y
  have hpt' : ∀ y : t'.θ, ((phiHomeomorph _ ht').symm y : P.TameBoundarySpace hP) ∈ uSet _ t →
      (P.phiTot hP t ((phiHomeomorph _ ht').symm y) : X) = y := fun y hy => by
    rw [P.phiTot_of_mem hy]; exact bMap_phiHomeomorph_symm _ y
  -- `Φ'⁻¹ (Φ' (Φ⁻¹ y)) = Φ⁻¹ y`
  have hback : ∀ y : t.θ, ((phiHomeomorph _ ht).symm y : P.TameBoundarySpace hP) ∈ uSet _ t' →
      ((phiHomeomorph _ ht').symm (P.phiTot hP t' ((phiHomeomorph _ ht).symm y)) :
        P.TameBoundarySpace hP) = (phiHomeomorph _ ht).symm y := fun y hy =>
    h'.left_inv _ hy
  have hback' : ∀ y : t'.θ, ((phiHomeomorph _ ht').symm y : P.TameBoundarySpace hP) ∈ uSet _ t →
      ((phiHomeomorph _ ht).symm (P.phiTot hP t ((phiHomeomorph _ ht').symm y)) :
        P.TameBoundarySpace hP) = (phiHomeomorph _ ht').symm y := fun y hy =>
    h.left_inv _ hy
  refine ⟨⟨?_, ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩, hpt⟩
  · exact IsScSmoothOn.comp h'.isScSmoothOn (h.isScSmoothOn_inv.mono hA (subset_univ _))
      fun y hy => hy
  · exact IsScSmoothOn.comp h.isScSmoothOn (h'.isScSmoothOn_inv.mono hA' (subset_univ _))
      fun y hy => hy
  · change ((phiHomeomorph _ ht').symm (P.phiTot hP t' ((phiHomeomorph _ ht).symm y)) :
      P.TameBoundarySpace hP) ∈ uSet _ t
    rw [hback y hy]; exact phiHomeomorph_symm_mem _ y
  · change ((phiHomeomorph _ ht).symm (P.phiTot hP t ((phiHomeomorph _ ht').symm y)) :
      P.TameBoundarySpace hP) ∈ uSet _ t'
    rw [hback' y hy]; exact phiHomeomorph_symm_mem _ y
  · rw [hback y hy]; exact h.right_inv y (mem_univ _)
  · rw [hback' y hy]; exact h'.right_inv y (mem_univ _)

/-- **Satisfiability of the hypothesis of `tameBoundaryPolyfold_unique`**: the structure
`tameBoundaryPolyfold` itself satisfies it (`phi_isScDiffeoOn`). -/
theorem tameBoundaryPolyfold_satisfies (hP : P.IsTame) :
    ∀ (t : BTriple (P.isCornerIndex_degIndex hP)) (ht : IsCenteredAt P.degIndex t.x t.V),
      letI := P.paracompactSpace_subtype t.θ
      (P.tameBoundaryPolyfold hP).IsScDiffeoOn (P.facePolyfold hP t.mem.1.1 t.mem_faces.1)
        (P.phiTot hP t) (fun y => ((phiHomeomorph _ ht).symm y : P.TameBoundarySpace hP))
        (uSet _ t) univ :=
  P.phi_isScDiffeoOn hP

/-- **2021 Theorem 2.7.13 (4)**, as printed: `d_X(B([x, V, θ])) − 1 = d_{bX}([x, V, θ])`. -/
theorem degIndex_tameBoundaryMap_sub_one (hP : P.IsTame) (p : P.TameBoundarySpace hP) :
    P.degIndex (P.tameBoundaryMap hP p) - 1 = (P.tameBoundaryPolyfold hP).degIndex p := by
  rw [P.degIndex_tameBoundaryMap hP p, Nat.add_sub_cancel]

/-- **2021 Theorem 2.7.13 (2)–(4)** and the characterization of its last paragraph, for a tame
M-polyfold `X`: (2) `bX`, with the topology `T_{bX}` of (1), carries the tame M-polyfold structure
`tameBoundaryPolyfold`; (3) `B : bX → X` is sc-smooth; (4) `d_X(B(p)) − 1 = d_{bX}(p)`; for every
triple `(x, V, θ)` with `V` centred at `x`, `Φ_{(x,V,θ)}` is an sc-diffeomorphism of the open set
`U(x, V, θ)` onto the face `θ` with its natural structure; and every M-polyfold structure on `bX`
with this property is equivalent to `tameBoundaryPolyfold`. -/
theorem theorem_2_7_13_structure_2021 (hP : P.IsTame) :
    (P.tameBoundaryPolyfold hP).IsTame ∧
      (P.tameBoundaryPolyfold hP).IsScSmoothMap P (P.tameBoundaryMap hP) ∧
      (∀ p, P.degIndex (P.tameBoundaryMap hP p) - 1 = (P.tameBoundaryPolyfold hP).degIndex p) ∧
      (∀ (t : BTriple (P.isCornerIndex_degIndex hP)) (ht : IsCenteredAt P.degIndex t.x t.V),
        IsOpen (uSet _ t) ∧
        letI := P.paracompactSpace_subtype t.θ
        (P.tameBoundaryPolyfold hP).IsScDiffeoOn (P.facePolyfold hP t.mem.1.1 t.mem_faces.1)
          (P.phiTot hP t) (fun y => ((phiHomeomorph _ ht).symm y : P.TameBoundarySpace hP))
          (uSet _ t) univ) ∧
      ∀ Q' : MPolyfold (P.TameBoundarySpace hP),
        (∀ (t : BTriple (P.isCornerIndex_degIndex hP)) (ht : IsCenteredAt P.degIndex t.x t.V),
          letI := P.paracompactSpace_subtype t.θ
          Q'.IsScDiffeoOn (P.facePolyfold hP t.mem.1.1 t.mem_faces.1) (P.phiTot hP t)
            (fun y => ((phiHomeomorph _ ht).symm y : P.TameBoundarySpace hP)) (uSet _ t) univ) →
        Q'.atlas.Equiv (P.tameBoundaryPolyfold hP).atlas :=
  ⟨P.tameBoundaryPolyfold_isTame hP, P.tameBoundaryMap_isScSmooth hP,
    P.degIndex_tameBoundaryMap_sub_one hP,
    fun t ht => ⟨isOpen_uSet _ t, P.phi_isScDiffeoOn hP t ht⟩,
    fun Q' h => P.tameBoundaryPolyfold_unique hP Q' h⟩

/-! ### The tame boundary (Definition 2.7.14) and its iterates ((2.45)–(2.47)) -/

/-- A tame M-polyfold bundled with its underlying space, so that `X ↦ bX` can be iterated. -/
structure TameMPolyfoldBundle : Type (u + 1) where
  /-- The underlying space. -/
  carrier : Type u
  [top : TopologicalSpace carrier]
  [t2 : T2Space carrier]
  [para : ParacompactSpace carrier]
  /-- The M-polyfold structure. -/
  P : MPolyfold carrier
  isTame : P.IsTame

namespace TameMPolyfoldBundle

attribute [instance] top t2 para

/-- **2021 Definition 2.7.14, p. 84**: the tame boundary `bX` of `X`, with its tame M-polyfold
structure (Theorem 2.7.13 (2)). -/
def b (Y : TameMPolyfoldBundle.{u}) : TameMPolyfoldBundle.{u} :=
  ⟨Y.P.TameBoundarySpace Y.isTame, Y.P.tameBoundaryPolyfold Y.isTame,
    Y.P.tameBoundaryPolyfold_isTame Y.isTame⟩

/-- **2021 (2.45)**: `bᵏX`, with `b⁰X = X` and `bᵏX = b(bᵏ⁻¹X)`. -/
def iter (Y : TameMPolyfoldBundle.{u}) (k : ℕ) : TameMPolyfoldBundle.{u} := b^[k] Y

/-- **2021 (2.46), (2.47)**: `Bᵏ : bᵏX → X`, `B⁰ = Id_X`, `Bᵏ = B_X ∘ B_{bX} ∘ ⋯ ∘ B_{bᵏ⁻¹X}`. -/
def iterMap : ∀ (Y : TameMPolyfoldBundle.{u}) (k : ℕ), (Y.iter k).carrier → Y.carrier
  | _, 0 => id
  | Y, k + 1 => Y.P.tameBoundaryMap Y.isTame ∘ iterMap (b Y) k

@[simp] lemma iterMap_zero (Y : TameMPolyfoldBundle.{u}) : Y.iterMap 0 = id := rfl

lemma iterMap_succ (Y : TameMPolyfoldBundle.{u}) (k : ℕ) :
    Y.iterMap (k + 1) = Y.P.tameBoundaryMap Y.isTame ∘ (b Y).iterMap k := rfl

/-- `Bᵏ` is sc-smooth (2021 (2.46)). -/
theorem iterMap_isScSmooth : ∀ (Y : TameMPolyfoldBundle.{u}) (k : ℕ),
    (Y.iter k).P.IsScSmoothMap Y.P (Y.iterMap k)
  | _, 0 => isScSmoothMap_id
  | Y, k + 1 => (Y.P.tameBoundaryMap_isScSmooth Y.isTame).comp (iterMap_isScSmooth (b Y) k)

/-- `d_X(Bᵏ(p)) = d_{bᵏX}(p) + k` (Theorem 2.7.13 (4), iterated). -/
theorem degIndex_iterMap : ∀ (Y : TameMPolyfoldBundle.{u}) (k : ℕ) (p : (Y.iter k).carrier),
    Y.P.degIndex (Y.iterMap k p) = (Y.iter k).P.degIndex p + k
  | _, 0, _ => rfl
  | Y, k + 1, p => by
    have h1 := Y.P.degIndex_tameBoundaryMap Y.isTame ((b Y).iterMap k p)
    have h2 := degIndex_iterMap (b Y) k p
    exact (h1.trans (congrArg (· + 1) h2)).trans (Nat.add_assoc _ _ _)

/-- **2021 (2.46)**: the image of `Bᵏ : bᵏX → X` is the set of points of degeneracy index at least
`k`. -/
theorem range_iterMap : ∀ (Y : TameMPolyfoldBundle.{u}) (k : ℕ),
    range (Y.iterMap k) = {x | k ≤ Y.P.degIndex x}
  | _, 0 => by ext x; exact ⟨fun _ => Nat.zero_le _, fun _ => ⟨x, rfl⟩⟩
  | Y, k + 1 => by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      change k + 1 ≤ Y.P.degIndex (Y.iterMap (k + 1) p)
      rw [degIndex_iterMap]; omega
    · intro hx
      change k + 1 ≤ Y.P.degIndex x at hx
      have hxb : x ∈ range (Y.P.tameBoundaryMap Y.isTame) := by
        rw [range_tameBoundaryMap]; change 1 ≤ Y.P.degIndex x; omega
      obtain ⟨p, rfl⟩ := hxb
      have hp : k ≤ (b Y).P.degIndex p := by
        have := Y.P.degIndex_tameBoundaryMap Y.isTame p
        change k ≤ (Y.P.tameBoundaryPolyfold Y.isTame).degIndex p
        omega
      have : p ∈ range ((b Y).iterMap k) := by rw [range_iterMap (b Y) k]; exact hp
      obtain ⟨q, rfl⟩ := this
      exact ⟨q, rfl⟩

end TameMPolyfoldBundle

/-- **2021 Definition 2.7.14, p. 84** (new in the 2021 edition): the **tame boundary** of the tame
`X` is the diagram `B : bX → X`, `bX` with its tame M-polyfold structure and `B` sc-smooth with
image `∂X`. -/
theorem definition_2_7_14_2021 (hP : P.IsTame) :
    (P.tameBoundaryPolyfold hP).IsTame ∧
      (P.tameBoundaryPolyfold hP).IsScSmoothMap P (P.tameBoundaryMap hP) ∧
      range (P.tameBoundaryMap hP) = P.boundary :=
  ⟨P.tameBoundaryPolyfold_isTame hP, P.tameBoundaryMap_isScSmooth hP, P.range_tameBoundaryMap hP⟩

/-! ### Witnesses -/

/-- **Satisfiability of `BChartData`**: for the tame quadrant `[0,∞)ⁿ ⊕ W`, `n ≥ 1`, chart data
exist (the charts of `bX` cover the nonempty `bX`). -/
theorem quadrantPolyfold_bChartData_nonempty (n : ℕ) (W : ScBanach) (hn : 1 ≤ n) :
    Nonempty ((quadrantPolyfold n W).BChartData (quadrantPolyfold_isTame n W)) := by
  obtain ⟨p⟩ := quadrantPolyfold_tameBoundarySpace_nonempty n W hn
  obtain ⟨D, -⟩ := (quadrantPolyfold n W).exists_bChartData_mem (quadrantPolyfold_isTame n W) p
  exact ⟨D⟩

/-- **Non-vacuity of Theorem 2.7.13 (4)**: in `b([0,∞)ⁿ ⊕ W)` the `n` points over the corner `0`
have degeneracy index `n − 1`. -/
theorem quadrantPolyfold_degIndex_tameBoundary (n : ℕ) (W : ScBanach)
    (p : (quadrantPolyfold n W).TameBoundarySpace (quadrantPolyfold_isTame n W))
    (hp : (quadrantPolyfold n W).tameBoundaryMap (quadrantPolyfold_isTame n W) p =
      ⟨0, zero_mem_quadrant n W⟩) :
    ((quadrantPolyfold n W).tameBoundaryPolyfold (quadrantPolyfold_isTame n W)).degIndex p =
      n - 1 := by
  rw [← degIndex_tameBoundaryMap_sub_one, hp, quadrantPolyfold_degIndex_zero]

end MPolyfold

end Polyfold
