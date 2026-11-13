import Polyfold.Chapter4.A3BoundaryForms2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4, pp. 198–199
(2017 p. 150; preprint p. 168): forms on `∂X`, "which coincide on the intersection of local faces".

# Forms on `∂X`: agreement of `τ` over `B` gives agreement of `dτ`

`BoundaryForms2021` reads a form on `∂Xⁱ` as an sc-form `τ` on `bXⁱ` such that `τ` agrees over
`Bⁱ` **and** `dτ` agrees over `Bⁱ⁺¹`.  Here the second condition is proved from the first, so
that `Ωᵏ(∂Xⁱ)` is the set of sc-forms on `bXⁱ` that coincide on the intersections of local faces,
as in the text:

* `MPolyfold.isFaceCompatible_extD`: if `τ ∈ Ωᵏ(bXⁱ)` agrees over `Bⁱ`, then `dτ` agrees over
  `Bⁱ⁺¹`;
* `MPolyfold.bForms_eq_agreeForms`, `MPolyfold.mem_bForms_iff`: `τ ∈ Ωᵏ(∂Xⁱ)` iff `τ` agrees
  over `Bⁱ`.

No hypothesis is added: `X` is a tame M-polyfold.

## The proof

By `BundledMPolyfold.isAgreeingOver_extD` (file `A3BoundaryForms2021`) two facts about
`B : bX → X` are needed.

* `isTangentInjective_bdryMap`: `TB` is injective on the tangent spaces.  In a chart `χ_D` of `bX`
  and the chart `φ` of `X` it is built from, `B` is the inclusion `ι` of the extended face
  `{λ_i = 0}` (`tangentChartMap_bdryMap`).
* `hasCornerCover_bdryMap`: let `p, p' ∈ bX` lie over `x ∈ X`, with centred representatives
  `(x, V, θ)`, `(x, V', θ')`.  In a tame chart `φ` around `x` inside `V ∩ V'`, with tame retraction
  `r`, the faces `θ`, `θ'` are near `x` faces of the retract, in `{λ_i = 0}` and `{λ_j = 0}`, and
  `r ∘ P_i`, `r ∘ P_j` retract onto them (2021 Proposition 2.5.15; `P_i` kills the coordinate
  `i`).  So `γ = r ∘ P_i ∘ P_j`, on a relatively open neighbourhood `Z` of `φ(x)` in the partial
  quadrant, has values in both faces: `g = φ⁻¹ ∘ γ : Z → X` maps into `θ ∩ θ'`, and
  `G = Φ⁻¹_{(x,V,θ)} ∘ g`, `G' = Φ⁻¹_{(x,V',θ')} ∘ g` are sc-smooth maps `Z → bX` with
  `B ∘ G = g = B ∘ G'` (Theorem 2.7.13: `Φ` is an sc-diffeomorphism onto the face).
  A vector of `T_xX` in `TB(T_p bX) ∩ TB(T_{p'} bX)` is, in the chart, a vector
  `h ∈ T_{φ(x)}O` with `λ_i(h) = λ_j(h) = 0`; then `Dγ(φ(x)) h = Dr(φ(x)) h = h`.  This is the
  text's "intersection of local faces" on the tangent level: `TF ∩ TF'` is the tangent space of
  the corner stratum.  No centred chart is used, so `x` need not be a smooth point.
-/

open Set Function

noncomputable section

namespace Polyfold

/-! ### The projections `P_i` commute -/

section KillCoord

variable {E : ScBanach} {n : ℕ} {W : ScBanach}
  (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))

lemma killCoord_snd (i : Fin n) (z : E 0) : (T 0 (killCoord T i 0 z)).2 = (T 0 z).2 := by
  rw [killCoord_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- `P_i ∘ P_j = P_j ∘ P_i`. -/
lemma killCoord_comm (i j : Fin n) (z : E 0) :
    killCoord T i 0 (killCoord T j 0 z) = killCoord T j 0 (killCoord T i 0 z) := by
  apply (T 0).injective
  refine Prod.ext (funext fun l => ?_) ?_
  · rw [killCoord_coord, killCoord_coord, killCoord_coord, killCoord_coord]
    split_ifs <;> rfl
  · rw [killCoord_snd, killCoord_snd, killCoord_snd, killCoord_snd]

/-- `P_i` fixes the level-one lift of a point with `λ_i = 0`. -/
lemma killCoord_one_eq_self {i : Fin n} {z : E 1} (hz : (T 0 (E.toBase 1 z)).1 i = 0) :
    killCoord T i 1 z = z := by
  apply E.toBase_injective 1
  exact ((killCoord T i).toBase_comm 1 z).trans (killCoord_eq_self hz)

end KillCoord

namespace MPolyfold

open TameBoundary BundledMPolyfold

/-! ### The tangent map of a map which is linear in charts -/

section Linear

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {f : X → Y}

/-- If `f` is the sc-operator `L` in the charts `χ`, `φ`, then `Tf` is `(L, L)` in the tangent
charts. -/
theorem tangentChartMap_tangentMap_of_linear (hf : P.IsScSmoothMap Q f) {χ : MChart X}
    (hχ : P.IsChart χ) {φ : MChart Y} (hφ : Q.IsChart φ) (L : ScOperator χ.model.E φ.model.E)
    (hmaps : ∀ x ∈ χ.source, f x ∈ φ.source) (hL : ∀ x ∈ χ.source, φ (f x) = L 0 (χ x))
    {α : P.TangentSpace} (hα : α ∈ tangentChartSet χ) :
    tangentChartMap hφ (tangentMap hf α) =
      (L 1 (tangentChartMap hχ α).1, L 0 (tangentChartMap hχ α).2) := by
  have hfd : TangentPre.fdom χ f φ = χ.source := by
    ext x; exact ⟨fun h => h.1, fun h => ⟨h, hmaps x h⟩⟩
  rw [tangentChartMap_tangentMap hf hχ hφ hα (hmaps _ hα), hfd, χ.image_source]
  have hmem := tangentChartMap_mem hχ hα
  have heq : EqOn (L 0) (φ ∘ f ∘ χ.symm) χ.model.O := by
    intro z hz
    have hz' : χ.symm z ∈ χ.source := χ.symm_mapsTo hz
    change L 0 z = φ (f (χ.symm z))
    rw [hL _ hz', χ.apply_symm_apply hz]
  have hLs : IsScSmoothRetractMap χ.model.E χ.model.C χ.model.O φ.model.E φ.model.C univ (L 0) :=
    L.isScSmoothRetractMap χ.model.isScRetract (mapsTo_univ _ _)
  rw [← retractTangentMap_congr hLs χ.model.isScRetract heq hmem]
  exact retractTangentMap_scOperator L χ.model.isScRetract (O' := univ) (mapsTo_univ _ _) hmem

end Linear

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  (hP : P.IsTame)

/-! ### `TB` is injective on the tangent spaces -/

/-- **`TB` in the charts `χ_D` of `bX` and `φ` of `X`** is the inclusion `ι` of the extended face
`{λ_i = 0}` on both components. -/
theorem tangentChartMap_bdryMap (D : P.BChartData hP)
    {a : (P.tameBoundaryPolyfold hP).TangentSpace} (ha : a ∈ tangentChartSet D.chart) :
    tangentChartMap D.isChart (tangentMap (P.tameBoundaryMap_isScSmooth hP) a) =
      (faceIncl D.T D.i 1 (tangentChartMap (P.isChart_chart D) a).1,
        faceIncl D.T D.i 0 (tangentChartMap (P.isChart_chart D) a).2) :=
  tangentChartMap_tangentMap_of_linear (P.tameBoundaryMap_isScSmooth hP) (P.isChart_chart D)
    D.isChart (faceIncl D.T D.i) (fun _ hp => D.bMap_mem_source hp)
    (fun _ hp => (D.incl_chart hp).symm) ha

/-- `TB` is injective on the tangent spaces of `bX`. -/
theorem tangentMap_tameBoundaryMap_injOn {a a' : (P.tameBoundaryPolyfold hP).TangentSpace}
    (hpr : (P.tameBoundaryPolyfold hP).tangentProj a = (P.tameBoundaryPolyfold hP).tangentProj a')
    (h : tangentMap (P.tameBoundaryMap_isScSmooth hP) a =
      tangentMap (P.tameBoundaryMap_isScSmooth hP) a') : a = a' := by
  obtain ⟨D, hp⟩ := P.exists_bChartData_mem hP
    ((P.tameBoundaryPolyfold hP).levelVal 1 ((P.tameBoundaryPolyfold hP).tangentProj a))
  have ha : a ∈ tangentChartSet (P := P.tameBoundaryPolyfold hP) D.chart := hp
  have ha' : a' ∈ tangentChartSet (P := P.tameBoundaryPolyfold hP) D.chart := by
    change (P.tameBoundaryPolyfold hP).levelVal 1 ((P.tameBoundaryPolyfold hP).tangentProj a') ∈
      D.chart.source
    rw [← hpr]; exact hp
  have h1 := tangentChartMap_bdryMap hP D ha
  have h2 := tangentChartMap_bdryMap hP D ha'
  have h3 : tangentChartMap D.isChart (tangentMap (P.tameBoundaryMap_isScSmooth hP) a) =
      tangentChartMap D.isChart (tangentMap (P.tameBoundaryMap_isScSmooth hP) a') :=
    congrArg _ h
  rw [h1, h2] at h3
  refine tangentChartMap_injOn (P.isChart_chart D) ha ha' (Prod.ext ?_ ?_)
  · rw [tangentChartMap_fst (P.isChart_chart D) ha, tangentChartMap_fst (P.isChart_chart D) ha',
      hpr]
  · have h4 := congrArg (faceProj D.T D.i 0) (congrArg Prod.snd h3)
    exact (faceProj_faceIncl D.T D.i _).symm.trans (h4.trans (faceProj_faceIncl D.T D.i _))

/-- **`TB : T_p(bX) → T_{B(p)}X` is injective.** -/
theorem isTangentInjective_bdryMap : IsTangentInjective (bdryMap hP) :=
  fun _ _ hpr h => tangentMap_tameBoundaryMap_injOn hP hpr h

/-! ### A face of a centred triple in a given tame chart -/

/-- **The face `θ` of a triple in a given tame chart** (the construction of the charts of `bX`,
`exists_bChartData`, for a prescribed tame chart `φ` of `X` inside `V`): near `y ∈ θ` the face is
the zero set of a coordinate `λ_i`, the chart data of `bX` exist with this `φ`, and there is a
retraction `s = r ∘ P_i` (2021 Proposition 2.5.15) whose values near `φ(y)` lie in `φ(θ)`. -/
theorem exists_face_chartData (t : BTriple (P.isCornerIndex_degIndex hP)) {y : X} (hy : y ∈ t.θ)
    {φ : MChart X} (hφ : P.IsChart φ) (hyφ : y ∈ φ.source) (hsrc : φ.source ⊆ t.V)
    (R : ScRetraction φ.model.E φ.model.C) (hRO : R.retract = φ.model.O) {k : ℕ} {W : ScBanach}
    {T : ScIso φ.model.E ((ScBanach.const (Fin (k + 1) → ℝ)).prod W)}
    (hT : φ.model.C = T 0 ⁻¹' quadrant (k + 1) W 0) (hR : R.IsTameWith T) :
    ∃ (i : Fin (k + 1)) (B : Set (φ.model.E 0)), IsOpen B ∧ φ y ∈ B ∧
      (∀ y' ∈ t.θ ∩ (φ.source ∩ φ ⁻¹' B), (T 0 (φ y')).1 i = 0) ∧
      IsTameRetract ((ScBanach.const (Fin k → ℝ)).prod W) (quadrant k W 0)
        (faceProj T i 0 '' (φ '' (t.θ ∩ (φ.source ∩ φ ⁻¹' B)))) ∧
      (∀ y' ∈ t.θ ∩ (φ.source ∩ φ ⁻¹' B), P.degIndex y' =
        Polyfold.degIndex ((ScBanach.const (Fin k → ℝ)).prod W) (quadrant k W 0)
          (faceProj T i 0 (φ y')) + 1) ∧
      ∃ S : ScRetraction φ.model.E φ.model.C,
        φ y ∈ S.U ∧ EqOn S (R ∘ killCoord T i 0) S.U ∧
        ∀ z ∈ S.U, S z ∈ B → S z ∈ φ.model.O ∧ φ.symm (S z) ∈ t.θ := by
  classical
  have hyV : y ∈ t.V := t.mem_faces.1.subset hy
  obtain ⟨Floc, hFloc, B, hB, hyB, hEq⟩ := P.exists_localFace_of_faceIn (t.mem.1.1.2 y hyV)
    ⟨t.mem_faces.1, hy⟩ hφ hyφ hsrc R hRO hT hR
  obtain ⟨i₀, hFi₀, S, hFS, -, hSret, hSeq⟩ := proposition_2_5_15 hT hR hFloc
  obtain ⟨i, hFi, R', hR'tame, hR'ret, hdeg'⟩ := proposition_2_5_15_tameModel hT hR hFloc
  have hii : i₀ = i := by
    obtain ⟨x0, hx0S, hx0⟩ := hFloc
    have hx0F : x0 ∈ Floc := hx0 ▸ ⟨subset_closure (mem_connectedComponentIn hx0S), hx0S.1⟩
    have h1 := zeroSet_eq_singleton (faceStratum_degIndexWith hT hx0S) (hFi₀ hx0F)
    have h2 := zeroSet_eq_singleton (faceStratum_degIndexWith hT hx0S) (hFi hx0F)
    exact Finset.singleton_injective (h1.symm.trans h2)
  subst hii
  have hT' : quadrant k W 0 = (ScIso.refl ((ScBanach.const (Fin k → ℝ)).prod W)) 0 ⁻¹'
      quadrant k W 0 := by ext; rfl
  set V₁ := φ.source ∩ φ ⁻¹' B with hV₁def
  have hFV : φ '' (t.θ ∩ V₁) = Floc ∩ B := by
    rw [← hEq]
    ext z
    constructor
    · rintro ⟨y, ⟨hyF, hyV, hyB⟩, rfl⟩; exact ⟨⟨y, ⟨hyF, hyV⟩, rfl⟩, hyB⟩
    · rintro ⟨⟨y, ⟨hyF, hyV⟩, rfl⟩, hyB⟩; exact ⟨y, ⟨hyF, hyV, hyB⟩, rfl⟩
  have hmemF : ∀ y' ∈ t.θ ∩ V₁, φ y' ∈ Floc := fun y' hy' => by
    have : φ y' ∈ φ '' (t.θ ∩ V₁) := ⟨y', hy', rfl⟩
    rw [hFV] at this; exact this.1
  set ι := faceIncl T i₀ with hι
  set π := faceProj T i₀ with hπ
  set Wι := ι 0 ⁻¹' B with hWι
  have hWιo : IsOpen Wι := hB.preimage (ι 0).continuous
  have hret_eq : (R'.restrict hWιo).retract = π 0 '' (φ '' (t.θ ∩ V₁)) := by
    rw [R'.restrict_retract, hR'ret, hFV]
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hyB⟩
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      have : ι 0 (π 0 y) = y := faceIncl_faceProj T i₀ (hFi hy)
      rw [← this]; exact hyB
    · rintro ⟨y, ⟨hy, hyB⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, ?_⟩
      change ι 0 (π 0 y) ∈ B
      rw [faceIncl_faceProj T i₀ (hFi hy)]; exact hyB
  have hyF : φ y ∈ Floc := hmemF y ⟨hy, hyφ, hyB⟩
  refine ⟨i₀, B, hB, hyB, fun y' hy' => hFi (hmemF y' hy'),
    ⟨R'.restrict hWιo, hret_eq, (hR'tame.restrict hWιo).isTame hT'⟩, fun y' hy' => ?_,
    S, hFS hyF, hSeq, fun z hz hzB => ?_⟩
  · rw [P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR hy'.2.1, chartDegIndex]
    exact (hdeg' _ (hmemF y' hy')).symm
  · have hzF : S z ∈ Floc ∩ B := ⟨hSret ▸ S.apply_mem_retract hz, hzB⟩
    rw [← hEq] at hzF
    obtain ⟨⟨y', ⟨hy'θ, hy's⟩, hy'eq⟩, -⟩ := hzF
    rw [← hy'eq, φ.symm_apply_apply hy's]
    exact ⟨φ.mapsTo_model y' hy's, hy'θ⟩

/-! ### The corner chart of two faces through a point -/

/-- Two centred triples `(x, V, θ)`, `(x, V', θ')` over the same point `x`, a tame chart `φ`
around `x` with tame retraction `r`, and the data of `exists_face_chartData` for both faces:
coordinates `i`, `j` with `θ ⊆ {λ_i = 0}`, `θ' ⊆ {λ_j = 0}` near `x`, and the retractions
`s = r ∘ P_i`, `s' = r ∘ P_j`. -/
structure CornerChart (hP : P.IsTame) where
  t : BTriple (P.isCornerIndex_degIndex hP)
  t' : BTriple (P.isCornerIndex_degIndex hP)
  centred : IsCenteredAt P.degIndex t.x t.V
  centred' : IsCenteredAt P.degIndex t'.x t'.V
  x_eq : t'.x = t.x
  φ : MChart X
  isChart : P.IsChart φ
  mem_source : t.x ∈ φ.source
  R : ScRetraction φ.model.E φ.model.C
  retract_eq : R.retract = φ.model.O
  k : ℕ
  W : ScBanach
  T : ScIso φ.model.E ((ScBanach.const (Fin (k + 1) → ℝ)).prod W)
  hT : φ.model.C = T 0 ⁻¹' quadrant (k + 1) W 0
  i : Fin (k + 1)
  j : Fin (k + 1)
  B : Set (φ.model.E 0)
  B' : Set (φ.model.E 0)
  isOpen_B : IsOpen B
  isOpen_B' : IsOpen B'
  mem_B : φ t.x ∈ B
  mem_B' : φ t.x ∈ B'
  coord_eq : ∀ y ∈ t.θ ∩ (φ.source ∩ φ ⁻¹' B), (T 0 (φ y)).1 i = 0
  coord_eq' : ∀ y ∈ t'.θ ∩ (φ.source ∩ φ ⁻¹' B'), (T 0 (φ y)).1 j = 0
  isTameRetract : IsTameRetract ((ScBanach.const (Fin k → ℝ)).prod W) (quadrant k W 0)
    (faceProj T i 0 '' (φ '' (t.θ ∩ (φ.source ∩ φ ⁻¹' B))))
  isTameRetract' : IsTameRetract ((ScBanach.const (Fin k → ℝ)).prod W) (quadrant k W 0)
    (faceProj T j 0 '' (φ '' (t'.θ ∩ (φ.source ∩ φ ⁻¹' B'))))
  degIndex_eq : ∀ y ∈ t.θ ∩ (φ.source ∩ φ ⁻¹' B), P.degIndex y =
    Polyfold.degIndex ((ScBanach.const (Fin k → ℝ)).prod W) (quadrant k W 0)
      (faceProj T i 0 (φ y)) + 1
  degIndex_eq' : ∀ y ∈ t'.θ ∩ (φ.source ∩ φ ⁻¹' B'), P.degIndex y =
    Polyfold.degIndex ((ScBanach.const (Fin k → ℝ)).prod W) (quadrant k W 0)
      (faceProj T j 0 (φ y)) + 1
  S : ScRetraction φ.model.E φ.model.C
  S' : ScRetraction φ.model.E φ.model.C
  mem_S : φ t.x ∈ S.U
  mem_S' : φ t.x ∈ S'.U
  S_eq : EqOn S (R ∘ killCoord T i 0) S.U
  S'_eq : EqOn S' (R ∘ killCoord T j 0) S'.U
  S_face : ∀ z ∈ S.U, S z ∈ B → S z ∈ φ.model.O ∧ φ.symm (S z) ∈ t.θ
  S'_face : ∀ z ∈ S'.U, S' z ∈ B' → S' z ∈ φ.model.O ∧ φ.symm (S' z) ∈ t'.θ

namespace CornerChart

variable {hP} (c : P.CornerChart hP)

/-- The chart data of `bX` at `[x, V, θ]` built on the chart `φ`. -/
def D : P.BChartData hP :=
  ⟨c.t, c.centred, c.φ, c.isChart, c.φ.source ∩ c.φ ⁻¹' c.B,
    c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source c.isOpen_B,
    inter_subset_left, c.k, c.W, c.T, c.i, c.coord_eq, c.isTameRetract, c.degIndex_eq⟩

/-- The chart data of `bX` at `[x, V', θ']` built on the same chart `φ`. -/
def D' : P.BChartData hP :=
  ⟨c.t', c.centred', c.φ, c.isChart, c.φ.source ∩ c.φ ⁻¹' c.B',
    c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source c.isOpen_B',
    inter_subset_left, c.k, c.W, c.T, c.j, c.coord_eq', c.isTameRetract', c.degIndex_eq'⟩

/-- The point `φ(x)`. -/
def e : c.φ.model.E 0 := c.φ c.t.x

/-- `P_i ∘ P_j`, the sc-projection onto `{λ_i = λ_j = 0}`. -/
def K : ScOperator c.φ.model.E c.φ.model.E := (killCoord c.T c.i).comp (killCoord c.T c.j)

lemma K_apply (z : c.φ.model.E 0) :
    c.K 0 z = killCoord c.T c.i 0 (killCoord c.T c.j 0 z) := rfl

lemma K_mem_C {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.C) : c.K 0 z ∈ c.φ.model.C :=
  killCoord_mem c.hT c.i (killCoord_mem c.hT c.j hz)

lemma coord_e : (c.T 0 c.e).1 c.i = 0 :=
  c.coord_eq _ ⟨c.t.mem_faces.2, c.mem_source, c.mem_B⟩

lemma coord_e' : (c.T 0 c.e).1 c.j = 0 :=
  c.coord_eq' _ ⟨c.x_eq ▸ c.t'.mem_faces.2, c.mem_source, c.mem_B'⟩

lemma killCoord_e : killCoord c.T c.i 0 c.e = c.e := killCoord_eq_self c.coord_e

lemma killCoord_e' : killCoord c.T c.j 0 c.e = c.e := killCoord_eq_self c.coord_e'

lemma K_e : c.K 0 c.e = c.e := by rw [K_apply, killCoord_e', killCoord_e]

lemma e_mem_O : c.e ∈ c.φ.model.O := c.φ.mapsTo_model _ c.mem_source

lemma e_mem_retract : c.e ∈ c.R.retract := c.retract_eq ▸ c.e_mem_O

lemma R_e : c.R c.e = c.e := c.R.apply_eq_self_of_mem_retract c.e_mem_retract

/-- The domain `Z` of the corner map: the points `z` of the partial quadrant near `φ(x)` for
which `r(P_i P_j z)` is defined and lies in both faces. -/
def U : Set (c.φ.model.E 0) :=
  {z | z ∈ c.φ.model.C ∧ c.K 0 z ∈ c.R.U ∧ killCoord c.T c.j 0 z ∈ c.S.U ∧
    killCoord c.T c.i 0 z ∈ c.S'.U ∧ c.R (c.K 0 z) ∈ c.B ∩ c.B'}

lemma e_mem_U : c.e ∈ c.U := by
  refine ⟨c.R.U_subset_C (c.R.retract_subset c.e_mem_retract), ?_, ?_, ?_, ?_⟩
  · rw [K_e]; exact c.R.retract_subset c.e_mem_retract
  · rw [killCoord_e']; exact c.mem_S
  · rw [killCoord_e]; exact c.mem_S'
  · rw [K_e, R_e]; exact ⟨c.mem_B, c.mem_B'⟩

lemma nonempty_U : c.U.Nonempty := ⟨c.e, c.e_mem_U⟩

/-- `Z` is relatively open in the partial quadrant. -/
theorem isRelOpen_U : IsRelOpenInQuadrant c.φ.model.E c.φ.model.C c.U := by
  refine ⟨c.R.relOpen.isPartialQuadrant, ?_⟩
  obtain ⟨WR, hWR, hWReq⟩ := c.R.relOpen.relOpen
  obtain ⟨WS, hWS, hWSeq⟩ := c.S.relOpen.relOpen
  obtain ⟨WS', hWS', hWS'eq⟩ := c.S'.relOpen.relOpen
  have hRc : ContinuousOn c.R c.R.U := c.R.isSc1.isSc0.continuousOn_base
  set s : Set (c.φ.model.E 0) := {z | c.K 0 z ∈ c.R.U} with hs
  have hf : ContinuousOn (fun z => c.R (c.K 0 z)) s :=
    hRc.comp (c.K 0).continuous.continuousOn fun z hz => hz
  obtain ⟨u, hu, hueq⟩ := (continuousOn_iff'.1 hf) (c.B ∩ c.B') (c.isOpen_B.inter c.isOpen_B')
  refine ⟨c.K 0 ⁻¹' WR ∩ killCoord c.T c.j 0 ⁻¹' WS ∩ killCoord c.T c.i 0 ⁻¹' WS' ∩ u,
    (((hWR.preimage (c.K 0).continuous).inter (hWS.preimage (killCoord c.T c.j 0).continuous)).inter
      (hWS'.preimage (killCoord c.T c.i 0).continuous)).inter hu, ?_⟩
  ext z
  constructor
  · rintro ⟨hzC, hzR, hzS, hzS', hzB⟩
    have hzu : z ∈ u := ((Set.ext_iff.1 hueq z).1 ⟨hzB, hzR⟩).1
    exact ⟨⟨⟨⟨(hWReq ▸ hzR : c.K 0 z ∈ WR ∩ c.φ.model.C).1,
      (hWSeq ▸ hzS : killCoord c.T c.j 0 z ∈ WS ∩ c.φ.model.C).1⟩,
      (hWS'eq ▸ hzS' : killCoord c.T c.i 0 z ∈ WS' ∩ c.φ.model.C).1⟩, hzu⟩, hzC⟩
  · rintro ⟨⟨⟨⟨hzR, hzS⟩, hzS'⟩, hzu⟩, hzC⟩
    have hzR' : c.K 0 z ∈ c.R.U := hWReq ▸ ⟨hzR, c.K_mem_C hzC⟩
    have hzB : z ∈ (fun z => c.R (c.K 0 z)) ⁻¹' (c.B ∩ c.B') ∩ s :=
      (Set.ext_iff.1 hueq z).2 ⟨hzu, hzR'⟩
    exact ⟨hzC, hzR', hWSeq ▸ ⟨hzS, killCoord_mem c.hT c.j hzC⟩,
      hWS'eq ▸ ⟨hzS', killCoord_mem c.hT c.i hzC⟩, hzB.1⟩

/-- The corner map in the chart: `γ = r ∘ P_i ∘ P_j`. -/
def γ (z : c.φ.model.E 0) : c.φ.model.E 0 := c.R (c.K 0 z)

lemma γ_e : c.γ c.e = c.e := by rw [γ, K_e, R_e]

/-- `γ` has values in the retract, and `φ⁻¹ ∘ γ` in both faces. -/
theorem γ_mem {z : c.φ.model.E 0} (hz : z ∈ c.U) :
    c.γ z ∈ c.φ.model.O ∧ c.φ.symm (c.γ z) ∈ c.t.θ ∧ c.φ.symm (c.γ z) ∈ c.t'.θ := by
  obtain ⟨-, -, hzS, hzS', hzB, hzB'⟩ := hz
  have h1 : c.S (killCoord c.T c.j 0 z) = c.γ z := c.S_eq hzS
  have h2 : c.S' (killCoord c.T c.i 0 z) = c.γ z := by
    rw [c.S'_eq hzS', γ, K_apply, killCoord_comm]; rfl
  have h3 := c.S_face _ hzS (h1 ▸ hzB)
  have h4 := c.S'_face _ hzS' (h2 ▸ hzB')
  rw [h1] at h3
  rw [h2] at h4
  exact ⟨h3.1, h3.2, h4.2⟩

/-- `γ : Z → O` is sc-smooth between the retracts. -/
theorem isScSmoothRetractMap_γ :
    IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.U c.φ.model.E c.φ.model.C c.φ.model.O c.γ :=
  c.retract_eq ▸ c.R.isScSmoothRetractMap.comp
    (c.K.isScSmoothRetractMap (C₁ := c.φ.model.C) c.isRelOpen_U.isScRetract (O₁ := c.R.U)
      fun _ hz => hz.2.1) c.R.relOpen.isScRetract

/-! #### The M-polyfold `Z` and the maps `G, G' : Z → bX` -/

/-- `Z` as an M-polyfold with one chart. -/
abbrev PZ : MPolyfold c.U := c.isRelOpen_U.toMPolyfold c.nonempty_U

/-- The chart `id` of `Z`. -/
abbrev ζ : MChart c.U := (LocalModel.ofRelOpen c.isRelOpen_U).selfChart c.nonempty_U

theorem isChart_ζ : c.PZ.IsChart c.ζ := c.isRelOpen_U.selfChart_isChart c.nonempty_U

open scoped Classical in
lemma ζ_symm_apply {z : c.φ.model.E 0} (hz : z ∈ c.U) : c.ζ.symm z = ⟨z, hz⟩ := by
  change (if h : z ∈ (LocalModel.ofRelOpen c.isRelOpen_U).O then
    (⟨z, h⟩ : (LocalModel.ofRelOpen c.isRelOpen_U).O) else _) = _
  exact dif_pos hz

/-- The point of `Z` over `x`. -/
def z₀ : c.U := ⟨c.e, c.e_mem_U⟩

/-- `g = φ⁻¹ ∘ γ` as a map into the face `θ`. -/
def gθ (z : c.U) : c.t.θ := ⟨c.φ.symm (c.γ z), (c.γ_mem z.2).2.1⟩

/-- `g = φ⁻¹ ∘ γ` as a map into the face `θ'`. -/
def gθ' (z : c.U) : c.t'.θ := ⟨c.φ.symm (c.γ z), (c.γ_mem z.2).2.2⟩

/-- `G = Φ⁻¹_{(x,V,θ)} ∘ g : Z → bX`. -/
def G (z : c.U) : P.TameBoundarySpace hP :=
  ((phiHomeomorph _ c.centred).symm (c.gθ z) : P.TameBoundarySpace hP)

/-- `G' = Φ⁻¹_{(x,V',θ')} ∘ g : Z → bX`. -/
def G' (z : c.U) : P.TameBoundarySpace hP :=
  ((phiHomeomorph _ c.centred').symm (c.gθ' z) : P.TameBoundarySpace hP)

lemma bMap_G (z : c.U) : bMap (P.isCornerIndex_degIndex hP) (c.G z) = c.φ.symm (c.γ z) :=
  bMap_phiHomeomorph_symm _ _

lemma bMap_G' (z : c.U) : bMap (P.isCornerIndex_degIndex hP) (c.G' z) = c.φ.symm (c.γ z) :=
  bMap_phiHomeomorph_symm _ _

lemma continuous_γ : Continuous fun z : c.U => c.γ z :=
  c.R.isSc1.isSc0.continuousOn_base.comp_continuous
    ((c.K 0).continuous.comp continuous_subtype_val) fun z => z.2.2.1

lemma continuous_G : Continuous c.G := by
  have h1 : Continuous c.gθ :=
    (c.φ.continuousOn_invFun.comp_continuous c.continuous_γ fun z => (c.γ_mem z.2).1).subtype_mk _
  exact continuous_subtype_val.comp ((phiHomeomorph _ c.centred).symm.continuous.comp h1)

lemma continuous_G' : Continuous c.G' := by
  have h1 : Continuous c.gθ' :=
    (c.φ.continuousOn_invFun.comp_continuous c.continuous_γ fun z => (c.γ_mem z.2).1).subtype_mk _
  exact continuous_subtype_val.comp ((phiHomeomorph _ c.centred').symm.continuous.comp h1)

lemma G_mem_source (z : c.U) : c.G z ∈ c.D.chart.source := by
  refine ⟨phiHomeomorph_symm_mem _ _, ?_⟩
  change bMap _ (c.G z) ∈ c.φ.source ∩ c.φ ⁻¹' c.B
  rw [bMap_G]
  refine ⟨c.φ.symm_mapsTo (c.γ_mem z.2).1, ?_⟩
  rw [mem_preimage, c.φ.apply_symm_apply (c.γ_mem z.2).1]
  exact z.2.2.2.2.2.1

lemma G'_mem_source (z : c.U) : c.G' z ∈ c.D'.chart.source := by
  refine ⟨phiHomeomorph_symm_mem _ _, ?_⟩
  change bMap _ (c.G' z) ∈ c.φ.source ∩ c.φ ⁻¹' c.B'
  rw [bMap_G']
  refine ⟨c.φ.symm_mapsTo (c.γ_mem z.2).1, ?_⟩
  rw [mem_preimage, c.φ.apply_symm_apply (c.γ_mem z.2).1]
  exact z.2.2.2.2.2.2

lemma φ_bMap_G (z : c.U) : c.φ (bMap (P.isCornerIndex_degIndex hP) (c.G z)) = c.γ z := by
  rw [bMap_G, c.φ.apply_symm_apply (c.γ_mem z.2).1]

lemma φ_bMap_G' (z : c.U) : c.φ (bMap (P.isCornerIndex_degIndex hP) (c.G' z)) = c.γ z := by
  rw [bMap_G', c.φ.apply_symm_apply (c.γ_mem z.2).1]

end CornerChart

/-- A map `G : Z → bX` from an M-polyfold with a global chart `ζ`, with values in the domain of a
chart `χ_D` of `bX`, is sc-smooth as soon as `φ ∘ B ∘ G` is sc-smooth in the chart `ζ` (then
`χ_D ∘ G = π ∘ φ ∘ B ∘ G`). -/
theorem isScSmoothMap_of_chart_bdry (D : P.BChartData hP) {Z : Type*} [TopologicalSpace Z]
    [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z} {ζ : MChart Z} (hζ : PZ.IsChart ζ)
    (hsrc : ζ.source = univ) {γ : ζ.model.E 0 → D.φ.model.E 0}
    (hγ : IsScSmoothRetractMap ζ.model.E ζ.model.C ζ.model.O D.φ.model.E D.φ.model.C
      D.φ.model.O γ)
    {G : Z → P.TameBoundarySpace hP} (hGc : Continuous G) (hGs : ∀ z, G z ∈ D.chart.source)
    (hG : ∀ z, D.φ (bMap (P.isCornerIndex_degIndex hP) (G z)) = γ (ζ z)) :
    PZ.IsScSmoothMap (P.tameBoundaryPolyfold hP) G := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ hGc.continuousOn fun x _ =>
    ⟨ζ, D.chart, univ, hζ, P.isChart_chart D, isOpen_univ, mem_univ x,
      fun z _ => ⟨mem_univ z, hsrc ▸ mem_univ z⟩, fun z _ => hGs z, ?_⟩
  have hO : ζ '' univ = ζ.model.O := by rw [← hsrc]; exact ζ.image_source
  rw [hO]
  have h := ((faceProj D.T D.i).isScSmoothRetractMap (C₁ := D.chart.model.C)
    D.φ.model.isScRetract (O₁ := univ) (mapsTo_univ _ _)).comp hγ D.φ.model.isScRetract
  have heq : EqOn (faceProj D.T D.i 0 ∘ γ) (D.chart ∘ G ∘ ζ.symm) ζ.model.O := fun z hz => by
    change faceProj D.T D.i 0 (γ z) = faceProj D.T D.i 0 (D.φ (bMap _ (G (ζ.symm z))))
    rw [hG, ζ.apply_symm_apply hz]
  exact ⟨fun z _ => D.chart_mem_O (hGs _), (h.congr heq).comp_isScSmooth⟩

namespace CornerChart

variable {hP} (c : P.CornerChart hP)

/-- **`G : Z → bX` is sc-smooth.** -/
theorem isScSmoothMap_G : c.PZ.IsScSmoothMap (P.tameBoundaryPolyfold hP) c.G :=
  isScSmoothMap_of_chart_bdry hP c.D c.isChart_ζ rfl c.isScSmoothRetractMap_γ c.continuous_G
    c.G_mem_source c.φ_bMap_G

/-- **`G' : Z → bX` is sc-smooth.** -/
theorem isScSmoothMap_G' : c.PZ.IsScSmoothMap (P.tameBoundaryPolyfold hP) c.G' :=
  isScSmoothMap_of_chart_bdry hP c.D' c.isChart_ζ rfl c.isScSmoothRetractMap_γ c.continuous_G'
    c.G'_mem_source c.φ_bMap_G'

lemma tameBoundaryMap_G (z : c.U) : P.tameBoundaryMap hP (c.G z) = c.φ.symm (c.γ z) := c.bMap_G z

lemma tameBoundaryMap_G' (z : c.U) : P.tameBoundaryMap hP (c.G' z) = c.φ.symm (c.γ z) :=
  c.bMap_G' z

lemma γ_z₀ : c.γ (c.z₀ : c.φ.model.E 0) = c.e := c.γ_e

lemma G_z₀ : c.G c.z₀ = c.t.cls := by
  have h : c.gθ c.z₀ = ⟨bMap _ c.t.cls, bMap_mem_of_mem_uSet _ (cls_mem_uSet _ c.t)⟩ :=
    Subtype.ext (by
      change c.φ.symm (c.γ c.e) = c.t.x
      rw [γ_e]; exact c.φ.symm_apply_apply c.mem_source)
  rw [G, h, phiHomeomorph_symm_bMap c.centred (cls_mem_uSet _ c.t)]

lemma G'_z₀ : c.G' c.z₀ = c.t'.cls := by
  have h : c.gθ' c.z₀ = ⟨bMap _ c.t'.cls, bMap_mem_of_mem_uSet _ (cls_mem_uSet _ c.t')⟩ :=
    Subtype.ext (by
      change c.φ.symm (c.γ c.e) = c.t'.x
      rw [γ_e, c.x_eq]; exact c.φ.symm_apply_apply c.mem_source)
  rw [G', h, phiHomeomorph_symm_bMap c.centred' (cls_mem_uSet _ c.t')]

/-- `B ∘ G : Z → X`, sc-smooth. -/
theorem isScSmoothMap_BG : c.PZ.IsScSmoothMap P (P.tameBoundaryMap hP ∘ c.G) :=
  (P.tameBoundaryMap_isScSmooth hP).comp c.isScSmoothMap_G

lemma z₀_mem_levelSet {m : ℕ} (hm : c.t.x ∈ P.levelSet m) :
    c.z₀ ∈ c.PZ.levelSet m := by
  rw [c.PZ.mem_levelSet_iff c.isChart_ζ (mem_univ _)]
  exact (P.mem_levelSet_iff c.isChart c.mem_source).1 hm

/-! #### The tangent vectors of both faces come from `Z` -/

/-- **`T(F ∩ F') = TF ∩ TF'` at `x`**: a vector `ε ∈ T_xX` whose representative `h` in the chart
`φ` satisfies `λ_i(h) = λ_j(h) = 0` is `T(B ∘ G) v` for the vector `v ∈ T_{z₀}Z` with the same
representative; `Dγ(φ(x)) h = Dr(φ(x)) (P_i P_j h) = h`. -/
theorem exists_tangent {ε : P.TangentSpace} (hε : P.levelVal 1 (P.tangentProj ε) = c.t.x)
    (hi : (c.T 0 (tangentChartMap c.isChart ε).2).1 c.i = 0)
    (hj : (c.T 0 (tangentChartMap c.isChart ε).2).1 c.j = 0) :
    ∃ v : c.PZ.TangentSpace, c.PZ.levelVal 1 (c.PZ.tangentProj v) = c.z₀ ∧
      tangentChartMap c.isChart_ζ v = tangentChartMap c.isChart ε ∧
      tangentMap c.isScSmoothMap_BG v = ε := by
  set q := tangentChartMap c.isChart ε with hq
  have hεs : ε ∈ tangentChartSet c.φ := by
    change P.levelVal 1 (P.tangentProj ε) ∈ c.φ.source
    rw [hε]; exact c.mem_source
  have hqO : q ∈ retractTangent c.φ.model.E c.φ.model.C c.φ.model.O :=
    tangentChartMap_mem c.isChart hεs
  have hq1 : c.φ.model.E.toBase 1 q.1 = c.e := by
    rw [hq, tangentChartMap_fst c.isChart hεs, P.toBase_levelLift c.isChart hεs (levelVal_mem _),
      hε]
    rfl
  have hqR : q ∈ c.R.tangent := by
    rw [← retractTangent_eq, c.retract_eq]; exact hqO
  have hqs : q ∈ c.φ.model.E.tangentSet c.U := by
    change c.φ.model.E.toBase 1 q.1 ∈ c.U
    rw [hq1]; exact c.e_mem_U
  have hqU : q ∈ retractTangent c.φ.model.E c.φ.model.C c.U := by
    have h := retractTangent_eq (ScRetraction.id c.isRelOpen_U)
    have hr : (ScRetraction.id c.isRelOpen_U).retract = c.U := image_id _
    rw [hr] at h
    rw [h, ScRetraction.mem_tangent_iff]
    exact ⟨hqs, tangentMap_id_eqOn c.isRelOpen_U.isScDomain hqs⟩
  set v : c.PZ.TangentSpace := TangentSpace.mk (TangentPre.ofVec c.isChart_ζ hqU) with hv
  have hvq : tangentChartMap c.isChart_ζ v = q := tangentChartMap_mk_ofVec c.isChart_ζ hqU
  have hvx : c.PZ.levelVal 1 (c.PZ.tangentProj v) = c.z₀ := by
    have h0 : c.PZ.levelVal 1 (c.PZ.tangentProj v) = c.ζ.symm (c.φ.model.E.toBase 1 q.1) := rfl
    exact h0.trans ((c.ζ_symm_apply (show c.φ.model.E.toBase 1 q.1 ∈ c.U from hqs)).trans
      (Subtype.ext hq1))
  refine ⟨v, hvx, hvq, ?_⟩
  have hvs : v ∈ tangentChartSet c.ζ := mem_univ _
  have hsrc : ∀ z : c.U, (P.tameBoundaryMap hP ∘ c.G) z ∈ c.φ.source := fun z => by
    change P.tameBoundaryMap hP (c.G z) ∈ c.φ.source
    rw [c.tameBoundaryMap_G]; exact c.φ.symm_mapsTo (c.γ_mem z.2).1
  have key := tangentChartMap_tangentMap c.isScSmoothMap_BG c.isChart_ζ c.isChart hvs (hsrc _)
  have hfd : TangentPre.fdom c.ζ (P.tameBoundaryMap hP ∘ c.G) c.φ = univ :=
    eq_univ_of_forall fun z => ⟨mem_univ _, hsrc z⟩
  rw [hfd, show c.ζ '' univ = c.U from c.ζ.image_source, hvq] at key
  have hcong : EqOn c.γ (c.φ ∘ (P.tameBoundaryMap hP ∘ c.G) ∘ c.ζ.symm) c.U := fun z hz => by
    change c.γ z = c.φ (bMap _ (c.G (c.ζ.symm z)))
    rw [c.ζ_symm_apply hz, c.φ_bMap_G]
  have key2 : tangentChartMap c.isChart (tangentMap c.isScSmoothMap_BG v) =
      retractTangentMap c.φ.model.E c.φ.model.C c.U
        (c.φ ∘ (P.tameBoundaryMap hP ∘ c.G) ∘ c.ζ.symm) q := key
  have hc := retractTangentMap_congr c.isScSmoothRetractMap_γ c.isRelOpen_U.isScRetract hcong hqU
  have hK : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.U c.φ.model.E c.φ.model.C c.R.U
      (c.K 0) :=
    c.K.isScSmoothRetractMap c.isRelOpen_U.isScRetract fun _ hz => hz.2.1
  have hcomp := retractTangentMap_comp c.R.isScSmoothRetractMap hK c.isRelOpen_U.isScRetract
    c.R.relOpen.isScRetract hqU
  have hKq : retractTangentMap c.φ.model.E c.φ.model.C c.U (c.K 0) q = q := by
    rw [retractTangentMap_scOperator c.K c.isRelOpen_U.isScRetract (O' := univ)
      (mapsTo_univ _ _) hqU]
    refine Prod.ext ?_ ?_
    · change killCoord c.T c.i 1 (killCoord c.T c.j 1 q.1) = q.1
      have hj1 : killCoord c.T c.j 1 q.1 = q.1 :=
        killCoord_one_eq_self c.T (by rw [hq1]; exact c.coord_e')
      have hi1 : killCoord c.T c.i 1 q.1 = q.1 :=
        killCoord_one_eq_self c.T (by rw [hq1]; exact c.coord_e)
      rw [hj1, hi1]
    · change killCoord c.T c.i 0 (killCoord c.T c.j 0 q.2) = q.2
      rw [killCoord_eq_self hj, killCoord_eq_self hi]
  have hqRU : q ∈ retractTangent c.φ.model.E c.φ.model.C c.R.U := by
    have := hK.tangentMap_mapsTo c.isRelOpen_U.isScRetract c.R.relOpen.isScRetract hqU
    rwa [hKq] at this
  have hRq : retractTangentMap c.φ.model.E c.φ.model.C c.R.U c.R q = q :=
    (retractTangentMap_eqOn c.R.isScSmoothRetractMap (ScRetraction.id c.R.relOpen) (image_id _)
      hqRU).trans (c.R.mem_tangent_iff.1 hqR).2
  have hγq : retractTangentMap c.φ.model.E c.φ.model.C c.U c.γ q = q := by
    refine hcomp.trans ?_
    rw [Function.comp_apply, hKq, hRq]
  refine tangentChartMap_injOn c.isChart ?_ hεs (key2.trans (hc.symm.trans hγq))
  change P.levelVal 1 (P.tangentProj (tangentMap c.isScSmoothMap_BG v)) ∈ c.φ.source
  rw [levelVal_tangentProj_tangentMap]
  exact hsrc _

/-- `G` as an `ScMap` into `bX`. -/
def GMap : ScMap c.PZ (bdry hP).P := ⟨c.G, c.isScSmoothMap_G⟩

/-- `G'` as an `ScMap` into `bX`. -/
def G'Map : ScMap c.PZ (bdry hP).P := ⟨c.G', c.isScSmoothMap_G'⟩

lemma cls_mem_source : c.t.cls ∈ c.D.chart.source :=
  ⟨cls_mem_uSet _ c.t, c.mem_source, c.mem_B⟩

lemma cls_mem_source' : c.t'.cls ∈ c.D'.chart.source :=
  ⟨cls_mem_uSet _ c.t', by
    change c.t'.x ∈ c.φ.source ∩ c.φ ⁻¹' c.B'
    rw [c.x_eq]; exact ⟨c.mem_source, c.mem_B'⟩⟩

/-- **The square over two faces through `x`**: every pair `(a, a') ∈ T_p(bX) × T_{p'}(bX)`,
`p = [x, V, θ]`, `p' = [x, V', θ']`, with `TB a = TB a'` is `(TG v, TG' v)` for a `v ∈ T_{z₀}Z`,
on the level of `a`. -/
theorem exists_tangent_pair {m : ℕ} {a a' : (P.tameBoundaryPolyfold hP).TangentSpace}
    (ham : a ∈ (P.tameBoundaryPolyfold hP).tangentPolyfold.levelSet m)
    (ha : (P.tameBoundaryPolyfold hP).levelVal 1 ((P.tameBoundaryPolyfold hP).tangentProj a) =
      c.t.cls)
    (ha' : (P.tameBoundaryPolyfold hP).levelVal 1 ((P.tameBoundaryPolyfold hP).tangentProj a') =
      c.t'.cls)
    (h : tangentMap (P.tameBoundaryMap_isScSmooth hP) a =
      tangentMap (P.tameBoundaryMap_isScSmooth hP) a') :
    ∃ v : c.PZ.TangentSpace, v ∈ c.PZ.tangentPolyfold.levelSet m ∧
      c.PZ.levelVal 1 (c.PZ.tangentProj v) = c.z₀ ∧
      tangentMap c.isScSmoothMap_G v = a ∧ tangentMap c.isScSmoothMap_G' v = a' := by
  have hB := P.tameBoundaryMap_isScSmooth hP
  set ε := tangentMap hB a with hεdef
  have has : a ∈ tangentChartSet (P := P.tameBoundaryPolyfold hP) c.D.chart := by
    change (P.tameBoundaryPolyfold hP).levelVal 1 ((P.tameBoundaryPolyfold hP).tangentProj a) ∈
      c.D.chart.source
    rw [ha]; exact c.cls_mem_source
  have has' : a' ∈ tangentChartSet (P := P.tameBoundaryPolyfold hP) c.D'.chart := by
    change (P.tameBoundaryPolyfold hP).levelVal 1 ((P.tameBoundaryPolyfold hP).tangentProj a') ∈
      c.D'.chart.source
    rw [ha']; exact c.cls_mem_source'
  have h1 : tangentChartMap c.isChart ε = _ := tangentChartMap_bdryMap hP c.D has
  have h2 : tangentChartMap c.isChart ε = _ := h ▸ tangentChartMap_bdryMap hP c.D' has'
  have hi : (c.T 0 (tangentChartMap c.isChart ε).2).1 c.i = 0 := by
    rw [h1]; exact coord_faceIncl_self c.T c.i _
  have hj : (c.T 0 (tangentChartMap c.isChart ε).2).1 c.j = 0 := by
    rw [h2]; exact coord_faceIncl_self c.T c.j _
  have hεx : P.levelVal 1 (P.tangentProj ε) = c.t.x := by
    rw [hεdef, levelVal_tangentProj_tangentMap, ha]; rfl
  have hεs : ε ∈ tangentChartSet c.φ := by
    change P.levelVal 1 (P.tangentProj ε) ∈ c.φ.source
    rw [hεx]; exact c.mem_source
  obtain ⟨v, hvz, hvq, hvε⟩ := c.exists_tangent hεx hi hj
  have hBG : tangentMap hB (tangentMap c.isScSmoothMap_G v) = ε :=
    (congrFun (tangentMap_comp hB c.isScSmoothMap_G) v).symm.trans hvε
  have hBG' : tangentMap hB (tangentMap c.isScSmoothMap_G' v) = ε :=
    (tangentMap_tangentMap_eq_of_comp_eq hB c.isScSmoothMap_G' c.isScSmoothMap_G
      (fun z => (c.tameBoundaryMap_G' z).trans (c.tameBoundaryMap_G z).symm) v).trans hBG
  refine ⟨v, ?_, hvz, ?_, ?_⟩
  · have hεm : ε ∈ P.tangentPolyfold.levelSet m :=
      (tangentMap_isScSmooth hB).mapsTo_levelSet m ham
    have h3 := (P.tangentPolyfold.mem_levelSet_iff (P.tangentPolyfold_isChart c.isChart ε)
      hεs).1 hεm
    refine (c.PZ.tangentPolyfold.mem_levelSet_iff (c.PZ.tangentPolyfold_isChart c.isChart_ζ v)
      (mem_univ _ : v ∈ tangentChartSet c.ζ)).2 ?_
    have h4 : tangentChart c.isChart_ζ v v = tangentChart c.isChart ε ε := hvq
    rw [h4]
    exact h3
  · refine tangentMap_tameBoundaryMap_injOn hP (level_ext ?_) hBG
    rw [levelVal_tangentProj_tangentMap, hvz, ha]
    exact c.G_z₀
  · refine tangentMap_tameBoundaryMap_injOn hP (level_ext ?_) (hBG'.trans h)
    rw [levelVal_tangentProj_tangentMap, hvz, ha']
    exact c.G'_z₀

/-- **The corner cover over two faces through a point**, in the form of `HasCornerCover`. -/
theorem cover :
    ∃ (Z : BundledMPolyfold.{0}) (g g' : ScMap Z.P (bdry hP).P) (z : Z.carrier),
      (∀ y, bdryMap hP (g y) = bdryMap hP (g' y)) ∧ g z = c.t.cls ∧ g' z = c.t'.cls ∧
      (∀ m, c.t.cls ∈ (bdry hP).P.levelSet m → z ∈ Z.P.levelSet m) ∧
      ∀ (m : ℕ) (a a' : (bdry hP).P.TangentSpace), a ∈ (bdry hP).P.tangentPolyfold.levelSet m →
        (bdry hP).P.levelVal 1 ((bdry hP).P.tangentProj a) = c.t.cls →
        (bdry hP).P.levelVal 1 ((bdry hP).P.tangentProj a') = c.t'.cls →
        tangentMap (bdryMap hP).isScSmoothMap a = tangentMap (bdryMap hP).isScSmoothMap a' →
        ∃ v : Z.P.TangentSpace, v ∈ Z.P.tangentPolyfold.levelSet m ∧
          Z.P.levelVal 1 (Z.P.tangentProj v) = z ∧
          tangentMap g.isScSmoothMap v = a ∧ tangentMap g'.isScSmoothMap v = a' :=
  ⟨BundledMPolyfold.of c.PZ, c.GMap, c.G'Map, c.z₀,
    fun y => (c.tameBoundaryMap_G y).trans (c.tameBoundaryMap_G' y).symm, c.G_z₀, c.G'_z₀,
    fun m hm => c.z₀_mem_levelSet ((P.tameBoundaryMap_isScSmooth hP).mapsTo_levelSet m hm),
    fun _ _ _ ham ha ha' h => c.exists_tangent_pair ham ha ha' h⟩

end CornerChart

/-! ### The corner cover of `B`, and the two definitions of `Ωᵏ(∂Xⁱ)` -/

/-- **Two points of `bX` over the same point of `X` are covered by a square** (`HasCornerCover`):
the corner chart of their two faces. -/
theorem hasCornerCover_bdryMap : HasCornerCover.{u, u, 0} (bdryMap hP) := by
  intro p p' _ hpp'
  obtain ⟨t, rfl, ht⟩ := BSpace.exists_centred_rep _ p
  obtain ⟨t', rfl, ht'⟩ := BSpace.exists_centred_rep _ p'
  have hx : t'.x = t.x := hpp'.symm
  have hxV' : t.x ∈ t'.V := hx ▸ t'.mem.2.1
  obtain ⟨φ, hφ, hxφ, hsrc, R, hRO, n, W, T, hT, hR⟩ := P.exists_tame_chart_subset hP
    (t.mem.1.1.1.inter t'.mem.1.1.1) ⟨t.mem.2.1, hxV'⟩
  have hsrc1 : φ.source ⊆ t.V := hsrc.trans inter_subset_left
  have hsrc2 : φ.source ⊆ t'.V := hsrc.trans inter_subset_right
  obtain ⟨Floc, hFloc, -⟩ := P.exists_localFace_of_faceIn (t.mem.1.1.2 t.x t.mem.2.1)
    t.mem_faces hφ hxφ hsrc1 R hRO hT hR
  obtain ⟨i₀, -⟩ := proposition_2_5_15 hT hR hFloc
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := i₀.pos; omega⟩
  obtain ⟨i, B, hB, hxB, hc, htr, hdeg, S, hxS, hSeq, hSf⟩ :=
    exists_face_chartData hP t t.mem_faces.2 hφ hxφ hsrc1 R hRO hT hR
  have hxθ' : t.x ∈ t'.θ := hx ▸ t'.mem_faces.2
  obtain ⟨j, B', hB', hxB', hc', htr', hdeg', S', hxS', hSeq', hSf'⟩ :=
    exists_face_chartData hP t' hxθ' hφ hxφ hsrc2 R hRO hT hR
  exact CornerChart.cover ⟨t, t', ht, ht', hx, φ, hφ, hxφ, R, hRO, k, W, T, hT, i, j, B, B', hB,
    hB', hxB, hxB', hc, hc', htr, htr', hdeg, hdeg', S, S', hxS, hxS', hSeq, hSeq', hSf, hSf'⟩

variable (k : ℕ)

/-- **2021 p. 198 (2017 p. 150; preprint p. 168): agreement of `τ` on the intersections of local
faces gives that of `dτ`.**  For a tame `X` and an sc-form `τ` on `bXⁱ` agreeing over `Bⁱ`, the
form `dτ` on `bXⁱ⁺¹` agrees over `Bⁱ⁺¹`.  No hypothesis is added. -/
theorem isFaceCompatible_extD {i : ℕ} (τ : (bdry hP).forms k i)
    (hτ : IsFaceCompatible hP i τ.1) : IsFaceCompatible hP (i + 1) (extD τ.1) :=
  isAgreeingOver_extD (isTangentInjective_bdryMap hP) (hasCornerCover_bdryMap hP) i τ hτ

/-- **2021 p. 198 (2017 p. 150; preprint p. 168): `Ωᵏ(∂Xⁱ)` is the set of sc-forms on `bXⁱ` that
agree over `Bⁱ`**: the definition of `BoundaryForms2021` (with the agreement of `dτ`) and the
text's reading (forms coinciding on the intersections of local faces) are the same. -/
theorem bForms_eq_agreeForms (i : ℕ) : bForms hP k i = agreeForms (bdryMap hP) k i :=
  agreeDForms_eq_agreeForms (isTangentInjective_bdryMap hP) (hasCornerCover_bdryMap hP) k i

/-- `τ ∈ Ωᵏ(∂Xⁱ)` iff `τ` agrees over `Bⁱ`. -/
theorem mem_bForms_iff {i : ℕ} {τ : (bdry hP).forms k i} :
    τ ∈ bForms hP k i ↔ IsFaceCompatible hP i τ.1 := by
  rw [bForms_eq_agreeForms]; rfl

end MPolyfold

end Polyfold
