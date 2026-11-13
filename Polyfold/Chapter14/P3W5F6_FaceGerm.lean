import Polyfold.Chapter14.P3W3B1_BoundaryMultisection
import Polyfold.Chapter11.GapP2_HFaces

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.6, pp. 680–682
(2017: §14.6): the preparations for **Definitions 14.6.1, 14.6.2** and **Theorem 14.6.3**.

# Faces of a face-structured ep-groupoid near a boundary point, and sc⁺ relative to a face

## The text, paraphrased

(p. 680) Let `X` be a face-structured tame ep-groupoid.  A face `F` is saturated and is a
sub-M-polyfold; with the induced structure and the morphisms between its points it is an
ep-groupoid.  For `x ∈ ∂X` and an open neighbourhood `U(x)` with the natural `G_x`-action,
`g ∗ (F ∩ U(x)) = F ∩ U(x)` for the faces through `x`; there are `d_X(x)` of them.  A structured
sc⁺-multisection on `W|F` has sc⁺-sections `sˣ_{F,i}` on good neighbourhoods `U_F(x) ⊆ F`, sc⁺ for
the induced M-polyfold structure of `F`.

## What is formalized

* Faces are the ep-faces `X_θ` of Definition 11.1.3 (`EpGroupoid.IsEpFace`); Proposition 11.1.6
  (`EpGroupoid.faceEpGroupoid`, Chapter 11) makes them tame ep-groupoids.
* `IsEpFace.subset_boundary`, `exists_isEpFace_mem` (every boundary point lies on a face),
  `finite_isEpFace_mem` (finitely many faces through a point), `eventually_mem_of_isEpFace`
  (near `x`, every face through a point contains `x`).
* `NaturalRep.eventually_Γ_eq`: two natural representations of `G_x` agree near `x` (the
  natural action on `F ∩ U(x)` does not depend on the choice of `U(x)`; this is what lets the
  face-wise symmetric structures be compared on a common neighbourhood).
* `exists_isEpFace_germ`: in a tame chart, near a point `y`, the local face `{tᵢ = 0}` of the
  model lies in one face of `X` (Part I's `local_face_structure`).
* **sc⁺ relative to a face** `IsFaceRelScPlusSectionOn A F s U` (the sc⁺-sections of `W|F`):
  in every tame strong bundle chart of `X`, at every point of `U`, on every local face germ of
  the model which lies in `F`, the local representative is an sc⁺-section
  (`IsScPlusOnFaceNear`).  The local face germ lying in `F` is the local model of the
  sub-M-polyfold `F` at that point (Theorem 2.5.17, Proposition 11.1.6), so this is "`s|F` is an
  sc⁺-section of `W|F`" read in the charts of `X`, in the same way as Definition 14.1.3 (1) is
  read in `IsFaceScPlusSectionOn`.
* `IsScPlusOnFaceNear.congr_nhds`: the property `IsScPlusOnFaceNear` only depends on the section
  near the point on the face germ.
* `isFaceScPlusSectionOn_of_local` (the gluing step of the proof of Theorem 14.6.3): a section of
  `W|U`, `U ⊆ ∂X`, which near each point `y` agrees on every face `F ∋ y` with a section that is
  sc⁺ relative to `F` at `y`, satisfies (1) of Definition 14.1.3 on `U`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

open TameBoundary

/-! ### Natural representations agree near the point -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- **Two natural representations of `G_x` agree near `x`**: `Γ(g, ·)` and `Γ'(g, ·)` are
continuous local inverses of the source map through `g`, and `s` is injective near `g`. -/
theorem NaturalRep.eventually_Γ_eq {x : Obj} (R R' : X.NaturalRep x) :
    ∀ᶠ y in 𝓝 x, ∀ g, R.Γ g y = R'.Γ g y := by
  refine Filter.eventually_all.2 fun g => ?_
  obtain ⟨O, hO, hgO, hinj, -⟩ := X.exists_isOpen_injOn_src_tgt g.val
  have h1 : ∀ᶠ y in 𝓝 x, R.Γ g y ∈ O := by
    have hc := ((R.isScSmoothOn_Γ g).continuousOn x R.mem_U).continuousAt
      (R.isOpen_U.mem_nhds R.mem_U)
    rw [ContinuousAt, R.Γ_self] at hc
    exact hc (hO.mem_nhds hgO)
  have h2 : ∀ᶠ y in 𝓝 x, R'.Γ g y ∈ O := by
    have hc := ((R'.isScSmoothOn_Γ g).continuousOn x R'.mem_U).continuousAt
      (R'.isOpen_U.mem_nhds R'.mem_U)
    rw [ContinuousAt, R'.Γ_self] at hc
    exact hc (hO.mem_nhds hgO)
  filter_upwards [h1, h2, R.isOpen_U.mem_nhds R.mem_U, R'.isOpen_U.mem_nhds R'.mem_U]
    with y hy1 hy2 hyU hyU'
  exact hinj hy1 hy2 (by rw [R.src_Γ g y hyU, R'.src_Γ g y hyU'])

/-- The natural actions agree near `x` as well. -/
theorem NaturalRep.eventually_Φ_eq {x : Obj} (R R' : X.NaturalRep x) :
    ∀ᶠ y in 𝓝 x, ∀ g, R.Φ g y = R'.Φ g y := by
  filter_upwards [R.eventually_Γ_eq R', R.isOpen_U.mem_nhds R.mem_U,
    R'.isOpen_U.mem_nhds R'.mem_U] with y hy hyU hyU' g
  rw [← R.tgt_Γ g y hyU, ← R'.tgt_Γ g y hyU', hy g]

/-! ### Faces through a boundary point -/

/-- A face `X_θ` consists of boundary points (a point in the closure of `{d = 1}` has `d ≥ 1`, by
upper semicontinuity of `d`). -/
theorem IsEpFace.subset_boundary {F : Set Obj} (hF : X.IsEpFace F) :
    F ⊆ X.PObj.boundary := by
  obtain ⟨θ, ⟨z, -, rfl⟩, rfl⟩ := hF
  intro y hy
  change X.π y ∈ closure _ at hy
  have hy' : y ∈ closure (X.π ⁻¹' connectedComponentIn {w | X.degIndexOrbit w = 1} z) := by
    rw [← X.proposition_7_1_8.preimage_closure_eq_closure_preimage X.continuous_π]
    exact hy
  by_contra hb
  have hb0 : X.PObj.degIndex y = 0 := by
    change ¬ 1 ≤ X.PObj.degIndex y at hb; omega
  have hle := lemma_2_4_3 X.PObj y
  obtain ⟨y', hy'N, hy'S⟩ := mem_closure_iff_nhds.1 hy' _ hle
  have h1 : X.degIndexOrbit (X.π y') = 1 :=
    (connectedComponentIn_subset {w | X.degIndexOrbit w = 1} z hy'S : _)
  have h2 : X.PObj.degIndex y' ≤ X.PObj.degIndex y := hy'N
  change X.PObj.degIndex y' = 1 at h1
  omega

/-- **Every boundary point lies on a face** (face-structured `X`: `|x|` lies on `d_X(x) ≥ 1`
faces of `|X|`). -/
theorem exists_isEpFace_mem (hX : X.IsEpFaceStructured) {x : Obj} (hx : x ∈ X.PObj.boundary) :
    ∃ F, X.IsEpFace F ∧ x ∈ F := by
  have h := hX.2 (X.π x)
  have h1 : (1 : ℕ∞) ≤ (X.orbitFacesThrough (X.π x)).encard := by
    rw [h]; exact_mod_cast hx
  obtain ⟨θ, hθ, hxθ⟩ := Set.one_le_encard_iff_nonempty.1 h1
  exact ⟨X.faceObj θ, ⟨θ, hθ, rfl⟩, hxθ⟩

/-- **Finitely many faces pass through a point** (face-structured `X`). -/
theorem finite_isEpFace_mem (hX : X.IsEpFaceStructured) (x : Obj) :
    {F | X.IsEpFace F ∧ x ∈ F}.Finite := by
  have hfin : (X.orbitFacesThrough (X.π x)).Finite := by
    refine Set.finite_of_encard_eq_coe (k := X.degIndexOrbit (X.π x)) ?_
    exact hX.2 _
  refine (hfin.image X.faceObj).subset ?_
  rintro F ⟨⟨θ, hθ, rfl⟩, hx⟩
  exact ⟨θ, ⟨hθ, hx⟩, rfl⟩

/-- **Near `x`, every face through a point contains `x`** (face-structured `X`; the local pieces
of `{d = 1}` at `x`, Proposition 2.7.5 (3) for the faces `X_θ`). -/
theorem eventually_mem_of_isEpFace (hX : X.IsEpFaceStructured) (x : Obj) :
    ∀ᶠ y in 𝓝 x, ∀ F, X.IsEpFace F → y ∈ F → x ∈ F := by
  have hd := MPolyfold.isCornerIndex_degIndex X.PObj hX.1
  obtain ⟨L⟩ := hd.exists_localPieces (univ_mem : (univ : Set Obj) ∈ 𝓝 x)
  filter_upwards [L.isOpen_B.mem_nhds L.mem_B] with y hy
  rintro F ⟨θ, hθ, rfl⟩ hyF
  obtain ⟨Fy, hFy, hyFy, hFyθ, -⟩ := hX.existsUnique_face_subset hθ hyF
  have hxFy : x ∈ Fy :=
    (L.facesThrough_subset (mem_univ x) hy (⟨hFy, hyFy⟩ : Fy ∈ facesThrough _ univ y)).2
  exact hFyθ hxFy

/-! ### The germ of a local face lies in a face of `X` -/

/-- **The local face `{tᵢ = 0}` of a tame chart lies, near `φ(y)`, in one face `X_θ` of `X`**: by
Part I's `local_face_structure`, near `φ(y)` the face `{tᵢ = 0}` of the retract lies in the
closure of one component `S` of `{d_O = 1}`; `φ⁻¹(S)` is a preconnected subset of `{d_X = 1}`, so
its closure lies in a face of the object M-polyfold, which lies in a face `X_θ`. -/
theorem exists_isEpFace_germ {n : ℕ} {W : ScBanach} {φ : MChart Obj} (hφ : X.PObj.IsChart φ)
    (R : ScRetraction φ.model.E φ.model.C) (hRO : R.retract = φ.model.O)
    {T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)}
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T) {y : Obj}
    (hy : y ∈ φ.source) {i : Fin n} (hi : (T 0 (φ y)).1 i = 0) :
    ∃ ε > 0, ∃ F, X.IsEpFace F ∧
      ∀ e' ∈ φ.model.O ∩ Metric.ball (φ y) ε, (T 0 e').1 i = 0 → φ.symm e' ∈ F := by
  have he : φ y ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model y hy
  obtain ⟨ε, hε, p, hpS, -, -, -, -, -, hcl⟩ := local_face_structure hT hR he hi
  set S := connectedComponentIn R.faceStratum p with hS_def
  have hSO : S ⊆ φ.model.O := fun z hz => hRO ▸ (connectedComponentIn_subset _ _ hz).1
  have hdeg : ∀ z ∈ S, X.PObj.degIndex (φ.symm z) = 1 := fun z hz => by
    have hzO := hSO hz
    rw [MPolyfold.degIndex_eq_chartDegIndex_of_isTameWith X.PObj hφ R hRO hT hR
      (φ.symm_mapsTo hzO), MPolyfold.chartDegIndex]
    have : φ (φ.symm z) = z := φ.toPartialEquiv.right_inv (φ.target_eq ▸ hzO)
    rw [this]
    exact (connectedComponentIn_subset _ _ hz).2
  have hpS' : p ∈ S := mem_connectedComponentIn hpS
  set q := φ.symm p with hq
  have hq1 : X.PObj.degIndex q = 1 := hdeg p hpS'
  have hpre : IsPreconnected (φ.symm '' S) :=
    isPreconnected_connectedComponentIn.image _ (φ.continuousOn_invFun.mono hSO)
  have hsubcc : φ.symm '' S ⊆ connectedComponentIn (univ ∩ {z | X.PObj.degIndex z = 1}) q :=
    hpre.subset_connectedComponentIn ⟨p, hpS', rfl⟩
      (by rintro _ ⟨z, hz, rfl⟩; exact ⟨mem_univ _, hdeg z hz⟩)
  set θ := faceAt X.degIndexOrbit univ (X.π q) with hθ_def
  have hθ : X.IsOrbitFace θ :=
    EpGroupoid.isOrbitFace_iff_isFaceIn.2 (isFaceIn_faceAt (mem_univ _) hq1)
  refine ⟨ε, hε, X.faceObj θ, ⟨θ, hθ, rfl⟩, fun e' he' hi' => ?_⟩
  have he'C : e' ∈ φ.model.C := (hRO ▸ he'.1 : e' ∈ R.retract) |> R.retract_subset_C
  have hRe' : R e' = e' := R.apply_eq_self_of_mem_retract (hRO ▸ he'.1)
  have hcl' : e' ∈ closure S := by
    have := hcl e' ⟨he'.2, he'C⟩ hi'
    rwa [hRe'] at this
  have hcw : ContinuousWithinAt φ.symm S e' :=
    (φ.continuousOn_invFun e' he'.1).mono hSO
  have h1 : φ.symm e' ∈ closure (φ.symm '' S) := hcw.mem_closure_image hcl'
  have h2 : φ.symm e' ∈ faceAt X.PObj.degIndex univ q :=
    ⟨mem_univ _, closure_mono hsubcc h1⟩
  exact X.image_faceAt_subset q ⟨_, h2, rfl⟩

end EpGroupoid

/-! ### `IsScPlusOnFaceNear` only depends on the section near the point -/

section Local

variable {E F W : ScBanach} {n : ℕ}

/-- If `s = s'` on the face germ `O ∩ N ∩ {tᵢ = 0}` for an open `N ∋ x`, then
`IsScPlusOnFaceNear` passes from `s` to `s'` (shrink the neighbourhood to `V ∩ N`,
Proposition 2.3.1 (1)). -/
theorem IsScPlusOnFaceNear.congr_nhds {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)}
    {C O : Set (E 0)} {K : Set (E 0 × F 0)} {s s' : E 0 → E 0 × F 1} {x : E 0} {i : Fin n}
    (h : IsScPlusOnFaceNear T C O K s x i) {N : Set (E 0)} (hN : IsOpen N) (hxN : x ∈ N)
    (hss' : EqOn s s' (O ∩ N ∩ coordHyper T i)) : IsScPlusOnFaceNear T C O K s' x i := by
  obtain ⟨V, hV, hxV, hret, hsec⟩ := h
  have hset : O ∩ (V ∩ N) ∩ coordHyper T i = (O ∩ V ∩ coordHyper T i) ∩ N := by
    ext z; simp only [mem_inter_iff]; tauto
  refine ⟨V ∩ N, hV.inter hN, ⟨hxV, hxN⟩, ?_, ?_⟩
  · rw [hset]; exact proposition_2_3_1_one hret hN
  · rw [hset]
    refine ⟨fun z hz => ?_, ?_⟩
    · rw [← hss' ⟨⟨hz.1.1.1, hz.2⟩, hz.1.2⟩]; exact hsec.fst_eq z hz.1
    · exact (hsec.isScSmooth.restrict hret).congr fun z hz =>
        hss' ⟨⟨hz.1.1.1, hz.2⟩, hz.1.2⟩

end Local

/-! ### Sc⁺-sections relative to a face -/

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-- **The germ of the local face `{tᵢ = 0}` at `e` lies in `F`**: for some `ε > 0`, every point of
the retract within `ε` of `e` with `tᵢ = 0` is mapped by the chart inverse into `F`. -/
def FaceGermIn (c : StrongBundleChart A.X.PObj A.P) {n : ℕ} {W : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)) (F : Set A.Obj)
    (e : c.φ.model.E 0) (i : Fin n) : Prop :=
  ∃ ε > 0, ∀ e' ∈ c.φ.model.O ∩ Metric.ball e ε, (T 0 e').1 i = 0 → c.φ.symm e' ∈ F

/-- **An sc⁺-section of `W|F` near `U ⊆ F`, read in the charts of `X`** (§14.6, p. 680): `s` is a
section over `U` with values in `W_{0,1}`, and in every tame strong bundle chart, at every point
`y ∈ U`, on every local face germ `{tᵢ = 0}` at `φ(y)` lying in `F` (the local model of the
sub-M-polyfold `F` at `y`), the local representative is an sc⁺-section (`IsScPlusOnFaceNear`).
Only the values of `s` on `F` near `U` enter. -/
def IsFaceRelScPlusSectionOn (A : SEP.{u}) (F : Set A.Obj) (s : A.Obj → A.W) (U : Set A.Obj) :
    Prop :=
  (∀ x ∈ U, A.P (s x) = x ∧ s x ∈ A.B.oneSet) ∧
  ∀ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c →
    ∀ (n : ℕ) (W : ScBanach) (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
      c.φ.model.C = T 0 ⁻¹' quadrant n W 0 →
      ∀ x ∈ U ∩ c.φ.source, ∀ i ∈ zeroSet T (c.φ x), FaceGermIn c T F (c.φ x) i →
        IsScPlusOnFaceNear T c.φ.model.C c.φ.model.O c.K (localRepOne c s) (c.φ x) i

theorem IsFaceRelScPlusSectionOn.mono {F : Set A.Obj} {s : A.Obj → A.W} {U U' : Set A.Obj}
    (h : IsFaceRelScPlusSectionOn A F s U) (hU' : U' ⊆ U) : IsFaceRelScPlusSectionOn A F s U' :=
  ⟨fun x hx => h.1 x (hU' hx), fun c hc n W T hT x hx i hi hg =>
    h.2 c hc n W T hT x ⟨hU' hx.1, hx.2⟩ i hi hg⟩

/-- Sc⁺ on all local faces (Definition 14.1.3 (1), `IsFaceScPlusSectionOn`) implies sc⁺ relative
to every face. -/
theorem IsFaceScPlusSectionOn.isFaceRelScPlusSectionOn {F : Set A.Obj} {s : A.Obj → A.W}
    {U : Set A.Obj} (h : IsFaceScPlusSectionOn A s U) : IsFaceRelScPlusSectionOn A F s U :=
  ⟨h.1, fun c hc n W T hT x hx i hi _ => h.2 c hc n W T hT x hx i hi⟩

/-- The zero section is sc⁺ relative to every face, on every `U ⊆ ∂X`. -/
theorem isFaceRelScPlusSectionOn_fiberZero {F U : Set A.Obj} (hU : U ⊆ A.X.PObj.boundary) :
    IsFaceRelScPlusSectionOn A F (fiberZero A.P) U :=
  (isFaceScPlusSectionOn_fiberZero hU).isFaceRelScPlusSectionOn

/-- The local representative only depends on the section at the point `φ⁻¹(z)`. -/
theorem localRepOne_congr (c : StrongBundleChart A.X.PObj A.P) {s s' : A.Obj → A.W}
    {z : c.φ.model.E 0} (h : s (c.φ.symm z) = s' (c.φ.symm z)) :
    localRepOne c s z = localRepOne c s' z := by
  simp only [localRepOne, h]

/-- **Gluing face-relative sc⁺ into Definition 14.1.3 (1)**: let `s` be a section over `U ⊆ X`
with values in `W_{0,1}`.  Suppose that for every `y ∈ U` and every face `F` of `X` (a set of the
family `𝓕`) containing a local face germ at `y`, `s` agrees near `y` on `F` with a section
`σ` which is sc⁺ relative to `F` at `y`.  Then `s` is sc⁺ on every local face at the points of
`U` (`IsFaceScPlusSectionOn`). -/
theorem isFaceScPlusSectionOn_of_local {s : A.Obj → A.W} {U : Set A.Obj}
    (hU : ∀ y ∈ U, A.P (s y) = y ∧ s y ∈ A.B.oneSet)
    (hloc : ∀ y ∈ U, ∀ F, A.X.IsEpFace F → y ∈ F → ∃ σ : A.Obj → A.W, ∃ N : Set A.Obj,
      IsOpen N ∧ y ∈ N ∧ IsFaceRelScPlusSectionOn A F σ {y} ∧ ∀ z ∈ F ∩ N, s z = σ z) :
    IsFaceScPlusSectionOn A s U := by
  refine ⟨hU, fun c hc n W T hT y hy i hi => ?_⟩
  have hRO := c.base_retract
  have hR := hc.isTame n W T hT
  obtain ⟨ε, hε, F, hF, hgerm⟩ := A.X.exists_isEpFace_germ c.isChart _ hRO hT hR hy.2
    ((mem_zeroSet T).1 hi)
  have hyF : y ∈ F := by
    have := hgerm (c.φ y) ⟨c.φ.mapsTo_model y hy.2, Metric.mem_ball_self hε⟩
      ((mem_zeroSet T).1 hi)
    rwa [c.φ.symm_apply_apply hy.2] at this
  obtain ⟨σ, N, hN, hyN, hσ, hsσ⟩ := hloc y hy.1 F hF hyF
  have hface := hσ.2 c hc n W T hT y ⟨rfl, hy.2⟩ i hi ⟨ε, hε, hgerm⟩
  -- the open set of the model over `N`
  obtain ⟨N', hN', hN'eq⟩ := continuousOn_iff'.1 c.φ.continuousOn_invFun N hN
  have hyN' : c.φ y ∈ N' := by
    have : c.φ y ∈ c.φ.symm ⁻¹' N ∩ c.φ.model.O :=
      ⟨by rw [mem_preimage, c.φ.symm_apply_apply hy.2]; exact hyN,
        c.φ.mapsTo_model y hy.2⟩
    rw [hN'eq] at this; exact this.1
  refine hface.congr_nhds (hN'.inter Metric.isOpen_ball) ⟨hyN', Metric.mem_ball_self hε⟩
    fun z hz => (localRepOne_congr c ?_).symm
  have hzO : z ∈ c.φ.model.O := hz.1.1
  have hzN : c.φ.symm z ∈ N := by
    have : z ∈ N' ∩ c.φ.model.O := ⟨hz.1.2.1, hzO⟩
    rw [← hN'eq] at this; exact this.1
  exact hsσ _ ⟨hgerm z ⟨hzO, hz.1.2.2⟩ hz.2, hzN⟩

end SBLocalization

end Polyfold
