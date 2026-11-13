import Polyfold.Chapter4.GapP1_Theorem4211

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.2,
**Theorem 4.2.11 (1) and (4)** (p. 190; preprint Theorem 4.22), and the local faces recalled before
**Proposition 2.5.16** (p. 62).

# The local faces of a neighbourhood are the faces of the chart

## The text

In the proof of Theorem 4.2.11 the text goes into a tame chart `(O, C, E)` centred at `x`,
`C = [0, ∞)ⁿ ⊕ W`, `n = d_X(x)`, and takes as local faces the sets `F_i = O ∩ {λ_i = 0}`; in the
statement, the local faces are the faces of the neighbourhood `U` (closures in `U` of the
components of `U ∩ {d_X = 1}`), and `F_σ = ⋂_{i ∈ σ} F_i`.

## What is formalized

* `MPolyfold.exists_faces_chart`: in a tame chart `ψ` centred at `x` and for any open
  `U ∋ x` inside the chart domain, there are faces `θ_0, …, θ_{n-1}` of `U` (pairwise distinct)
  and a smaller open `U' ∋ x` with `θ_i ∩ U' = U' ∩ ψ⁻¹{λ_i = 0}` and, for every face `F ∋ 0`
  of the model retract with `F ⊆ {λ_i = 0}`, `U' ∩ ψ⁻¹(F) = U' ∩ ψ⁻¹{λ_i = 0}`.  If moreover
  `d_X(x) = n`, the faces of `U` through `x` are exactly the `θ_i`.
* `MPolyfold.theorem_4_2_11_faces`: Theorem 4.2.11 with (1) in the text's sense, the local faces
  `θ_i` of `U` identified near `x` with the chart faces, and the text's `F_σ = ⋂_{i ∈ σ} θ_i`
  agreeing near `x` with the sets `ψ⁻¹(G ∩ ⋂_{i ∈ σ} F_i)` of the formal (4)
  (`theorem_4_2_11_preprint`), for every `σ`.

The proof reuses Lemma 4.C of the exposition (`local_face_structure`): near `0`, the points of
`O ∩ {λ_i = 0}` are limits of `r({z ∈ C : I(z) = {i}})`, a connected subset of `{d = 1}`.
-/

open Set Filter Topology Function

universe u

namespace Polyfold

namespace MPolyfold

open TameBoundary

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **The faces of a neighbourhood in a tame centred chart.**  Let `ψ` be a chart modelled on the
tame retract `O = r(U_r)`, `C = T⁻¹([0,∞)ⁿ ⊕ W)`, with `ψ(x) = 0`, and `U ∋ x` open inside the
chart domain.  Then there are an open `U' ∋ x`, `U' ⊆ U`, and pairwise distinct faces `θ_i` of `U`
(`i < n`) with `θ_i ∩ U' = U' ∩ ψ⁻¹{λ_i = 0}`; and for every face `F ∋ 0` of the retract `O` with
`F ⊆ {λ_i = 0}`, `U' ∩ ψ⁻¹(F) = U' ∩ ψ⁻¹{λ_i = 0}`. -/
theorem exists_faces_chart {ψ : MChart X} (hψ : P.IsChart ψ)
    (R : ScRetraction ψ.model.E ψ.model.C) (hRO : R.retract = ψ.model.O) {n : ℕ} {W : ScBanach}
    {T : ScIso ψ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)}
    (hT : ψ.model.C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T) {x : X} (hx : x ∈ ψ.source)
    (hψ0 : ψ x = 0) {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) (hUψ : U ⊆ ψ.source) :
    ∃ U' : Set X, IsOpen U' ∧ x ∈ U' ∧ U' ⊆ U ∧ ∃ θ : Fin n → Set X, Injective θ ∧
      (∀ i, IsFaceIn P.degIndex U (θ i)) ∧
      (∀ i, θ i ∩ U' = U' ∩ ψ ⁻¹' coordHyper T i) ∧
      (∀ i (F : Set (ψ.model.E 0)), R.IsRetractFace F → (0 : ψ.model.E 0) ∈ F →
        F ⊆ coordHyper T i → U' ∩ ψ ⁻¹' F = U' ∩ ψ ⁻¹' coordHyper T i) := by
  classical
  have hdeg : ∀ z ∈ ψ.source, P.degIndex z = degIndexWith T (ψ z) := fun z hz => by
    rw [P.degIndex_eq_chartDegIndex_of_isTameWith hψ R hRO hT hR hz, chartDegIndex,
      degIndex_eq T hT (ψ.apply_mem_C hz)]
  have h0O : (0 : ψ.model.E 0) ∈ R.retract := by
    rw [hRO, ← hψ0]; exact ψ.mapsTo_model x hx
  have h0U : (0 : ψ.model.E 0) ∈ R.U := R.retract_subset h0O
  have h0C : (0 : ψ.model.E 0) ∈ ψ.model.C := R.U_subset_C h0U
  have hR0 : R 0 = 0 := R.apply_eq_self_of_mem_retract h0O
  have h0i : ∀ i : Fin n, (T 0 (0 : ψ.model.E 0)).1 i = 0 := fun i => by simp
  have key := fun i => local_face_structure hT hR h0O (h0i i)
  choose ε hε p hpS hpi hBU _ _ hB hcl using key
  have hRc : ContinuousOn R R.U := R.isSc1.isSc0.continuousOn_base
  have hRO' : ∀ z ∈ R.U, R z ∈ ψ.model.O := fun z hz => by
    rw [← hRO]; exact R.apply_mem_retract hz
  have hcomp : ContinuousWithinAt (fun z => ψ.symm (R z)) R.U 0 :=
    (ψ.continuousOn_invFun (R 0) (hRO' 0 h0U)).comp (hRc 0 h0U) hRO'
  have hsx : ψ.symm (R 0) = x := by rw [hR0, ← hψ0]; exact ψ.symm_apply_apply hx
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := Metric.mem_nhdsWithin_iff.1
    (hcomp.tendsto (hsx.symm ▸ hU.mem_nhds hxU : U ∈ 𝓝 (ψ.symm (R 0))))
  obtain ⟨O₀, hO₀, hUO₀⟩ := R.relOpen.relOpen
  have h0O₀ : (0 : ψ.model.E 0) ∈ O₀ := (hUO₀ ▸ h0U).1
  have hev : ∀ᶠ z in 𝓝 (0 : ψ.model.E 0), (∀ i, z ∈ Metric.ball 0 (ε i)) ∧
      z ∈ Metric.ball 0 δ₀ ∧ z ∈ O₀ :=
    (eventually_all.2 fun i => Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hε i))).and
      (Filter.Eventually.and (Metric.ball_mem_nhds _ hδ₀) (hO₀.mem_nhds h0O₀))
  obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhds_iff.1 hev
  have hδε : ∀ i, Metric.ball (0 : ψ.model.E 0) δ ⊆ Metric.ball 0 (ε i) := fun i z hz =>
    (hδb hz).1 i
  have hδU : ∀ z ∈ Metric.ball (0 : ψ.model.E 0) δ ∩ ψ.model.C,
      z ∈ R.U ∧ ψ.symm (R z) ∈ U := by
    intro z hz
    have hzU : z ∈ R.U := hUO₀ ▸ ⟨(hδb hz.1).2.2, hz.2⟩
    exact ⟨hzU, hδ₀U ⟨(hδb hz.1).2.1, hzU⟩⟩
  -- the neighbourhood `U'`
  set U' : Set X := U ∩ ψ ⁻¹' Metric.ball 0 δ with hU'def
  have hU'o : IsOpen U' :=
    (ψ.continuousOn_toFun.mono hUψ).isOpen_inter_preimage hU Metric.isOpen_ball
  have hxU' : x ∈ U' := ⟨hxU, by rw [mem_preimage, hψ0]; exact Metric.mem_ball_self hδ⟩
  -- points `q_i` of the stratum `{d = 1}` on `{λ_i = 0}` near `0`
  have hq : ∀ i, ∃ q ∈ R.faceStratum, q ∈ Metric.ball (0 : ψ.model.E 0) δ ∧ (T 0 q).1 i = 0 := by
    intro i
    have h := hcl i 0 ⟨Metric.mem_ball_self (hε i), h0C⟩ (h0i i)
    rw [hR0] at h
    obtain ⟨s, hs, hsd⟩ := Metric.mem_closure_iff.1 h δ hδ
    exact ⟨s, connectedComponentIn_subset _ _ hs, by rw [Metric.mem_ball, dist_comm]; exact hsd,
      connectedComponentIn_faceStratum_subset hT (hpi i) hs⟩
  choose q hqS hqb hqi using hq
  have hqO : ∀ i, q i ∈ ψ.model.O := fun i => hRO ▸ (hqS i).1
  have hqC : ∀ i, q i ∈ ψ.model.C := fun i => R.retract_subset_C (hqS i).1
  have hqI : ∀ i, zeroSet T (q i) = {i} := fun i =>
    zeroSet_eq_singleton (faceStratum_degIndexWith hT (hqS i)) (hqi i)
  set w : Fin n → X := fun i => ψ.symm (q i) with hwdef
  have hψw : ∀ i, ψ (w i) = q i := fun i => ψ.apply_symm_apply (hqO i)
  have hwU : ∀ i, w i ∈ U := fun i => by
    have := (hδU (q i) ⟨hqb i, hqC i⟩).2
    rwa [R.apply_eq_self_of_mem_retract (hqS i).1] at this
  have hw1 : ∀ i, P.degIndex (w i) = 1 := fun i => by
    rw [hdeg _ (ψ.symm_mapsTo (hqO i)), hψw]; exact faceStratum_degIndexWith hT (hqS i)
  -- the sets `A_i = {z ∈ C : |z| < δ, I(z) = {i}}` and their images
  have hC : Convex ℝ ψ.model.C := R.relOpen.isPartialQuadrant.convex
  set A : Fin n → Set (ψ.model.E 0) := fun i =>
    {z | z ∈ Metric.ball 0 δ ∩ ψ.model.C ∧ zeroSet T z = {i}} with hAdef
  have hAU : ∀ i, A i ⊆ R.U := fun i z hz => (hδU z hz.1).1
  have hqA : ∀ i, q i ∈ A i := fun i => ⟨⟨hqb i, hqC i⟩, hqI i⟩
  have hK : ∀ i, ψ.symm '' (R '' A i) ⊆
      connectedComponentIn (U ∩ {y | P.degIndex y = 1}) (w i) := by
    intro i
    have hpre : IsPreconnected (ψ.symm '' (R '' A i)) :=
      ((convex_ball_inter_zeroSet_eq hT hC 0 δ i).isPreconnected.image R
        (hRc.mono (hAU i))).image ψ.symm
        (ψ.continuousOn_invFun.mono fun _ ⟨z, hz, hzR⟩ => hzR ▸ hRO' z (hAU i hz))
    refine hpre.subset_connectedComponentIn ⟨_, ⟨q i, hqA i, rfl⟩, by
      simp only [hwdef]; rw [R.apply_eq_self_of_mem_retract (hqS i).1]⟩ ?_
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨(hδU z hz.1).2, ?_⟩
    have hRzO := hRO' z (hAU i hz)
    have hRzC : R z ∈ ψ.model.C := R.retract_subset_C (R.apply_mem_retract (hAU i hz))
    change P.degIndex (ψ.symm (R z)) = 1
    rw [hdeg _ (ψ.symm_mapsTo hRzO), ψ.apply_symm_apply hRzO, ← degIndex_eq T hT hRzC,
      hR.degIndex_apply _ (hAU i hz), degIndex_eq T hT hz.1.2, degIndexWith_eq_card_zeroSet,
      hz.2, Finset.card_singleton]
  -- the faces
  set θ : Fin n → Set X := fun i => faceAt P.degIndex U (w i) with hθdef
  have hcH : ∀ i, connectedComponentIn (U ∩ {y | P.degIndex y = 1}) (w i) ⊆
      ψ ⁻¹' coordHyper T i := by
    intro i
    have hcs : connectedComponentIn (U ∩ {y | P.degIndex y = 1}) (w i) ⊆
        U ∩ {y | P.degIndex y = 1} := connectedComponentIn_subset _ _
    have himg := subset_coordHyper_of_isPreconnected hT
      (isPreconnected_connectedComponentIn.image ψ
        (ψ.continuousOn_toFun.mono fun z hz => hUψ (hcs hz).1))
      (by rintro _ ⟨z, hz, rfl⟩; exact ψ.apply_mem_C (hUψ (hcs hz).1))
      (by rintro _ ⟨z, hz, rfl⟩; rw [← hdeg z (hUψ (hcs hz).1)]; exact (hcs hz).2)
      (p := q i) ⟨w i, mem_connectedComponentIn ⟨hwU i, hw1 i⟩, hψw i⟩ (hqi i)
    exact fun z hz => himg ⟨z, hz, rfl⟩
  have hθH : ∀ i, θ i ⊆ ψ ⁻¹' coordHyper T i := by
    rintro i z ⟨hzU, hzc⟩
    have hca : ContinuousAt ψ z :=
      ψ.continuousOn_toFun.continuousAt (ψ.isOpen_source.mem_nhds (hUψ hzU))
    exact (isClosed_coordHyper T i).closure_subset_iff.2 (image_subset_iff.2 (hcH i))
      (hca.continuousWithinAt.mem_closure_image hzc)
  have hHθ : ∀ i, U' ∩ ψ ⁻¹' coordHyper T i ⊆ θ i := by
    rintro i z ⟨⟨hzU, hzb⟩, hzi⟩
    have hzs := hUψ hzU
    have he'O : ψ z ∈ ψ.model.O := ψ.mapsTo_model z hzs
    have he'R : ψ z ∈ R.retract := hRO ▸ he'O
    have h := hcl i (ψ z) ⟨hδε i hzb, ψ.apply_mem_C hzs⟩ hzi
    rw [R.apply_eq_self_of_mem_retract he'R] at h
    have h2 : ψ z ∈ closure (Metric.ball 0 δ ∩ connectedComponentIn R.faceStratum (p i)) :=
      Metric.isOpen_ball.inter_closure ⟨hzb, h⟩
    have hsub : Metric.ball 0 δ ∩ connectedComponentIn R.faceStratum (p i) ⊆ R '' A i := by
      rintro y ⟨hyb, hy⟩
      have hyS : y ∈ R.faceStratum := connectedComponentIn_subset _ _ hy
      have hyi := connectedComponentIn_faceStratum_subset hT (hpi i) hy
      exact ⟨y, ⟨⟨hyb, R.retract_subset_C hyS.1⟩,
        zeroSet_eq_singleton (faceStratum_degIndexWith hT hyS) hyi⟩,
        R.apply_eq_self_of_mem_retract hyS.1⟩
    have hsO : Metric.ball 0 δ ∩ connectedComponentIn R.faceStratum (p i) ⊆ ψ.model.O :=
      fun y hy => hRO ▸ (connectedComponentIn_subset _ _ hy.2 : y ∈ R.faceStratum).1
    have h3 := ((ψ.continuousOn_invFun (ψ z) he'O).mono hsO).mem_closure_image h2
    rw [show ψ.toPartialEquiv.symm (ψ.toPartialEquiv z) = z from ψ.symm_apply_apply hzs] at h3
    exact ⟨hzU, closure_mono ((image_mono hsub).trans (hK i)) h3⟩
  refine ⟨U', hU'o, hxU', inter_subset_left, θ, ?_, fun i => isFaceIn_faceAt (hwU i) (hw1 i),
    fun i => Subset.antisymm (fun z hz => ⟨hz.2, hθH i hz.1⟩)
      (fun z hz => ⟨hHθ i hz, hz.1⟩), ?_⟩
  · intro i j hij
    have h : w i ∈ θ j := hij ▸ mem_faceAt_self (hwU i) (hw1 i)
    have hj : j ∈ zeroSet T (q i) := (mem_zeroSet T).2 (by rw [← hψw]; exact hθH j h)
    rw [hqI, Finset.mem_singleton] at hj
    exact hj.symm
  · intro i F hF hF0 hFi
    refine Subset.antisymm (fun z hz => ⟨hz.1, hFi hz.2⟩) ?_
    rintro z ⟨hzU', hzi⟩
    refine ⟨hzU', ?_⟩
    have hzs := hUψ hzU'.1
    have he'R : ψ z ∈ R.retract := hRO ▸ ψ.mapsTo_model z hzs
    obtain ⟨x0, hx0S, rfl⟩ := hF
    have hx0i : (T 0 x0).1 i = 0 :=
      hFi ⟨subset_closure (mem_connectedComponentIn hx0S), hx0S.1⟩
    rw [closure_connectedComponentIn_faceStratum hT hR hx0S hx0i] at hF0
    rw [mem_preimage, closure_connectedComponentIn_faceStratum hT hR hx0S hx0i,
      connectedComponentIn_eq hF0]
    have hz' : ψ z ∈ closure (connectedComponentIn R.faceStratum (p i)) ∩ R.retract := by
      have h := hcl i (ψ z) ⟨hδε i hzU'.2, ψ.apply_mem_C hzs⟩ hzi
      rw [R.apply_eq_self_of_mem_retract he'R] at h
      exact ⟨h, he'R⟩
    have h0' : (0 : ψ.model.E 0) ∈
        closure (connectedComponentIn R.faceStratum (p i)) ∩ R.retract := by
      have h := hcl i 0 ⟨Metric.mem_ball_self (hε i), h0C⟩ (h0i i)
      rw [hR0] at h
      exact ⟨h, h0O⟩
    rw [closure_connectedComponentIn_faceStratum hT hR (hpS i) (hpi i)] at hz' h0'
    rw [← connectedComponentIn_eq h0']
    exact hz'

/-- **2021 Theorem 4.2.11 (1)–(4)** (p. 190; preprint Theorem 4.22), with the text's local faces.
In the tame chart `ψ` centred at `x` (with `n = d_X(x)` half-line coordinates, all vanishing at
`0`) there is an open `U ∋ x`, face-structured (2021 Definition 2.7.6), such that:
(1) the faces of `U` through `x` (closures in `U` of the components of `U ∩ {d_X = 1}`) are exactly
`d_X(x) = n` pairwise distinct sets `θ_0, …, θ_{n-1}`, and near `x` the face `θ_i` is the chart face
`ψ⁻¹{λ_i = 0}`; (2) `d_A = d_X` on `A ∩ U`; (3) general position on `A ∩ U`; (4) for every
`σ ⊆ {0, …, n-1}` the text's `F_σ = ⋂_{i ∈ σ} θ_i` agrees near `x` with `ψ⁻¹(G ∩ ⋂_{i ∈ σ} F_i)`,
`F_i ∋ 0` faces of the model, which is a tame sub-M-polyfold with `d_{F_σ} + #σ = d_X`, in which
`A ∩ F_σ` is a tame smooth submanifold in general position (`theorem_4_2_11_preprint` (4)). -/
theorem theorem_4_2_11_faces (hP : P.IsTame) {A : Set X} (hA : P.IsSmoothSubmanifold A)
    [ParacompactSpace A] {x : X} (hgp : P.IsGeneralPositionAt A x) :
    ∃ ψ : MChart X, P.IsChart ψ ∧ x ∈ ψ.source ∧ ψ x = 0 ∧
      ∃ (R : ScRetraction ψ.model.E ψ.model.C) (n : ℕ) (Wq : ScBanach)
        (T : ScIso ψ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
        R.retract = ψ.model.O ∧ ψ.model.C = T 0 ⁻¹' quadrant n Wq 0 ∧ R.IsTameWith T ∧
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ ψ.source ∧
        (∀ y ∈ U, (facesThrough P.degIndex U y).encard = P.degIndex y) ∧
        -- (1)
        P.degIndex x = n ∧
        ∃ θ : Fin n → Set X, Injective θ ∧ facesThrough P.degIndex U x = range θ ∧
        ∃ U' : Set X, IsOpen U' ∧ x ∈ U' ∧ U' ⊆ U ∧
          (∀ i, θ i ∩ U' = U' ∩ ψ ⁻¹' coordHyper T i) ∧
        -- (2)
        (∀ a : A, (a : X) ∈ U → (subPolyfold hA.isSubMPolyfold).degIndex a = P.degIndex a) ∧
        -- (3)
        (∀ a ∈ U ∩ A, P.IsGeneralPositionAt A a) ∧
        -- (4)
        ∀ σ : Finset (Fin n), ∃ (Fc : σ → Set (ψ.model.E 0)) (G : Set (ψ.model.E 0)),
          (∀ i, R.IsRetractFace (Fc i) ∧ (0 : ψ.model.E 0) ∈ Fc i ∧ Fc i ⊆ coordHyper T i) ∧
          IsOpen G ∧ (0 : ψ.model.E 0) ∈ G ∧ x ∈ ψ.cornerPreimage G Fc ∧
          (∃ V : Set X, IsOpen V ∧ x ∈ V ∧
            (⋂ i : σ, θ i) ∩ V = ψ.cornerPreimage G Fc ∩ V) ∧
          ∃ hF : P.IsSubMPolyfold (ψ.cornerPreimage G Fc),
            haveI := P.paracompactSpace_subtype (ψ.cornerPreimage G Fc)
            (subPolyfold hF).IsTame ∧
            (∀ a, (subPolyfold hF).degIndex a + σ.card = P.degIndex a) ∧
            (subPolyfold hF).IsSmoothSubmanifold {b | (b : X) ∈ A} ∧
            (∀ b : ψ.cornerPreimage G Fc, (b : X) ∈ A →
              (subPolyfold hF).IsGeneralPositionAt {b | (b : X) ∈ A} b) ∧
            haveI := (subPolyfold hF).paracompactSpace_subtype {b | (b : X) ∈ A}
            (subPolyfold hF).IsTameSubmanifold {b | (b : X) ∈ A} := by
  obtain ⟨ψ, hψ, hx, hψ0, R, n, Wq, T, hR, hT, hRT, U₀, hU₀, hxU₀, hU₀s, hdx, -, h2, h3, h4⟩ :=
    theorem_4_2_11_preprint hP hA hgp
  obtain ⟨D, hD, hxD, hfs⟩ :=
    TameBoundary.exists_nbhd_forall_isFaceStructuredOpen (P.isCornerIndex_degIndex hP) x
  set U := U₀ ∩ D with hUdef
  have hU : IsOpen U := hU₀.inter hD
  have hxU : x ∈ U := ⟨hxU₀, hxD⟩
  have hUs : U ⊆ ψ.source := inter_subset_left.trans hU₀s
  have hV : IsFaceStructuredOpen P.degIndex U := hfs _ hU inter_subset_right
  obtain ⟨U', hU'o, hxU', hU'U, θ, hθinj, hθface, hθH, hθF⟩ :=
    exists_faces_chart hψ R hR hT hRT hx hψ0 hU hxU hUs
  have hxθ : ∀ i, x ∈ θ i := fun i => by
    have : x ∈ U' ∩ ψ ⁻¹' coordHyper T i := ⟨hxU', by
      rw [mem_preimage, hψ0, coordHyper, mem_ofPred_eq, map_zero]; rfl⟩
    rw [← hθH i] at this; exact this.1
  have hfaces : facesThrough P.degIndex U x = range θ := by
    refine ((finite_range θ).eq_of_subset_of_encard_le ?_ ?_).symm
    · rintro _ ⟨i, rfl⟩; exact ⟨hθface i, hxθ i⟩
    · rw [encard_range_of_injective_fin hθinj, ← hdx]
      exact encard_facesThrough_le (P.isCornerIndex_degIndex hP) hU hxU
  refine ⟨ψ, hψ, hx, hψ0, R, n, Wq, T, hR, hT, hRT, U, hU, hxU, hUs, hV.2, hdx, θ, hθinj,
    hfaces, U', hU'o, hxU', hU'U, hθH, fun a ha => h2 a ha.1, fun a ha => h3 a ⟨ha.1.1, ha.2⟩,
    fun σ => ?_⟩
  obtain ⟨Fc, G, hFc, hG, h0G, hxF, -, rest⟩ := h4 σ
  refine ⟨Fc, G, hFc, hG, h0G, hxF, ⟨U' ∩ ψ ⁻¹' G,
    (ψ.continuousOn_toFun.mono (hU'U.trans hUs)).isOpen_inter_preimage hU'o hG,
    ⟨hxU', by rw [mem_preimage, hψ0]; exact h0G⟩, ?_⟩, rest⟩
  ext z
  simp only [mem_inter_iff, mem_iInter, MChart.cornerPreimage, mem_ofPred_eq, mem_preimage]
  constructor
  · rintro ⟨hz, hzU', hzG⟩
    refine ⟨⟨hUs (hU'U hzU'), hzG, fun i => ?_⟩, hzU', hzG⟩
    have h1 : z ∈ U' ∩ ψ ⁻¹' coordHyper T i := by rw [← hθH i]; exact ⟨hz i, hzU'⟩
    rw [← hθF i (Fc i) (hFc i).1 (hFc i).2.1 (hFc i).2.2] at h1
    exact h1.2
  · rintro ⟨⟨-, -, hzF⟩, hzU', hzG⟩
    refine ⟨fun i => ?_, hzU', hzG⟩
    have h1 : z ∈ U' ∩ ψ ⁻¹' Fc i := ⟨hzU', hzF i⟩
    rw [hθF i (Fc i) (hFc i).1 (hFc i).2.1 (hFc i).2.2, ← hθH i] at h1
    exact h1.1

end MPolyfold

end Polyfold
