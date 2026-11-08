import Polyfold.Chapter4.LocalStructure
import Polyfold.Chapter4.Families

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 4, the two
statements of §4.2–§4.3 that the 2021 edition changes: **Theorem 4.2.11** (p. 190; 2017:
Theorem 4.3; preprint: Theorem 4.22) and **Theorem 4.3.1** (p. 193; 2017: Theorem 4.4; preprint:
Theorem 4.23).  The third changed statement, Proposition 4.4.5 (2017: Proposition 4.5; preprint:
Proposition 4.26), and the 2021-only items of §4.4–§4.5 are in `Chapter4/VectorFields.lean`.

# Theorems 4.2.11 and 4.3.1 in the 2021 edition

## The text, paraphrased

(Theorem 4.2.11, p. 190) `A` a smooth submanifold of the tame M-polyfold `X`, in general position
at `x ∈ A`.  There is an open `U ∋ x` with: (1) there are precisely `d = d_X(x)` local faces
`F_1, …, F_d` contained in `U` **and containing `x`** (2017: "contained in `U`" only); (2)
`d_X(a) = d_A(a)` on `A ∩ U`; (3) general position at every `a ∈ A ∩ U`; (4) for
`σ ⊆ {1, …, d}`, `F_σ = ⋂_{i ∈ σ} F_i` is a tame M-polyfold and `A ∩ F_σ` a tame smooth
submanifold of `F_σ`, in general position in `F_σ` at its points in `U`.

(Theorem 4.3.1, p. 193) `A ⊆ Z = ℝᵐ ⊕ X` a smooth submanifold of the tame M-polyfold `Z` with
tame induced structure and compact closure, `p = P|_A`, `ε > 0` with (1) `p⁻¹(λ)` compact for
`|λ| ≤ ε` (2017: "compact and non-empty") and (2) general position (the printed hypothesis is
still misprinted, Findings Chapter 4 item 101).  Then there is a **measurable** set
`Σ ⊆ {|λ| < ε}` (2017: "a set") of regular values of `p`, of full measure in `B^m(ε)`, such that
for `λ ∈ Σ` the fibre `A_λ` is a smooth compact manifold with boundary with corners whose tangent
spaces have sc-complements in `T_x^R X`.

## What is formalized

* `Polyfold.MPolyfold.theorem_4_2_11_2021`: Theorem 4.2.11 with (1) in the 2021 form.  The
  existing `MPolyfold.theorem_4_22` (`LocalStructure.lean`) already reads (1) as "`x` lies in
  exactly `d_X(x)` faces of the model of a tame chart centred at `x`", i.e. it counts the local
  faces **through `x`**, which is the 2021 statement; the 2021 version here adds, for each of the
  `d_X(x)` coordinate faces `F_i` (`i < d_X(x)`), its germ `ψ⁻¹(G_i ∩ F_i)`, which **contains `x`
  and is contained in `U`** (read off from (4) for `σ = {i}`).  (2)–(4) are those of
  `theorem_4_22`.
* `Polyfold.theorem_4_3_1_2021`: Theorem 4.3.1 with hypothesis (1) without non-emptiness and
  with `Σ` **measurable**.  The existing `theorem_4_23` (`Families.lean`) assumes non-emptiness
  but never uses it; its `Σ` is not shown measurable.  Here `Σ` is shrunk to a measurable subset
  of the same full measure (the complement of a measurable null hull,
  `MeasureTheory.toMeasurable`), which keeps all other conclusions.

## What the text leaves implicit, and the choices made

* "Local faces" are, as in `theorem_4_22` and `proposition_2_44`, the faces of the model of a
  tame chart centred at `x` (Findings Chapter 4 item 130, gap G.35: the identification with the
  faces of the neighbourhood `U` itself is not formalized).
* "Regular value" is read in the stratified sense of the proof (`IsStratRegularValue`, Findings
  Chapter 4 items 102, 108), and hypothesis (2) as general position at every point, as in
  `theorem_4_23`.  The hypotheses "tame induced structure on `A`" and "`ε > 0`" are kept and
  not used, as there.
-/

open Set Filter Topology Function Module MeasureTheory

noncomputable section

namespace Polyfold

/-! ### Theorem 4.2.11 -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **Theorem 4.2.11 (Local structure of smooth submanifolds), p. 190** (2017: Theorem 4.3;
preprint: Theorem 4.22), in the 2021 form of (1).  Let `X` be a tame M-polyfold, `A ⊆ X` a smooth
finite-dimensional submanifold and `x ∈ A` a point at which `A` is in general position.  Then
there are a tame chart `ψ` of `X` with `ψ(x) = 0` (tame retraction `R` onto the model `O`,
presentation `T : E ≅ ℝⁿ ⊕ W` of the partial quadrant) and an open `U ∋ x` inside the chart
domain such that:
(1) `d_X(x) = n`, `x` lies in exactly `d_X(x)` local faces (faces of the model through `ψ(x)`),
and for every `i < n` the local face `F_i` (the face of the model through `0` in the `i`-th
coordinate hyperplane) has a germ `ψ⁻¹(G ∩ F_i)` **containing `x` and contained in `U`**;
(2) `d_X(a) = d_A(a)` for `a ∈ A ∩ U`;
(3) `A` is in general position at every `a ∈ A ∩ U`;
(4) for every `σ ⊆ {1, …, n}` the intersection of local faces `F_σ = ψ⁻¹(G ∩ ⋂_{i ∈ σ} F_i) ⊆ U`
is a tame sub-M-polyfold with `d_{F_σ} + #σ = d_X`, and `A ∩ F_σ` is a tame smooth submanifold of
`F_σ` in general position at each of its points. -/
theorem theorem_4_2_11_2021 (hP : P.IsTame) {A : Set X} (hA : P.IsSmoothSubmanifold A)
    [ParacompactSpace A] {x : X} (hgp : P.IsGeneralPositionAt A x) :
    ∃ ψ : MChart X, P.IsChart ψ ∧ ∃ hx : x ∈ ψ.source, ψ x = 0 ∧
      ∃ (R : ScRetraction ψ.model.E ψ.model.C) (n : ℕ) (Wq : ScBanach)
        (T : ScIso ψ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
        R.retract = ψ.model.O ∧ ψ.model.C = T 0 ⁻¹' quadrant n Wq 0 ∧ R.IsTameWith T ∧
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ ψ.source ∧
        -- (1)
        P.degIndex x = n ∧
        {F | (ψ.model.toMPolyfold ⟨_, ψ.mapsTo_model x hx⟩).IsFace F ∧
          (⟨ψ x, ψ.mapsTo_model x hx⟩ : ψ.model.O) ∈ F}.encard = (P.degIndex x : ℕ∞) ∧
        (∀ i : Fin n, ∃ Fi G : Set (ψ.model.E 0), R.IsRetractFace Fi ∧ (0 : ψ.model.E 0) ∈ Fi ∧
          Fi ⊆ coordHyper T i ∧ IsOpen G ∧ (0 : ψ.model.E 0) ∈ G ∧
          x ∈ ψ.cornerPreimage G (fun _ : Unit => Fi) ∧
          ψ.cornerPreimage G (fun _ : Unit => Fi) ⊆ U) ∧
        -- (2)
        (∀ a : A, (a : X) ∈ U → (subPolyfold hA.isSubMPolyfold).degIndex a = P.degIndex a) ∧
        -- (3)
        (∀ a ∈ U ∩ A, P.IsGeneralPositionAt A a) ∧
        -- (4)
        ∀ σ : Finset (Fin n), ∃ (Fc : σ → Set (ψ.model.E 0)) (G : Set (ψ.model.E 0)),
          (∀ i, R.IsRetractFace (Fc i) ∧ (0 : ψ.model.E 0) ∈ Fc i ∧ Fc i ⊆ coordHyper T i) ∧
          IsOpen G ∧ (0 : ψ.model.E 0) ∈ G ∧ x ∈ ψ.cornerPreimage G Fc ∧
          ψ.cornerPreimage G Fc ⊆ U ∧
          ∃ hF : P.IsSubMPolyfold (ψ.cornerPreimage G Fc),
            haveI := P.paracompactSpace_subtype (ψ.cornerPreimage G Fc)
            (subPolyfold hF).IsTame ∧
            (∀ a, (subPolyfold hF).degIndex a + σ.card = P.degIndex a) ∧
            (subPolyfold hF).IsSmoothSubmanifold {b | (b : X) ∈ A} ∧
            (∀ b : ψ.cornerPreimage G Fc, (b : X) ∈ A →
              (subPolyfold hF).IsGeneralPositionAt {b | (b : X) ∈ A} b) ∧
            haveI := (subPolyfold hF).paracompactSpace_subtype {b | (b : X) ∈ A}
            (subPolyfold hF).IsTameSubmanifold {b | (b : X) ∈ A} := by
  obtain ⟨ψ, hψ, hx, hψ0, R, n, Wq, T, hR, hT, hRT, U, hU, hxU, hUψ, h1, h1', h2, h3, h4⟩ :=
    theorem_4_22 hP hA hgp
  refine ⟨ψ, hψ, hx, hψ0, R, n, Wq, T, hR, hT, hRT, U, hU, hxU, hUψ, h1, h1', fun i => ?_,
    h2, h3, h4⟩
  obtain ⟨Fc, G, hFc, hG, h0G, hxF, hFU, -⟩ := h4 {i}
  set j : ({i} : Finset (Fin n)) := ⟨i, Finset.mem_singleton_self i⟩ with hj
  have hall : ∀ k : ({i} : Finset (Fin n)), k = j := fun k =>
    Subtype.ext (Finset.mem_singleton.1 k.2)
  have hset : ψ.cornerPreimage G (fun _ : Unit => Fc j) = ψ.cornerPreimage G Fc := by
    ext y
    simp only [MChart.cornerPreimage, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun k => by rw [hall k]; exact h3 ()⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun _ => h3 j⟩
  obtain ⟨hface, h0, hhyp⟩ := hFc j
  exact ⟨Fc j, G, hface, h0, hhyp, hG, h0G, hset ▸ hxF, hset ▸ hFU⟩

end MPolyfold

/-! ### Theorem 4.3.1 -/

section Family

universe u

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} [ParacompactSpace ((Fin m → ℝ) × X)]

/-- **Theorem 4.3.1, p. 193** (2017: Theorem 4.4; preprint: Theorem 4.23), in the 2021 form:
hypothesis (1) asks only that the fibres `p⁻¹(λ)`, `|λ| ≤ ε`, be compact (not non-empty), and the
set `Σ` of regular values is **measurable**.  Let `X` be a tame M-polyfold and `A ⊆ ℝᵐ × X` a
smooth finite-dimensional submanifold with tame induced structure and compact closure, in general
position at every point.  Then there is a measurable `Σ ⊆ {|λ| < ε}` with `{|λ| < ε} ∖ Σ` null,
consisting of (stratified) regular values of `p = P|_A`, such that for `λ ∈ Σ` the fibre `A_λ`
is compact, a smooth finite-dimensional submanifold of `X` in general position at each of its
points, and with its induced structure a manifold with boundary with corners, tame. -/
theorem theorem_4_3_1_2021 (hX : PX.IsTame) {A : Set ((Fin m → ℝ) × X)}
    (hA : ((rnPolyfold m).prod PX).IsSmoothSubmanifold A) [ParacompactSpace A]
    (_hAt : ((rnPolyfold m).prod PX).IsTameSubmanifold A) (hcl : IsCompact (closure A))
    {ε : ℝ} (_hε : 0 < ε)
    (h1 : ∀ lam : Fin m → ℝ, ∑ i, lam i ^ 2 ≤ ε ^ 2 → IsCompact (A ∩ Prod.fst ⁻¹' {lam}))
    (h2 : ∀ z ∈ A, ((rnPolyfold m).prod PX).IsGeneralPositionAt A z) :
    ∃ Sig ⊆ {lam : Fin m → ℝ | ∑ i, lam i ^ 2 < ε ^ 2}, MeasurableSet Sig ∧
      volume ({lam : Fin m → ℝ | ∑ i, lam i ^ 2 < ε ^ 2} \ Sig) = 0 ∧
      ∀ lam ∈ Sig, IsStratRegularValue PX A lam ∧ IsCompact (fibreSet A lam) ∧
        ∃ hF : PX.IsSmoothSubmanifold (fibreSet A lam),
          (∀ x ∈ fibreSet A lam, PX.IsGeneralPositionAt (fibreSet A lam) x) ∧
          haveI := PX.paracompactSpace_subtype (fibreSet A lam)
          (MPolyfold.subPolyfold hF.isSubMPolyfold).HasCornerStructure ∧
            PX.IsTameSubmanifold (fibreSet A lam) := by
  set B : Set (Fin m → ℝ) := {lam | ∑ i, lam i ^ 2 < ε ^ 2} with hB
  obtain ⟨Sig, hSig, hnull, hprop⟩ := theorem_4_23_of_subset hX hA hcl h2 B
  have hBm : MeasurableSet B :=
    measurableSet_lt (by fun_prop) measurable_const
  -- a measurable null hull of the exceptional set
  set N := toMeasurable volume (B \ Sig) with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by rw [hN, measure_toMeasurable]; exact hnull
  have hsub : B \ Sig ⊆ N := subset_toMeasurable _ _
  set Sig' := B \ N with hSig'
  have hSig'Sig : Sig' ⊆ Sig := fun lam hlam => by
    by_contra h
    exact hlam.2 (hsub ⟨hlam.1, h⟩)
  refine ⟨Sig', sdiff_subset, hBm.diff hNm, measure_mono_null (fun lam hlam => ?_) hN0,
    fun lam hlam => ?_⟩
  · by_contra h
    exact hlam.2 ⟨hlam.1, h⟩
  · have hlamS := hSig'Sig hlam
    obtain ⟨hreg, hloc⟩ := hprop lam hlamS
    have hlamε : ∑ i, lam i ^ 2 ≤ ε ^ 2 := (hSig hlamS).le
    have hcpt : IsCompact (fibreSet A lam) := by
      have := (h1 lam hlamε).image continuous_snd
      convert this using 1
      ext x
      constructor
      · intro hx
        exact ⟨(lam, x), ⟨hx, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨hw, hw1⟩, rfl⟩
        have hw1' : w.1 = lam := hw1
        change (lam, w.2) ∈ A
        rw [← hw1']
        exact hw
    have hF : PX.IsSmoothSubmanifold (fibreSet A lam) := fun x hx => by
      obtain ⟨-, ⟨V, hV, hxV, s, hs, himg⟩, -, -⟩ := hloc x hx
      exact ⟨V, hV, hxV, s, hs, himg⟩
    have := PX.paracompactSpace_subtype (fibreSet A lam)
    have hgpF : ∀ x ∈ fibreSet A lam, PX.IsGeneralPositionAt (fibreSet A lam) x :=
      fun x hx => (hloc x hx).2.2.1
    have hgoodF : ∀ x ∈ fibreSet A lam, PX.IsGoodPositionAt (fibreSet A lam) x :=
      fun x hx => (hloc x hx).2.2.2
    obtain ⟨hcs, htameF⟩ := MPolyfold.theorem_4_18 hX hF hgoodF
    exact ⟨hreg, hcpt, hF, hgpF, hcs, htameF⟩

end Family

end Polyfold
