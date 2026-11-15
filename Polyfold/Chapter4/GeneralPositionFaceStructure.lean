import Polyfold.Chapter4.LocalStructure
import Polyfold.Chapter2.FaceLabels

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.2,
**Theorem 4.2.11** (p. 190; preprint Theorem 4.22) and **Definition 2.5.10** (p. 60).

# A submanifold in general position of a face-structured M-polyfold is face-structured

## The text

Theorem 4.2.11: for a smooth submanifold `A` of a tame `X`, in general position at `x`, there are
exactly `d = d_X(x)` local faces `F_1, …, F_d` at `x`, `d_A = d_X` on `A` near `x`, and
`A ∩ F_σ` is a tame submanifold of `F_σ` in general position.  Stokes' theorem (Theorem 4.4.7)
and the boundary terms of Chapter 6 use that the faces of `A` are cut out by the faces of `X`.

## What is formalized

* **`MPolyfold.theorem_4_2_11_exists_mem_coordHyper`**: in the tame chart `ψ` of
  `theorem_4_2_11_preprint`, for every half-line coordinate `λ_i` there are points of `A`
  arbitrarily near `x` with `d_X = 1` and `λ_i = 0`.  *Proof*: `A ∩ F_{\{i\}}` is a tame
  submanifold of the local face `F_{\{i\}}` (Theorem 4.2.11 (4)); its points with `d = 0`
  are dense (`exists_degIndex_eq_zero_of_isTame`); there `d_{F_{\{i\}}} = 0` by (2) applied in
  `F_{\{i\}}`, so `d_X = 1`.
* **`MPolyfold.theorem_4_2_11_isFaceStructured`**: let `X` be tame and face-structured and `A` a
  smooth submanifold in general position at every point, with tame induced structure.  Then `A`
  is face-structured.  *Proof*: the label `a ↦ cc_{d_X = 1}(a)` (the component of `{d_X = 1}`,
  hence the face of `X`) is a face label on `A`, since `d_A = d_X`; at `a ∈ A`, the `d(a)` local
  pieces of `{d_X = 1}` at `a` carry distinct labels (`X` face-structured) and lie in distinct
  coordinate hyperplanes of `ψ` (every hyperplane is met, by the first item, and there are as
  many hyperplanes as pieces); every piece contains points of `A` near `a`.  The label criterion
  `MPolyfold.isFaceStructured_of_label` concludes.

## Reading

The tameness of the induced structure is a hypothesis here; Theorem 4.2.7 with Lemma 4.2.8
(general position implies good position, `IsGeneralPositionAt.isGoodPositionAt` in Chapter 6)
gives it, and the corollary without it is `theorem_4_2_11_isFaceStructured_of_tame` in
`Chapter9/IntervalCobordismFaceStructure.lean`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace MPolyfold

open TameBoundary

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **Points of `A` on each local face** (from Theorem 4.2.11 (2), (4)): in the tame chart `ψ`
of `theorem_4_2_11_preprint` at `x`, for every half-line coordinate `λ_i` and every
neighbourhood `N` of `x` there is `w ∈ A ∩ N` in the domain of `ψ` with `d_X(w) = 1` and
`λ_i(ψ w) = 0`. -/
theorem theorem_4_2_11_exists_mem_coordHyper {A : Set X} {x : X} (hxA : x ∈ A)
    {ψ : MChart X} {R : ScRetraction ψ.model.E ψ.model.C} {n : ℕ} {Wq : ScBanach}
    {T : ScIso ψ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)} {U : Set X}
    (h4 : ∀ σ : Finset (Fin n), ∃ (Fc : σ → Set (ψ.model.E 0)) (G : Set (ψ.model.E 0)),
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
            (subPolyfold hF).IsTameSubmanifold {b | (b : X) ∈ A})
    (i : Fin n) {N : Set X} (hN : N ∈ 𝓝 x) :
    ∃ w ∈ A, w ∈ N ∧ w ∈ ψ.source ∧ P.degIndex w = 1 ∧ (T 0 (ψ w)).1 i = 0 := by
  obtain ⟨Fc, G, hFc, -, -, hxF, -, hF, hFt, hFd, hFsm, hFgp, hFtame⟩ := h4 {i}
  have := P.paracompactSpace_subtype (ψ.cornerPreimage G Fc)
  have := (subPolyfold hF).paracompactSpace_subtype {b | (b : X) ∈ A}
  obtain ⟨hA', hA't⟩ := hFtame
  set x' : {b : ψ.cornerPreimage G Fc | (b : X) ∈ A} := ⟨⟨x, hxF⟩, hxA⟩
  have hN' : (fun q : {b : ψ.cornerPreimage G Fc | (b : X) ∈ A} =>
      ((q : ψ.cornerPreimage G Fc) : X)) ⁻¹' N ∈ 𝓝 x' :=
    (continuous_subtype_val.comp continuous_subtype_val).continuousAt.preimage_mem_nhds hN
  obtain ⟨q, hqN, hq0⟩ := exists_degIndex_eq_zero_of_isTame _ hA't x' hN'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, U', -, hqU', -, -, -, h2', -, -⟩ :=
    theorem_4_2_11_preprint hFt hFsm (hFgp q.1 q.2)
  have hQ0 : (subPolyfold hF).degIndex q.1 = 0 := by
    rw [← h2' q hqU']; exact hq0
  have hd1 : P.degIndex ((q : ψ.cornerPreimage G Fc) : X) = 1 := by
    have := hFd q.1
    rw [hQ0, Finset.card_singleton] at this
    omega
  have hqF := (q : ψ.cornerPreimage G Fc).2
  refine ⟨_, q.2, hqN, hqF.1, hd1, ?_⟩
  exact (hFc ⟨i, Finset.mem_singleton_self i⟩).2.2 (hqF.2.2 ⟨i, Finset.mem_singleton_self i⟩)

/-- **2021 Theorem 4.2.11, the faces of a submanifold in general position**: let `X` be tame and
face-structured (Definition 2.5.10) and `A ⊆ X` a smooth finite-dimensional submanifold in
general position (Definition 4.2.10) at every point, whose induced structure is tame.  Then `A`
is face-structured: every `a ∈ A` lies in exactly `d_A(a)` faces of `A`. -/
theorem theorem_4_2_11_isFaceStructured (hP : P.IsTame) (hfs : P.IsFaceStructured) {A : Set X}
    (hA : P.IsSmoothSubmanifold A) [ParacompactSpace A]
    (htame : (subPolyfold hA.isSubMPolyfold).IsTame)
    (hgp : ∀ a ∈ A, P.IsGeneralPositionAt A a) :
    (subPolyfold hA.isSubMPolyfold).IsFaceStructured := by
  classical
  have hPc := P.isCornerIndex_degIndex hP
  have hΛP : IsFaceLabel P.degIndex (ccLabel P.degIndex) := isFaceLabel_ccLabel
  have hrP := (isFaceStructured_iff_label hP).1 hfs
  have hdeg : ∀ a : A, (subPolyfold hA.isSubMPolyfold).degIndex a = P.degIndex a := fun a => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, U, -, haU, -, -, -, h2, -, -⟩ :=
      theorem_4_2_11_preprint hP hA (hgp a a.2)
    exact h2 a haU
  refine isFaceStructured_of_label htame (Λ := fun a : A => ccLabel P.degIndex (a : X)) ?_ ?_
  · intro S hS hSc p hp q hq
    refine hΛP (Subtype.val '' S) ?_ (hSc.image _ continuous_subtype_val.continuousOn) _
      (mem_image_of_mem _ hp) _ (mem_image_of_mem _ hq)
    rintro _ ⟨b, hb, rfl⟩
    change P.degIndex b = 1
    rw [← hdeg]; exact hS hb
  · intro a
    obtain ⟨ψ, hψ, hx, -, R, n, Wq, T, hR, hC, hRT, U, -, -, -, hdn, -, -, -, h4⟩ :=
      theorem_4_2_11_preprint hP hA (hgp a a.2)
    have key := fun i (N : Set X) (hN : N ∈ 𝓝 (a : X)) =>
      theorem_4_2_11_exists_mem_coordHyper a.2 h4 i hN
    obtain ⟨LP⟩ := hPc.exists_localPieces (ψ.isOpen_source.mem_nhds hx)
    have hinj : Injective fun b => ccLabel P.degIndex (LP.pt b) := LP.injective_label hΛP hrP
    have hdegc : ∀ z ∈ ψ.source, P.degIndex z = degIndexWith T (ψ z) := fun z hz => by
      rw [P.degIndex_eq_chartDegIndex_of_isTameWith hψ R hR hC hRT hz, chartDegIndex,
        degIndex_eq T hC (ψ.apply_mem_C hz)]
    -- a local piece lies in one coordinate hyperplane of `ψ`
    have hpiece : ∀ b, ∀ w ∈ LP.piece b, ∀ i, (T 0 (ψ w)).1 i = 0 →
        ∀ w' ∈ LP.piece b, (T 0 (ψ w')).1 i = 0 := by
      intro b w hw i hi w' hw'
      have hsub := LP.piece_subset b
      have hS : IsPreconnected (ψ '' LP.piece b) :=
        (LP.isPreconnected b).image ψ (ψ.continuousOn_toFun.mono fun z hz => (hsub hz).1)
      have hSC : ψ '' LP.piece b ⊆ ψ.model.C := by
        rintro _ ⟨z, hz, rfl⟩; exact ψ.apply_mem_C (hsub hz).1
      have h1 : ∀ z ∈ ψ '' LP.piece b, degIndexWith T z = 1 := by
        rintro _ ⟨z, hz, rfl⟩; rw [← hdegc z (hsub hz).1]; exact (hsub hz).2
      exact subset_coordHyper_of_isPreconnected hC hS hSC h1 (mem_image_of_mem ψ hw) hi
        (mem_image_of_mem ψ hw')
    have hone : ∀ b, ∃ i, zeroSet T (ψ (LP.pt b)) = {i} := fun b => by
      have hb := LP.piece_subset b (LP.pt_mem b)
      have h1 := hb.2
      rw [mem_ofPred_eq, hdegc _ hb.1, degIndexWith_eq_card_zeroSet, Finset.card_eq_one] at h1
      exact h1
    choose c hc using hone
    have hcz : ∀ b, ∀ w ∈ LP.piece b, (T 0 (ψ w)).1 (c b) = 0 := fun b w hw =>
      hpiece b (LP.pt b) (LP.pt_mem b) (c b)
        ((mem_zeroSet T).1 (by rw [hc b]; exact Finset.mem_singleton_self _)) w hw
    have hci : ∀ b, ∀ w ∈ LP.piece b, ∀ i, (T 0 (ψ w)).1 i = 0 → c b = i := by
      intro b w hw i hi
      have hws := LP.piece_subset b hw
      have h1 : degIndexWith T (ψ w) = 1 := by rw [← hdegc w hws.1]; exact hws.2
      have hz := zeroSet_eq_singleton h1 hi
      have hcm : c b ∈ zeroSet T (ψ w) := (mem_zeroSet T).2 (hcz b w hw)
      rw [hz, Finset.mem_singleton] at hcm
      exact hcm
    have hcs : Surjective c := by
      intro i
      obtain ⟨w, -, hwB, -, hw1, hwi⟩ := key i LP.B (LP.isOpen_B.mem_nhds LP.mem_B)
      obtain ⟨b, hb⟩ := mem_iUnion.1 (LP.cover ⟨hwB, hw1⟩)
      exact ⟨b, hci b w hb i hwi⟩
    have hcinj : Injective c := (Finite.injective_iff_surjective_of_equiv (finCongr hdn)).2 hcs
    refine ⟨Finset.univ.image fun b => ccLabel P.degIndex (LP.pt b), ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hdeg a]
    · intro l hl N hN
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hl
      obtain ⟨N', hN', hN'N⟩ := (mem_nhds_induced Subtype.val a N).1 hN
      obtain ⟨w, hwA, hwN, -, hw1, hwi⟩ :=
        key (c b) (N' ∩ LP.B) (inter_mem hN' (LP.isOpen_B.mem_nhds LP.mem_B))
      obtain ⟨b', hb'⟩ := mem_iUnion.1 (LP.cover ⟨hwN.2, hw1⟩)
      have hbb : b' = b := hcinj (hci b' w hb' (c b) hwi)
      subst hbb
      refine ⟨⟨w, hwA⟩, hN'N hwN.1, ?_, hΛP.eq_of_mem_piece LP b' hb'⟩
      rw [hdeg]; exact hw1

end MPolyfold

end Polyfold
