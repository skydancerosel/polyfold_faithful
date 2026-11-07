import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_64

/-! Round trip for V6_64 (§6.7.2, the proof of Proposition 6.12).

A is the conjunction of the three lemmas the project isolates from the proof:
`mem_span_append_of_ker` (the step "`ker Q̃` is spanned by `[d]`, `[T b]`", in `F`),
`gammaProj_wedge_tmul` (formula (91) for `γ^P_T` on families of vectors) and
`comp_comp_eq_of_projLE` (`P(QT) = PT`).  B is the blind author's four-part computation for the
specific data of §6.7.2.

* `A ⇒ B`: (1) and (4) are `gammaProj_wedge_tmul` (twice, resp. once) with the lifts
  `c = [d]_Q`, `[d]_P, [T b]_P`, plus bookkeeping (`linDetEquivOfEq`, re-bracketing); (3) is
  `mem_span_append_of_ker` mapped to `F / R(PT)` and `wedge_append_add_right`; (2) is elementary.
* `B ⇒ A`: `gammaProj_wedge_tmul` follows from B (4) with `Q := P`, no `b̃` (`m = 0`) and
  `dᵢ := fᵢ − P fᵢ` for representatives `fᵢ` of the given lifts `cᵢ`.  The two auxiliary lemmas are
  not consequences of B (B only states their effect in quotients); they are elementary and are
  re-proved here outright (`mem_span_append_of_ker'` copies the project's argument).
-/

namespace RoundTrip.V6_64
open Polyfold Module

set_option linter.unusedSimpArgs false

/-- The project's statement (the three lemmas of the item), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.mem_span_append_of_ker.{0, 0} ∧
  type_of% @Polyfold.gammaProj_wedge_tmul.{0, 0} ∧
  type_of% @Polyfold.comp_comp_eq_of_projLE.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.mem_span_append_of_ker.{0, 0}, @Polyfold.gammaProj_wedge_tmul.{0, 0},
    @Polyfold.comp_comp_eq_of_projLE.{0, 0}⟩

theorem comp_append' {X Y : Type*} (φ : X → Y) {p q : ℕ} (f : Fin p → X) (g : Fin q → X) :
    φ ∘ Fin.append f g = Fin.append (φ ∘ f) (φ ∘ g) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

/-- `A ⇒ B`. -/
theorem A_to_B : A → B := by
  rintro ⟨hspan, hgw, hcc⟩
  intro E F _ _ _ _ _ _ T hT P Q hP hQ hPQ hQT hPQT n k m l a b bt d haT ha hn habQ hab hnk
    habP habt hnkm hdQ hd hl hlkm h mkP αP βP βP'
  have iT := hT.finite_ker
  have iTc : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have := hP.finite_coker
  have := hQ.finite_coker
  have := hQT.finite_ker
  have := (hP.isFredholm_comp hT).finite_ker
  have := (hPQT.isFredholm_comp hQT).finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    hQT.finite_coker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    (hP.isFredholm_comp hT).finite_coker
  have : FiniteDimensional ℝ
      (F ⧸ LinearMap.range ((P ∘L (Q ∘L T) : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    (hPQT.isFredholm_comp hQT).finite_coker
  -- `PQ = P = QP`, `Q² = Q`, `Q d = 0`
  have hPQf : ∀ f, P (Q f) = P f := fun f => by
    simpa using (congrArg (fun A : F →L[ℝ] F => A f) hPQ.1).symm
  have hQPf : ∀ f, Q (P f) = P f := fun f => by
    simpa using (congrArg (fun A : F →L[ℝ] F => A f) hPQ.2).symm
  have hQQ : ∀ f, Q (Q f) = Q f := fun f => by
    simpa using congrArg (fun A : F →L[ℝ] F => A f) hQ.isProj
  have hQd : ∀ i, Q (d i) = 0 := fun i => by
    obtain ⟨y, hy⟩ := hdQ i
    rw [← hy]
    simp [hQQ]
  have hPd : ∀ i, P (d i) = 0 := fun i => by rw [← hPQf, hQd, map_zero]
  have hQTb : ∀ i, Q (T (b i)) = 0 := fun i => by simpa using habQ (Fin.natAdd n i)
  have hPTb : ∀ i, P (T (b i)) = 0 := fun i => by rw [← hPQf, hQTb, map_zero]
  have hPTbt : ∀ i, P (T (bt i)) = 0 := fun i => by simpa using habP (Fin.natAdd (n + k) i)
  have e : ((P ∘L (Q ∘L T) : E →L[ℝ] F) : E →ₗ[ℝ] F) = ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
    rw [hcc (T := T) hPQ]
  have hker : LinearMap.ker ((P ∘L (Q ∘L T) : E →L[ℝ] F) : E →ₗ[ℝ] F) =
      LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) := by rw [e]
  -- the families
  let a' : Fin n → LinearMap.ker (T : E →ₗ[ℝ] F) := fun i => ⟨a i, haT i⟩
  have ha' : LinearIndependent ℝ a' :=
    LinearIndependent.of_comp (LinearMap.ker (T : E →ₗ[ℝ] F)).subtype ha
  let d' : Fin l → F ⧸ LinearMap.range (T : E →ₗ[ℝ] F) := fun i => Submodule.Quotient.mk (d i)
  let b' : Fin k → LinearMap.ker ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) :=
    fun i => ⟨b i, LinearMap.mem_ker.2 (hQTb i)⟩
  have hb' : LinearIndependent ℝ (Fin.append (projSeqJ T Q ∘ a') b') := by
    apply LinearIndependent.of_comp (LinearMap.ker ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).subtype
    convert hab using 1
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · (simp only [Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
    · (simp only [Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
  -- `γ^Q_T(h) = (a ∧ b) ⊗ ([d]_Q ∧ [T b]_Q)*`
  let c1 : Fin l → F ⧸ LinearMap.range (Q : F →ₗ[ℝ] F) := fun i => Submodule.Quotient.mk (d i)
  have hc1 : ∀ i, projSeqPi (T := T) hQ.isProj (c1 i) = d' i := by
    intro i
    simp only [c1, d', projSeqPi_mk, hQd, sub_zero]
  have hC1 : l + k = finrank ℝ (F ⧸ LinearMap.range (Q : F →ₗ[ℝ] F)) :=
    (projSeq hQ).finrank_eq_of_families hn hl hnk
  have hC1' : l + k = finrank ℝ (F ⧸ LinearMap.range ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    hC1.trans (cokerCompEquiv hQ).finrank_eq.symm
  have step1 := hgw hT hQ ha' hn hd hl hb' hnk hc1 hC1'
  let a2 := Fin.append (projSeqJ T Q ∘ a') b'
  let d2 := (cokerCompEquiv hQ).symm ∘ Fin.append c1 (projSeqPhi T Q ∘ b')
  have hd2li : LinearIndependent ℝ d2 :=
    ((projSeq hQ).linearIndependent_append_lift ha' hn hd hl hb' hnk hc1 hC1).map' _
      (cokerCompEquiv hQ).symm.ker
  -- `γ^P_{QT}(γ^Q_T h) = (a ∧ b ∧ b̃) ⊗ ([d]_P ∧ [T b]_P ∧ [Q T b̃]_P)*`
  let bt' : Fin m → LinearMap.ker ((P ∘L (Q ∘L T) : E →L[ℝ] F) : E →ₗ[ℝ] F) :=
    fun i => ⟨bt i, LinearMap.mem_ker.2 (by simp [hPQf, hPTbt])⟩
  have hbt' : LinearIndependent ℝ (Fin.append (projSeqJ (Q ∘L T) P ∘ a2) bt') := by
    apply LinearIndependent.of_comp
      (LinearMap.ker ((P ∘L (Q ∘L T) : E →L[ℝ] F) : E →ₗ[ℝ] F)).subtype
    convert habt using 1
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · (simp only [a2, Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
      · (simp only [a2, Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
    · (simp only [a2, Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
  have hk' : n + k + m = finrank ℝ (LinearMap.ker ((P ∘L (Q ∘L T) : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    hnkm.trans (LinearEquiv.ofEq _ _ hker).finrank_eq.symm
  let c2 : Fin (l + k) → F ⧸ LinearMap.range (P : F →ₗ[ℝ] F) :=
    fun i => Submodule.Quotient.mk (Fin.append d (fun i => T (b i)) i)
  have hc2 : ∀ i, projSeqPi (T := Q ∘L T) hPQT.isProj (c2 i) = d2 i := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      simp only [c2, d2, Function.comp_apply, Fin.append_left, projSeqPi_mk, hPd, sub_zero, c1]
      rfl
    | right i =>
      simp only [c2, d2, Function.comp_apply, Fin.append_right, projSeqPi_mk, hPTb, sub_zero]
      rfl
  have hC2 : l + k + m = finrank ℝ (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)) :=
    (projSeq hPQT).finrank_eq_of_families hnk hC1' hk'
  have hC2' : l + k + m =
      finrank ℝ (F ⧸ LinearMap.range ((P ∘L (Q ∘L T) : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    hC2.trans (cokerCompEquiv hPQT).finrank_eq.symm
  have step2 := hgw hQT hPQT hb' hnk hd2li hC1' hbt' hk' hc2 hC2'
  let w2 := Fin.append c2 (projSeqPhi (Q ∘L T) P ∘ bt')
  have hw2li : LinearIndependent ℝ ((cokerCompEquiv hPQT).symm ∘ w2) :=
    ((projSeq hPQT).linearIndependent_append_lift hb' hnk hd2li hC1' hbt' hk' hc2 hC2).map' _
      (cokerCompEquiv hPQT).symm.ker
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1)
    refine (congrArg (fun x => linDetEquivOfEq e (gammaProj hQT hPQT x)) step1).trans ?_
    refine (congrArg (fun x => linDetEquivOfEq e x) step2).trans ?_
    refine (linDetEquivOfEq_tmul e _ _ _ hw2li _).trans ?_
    refine congrArg₂ (fun x y => x ⊗ₜ[ℝ] y) ?_ (congrArg dualVec ?_)
    · refine congrArg (fun v => wedge v hnkm) ?_
      funext i
      apply Subtype.ext
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · (simp only [a2, Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
        · (simp only [a2, Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
      · (simp only [a2, Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
    · refine congrArg (fun v => wedge v hlkm) ?_
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simp only [Function.comp_apply, w2, c2, Fin.append_left]
          rfl
        · simp only [Function.comp_apply, w2, c2, Fin.append_left, Fin.append_right]
          rfl
      · simp only [Function.comp_apply, w2, Fin.append_right]
        rfl
  · -- (2) the split `F / R(P) = ker Q̃ ⊕ ker(I − Q̃)`
    have hRQ : ∀ y ∈ LinearMap.range (P : F →ₗ[ℝ] F), Q y ∈ LinearMap.range (P : F →ₗ[ℝ] F) := by
      rintro _ ⟨f, rfl⟩
      exact ⟨f, (hQPf f).symm⟩
    constructor
    · rw [Submodule.disjoint_def]
      rintro x ⟨f, hf, rfl⟩ ⟨g, hg, hgf⟩
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hgf
      have hf' : Q f ∈ LinearMap.range (P : F →ₗ[ℝ] F) := hf
      have hg' : g - Q g ∈ LinearMap.range (P : F →ₗ[ℝ] F) := hg
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      have hfe : f = Q f + ((g - Q g) - (g - f) + Q (g - f)) := by rw [map_sub]; abel
      rw [hfe]
      exact add_mem hf' (add_mem (sub_mem hg' hgf) (hRQ _ hgf))
    · rw [codisjoint_iff, eq_top_iff]
      rintro x -
      obtain ⟨f, rfl⟩ := (LinearMap.range (P : F →ₗ[ℝ] F)).mkQ_surjective x
      have hsplit : (LinearMap.range (P : F →ₗ[ℝ] F)).mkQ f =
          (LinearMap.range (P : F →ₗ[ℝ] F)).mkQ (f - Q f) +
            (LinearMap.range (P : F →ₗ[ℝ] F)).mkQ (Q f) := by
        rw [← map_add, sub_add_cancel]
      rw [hsplit]
      refine Submodule.add_mem_sup ⟨f - Q f, ?_, rfl⟩ ⟨Q f, ?_, rfl⟩
      · show Q (f - Q f) ∈ LinearMap.range (P : F →ₗ[ℝ] F)
        rw [map_sub, hQQ, sub_self]
        exact zero_mem _
      · show Q f - Q (Q f) ∈ LinearMap.range (P : F →ₗ[ℝ] F)
        rw [hQQ, sub_self]
        exact zero_mem _
  · -- (3) replacing `[Q T b̃]` by `[T b̃]`
    show wedge (Fin.append (Fin.append (fun i => mkP (d i)) (fun i => mkP (T (b i))))
      (fun i => mkP (Q (T (bt i))))) hlkm =
      wedge (Fin.append (Fin.append (fun i => mkP (d i)) (fun i => mkP (T (b i))))
      (fun i => mkP (T (bt i)))) hlkm
    have hsplit : (fun i => mkP (T (bt i))) = (fun i => mkP (Q (T (bt i)))) +
        fun i => mkP (T (bt i) - Q (T (bt i))) := by
      funext i
      simp only [Pi.add_apply, mkP]
      rw [← Submodule.Quotient.mk_add, add_sub_cancel]
    rw [hsplit, wedge_append_add_right]
    intro i
    let d0 := basisOfLinearIndependentOfCardEqFinrank' _ hd (by rw [Fintype.card_fin]; exact hl)
    have hg := hspan hT hQ d0 (dt := d) (fun i => by simp [d0]) hQd hb' hnk
      (g := T (bt i) - Q (T (bt i))) (by rw [map_sub, hQQ, sub_self])
    have hg' := Submodule.mem_map_of_mem
      (f := (LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).mkQ) hg
    rw [← Submodule.span_image, ← Set.range_comp, comp_append'] at hg'
    exact hg'
  · -- (4) `γ^P_T(h)`
    let bP : Fin k → LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) :=
      fun i => ⟨b i, LinearMap.mem_ker.2 (hPTb i)⟩
    let btP : Fin m → LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) :=
      fun i => ⟨bt i, LinearMap.mem_ker.2 (hPTbt i)⟩
    have hab3 : LinearIndependent ℝ (Fin.append a (Fin.append b bt)) := by
      rw [Fin.append_assoc] at habt
      exact habt.comp (Fin.cast (Nat.add_assoc n k m).symm) (Fin.cast_injective _)
    have hb3 : LinearIndependent ℝ (Fin.append (projSeqJ T P ∘ a') (Fin.append bP btP)) := by
      apply LinearIndependent.of_comp (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).subtype
      convert hab3 using 1
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · (simp only [a2, Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · (simp only [a2, Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
        · (simp only [a2, Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
    have hj3 : n + (k + m) = finrank ℝ (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) := by
      omega
    let c3 : Fin l → F ⧸ LinearMap.range (P : F →ₗ[ℝ] F) := fun i => Submodule.Quotient.mk (d i)
    have hc3 : ∀ i, projSeqPi (T := T) hP.isProj (c3 i) = d' i := by
      intro i
      simp only [c3, d', projSeqPi_mk, hPd, sub_zero]
    have hC3 : l + (k + m) =
        finrank ℝ (F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) := by omega
    have step4 := hgw hT hP ha' hn hd hl hb3 hj3 hc3 hC3
    refine step4.trans (congrArg₂ (fun x y => x ⊗ₜ[ℝ] y) ?_ (congrArg dualVec ?_))
    · refine (wedge_append_assoc _ _ _ hj3 hnkm).trans ?_
      refine congrArg (fun v => wedge v hnkm) ?_
      funext i
      apply Subtype.ext
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · (simp only [a2, Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
        · (simp only [a2, Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
      · (simp only [a2, Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
    · have hfun : ⇑(cokerCompEquiv hP).symm ∘ Fin.append c3 (projSeqPhi T P ∘ Fin.append bP btP) =
          Fin.append (fun i => mkP (d i))
            (Fin.append (fun i => mkP (T (b i))) (fun i => mkP (T (bt i)))) := by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simp only [Function.comp_apply, Fin.append_left]
          rfl
        · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
          · simp only [Function.comp_apply, Fin.append_right, Fin.append_left]
            rfl
          · simp only [Function.comp_apply, Fin.append_right]
            rfl
      rw [hfun]
      exact wedge_append_assoc _ _ _ hC3 hlkm

/-- `mem_span_append_of_ker`, re-proved (the project's argument, copied): B does not contain it. -/
theorem mem_span_append_of_ker' {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {T : E →L[ℝ] F} {Q : F →L[ℝ] F} (hT : T.IsFredholm) (hQ : IsGoodLeftProj T Q)
    {n l m : ℕ} {a : Fin n → LinearMap.ker (T : E →ₗ[ℝ] F)}
    (d0 : Basis (Fin l) ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))) {dt : Fin l → F}
    (hdt : ∀ i, Submodule.Quotient.mk (dt i) = d0 i) (hQdt : ∀ i, Q (dt i) = 0)
    {b : Fin m → LinearMap.ker ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)}
    (hb : LinearIndependent ℝ (Fin.append (projSeqJ T Q ∘ a) b))
    (hm : n + m = finrank ℝ (LinearMap.ker ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)))
    {g : F} (hg : Q g = 0) :
    g ∈ Submodule.span ℝ (Set.range (Fin.append dt (fun i => T (b i : E)))) := by
  have := (hQ.isFredholm_comp hT).finite_ker
  have hg0 : (Submodule.Quotient.mk g : F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) ∈
      Submodule.span ℝ (Set.range d0) := d0.span_eq ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hg0
  have hmem : g - ∑ i, r i • dt i ∈ LinearMap.range (T : E →ₗ[ℝ] F) := by
    rw [← Submodule.Quotient.mk_eq_zero]
    have : (LinearMap.range (T : E →ₗ[ℝ] F)).mkQ (g - ∑ i, r i • dt i) = 0 := by
      rw [map_sub, map_sum]
      simp only [map_smul, Submodule.mkQ_apply, hdt]
      rw [hr, sub_self]
    exact this
  obtain ⟨x, hx⟩ := hmem
  have hx' : T x = g - ∑ i, r i • dt i := hx
  have hxQ : Q (T x) = 0 := by
    rw [hx', map_sub, hg, map_sum]
    simp [hQdt]
  let xk : LinearMap.ker ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) := ⟨x, by simpa using hxQ⟩
  have hxspan : xk ∈ Submodule.span ℝ (Set.range (Fin.append (projSeqJ T Q ∘ a) b)) :=
    (hb.span_eq_top_of_card_eq_finrank' (by simp [hm])) ▸ Submodule.mem_top
  have hle : Submodule.span ℝ (Set.range (Fin.append (projSeqJ T Q ∘ a) b)) ≤
      (Submodule.span ℝ (Set.range (fun i => T (b i : E)))).comap
        ((T : E →ₗ[ℝ] F) ∘ₗ (LinearMap.ker ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).subtype) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i =>
      have hTa : T ((a i : LinearMap.ker (T : E →ₗ[ℝ] F)) : E) = 0 := (a i).2
      simp only [Fin.append_left, Function.comp_apply, SetLike.mem_coe,
        Submodule.mem_comap, LinearMap.comp_apply, Submodule.coe_subtype]
      change T ((a i : LinearMap.ker (T : E →ₗ[ℝ] F)) : E) ∈ _
      rw [hTa]
      exact zero_mem _
    | right i =>
      simp only [Fin.append_right, SetLike.mem_coe, Submodule.mem_comap,
        LinearMap.comp_apply, Submodule.coe_subtype, ContinuousLinearMap.coe_coe]
      exact Submodule.subset_span ⟨i, rfl⟩
  have hTx : T x ∈ Submodule.span ℝ (Set.range (fun i => T (b i : E))) := hle hxspan
  rw [span_range_append]
  have : g = ∑ i, r i • dt i + T x := by rw [hx']; abel
  rw [this]
  exact Submodule.add_mem_sup
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) hTx

/-- `B ⇒ A`: `gammaProj_wedge_tmul` from B (4) with `Q := P`, `m := 0`; the two auxiliary lemmas
re-proved outright. -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro E F _ _ _ _ _ _ T Q hT hQ n l m a d0 dt hdt hQdt b hb hm g hg
    exact mem_span_append_of_ker' hT hQ d0 hdt hQdt hb hm hg
  · intro E F _ _ _ _ _ _ T P hT hP n l j a ha hn d hd hl b hb hj c hc hC
    have hPPT : P ∘L (P ∘L T) = P ∘L T := by
      rw [← ContinuousLinearMap.comp_assoc, hP.isProj]
    have hPT : IsGoodLeftProj (P ∘L T) P :=
      { isProj := hP.isProj, finite_coker := hP.finite_coker
        range_comp := by rw [hPPT]; exact hP.range_comp }
    choose f hf using fun i => Submodule.Quotient.mk_surjective _ (c i)
    let dd : Fin l → F := fun i => f i - P (f i)
    have hdd : (fun i => (Submodule.Quotient.mk (dd i) :
        F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))) = d := by
      funext i
      rw [← hc i, ← hf i]
      rfl
    have haT : ∀ i, (a i : E) ∈ LinearMap.ker (T : E →ₗ[ℝ] F) := fun i => (a i).2
    have haE : LinearIndependent ℝ (fun i => (a i : E)) :=
      ha.map' _ (LinearMap.ker (T : E →ₗ[ℝ] F)).ker_subtype
    have habQ : ∀ i, Fin.append (fun i => (a i : E)) (fun i => (b i : E)) i ∈
        LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]; exact ker_le_ker_comp T P (a i).2
      · rw [Fin.append_right]; exact (b i).2
    have habE : LinearIndependent ℝ (Fin.append (fun i => (a i : E)) (fun i => (b i : E))) := by
      have := hb.map' _ (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).ker_subtype
      have e : ⇑(LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).subtype ∘
          Fin.append (projSeqJ T P ∘ a) b = Fin.append (fun i => (a i : E)) (fun i => (b i : E)) := by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · (simp only [Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
        · (simp only [Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
      rw [e] at this
      exact this
    let bt : Fin 0 → E := fun i => i.elim0
    have habP : ∀ i, Fin.append (Fin.append (fun i => (a i : E)) (fun i => (b i : E))) bt i ∈
        LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => i.elim0) i
      rw [Fin.append_left]; exact habQ i
    have habtE : LinearIndependent ℝ
        (Fin.append (Fin.append (fun i => (a i : E)) (fun i => (b i : E))) bt) := by
      rw [Fin.append_right_nil _ _ rfl]
      exact habE.comp _ (Fin.cast_injective _)
    have hnkm : n + j + 0 = finrank ℝ (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) := hj
    have hddR : ∀ i, dd i ∈ LinearMap.range (((1 : F →L[ℝ] F) - P : F →L[ℝ] F) : F →ₗ[ℝ] F) :=
      fun i => ⟨f i, by simp [dd]⟩
    have hddLI : LinearIndependent ℝ
        (fun i => Submodule.Quotient.mk (p := LinearMap.range (T : E →ₗ[ℝ] F)) (dd i)) := by
      rw [hdd]; exact hd
    have hlkm : l + j + 0 =
        finrank ℝ (F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) := hC
    have key := (hB T hT P P hP hP (ProjLE.refl hP.isProj) (hP.isFredholm_comp hT) hPT
      (fun i => (a i : E)) (fun i => (b i : E)) bt dd haT haE hn habQ habE hj habP habtE hnkm
      hddR hddLI hl hlkm).2.2.2
    have hv : ∀ i, ((Fin.append (projSeqJ T P ∘ a) b i :
        LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) : E) =
        Fin.append (fun i => (a i : E)) (fun i => (b i : E)) i := by
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · (simp only [Function.comp_apply, Fin.append_left, Fin.append_right]; rfl)
      · simp only [Function.comp_apply, Fin.append_left, Fin.append_right]
    have e1 : wedge (fun i => (⟨Fin.append (Fin.append (fun i => (a i : E))
        (fun i => (b i : E))) bt i, habP i⟩ : LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)))
          hnkm = wedge (Fin.append (projSeqJ T P ∘ a) b) hj := by
      refine Eq.trans ?_ (wedge_cast (Fin.append (projSeqJ T P ∘ a) b) hj (Nat.add_zero (n + j)))
      refine congrArg (fun v => wedge v hnkm) ?_
      funext i
      apply Subtype.ext
      refine Fin.addCases (fun i => ?_) (fun i => i.elim0) i
      simp only [Fin.append_left, Function.comp_apply]
      rw [hv]
      rfl
    have hw : ∀ i, (cokerCompEquiv hP).symm (Fin.append c (projSeqPhi T P ∘ b) i) =
        Fin.append (fun i => (Submodule.Quotient.mk (dd i) :
          F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)))
          (fun i => Submodule.Quotient.mk (T (b i : E))) i := by
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        rw [← hf i]
        show (Submodule.Quotient.mk (f i) :
          F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) =
            Submodule.Quotient.mk (f i - P (f i))
        rw [Submodule.Quotient.eq, hP.range_comp, sub_sub_cancel]
        exact ⟨f i, rfl⟩
      · simp only [Fin.append_right, Function.comp_apply]
        rfl
    have e2 : wedge (Fin.append (Fin.append (fun i => (Submodule.Quotient.mk (dd i) :
        F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)))
        (fun i => Submodule.Quotient.mk (T (b i : E)))) (fun i => Submodule.Quotient.mk (T (bt i))))
          hlkm = wedge ((cokerCompEquiv hP).symm ∘ Fin.append c (projSeqPhi T P ∘ b)) hC := by
      refine Eq.trans ?_ (wedge_cast _ hC (Nat.add_zero (l + j)))
      refine congrArg (fun v => wedge v hlkm) ?_
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => i.elim0) i
      simp only [Fin.append_left, Function.comp_apply]
      rw [hw]
      rfl
    refine Eq.trans ?_ (key.trans ?_)
    · exact congrArg (fun x : Fin l → F ⧸ LinearMap.range (T : E →ₗ[ℝ] F) =>
        gammaProj hT hP (wedge a hn ⊗ₜ[ℝ] dualVec (wedge x hl))) hdd.symm
    · exact congrArg₂ (fun x y => x ⊗ₜ[ℝ] dualVec y) e1 e2
  · intro E F _ _ _ _ _ _ T P Q hPQ
    rw [← ContinuousLinearMap.comp_assoc, ← hPQ.1]

#rt_check RoundTrip.V6_64.A_to_B [Polyfold.mem_span_append_of_ker, Polyfold.gammaProj_wedge_tmul,
  Polyfold.comp_comp_eq_of_projLE]
#rt_check RoundTrip.V6_64.B_to_A [Polyfold.mem_span_append_of_ker, Polyfold.gammaProj_wedge_tmul,
  Polyfold.comp_comp_eq_of_projLE]
#rt_overlap RoundTrip.V6_64.B_to_A [Polyfold.mem_span_append_of_ker,
  Polyfold.gammaProj_wedge_tmul, Polyfold.comp_comp_eq_of_projLE]

end RoundTrip.V6_64
