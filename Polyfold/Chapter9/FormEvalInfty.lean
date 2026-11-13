import Polyfold.Chapter9.FormEvalEp
import Polyfold.Chapter7.ZhouLevels
import Polyfold.Chapter9.TangentSubmanifoldSmooth

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §8.2 (Definition 8.2.1, p. 281) and §9.5, pp. 438–445 (gap G.107).  Numbers and pages
are the 2021 text's.

# Smooth finite-dimensional submanifolds and their tangent spaces on the level `X¹`

A smooth finite-dimensional submanifold `N` of an M-polyfold `X` lies in `X_∞`; it is a smooth
finite-dimensional submanifold of `X¹` (`IsSmoothSubmanifold.levelOne`), and the natural
inclusion `T(X¹) → TX` (`tangentLower`) maps `T_y(N ⊆ X¹)` bijectively onto `T_yN`
(`mem_submanifoldTangent_levelOne_iff`, `exists_tangentLower_eq_of_mem_submanifoldTangent`).
This is the step from the forms on `Xⁱ` to the forms on `Xⁱ⁺¹` in the evaluation of the classes
of `Ωⁿ_{ep,∞}(X)` on the tangent spaces of the sheets.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology Module

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

namespace SubmanifoldData

variable {A : Set X} (d : P.SubmanifoldData A)

/-- The sc⁺-retraction `s` read on `X¹`. -/
def liftS (x₀ : P.Level 1) : P.Level 1 → P.Level 1 :=
  (P.toLevelOne x₀ ∘ d.s) ∘ P.levelVal 1

theorem levelVal_liftS (x₀ : P.Level 1) {x : P.Level 1} (hx : P.levelVal 1 x ∈ d.V) :
    P.levelVal 1 (d.liftS x₀ x) = d.s (P.levelVal 1 x) :=
  levelVal_toLevelOne x₀ (d.isScPlusRetractionOn.mem_levelSet _ hx)

theorem isScPlusRetractionOn_liftS (hA : A ⊆ P.smoothSet) (x₀ : P.Level 1) :
    P.shift.IsScPlusRetractionOn (d.liftS x₀) {x | P.levelVal 1 x ∈ d.V} := by
  have hmem : ∀ x : P.Level 1, P.levelVal 1 x ∈ d.V → d.liftS x₀ x ∈ P.shift.levelSet 1 := by
    intro x hx
    have h1 : d.s (P.levelVal 1 x) ∈ A ∩ d.V := d.image ▸ mem_image_of_mem d.s hx
    have h2 : P.levelVal 1 (d.liftS x₀ x) ∈ P.smoothSet := by
      rw [d.levelVal_liftS x₀ hx]; exact hA h1.1
    exact mem_iInter.1 ((mem_shift_smoothSet_iff _).2 h2) 1
  refine ⟨d.isScPlusRetractionOn.isScSmoothOn.levelOne fun x hx => d.levelVal_liftS x₀ hx,
    fun x hx => ?_, fun x hx => level_ext ?_, hmem, fun y₀ => ?_⟩
  · change P.levelVal 1 (d.liftS x₀ x) ∈ d.V
    rw [d.levelVal_liftS x₀ hx]; exact d.isScPlusRetractionOn.mapsTo hx
  · have hx' : P.levelVal 1 (d.liftS x₀ x) ∈ d.V := by
      rw [d.levelVal_liftS x₀ hx]; exact d.isScPlusRetractionOn.mapsTo hx
    rw [d.levelVal_liftS x₀ hx', d.levelVal_liftS x₀ hx]
    exact d.isScPlusRetractionOn.idem _ hx
  · refine (d.isScPlusRetractionOn.isScSmoothOn_one x₀).levelOne fun x hx => ?_
    exact levelVal_toLevelOne (P := P.shift) y₀ (hmem x hx)

/-- **The data of Definition 4.2.1 on the level `X¹`.** -/
def levelOne (hA : A ⊆ P.smoothSet) (x₀ : P.Level 1) :
    P.shift.SubmanifoldData {x : P.Level 1 | P.levelVal 1 x ∈ A} where
  V := {x | P.levelVal 1 x ∈ d.V}
  s := d.liftS x₀
  isOpen := d.isOpen.preimage (continuous_levelVal 1)
  isScPlusRetractionOn := d.isScPlusRetractionOn_liftS hA x₀
  image := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : d.s (P.levelVal 1 x) ∈ A ∩ d.V := d.image ▸ mem_image_of_mem d.s hx
      change P.levelVal 1 (d.liftS x₀ x) ∈ A ∧ P.levelVal 1 (d.liftS x₀ x) ∈ d.V
      rw [d.levelVal_liftS x₀ hx]; exact h1
    · rintro ⟨hyA, hyV⟩
      refine ⟨y, hyV, level_ext ?_⟩
      rw [d.levelVal_liftS x₀ hyV]
      exact d.apply_eq_self ⟨hyA, hyV⟩

/-- **`ι_T ∘ T(s¹) = Ts ∘ ι_T`** on `T(V¹)`, and `T(s¹) = T(1₀¹ ∘ s) ∘ ι_T`. -/
theorem tmap_levelOne (hA : A ⊆ P.smoothSet) (x₀ : P.Level 1) {β : P.shift.TangentSpace}
    (hβ : shiftBase β ∈ d.V) :
    (d.levelOne hA x₀).tmap β =
        tangentMapOn (d.isScPlusRetractionOn.isScSmoothOn_one x₀) (tangentLower β) ∧
      tangentLower ((d.levelOne hA x₀).tmap β) = d.tmap (tangentLower β) := by
  have hι : P.shift.IsScSmoothOn P (P.levelVal 1) univ := P.remark_4_1_3_levelVal
  have hV1 : IsOpen {x : P.Level 1 | P.levelVal 1 x ∈ d.V} :=
    d.isOpen.preimage (continuous_levelVal 1)
  have hι' := hι.mono hV1 (subset_univ _)
  have hg := d.isScPlusRetractionOn.isScSmoothOn_one x₀
  have hβ1 : β ∈ P.shift.tangentPreimage {x : P.Level 1 | P.levelVal 1 x ∈ d.V} := hβ
  have h1 := tangentMapOn_comp hg hι' (fun x hx => hx) hβ1
  have h2 : tangentMapOn hι' β = tangentLower β := by
    have := tangentMapOn_congr hι' hι hV1 subset_rfl (subset_univ _) (fun _ _ => rfl) hβ1
    rw [this, tangentMapOn_univ P.remark_4_1_3_levelVal, tangentMap_levelVal_one]
  have hαV : tangentLower β ∈ P.tangentPreimage d.V := by
    change P.levelVal 1 (P.tangentProj (tangentLower β)) ∈ d.V
    rw [tangentProj_tangentLower]; exact hβ
  have e : (d.levelOne hA x₀).tmap β = tangentMapOn hg (tangentLower β) := by
    rw [← h2]; exact h1
  exact ⟨e, by rw [e]; exact d.tangentLower_tangentMapOn_one x₀ hαV⟩

end SubmanifoldData

/-- **A smooth finite-dimensional submanifold of `X` is one of `X¹`.** -/
theorem IsSmoothSubmanifold.levelOne {N : Set X} (hN : P.IsSmoothSubmanifold N) :
    P.shift.IsSmoothSubmanifold {x : P.Level 1 | P.levelVal 1 x ∈ N} :=
  isSmoothSubmanifold_iff.2 fun a ha =>
    ⟨(hN.data ha).levelOne hN.subset_smoothSet a, hN.mem_data_V ha⟩

/-- **`T_y(N ⊆ X¹)` is the preimage of `T_yN` under `T(X¹) → TX`.** -/
theorem mem_submanifoldTangent_levelOne_iff {N : Set X} (hN : P.IsSmoothSubmanifold N)
    {y : P.Level 1} (hy : P.levelVal 1 y ∈ N) {β : P.shift.TangentSpace} :
    β ∈ P.shift.submanifoldTangent {x : P.Level 1 | P.levelVal 1 x ∈ N} y ↔
      P.shift.levelVal 1 (P.shift.tangentProj β) = y ∧
        tangentLower β ∈ P.submanifoldTangent N (P.levelVal 1 y) := by
  set d := hN.data hy
  have hyV : P.levelVal 1 y ∈ d.V := hN.mem_data_V hy
  have hbase : ∀ hb : P.shift.levelVal 1 (P.shift.tangentProj β) = y,
      P.levelVal 1 (P.tangentProj (tangentLower β)) = P.levelVal 1 y := fun hb => by
    rw [tangentProj_tangentLower, hb]
  rw [mem_submanifoldTangent_iff (d.levelOne hN.subset_smoothSet y) (y := y) hyV]
  refine and_congr_right fun hb => ?_
  have hβV : shiftBase β ∈ d.V := by change P.levelVal 1 _ ∈ d.V; rw [hb]; exact hyV
  obtain ⟨-, h2⟩ := d.tmap_levelOne hN.subset_smoothSet y hβV
  rw [mem_submanifoldTangent_iff d hyV]
  constructor
  · intro h
    exact ⟨hbase hb, by rw [← h2, h]⟩
  · rintro ⟨-, h⟩
    exact tangentLower_injective (h2.trans h)

/-- **Every vector of `T_yN` is the image of a vector of `T(X¹)`**, which lies in
`T_y(N ⊆ X¹)`. -/
theorem exists_tangentLower_eq_of_mem_submanifoldTangent {N : Set X}
    (hN : P.IsSmoothSubmanifold N) {y : X} {α : P.TangentSpace}
    (hα : α ∈ P.submanifoldTangent N y) :
    ∃ β : P.shift.TangentSpace, tangentLower β = α ∧
      β ∈ P.shift.submanifoldTangent {x : P.Level 1 | P.levelVal 1 x ∈ N}
        (P.levelMk 1 y (hN.mem_levelSet_one (mem_of_mem_submanifoldTangent hα))) := by
  have hyN := mem_of_mem_submanifoldTangent hα
  set y₁ : P.Level 1 := P.levelMk 1 y (hN.mem_levelSet_one hyN) with hy₁
  have hy₁N : P.levelVal 1 y₁ ∈ N := hyN
  set d := hN.data hy₁N
  have hyV : y ∈ d.V := hN.mem_data_V hy₁N
  obtain ⟨hb, hfix⟩ := (mem_submanifoldTangent_iff d hyV).1 hα
  have hαV : α ∈ P.tangentPreimage d.V := by change _ ∈ d.V; rw [hb]; exact hyV
  set β := tangentMapOn (d.isScPlusRetractionOn.isScSmoothOn_one y₁) α with hβ
  have hlow : tangentLower β = α := (d.tangentLower_tangentMapOn_one y₁ hαV).trans hfix
  have hbβ : P.shift.levelVal 1 (P.shift.tangentProj β) = y₁ := by
    apply level_ext
    have := tangentProj_tangentLower β
    rw [hlow] at this
    rw [← this]; exact hb
  exact ⟨β, hlow, (mem_submanifoldTangent_levelOne_iff hN hy₁N).2 ⟨hbβ, by rw [hlow]; exact hα⟩⟩

/-- A vector of `T(X¹)` over `y` whose image in `TX` lies in `T_yN` lies in `T_y(N ⊆ X¹)`. -/
theorem mem_submanifoldTangent_levelOne_of_tangentLower {N : Set X}
    (hN : P.IsSmoothSubmanifold N) {y : P.Level 1} {β : P.shift.TangentSpace}
    (h : tangentLower β ∈ P.submanifoldTangent N (P.levelVal 1 y)) :
    β ∈ P.shift.submanifoldTangent {x : P.Level 1 | P.levelVal 1 x ∈ N} y := by
  have hy : P.levelVal 1 y ∈ N := mem_of_mem_submanifoldTangent h
  refine (mem_submanifoldTangent_levelOne_iff hN hy).2 ⟨level_ext ?_, h⟩
  rw [← tangentProj_tangentLower]
  exact levelVal_tangentProj_of_mem h

/-- **The chart vector of the level chart `φ¹`, read on level `0`, is the chart vector of the
image in `TX`.** -/
theorem toBase_chartVec_levelOne {φ : MChart X} (hφ : P.IsChart φ) (y₀ : P.Level 1)
    (β : P.shift.TangentSpace) (hβ : shiftBase β ∈ φ.source) :
    φ.model.E.toBase 1 (chartVec (P.shift_isChart hφ y₀) β) = chartVec hφ (tangentLower β) :=
  (congrArg Prod.snd (tangentChartMap_tangentLower β hφ hβ y₀)).symm

variable {n : ℕ}

open Classical in
/-- **An evaluation on the tangent vectors of `X¹`, read on the tangent vectors of `X`**: the
value on the vectors of `T(X¹)` over the given ones (unique, `tangentLower_injective`), and `0`
if there are none. -/
def lowerEv (f : (Fin n → P.shift.TangentSpace) → ℝ) (α : Fin n → P.TangentSpace) : ℝ :=
  if h : ∃ β : Fin n → P.shift.TangentSpace, ∀ i, tangentLower (β i) = α i then f h.choose
  else 0

theorem lowerEv_eq (f : (Fin n → P.shift.TangentSpace) → ℝ) {α : Fin n → P.TangentSpace}
    (β : Fin n → P.shift.TangentSpace) (hβ : ∀ i, tangentLower (β i) = α i) :
    lowerEv f α = f β := by
  have h : ∃ β : Fin n → P.shift.TangentSpace, ∀ i, tangentLower (β i) = α i := ⟨β, hβ⟩
  rw [lowerEv, dif_pos h]
  congr 1
  funext i
  exact tangentLower_injective ((h.choose_spec i).trans (hβ i).symm)

theorem lowerEv_add (f g : (Fin n → P.shift.TangentSpace) → ℝ) (α : Fin n → P.TangentSpace) :
    lowerEv (fun β => f β + g β) α = lowerEv f α + lowerEv g α := by
  unfold lowerEv
  split_ifs <;> simp

theorem lowerEv_smul (c : ℝ) (f : (Fin n → P.shift.TangentSpace) → ℝ)
    (α : Fin n → P.TangentSpace) : lowerEv (fun β => c * f β) α = c * lowerEv f α := by
  unfold lowerEv
  split_ifs <;> simp

/-- The tuples of vectors of one tangent space `T_yN` of a smooth finite-dimensional
submanifold. -/
def IsSubTuple (P : MPolyfold X) (α : Fin n → P.TangentSpace) : Prop :=
  ∃ (N : Set X) (y : X), P.IsSmoothSubmanifold N ∧ y ∈ N ∧ ∀ i, α i ∈ P.submanifoldTangent N y

/-- A tuple of `T_yN` is the image of a tuple of `T_y(N ⊆ X¹)`. -/
theorem IsSubTuple.exists_lift {α : Fin n → P.TangentSpace} (h : IsSubTuple P α) :
    ∃ β : Fin n → P.shift.TangentSpace, (∀ i, tangentLower (β i) = α i) ∧ IsSubTuple P.shift β := by
  obtain ⟨N, y, hN, hy, hα⟩ := h
  choose β hβ hβm using fun i => exists_tangentLower_eq_of_mem_submanifoldTangent hN (hα i)
  exact ⟨β, hβ, _, P.levelMk 1 y (hN.mem_levelSet_one hy), hN.levelOne, hy, hβm⟩

/-- Two evaluations on `T(X¹)` which agree on the tuples of the tangent spaces of submanifolds
have lowered evaluations which agree on such tuples. -/
theorem lowerEv_congr {f g : (Fin n → P.shift.TangentSpace) → ℝ}
    (h : ∀ β, IsSubTuple P.shift β → f β = g β) {α : Fin n → P.TangentSpace}
    (hα : IsSubTuple P α) : lowerEv f α = lowerEv g α := by
  obtain ⟨β, hβ, hβs⟩ := hα.exists_lift
  rw [lowerEv_eq f β hβ, lowerEv_eq g β hβ, h β hβs]

/-- **A form on `X` and its pull-back to `X¹` have the same values** on the tangent spaces of
the submanifolds. -/
theorem lowerEv_evalFamily_formLower (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin n]→ₗ[ℝ] ℝ)
    {α : Fin n → P.TangentSpace} (hα : IsSubTuple P α) :
    lowerEv (evalFamily (formLower ω)) α = evalFamily ω α := by
  obtain ⟨β, hβ, N, y, -, -, hβm⟩ := hα.exists_lift
  rw [lowerEv_eq _ β hβ]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [evalFamily_of_eq_zero hn, evalFamily_of_eq_zero hn]
  obtain ⟨x, b, -, hb⟩ := exists_fiber_lift (P := P.shift)
    (fun i => levelVal_tangentProj_of_mem (hβm i)) hn
  have e1 : evalFamily (formLower ω) β = formLower ω x b := by
    rw [← evalFamily_eq hn (formLower ω) b]; congr 1; funext i; exact (hb i).symm
  rw [e1, formLower_apply, ← evalFamily_eq hn ω]
  congr 1
  funext i
  rw [coe_lowerFiberCLM_apply, hb i, hβ i]

/-- **A frame field of a submanifold with continuous chart vectors is continuous into `TX`.** -/
theorem continuousWithinAt_frame {N : Set X} (hN : P.IsSmoothSubmanifold N) {φ : MChart X}
    (hφ : P.IsChart φ) {K : Set X} (hK : K ⊆ N ∩ φ.source) (e : X → Fin n → P.TangentSpace)
    (he : ∀ z ∈ K, ∀ i, P.levelVal 1 (P.tangentProj (e z i)) = z)
    (hc : ContinuousOn (fun z i => chartVec hφ (e z i)) K) {z₀ : X} (hz₀ : z₀ ∈ K) (i : Fin n) :
    ContinuousWithinAt (fun z => e z i) K z₀ := by
  set α₀ := e z₀ i
  have hmem : ∀ z ∈ K, e z i ∈ tangentChartSet (P := P) φ := fun z hz => by
    change P.levelVal 1 (P.tangentProj (e z i)) ∈ φ.source
    rw [he z hz i]; exact (hK hz).2
  have hpair : ContinuousWithinAt
      (fun z => ((levelLift φ 1 z, chartVec hφ (e z i)) : φ.model.E.tangent 0)) K z₀ :=
    (continuousWithinAt_levelLift hN hφ hK hz₀).prodMk
      ((continuous_apply i).continuousAt.comp_continuousWithinAt (hc z₀ hz₀))
  have heq : ∀ z ∈ K, tangentChartMap hφ (e z i) = (levelLift φ 1 z, chartVec hφ (e z i)) :=
    fun z hz => Prod.ext (by rw [tangentChartMap_fst hφ (hmem z hz), he z hz i]) rfl
  have hO : ∀ z ∈ K, ((levelLift φ 1 z, chartVec hφ (e z i)) : φ.model.E.tangent 0) ∈
      retractTangent φ.model.E φ.model.C φ.model.O := fun z hz => by
    rw [← heq z hz]; exact tangentChartMap_mem hφ (hmem z hz)
  have hinv : ContinuousOn (tangentChartInv hφ α₀)
      (retractTangent φ.model.E φ.model.C φ.model.O) := (tangentChart hφ α₀).continuousOn_invFun
  have h1 := ContinuousWithinAt.comp (g := tangentChartInv hφ α₀)
    (f := fun z => ((levelLift φ 1 z, chartVec hφ (e z i)) : φ.model.E.tangent 0))
    (hinv _ (hO z₀ hz₀)) hpair hO
  refine h1.congr (fun z hz => ?_) ?_
  · exact (((tangentChart hφ α₀).symm_apply_apply (hmem z hz)).symm.trans
      (congrArg (tangentChartInv hφ α₀) (heq z hz)))
  · exact (((tangentChart hφ α₀).symm_apply_apply (hmem z₀ hz₀)).symm.trans
      (congrArg (tangentChartInv hφ α₀) (heq z₀ hz₀)))

/-- **Continuity of a lowered evaluation along a frame field**: if `f` is continuous along the
frame fields of the submanifolds of `X¹` with continuous chart vectors, then `lowerEv f` is
continuous along those of the submanifolds of `X`. -/
theorem continuousOn_lowerEv {f : (Fin n → P.shift.TangentSpace) → ℝ}
    (hf : ∀ {N₁ : Set (P.Level 1)}, P.shift.IsSmoothSubmanifold N₁ →
      ∀ {χ : MChart (P.Level 1)} (hχ : P.shift.IsChart χ) {K₁ : Set (P.Level 1)},
      K₁ ⊆ N₁ ∩ χ.source → ∀ e₁ : P.Level 1 → Fin n → P.shift.TangentSpace,
      (∀ x ∈ K₁, ∀ i, e₁ x i ∈ P.shift.submanifoldTangent N₁ x) →
      ContinuousOn (fun x i => chartVec hχ (e₁ x i)) K₁ → ContinuousOn (fun x => f (e₁ x)) K₁)
    {N : Set X} (hN : P.IsSmoothSubmanifold N) {φ : MChart X} (hφ : P.IsChart φ) {K : Set X}
    (hK : K ⊆ N ∩ φ.source) (e : X → Fin n → P.TangentSpace)
    (he : ∀ z ∈ K, ∀ i, e z i ∈ P.submanifoldTangent N z)
    (hc : ContinuousOn (fun z i => chartVec hφ (e z i)) K) :
    ContinuousOn (fun z => lowerEv f (e z)) K := by
  classical
  intro z₀ hz₀
  have hz₀N : z₀ ∈ N := (hK hz₀).1
  set y₀ : P.Level 1 := P.levelMk 1 z₀ (hN.mem_levelSet_one hz₀N) with hy₀
  set χ := levelChart hφ y₀ with hχdef
  have hχ : P.shift.IsChart χ := P.shift_isChart hφ y₀
  -- the lifted frame field
  let e₁ : P.Level 1 → Fin n → P.shift.TangentSpace := fun x i =>
    haveI := nonempty_tangentSpace P.shift x
    Classical.epsilon fun β => tangentLower β = e (P.levelVal 1 x) i
  have hspec : ∀ x : P.Level 1, P.levelVal 1 x ∈ K → ∀ i,
      tangentLower (e₁ x i) = e (P.levelVal 1 x) i := fun x hx i => by
    obtain ⟨β, hβ, -⟩ := exists_tangentLower_eq_of_mem_submanifoldTangent hN (he _ hx i)
    have := nonempty_tangentSpace P.shift x
    exact Classical.epsilon_spec (p := fun β => tangentLower β = e (P.levelVal 1 x) i) ⟨β, hβ⟩
  have hmem₁ : ∀ x : P.Level 1, P.levelVal 1 x ∈ K → ∀ i,
      e₁ x i ∈ P.shift.submanifoldTangent {x : P.Level 1 | P.levelVal 1 x ∈ N} x :=
    fun x hx i => mem_submanifoldTangent_levelOne_of_tangentLower hN
      (by rw [hspec x hx i]; exact he _ hx i)
  -- its chart vectors are continuous
  have hc₁ : ContinuousOn (fun x i => chartVec hχ (e₁ x i)) {x | P.levelVal 1 x ∈ K} := by
    intro x₀ hx₀
    have hzN : P.levelVal 1 x₀ ∈ N := (hK hx₀).1
    set d := hN.data hzN
    have hzV : P.levelVal 1 x₀ ∈ d.V := hN.mem_data_V hzN
    have hg := d.isScPlusRetractionOn.isScSmoothOn_one x₀
    have hV₁ : IsOpen {x : P.Level 1 | P.levelVal 1 x ∈ d.V} :=
      d.isOpen.preimage (continuous_levelVal 1)
    refine (continuousWithinAt_inter (hV₁.mem_nhds hzV)).1 (continuousWithinAt_pi.2 fun i => ?_)
    have hKV : K ∩ d.V ⊆ N ∩ φ.source := inter_subset_left.trans hK
    have hbase : ∀ z ∈ K ∩ d.V, ∀ i, P.levelVal 1 (P.tangentProj (e z i)) = z :=
      fun z hz i => levelVal_tangentProj_of_mem (he z hz.1 i)
    have A1 := continuousWithinAt_frame hN hφ hKV e hbase (hc.mono inter_subset_left)
      (z₀ := P.levelVal 1 x₀) ⟨hx₀, hzV⟩ i
    have hpre : ∀ z ∈ K ∩ d.V, e z i ∈ P.tangentPreimage d.V := fun z hz => by
      change _ ∈ d.V; rw [hbase z hz i]; exact hz.2
    have A2 : ContinuousWithinAt (fun z => tangentMapOn hg (e z i)) (K ∩ d.V)
        (P.levelVal 1 x₀) :=
      ContinuousWithinAt.comp (g := tangentMapOn hg)
        (continuousOn_tangentMapOn hg _ (hpre _ ⟨hx₀, hzV⟩)) A1 hpre
    have hchart : ∀ z ∈ K ∩ d.V, tangentMapOn hg (e z i) ∈ tangentChartSet (P := P.shift) χ :=
      fun z hz => by
        change P.levelVal 1 (P.shift.levelVal 1 (P.shift.tangentProj _)) ∈ φ.source
        rw [levelVal_tangentProj_tangentMapOn hg (hpre z hz), hbase z hz i]
        change P.levelVal 1 (P.toLevelOne x₀ (d.s z)) ∈ φ.source
        rw [levelVal_toLevelOne x₀ (d.isScPlusRetractionOn.mem_levelSet z hz.2),
          d.apply_eq_self ⟨(hK hz.1).1, hz.2⟩]
        exact (hK hz.1).2
    have hsnd : ContinuousOn (fun β => chartVec hχ β) (tangentChartSet (P := P.shift) χ) :=
      continuous_snd.comp_continuousOn
        (tangentChart hχ (tangentMapOn hg (e (P.levelVal 1 x₀) i))).continuousOn_toFun
    have A3 : ContinuousWithinAt (fun z => chartVec hχ (tangentMapOn hg (e z i))) (K ∩ d.V)
        (P.levelVal 1 x₀) :=
      ContinuousWithinAt.comp (g := fun β => chartVec hχ β)
        (hsnd _ (hchart _ ⟨hx₀, hzV⟩)) A2 hchart
    have A4 : ContinuousWithinAt
        (fun x : P.Level 1 => chartVec hχ (tangentMapOn hg (e (P.levelVal 1 x) i)))
        ({x | P.levelVal 1 x ∈ K} ∩ {x | P.levelVal 1 x ∈ d.V}) x₀ :=
      ContinuousWithinAt.comp (f := P.levelVal 1) A3
        (continuous_levelVal 1).continuousWithinAt fun x hx => hx
    have hlift : ∀ x : P.Level 1, P.levelVal 1 x ∈ K → P.levelVal 1 x ∈ d.V →
        e₁ x i = tangentMapOn hg (e (P.levelVal 1 x) i) := fun x hxK hxV => by
      apply tangentLower_injective
      rw [hspec x hxK i, d.tangentLower_tangentMapOn_one x₀ (hpre _ ⟨hxK, hxV⟩)]
      exact (((mem_submanifoldTangent_iff d hxV).1 (he _ hxK i)).2).symm
    refine A4.congr (fun x hx => ?_) ?_
    · exact congrArg (chartVec hχ) (hlift x hx.1 hx.2)
    · exact congrArg (chartVec hχ) (hlift x₀ hx₀ hzV)
  have H := hf hN.levelOne hχ (K₁ := {x | P.levelVal 1 x ∈ K})
    (fun x hx => ⟨(hK hx).1, (hK hx).2⟩) e₁ hmem₁ hc₁
  -- back to `K`
  set d := hN.data hz₀N
  have hz₀V : z₀ ∈ d.V := hN.mem_data_V hz₀N
  have hg := d.isScPlusRetractionOn.isScSmoothOn_one y₀
  have hval : ∀ z ∈ K ∩ d.V, P.levelVal 1 ((P.toLevelOne y₀ ∘ d.s) z) = z := fun z hz => by
    change P.levelVal 1 (P.toLevelOne y₀ (d.s z)) = z
    rw [levelVal_toLevelOne y₀ (d.isScPlusRetractionOn.mem_levelSet z hz.2),
      d.apply_eq_self ⟨(hK hz.1).1, hz.2⟩]
  have hmaps : MapsTo (P.toLevelOne y₀ ∘ d.s) (K ∩ d.V) {x | P.levelVal 1 x ∈ K} :=
    fun z hz => by change P.levelVal 1 _ ∈ K; rw [hval z hz]; exact hz.1
  have h1 : ContinuousWithinAt ((fun x => f (e₁ x)) ∘ (P.toLevelOne y₀ ∘ d.s)) (K ∩ d.V) z₀ :=
    ContinuousWithinAt.comp (H _ (hmaps ⟨hz₀, hz₀V⟩))
      ((hg.continuousOn z₀ hz₀V).mono inter_subset_right) hmaps
  have hev : ∀ z ∈ K ∩ d.V, lowerEv f (e z) = f (e₁ ((P.toLevelOne y₀ ∘ d.s) z)) :=
    fun z hz => lowerEv_eq f _ fun i => by
      rw [hspec _ (hmaps hz) i, hval z hz]
  refine (continuousWithinAt_inter (d.isOpen.mem_nhds hz₀V)).1 (h1.congr hev (hev z₀ ⟨hz₀, hz₀V⟩))

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {n : ℕ}

/-- **The properties of the values of one form** on the tangent spaces of the smooth
finite-dimensional submanifolds (the three last fields of `FormEval`). -/
structure IsGoodEv (X : EpGroupoid Obj Mor) (f : (Fin n → X.PObj.TangentSpace) → ℝ) : Prop where
  det : ∀ {N : Set Obj}, X.PObj.IsSmoothSubmanifold N → ∀ {y : Obj}, y ∈ N →
    ∀ {φ : MChart Obj} (hφ : X.PObj.IsChart φ), y ∈ φ.source →
    ∀ (α β : Fin n → X.PObj.TangentSpace), (∀ i, α i ∈ X.PObj.submanifoldTangent N y) →
    (∀ i, β i ∈ X.PObj.submanifoldTangent N y) → ∀ M : Matrix (Fin n) (Fin n) ℝ,
    (∀ j, MPolyfold.chartVec hφ (β j) = ∑ i, M i j • MPolyfold.chartVec hφ (α i)) →
    f β = M.det * f α
  mor : ∀ {N : Set Obj}, X.PObj.IsSmoothSubmanifold N → ∀ {y : Obj}, y ∈ N →
    ∀ ψ : Mor, X.src ψ = y → ∀ α : Fin n → X.PObj.TangentSpace,
    (∀ i, α i ∈ X.PObj.submanifoldTangent N y) → f (fun i => X.tangentMor ψ (α i)) = f α
  cont : ∀ {N : Set Obj}, X.PObj.IsSmoothSubmanifold N →
    ∀ {φ : MChart Obj} (hφ : X.PObj.IsChart φ) {K : Set Obj}, K ⊆ N ∩ φ.source →
    ∀ e : Obj → Fin n → X.PObj.TangentSpace,
    (∀ z ∈ K, ∀ i, e z i ∈ X.PObj.submanifoldTangent N z) →
    ContinuousOn (fun z i => MPolyfold.chartVec hφ (e z i)) K →
    ContinuousOn (fun z => f (e z)) K

theorem FormEval.isGoodEv {X : EpGroupoid Obj Mor} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]
    (F : X.FormEval n Ω) (ω : Ω) : X.IsGoodEv (F.ev ω) :=
  ⟨fun hN _ hy _ hφ hyφ α β hα hβ M h => F.ev_det ω hN hy hφ hyφ α β hα hβ M h,
    fun hN _ hy ψ hψ α hα => F.ev_mor ω hN hy ψ hψ α hα,
    fun hN _ hφ _ hK e he hc => F.ev_continuousOn ω hN hφ hK e he hc⟩


namespace IsGoodEv

variable {X : EpGroupoid Obj Mor} {f : (Fin n → X.PObj.shift.TangentSpace) → ℝ}

theorem lower_det (h : X.liftOne.IsGoodEv f) {N : Set Obj} (hN : X.PObj.IsSmoothSubmanifold N)
    {y : Obj} (hy : y ∈ N) {φ : MChart Obj} (hφ : X.PObj.IsChart φ) (hyφ : y ∈ φ.source)
    (α β : Fin n → X.PObj.TangentSpace) (hα : ∀ i, α i ∈ X.PObj.submanifoldTangent N y)
    (hβ : ∀ i, β i ∈ X.PObj.submanifoldTangent N y) (M : Matrix (Fin n) (Fin n) ℝ)
    (hrel : ∀ j, MPolyfold.chartVec hφ (β j) = ∑ i, M i j • MPolyfold.chartVec hφ (α i)) :
    MPolyfold.lowerEv f β = M.det * MPolyfold.lowerEv f α := by
  choose a ha ham using fun i =>
    MPolyfold.exists_tangentLower_eq_of_mem_submanifoldTangent hN (hα i)
  choose b hb hbm using fun i =>
    MPolyfold.exists_tangentLower_eq_of_mem_submanifoldTangent hN (hβ i)
  set y₁ : X.PObj.Level 1 := X.PObj.levelMk 1 y (hN.mem_levelSet_one hy)
  rw [MPolyfold.lowerEv_eq f b hb, MPolyfold.lowerEv_eq f a ha]
  have hsrc : ∀ γ : X.PObj.shift.TangentSpace,
      γ ∈ X.PObj.shift.submanifoldTangent {x : X.PObj.Level 1 | X.PObj.levelVal 1 x ∈ N} y₁ →
      MPolyfold.shiftBase γ ∈ φ.source := fun γ hγ => by
    change X.PObj.levelVal 1 _ ∈ φ.source
    rw [MPolyfold.levelVal_tangentProj_of_mem hγ]; exact hyφ
  refine h.det hN.levelOne (y := y₁) hy (X.PObj.shift_isChart hφ y₁) hyφ a b ham hbm M fun j => ?_
  apply φ.model.E.toBase_injective 1
  have e1 := MPolyfold.toBase_chartVec_levelOne hφ y₁ (b j) (hsrc _ (hbm j))
  have e2 : ∀ i, φ.model.E.toBase 1 (MPolyfold.chartVec (X.PObj.shift_isChart hφ y₁) (a i)) =
      MPolyfold.chartVec hφ (α i) := fun i => by
    rw [MPolyfold.toBase_chartVec_levelOne hφ y₁ (a i) (hsrc _ (ham i)), ha i]
  refine e1.trans ?_
  rw [hb j, hrel j]
  refine Eq.symm ((map_sum (φ.model.E.toBase 1) _ _).trans (Finset.sum_congr rfl fun i _ => ?_))
  exact ((φ.model.E.toBase 1).map_smul _ _).trans (congrArg _ (e2 i))

theorem lower_mor (h : X.liftOne.IsGoodEv f) {N : Set Obj} (hN : X.PObj.IsSmoothSubmanifold N)
    {y : Obj} (hy : y ∈ N) (ψ : Mor) (hψ : X.src ψ = y) (α : Fin n → X.PObj.TangentSpace)
    (hα : ∀ i, α i ∈ X.PObj.submanifoldTangent N y) :
    MPolyfold.lowerEv f (fun i => X.tangentMor ψ (α i)) = MPolyfold.lowerEv f α := by
  choose a ha ham using fun i =>
    MPolyfold.exists_tangentLower_eq_of_mem_submanifoldTangent hN (hα i)
  set y₁ : X.PObj.Level 1 := X.PObj.levelMk 1 y (hN.mem_levelSet_one hy)
  have hψ1 : ψ ∈ X.PMor.levelSet 1 :=
    (X.mem_levelSet_src_iff ψ 1).1 (hψ ▸ hN.mem_levelSet_one hy)
  set ψ₁ : X.PMor.Level 1 := X.PMor.levelMk 1 ψ hψ1
  have hsrc : X.liftOne.src ψ₁ = y₁ := MPolyfold.level_ext hψ
  have hy₁ : y₁ ∈ X.liftOne.PObj.levelSet 1 :=
    mem_iInter.1 ((MPolyfold.mem_shift_smoothSet_iff y₁).2
      (show X.PObj.levelVal 1 y₁ ∈ X.PObj.smoothSet from hN.subset_smoothSet hy)) 1
  have hψ2 : ψ₁ ∈ X.liftOne.PMor.levelSet 1 :=
    (X.liftOne.mem_levelSet_src_iff ψ₁ 1).1 (hsrc ▸ hy₁)
  have hl : ∀ i, MPolyfold.tangentLower (X.liftOne.tangentMor ψ₁ (a i)) =
      X.tangentMor ψ (α i) := fun i => by
    rw [X.tangentLower_tangentMor_liftOne hψ2
      ((MPolyfold.levelVal_tangentProj_of_mem (ham i)).trans hsrc.symm), ha i]
    rfl
  rw [MPolyfold.lowerEv_eq f _ hl, MPolyfold.lowerEv_eq f a ha]
  exact h.mor hN.levelOne (y := y₁) hy ψ₁ hsrc a ham

/-- **From `X¹` to `X`**: an evaluation on `T(X¹)` with the properties of `IsGoodEv`, read on
`TX` (`lowerEv`), has them. -/
theorem lower (h : X.liftOne.IsGoodEv f) : X.IsGoodEv (MPolyfold.lowerEv f) :=
  ⟨fun hN _ hy _ hφ hyφ α β hα hβ M hrel => h.lower_det hN hy hφ hyφ α β hα hβ M hrel,
    fun hN _ hy ψ hψ α hα => h.lower_mor hN hy ψ hψ α hα,
    fun hN _ hφ _ hK e he hc => MPolyfold.continuousOn_lowerEv
      (fun hN₁ _ hχ _ hK₁ e₁ he₁ hc₁ => h.cont hN₁ hχ hK₁ e₁ he₁ hc₁) hN hφ hK e he hc⟩

end IsGoodEv

end EpGroupoid

namespace EP

variable (A : EP.{u}) {n : ℕ}

/-- **An evaluation on the tangent vectors of `Xⁱ`, read on the tangent vectors of `X`**
(`lowerEv`, `i` times). -/
def lowerEvIter : ∀ i : ℕ, ((Fin n → (A.lift i).X.PObj.TangentSpace) → ℝ) →
    (Fin n → A.X.PObj.TangentSpace) → ℝ
  | 0, f => f
  | i + 1, f => lowerEvIter i (MPolyfold.lowerEv (P := (A.lift i).X.PObj) f)

theorem lowerEvIter_succ (i : ℕ) (f : (Fin n → (A.lift (i + 1)).X.PObj.TangentSpace) → ℝ) :
    A.lowerEvIter (i + 1) f = A.lowerEvIter i (MPolyfold.lowerEv (P := (A.lift i).X.PObj) f) :=
  rfl

theorem lowerEvIter_add : ∀ (i : ℕ) (f g : (Fin n → (A.lift i).X.PObj.TangentSpace) → ℝ)
    (α : Fin n → A.X.PObj.TangentSpace),
    A.lowerEvIter i (fun β => f β + g β) α = A.lowerEvIter i f α + A.lowerEvIter i g α
  | 0, _, _, _ => rfl
  | i + 1, f, g, α => by
    rw [lowerEvIter_succ, lowerEvIter_succ, lowerEvIter_succ,
      ← lowerEvIter_add i _ _ α]
    congr 1
    funext β
    exact MPolyfold.lowerEv_add f g β

theorem lowerEvIter_smul : ∀ (i : ℕ) (c : ℝ) (f : (Fin n → (A.lift i).X.PObj.TangentSpace) → ℝ)
    (α : Fin n → A.X.PObj.TangentSpace),
    A.lowerEvIter i (fun β => c * f β) α = c * A.lowerEvIter i f α
  | 0, _, _, _ => rfl
  | i + 1, c, f, α => by
    rw [lowerEvIter_succ, lowerEvIter_succ, ← lowerEvIter_smul i c _ α]
    congr 1
    funext β
    exact MPolyfold.lowerEv_smul c f β

theorem isGoodEv_lowerEvIter : ∀ (i : ℕ) {f : (Fin n → (A.lift i).X.PObj.TangentSpace) → ℝ},
    (A.lift i).X.IsGoodEv f → A.X.IsGoodEv (A.lowerEvIter i f)
  | 0, _, h => h
  | i + 1, _, h => isGoodEv_lowerEvIter i (EpGroupoid.IsGoodEv.lower h)

theorem lowerEvIter_congr : ∀ (i : ℕ) {f g : (Fin n → (A.lift i).X.PObj.TangentSpace) → ℝ},
    (∀ β, MPolyfold.IsSubTuple (A.lift i).X.PObj β → f β = g β) →
    ∀ {α : Fin n → A.X.PObj.TangentSpace}, MPolyfold.IsSubTuple A.X.PObj α →
    A.lowerEvIter i f α = A.lowerEvIter i g α
  | 0, _, _, h, _, hα => h _ hα
  | i + 1, _, _, h, _, hα =>
    lowerEvIter_congr i (fun _ hβ => MPolyfold.lowerEv_congr h hβ) hα

/-- The tuples on which the classes of `Ωⁿ_{ep,∞}(X)` are evaluated: the tuples of one tangent
space `T_yN` of a smooth finite-dimensional submanifold, and their images under the tangent map
of a morphism starting at `y`. -/
def IsEvalTuple (α : Fin n → A.X.PObj.TangentSpace) : Prop :=
  MPolyfold.IsSubTuple A.X.PObj α ∨ ∃ (ψ : A.Mor) (α₀ : Fin n → A.X.PObj.TangentSpace),
    (∃ N : Set A.Obj, A.X.PObj.IsSmoothSubmanifold N ∧ A.X.src ψ ∈ N ∧
      ∀ i, α₀ i ∈ A.X.PObj.submanifoldTangent N (A.X.src ψ)) ∧
    α = fun i => A.X.tangentMor ψ (α₀ i)

/-- The values of a form of `Xⁱ` on the tangent vectors of `X`, before the cut-off. -/
def levelEv (i : ℕ) (ω : A.epForms n i) : (Fin n → A.X.PObj.TangentSpace) → ℝ :=
  A.lowerEvIter i (MPolyfold.evalFamily ω.1)

theorem isGoodEv_levelEv (i : ℕ) (ω : A.epForms n i) : A.X.IsGoodEv (A.levelEv i ω) :=
  A.isGoodEv_lowerEvIter i (((A.lift i).X.epFormEval n).isGoodEv ω)

/-- **A form on `Xⁱ` and its pull-back to `Xⁱ⁺¹` have the same values** on the evaluation
tuples. -/
theorem levelEv_epFormsStep (i : ℕ) (ω : A.epForms n i) {α : Fin n → A.X.PObj.TangentSpace}
    (hα : A.IsEvalTuple α) : A.levelEv (i + 1) (A.epFormsStep n i ω) α = A.levelEv i ω α := by
  have key : ∀ {α : Fin n → A.X.PObj.TangentSpace}, MPolyfold.IsSubTuple A.X.PObj α →
      A.levelEv (i + 1) (A.epFormsStep n i ω) α = A.levelEv i ω α := fun {α} hα => by
    change A.lowerEvIter i (MPolyfold.lowerEv (MPolyfold.evalFamily (MPolyfold.formLower ω.1)))
      α = A.lowerEvIter i (MPolyfold.evalFamily ω.1) α
    exact A.lowerEvIter_congr i
      (fun β hβ => MPolyfold.lowerEv_evalFamily_formLower ω.1 hβ) hα
  rcases hα with hα | ⟨ψ, α₀, ⟨N, hN, hy, hα₀⟩, rfl⟩
  · exact key hα
  · rw [(A.isGoodEv_levelEv (i + 1) _).mor hN hy ψ rfl α₀ hα₀,
      (A.isGoodEv_levelEv i ω).mor hN hy ψ rfl α₀ hα₀]
    exact key ⟨N, _, hN, hy, hα₀⟩

open Classical in
/-- **The values of the forms of `Xⁱ` on the tangent spaces of the smooth finite-dimensional
submanifolds of `X`** (`FormEval`): the vectors of `T_yN` are lifted to `T(Xⁱ)` (`N ⊆ X_∞` is a
submanifold of every `Xⁱ`), and the form is evaluated there; the value is `0` off the
evaluation tuples (`IsEvalTuple`). -/
def epFormsLevelEval (n i : ℕ) : A.X.FormEval n (A.epForms n i) where
  ev ω α := if A.IsEvalTuple α then A.levelEv i ω α else 0
  ev_add ω τ α := by
    split_ifs
    · change A.lowerEvIter i (MPolyfold.evalFamily (ω.1 + τ.1)) α =
        A.lowerEvIter i (MPolyfold.evalFamily ω.1) α + A.lowerEvIter i (MPolyfold.evalFamily τ.1) α
      rw [← A.lowerEvIter_add i]
      congr 1
      funext β
      exact MPolyfold.evalFamily_add ω.1 τ.1 β
    · rw [add_zero]
  ev_smul c ω α := by
    split_ifs
    · change A.lowerEvIter i (MPolyfold.evalFamily (c • ω.1)) α =
        c * A.lowerEvIter i (MPolyfold.evalFamily ω.1) α
      rw [← A.lowerEvIter_smul i]
      congr 1
      funext β
      exact MPolyfold.evalFamily_smul c ω.1 β
    · rw [mul_zero]
  ev_det ω N hN y hy φ hφ hyφ α β hα hβ M h := by
    rw [if_pos (show A.IsEvalTuple β from Or.inl ⟨N, y, hN, hy, hβ⟩),
      if_pos (show A.IsEvalTuple α from Or.inl ⟨N, y, hN, hy, hα⟩)]
    exact (A.isGoodEv_levelEv i ω).det hN hy hφ hyφ α β hα hβ M h
  ev_mor ω N hN y hy ψ hψ α hα := by
    subst hψ
    rw [if_pos (show A.IsEvalTuple _ from Or.inr ⟨ψ, α, ⟨N, hN, hy, hα⟩, rfl⟩),
      if_pos (show A.IsEvalTuple α from Or.inl ⟨N, _, hN, hy, hα⟩)]
    exact (A.isGoodEv_levelEv i ω).mor hN hy ψ rfl α hα
  ev_continuousOn ω N hN φ hφ K hK e he hc :=
    ((A.isGoodEv_levelEv i ω).cont hN hφ hK e he hc).congr fun z hz =>
      if_pos (show A.IsEvalTuple (e z) from Or.inl ⟨N, z, hN, (hK hz).1, he z hz⟩)

theorem epFormsLevelEval_ev (n i : ℕ) (ω : A.epForms n i) {α : Fin n → A.X.PObj.TangentSpace}
    (hα : A.IsEvalTuple α) : (A.epFormsLevelEval n i).ev ω α = A.levelEv i ω α := if_pos hα

/-- For `i = 0` the evaluation is that of the forms of `X` (`epFormEval`), on the evaluation
tuples. -/
theorem epFormsLevelEval_zero (n : ℕ) (ω : A.epForms n 0) {α : Fin n → A.X.PObj.TangentSpace}
    (hα : A.IsEvalTuple α) : (A.epFormsLevelEval n 0).ev ω α = (A.X.epFormEval n).ev ω α :=
  if_pos hα

theorem epFormsLevelEval_step (n i : ℕ) (ω : A.epForms n i)
    (α : Fin n → A.X.PObj.TangentSpace) :
    (A.epFormsLevelEval n (i + 1)).ev (A.epFormsStep n i ω) α =
      (A.epFormsLevelEval n i).ev ω α := by
  by_cases hα : A.IsEvalTuple α
  · rw [A.epFormsLevelEval_ev n (i + 1) _ hα, A.epFormsLevelEval_ev n i _ hα]
    exact A.levelEv_epFormsStep i ω hα
  · exact (if_neg hα).trans (if_neg hα).symm

/-- **The values of the classes of `Ωⁿ_{ep,∞}(X)` (2021 p. 372) on the tangent spaces of the
smooth finite-dimensional submanifolds of `X`** (`FormEval`): `ev [ω] α` is the value of a
representative `ω ∈ Ωⁿ_ep(Xⁱ)` on the vectors of `T(Xⁱ)` over `α₁, …, αₙ ∈ T_yN`
(`epFormsInftyEval_of`); it does not depend on the representative (`epFormsLevelEval_step`). -/
def epFormsInftyEval (n : ℕ) : A.X.FormEval n (A.epFormsInfty n) :=
  A.formEvalInfty (fun i => A.epFormsLevelEval n i) fun i ω α => A.epFormsLevelEval_step n i ω α

theorem epFormsInftyEval_of (n i : ℕ) (ω : A.epForms n i)
    (α : Fin n → A.X.PObj.TangentSpace) :
    (A.epFormsInftyEval n).ev (A.epFormsInftyOf n i ω) α = (A.epFormsLevelEval n i).ev ω α :=
  A.formEvalInfty_of _ _ i ω α

/-- The class of a form `ω ∈ Ωⁿ_ep(X)` has the values of `ω` on the tangent spaces of the
smooth finite-dimensional submanifolds. -/
theorem epFormsInftyEval_of_zero (n : ℕ) (ω : A.epForms n 0) {N : Set A.Obj}
    (hN : A.X.PObj.IsSmoothSubmanifold N) {y : A.Obj} (hy : y ∈ N)
    {α : Fin n → A.X.PObj.TangentSpace} (hα : ∀ i, α i ∈ A.X.PObj.submanifoldTangent N y) :
    (A.epFormsInftyEval n).ev (A.epFormsInftyOf n 0 ω) α = (A.X.epFormEval n).ev ω α :=
  (A.epFormsInftyEval_of n 0 ω α).trans
    (A.epFormsLevelEval_zero n ω (Or.inl ⟨N, y, hN, hy, hα⟩))

end EP

end Polyfold
