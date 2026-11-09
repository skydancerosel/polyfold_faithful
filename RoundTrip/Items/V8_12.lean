import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_12

/-! Round trip for V8_12 (Remark 8.1.10 (2017: 8.1): the morphisms of `T𝐗` as pairs `(Tφ, a)`).

`A` is the conjunction of the types of the three listed theorems, universe instantiated at `0`
(`B` lives in `Type`): `tangentMor_tSrc` (`Tφ(Ts h) = Tt h`), `tangentMor_comp`
(`T(ψ ∘ φ) = Tψ ∘ Tφ` on `T_{s φ}X`) and `remark_8_1_10` (these two, `G = remarkG` injective with
range `{(φ, a) | φ ∈ 𝐗₁, p(a) = s φ}` — `Tφ` *labelled by `φ`* —, composability via `Tφ`, and
`G` compatible with the composition).  `tangentMor` (Chapter 7's `Tφ`) and `remarkG` are
definitions (vocabulary).

* **`B` is false** (`not_B`), as its author predicted: `B` (iii) asserts the bijection
  `G : T𝐗 → {(Tφ, a)}` literally, with `Tφ` the bare map.  On Chapter 7's `ℤ/3 × ℝ ⇉ ℝ` (trivial
  action, `s = t`), `B`'s own clause (vi) forces `Tφ = id` for every `φ`, so the vectors over
  `(1, x)` and `(g, x)`, `g ≠ 1`, with the same `Ts` have the same image under `G`.  Hence
  `A → B` is false (`not_A_to_B`) and `B → A` holds only ex falso.
* **`BCore`** is `B` under the project's (labelled) reading of the bijection, i.e. `B` with
  (iii)'s bijection onto `{(Tφ, a)}` replaced by the bijection `k ↦ (p k, Ts k)` onto
  `{(φ, a) | φ ∈ 𝐗₁, p(a) = s φ}`, and with the clauses `A` does not address removed:
  (0) `Tφ` is the tangent of `t ∘ (s|𝐔(φ))⁻¹` on every sheet, the chart-linearity half of (i),
  and (iv) the transported M-polyfold structure.  Everything else of `B` is kept: the fibrewise
  bijectivity of `Tφ` in (i), (ii), (vi) and the five compatibility clauses of (iii) with `B`'s own
  pair category.  `A_to_BCore` and `BCore_to_A` are both proved. -/

namespace RoundTrip.V8_12
open Polyfold

/-- The project's statement (universe at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.tangentMor_tSrc.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tangentMor_comp.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.remark_8_1_10.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.tangentMor_tSrc.{0}, @Polyfold.EpGroupoid.tangentMor_comp.{0},
    @Polyfold.EpGroupoid.remark_8_1_10.{0}⟩

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-! ### Evaluating `B`'s `TφB` and `pairCompB` -/

theorem TφB_pos (X : EpGroupoid Obj Mor) {φ : Mor} {c : X.PObj.TangentSpace}
    (hc : baseB X.PObj c = X.src φ) : TφB X φ c = X.tangentMor φ c := if_pos hc

theorem TφB_neg (X : EpGroupoid Obj Mor) {φ : Mor} {c : X.PObj.TangentSpace}
    (hc : ¬ baseB X.PObj c = X.src φ) : TφB X φ c = c := if_neg hc

theorem pairCompB_fst_pos (X : EpGroupoid Obj Mor)
    {P₂ P₁ : (X.PObj.TangentSpace → X.PObj.TangentSpace) × X.PObj.TangentSpace}
    {c : X.PObj.TangentSpace} (hc : baseB X.PObj c = baseB X.PObj P₁.2) :
    (pairCompB X P₂ P₁).1 c = P₂.1 (P₁.1 c) := if_pos hc

theorem pairCompB_fst_neg (X : EpGroupoid Obj Mor)
    {P₂ P₁ : (X.PObj.TangentSpace → X.PObj.TangentSpace) × X.PObj.TangentSpace}
    {c : X.PObj.TangentSpace} (hc : ¬ baseB X.PObj c = baseB X.PObj P₁.2) :
    (pairCompB X P₂ P₁).1 c = c := if_neg hc

/-! ### `B` is false -/

/-- If `s = t`, `B`'s clause (vi) forces `Tφ = id` (as `B`'s `TφB`, on all of `TX`). -/
theorem TφB_eq_id_of_tgt_eq_src (X : EpGroupoid Obj Mor) (hts : X.tgt = X.src)
    (hvi : ∀ h, X.tangentMor (X.tBase h) (X.tSrc h) = X.tTgt h) {φ : Mor}
    (hφ : φ ∈ X.PMor.levelSet 1) : TφB X φ = id := by
  funext c
  by_cases hc : baseB X.PObj c = X.src φ
  · rw [TφB_pos X hc]
    obtain ⟨w, hw1, hw2⟩ := X.exists_tSrc_eq' hφ hc
    have h1 := hvi w
    have hts' : X.tTgt w = X.tSrc w := by
      unfold EpGroupoid.tTgt EpGroupoid.tSrc
      exact congrFun (MPolyfold.tangentMap_congr_fun _ _ hts) w
    rw [hw1, hw2, hts', hw2] at h1
    exact h1
  · rw [TφB_neg X hc]
    rfl

/-- `B`'s clauses (vi) and (iii)-bijection are contradictory on an ep-groupoid with `s = t` and
two distinct morphisms with the same source. -/
theorem false_of_clauses (X : EpGroupoid Obj Mor) (hs : X.PMor.IsScSmoothMap X.PObj X.src)
    (ht : X.PMor.IsScSmoothMap X.PObj X.tgt) (hts : X.tgt = X.src)
    (hvi : ∀ h : X.PMor.TangentSpace,
      X.tangentMor (baseB X.PMor h) (MPolyfold.tangentMap hs h) = MPolyfold.tangentMap ht h)
    (hbij : Set.BijOn (GB X hs) Set.univ (SB X)) {φ₁ φ₂ : Mor} (hne : φ₁ ≠ φ₂)
    (hsrc : X.src φ₁ = X.src φ₂) (a : X.PObj.TangentSpace) (ha : baseB X.PObj a = X.src φ₁) :
    False := by
  have hvi' : ∀ h, X.tangentMor (X.tBase h) (X.tSrc h) = X.tTgt h := hvi
  have hx1 : X.src φ₁ ∈ X.PObj.levelSet 1 := ha ▸ MPolyfold.levelVal_mem _
  have hφ₁ : φ₁ ∈ X.PMor.levelSet 1 := (X.mem_levelSet_src_iff φ₁ 1).1 hx1
  have hφ₂ : φ₂ ∈ X.PMor.levelSet 1 := (X.mem_levelSet_src_iff φ₂ 1).1 (hsrc ▸ hx1)
  obtain ⟨v₁, hv₁b, hv₁s⟩ := X.exists_tSrc_eq' hφ₁ ha
  obtain ⟨v₂, hv₂b, hv₂s⟩ := X.exists_tSrc_eq' hφ₂ (ha.trans hsrc)
  have hG : GB X hs v₁ = GB X hs v₂ := by
    show (TφB X (X.tBase v₁), X.tSrc v₁) = (TφB X (X.tBase v₂), X.tSrc v₂)
    rw [hv₁b, hv₂b, hv₁s, hv₂s, TφB_eq_id_of_tgt_eq_src X hts hvi' hφ₁,
      TφB_eq_id_of_tgt_eq_src X hts hvi' hφ₂]
  have hv : v₁ = v₂ := hbij.injOn (Set.mem_univ _) (Set.mem_univ _) hG
  exact hne (hv₁b.symm.trans ((congrArg X.tBase hv).trans hv₂b))

end

open Polyfold.EpGroupoid.Examples in
/-- **`B` is false**: on `ℤ/3 × ℝ ⇉ ℝ` (trivial action), the vectors over `(1, x)` and
`(g, x)`, `g ≠ 1`, with the same `Ts` have the same `G`-image `(id, a)`. -/
theorem not_B : ¬ B := by
  intro hB
  obtain ⟨hs, ht, -, -, -, -, -, hvi, -, -, -, -, -, hbij, -⟩ := hB _ _ trivialZ3EpGroupoid
  obtain ⟨a⟩ := MPolyfold.nonempty_tangentSpace trivialZ3EpGroupoid.PObj (0 : Fin 1 → ℝ)
  have hne : ((1 : Multiplicative (ZMod 3)), baseB trivialZ3EpGroupoid.PObj a) ≠
      (Multiplicative.ofAdd (1 : ZMod 3), baseB trivialZ3EpGroupoid.PObj a) := by
    intro h
    have h0 : Multiplicative.toAdd (1 : Multiplicative (ZMod 3)) ≠
        Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 3)) := by decide
    exact h0 (congrArg (fun p => Multiplicative.toAdd p.1) h)
  exact false_of_clauses trivialZ3EpGroupoid hs ht (funext fun p => z3_smul_eq p.1 p.2) hvi hbij
    hne rfl a rfl

theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B → A` only ex falso. -/
theorem B_to_A : B → A := fun h => absurd h not_B

/-! ### `BCore`: `B` with the labelled bijection, without (0), chart linearity and (iv) -/

/-- The labelled pairs `{(φ, a) | φ ∈ 𝐗₁, a ∈ T_{s φ}X}`. -/
def SL {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor) :
    Set (Mor × X.PObj.TangentSpace) :=
  {P | P.1 ∈ X.PMor.levelSet 1 ∧ baseB X.PObj P.2 = X.src P.1}

/-- `B` without (0), the chart-linearity half of (i) and (iv), and with (iii)'s bijection read
with `Tφ` labelled by `φ`: `k ↦ (p k, Ts k)` is a bijection `T𝐗 → SL X`. -/
def BCore : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ∃ (hs : X.PMor.IsScSmoothMap X.PObj X.src) (ht : X.PMor.IsScSmoothMap X.PObj X.tgt)
      (hι : X.PMor.IsScSmoothMap X.PMor X.inv),
      -- (i) `Tφ : T_xX → T_yX` is a bijection
      (∀ φ ∈ X.PMor.levelSet 1,
        Set.BijOn (X.tangentMor φ) (fibreB X.PObj (X.src φ)) (fibreB X.PObj (X.tgt φ))) ∧
      -- (ii)
      (∀ φ ∈ X.PMor.levelSet 1, ∀ ψ ∈ X.PMor.levelSet 1, X.src ψ = X.tgt φ →
        ∀ c ∈ fibreB X.PObj (X.src φ),
          X.tangentMor (X.comp ψ φ) c = X.tangentMor ψ (X.tangentMor φ c)) ∧
      -- (vi)
      (∀ φ ∈ X.PMor.levelSet 1,
        Set.BijOn (MPolyfold.tangentMap hs) (fibreB X.PMor φ) (fibreB X.PObj (X.src φ))) ∧
      (∀ h : X.PMor.TangentSpace,
        X.tangentMor (baseB X.PMor h) (MPolyfold.tangentMap hs h) = MPolyfold.tangentMap ht h) ∧
      -- (iii) compatibility, as in `B`
      (∀ k : X.PMor.TangentSpace, (GB X hs k).2 = MPolyfold.tangentMap hs k) ∧
      (∀ k : X.PMor.TangentSpace, (GB X hs k).1 (GB X hs k).2 = MPolyfold.tangentMap ht k) ∧
      (∀ l k : X.PMor.TangentSpace, MPolyfold.tangentMap hs l = MPolyfold.tangentMap ht k →
        GB X hs (tCompB X hs l k) = pairCompB X (GB X hs l) (GB X hs k)) ∧
      (∀ (q : X.PObj.TangentSpace) (v : X.PMor.TangentSpace), IsTUnitB X hs q v →
        GB X hs v = (id, q)) ∧
      (∀ k : X.PMor.TangentSpace,
        (GB X hs (MPolyfold.tangentMap hι k)).2 = (GB X hs k).1 (GB X hs k).2 ∧
        (∀ c ∈ fibreB X.PObj (X.src (baseB X.PMor k)),
          (GB X hs (MPolyfold.tangentMap hι k)).1 ((GB X hs k).1 c) = c) ∧
        (∀ d ∈ fibreB X.PObj (X.tgt (baseB X.PMor k)),
          (GB X hs k).1 ((GB X hs (MPolyfold.tangentMap hι k)).1 d) = d)) ∧
      -- (iii) the bijection, labelled reading
      Set.BijOn (fun k => (baseB X.PMor k, MPolyfold.tangentMap hs k)) Set.univ (SL X)

section Glue
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
  (h1 : ∀ v, X.tangentMor (X.tBase v) (X.tSrc v) = X.tTgt v)
  (h2 : ∀ φ ψ, φ ∈ X.PMor.levelSet 1 → X.src ψ = X.tgt φ → ∀ a,
    X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src φ →
      X.tangentMor (X.comp ψ φ) a = X.tangentMor ψ (X.tangentMor φ a))
include h1

theorem base_tangentMor {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) {c : X.PObj.TangentSpace}
    (hc : baseB X.PObj c = X.src φ) : baseB X.PObj (X.tangentMor φ c) = X.tgt φ := by
  obtain ⟨w, hw1, hw2⟩ := X.exists_tSrc_eq' hφ hc
  rw [← hw1, ← hw2, h1]
  exact X.levelVal_tangentProj_tTgt w

theorem tangentMor_unit {x : Obj} {c : X.PObj.TangentSpace} (hc : baseB X.PObj c = x) :
    X.tangentMor (X.unit x) c = c := by
  have h := h1 (X.tUnit c)
  rw [X.tBase_tUnit, X.tSrc_tUnit, X.tTgt_tUnit] at h
  rw [← hc]
  exact h

omit h1 in
theorem inv_mem_levelSet {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) : X.inv φ ∈ X.PMor.levelSet 1 :=
  (X.mem_levelSet_src_iff (X.inv φ) 1).1 (by rw [X.src_inv]; exact (X.mem_levelSet_tgt_iff φ 1).2 hφ)

include h1 h2

theorem tangentMor_inv_left {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) {c : X.PObj.TangentSpace}
    (hc : baseB X.PObj c = X.src φ) : X.tangentMor (X.inv φ) (X.tangentMor φ c) = c := by
  rw [← h2 φ (X.inv φ) hφ (X.src_inv φ) c hc, X.inv_comp]
  exact tangentMor_unit X h1 hc

theorem tangentMor_inv_right {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) {d : X.PObj.TangentSpace}
    (hd : baseB X.PObj d = X.tgt φ) : X.tangentMor φ (X.tangentMor (X.inv φ) d) = d := by
  have hi := inv_mem_levelSet X hφ
  rw [← h2 (X.inv φ) φ hi (X.tgt_inv φ).symm d (hd.trans (X.src_inv φ).symm), X.comp_inv]
  exact tangentMor_unit X h1 hd

end Glue

theorem A_to_BCore : A → BCore := by
  intro hA Obj Mor _ _ _ _ _ _ X
  obtain ⟨h1, h2, -⟩ := hA
  have h1 : ∀ v, X.tangentMor (X.tBase v) (X.tSrc v) = X.tTgt v := h1 X
  have h2 := @h2 Obj Mor _ _ _ _ _ _ X
  have h2' : ∀ φ ψ, φ ∈ X.PMor.levelSet 1 → X.src ψ = X.tgt φ → ∀ a,
      X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src φ →
        X.tangentMor (X.comp ψ φ) a = X.tangentMor ψ (X.tangentMor φ a) :=
    fun φ ψ hφ hψφ a ha => h2 hφ hψφ ha
  refine ⟨X.isScSmoothMap_src, X.isScSmoothMap_tgt, X.isScSmoothMap_inv, fun φ hφ => ?_,
    fun φ hφ ψ _ hψφ c hc => h2' φ ψ hφ hψφ c hc, fun φ hφ => ?_, h1, fun k => rfl,
    fun k => ?_, fun l k hlk => ?_, fun q v hv => ?_, fun k => ?_, ?_⟩
  · -- (i)
    refine ⟨fun c hc => base_tangentMor X h1 hφ hc, fun c hc c' hc' hcc => ?_, fun d hd => ?_⟩
    · rw [← tangentMor_inv_left X h1 h2' hφ hc, hcc, tangentMor_inv_left X h1 h2' hφ hc']
    · have hi := inv_mem_levelSet X hφ
      have hd' : baseB X.PObj d = X.src (X.inv φ) := hd.trans (X.src_inv φ).symm
      refine ⟨X.tangentMor (X.inv φ) d, ?_, tangentMor_inv_right X h1 h2' hφ hd⟩
      exact (base_tangentMor X h1 hi hd').trans (X.tgt_inv φ)
  · -- (vi): `Ts` is a bijection `T_φ𝐗 → T_{s φ}X`
    refine ⟨fun w hw => ?_, fun w hw w' hw' hww => X.tangent_ext (hw.trans hw'.symm) hww,
      fun c hc => ?_⟩
    · change baseB X.PObj (X.tSrc w) = X.src φ
      rw [← hw]
      exact X.levelVal_tangentProj_tSrc w
    · obtain ⟨w, hw1, hw2⟩ := X.exists_tSrc_eq' hφ hc
      exact ⟨w, hw1, hw2⟩
  · -- (iii) `G(k)` is a morphism `Ts k → Tt k`
    show TφB X (X.tBase k) (X.tSrc k) = X.tTgt k
    rw [TφB_pos X (X.levelVal_tangentProj_tSrc k)]
    exact h1 k
  · -- (iii) composition
    have hlk' : X.tSrc l = X.tTgt k := hlk
    have hc := X.src_tBase_eq hlk'
    have hk1 := X.tBase_mem_levelSet k
    have hsk : baseB X.PObj (X.tSrc k) = X.src (X.tBase k) := X.levelVal_tangentProj_tSrc k
    refine Prod.ext (funext fun c => ?_) ?_
    · change TφB X (X.tBase (X.tComp l k)) c =
        (pairCompB X (GB X X.isScSmoothMap_src l) (GB X X.isScSmoothMap_src k)).1 c
      rw [X.tBase_tComp hlk']
      by_cases h : baseB X.PObj c = X.src (X.tBase k)
      · rw [TφB_pos X (h.trans (X.src_comp _ _ hc).symm),
          pairCompB_fst_pos X (P₂ := GB X X.isScSmoothMap_src l)
            (P₁ := GB X X.isScSmoothMap_src k) (h.trans hsk.symm)]
        change _ = TφB X (X.tBase l) (TφB X (X.tBase k) c)
        rw [TφB_pos X h, TφB_pos X ((base_tangentMor X h1 hk1 h).trans hc.symm)]
        exact h2' _ _ hk1 hc c h
      · rw [TφB_neg X (fun h' => h (h'.trans (X.src_comp _ _ hc))),
          pairCompB_fst_neg X (P₂ := GB X X.isScSmoothMap_src l)
            (P₁ := GB X X.isScSmoothMap_src k) (fun h' => h (h'.trans hsk))]
    · change X.tSrc (X.tComp l k) = X.tSrc k
      exact X.tSrc_tComp hlk'
  · -- (iii) units
    have hv' : X.tBase v = X.unit (baseB X.PObj q) := hv.1
    have hq : X.tSrc v = q := hv.2
    refine Prod.ext (funext fun c => ?_) hq
    change TφB X (X.tBase v) c = c
    rw [hv']
    by_cases h : baseB X.PObj c = X.src (X.unit (baseB X.PObj q))
    · rw [TφB_pos X h]
      exact tangentMor_unit X h1 (h.trans (X.src_unit _))
    · rw [TφB_neg X h]
  · -- (iii) inverses
    have hk1 := X.tBase_mem_levelSet k
    have hbi : baseB X.PMor (MPolyfold.tangentMap X.isScSmoothMap_inv k) = X.inv (X.tBase k) :=
      X.tBase_tInv k
    refine ⟨?_, fun c hc => ?_, fun d hd => ?_⟩
    · show X.tSrc (X.tInv k) = TφB X (X.tBase k) (X.tSrc k)
      rw [X.tSrc_tInv, TφB_pos X (X.levelVal_tangentProj_tSrc k), h1]
    · have hc' : baseB X.PObj c = X.src (X.tBase k) := hc
      show TφB X (baseB X.PMor (MPolyfold.tangentMap X.isScSmoothMap_inv k))
        (TφB X (X.tBase k) c) = c
      rw [hbi, TφB_pos X hc', TφB_pos X ((base_tangentMor X h1 hk1 hc').trans
        (X.src_inv _).symm)]
      exact tangentMor_inv_left X h1 h2' hk1 hc'
    · have hd' : baseB X.PObj d = X.tgt (X.tBase k) := hd
      have hi := inv_mem_levelSet X hk1
      have hd'' : baseB X.PObj d = X.src (X.inv (X.tBase k)) := hd'.trans (X.src_inv _).symm
      show TφB X (X.tBase k)
        (TφB X (baseB X.PMor (MPolyfold.tangentMap X.isScSmoothMap_inv k)) d) = d
      rw [hbi, TφB_pos X hd'', TφB_pos X ((base_tangentMor X h1 hi hd'').trans
        (X.tgt_inv _))]
      exact tangentMor_inv_right X h1 h2' hk1 hd'
  · -- (iii) the labelled bijection
    refine ⟨fun k _ => ⟨X.tBase_mem_levelSet k, X.levelVal_tangentProj_tSrc k⟩,
      fun k _ k' _ hkk => X.tangent_ext (congrArg Prod.fst hkk) (congrArg Prod.snd hkk),
      fun p hp => ?_⟩
    obtain ⟨w, hw1, hw2⟩ := X.exists_tSrc_eq' hp.1 hp.2
    exact ⟨w, Set.mem_univ _, Prod.ext hw1 hw2⟩

theorem BCore_to_A : BCore → A := by
  intro hB
  have key : ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
      (∀ v, X.tangentMor (X.tBase v) (X.tSrc v) = X.tTgt v) ∧
      (∀ φ ψ, φ ∈ X.PMor.levelSet 1 → X.src ψ = X.tgt φ → ∀ a,
        X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src φ →
          X.tangentMor (X.comp ψ φ) a = X.tangentMor ψ (X.tangentMor φ a)) ∧
      Set.BijOn X.remarkG Set.univ (SL X) := by
    intro Obj Mor _ _ _ _ _ _ X
    obtain ⟨hs, ht, hι, -, hii, -, hvi, -, -, -, -, -, hlab⟩ := hB Obj Mor X
    refine ⟨hvi, fun φ ψ hφ hψφ a ha => ?_, hlab⟩
    have hψ : ψ ∈ X.PMor.levelSet 1 :=
      (X.mem_levelSet_src_iff ψ 1).1 (by rw [hψφ]; exact (X.mem_levelSet_tgt_iff φ 1).2 hφ)
    exact hii φ hφ ψ hψ hψφ a ha
  refine ⟨fun X v => (key _ _ X).1 v, fun X φ ψ hφ hψφ a ha => (key _ _ X).2.1 φ ψ hφ hψφ a ha,
    fun X => ?_⟩
  obtain ⟨h1, h2, hlab⟩ := key _ _ X
  refine ⟨h1, h2, fun v w hvw => hlab.injOn (Set.mem_univ v) (Set.mem_univ w) hvw, ?_,
    fun k h => by rw [h1], fun k h hkh => ⟨?_, fun a ha =>
      h2 _ _ (X.tBase_mem_levelSet h) (X.src_tBase_eq hkh) a ha⟩⟩
  · rw [← Set.image_univ, hlab.image_eq]
    rfl
  · show (X.tBase (X.tComp k h), X.tSrc (X.tComp k h)) = _
    rw [X.tBase_tComp hkh, X.tSrc_tComp hkh]

#rt_check RoundTrip.V8_12.not_B [Polyfold.EpGroupoid.tangentMor_tSrc,
  Polyfold.EpGroupoid.tangentMor_comp, Polyfold.EpGroupoid.remark_8_1_10]
#rt_check RoundTrip.V8_12.B_to_A [Polyfold.EpGroupoid.tangentMor_tSrc,
  Polyfold.EpGroupoid.tangentMor_comp, Polyfold.EpGroupoid.remark_8_1_10]
#rt_check RoundTrip.V8_12.A_to_BCore [Polyfold.EpGroupoid.tangentMor_tSrc,
  Polyfold.EpGroupoid.tangentMor_comp, Polyfold.EpGroupoid.remark_8_1_10]
#rt_check RoundTrip.V8_12.BCore_to_A [Polyfold.EpGroupoid.tangentMor_tSrc,
  Polyfold.EpGroupoid.tangentMor_comp, Polyfold.EpGroupoid.remark_8_1_10]
#rt_overlap RoundTrip.V8_12.B_to_A [Polyfold.EpGroupoid.tangentMor_tSrc,
  Polyfold.EpGroupoid.tangentMor_comp, Polyfold.EpGroupoid.remark_8_1_10]
#rt_overlap RoundTrip.V8_12.BCore_to_A [Polyfold.EpGroupoid.tangentMor_tSrc,
  Polyfold.EpGroupoid.tangentMor_comp, Polyfold.EpGroupoid.remark_8_1_10]

end RoundTrip.V8_12
