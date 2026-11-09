import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_41

/-! Round trip for V8_41 (Lemma 8.6.3 / 2017: Lemma 8.11: `#Θ_j = #Θ'_j` and
`#F⁻¹(x) = #F⁻¹(x')` for isomorphic `x`, `x'`).

`A` is the conjunction of the types of the three listed theorems, universes at `0`:
`IsProperCovering.ncard_fiber_eq_sum` (`#F⁻¹(x) = ∑_{c ∈ π(F⁻¹(x))} #Θ_c`),
`IsProperCovering.lemma_8_11` (`#Θ_c = #Θ'_c` for every `c ∈ |Y|`, `#F⁻¹(x) = #F⁻¹(x')`) and
`IsProperCovering.ncard_fiber_eq_of_isomorphic`.

The project indexes the classes by `c ∈ |Y|`; B takes arbitrary decompositions `Θ`, `Θ'` (indexed
by `Fin q`) matched as in Lemma 8.6.2.  The bridge: a class `Θ_j` is `fiberClass x (π y₀)` for each
`y₀ ∈ Θ_j` (`eq_fiberClass`), `∑_j #Θ_j = ∑_c #Θ_c` (`sum_decomp_eq`, a reindexing), and the
project's classes enumerated by `Fin q` form matched decompositions (`decomp_of_index`).

* `A ⇒ B`: matched classes `Θ_j`, `Θ'_j` are `fiberClass x c`, `fiberClass x' c` for one `c` (the
  points of `Θ_j` and `Θ'_j` are isomorphic: lift by the non-item
  `exists_isomorphic_of_isomorphic` and use the uniqueness of the matching index), so
  `#Θ_j = #Θ'_j` is `lemma_8_11`; the sums are `ncard_fiber_eq_sum`; `#F⁻¹(x) = #F⁻¹(x')` is
  `ncard_fiber_eq_of_isomorphic`.  B's three claims from the paragraph before the lemma are not in
  A's theorems and are proved outright: `#G_{y₀} = #G_{y₀'}` and `#G_x = #G_{x'}` from the
  Chapter 7 `nat_card_isotropy_eq`, and `#Θ_j = #G_x / #G_{y₀}` from the non-item Lemma 8.6.1
  (`lemma_8_9`).
* `B ⇒ A`: B applied to the project's classes, enumerated by `Fin q` (for `x'` via the non-item
  `fiberIndex_eq`), gives all three theorems (for `ncard_fiber_eq_sum`, B at `x' = x`).
-/

namespace RoundTrip.V8_41
open Polyfold Set Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.IsProperCovering.ncard_fiber_eq_sum.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.lemma_8_11.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.ncard_fiber_eq_of_isomorphic.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.IsProperCovering.ncard_fiber_eq_sum.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.lemma_8_11.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.ncard_fiber_eq_of_isomorphic.{0, 0}⟩

/-- `#G_x` computed on the group or on the set of morphisms `x → x`. -/
theorem nat_card_isotropy_eq_ncard {Obj Mor : Type} (G : GroupoidStr Obj Mor) (x : Obj) :
    Nat.card (G.Isotropy x) = (isoSetB G x).ncard := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    { toFun := fun g => ⟨g.val, g.src_val, g.tgt_val⟩
      invFun := fun g => ⟨g.1, g.2.1, g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

section
variable {ObjY MorY ObjX MorX : Type}
  [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}

/-- A class of a decomposition is the project's class of each of its points. -/
theorem eq_fiberClass (F : EpFunctor Y X) {x : ObjX} {q : ℕ} {Θ : Fin q → Set ObjY}
    (hΘ : IsIsoClassDecompB Y.toGroupoidStr (F.obj ⁻¹' {x}) Θ) (j : Fin q) {y₀ : ObjY}
    (h₀ : y₀ ∈ Θ j) : Θ j = F.fiberClass x (Y.π y₀) := by
  obtain ⟨-, hsub, -, -, hcl⟩ := hΘ
  ext y
  constructor
  · intro hy
    exact ⟨hsub j hy, (Y.π_eq_π_iff.2 ((hcl j y₀ h₀ y (hsub j hy)).1 hy)).symm⟩
  · intro hy
    exact (hcl j y₀ h₀ y hy.1).2 (Y.π_eq_π_iff.1 hy.2.symm)

/-- `∑_j #Θ_j = ∑_{c ∈ π(F⁻¹(x))} #Θ_c` for every decomposition `Θ` of `F⁻¹(x)`. -/
theorem sum_decomp_eq (F : EpFunctor Y X) (x : ObjX) (hfin : (F.fiberIndex x).Finite) {q : ℕ}
    {Θ : Fin q → Set ObjY} (hΘ : IsIsoClassDecompB Y.toGroupoidStr (F.obj ⁻¹' {x}) Θ) :
    ∑ j, (Θ j).ncard = ∑ c ∈ hfin.toFinset, (F.fiberClass x c).ncard := by
  have hΘ₀ := hΘ
  obtain ⟨hne, hsub, hU, hdisj, hcl⟩ := hΘ
  refine Finset.sum_bij (fun j _ => Y.π (hne j).some) (fun j _ => ?_) (fun i _ j _ h => ?_)
    (fun c hc => ?_) (fun j _ => congrArg Set.ncard (eq_fiberClass F hΘ₀ j (hne j).some_mem))
  · rw [Set.Finite.mem_toFinset]
    exact ⟨_, hsub j (hne j).some_mem, rfl⟩
  · by_contra hij
    have : (hne j).some ∈ Θ i :=
      (hcl i _ (hne i).some_mem _ (hsub j (hne j).some_mem)).2 (Y.π_eq_π_iff.1 h)
    exact disjoint_left.1 (hdisj hij) this (hne j).some_mem
  · rw [Set.Finite.mem_toFinset] at hc
    obtain ⟨y, hy, rfl⟩ := hc
    rw [← hU] at hy
    obtain ⟨j, hj⟩ := mem_iUnion.1 hy
    exact ⟨j, Finset.mem_univ _, Y.π_eq_π_iff.2 ((hcl j _ (hne j).some_mem y (hsub j hj)).1 hj)⟩

/-- The project's classes of `F⁻¹(x)`, enumerated by `Fin n` through their index set. -/
theorem decomp_of_index (F : EpFunctor Y X) (x : ObjX) {S : Set Y.OrbitSpace}
    (hS : F.fiberIndex x = S) {n : ℕ} (e : S ≃ Fin n) :
    IsIsoClassDecompB Y.toGroupoidStr (F.obj ⁻¹' {x}) (fun j => F.fiberClass x (e.symm j)) := by
  subst hS
  refine ⟨fun j => EpFunctor.nonempty_fiberClass_iff.2 (e.symm j).2,
    fun j => EpFunctor.fiberClass_subset x _, ?_, fun i j hij => ?_, fun j y hy y' hy' => ?_⟩
  · ext y
    simp only [mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      exact EpFunctor.fiberClass_subset x _ hj
    · intro hy
      rw [← EpFunctor.iUnion_fiberClass x] at hy
      obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.1 hy
      exact ⟨e ⟨c, hc⟩, by rw [Equiv.symm_apply_apply]; exact hyc⟩
  · have hne : (e.symm i : Y.OrbitSpace) ≠ e.symm j := fun h =>
      hij (e.symm.injective (Subtype.ext h))
    exact EpFunctor.pairwiseDisjoint_fiberClass x (mem_univ _) (mem_univ _) hne
  · rw [EpFunctor.mem_fiberClass_iff hy]
    exact ⟨fun h => h.2, fun h => ⟨hy', h⟩⟩

/-- B applied to the project's classes. -/
theorem fromB (hB : B) (F : EpFunctor Y X) (hF : F.IsProperCovering) {x x' : ObjX}
    (hx : X.Isomorphic x x') :
    (∀ c, (F.fiberClass x c).ncard = (F.fiberClass x' c).ncard) ∧
    (F.obj ⁻¹' {x}).ncard = ∑ c ∈ (hF.finite_fiberIndex x).toFinset, (F.fiberClass x c).ncard ∧
    (F.obj ⁻¹' {x}).ncard = (F.obj ⁻¹' {x'}).ncard := by
  have hidx := hF.fiberIndex_eq hx
  have := (hF.finite_fiberIndex x).to_subtype
  let e := Finite.equivFin (F.fiberIndex x)
  have hΘ := decomp_of_index F x rfl e
  have hΘ' := decomp_of_index F x' hidx.symm e
  have hm : ∀ y ∈ F.obj ⁻¹' {x}, ∀ y' ∈ F.obj ⁻¹' {x'}, IsoB Y.toGroupoidStr y y' →
      ∃! j, y ∈ F.fiberClass x (e.symm j) ∧ y' ∈ F.fiberClass x' (e.symm j) := by
    intro y hy y' hy' hyy'
    have hyy'' : Y.Isomorphic y y' := hyy'
    refine ⟨e ⟨Y.π y, y, hy, rfl⟩, ⟨?_, ?_⟩, fun k hk => ?_⟩
    · rw [Equiv.symm_apply_apply]
      exact ⟨hy, rfl⟩
    · rw [Equiv.symm_apply_apply]
      exact ⟨hy', (Y.π_eq_π_iff.2 hyy'').symm⟩
    · exact e.symm_apply_eq.1 (Subtype.ext (show Y.π y = _ from hk.1.2).symm)
  obtain ⟨h1, h2, -, h4, -⟩ := hB _ _ _ _ Y X F hF x x' hx _ _ _ hΘ hΘ' hm
  refine ⟨fun c => ?_, by rw [h2]; exact sum_decomp_eq F x _ hΘ, h4⟩
  by_cases hc : c ∈ F.fiberIndex x
  · have := h1 (e ⟨c, hc⟩)
    simp only [Equiv.symm_apply_apply] at this
    exact this
  · have h₁ : F.fiberClass x c = ∅ :=
      not_nonempty_iff_eq_empty.1 fun hne => hc (EpFunctor.nonempty_fiberClass_iff.1 hne)
    have h₂ : F.fiberClass x' c = ∅ :=
      not_nonempty_iff_eq_empty.1 fun hne => hc (hidx ▸ EpFunctor.nonempty_fiberClass_iff.1 hne)
    rw [h₁, h₂]

end

theorem A_to_B : A → B := by
  intro hA ObjY MorY ObjX MorX _ _ _ _ _ _ _ _ _ _ _ _ Y X F hF x x' hxx' q Θ Θ' hΘ hΘ' hmatch
  obtain ⟨hsum, h811, hiso⟩ := hA
  have hx : X.Isomorphic x x' := hxx'
  -- points of matched classes are isomorphic
  have hcorr : ∀ j, ∀ y₀ ∈ Θ j, ∀ y₀' ∈ Θ' j, Y.Isomorphic y₀ y₀' := by
    intro j y₀ h₀ y₀' h₀'
    obtain ⟨y', hy', hyy'⟩ := hF.exists_isomorphic_of_isomorphic hx (hΘ.2.1 j h₀)
    obtain ⟨k, ⟨hk, hk'⟩, -⟩ := hmatch y₀ (hΘ.2.1 j h₀) y' hy' hyy'
    have hkj : k = j := by
      by_contra hne
      exact disjoint_left.1 (hΘ.2.2.2.1 hne) hk h₀
    subst hkj
    exact hyy'.trans ((hΘ'.2.2.2.2 k y' hk' y₀' (hΘ'.2.1 k h₀')).1 h₀')
  refine ⟨fun j => ?_, ?_, ?_, hiso hF hx, fun j y₀ h₀ y₀' h₀' => ?_, ?_, fun j y₀ h₀ => ?_⟩
  · obtain ⟨y₀, h₀⟩ := hΘ.1 j
    obtain ⟨y₀', h₀'⟩ := hΘ'.1 j
    rw [eq_fiberClass F hΘ j h₀, eq_fiberClass F hΘ' j h₀',
      Y.π_eq_π_iff.2 (hcorr j y₀ h₀ y₀' h₀').symm]
    exact (h811 hF hx).1 _
  · rw [hsum hF x]
    exact (sum_decomp_eq F x _ hΘ).symm
  · rw [hsum hF x']
    exact sum_decomp_eq F x' _ hΘ'
  · -- before the lemma (outright)
    rw [← nat_card_isotropy_eq_ncard, ← nat_card_isotropy_eq_ncard]
    exact Y.nat_card_isotropy_eq (hcorr j y₀ h₀ y₀' h₀')
  · rw [← nat_card_isotropy_eq_ncard, ← nat_card_isotropy_eq_ncard]
    exact X.nat_card_isotropy_eq hx
  · -- `#Θ_j = #G_x / #G_{y₀}` from the non-item Lemma 8.6.1
    rw [← nat_card_isotropy_eq_ncard, ← nat_card_isotropy_eq_ncard,
      ((hF.lemma_8_9 x (Y.π y₀)).2 y₀ ⟨hΘ.2.1 j h₀, rfl⟩).2, eq_fiberClass F hΘ j h₀]
    exact (Nat.mul_div_cancel_left _ Nat.card_pos).symm

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x
    exact (fromB hB F hF (X.isomorphic_refl x)).2.1
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x x' h
    exact ⟨(fromB hB F hF h).1, (fromB hB F hF h).2.2⟩
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x x' h
    exact (fromB hB F hF h).2.2

#rt_check RoundTrip.V8_41.A_to_B [Polyfold.EpFunctor.IsProperCovering.ncard_fiber_eq_sum,
  Polyfold.EpFunctor.IsProperCovering.lemma_8_11,
  Polyfold.EpFunctor.IsProperCovering.ncard_fiber_eq_of_isomorphic]
#rt_check RoundTrip.V8_41.B_to_A [Polyfold.EpFunctor.IsProperCovering.ncard_fiber_eq_sum,
  Polyfold.EpFunctor.IsProperCovering.lemma_8_11,
  Polyfold.EpFunctor.IsProperCovering.ncard_fiber_eq_of_isomorphic]
#rt_overlap RoundTrip.V8_41.B_to_A [Polyfold.EpFunctor.IsProperCovering.ncard_fiber_eq_sum,
  Polyfold.EpFunctor.IsProperCovering.lemma_8_11,
  Polyfold.EpFunctor.IsProperCovering.ncard_fiber_eq_of_isomorphic]

end RoundTrip.V8_41
