import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_40

/-! Round trip for V8_40 (Lemma 8.6.2 / 2017: Lemma 8.10: the isomorphism classes over isomorphic
objects).

`A` is the conjunction of the types of the four listed theorems, universes at `0`:
`IsProperCovering.exists_isomorphic_of_isomorphic` (every `y ∈ F⁻¹(x)` is isomorphic to some
`y' ∈ F⁻¹(x')`), `IsProperCovering.fiberIndex_eq` (`π(F⁻¹(x)) = π(F⁻¹(x'))` in `|Y|`),
`IsProperCovering.lemma_8_10` (same index set, unique index for isomorphic `y, y'`) and
`IsProperCovering.lemma_8_10_equiv` (a bijection between the sets of classes, corresponding
classes isomorphic).

* `A ⇒ B`: B's paragraph-before-the-lemma claim is transitivity of `≅`.  For the lemma, given an
  arbitrary enumeration `Θ : Fin q → Set` of the classes of `F⁻¹(x)`, we put
  `Θ'_j = {y' ∈ F⁻¹(x') | ∃ y ∈ Θ_j, y ≅ y'}`; that these are nonempty and cover `F⁻¹(x')` is
  A's `exists_isomorphic_of_isomorphic` (for `x ≅ x'` and `x' ≅ x`); the rest is bookkeeping with
  the classes.
* `B ⇒ A` holds only by proving `A` outright (from the non-item `existsUnique_lift`, by the
  project's arguments); **B is not used**.  The reason is a genuine gap: B's matching condition
  only constrains *isomorphic* pairs `y ∈ F⁻¹(x)`, `y' ∈ F⁻¹(x')` (and gives equally many classes,
  `q`); it never says that a point of `F⁻¹(x)` has an isomorphic partner in `F⁻¹(x')`.  If no
  such pairs existed, every enumeration `Θ'` of the `q` classes of `F⁻¹(x')` would satisfy B's
  conclusion, so B's conclusion does not imply A's `exists_isomorphic_of_isomorphic`,
  `fiberIndex_eq` or `lemma_8_10_equiv` (all of which assert that totality); `A` is stronger.
-/

namespace RoundTrip.V8_40
open Polyfold Set Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.IsProperCovering.exists_isomorphic_of_isomorphic.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.fiberIndex_eq.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.lemma_8_10.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.lemma_8_10_equiv.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.IsProperCovering.exists_isomorphic_of_isomorphic.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.fiberIndex_eq.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.lemma_8_10.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.lemma_8_10_equiv.{0, 0}⟩

theorem A_to_B : A → B := by
  intro hA ObjY MorY ObjX MorX _ _ _ _ _ _ _ _ _ _ _ _ Y X F hF x x' hxx'
  obtain ⟨hex, -⟩ := hA
  have hxx'' : X.Isomorphic x x' := hxx'
  refine ⟨?_, ?_⟩
  · -- before the lemma: transitivity
    rintro y - y₁ - y₂ - ⟨z₁, -, h₁, h₁'⟩ ⟨z₂, -, h₂, h₂'⟩
    have h₁ : Y.Isomorphic y z₁ := h₁
    have h₁' : Y.Isomorphic z₁ y₁ := h₁'
    have h₂ : Y.Isomorphic y z₂ := h₂
    have h₂' : Y.Isomorphic z₂ y₂ := h₂'
    exact (h₁'.symm.trans h₁.symm).trans (h₂.trans h₂')
  · intro q Θ hΘ
    obtain ⟨hne, hsub, hU, hdisj, hcl⟩ := hΘ
    have hcov : ∀ y ∈ F.obj ⁻¹' {x}, ∃ j, y ∈ Θ j := fun y hy => by
      rw [← hU] at hy
      exact mem_iUnion.1 hy
    have hsame : ∀ j, ∀ y₁ ∈ Θ j, ∀ y₂ ∈ Θ j, Y.Isomorphic y₁ y₂ :=
      fun j y₁ h₁ y₂ h₂ => (hcl j y₁ h₁ y₂ (hsub j h₂)).1 h₂
    have hmem : ∀ j, ∀ y₁ ∈ Θ j, ∀ y₂ ∈ F.obj ⁻¹' {x}, Y.Isomorphic y₁ y₂ → y₂ ∈ Θ j :=
      fun j y₁ h₁ y₂ h₂ h => (hcl j y₁ h₁ y₂ h₂).2 h
    have huniq : ∀ i j, ∀ y, y ∈ Θ i → y ∈ Θ j → i = j := fun i j y hi hj => by
      by_contra hij
      exact disjoint_left.1 (hdisj hij) hi hj
    let Θ' : Fin q → Set ObjY := fun j => {y' | F.obj y' = x' ∧ ∃ y ∈ Θ j, Y.Isomorphic y y'}
    refine ⟨Θ', ⟨fun j => ?_, fun j y' hy' => hy'.1, ?_, fun i j hij => ?_,
      fun j y₁' h₁' y₂' h₂' => ?_⟩, ?_⟩
    · obtain ⟨y, hy⟩ := hne j
      obtain ⟨y', hy', hyy'⟩ := hex hF hxx'' (hsub j hy)
      exact ⟨y', hy', y, hy, hyy'⟩
    · ext y'
      simp only [mem_iUnion]
      constructor
      · rintro ⟨j, hj⟩
        exact hj.1
      · intro hy'
        obtain ⟨y, hy, hyy'⟩ := hex hF hxx''.symm hy'
        obtain ⟨j, hj⟩ := hcov y hy
        exact ⟨j, hy', y, hj, hyy'.symm⟩
    · refine disjoint_left.2 fun y' hi hj => hij ?_
      obtain ⟨yi, hyi, hi'⟩ := hi.2
      obtain ⟨yj, hyj, hj'⟩ := hj.2
      exact huniq i j yj (hmem i yi hyi yj (hsub j hyj) (hi'.trans hj'.symm)) hyj
    · obtain ⟨y₁, hy₁, h₁⟩ := h₁'.2
      constructor
      · rintro ⟨-, y₂, hy₂, h₂⟩
        exact (h₁.symm.trans (hsame j y₁ hy₁ y₂ hy₂)).trans h₂
      · intro h
        exact ⟨h₂', y₁, hy₁, h₁.trans h⟩
    · intro y hy y' hy' hyy'
      obtain ⟨j, hj⟩ := hcov y hy
      exact ⟨j, ⟨hj, hy', y, hj, hyy'⟩, fun k hk => huniq k j y hk.1 hj⟩

/-! ### `B ⇒ A`: `A` re-proved outright (B is not used) -/

theorem exists_isomorphic' :
    type_of% @Polyfold.EpFunctor.IsProperCovering.exists_isomorphic_of_isomorphic.{0, 0} := by
  intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x x' h y hy
  obtain ⟨φ, hφs, hφt⟩ := h
  obtain ⟨ψ, ⟨hψm, hψs⟩, -⟩ := hF.existsUnique_lift (φ := φ) (y := y) (hφs.trans hy.symm)
  exact ⟨Y.tgt ψ, by rw [← F.tgt_mor, hψm, hφt], ψ, hψs, rfl⟩

theorem fiberIndex_eq' : type_of% @Polyfold.EpFunctor.IsProperCovering.fiberIndex_eq.{0, 0} := by
  intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x x' h
  have key : ∀ {x x' : ObjX}, X.Isomorphic x x' → F.fiberIndex x ⊆ F.fiberIndex x' := by
    rintro x x' h _ ⟨y, hy, rfl⟩
    obtain ⟨y', hy', hyy'⟩ := exists_isomorphic' hF h hy
    exact ⟨y', hy', (Y.π_eq_π_iff.2 hyy').symm⟩
  exact Subset.antisymm (key h) (key h.symm)

theorem B_to_A : B → A := by
  intro _
  refine ⟨exists_isomorphic', fiberIndex_eq', ?_, ?_⟩
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x x' h
    refine ⟨fiberIndex_eq' hF h, fun y hy y' hy' hyy' => ⟨Y.π y, ⟨⟨y, hy, rfl⟩,
      ⟨hy, rfl⟩, hy', (Y.π_eq_π_iff.2 hyy').symm⟩, fun c hc => ?_⟩⟩
    exact (show Y.π y = c from hc.2.1.2).symm
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x x' h
    let b := fun x : ObjX =>
      ((EpFunctor.injOn_fiberClass (F := F) x).bijOn_image).equiv (F.fiberClass x)
    refine ⟨(b x).symm.trans ((Equiv.setCongr (fiberIndex_eq' hF h)).trans (b x')),
      fun Θ y hy y' hy' => ?_⟩
    set c := (b x).symm Θ with hc
    have hΘ : (Θ : Set ObjY) = F.fiberClass x c := by
      have := congrArg Subtype.val ((b x).apply_symm_apply Θ)
      exact this.symm
    rw [hΘ] at hy
    have hy'' : y' ∈ F.fiberClass x' c := hy'
    exact Y.π_eq_π_iff.1 ((show Y.π y = c from hy.2).trans hy''.2.symm)

#rt_check RoundTrip.V8_40.A_to_B [Polyfold.EpFunctor.IsProperCovering.exists_isomorphic_of_isomorphic,
  Polyfold.EpFunctor.IsProperCovering.fiberIndex_eq,
  Polyfold.EpFunctor.IsProperCovering.lemma_8_10,
  Polyfold.EpFunctor.IsProperCovering.lemma_8_10_equiv]
#rt_check RoundTrip.V8_40.B_to_A [Polyfold.EpFunctor.IsProperCovering.exists_isomorphic_of_isomorphic,
  Polyfold.EpFunctor.IsProperCovering.fiberIndex_eq,
  Polyfold.EpFunctor.IsProperCovering.lemma_8_10,
  Polyfold.EpFunctor.IsProperCovering.lemma_8_10_equiv]
#rt_overlap RoundTrip.V8_40.B_to_A [Polyfold.EpFunctor.IsProperCovering.exists_isomorphic_of_isomorphic,
  Polyfold.EpFunctor.IsProperCovering.fiberIndex_eq,
  Polyfold.EpFunctor.IsProperCovering.lemma_8_10,
  Polyfold.EpFunctor.IsProperCovering.lemma_8_10_equiv]

end RoundTrip.V8_40
