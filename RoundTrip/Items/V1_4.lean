import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_4

/-! Round trip for V1_4 (Definition 1.5: sc-subspaces, sc-complements, sc-splittings).

`A` is the conjunction of the types of the theorems `ScBanach.isClosed_levelSub`,
`ScBanach.IsScSplitting.closedComplemented` and `ScBanach.IsScSplitting.symm` (no universe
parameters); `levelSub`, `IsScSubspace`, `ofSubspaceScale`, `ofSubspace`, `IsScSplitting` are
vocabulary.  `B` says that the project's `IsScSubspace` and `IsScSplitting` are exactly the text's
notions (with the full sc-structure conditions on `F_m = F ∩ E_m`, and topological direct sums).

* `A → B` (proved): the text's induced structure `A_m = A ∩ E_m` has the same smooth points as
  `E` (the composite inclusions `A_m → A₀` are those of `E`), so its density condition is the
  project's `levelSub A m ⊆ closure (levelSub A m ∩ smoothLvl m)`; its completeness and
  compactness conditions hold because the levels `A_m` are closed (`A`'s `isClosed_levelSub`), and
  injectivity is automatic.  The topological direct sum `E_m = F_m ⊕ G_m` comes from `IsCompl` of the closed
  (by `A`'s `isClosed_levelSub`) subspaces `F_m`, `G_m` (Mathlib's `prodEquivOfClosedCompl`, i.e.
  the closed graph theorem); conversely a topological direct sum is in particular `IsCompl`, and
  the completeness of `G₀ = G` required by the text's sc-structure gives that `G` is closed.
* `B → A` (proved): `closedComplemented` and `symm` follow from `B` (the text's splittings have
  continuous projections and are symmetric); `isClosed_levelSub` (closed `A` ⇒ closed `A_m`, for
  any closed `A`, not only sc-subspaces) is not about the notions `B` characterizes and is
  re-proved from the definitions. -/

namespace RoundTrip.V1_4
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.ScBanach.isClosed_levelSub) ∧
    (type_of% @Polyfold.ScBanach.IsScSplitting.closedComplemented) ∧
    (type_of% @Polyfold.ScBanach.IsScSplitting.symm)

theorem A_holds : A :=
  ⟨@Polyfold.ScBanach.isClosed_levelSub, @Polyfold.ScBanach.IsScSplitting.closedComplemented,
    @Polyfold.ScBanach.IsScSplitting.symm⟩

section Glue

/-- The composite inclusion `A_m → A₀` of the text's induced structure is `E_m → E₀`. -/
theorem inclTo0_sub (E : ScBanach) (A' : Submodule ℝ (E.lvl 0)) :
    ∀ m (x : lvlSub E A' m),
      ((inclTo0 (fun m => lvlSub E A' m) (subIncl E A') m x : lvlSub E A' 0) : E.lvl 0) =
        E.toBase m x
  | 0, _ => rfl
  | m + 1, x => inclTo0_sub E A' m (subIncl E A' m x)

/-- The smooth points of the text's induced structure on `A` are those of `E`. -/
theorem mem_preimage_smoothPts (E : ScBanach) (A' : Submodule ℝ (E.lvl 0)) (m : ℕ)
    (x : lvlSub E A' m) :
    x ∈ inclTo0 (fun m => lvlSub E A' m) (subIncl E A') m ⁻¹'
        smoothPts (fun m => lvlSub E A' m) (subIncl E A') ↔
      (x : E.lvl m) ∈ E.smoothLvl m := by
  simp only [Set.mem_preimage, smoothPts, Set.mem_iInter, Set.mem_range]
  rw [ScScale.mem_smoothLvl_iff]
  refine forall_congr' fun j => ⟨fun ⟨y, hy⟩ => ⟨y, ?_⟩, fun ⟨y, hy⟩ => ⟨⟨y, ?_⟩, ?_⟩⟩
  · have := congrArg Subtype.val hy
    rwa [inclTo0_sub, inclTo0_sub] at this
  · change E.toBase j y ∈ A'
    rw [hy]; exact x.2
  · apply Subtype.ext
    rw [inclTo0_sub, inclTo0_sub]
    exact hy

/-- With closed levels `A_m`, the text's induced structure on `A` is an sc-structure iff the
project's density condition holds. -/
theorem isScStructureOn_iff (E : ScBanach) (A' : Submodule ℝ (E.lvl 0))
    (hcl : ∀ m, IsClosed (E.levelSub A' m : Set (E.lvl m))) :
    IsScStructureOn E A' ↔
      ∀ m, (E.levelSub A' m : Set (E.lvl m)) ⊆ closure (E.levelSub A' m ∩ E.smoothLvl m) := by
  have hd : ∀ m, Dense (inclTo0 (fun m => lvlSub E A' m) (subIncl E A') m ⁻¹'
        smoothPts (fun m => lvlSub E A' m) (subIncl E A')) ↔
      (E.levelSub A' m : Set (E.lvl m)) ⊆ closure (E.levelSub A' m ∩ E.smoothLvl m) := by
    intro m
    have hs : inclTo0 (fun m => lvlSub E A' m) (subIncl E A') m ⁻¹'
        smoothPts (fun m => lvlSub E A' m) (subIncl E A') =
        (Subtype.val ⁻¹' E.smoothLvl m : Set (lvlSub E A' m)) :=
      Set.ext fun x => mem_preimage_smoothPts E A' m x
    rw [hs, Subtype.dense_iff]
    apply Iff.of_eq
    congr 2
    ext y
    constructor
    · rintro ⟨⟨y, hy⟩, hs, rfl⟩
      exact ⟨hy, hs⟩
    · rintro ⟨hy, hs⟩
      exact ⟨⟨y, hy⟩, hs, rfl⟩
  constructor
  · intro h m
    exact (hd m).1 (h.2.2.2 m)
  · intro h
    refine ⟨fun m => (hcl m).completeSpace_coe, fun m x y hxy => ?_, fun m => ?_,
      fun m => (hd m).2 (h m)⟩
    · apply Subtype.ext
      apply E.incl_injective m
      exact congrArg Subtype.val hxy
    · exact ((E.incl_isCompactOperator m).comp_clm (lvlSub E A' (m + 1)).subtypeL).codRestrict _
        (hcl m)

theorem isScSubspace_iff (E : ScBanach) (A' : Submodule ℝ (E.lvl 0))
    (hcl : IsClosed (A' : Set (E.lvl 0)) → ∀ m, IsClosed (E.levelSub A' m : Set (E.lvl m))) :
    E.IsScSubspace A' ↔ IsScSubspaceText E A' :=
  ⟨fun h => ⟨h.1, (isScStructureOn_iff E A' (hcl h.1)).2 h.2⟩,
    fun h => ⟨h.1, (isScStructureOn_iff E A' (hcl h.1)).1 h.2⟩⟩

/-- The completeness of `G₀` in the text's sc-structure on `G` makes `G` closed. -/
theorem isClosed_of_on (E : ScBanach) (G : Submodule ℝ (E.lvl 0)) (h : IsScStructureOn E G) :
    IsClosed (G : Set (E.lvl 0)) := by
  have h0 : CompleteSpace (lvlSub E G 0) := h.1 0
  have : IsComplete ((lvlSub E G 0 : Submodule ℝ (E.lvl 0)) : Set (E.lvl 0)) :=
    completeSpace_coe_iff_isComplete.1 h0
  exact this.isClosed

theorem isCompl_of_top {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {P Q : Submodule ℝ V} (h : IsTopDirectSum P Q) : IsCompl P Q := by
  obtain ⟨e, he⟩ := h
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxP hxQ
    have h1 : e ((⟨x, hxP⟩ : P), (0 : Q)) = e ((0 : P), (⟨x, hxQ⟩ : Q)) := by
      rw [he, he]; simp
    have h2 := congrArg (fun z : P × Q => (z.1 : V)) (e.injective h1)
    simpa using h2
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    obtain ⟨⟨p, q⟩, rfl⟩ := e.surjective v
    rw [he]
    exact Submodule.add_mem_sup p.2 q.2

theorem top_of_isCompl {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {P Q : Submodule ℝ V} (h : IsCompl P Q) (hP : IsClosed (P : Set V))
    (hQ : IsClosed (Q : Set V)) : IsTopDirectSum P Q :=
  ⟨Submodule.prodEquivOfClosedCompl P Q h hP hQ, fun _ _ => rfl⟩

theorem top_symm {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {P Q : Submodule ℝ V} (h : IsTopDirectSum P Q) : IsTopDirectSum Q P := by
  obtain ⟨e, he⟩ := h
  exact ⟨(ContinuousLinearEquiv.prodComm ℝ Q P).trans e, fun q p => by
    simp [he, add_comm]⟩

end Glue

theorem A_to_B : A → B := by
  intro hA
  have hsub : ∀ (E : ScBanach) (A' : Submodule ℝ (E.lvl 0)),
      E.IsScSubspace A' ↔ IsScSubspaceText E A' := fun E A' => isScSubspace_iff E A' (hA.1 E)
  refine ⟨hsub, fun E F G => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨hF, hG, hc⟩ := h
    refine ⟨(hsub E F).1 hF, ?_, ((hsub E G).1 hG).2, fun m =>
      top_of_isCompl (hc m) (hA.1 E hF.1 m) (hA.1 E hG.1 m)⟩
    have := hc 0
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
  · obtain ⟨hFt, -, hGs, htop⟩ := h
    have hGc := isClosed_of_on E G hGs
    exact ⟨(hsub E F).2 hFt, (hsub E G).2 ⟨hGc, hGs⟩,
      fun m => isCompl_of_top (htop m)⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun E A' hA m => hA.preimage (E.toBase m).continuous, fun E F G h m => ?_,
    fun E F G h => ?_⟩
  · obtain ⟨-, -, -, htop⟩ := (hB.2 E F G).1 h
    obtain ⟨e, he⟩ := htop m
    let f : E.lvl m →L[ℝ] lvlSub E F m := (ContinuousLinearMap.fst ℝ _ _).comp
      (e.symm : E.lvl m →L[ℝ] lvlSub E F m × lvlSub E G m)
    refine ⟨f, fun x => ?_⟩
    have : e.symm (x : E.lvl m) = (x, 0) := by
      apply e.injective
      rw [ContinuousLinearEquiv.apply_symm_apply]
      have := he x 0
      simp only [ZeroMemClass.coe_zero, add_zero] at this
      exact this.symm
    change (e.symm (x : E.lvl m)).1 = x
    rw [this]
  · obtain ⟨hFt, hcompl, hGs, htop⟩ := (hB.2 E F G).1 h
    exact (hB.2 E G F).2 ⟨⟨isClosed_of_on E G hGs, hGs⟩, hcompl.symm, hFt.2,
      fun m => top_symm (htop m)⟩

#rt_check RoundTrip.V1_4.A_to_B [Polyfold.ScBanach.isClosed_levelSub,
  Polyfold.ScBanach.IsScSplitting.closedComplemented, Polyfold.ScBanach.IsScSplitting.symm]
#rt_check RoundTrip.V1_4.B_to_A [Polyfold.ScBanach.isClosed_levelSub,
  Polyfold.ScBanach.IsScSplitting.closedComplemented, Polyfold.ScBanach.IsScSplitting.symm]
#rt_overlap RoundTrip.V1_4.B_to_A [Polyfold.ScBanach.isClosed_levelSub,
  Polyfold.ScBanach.IsScSplitting.closedComplemented, Polyfold.ScBanach.IsScSplitting.symm]

end RoundTrip.V1_4
