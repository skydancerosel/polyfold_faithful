import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_4

set_option maxSynthPendingDepth 3

/-! Round trip for V11_4 (2021 Example 11.1.4, p. 523; 2017: Example 11.1, p. 377: the quadrant
with and without the swap).

The item lists the definition `Examples.swapEpGroupoid W` (`ℤ/2 ⋉ C`, `C = [0, ∞)² ⊕ W`,
`−1` exchanging the coordinates; vocabulary) and six theorems; `A` is the conjunction of their
types (the `W`-indexed ones have no universe parameters; `isHomeomorph_π_trivial` at `0`):
`example_11_1_4` (for **every** sc-Banach space `W`: `trivial C` is face structured, `ℤ/2 ⋉ C` is
weakly face structured and not face structured), `isFaceStructured_quadrant` (every `[0,∞)ⁿ ⊕ W`),
`isHomeomorph_π_trivial`, `setOf_degIndexOrbit_eq_one_swap`, `isOrbitFace_swap_iff`,
`not_isEpFaceStructured_swap`.  The text's case is `W = 0`; `B` is stated for `W₀ = 0`.

`B`'s notions (`FaceStructuredB`, `WeaklyFSB`) are the blind Definition 11.1.3, equivalent to the
project's (`faceStructuredB_iff`, `weaklyFSB_iff`, as in V11_3).  `B` quantifies over every
ep-groupoid `E` with the described object M-polyfold and structure maps; these determine the
orbit-space setoid, and `FaceStructuredB E` depends only on `E.PObj` and that setoid
(`faceStructuredB_eq`), so `B`'s universal claims reduce to the project's `trivial` and
`swapEpGroupoid W₀`.

* `A_to_B`: witnesses `trivial (quadrantPolyfold 2 W₀)` and `swapEpGroupoid W₀` (`actB_eq`:
  `actB g p = t(g, p) = g • p`);
  the universal claims from `example_11_1_4 W₀` by the reduction above.
* `B_to_A0`: the main conjunct at the text's case, `example_11_1_4 W₀`, from `B` (apply `B` to the
  project's two groupoids).
* `B_to_A`: `A` is about every `W` and `n`; `B` is about `W₀`, `n = 2` only, so `A` is re-proved
  outright (the project's proofs, copied, from non-item lemmas).  Vacuous: the hypothesis is not
  used. -/

namespace RoundTrip.V11_4
open Polyfold Set Function Topology Filter TameBoundary
open Polyfold.EpGroupoid.Examples Polyfold.MPolyfold Polyfold.TameBoundaryExample

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.Examples.example_11_1_4) ∧
  (type_of% @Polyfold.EpGroupoid.Examples.isFaceStructured_quadrant) ∧
  (type_of% @Polyfold.EpGroupoid.Examples.isHomeomorph_π_trivial.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.Examples.setOf_degIndexOrbit_eq_one_swap) ∧
  (type_of% @Polyfold.EpGroupoid.Examples.isOrbitFace_swap_iff) ∧
  (type_of% @Polyfold.EpGroupoid.Examples.not_isEpFaceStructured_swap)

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.Examples.example_11_1_4,
    @Polyfold.EpGroupoid.Examples.isFaceStructured_quadrant,
    @Polyfold.EpGroupoid.Examples.isHomeomorph_π_trivial.{0},
    @Polyfold.EpGroupoid.Examples.setOf_degIndexOrbit_eq_one_swap,
    @Polyfold.EpGroupoid.Examples.isOrbitFace_swap_iff,
    @Polyfold.EpGroupoid.Examples.not_isEpFaceStructured_swap⟩

/-! ### Glue: `B`'s notions are the project's, and depend only on `PObj` and the setoid -/

theorem faceIffB {S : Type} [TopologicalSpace S] (d : S → ℕ) (θ : Set S) :
    (∃ x, d x = 1 ∧ θ = closure (connectedComponentIn {y | d y = 1} x)) ↔
      ∃ s : {y // d y = 1}, θ = closure (Subtype.val '' connectedComponent s) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, by rw [connectedComponentIn_eq_image (F := {y | d y = 1}) hx]; rfl⟩
  · rintro ⟨⟨x, hx⟩, rfl⟩
    exact ⟨x, hx, by rw [connectedComponentIn_eq_image (F := {y | d y = 1}) hx]; rfl⟩

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

theorem degOrbB_eq (X : EpGroupoid Obj Mor) : degOrbB X = X.degIndexOrbit :=
  funext fun z => congrArg X.degIndexOrbit (Quotient.out_eq z)

theorem isOrbitFace_iff_B (X : EpGroupoid Obj Mor) (θ : Set X.OrbitSpace) :
    X.IsOrbitFace θ ↔ IsOrbitFaceB X θ := by
  unfold IsOrbitFaceB
  rw [degOrbB_eq]
  exact faceIffB X.degIndexOrbit θ

theorem faceStructuredB_iff (X : EpGroupoid Obj Mor) : FaceStructuredB X ↔ X.IsEpFaceStructured := by
  unfold EpGroupoid.IsEpFaceStructured FaceStructuredB EpGroupoid.orbitFacesThrough
  rw [degOrbB_eq]
  refine and_congr_right' (forall_congr' fun z => ?_)
  rw [show {θ | X.IsOrbitFace θ ∧ z ∈ θ} = {θ | IsOrbitFaceB X θ ∧ z ∈ θ} from
    Set.ext fun θ => and_congr_left' (isOrbitFace_iff_B X θ)]

theorem weaklyFSB_iff (X : EpGroupoid Obj Mor) : WeaklyFSB X ↔ X.IsWeaklyFaceStructured := by
  unfold EpGroupoid.IsWeaklyFaceStructured WeaklyFSB MPolyfold.IsFaceStructured IsFaceStructuredMB
  refine and_congr_right' (forall_congr' fun x => ?_)
  rw [show {F | X.PObj.IsFace F ∧ x ∈ F} = {F | IsFaceMB X.PObj F ∧ x ∈ F} from
    Set.ext fun F => and_congr_left' (faceIffB X.PObj.degIndex F)]

/-- `FaceStructuredB` in terms of the object M-polyfold and the orbit setoid only. -/
def FSgen (P : MPolyfold Obj) (r : Setoid Obj) : Prop :=
  P.IsTame ∧ ∀ z : Quotient r,
    {θ | (∃ s : {z : Quotient r // P.degIndex z.out = 1},
      θ = closure (Subtype.val '' connectedComponent s)) ∧ z ∈ θ}.encard = (P.degIndex z.out : ℕ∞)

theorem faceStructuredB_eq (X : EpGroupoid Obj Mor) :
    FaceStructuredB X ↔ FSgen X.PObj X.orbitSetoid := Iff.rfl

end

/-- Two ep-groupoids with the same object M-polyfold and orbit relation. -/
theorem faceStructuredB_congr {Obj Mor Mor' : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (E : EpGroupoid Obj Mor) (E' : EpGroupoid Obj Mor') (hP : E.PObj = E'.PObj)
    (hr : ∀ x y, E.Isomorphic x y ↔ E'.Isomorphic x y) :
    FaceStructuredB E ↔ FaceStructuredB E' := by
  rw [faceStructuredB_eq, faceStructuredB_eq, hP,
    show E.orbitSetoid = E'.orbitSetoid from Setoid.ext hr]

/-- `B`'s action is the project's (the target map of `swapEpGroupoid W₀`). -/
theorem actB_eq (g : ℤˣ) (p : QB) : actB g p = (swapEpGroupoid W₀).tgt (g, p) := by
  unfold actB
  rcases Int.units_eq_one_or g with rfl | rfl
  · rw [if_pos rfl]
    exact ((swapEpGroupoid W₀).tgt_unit p).symm
  · rw [if_neg (by decide),
      show (swapEpGroupoid W₀).tgt (-1, p) = swapQ W₀ p from neg_one_smul_eq W₀ p]
    rfl

theorem isIdOnlyB_trivial : IsIdOnlyB (EpGroupoid.trivial (quadrantPolyfold 2 W₀)) :=
  ⟨rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩

theorem isSwapB_swap : IsSwapB (swapEpGroupoid W₀) :=
  ⟨rfl, fun g p => ⟨rfl, (actB_eq g p).symm⟩, fun _ => rfl,
    fun g p => by rw [actB_eq]; rfl, fun _ _ _ => rfl⟩

theorem iso_idOnly {E : EpGroupoid QB QB} (hE : IsIdOnlyB E) (x y : QB) :
    E.Isomorphic x y ↔ (EpGroupoid.trivial (quadrantPolyfold 2 W₀)).Isomorphic x y := by
  constructor
  · rintro ⟨φ, rfl, rfl⟩
    exact ⟨φ, ((hE.2 φ).1).symm, ((hE.2 φ).2.1).symm⟩
  · rintro ⟨φ, rfl, rfl⟩
    exact ⟨φ, (hE.2 φ).1, (hE.2 φ).2.1⟩

theorem iso_swap {E : EpGroupoid QB (ℤˣ × QB)} (hE : IsSwapB E) (x y : QB) :
    E.Isomorphic x y ↔ (swapEpGroupoid W₀).Isomorphic x y := by
  constructor
  · rintro ⟨⟨g, p⟩, rfl, rfl⟩
    exact ⟨(g, p), ((hE.2.1 g p).1).symm, ((hE.2.1 g p).2.trans (actB_eq g p)).symm⟩
  · rintro ⟨⟨g, p⟩, rfl, rfl⟩
    exact ⟨(g, p), (hE.2.1 g p).1, (hE.2.1 g p).2.trans (actB_eq g p)⟩

/-! ### `A ⇒ B` -/

theorem A_to_B : A → B := by
  rintro ⟨hex, -⟩
  obtain ⟨htriv, hweak, hnot⟩ := hex W₀
  refine ⟨⟨_, isIdOnlyB_trivial⟩, fun E hE => ?_, ⟨_, isSwapB_swap⟩, fun E hE => ⟨?_, ?_⟩⟩
  · rw [faceStructuredB_congr E _ hE.1 (iso_idOnly hE), faceStructuredB_iff]
    exact htriv
  · have h := (weaklyFSB_iff (swapEpGroupoid W₀)).2 hweak
    unfold WeaklyFSB at h ⊢
    rw [hE.1]
    exact h
  · rw [faceStructuredB_congr E _ hE.1 (iso_swap hE), faceStructuredB_iff]
    exact hnot

/-! ### `B ⇒ A` at the text's case `W = 0` -/

/-- The main conjunct of `A` at `W = W₀`. -/
def A0 : Prop :=
  (EpGroupoid.trivial (quadrantPolyfold 2 W₀)).IsEpFaceStructured ∧
    (swapEpGroupoid W₀).IsWeaklyFaceStructured ∧ ¬ (swapEpGroupoid W₀).IsEpFaceStructured

theorem A_to_A0 : A → A0 := fun h => h.1 W₀

theorem B_to_A0 : B → A0 := by
  rintro ⟨-, htriv, -, hswap⟩
  obtain ⟨hw, hn⟩ := hswap _ isSwapB_swap
  exact ⟨(faceStructuredB_iff _).1 (htriv _ isIdOnlyB_trivial), (weaklyFSB_iff _).1 hw,
    fun h => hn ((faceStructuredB_iff _).2 h)⟩

/-! ### `B ⇒ A`, vacuous: `A` for every `W` re-proved outright (the project's proofs, copied) -/

section Copies

variable (W : ScBanach)

theorem setOf_degIndexOrbit_eq_one_swap' :
    {z | (swapEpGroupoid W).degIndexOrbit z = 1} = (swapEpGroupoid W).π '' part (0 : Fin 2) := by
  ext z
  obtain ⟨p, rfl⟩ := (swapEpGroupoid W).surjective_π z
  rw [Set.mem_ofPred_eq, degIndexOrbit_swap, dq_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    fin_cases k
    · exact ⟨p, hk, rfl⟩
    · refine ⟨swapQ W p, ⟨hk.1, fun l hl => ?_⟩, ?_⟩
      · fin_cases l
        · exact absurd rfl hl
        · exact hk.2 0 (by decide)
      · rw [← neg_one_smul_eq]
        exact ((action_π_eq_π_iff (isScSmoothMap_swap_smul W)).2 ⟨-1, rfl⟩).symm
  · rintro ⟨q, hq, hqp⟩
    obtain ⟨k, rfl⟩ := (action_π_eq_π_iff (isScSmoothMap_swap_smul W)).1 hqp
    rcases Int.units_eq_one_or k with rfl | rfl
    · exact ⟨0, by rwa [one_smul]⟩
    · refine ⟨1, ?_⟩
      rw [neg_one_smul_eq]
      refine ⟨hq.1, fun l hl => ?_⟩
      fin_cases l
      · exact hq.2 1 (by decide)
      · exact absurd rfl hl

theorem isOrbitFace_swap_iff' (θ : Set (swapEpGroupoid W).OrbitSpace) :
    (swapEpGroupoid W).IsOrbitFace θ ↔
      θ = closure {z | (swapEpGroupoid W).degIndexOrbit z = 1} := by
  have hS : IsConnected {z | (swapEpGroupoid W).degIndexOrbit z = 1} := by
    rw [setOf_degIndexOrbit_eq_one_swap']
    exact (isConnected_part_zero W).image _ (swapEpGroupoid W).continuous_π.continuousOn
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [hS.isPreconnected.connectedComponentIn hz]
  · rintro rfl
    obtain ⟨z, hz⟩ := hS.nonempty
    exact ⟨z, hz, by rw [hS.isPreconnected.connectedComponentIn hz]⟩

theorem not_isEpFaceStructured_swap' : ¬ (swapEpGroupoid W).IsEpFaceStructured := by
  rintro ⟨-, h⟩
  have hc := h ((swapEpGroupoid W).π (corner W))
  have hfaces : (swapEpGroupoid W).orbitFacesThrough ((swapEpGroupoid W).π (corner W)) =
      {closure {z | (swapEpGroupoid W).degIndexOrbit z = 1}} := by
    ext θ
    refine ⟨fun hθ => (isOrbitFace_swap_iff' W θ).1 hθ.1,
      fun hθ => ⟨(isOrbitFace_swap_iff' W θ).2 hθ, ?_⟩⟩
    rw [mem_singleton_iff.1 hθ, setOf_degIndexOrbit_eq_one_swap']
    exact closure_mono (image_mono subset_rfl) <|
      (map_mem_closure (swapEpGroupoid W).continuous_π (corner_mem_closure_part W)
        fun x hx => mem_image_of_mem _ hx)
  rw [hfaces, encard_singleton, degIndexOrbit_swap] at hc
  have h2 : dq 2 W (corner W) = 2 := quadrantPolyfold_degIndex_zero 2 W
  rw [h2] at hc
  exact absurd hc (by decide)

theorem isFaceStructured_quadrant' (n : ℕ) : (quadrantPolyfold n W).IsFaceStructured := by
  intro x
  have h := (isFaceStructuredOpen_quadrant (W := W) (n := n) isOpen_univ).2 x (mem_univ x)
  rw [← h]
  congr 1
  ext θ
  exact and_congr_left' ((quadrantPolyfold n W).isFaceIn_univ_iff).symm

theorem isHomeomorph_π_trivial' {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (P : MPolyfold Z) : IsHomeomorph (EpGroupoid.trivial P).π := by
  refine ⟨(EpGroupoid.trivial P).continuous_π, (EpGroupoid.trivial P).proposition_7_1,
    fun x y hxy => ?_, (EpGroupoid.trivial P).surjective_π⟩
  obtain ⟨φ, rfl, rfl⟩ := (EpGroupoid.trivial P).π_eq_π_iff.1 hxy
  rfl

theorem example_11_1_4' :
    (EpGroupoid.trivial (quadrantPolyfold 2 W)).IsEpFaceStructured ∧
      (swapEpGroupoid W).IsWeaklyFaceStructured ∧ ¬ (swapEpGroupoid W).IsEpFaceStructured := by
  refine ⟨?_, ⟨quadrantPolyfold_isTame 2 W, isFaceStructured_quadrant' W 2⟩,
    not_isEpFaceStructured_swap' W⟩
  refine EpGroupoid.isEpFaceStructured_iff.2 ⟨quadrantPolyfold_isTame 2 W, ?_⟩
  exact (isFaceStructuredOpen_univ_iff (isHomeomorph_π_trivial' _)
    fun _ => rfl).1 (isFaceStructuredOpen_quadrant isOpen_univ)

end Copies

theorem B_to_A : B → A := fun _ =>
  ⟨example_11_1_4', isFaceStructured_quadrant', fun P => isHomeomorph_π_trivial' P,
    setOf_degIndexOrbit_eq_one_swap', isOrbitFace_swap_iff', not_isEpFaceStructured_swap'⟩

#rt_check RoundTrip.V11_4.A_to_B [Polyfold.EpGroupoid.Examples.example_11_1_4,
  Polyfold.EpGroupoid.Examples.isFaceStructured_quadrant,
  Polyfold.EpGroupoid.Examples.isHomeomorph_π_trivial,
  Polyfold.EpGroupoid.Examples.setOf_degIndexOrbit_eq_one_swap,
  Polyfold.EpGroupoid.Examples.isOrbitFace_swap_iff,
  Polyfold.EpGroupoid.Examples.not_isEpFaceStructured_swap]
#rt_check RoundTrip.V11_4.B_to_A0 [Polyfold.EpGroupoid.Examples.example_11_1_4,
  Polyfold.EpGroupoid.Examples.isFaceStructured_quadrant,
  Polyfold.EpGroupoid.Examples.isHomeomorph_π_trivial,
  Polyfold.EpGroupoid.Examples.setOf_degIndexOrbit_eq_one_swap,
  Polyfold.EpGroupoid.Examples.isOrbitFace_swap_iff,
  Polyfold.EpGroupoid.Examples.not_isEpFaceStructured_swap]
#rt_check RoundTrip.V11_4.B_to_A [Polyfold.EpGroupoid.Examples.example_11_1_4,
  Polyfold.EpGroupoid.Examples.isFaceStructured_quadrant,
  Polyfold.EpGroupoid.Examples.isHomeomorph_π_trivial,
  Polyfold.EpGroupoid.Examples.setOf_degIndexOrbit_eq_one_swap,
  Polyfold.EpGroupoid.Examples.isOrbitFace_swap_iff,
  Polyfold.EpGroupoid.Examples.not_isEpFaceStructured_swap]
#rt_overlap RoundTrip.V11_4.B_to_A0 [Polyfold.EpGroupoid.Examples.example_11_1_4,
  Polyfold.EpGroupoid.Examples.isFaceStructured_quadrant,
  Polyfold.EpGroupoid.Examples.isHomeomorph_π_trivial,
  Polyfold.EpGroupoid.Examples.setOf_degIndexOrbit_eq_one_swap,
  Polyfold.EpGroupoid.Examples.isOrbitFace_swap_iff,
  Polyfold.EpGroupoid.Examples.not_isEpFaceStructured_swap]
#rt_overlap RoundTrip.V11_4.B_to_A [Polyfold.EpGroupoid.Examples.example_11_1_4,
  Polyfold.EpGroupoid.Examples.isFaceStructured_quadrant,
  Polyfold.EpGroupoid.Examples.isHomeomorph_π_trivial,
  Polyfold.EpGroupoid.Examples.setOf_degIndexOrbit_eq_one_swap,
  Polyfold.EpGroupoid.Examples.isOrbitFace_swap_iff,
  Polyfold.EpGroupoid.Examples.not_isEpFaceStructured_swap]

end RoundTrip.V11_4
