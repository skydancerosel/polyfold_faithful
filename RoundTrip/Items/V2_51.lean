import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_51

/-! Round trip for V2_51 (Theorem 2.45: interiors of faces and faces of face-structured
M-polyfolds).

`A` is the conjunction of the types of `MPolyfold.theorem_2_45_interior`,
`MPolyfold.isSubMPolyfold_of_local`, `MPolyfold.theorem_2_45_isSubMPolyfold_interior`,
`MPolyfold.exists_localFace_of_isFaceStructured`, `MPolyfold.theorem_2_45_isSubMPolyfold_face`,
`MPolyfold.theorem_2_45_isTame_face` and `MPolyfold.isTame_of_forall_exists_chart` (namespace
`Polyfold`), all at universe `0`.

`A → B`:
* (interior) B's interior of `F = closure G` is `F ∩ {d_X = 1}`; `theorem_2_45_interior` says this
  is `G`, a sub-M-polyfold by `theorem_2_45_isSubMPolyfold_interior`.
* (face-structured case) `theorem_2_45_isSubMPolyfold_face` and `theorem_2_45_isTame_face`
  (paracompactness of `F` from `paracompactSpace_of_isClosed`).
* (local face count) NOT in `A`: the project proves it as `Polyfold.proposition_2_42` (the chart
  model `O` of a tame chart around `x` is a face-structured M-polyfold with `d_O ∘ φ = d_X`), which
  is not among the listed theorems.  It is used here, transported from the M-polyfold `O` to B's
  "faces of the open set `U = dom φ`" along `φ⁻¹ : O → U` (`localCount`).
* (global count) is the definition of face-structured.

Harness note: the statement of `theorem_2_45_isTame_face` contains the banned
`theorem_2_45_isSubMPolyfold_face` (as the proof argument of `subPolyfold`), so `#rt_check` fails
for any proof that mentions `A`.  The proof is therefore `A'_to_B`, where `A'` is `A` with that
proof term replaced by an arbitrary proof `hsub` (definitionally implied by `A`, by proof
irrelevance: `A_to_A'`); `#rt_check` is run on `A'_to_B`, and `A_to_B := A'_to_B ∘ A_to_A'`.

`B → A` fails: `A` contains proof-internal statements that B does not imply:
`exists_localFace_of_isFaceStructured` (near each point of a face, the face is a face of a tame
local model), and the general criterion `isSubMPolyfold_of_local`.  The face-structured
conjuncts follow from B (`B_to_isSubMPolyfold_face`, `B_to_isTame_face`).  The interior conjuncts
(`F ∩ {d_X = 1} = G`, and `G` a sub-M-polyfold) would follow from B's interior claim plus local
connectedness of sub-M-polyfolds (then `G` is clopen in the locally connected `F ∩ {d_X = 1}`);
that topological fact is not proved here. -/

namespace RoundTrip.V2_51
open Polyfold Set

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.theorem_2_45_interior.{0}) ∧
    (type_of% @Polyfold.MPolyfold.isSubMPolyfold_of_local.{0}) ∧
    (type_of% @Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_interior.{0}) ∧
    (type_of% @Polyfold.MPolyfold.exists_localFace_of_isFaceStructured.{0}) ∧
    (type_of% @Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_face.{0}) ∧
    (type_of% @Polyfold.MPolyfold.theorem_2_45_isTame_face.{0}) ∧
    (type_of% @Polyfold.MPolyfold.isTame_of_forall_exists_chart.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.theorem_2_45_interior.{0}, @Polyfold.MPolyfold.isSubMPolyfold_of_local.{0},
    @Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_interior.{0},
    @Polyfold.MPolyfold.exists_localFace_of_isFaceStructured.{0},
    @Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_face.{0},
    @Polyfold.MPolyfold.theorem_2_45_isTame_face.{0},
    @Polyfold.MPolyfold.isTame_of_forall_exists_chart.{0}⟩

/-! ### Glue: transporting faces along an embedding with a continuous left inverse -/

section Transport

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] (h : β → α) (g : α → β)
  (hh : Continuous h) (hg : ContinuousOn g (range h)) (hgh : ∀ b, g (h b) = b)
include hh hg hgh

theorem image_connectedComponentIn (s : Set β) {b : β} (hb : b ∈ s) :
    h '' connectedComponentIn s b = connectedComponentIn (h '' s) (h b) := by
  refine (hh.continuousOn.image_connectedComponentIn_subset hb).antisymm ?_
  have hgs : g '' (h '' s) = s := by rw [image_image]; simp [hgh]
  have := (hg.mono (image_subset_range h s)).image_connectedComponentIn_subset
    (mem_image_of_mem h hb)
  rw [hgs, hgh] at this
  intro a ha
  obtain ⟨c, -, rfl⟩ := connectedComponentIn_subset _ _ ha
  exact ⟨c, by simpa [hgh] using this (mem_image_of_mem g ha), rfl⟩

omit hh in
theorem image_closure (s : Set β) (hh : Continuous h) :
    h '' closure s = range h ∩ closure (h '' s) := by
  refine Subset.antisymm (fun a ⟨c, hc, hca⟩ => ⟨⟨c, hca⟩, ?_⟩) ?_
  · rw [← hca]; exact image_closure_subset_closure_image hh (mem_image_of_mem h hc)
  · rintro a ⟨⟨c, rfl⟩, hac⟩
    refine ⟨c, ?_, rfl⟩
    have hcont : ContinuousWithinAt g (h '' s) (h c) :=
      (hg (h c) (mem_range_self c)).mono (image_subset_range h s)
    have := hcont.mem_closure_image hac
    rwa [image_image, show (fun x => g (h x)) = id from funext hgh, image_id, hgh] at this

end Transport

/-! ### The local face count from Proposition 2.42 -/

section LocalCount

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- The faces of the open set `dom φ` (B's `IsFaceOfOpen`) through `y` correspond to the faces of
the M-polyfold `O` through `φ y`, when `d_O ∘ φ = d_X` and `O` is face-structured. -/
theorem localCount (φ : MChart X) (hne : φ.model.O.Nonempty)
    (hdO : ∀ y (hy : y ∈ φ.source),
      (φ.model.toMPolyfold ⟨_, φ.mapsTo_model y hy⟩).degIndex ⟨φ y, φ.mapsTo_model y hy⟩ =
        P.degIndex y)
    (hfs : (φ.model.toMPolyfold hne).IsFaceStructured) (y : X) (hy : y ∈ φ.source) :
    {G : Set X | IsFaceOfOpen P φ.source G ∧ y ∈ G}.encard = (P.degIndex y : ℕ∞) := by
  classical
  set M := φ.model with hM
  set Q := M.toMPolyfold hne with hQ
  set V := φ.source with hV
  obtain ⟨z₀, hz₀⟩ := hne
  -- the embedding `h = φ⁻¹ : O → X` and its left inverse `g = φ` on `V`
  let h : M.O → X := fun z => φ.symm z
  let g : X → M.O := fun x => if hx : x ∈ V then ⟨φ x, φ.mapsTo_model x hx⟩ else ⟨z₀, hz₀⟩
  have hh : Continuous h :=
    continuousOn_iff_continuous_domRestrict.1 φ.continuousOn_invFun
  have hrange : range h = V := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩; exact φ.symm_mapsTo z.2
    · intro hx; exact ⟨⟨φ x, φ.mapsTo_model x hx⟩, φ.symm_apply_apply hx⟩
  have hgV : ∀ x (hx : x ∈ V), g x = ⟨φ x, φ.mapsTo_model x hx⟩ := fun x hx => dif_pos hx
  have hg : ContinuousOn g (range h) := by
    rw [hrange, continuousOn_iff_continuous_domRestrict]
    have : V.domRestrict g = fun x : V => (⟨φ x, φ.mapsTo_model x x.2⟩ : M.O) :=
      funext fun x => hgV x x.2
    rw [this]
    exact (continuousOn_iff_continuous_domRestrict.1 φ.continuousOn_toFun).subtype_mk _
  have hgh : ∀ z, g (h z) = z := fun z => by
    rw [hgV _ (φ.symm_mapsTo z.2)]
    exact Subtype.ext (φ.apply_symm_apply z.2)
  have hhg : ∀ x ∈ V, h (g x) = x := fun x hx => by
    rw [hgV x hx]; exact φ.symm_apply_apply hx
  -- `d_O = d_X ∘ h`
  have hdeg : ∀ z : M.O, Q.degIndex z = P.degIndex (h z) := fun z => by
    have := hdO (h z) (φ.symm_mapsTo z.2)
    have hz : (⟨φ (h z), φ.mapsTo_model _ (φ.symm_mapsTo z.2)⟩ : M.O) = z :=
      Subtype.ext (φ.apply_symm_apply z.2)
    rw [hz] at this
    exact this
  have hD : h '' {w : M.O | Q.degIndex w = 1} = V ∩ {x | P.degIndex x = 1} := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨φ.symm_mapsTo w.2, by change P.degIndex (h w) = 1; rw [← hdeg]; exact hw⟩
    · rintro ⟨hx, hx1⟩
      refine ⟨g x, ?_, hhg x hx⟩
      change Q.degIndex (g x) = 1
      rw [hdeg, hhg x hx]; exact hx1
  -- the image of a face of `O`
  have hface : ∀ z : M.O, Q.degIndex z = 1 →
      h '' closure (connectedComponentIn {w : M.O | Q.degIndex w = 1} z) =
        V ∩ closure (connectedComponentIn (V ∩ {x | P.degIndex x = 1}) (h z)) := fun z hz => by
    rw [image_closure h g hg hgh _ hh, hrange,
      image_connectedComponentIn h g hh hg hgh _ (show z ∈ {w : M.O | Q.degIndex w = 1} from hz),
      hD]
  have hinj : InjOn (image h) univ := fun s _ t _ hst => by
    have := congrArg (image g) hst
    simpa [image_image, hgh] using this
  have hset : {G : Set X | IsFaceOfOpen P V G ∧ y ∈ G} =
      image h '' {F : Set M.O | Q.IsFace F ∧ g y ∈ F} := by
    ext G
    constructor
    · rintro ⟨⟨x', hx'V, hx'1, rfl⟩, hyG⟩
      have hz1 : Q.degIndex (g x') = 1 := by rw [hdeg, hhg x' hx'V]; exact hx'1
      have hGeq := hface (g x') hz1
      rw [hhg x' hx'V] at hGeq
      refine ⟨closure (connectedComponentIn {w : M.O | Q.degIndex w = 1} (g x')),
        ⟨⟨g x', hz1, rfl⟩, ?_⟩, hGeq⟩
      rw [← hGeq] at hyG
      obtain ⟨w, hw, rfl⟩ := hyG
      rwa [hgh]
    · rintro ⟨F, ⟨⟨z, hz1, rfl⟩, hyF⟩, rfl⟩
      refine ⟨⟨h z, φ.symm_mapsTo z.2, by rw [← hdeg]; exact hz1, hface z hz1⟩, ?_⟩
      exact ⟨g y, hyF, hhg y hy⟩
  rw [hset, (hinj.mono (subset_univ _)).encard_image, hfs (g y), hdeg, hhg y hy]

/-- B's local face count, from `Polyfold.proposition_2_42` (not one of the listed theorems). -/
theorem localFaceCount (hP : P.IsTame) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, {G : Set X | IsFaceOfOpen P U G ∧ y ∈ G}.encard = (P.degIndex y : ℕ∞) := by
  obtain ⟨⟨φ, -, hx, -, hdO, hfs⟩, -⟩ := proposition_2_42 P hP x
  have hne : φ.model.O.Nonempty := ⟨φ x, φ.mapsTo_model x hx⟩
  exact ⟨φ.source, φ.isOpen_source, hx, fun y hy => localCount P φ hne hdO (hfs hne) y hy⟩

end LocalCount

/-- `A` with the proof `theorem_2_45_isSubMPolyfold_face P hP hfs hF` that occurs inside the
*statement* of `theorem_2_45_isTame_face` (as the argument of `subPolyfold`) replaced by an
arbitrary proof `hsub` (and the paracompactness instance on `F` by an arbitrary one).  Both are
proofs of propositions, so `A → A'` is definitional (`A_to_A'`).  `A'` is needed only for the
harness: `#rt_check` follows the constants of `A`'s own definition, so any proof that mentions `A`
reaches the banned `theorem_2_45_isSubMPolyfold_face` through the statement of
`theorem_2_45_isTame_face`. -/
def A' : Prop :=
  (type_of% @Polyfold.MPolyfold.theorem_2_45_interior.{0}) ∧
    (type_of% @Polyfold.MPolyfold.isSubMPolyfold_of_local.{0}) ∧
    (type_of% @Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_interior.{0}) ∧
    (type_of% @Polyfold.MPolyfold.exists_localFace_of_isFaceStructured.{0}) ∧
    (type_of% @Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_face.{0}) ∧
    (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
      P.IsTame → P.IsFaceStructured → ∀ {F : Set X}, P.IsFace F →
        ∀ (hsub : P.IsSubMPolyfold F) [ParacompactSpace F],
          (MPolyfold.subPolyfold hsub).IsTame ∧
            ∀ x : F, P.degIndex x = (MPolyfold.subPolyfold hsub).degIndex x + 1) ∧
    (type_of% @Polyfold.MPolyfold.isTame_of_forall_exists_chart.{0})

/-- `A → A'` by proof irrelevance (definitional). -/
theorem A_to_A' : A → A' := fun ⟨h1, h2, h3, h4, h5, h6, h7⟩ =>
  ⟨h1, h2, h3, h4, h5, fun P hP hfs _ hF _ _ => h6 P hP hfs hF, h7⟩

theorem A'_to_B : A' → B := by
  intro hA X _ _ _ P hP
  obtain ⟨hint, -, hsubint, -, hsubface, htame, -⟩ := hA
  refine ⟨?_, ?_, localFaceCount P hP, fun hfs x => hfs x⟩
  · rintro F ⟨y₀, -, rfl⟩
    have : faceInterior P (closure (connectedComponentIn {y | P.degIndex y = 1} y₀)) =
        connectedComponentIn {y | P.degIndex y = 1} y₀ := hint P hP y₀
    rw [this]
    exact hsubint P hP y₀
  · intro hfs F hF
    have hpc : ParacompactSpace F :=
      MPolyfold.paracompactSpace_of_isClosed (MPolyfold.IsFace.isClosed P hF)
    exact ⟨hsubface P hP hfs hF, hpc, htame P hP hfs hF (hsubface P hP hfs hF)⟩

theorem A_to_B : A → B := fun h => A'_to_B (A_to_A' h)

/-- `B` gives `theorem_2_45_isSubMPolyfold_face`. -/
theorem B_to_isSubMPolyfold_face (hB : B) {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] (P : MPolyfold X) (hP : P.IsTame) (hfs : P.IsFaceStructured) {F : Set X}
    (hF : P.IsFace F) : P.IsSubMPolyfold F :=
  ((hB X P hP).2.1 hfs F hF).1

/-- `B` gives `theorem_2_45_isTame_face`, for any proof `hsub` that `F` is a sub-M-polyfold and any
paracompactness instance on `F` (both propositions). -/
theorem B_to_isTame_face (hB : B) {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] (P : MPolyfold X) (hP : P.IsTame) (hfs : P.IsFaceStructured) {F : Set X}
    (hF : P.IsFace F) (hsub : P.IsSubMPolyfold F) [ParacompactSpace F] :
    (MPolyfold.subPolyfold hsub).IsTame ∧
      ∀ x : F, P.degIndex x = (MPolyfold.subPolyfold hsub).degIndex x + 1 := by
  obtain ⟨_, _, h1, h2⟩ := (hB X P hP).2.1 hfs F hF
  exact ⟨h1, h2⟩

#rt_check RoundTrip.V2_51.A'_to_B [Polyfold.MPolyfold.theorem_2_45_interior,
  Polyfold.MPolyfold.isSubMPolyfold_of_local, Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_interior,
  Polyfold.MPolyfold.exists_localFace_of_isFaceStructured,
  Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_face, Polyfold.MPolyfold.theorem_2_45_isTame_face,
  Polyfold.MPolyfold.isTame_of_forall_exists_chart]
#rt_check RoundTrip.V2_51.B_to_isSubMPolyfold_face [Polyfold.MPolyfold.theorem_2_45_interior,
  Polyfold.MPolyfold.isSubMPolyfold_of_local, Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_interior,
  Polyfold.MPolyfold.exists_localFace_of_isFaceStructured,
  Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_face, Polyfold.MPolyfold.theorem_2_45_isTame_face,
  Polyfold.MPolyfold.isTame_of_forall_exists_chart]
#rt_check RoundTrip.V2_51.B_to_isTame_face [Polyfold.MPolyfold.theorem_2_45_interior,
  Polyfold.MPolyfold.isSubMPolyfold_of_local, Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_interior,
  Polyfold.MPolyfold.exists_localFace_of_isFaceStructured,
  Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_face, Polyfold.MPolyfold.theorem_2_45_isTame_face,
  Polyfold.MPolyfold.isTame_of_forall_exists_chart]

end RoundTrip.V2_51
