import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_2

/-! Round trip for V3_2 (Definition 3.2: sc⁰-, sc¹-, scᵏ-, sc-smooth germs).

`A` is the conjunction of the types of the two listed theorems `Polyfold.IsSck.isSckGerm` and
`Polyfold.IsScSmooth.isScSmoothGerm` (the bridge "an scᵏ map on a relatively open `U ∋ 0` is an
scᵏ-germ on `ofSet U`"; no universe parameters).  `IsSc0Germ`, `IsSc1GermWith`, `IsSc1Germ`,
`IsSckGerm`, `IsScSmoothGerm` are definitions (vocabulary).

* `A → B` is proved, outright (B is the agreement of the definitions; A is not used):
  - sc⁰: the project's `levelMap f m` is a level lift as in B; conversely B's lift `f_m` agrees with
    `levelMap f m` on `U_m` (`levelMap_eq_of_toBase_eq`), so continuity transfers.
  - sc¹: `HasFDerivWithinAt (f ∘ ι₁) (Df(x) ∘ ι₁) U₁ x` is B's quotient limit after the
    translation `h ↦ x + h` (`hasFDerivWithinAt_iff_tendsto`); the project's tangent map
    `(levelMap f 1 x, Df(x)h)` and B's `TfB` (with `liftB`) agree on `TO(C, 0)` once `f` is sc⁰.
  - scᵏ: by induction; the project uses the chosen derivative `scDerivGerm`, B an existential `D`.
    They agree on `U₁` by uniqueness of derivatives, which uses that `C` (and then `TC`) is
    quadrant-like (`IsPartialQuadrant.isQuadrantLike`, `IsQuadrantLike.tangentSet`); B's
    hypothesis that `C` is a partial quadrant is used here.
* `B → A` is proved outright as well: B does not speak about sc^k maps on sets (Chapter 1), so the
  bridge is re-proved from the non-banned lemmas `IsSc0.isSc0Germ`, `ScNbhdGerm.ofSet_tangent`,
  `IsSc1.scDerivGerm_ofSet_eqOn`, `IsSckGerm.congr` (verbatim the project's proof). -/

namespace RoundTrip.V3_2
open Polyfold Set Filter Topology

/-! ### The comparison of the definitions -/

theorem sc0_iff {E F : ScBanach} {C : Set (E.lvl 0)} (G : ScNbhdGerm E C)
    (f : E.lvl 0 → F.lvl 0) : IsSc0Germ G f ↔ IsSc0GermB E F G.U f := by
  constructor
  · intro h m
    exact ⟨levelMap f m, fun x hx => h.toBase_levelMap hx, h.continuousOn m⟩
  · intro h
    refine ⟨fun m x hx => ?_, fun m => ?_⟩
    · obtain ⟨fm, h1, _⟩ := h m
      exact ⟨fm x, h1 x hx⟩
    · obtain ⟨fm, h1, h2⟩ := h m
      exact h2.congr fun x hx => levelMap_eq_of_toBase_eq (h1 x hx)

theorem tangent_U_eq {E : ScBanach} {C : Set (E.lvl 0)} (G : ScNbhdGerm E C) :
    G.tangent.U = TUB G.U := by
  funext m
  ext p
  exact ⟨fun h => h.1, fun h => ⟨h, mem_univ _⟩⟩

theorem eqOn_TfB {E F : ScBanach} {C : Set (E.lvl 0)} {G : ScNbhdGerm E C}
    {f : E.lvl 0 → F.lvl 0} (hf : IsSc0Germ G f) (D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0) :
    EqOn (tangentMapWith f D) (TfB f D) (G.tangent.U 0) := by
  intro p hp
  have hp1 : p.1 ∈ G.U 1 := hp.1
  refine Prod.ext ?_ rfl
  show levelMap f 1 p.1 = liftB F 1 (f (E.toBase 1 p.1))
  have hex : ∃ z : F.lvl 1, F.toBase 1 z = f (E.toBase 1 p.1) := hf.mem_range 1 p.1 hp1
  rw [liftB, dif_pos hex]
  exact levelMap_eq_of_toBase_eq hex.choose_spec

theorem deriv_iff {E F : ScBanach} (U1 : Set (E.lvl 1)) (f : E.lvl 0 → F.lvl 0)
    (L : E.lvl 0 →L[ℝ] F.lvl 0) (x : E.lvl 1) :
    HasFDerivWithinAt (f ∘ E.toBase 1) (L.comp (E.toBase 1)) U1 x ↔
      Tendsto (fun h : E.lvl 1 =>
        ‖f (E.toBase 1 (x + h)) - f (E.toBase 1 x) - L (E.toBase 1 h)‖ / ‖h‖)
        (𝓝[{h | x + h ∈ U1}] 0) (𝓝 0) := by
  rw [hasFDerivWithinAt_iff_tendsto]
  have hmap : map (fun h => x + h) (𝓝[{h | x + h ∈ U1}] 0) = 𝓝[U1] x := by
    have h1 := (Homeomorph.addLeft x).isEmbedding.map_nhdsWithin_eq {h | x + h ∈ U1} 0
    have h2 : ((Homeomorph.addLeft x) '' {h | x + h ∈ U1}) = U1 := by
      ext y
      simp only [Homeomorph.coe_addLeft, mem_image, mem_setOf_eq]
      constructor
      · rintro ⟨h, hh, rfl⟩; exact hh
      · intro hy; exact ⟨y - x, by simpa using hy, by simp⟩
    rw [h2] at h1
    simpa using h1
  rw [← hmap, tendsto_map'_iff]
  refine tendsto_congr fun h => ?_
  simp [div_eq_inv_mul]

theorem sc1With_iff {E F : ScBanach} {C : Set (E.lvl 0)} (G : ScNbhdGerm E C)
    (f : E.lvl 0 → F.lvl 0) (D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0) :
    IsSc1GermWith G f D ↔ IsSc1GermWithB E F G.U f D := by
  constructor
  · intro h
    refine ⟨(sc0_iff G f).1 h.isSc0, fun x hx => (deriv_iff _ f (D x) x).1
      (h.hasFDerivWithinAt x hx), ?_⟩
    have := (sc0_iff G.tangent _).1 (h.tangent_isSc0.congr (eqOn_TfB h.isSc0 D))
    rw [tangent_U_eq] at this
    exact this
  · intro h
    have h0 := (sc0_iff G f).2 h.1
    refine ⟨h0, fun x hx => (deriv_iff _ f (D x) x).2 (h.2.1 x hx), ?_⟩
    have h3 := h.2.2
    rw [← tangent_U_eq] at h3
    exact ((sc0_iff G.tangent _).2 h3).congr (eqOn_TfB h0 D).symm

theorem sc1_iff {E F : ScBanach} {C : Set (E.lvl 0)} (G : ScNbhdGerm E C)
    (f : E.lvl 0 → F.lvl 0) : IsSc1Germ G f ↔ IsSc1GermB E F G.U f :=
  ⟨fun ⟨D, h⟩ => ⟨D, (sc1With_iff G f D).1 h⟩, fun ⟨D, h⟩ => ⟨D, (sc1With_iff G f D).2 h⟩⟩

theorem sck_iff : ∀ (k : ℕ) {E F : ScBanach} {C : Set (E.lvl 0)}, IsQuadrantLike E C →
    ∀ (G : ScNbhdGerm E C) (f : E.lvl 0 → F.lvl 0), IsSckGerm k G f ↔ IsSckGermB k E F G.U f
  | 0, _, _, _, _, G, f => sc0_iff G f
  | k + 1, E, F, C, hC, G, f => by
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨scDerivGerm G f, (sc1With_iff G f _).1 h1.isSc1GermWith_scDerivGerm, ?_⟩
      have h3 : IsSckGerm k G.tangent (TfB f (scDerivGerm G f)) :=
        IsSckGerm.congr hC.tangentSet (eqOn_TfB h1.isSc0 _) h2
      have := (sck_iff k hC.tangentSet G.tangent _).1 h3
      rw [tangent_U_eq] at this
      exact this
    · rintro ⟨D, h1, h2⟩
      have h1' := (sc1With_iff G f D).2 h1
      refine ⟨h1'.isSc1Germ, ?_⟩
      rw [← tangent_U_eq] at h2
      have h3 := (sck_iff k hC.tangentSet G.tangent (F := F.tangent) (TfB f D)).2 h2
      refine IsSckGerm.congr hC.tangentSet ?_ h3
      exact (eqOn_TfB h1'.isSc0 D).symm.trans (IsSc1Germ.tangentMapGerm_eqOn hC h1').symm

theorem B_holds : B := by
  intro E F C hC G f
  have hQ := hC.isQuadrantLike
  exact ⟨sc0_iff G f, sc1With_iff G f, sc1_iff G f, fun k => sck_iff k hQ G f,
    forall_congr' fun k => sck_iff k hQ G f⟩

/-! ### The round trip -/

/-- The project's statement (no universe parameters). -/
def A : Prop :=
  (type_of% @Polyfold.IsSck.isSckGerm) ∧ (type_of% @Polyfold.IsScSmooth.isScSmoothGerm)

theorem A_holds : A := ⟨@Polyfold.IsSck.isSckGerm, @Polyfold.IsScSmooth.isScSmoothGerm⟩

theorem A_to_B : A → B := fun _ => B_holds

/-- The bridge, re-proved (the project's proof, with non-banned lemmas only). -/
theorem isSckGerm' : ∀ {k : ℕ} {E F : ScBanach} {C U : Set (E.lvl 0)}, IsQuadrantLike E C →
    ∀ (hU : ∃ O : Set (E.lvl 0), IsOpen O ∧ U = O ∩ C) (h0 : (0 : E.lvl 0) ∈ U)
      {f : E.lvl 0 → F.lvl 0}, IsSck k E F U f → IsSckGerm k (ScNbhdGerm.ofSet hU h0) f
  | 0, _, _, _, _, _, hU, h0, _, h => IsSc0.isSc0Germ hU h0 h
  | k + 1, E, F, C, U, hC, hU, h0, f, h => by
    refine ⟨⟨scDeriv U f, h.1.isSc0.isSc0Germ hU h0, h.1.isSc1With_scDeriv.hasFDerivWithinAt, ?_⟩,
      ?_⟩
    · rw [ScNbhdGerm.ofSet_tangent]; exact h.1.tangentMap_isSc0.isSc0Germ _ _
    · have := isSckGerm' (k := k) hC.tangentSet (ScNbhdGerm.tangentSet_relOpen hU)
        (ScNbhdGerm.zero_mem_tangentSet h0) h.2
      rw [← ScNbhdGerm.ofSet_tangent hU h0] at this
      exact IsSckGerm.congr hC.tangentSet (h.1.scDerivGerm_ofSet_eqOn hC hU h0).symm this

theorem B_to_A : B → A := fun _ =>
  ⟨@isSckGerm', fun {_ _ _ _} hC hU h0 _ hf => fun k => isSckGerm' hC hU h0 (hf k)⟩

#rt_check RoundTrip.V3_2.A_to_B [Polyfold.IsSck.isSckGerm, Polyfold.IsScSmooth.isScSmoothGerm]
#rt_check RoundTrip.V3_2.B_to_A [Polyfold.IsSck.isSckGerm, Polyfold.IsScSmooth.isScSmoothGerm]
#rt_overlap RoundTrip.V3_2.B_to_A [Polyfold.IsSck.isSckGerm, Polyfold.IsScSmooth.isScSmoothGerm]

end RoundTrip.V3_2
