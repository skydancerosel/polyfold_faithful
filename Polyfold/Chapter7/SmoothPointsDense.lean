import Polyfold.Chapter7.Zhou

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §7.1, p. 289 and
pp. 289–290 (2017: §7.1, pp. 227–228): the filtrations `X = X₀ ⊃ X₁ ⊃ ⋯ ⊃ X_∞` of the object and
morphism M-polyfolds of an ep-groupoid, the density of `X_∞` in every `X_k`, and the induced
filtration `|X| = |X₀| ⊃ |X₁| ⊃ ⋯ ⊃ |X_∞| = ⋂_k |X_k|` of the orbit space.

# Smooth points are dense; the filtration of `|X|`

## The text, paraphrased

(2021 p. 289) The M-polyfolds `X` and `𝐗` carry the filtrations `X = X₀ ⊃ X₁ ⊃ ⋯ ⊃
X_∞ = ⋂_k X_k`; the set `X_∞` is dense in every `X_k`.  (pp. 289–290) Source and target maps
preserve the levels, so `ml(x) = ml(y) = ml(φ)` for `φ : x → y`, and the filtration of `X`
induces the filtration `|X| = |X₀| ⊃ |X₁| ⊃ ⋯ ⊃ |X_∞| = ⋂_k |X_k|` of the orbit space.  The
density is stated without proof.  Part I proves it for sc-Banach spaces (Definition 1.1.1 (2)),
and uses "`U_∞` is dense in every `U_k`" for `U` relatively open in a partial quadrant in the
proof of Lemma 2.2.1 (2021 p. 30).

## What is formalized

* `IsPartialQuadrant.lvlSet_subset_closure_smooth`: for a partial quadrant `C ⊆ E`,
  `C_m ∩ E_∞` is dense in `C_m` (on level `m`, in `E_m`).
* `IsRelOpenInQuadrant.lvlSet_subset_closure_smooth`: the same for `U` relatively open in `C`
  (the fact used in the proof of Lemma 2.2.1).
* `ScRetraction.lvlSet_retract_subset_closure_smooth`, `IsScRetract.lvlSet_subset_closure_smooth`:
  for a retract `O = r(U)`, `O_m ∩ E_∞` is dense in `O_m`.
* `MPolyfold.mem_smoothSet_of_chart` and **`MPolyfold.denseSmooth`**: for every M-polyfold `X`
  and every `m`, `X_∞` is dense in `X_m` (with the topology of `X_m`), i.e. Chapter 7's
  hypothesis `MPolyfold.DenseSmooth` (gap G.73) holds for every M-polyfold;
  `MPolyfold.dense_smoothSet` (`X_∞` dense in `X`), `MPolyfold.smoothRegular_iff` (the field
  `denseSmooth` of `SmoothRegular` is automatic).
* **`EpGroupoid.denseSmooth_obj`**, **`EpGroupoid.denseSmooth_mor`**, `EpGroupoid.p289_dense_2021`:
  the density for the object and the morphism M-polyfold of an ep-groupoid.
* The filtration of `|X|` (gap G.72): `EpGroupoid.mem_levelSet_of_isomorphic`,
  `π_mem_orbitLevel_iff`, `preimage_orbitLevel` (`π⁻¹(|X_k|) = X_k`), `orbitLevel_zero`,
  `orbitLevel_antitone`, `orbitSmooth` (`|X_∞| = π(X_∞)`), `preimage_orbitSmooth`,
  **`orbitSmooth_eq_iInter`** (`|X_∞| = ⋂_k |X_k|`), `p290_orbit_filtration_2021`.
* `EpGroupoid.dense_orbitSmooth`: `|X_∞|` is dense in `|X|`.  The text does not state this; it
  follows from the density of `X_∞` in `X` and the continuity of `π`.

## What the text leaves implicit, and the choices made

* The density in a retract is proved as the round-trip audit sketched it: approximate `x ∈ O_m`
  in `U_m` by points of `U_m ∩ E_∞`, apply `r`, which maps smooth points to smooth points and is
  continuous on level `m`, and use `r(x) = x`.  The density of `U_m ∩ E_∞` in `U_m` for `U`
  relatively open in a partial quadrant `C` comes from the convexity of `C_m` and its nonempty
  interior: `C_m ⊆ cl(int C_m)`, and `E_∞` is dense in the open set `int C_m`.
* For the M-polyfold, a nonempty open subset of `X_m` is read in a chart through the embedding
  `V_m → O_m ⊆ E_m` (`MPolyfold.isEmbedding_levelLift`), and the chart inverse of a smooth point
  of `O_m` is a smooth point of `X`.
* `|X_k|` is Chapter 7's `orbitLevel k = π(X_k)`; `|X_∞|` is defined as `π(X_∞)`, and the text's
  `|X_∞| = ⋂_k |X_k|` is then a theorem (it uses that `X_k` is saturated).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

variable {E : ScBanach}

/-! ### Density in partial quadrants and retracts -/

/-- For a partial quadrant `C ⊆ E`, the smooth points of `C_m` are dense in `C_m`. -/
theorem IsPartialQuadrant.lvlSet_subset_closure_smooth {C : Set (E 0)}
    (hC : IsPartialQuadrant E C) (m : ℕ) :
    E.lvlSet C m ⊆ closure (E.lvlSet C m ∩ E.smoothLvl m) := by
  intro x hx
  have h1 : x ∈ closure (interior (E.lvlSet C m)) := by
    rw [(hC.convex_lvlSet m).closure_interior_eq_closure_of_nonempty_interior
      (hC.interior_lvlSet_nonempty m)]
    exact subset_closure hx
  have h2 : interior (E.lvlSet C m) ⊆ closure (interior (E.lvlSet C m) ∩ E.smoothLvl m) :=
    (E.dense_smooth m).open_subset_closure_inter isOpen_interior
  exact closure_mono (inter_subset_inter_left _ interior_subset)
    (closure_minimal h2 isClosed_closure h1)

/-- For `U` relatively open in a partial quadrant, `U_∞` is dense in every `U_m` (the fact used in
the proof of 2021 Lemma 2.2.1). -/
theorem IsRelOpenInQuadrant.lvlSet_subset_closure_smooth {C U : Set (E 0)}
    (hU : IsRelOpenInQuadrant E C U) (m : ℕ) :
    E.lvlSet U m ⊆ closure (E.lvlSet U m ∩ E.smoothLvl m) := by
  obtain ⟨O, hO, rfl⟩ := hU.relOpen
  intro x hx
  rw [ScBanach.lvlSet_inter] at hx ⊢
  have h := (E.isOpen_lvlSet hO m).inter_closure
    ⟨hx.1, hU.isPartialQuadrant.lvlSet_subset_closure_smooth m hx.2⟩
  refine closure_mono ?_ h
  rintro y ⟨hyO, hyC, hyS⟩
  exact ⟨⟨hyO, hyC⟩, hyS⟩

/-- For a retract `O = r(U)`, the smooth points of `O_m` are dense in `O_m`. -/
theorem ScRetraction.lvlSet_retract_subset_closure_smooth {C : Set (E 0)} (R : ScRetraction E C)
    (m : ℕ) : E.lvlSet R.retract m ⊆ closure (E.lvlSet R.retract m ∩ E.smoothLvl m) := by
  intro x hx
  have hxU : x ∈ E.lvlSet R.U m := R.lvlSet_retract_subset m hx
  have h0 := R.isSc1.isSc0
  have hfix : levelMap R m x = x :=
    levelMap_eq_of_toBase_eq (R.apply_eq_self_of_mem_retract hx).symm
  have hcont : ContinuousWithinAt (levelMap R m) (E.lvlSet R.U m ∩ E.smoothLvl m) x :=
    ((h0.continuousOn m) x hxU).mono inter_subset_left
  have hcl := hcont.mem_closure_image (R.relOpen.lvlSet_subset_closure_smooth m hxU)
  rw [hfix] at hcl
  refine closure_mono ?_ hcl
  rintro _ ⟨e, ⟨heU, heS⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [ScBanach.mem_lvlSet, h0.toBase_levelMap heU]
    exact ⟨_, heU, rfl⟩
  · change E.toBase m (levelMap R m e) ∈ E.smooth
    rw [h0.toBase_levelMap heU, E.mem_smooth_iff]
    intro j
    obtain ⟨y, hy⟩ := E.mem_smooth_iff.1 (show E.toBase m e ∈ E.smooth from heS) j
    have hyU : y ∈ E.lvlSet R.U j := by rw [ScBanach.mem_lvlSet, hy]; exact heU
    have := h0.mem_range j y hyU
    rwa [hy] at this

/-- For a retract `(O, C, E)`, the smooth points of `O_m` are dense in `O_m`. -/
theorem IsScRetract.lvlSet_subset_closure_smooth {C O : Set (E 0)} (h : IsScRetract E C O)
    (m : ℕ) : E.lvlSet O m ⊆ closure (E.lvlSet O m ∩ E.smoothLvl m) := by
  obtain ⟨R, rfl⟩ := h
  exact R.lvlSet_retract_subset_closure_smooth m

/-! ### Density of `X_∞` in `X_m` for an M-polyfold -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

variable {P} in
/-- A point of a chart domain whose image is a smooth point of `E` is a smooth point of `X`. -/
theorem mem_smoothSet_of_chart {φ : MChart X} (hφ : P.IsChart φ) {x : X} (hx : x ∈ φ.source)
    (h : φ x ∈ φ.model.E.smooth) : x ∈ P.smoothSet :=
  mem_iInter.2 fun j => (P.mem_levelSet_iff hφ hx).2 (φ.model.E.mem_smooth_iff.1 h j)

/-- **2021 p. 289 (2017 p. 227), gap G.73**: for every M-polyfold `X` and every `m`, the smooth
points `X_∞` are dense in `X_m` (with the topology of `X_m`).  This is Chapter 7's hypothesis
`DenseSmooth`. -/
theorem denseSmooth : P.DenseSmooth := by
  intro m
  refine dense_iff_inter_open.2 fun S hS ⟨y, hyS⟩ => ?_
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source (P.levelVal m y)
  have hemb := P.isEmbedding_levelLift hφ m
  have hSV : IsOpen ((Subtype.val : (P.levelVal m ⁻¹' φ.source : Set (P.Level m)) → P.Level m) ⁻¹'
      S) := hS.preimage continuous_subtype_val
  obtain ⟨W, hW, hWeq⟩ := hemb.isInducing.isOpen_iff.1 hSV
  set z₀ := levelLift φ m (P.levelVal m y) with hz₀
  have hz₀W : z₀ ∈ W := by
    have : (⟨y, hyφ⟩ : (P.levelVal m ⁻¹' φ.source : Set (P.Level m))) ∈
        (Subtype.val ⁻¹' S : Set (P.levelVal m ⁻¹' φ.source : Set (P.Level m))) := hyS
    rw [← hWeq] at this
    exact this
  have hz₀O : z₀ ∈ φ.model.E.lvlSet φ.model.O m := by
    rw [ScBanach.mem_lvlSet, hz₀, P.toBase_levelLift hφ hyφ (levelVal_mem y)]
    exact φ.mapsTo_model _ hyφ
  obtain ⟨z, hzW, hzO, hzS⟩ := mem_closure_iff.1
    (φ.model.isScRetract.lvlSet_subset_closure_smooth m hz₀O) W hW hz₀W
  have hzO' : φ.model.E.toBase m z ∈ φ.model.O := hzO
  set x := φ.symm (φ.model.E.toBase m z) with hx
  have hxφ : x ∈ φ.source := φ.symm_mapsTo hzO'
  have hφx : φ x = φ.model.E.toBase m z := φ.apply_symm_apply hzO'
  have hxm : x ∈ P.levelSet m := (P.mem_levelSet_iff hφ hxφ).2 ⟨z, hφx.symm⟩
  have hlift : levelLift φ m x = z := by
    apply φ.model.E.toBase_injective m
    rw [P.toBase_levelLift hφ hxφ hxm, hφx]
  refine ⟨P.levelMk m x hxm, ?_, ?_⟩
  · have : (⟨P.levelMk m x hxm, hxφ⟩ : (P.levelVal m ⁻¹' φ.source : Set (P.Level m))) ∈
        (fun x : (P.levelVal m ⁻¹' φ.source : Set (P.Level m)) =>
          levelLift φ m (P.levelVal m x)) ⁻¹' W := by
      change levelLift φ m x ∈ W
      rw [hlift]; exact hzW
    rw [hWeq] at this
    exact this
  · exact mem_smoothSet_of_chart (x := x) hφ hxφ (by rw [hφx]; exact hzS)

/-- `X_∞` is dense in `X`. -/
theorem dense_smoothSet : Dense P.smoothSet := P.denseSmooth.dense

/-- The field `denseSmooth` of `SmoothRegular` holds for every M-polyfold. -/
theorem smoothRegular_iff : P.SmoothRegular ↔
    P.SmoothConnected ∧ IsOpenMap P.tangentProj ∧ P.TangentDeterminedSmooth :=
  ⟨fun h => ⟨h.smoothConnected, h.isOpenMap_tangentProj, h.tangentDeterminedSmooth⟩,
    fun h => ⟨P.denseSmooth, h.1, h.2.1, h.2.2⟩⟩

end MPolyfold

/-! ### Ep-groupoids: density on objects and morphisms, the filtration of `|X|` -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- `X_∞` is dense in every `X_k` (2021 p. 289). -/
theorem denseSmooth_obj : X.PObj.DenseSmooth := X.PObj.denseSmooth

/-- `𝐗_∞` is dense in every `𝐗_k` (2021 p. 289). -/
theorem denseSmooth_mor : X.PMor.DenseSmooth := X.PMor.denseSmooth

/-- **2021 p. 289 (2017 p. 227)**: for an ep-groupoid `(X, 𝐗)`, `X_∞` is dense in every `X_k` and
`𝐗_∞` is dense in every `𝐗_k`. -/
theorem p289_dense_2021 :
    (∀ k, Dense {y : X.PObj.Level k | X.PObj.levelVal k y ∈ X.PObj.smoothSet}) ∧
      ∀ k, Dense {y : X.PMor.Level k | X.PMor.levelVal k y ∈ X.PMor.smoothSet} :=
  ⟨X.denseSmooth_obj, X.denseSmooth_mor⟩

/-- Isomorphic objects lie on the same levels: `ml(x) = ml(y)` for `φ : x → y`. -/
theorem mem_levelSet_of_isomorphic {x y : Obj} (h : X.Isomorphic x y) {k : ℕ}
    (hx : x ∈ X.PObj.levelSet k) : y ∈ X.PObj.levelSet k := by
  obtain ⟨φ, rfl, rfl⟩ := h
  exact (X.mem_levelSet_tgt_iff φ k).2 ((X.mem_levelSet_src_iff φ k).1 hx)

/-- `|x| ∈ |X_k| ⟺ x ∈ X_k`. -/
theorem π_mem_orbitLevel_iff {x : Obj} {k : ℕ} : X.π x ∈ X.orbitLevel k ↔ x ∈ X.PObj.levelSet k :=
  ⟨fun ⟨_, hy, hyx⟩ => X.mem_levelSet_of_isomorphic ((X.π_eq_π_iff).1 hyx) hy,
    fun hx => ⟨x, hx, rfl⟩⟩

/-- `π⁻¹(|X_k|) = X_k`: the levels are saturated. -/
theorem preimage_orbitLevel (k : ℕ) : X.π ⁻¹' X.orbitLevel k = X.PObj.levelSet k :=
  ext fun _ => X.π_mem_orbitLevel_iff

/-- `|X₀| = |X|`. -/
theorem orbitLevel_zero : X.orbitLevel 0 = univ := by
  rw [orbitLevel, X.PObj.levelSet_zero, image_univ, X.surjective_π.range_eq]

/-- `|X_k| ⊃ |X_{k+1}|`. -/
theorem orbitLevel_antitone : Antitone X.orbitLevel :=
  fun _ _ hkl => image_mono (X.PObj.levelSet_antitone hkl)

/-- `|X_∞| = π(X_∞)`, the smooth points of the orbit space (2021 p. 290). -/
def orbitSmooth : Set X.OrbitSpace := X.π '' X.PObj.smoothSet

/-- `π⁻¹(|X_∞|) = X_∞`. -/
theorem preimage_orbitSmooth : X.π ⁻¹' X.orbitSmooth = X.PObj.smoothSet := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact mem_iInter.2 fun k =>
      X.mem_levelSet_of_isomorphic ((X.π_eq_π_iff).1 hyx) (mem_iInter.1 hy k)
  · intro hx; exact ⟨x, hx, rfl⟩

/-- **2021 p. 290 (2017 p. 228), gap G.72**: `|X_∞| = ⋂_k |X_k|`. -/
theorem orbitSmooth_eq_iInter : X.orbitSmooth = ⋂ k, X.orbitLevel k := by
  ext z
  obtain ⟨x, rfl⟩ := X.surjective_π z
  rw [mem_iInter, ← mem_preimage, preimage_orbitSmooth]
  simp only [X.π_mem_orbitLevel_iff]
  exact mem_iInter

/-- **2021 pp. 289–290 (2017 pp. 227–228)**: the filtration
`|X| = |X₀| ⊃ |X₁| ⊃ ⋯ ⊃ |X_∞| = ⋂_k |X_k|` of the orbit space, with `π⁻¹(|X_k|) = X_k`. -/
theorem p290_orbit_filtration_2021 :
    X.orbitLevel 0 = univ ∧ Antitone X.orbitLevel ∧ X.orbitSmooth = ⋂ k, X.orbitLevel k ∧
      (∀ k, X.π ⁻¹' X.orbitLevel k = X.PObj.levelSet k) ∧
      X.π ⁻¹' X.orbitSmooth = X.PObj.smoothSet :=
  ⟨X.orbitLevel_zero, X.orbitLevel_antitone, X.orbitSmooth_eq_iInter, X.preimage_orbitLevel,
    X.preimage_orbitSmooth⟩

/-- `|X_∞|` is dense in `|X|` (not stated in the text; from the density of `X_∞` in `X`). -/
theorem dense_orbitSmooth : Dense X.orbitSmooth :=
  X.surjective_π.denseRange.dense_image X.continuous_π X.PObj.dense_smoothSet

end EpGroupoid

end Polyfold
