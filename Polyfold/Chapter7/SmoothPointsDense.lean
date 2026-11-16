import Polyfold.Chapter7.Zhou
import Polyfold.Chapter5.DenseSmoothPoints

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
* **`EpGroupoid.denseSmooth_obj`**, **`EpGroupoid.denseSmooth_mor`**, `EpGroupoid.p289_dense`:
  the density for the object and the morphism M-polyfold of an ep-groupoid.
* The filtration of `|X|` (gap G.72): `EpGroupoid.mem_levelSet_of_isomorphic`,
  `π_mem_orbitLevel_iff`, `preimage_orbitLevel` (`π⁻¹(|X_k|) = X_k`), `orbitLevel_zero`,
  `orbitLevel_antitone`, `orbitSmooth` (`|X_∞| = π(X_∞)`), `preimage_orbitSmooth`,
  **`orbitSmooth_eq_iInter`** (`|X_∞| = ⋂_k |X_k|`), `p290_orbit_filtration`.
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

Smooth points are dense (`MPolyfold.denseSmooth`, `MPolyfold.dense_smoothSet`,
`MPolyfold.mem_smoothSet_of_chart`, `IsScRetract.lvlSet_subset_closure_smooth`, …):
`Chapter5/DenseSmoothPoints.lean`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

variable {E : ScBanach}

/-! ### Density in partial quadrants and retracts -/

/-! ### Density of `X_∞` in `X_m` for an M-polyfold -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

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
theorem p289_dense :
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
theorem p290_orbit_filtration :
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
