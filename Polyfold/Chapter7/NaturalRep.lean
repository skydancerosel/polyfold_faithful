import Polyfold.Chapter7.EpGroupoid
import Polyfold.Chapter7.ProperMaps
import Polyfold.Chapter7.LocConnected
import Polyfold.Chapter7.Discrete
import Polyfold.Chapter7.LocalDiffeo

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 7: **Theorem 7.1.13 (2017: 7.1)** (the natural representation of `G_x`, p. 231) and its restatement
**Theorem 7.6.1 (2017: 7.5)** with its proof in Appendix 7.5.1 (pp. 253–254), including **Lemma 7.6.2 (2017: 7.8)**
(pp. 253–254) and **Lemma 7.6.3 (2017: 7.9)** (p. 345 (2017 p. 254)).  There is no 2014 preprint of Part II; numbers and pages
are the 2017 text's.

# The natural representation of the isotropy group

## The text, paraphrased

(Theorem 7.1.13 (2017: 7.1) = Theorem 7.6.1 (2017: 7.5)) Let `x₀` be an object and `V ∋ x₀` open.  There are an open
`U ⊆ V` of `x₀`, a group homomorphism `Φ : G_{x₀} → Diff_sc(U)`, `Φ(g) = t_g ∘ s_g⁻¹`, and an
sc-smooth `Γ : G_{x₀} × U → 𝐗` with `Γ(g, x₀) = g`, `s Γ(g, y) = y`, `t Γ(g, y) = Φ(g)(y)`, and
every `h : y → z` between points of `U` is `Γ(g, y)` for a unique `g`.  (Proof, p. 253) For
every `g ∈ G_{x₀}` choose contractible open `N^t_g`, `N^s_g` on which `t` and `s` are
sc-diffeomorphisms onto some open `U₀ ∋ x₀`; since `G_{x₀}` is finite, `N^t_g ∪ N^s_g` may be
taken disjoint; `N_g := N^t_g ∩ N^s_g`, `s_g := s|N_g`, `t_g := t|N_g`.  (Lemma 7.6.2 (2017: 7.8)) There is an
open `U₁ ⊆ U₀` of `x₀` such that every morphism `h` with `s(h), t(h) ∈ U₁` belongs to some
`N_g`: otherwise there are `h_k ∉ ⋃ N_g` with `s(h_k), t(h_k) → x₀`; by properness
`h_{k_l} → h`, necessarily `h ∈ G_{x₀}`, so `h ∈ N_g` for some `g`, a contradiction.
(Lemma 7.6.3 (2017: 7.9)) There is an open `U₂ ⊆ U₁` of `x₀` such that `U := ⋃_g t_g s_g⁻¹(U₂)` is contained
in `U₁` and invariant under all `t_g s_g⁻¹`: choose `U₂` so small that `U` and `t_g s_g⁻¹(U)`
lie in `U₁`; for `x = t_h s_h⁻¹(u) ∈ U`, `u ∈ U₂`, the point `v := t_g s_g⁻¹ t_h s_h⁻¹(u) ∈ U₁`
is the target of a morphism `u → v`, which by Lemma 7.6.2 (2017: 7.8) is `s_{g'}⁻¹(u)` for some `g'`, so
`v = t_{g'} s_{g'}⁻¹(u) ∈ U`.  Then `Φ(g) := t_g ∘ s_g⁻¹ : U → U`; "since the neighborhoods
`N_g` … are disjoint and since the structure maps are continuous" `Φ` is a homomorphism;
`Γ(g, y) := s_g⁻¹(y)`.

## What is formalized

* **The choices of the proof**: `NatRepConstruction.Sheets X x` (open `N_g ∋ g`, pairwise
  disjoint, `s : N_g → s(N_g)` an sc-diffeomorphism with inverse `s_g⁻¹ = σ g`, `t` an
  sc-diffeomorphism on `N_g`), `NatRepConstruction.exists_sheets`; `G_x` is finite
  (`NatRepConstruction.finite_isotropy`, from Definition 7.1.3 (2017: 7.3) (1), (3)); `Sheets.hat`
  (`t_g ∘ s_g⁻¹`) and `Sheets.unionHat` (`⋃_g t_g s_g⁻¹(U₂)`).
* **Lemma 7.6.2 (2017: 7.8)**: `lemma_7_6_2`, for any open neighbourhoods `N_g ∋ g` and any neighbourhood `U₀`.
* **Lemma 7.6.3 (2017: 7.9)**: `lemma_7_6_3` (with `U₂` connected), and `Sheets.isOpen_unionHat`,
  `Sheets.isConnected_unionHat`, `Sheets.mem_unionHat`: `U` is an open connected neighbourhood.
* The homomorphism: `Sheets.eqOn_σ_one` (`s_1⁻¹ = u` on a connected `U`), `Sheets.hat_one`,
  `Sheets.eqOn_σ_mul` (`s_{gh}⁻¹(y) = s_g⁻¹(Φ(h) y) ∘ s_h⁻¹(y)`), `Sheets.hat_mul`,
  `Sheets.isScDiffeoOn_hat`; the natural representation `Sheets.mkRep` on every open connected
  invariant `U ⊆ ⋂_g s(N_g)` satisfying the conclusion of Lemma 7.6.2 (2017: 7.8).
* **Theorem 7.6.1 (2017: 7.5)**, in the form of its proof: `NatRepConstruction.exists_naturalRep_sheets`
  (`Φ(g) = t_g ∘ s_g⁻¹`, `Γ(g, ·) = s_g⁻¹`).  **Theorem 7.1.13 (2017: 7.1)**: `theorem_7_1_13`; **Theorem 7.6.1 (2017: 7.5)**:
  `theorem_7_6_1` (a restatement).
* Smaller neighbourhoods: `NatRepConstruction.restrict` and `exists_naturalRep_restrict` (a
  natural representation restricts, with the same `Φ`, `Γ`, to every smaller open connected
  invariant neighbourhood of `x`), and `exists_naturalRep_shrink` (into every open `V ∋ x`).

## Reading

* **Connectedness** (PLAN II.6, 3).  "`Φ` is a homomorphism" is proved by comparing the two
  continuous sections `y ↦ s_{gh}⁻¹(y)` and `y ↦ s_g⁻¹(Φ(h) y) ∘ s_h⁻¹(y)` of `s` over `U`; they
  agree at `x₀`, and the set where they agree is open and closed, i.e. the sheet index is only
  locally constant.  As we read it, the argument needs `U` connected, which the text does not
  state (it does choose a connected `U(x)` on p. 231).  The same holds for `Φ(1) = id`, which the
  text does not mention and which is needed for `Φ(g) ∈ Diff_sc(U)` with inverse `Φ(g⁻¹)`: `s_1⁻¹`
  and the unit section `u` agree at `x₀`.  We take `U₂` connected (M-polyfolds are locally
  connected, `LocConnected.lean`; the text does not state it).  Then `U = ⋃_g t_g s_g⁻¹(U₂)` is
  connected itself, a union of connected sets through `x₀ = t_g s_g⁻¹(x₀)`; no passage to a
  connected component is needed.  The comparison uses `eqOn_sections_of_isPreconnected`.  The
  "contractible" `N^t_g`, `N^s_g` are not needed (as in `LocConnected.lean`).
* **The structure maps are continuous**: the continuity of `m` used here comes from
  Definition 7.1.3 (2017: 7.3) (4), in its sheet form `isScSmoothCompSheet`; that of `u` from (2).
* **The disjointness of the `N_g`** (by Hausdorff separation of the finite set `G_{x₀} ⊆ 𝐗`) is
  used only for the uniqueness in (3): `Γ(g', y) = h` puts `h` into `N_{g'}`.
* **`U ⊆ V`**: the proof does not mention `V`; we take `U₀ := V ∩ ⋂_g s(N_g)`.  The text has
  `s` and `t` map every `N_g` onto one `U₀`; only `s_g` needs to be an sc-diffeomorphism onto
  its (open) image.  That `t_g` is one too (`Sheets.isScDiffeoOn_tgt`, the text's `N^t_g`) is
  recorded but not used: `t_g s_g⁻¹(U₂)` is open because `t` is an open map and
  `s_g⁻¹(U₂) = N_g ∩ s⁻¹(U₂)`.  The text calls `U` an open neighbourhood without comment.
* **Finiteness of `G_{x₀}`** (Proposition 7.1.12 (2017: 7.4)) is taken from `Discrete.lean`
  (`MPolyfold.finite_isotropy_of_isLocalScDiffeo`).
* **Lemma 7.6.2 (2017: 7.8).**  The sequence `h_k` is chosen along a countable neighbourhood basis of `x₀`
  (`X` is metrizable, Theorem 2.3.10 (2017: 2.2) [2.16]).  "By the properness assumption" is Definition 7.1.3 (2017: 7.3) (3)
  at `x₀`: it applies to the `h_k` with `s(h_k) ∈ cl V(x₀)`, i.e. to all large `k`.  "Necessarily
  `h ∈ G_{x₀}`": `t(h) = x₀` comes with properness, `s(h) = x₀` from the continuity of `s` and
  the uniqueness of limits.  The lemma holds for any open `N_g ∋ g`; the sheet property is not
  used.  The text's "the properness assumption of ep-polyfolds" is read as that of ep-groupoids
  (possible misprint).
* **Lemma 7.6.3 (2017: 7.9).**  "`U₂` so small that `U` and `t_g s_g⁻¹(U)` are contained in `U₁`" is possible
  because each `t_g s_g⁻¹` is continuous at its fixed point `x₀` and `G_{x₀}` is finite; we ask
  `t_h s_h⁻¹(U₂) ⊆ U₁` and `t_g s_g⁻¹ t_h s_h⁻¹(U₂) ⊆ U₁`.  The morphism `u → v` is
  `s_g⁻¹(x) ∘ s_h⁻¹(u)`, composable because `x ∈ U₁ ⊆ s(N_g)`; "it has necessarily the form
  `v = t_{g'} s_{g'}⁻¹(u)`" uses that `s` is injective on `N_{g'}`.
* **`Γ` sc-smooth on `G_{x₀} × U`** is read on each sheet `{g} × U`, as in `EpGroupoid.lean`
  (equivalent by `isScSmoothOn_univ_prod_discrete_iff`).
* **Hypotheses.**  `Sheets X x` is inhabited (`exists_sheets`); the hypotheses of `mkRep` are met
  in `exists_naturalRep_sheets`; those of `restrict` by `U' = R.U`.
* The consequences of the data (uniqueness of `(Φ, Γ)`, `Γ` a functor, `G_x ⋉ U` an
  ep-groupoid, pp. 231–233) are not proved here.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### Lemma 7.6.2 (2017: 7.8) -/

/-- **Lemma 7.6.2 (2017: 7.8)**: for open neighbourhoods `N_g ∋ g` (`g ∈ G_x`; the sheets of the proof of
Theorem 7.6.1 (2017: 7.5)) and a neighbourhood `U₀` of `x`, there is an open `U₁ ⊆ U₀` of `x` such that every
morphism `h` with `s(h), t(h) ∈ U₁` belongs to `N_g` for some `g ∈ G_x`. -/
theorem lemma_7_6_2 {x : Obj} {N : X.Isotropy x → Set Mor} (hN : ∀ g, IsOpen (N g))
    (hgN : ∀ g, g.val ∈ N g) {U₀ : Set Obj} (hU₀ : U₀ ∈ 𝓝 x) :
    ∃ U₁, IsOpen U₁ ∧ x ∈ U₁ ∧ U₁ ⊆ U₀ ∧
      ∀ h : Mor, X.src h ∈ U₁ → X.tgt h ∈ U₁ → ∃ g, h ∈ N g := by
  have := X.PObj.metrizableSpace
  have := X.PMor.metrizableSpace
  suffices H : ∃ W ∈ 𝓝 x, ∀ h : Mor, X.src h ∈ W → X.tgt h ∈ W → ∃ g, h ∈ N g by
    obtain ⟨W, hW, hWN⟩ := H
    exact ⟨interior (W ∩ U₀), isOpen_interior, mem_interior_iff_mem_nhds.2 (inter_mem hW hU₀),
      interior_subset.trans inter_subset_right,
      fun h hs ht => hWN h (interior_subset hs).1 (interior_subset ht).1⟩
  -- arguing indirectly: `h_k ∉ ⋃ N_g` with `s(h_k), t(h_k) → x`
  by_contra H
  push Not at H
  obtain ⟨u, hu⟩ := (𝓝 x).exists_antitone_basis
  choose h hs ht hN' using fun n => H (u n) (hu.mem n)
  have hs' : Tendsto (X.src ∘ h) atTop (𝓝 x) := hu.tendsto hs
  have ht' : Tendsto (X.tgt ∘ h) atTop (𝓝 x) := hu.tendsto ht
  -- the properness of Definition 7.1.3 (2017: 7.3) (3) at `x` gives `h_{k_l} → φ₀`
  obtain ⟨V, hVo, hxV, hV⟩ := X.exists_isProperMap x
  have hev : ∀ᶠ n in atTop, X.src (h n) ∈ closure V :=
    (hs'.eventually (hVo.mem_nhds hxV)).mono fun n hn => subset_closure hn
  obtain ⟨φ₀, -, htφ₀, ψ, hψ, hlim⟩ :=
    exists_tendsto_subseq_of_isProperMap_domRestrict_of_eventually hV hev ht'
  -- necessarily `φ₀ ∈ G_x`
  have hsφ₀ : X.src φ₀ = x :=
    tendsto_nhds_unique ((X.continuous_src.tendsto φ₀).comp hlim) (hs'.comp hψ.tendsto_atTop)
  let g₀ : X.Isotropy x := ⟨φ₀, hsφ₀, htφ₀⟩
  obtain ⟨n, hn⟩ := (hlim.eventually ((hN g₀).mem_nhds (hgN g₀))).exists
  exact hN' (ψ n) g₀ hn

namespace NatRepConstruction

/-! ### The choices of the proof of Theorem 7.6.1 (2017: 7.5) -/

/-- `G_x` is finite (Proposition 7.1.12 (2017: 7.4), from Definition 7.1.3 (2017: 7.3) (1) and (3)). -/
theorem finite_isotropy (x : Obj) : Finite (X.Isotropy x) := by
  have hfin := MPolyfold.finite_isotropy_of_isLocalScDiffeo X.isLocalScDiffeo_tgt
    (X.exists_isProperMap x)
  have := hfin.to_subtype
  exact Finite.of_injective (fun g : X.Isotropy x =>
    (⟨g.val, g.src_val, g.tgt_val⟩ : {φ | X.src φ = x ∧ X.tgt φ = x}))
    fun g h hgh => GroupoidStr.Isotropy.ext (congrArg Subtype.val hgh)

/-- **The choices of the proof of Theorem 7.6.1 (2017: 7.5)** (p. 344 (2017 p. 253)): for every `g ∈ G_x` an open
neighbourhood `N_g` of `g`, pairwise disjoint, on which `s` is an sc-diffeomorphism onto the open
set `S g = s(N_g)`, with inverse `σ g = s_g⁻¹`, and on which `t` is an sc-diffeomorphism as
well (`N_g = N^t_g ∩ N^s_g`). -/
structure Sheets (x : Obj) where
  /-- The sheet `N_g ∋ g`. -/
  N : X.Isotropy x → Set Mor
  /-- `s(N_g)`. -/
  S : X.Isotropy x → Set Obj
  /-- `s_g⁻¹ : s(N_g) → N_g`. -/
  σ : X.Isotropy x → Obj → Mor
  mem_N : ∀ g, g.val ∈ N g
  disjoint_N : Pairwise (Disjoint on N)
  isScDiffeoOn_src : ∀ g, X.PMor.IsScDiffeoOn X.PObj X.src (σ g) (N g) (S g)
  isScDiffeoOn_tgt : ∀ g, ∃ (τ : Obj → Mor) (T : Set Obj),
    X.PMor.IsScDiffeoOn X.PObj X.tgt τ (N g) T

/-- The choices of the proof of Theorem 7.6.1 (2017: 7.5) can be made: disjoint open neighbourhoods of the
finitely many `g ∈ G_x` (Hausdorff), shrunk to sheets of `t` and of `s`. -/
theorem exists_sheets (x : Obj) : Nonempty (Sheets X x) := by
  have := finite_isotropy X x
  obtain ⟨D, hD, hdisj⟩ := (Set.finite_range fun g : X.Isotropy x => g.val).t2_separation
  have key : ∀ g : X.Isotropy x, ∃ (N : Set Mor) (S : Set Obj) (σ : Obj → Mor),
      g.val ∈ N ∧ N ⊆ D g.val ∧ X.PMor.IsScDiffeoOn X.PObj X.src σ N S ∧
      ∃ (τ : Obj → Mor) (T : Set Obj), X.PMor.IsScDiffeoOn X.PObj X.tgt τ N T := by
    intro g
    obtain ⟨Wt, Vt, τ, hgt, hdt⟩ := X.isLocalScDiffeo_tgt g.val
    obtain ⟨N, S, σ, hgN, hNsub, hds⟩ := X.isLocalScDiffeo_src.exists_isScDiffeoOn_subset
      ((hD g.val).2.inter hdt.isOpen_source) ⟨(hD g.val).1, hgt⟩
    exact ⟨N, S, σ, hgN, fun φ hφ => (hNsub hφ).1, hds, τ, _,
      hdt.restrict hds.isOpen_source fun φ hφ => (hNsub hφ).2⟩
  choose N S σ hgN hNsub hds htd using key
  refine ⟨⟨N, S, σ, hgN, fun g g' hne => ?_, hds, htd⟩⟩
  exact Disjoint.mono (hNsub g) (hNsub g') (hdisj (mem_range_self g) (mem_range_self g')
    fun h => hne (GroupoidStr.Isotropy.ext h))

namespace Sheets

variable {X} {x : Obj} (D : Sheets X x)

/-- `t_g ∘ s_g⁻¹`, the map `Φ(g)` of Theorem 7.6.1 (2017: 7.5). -/
def hat (g : X.Isotropy x) : Obj → Obj := fun y => X.tgt (D.σ g y)

/-- `U = ⋃_g t_g s_g⁻¹(U₂)` (Lemma 7.6.3 (2017: 7.9)). -/
def unionHat (U₂ : Set Obj) : Set Obj := ⋃ g, D.hat g '' U₂

theorem hat_apply (g : X.Isotropy x) (y : Obj) : D.hat g y = X.tgt (D.σ g y) := rfl

theorem isOpen_N (g : X.Isotropy x) : IsOpen (D.N g) := (D.isScDiffeoOn_src g).isOpen_source

theorem isOpen_S (g : X.Isotropy x) : IsOpen (D.S g) := (D.isScDiffeoOn_src g).isOpen_target

theorem mem_S (g : X.Isotropy x) : x ∈ D.S g := by
  have := (D.isScDiffeoOn_src g).mapsTo (D.mem_N g)
  rwa [g.src_val] at this

/-- `s_g⁻¹(x) = g`. -/
theorem σ_self (g : X.Isotropy x) : D.σ g x = g.val := by
  have := (D.isScDiffeoOn_src g).left_inv _ (D.mem_N g)
  rwa [g.src_val] at this

theorem src_σ (g : X.Isotropy x) {y : Obj} (hy : y ∈ D.S g) : X.src (D.σ g y) = y :=
  (D.isScDiffeoOn_src g).right_inv y hy

theorem σ_mem_N (g : X.Isotropy x) {y : Obj} (hy : y ∈ D.S g) : D.σ g y ∈ D.N g :=
  (D.isScDiffeoOn_src g).mapsTo_inv hy

theorem σ_src (g : X.Isotropy x) {φ : Mor} (hφ : φ ∈ D.N g) : D.σ g (X.src φ) = φ :=
  (D.isScDiffeoOn_src g).left_inv φ hφ

/-- `t_g s_g⁻¹(x) = x`. -/
theorem hat_self (g : X.Isotropy x) : D.hat g x = x := by
  rw [hat_apply, D.σ_self]
  exact g.tgt_val

theorem continuousOn_σ (g : X.Isotropy x) : ContinuousOn (D.σ g) (D.S g) :=
  (D.isScDiffeoOn_src g).isScSmoothOn_inv.continuousOn

theorem continuousOn_hat (g : X.Isotropy x) : ContinuousOn (D.hat g) (D.S g) :=
  X.continuous_tgt.comp_continuousOn (D.continuousOn_σ g)

/-- The sheets are disjoint. -/
theorem eq_of_mem_N {g g' : X.Isotropy x} {φ : Mor} (h : φ ∈ D.N g) (h' : φ ∈ D.N g') :
    g = g' := by
  by_contra hne
  exact Set.disjoint_left.1 (D.disjoint_N hne) h h'

/-- `s_g⁻¹(A) = N_g ∩ s⁻¹(A)` for `A ⊆ s(N_g)`. -/
theorem image_σ (g : X.Isotropy x) {A : Set Obj} (hA : A ⊆ D.S g) :
    D.σ g '' A = D.N g ∩ X.src ⁻¹' A := by
  ext φ
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨D.σ_mem_N g (hA hy), by rw [mem_preimage, D.src_σ g (hA hy)]; exact hy⟩
  · rintro ⟨hφ, hφA⟩
    exact ⟨X.src φ, hφA, D.σ_src g hφ⟩

/-- `t_g s_g⁻¹(A)` is open for open `A ⊆ s(N_g)` (`t` is an open map). -/
theorem isOpen_image_hat (g : X.Isotropy x) {A : Set Obj} (hA : IsOpen A) (hAS : A ⊆ D.S g) :
    IsOpen (D.hat g '' A) := by
  have : D.hat g '' A = X.tgt '' (D.σ g '' A) := by
    rw [image_image]
    rfl
  rw [this, D.image_σ g hAS]
  exact X.isLocalScDiffeo_tgt.isOpenMap _ ((D.isOpen_N g).inter (hA.preimage X.continuous_src))

theorem isScSmoothOn_hat (g : X.Isotropy x) {U : Set Obj} (hU : IsOpen U) (hUS : U ⊆ D.S g) :
    X.PObj.IsScSmoothOn X.PObj (D.hat g) U :=
  MPolyfold.IsScSmoothOn.comp X.isScSmoothMap_tgt
    ((D.isScDiffeoOn_src g).isScSmoothOn_inv.mono hU hUS) (mapsTo_univ _ _)

/-! #### The set `U = ⋃_g t_g s_g⁻¹(U₂)` -/

theorem mem_unionHat_iff {U₂ : Set Obj} {y : Obj} :
    y ∈ D.unionHat U₂ ↔ ∃ g, ∃ u ∈ U₂, D.hat g u = y := by
  simp only [unionHat, mem_iUnion, mem_image]

theorem mem_unionHat {U₂ : Set Obj} (hx : x ∈ U₂) : x ∈ D.unionHat U₂ :=
  mem_iUnion.2 ⟨1, x, hx, D.hat_self 1⟩

/-- `U` is open. -/
theorem isOpen_unionHat {U₂ : Set Obj} (hU₂ : IsOpen U₂) (hU₂S : ∀ g, U₂ ⊆ D.S g) :
    IsOpen (D.unionHat U₂) :=
  isOpen_iUnion fun g => D.isOpen_image_hat g hU₂ (hU₂S g)

/-- `U` is connected if `U₂ ∋ x` is: a union of connected sets through `x = t_g s_g⁻¹(x)`. -/
theorem isConnected_unionHat {U₂ : Set Obj} (hU₂ : IsConnected U₂) (hx : x ∈ U₂)
    (hU₂S : ∀ g, U₂ ⊆ D.S g) : IsConnected (D.unionHat U₂) :=
  ⟨⟨x, D.mem_unionHat hx⟩, isPreconnected_iUnion
    ⟨x, mem_iInter.2 fun g => ⟨x, hx, D.hat_self g⟩⟩
    fun g => (hU₂.image _ ((D.continuousOn_hat g).mono (hU₂S g))).isPreconnected⟩

/-! #### `Φ` is a homomorphism on a connected invariant `U` -/

section Connected

variable {U : Set Obj} (hUc : IsPreconnected U) (hxU : x ∈ U) (hUS : ∀ g, U ⊆ D.S g)
include hUc hxU hUS

/-- `s_1⁻¹` is the unit section `u` on a connected `U` (both sections of `s` through `1_x`). -/
theorem eqOn_σ_one : EqOn (D.σ 1) X.unit U :=
  eqOn_sections_of_isPreconnected X.isLocalScDiffeo_src.isLocallyInjective hUc
    ((D.continuousOn_σ 1).mono (hUS 1)) X.continuous_unit.continuousOn
    (fun _ hy => D.src_σ 1 (hUS 1 hy)) (fun _ _ => X.src_unit _) hxU (D.σ_self 1)

/-- `Φ(1) = id` on a connected `U`. -/
theorem hat_one {y : Obj} (hy : y ∈ U) : D.hat 1 y = y := by
  rw [hat_apply, D.eqOn_σ_one hUc hxU hUS hy, X.tgt_unit]

variable (hinv : ∀ g, MapsTo (D.hat g) U U)
include hinv

/-- `s_{gh}⁻¹(y) = s_g⁻¹(Φ(h) y) ∘ s_h⁻¹(y)` on a connected invariant `U`: both sides are
continuous sections of `s` (the continuity of `m`, Definition 7.1.3 (2017: 7.3) (4)) through `g ∘ h`. -/
theorem eqOn_σ_mul (g h : X.Isotropy x) :
    EqOn (D.σ (g * h)) (fun y => X.comp (D.σ g (D.hat h y)) (D.σ h y)) U := by
  have hF :=
    (X.isScSmoothCompSheet (D.σ g) (D.N g) (D.S g) (D.isScDiffeoOn_src g)).continuousOn
  have h2 : ContinuousOn (fun y => X.comp (D.σ g (D.hat h y)) (D.σ h y)) U :=
    hF.comp ((D.continuousOn_σ h).mono (hUS h)) fun y hy => hUS g (hinv h hy)
  refine eqOn_sections_of_isPreconnected X.isLocalScDiffeo_src.isLocallyInjective hUc
    ((D.continuousOn_σ (g * h)).mono (hUS _)) h2 (fun y hy => D.src_σ _ (hUS _ hy))
    (fun y hy => ?_) hxU ?_
  · have hc : X.src (D.σ g (D.hat h y)) = X.tgt (D.σ h y) := D.src_σ g (hUS g (hinv h hy))
    rw [X.src_comp _ _ hc, D.src_σ h (hUS h hy)]
  · rw [D.hat_self, D.σ_self, D.σ_self, D.σ_self]
    rfl

/-- **`Φ` is a homomorphism**: `Φ(gh) = Φ(g) ∘ Φ(h)` on a connected invariant `U`. -/
theorem hat_mul (g h : X.Isotropy x) {y : Obj} (hy : y ∈ U) :
    D.hat (g * h) y = D.hat g (D.hat h y) := by
  have hc : X.src (D.σ g (D.hat h y)) = X.tgt (D.σ h y) := D.src_σ g (hUS g (hinv h hy))
  rw [hat_apply, D.eqOn_σ_mul hUc hxU hUS hinv g h hy]
  exact X.tgt_comp _ _ hc

/-- `Φ(g) ∈ Diff_sc(U)`, with inverse `Φ(g⁻¹)`. -/
theorem isScDiffeoOn_hat (hUo : IsOpen U) (g : X.Isotropy x) :
    X.PObj.IsScDiffeoOn X.PObj (D.hat g) (D.hat g⁻¹) U U where
  isScSmoothOn := D.isScSmoothOn_hat g hUo (hUS g)
  isScSmoothOn_inv := D.isScSmoothOn_hat g⁻¹ hUo (hUS g⁻¹)
  mapsTo := hinv g
  mapsTo_inv := hinv g⁻¹
  left_inv y hy := by
    rw [← D.hat_mul hUc hxU hUS hinv g⁻¹ g hy, inv_mul_cancel, D.hat_one hUc hxU hUS hy]
  right_inv y hy := by
    rw [← D.hat_mul hUc hxU hUS hinv g g⁻¹ hy, mul_inv_cancel, D.hat_one hUc hxU hUS hy]

end Connected

/-- **The natural representation built from the sheets** on an open connected `U ∋ x` inside
every `s(N_g)`, invariant under every `t_g s_g⁻¹` and with the property of Lemma 7.6.2 (2017: 7.8):
`Φ(g) = t_g ∘ s_g⁻¹`, `Γ(g, y) = s_g⁻¹(y)`. -/
def mkRep (U : Set Obj) (hUo : IsOpen U) (hUc : IsConnected U) (hxU : x ∈ U)
    (hUS : ∀ g, U ⊆ D.S g) (hinv : ∀ g, MapsTo (D.hat g) U U)
    (h78 : ∀ h : Mor, X.src h ∈ U → X.tgt h ∈ U → ∃ g, h ∈ D.N g) : X.NaturalRep x where
  U := U
  isOpen_U := hUo
  isConnected_U := hUc
  mem_U := hxU
  Φ := D.hat
  Γ := D.σ
  isScDiffeoOn_Φ := D.isScDiffeoOn_hat hUc.isPreconnected hxU hUS hinv hUo
  Φ_mul g h y hy := D.hat_mul hUc.isPreconnected hxU hUS hinv g h hy
  isScSmoothOn_Γ g := (D.isScDiffeoOn_src g).isScSmoothOn_inv.mono hUo (hUS g)
  Γ_self := D.σ_self
  src_Γ g y hy := D.src_σ g (hUS g hy)
  tgt_Γ _ _ _ := rfl
  existsUnique_Γ h hs ht := by
    obtain ⟨g, hg⟩ := h78 h hs ht
    refine ⟨g, D.σ_src g hg, fun g' hg' => D.eq_of_mem_N ?_ hg⟩
    rw [← hg']
    exact D.σ_mem_N g' (hUS g' hs)

end Sheets

end NatRepConstruction

/-! ### Lemma 7.6.3 (2017: 7.9) -/

/-- **Lemma 7.6.3 (2017: 7.9)**: if `U₁ ⊆ ⋂_g s(N_g)` is an open neighbourhood of `x` as in Lemma 7.6.2 (2017: 7.8), there is
an open neighbourhood `U₂ ⊆ U₁` of `x`, which may be taken connected, such that
`U = ⋃_g t_g s_g⁻¹(U₂)` is contained in `U₁` and invariant under all the maps `t_g ∘ s_g⁻¹`. -/
theorem lemma_7_6_3 {x : Obj} (D : NatRepConstruction.Sheets X x) {U₁ : Set Obj}
    (hU₁ : IsOpen U₁) (hxU₁ : x ∈ U₁) (hU₁S : ∀ g, U₁ ⊆ D.S g)
    (h78 : ∀ h : Mor, X.src h ∈ U₁ → X.tgt h ∈ U₁ → ∃ g, h ∈ D.N g) :
    ∃ U₂, IsOpen U₂ ∧ IsConnected U₂ ∧ x ∈ U₂ ∧ U₂ ⊆ U₁ ∧ D.unionHat U₂ ⊆ U₁ ∧
      ∀ g, MapsTo (D.hat g) (D.unionHat U₂) (D.unionHat U₂) := by
  have := NatRepConstruction.finite_isotropy X x
  -- `U₂` so small that `t_h s_h⁻¹(U₂)` and `t_g s_g⁻¹ t_h s_h⁻¹(U₂)` lie in `U₁`
  have hcont : ∀ g, ContinuousAt (D.hat g) x := fun g =>
    (D.continuousOn_hat g).continuousAt ((D.isOpen_S g).mem_nhds (D.mem_S g))
  have hU₁n : U₁ ∈ 𝓝 x := hU₁.mem_nhds hxU₁
  have h1 : ∀ h, D.hat h ⁻¹' U₁ ∈ 𝓝 x := fun h =>
    (hcont h).preimage_mem_nhds (by rw [D.hat_self]; exact hU₁n)
  have h2 : ∀ g h, (D.hat g ∘ D.hat h) ⁻¹' U₁ ∈ 𝓝 x := fun g h =>
    ((hcont g).comp_of_eq (hcont h) (D.hat_self h)).preimage_mem_nhds
      (by rw [comp_apply, D.hat_self, D.hat_self]; exact hU₁n)
  have hA : U₁ ∩ (⋂ h, D.hat h ⁻¹' U₁) ∩ ⋂ g, ⋂ h, (D.hat g ∘ D.hat h) ⁻¹' U₁ ∈ 𝓝 x :=
    inter_mem (inter_mem hU₁n (iInter_mem.2 h1)) (iInter_mem.2 fun g => iInter_mem.2 (h2 g))
  obtain ⟨U₂, hU₂o, hxU₂, hU₂A, hU₂c⟩ := X.PObj.exists_isOpen_isConnected_subset hA
  have hU₂U₁ : U₂ ⊆ U₁ := fun y hy => (hU₂A hy).1.1
  refine ⟨U₂, hU₂o, hU₂c, hxU₂, hU₂U₁, fun y hy => ?_, fun g y hy => ?_⟩
  · obtain ⟨h, u, hu, rfl⟩ := D.mem_unionHat_iff.1 hy
    exact mem_iInter.1 (hU₂A hu).1.2 h
  · -- `y = t_h s_h⁻¹(u)`, `v = t_g s_g⁻¹(y)`, and the morphism `s_g⁻¹(y) ∘ s_h⁻¹(u) : u → v`
    obtain ⟨h, u, hu, rfl⟩ := D.mem_unionHat_iff.1 hy
    have huA := hU₂A hu
    have hyU₁ : D.hat h u ∈ U₁ := mem_iInter.1 huA.1.2 h
    have hvU₁ : D.hat g (D.hat h u) ∈ U₁ := mem_iInter.1 (mem_iInter.1 huA.2 g) h
    have huS : u ∈ D.S h := hU₁S h (hU₂U₁ hu)
    have hc : X.src (D.σ g (D.hat h u)) = X.tgt (D.σ h u) := D.src_σ g (hU₁S g hyU₁)
    have hsk : X.src (X.comp (D.σ g (D.hat h u)) (D.σ h u)) = u := by
      rw [X.src_comp _ _ hc, D.src_σ h huS]
    have htk : X.tgt (X.comp (D.σ g (D.hat h u)) (D.σ h u)) = D.hat g (D.hat h u) :=
      X.tgt_comp _ _ hc
    -- by Lemma 7.6.2 (2017: 7.8) the morphism lies in some `N_{g'}`, so it is `s_{g'}⁻¹(u)`
    obtain ⟨g', hg'⟩ := h78 _ (by rw [hsk]; exact hU₂U₁ hu) (by rw [htk]; exact hvU₁)
    have hσ := D.σ_src g' hg'
    rw [hsk] at hσ
    refine D.mem_unionHat_iff.2 ⟨g', u, hu, ?_⟩
    rw [D.hat_apply, hσ, htk]

/-! ### Theorems 7.1.13 and 7.6.1 (2017: 7.1 and 7.5) -/

namespace NatRepConstruction

/-- **Theorem 7.6.1 (2017: 7.5), in the form of its proof** (pp. 253–254): for an open `V ∋ x` there are
sheets `N_g` and a natural representation on `U ⊆ V ∩ ⋂_g s(N_g)` with `Φ(g) = t_g ∘ s_g⁻¹`
and `Γ(g, ·) = s_g⁻¹`. -/
theorem exists_naturalRep_sheets (x : Obj) {V : Set Obj} (hV : IsOpen V) (hx : x ∈ V) :
    ∃ (D : Sheets X x) (R : X.NaturalRep x), R.U ⊆ V ∧ (∀ g, R.U ⊆ D.S g) ∧
      R.Φ = D.hat ∧ R.Γ = D.σ := by
  have := finite_isotropy X x
  obtain ⟨D⟩ := exists_sheets X x
  -- `U₀ = V ∩ ⋂_g s(N_g)`, `U₁` by Lemma 7.6.2 (2017: 7.8), `U₂` by Lemma 7.6.3 (2017: 7.9)
  have hU₀ : V ∩ ⋂ g, D.S g ∈ 𝓝 x :=
    inter_mem (hV.mem_nhds hx) (iInter_mem.2 fun g => (D.isOpen_S g).mem_nhds (D.mem_S g))
  obtain ⟨U₁, hU₁o, hxU₁, hU₁U₀, h78⟩ := X.lemma_7_6_2 D.isOpen_N D.mem_N hU₀
  have hU₁S : ∀ g, U₁ ⊆ D.S g := fun g y hy => mem_iInter.1 (hU₁U₀ hy).2 g
  obtain ⟨U₂, hU₂o, hU₂c, hxU₂, hU₂U₁, hUU₁, hinv⟩ := X.lemma_7_6_3 D hU₁o hxU₁ hU₁S h78
  have hU₂S : ∀ g, U₂ ⊆ D.S g := fun g => hU₂U₁.trans (hU₁S g)
  have hUS : ∀ g, D.unionHat U₂ ⊆ D.S g := fun g => hUU₁.trans (hU₁S g)
  refine ⟨D, D.mkRep _ (D.isOpen_unionHat hU₂o hU₂S) (D.isConnected_unionHat hU₂c hxU₂ hU₂S)
    (D.mem_unionHat hxU₂) hUS hinv fun h hs ht => h78 h (hUU₁ hs) (hUU₁ ht),
    fun y hy => (hU₁U₀ (hUU₁ hy)).1, hUS, rfl, rfl⟩

/-- **The restriction of a natural representation** to a smaller open connected neighbourhood
`U' ⊆ U` of `x` invariant under all `Φ(g)`, with the same `Φ` and `Γ`. -/
def restrict {x : Obj} (R : X.NaturalRep x) (U' : Set Obj) (hU'o : IsOpen U')
    (hU'c : IsConnected U') (hxU' : x ∈ U') (hU'U : U' ⊆ R.U)
    (hinv : ∀ g, MapsTo (R.Φ g) U' U') : X.NaturalRep x where
  U := U'
  isOpen_U := hU'o
  isConnected_U := hU'c
  mem_U := hxU'
  Φ := R.Φ
  Γ := R.Γ
  isScDiffeoOn_Φ g :=
    { isScSmoothOn := (R.isScDiffeoOn_Φ g).isScSmoothOn.mono hU'o hU'U
      isScSmoothOn_inv := (R.isScDiffeoOn_Φ g).isScSmoothOn_inv.mono hU'o hU'U
      mapsTo := hinv g
      mapsTo_inv := hinv g⁻¹
      left_inv := fun y hy => (R.isScDiffeoOn_Φ g).left_inv y (hU'U hy)
      right_inv := fun y hy => (R.isScDiffeoOn_Φ g).right_inv y (hU'U hy) }
  Φ_mul g h y hy := R.Φ_mul g h y (hU'U hy)
  isScSmoothOn_Γ g := (R.isScSmoothOn_Γ g).mono hU'o hU'U
  Γ_self := R.Γ_self
  src_Γ g y hy := R.src_Γ g y (hU'U hy)
  tgt_Γ g y hy := R.tgt_Γ g y (hU'U hy)
  existsUnique_Γ h hs ht := R.existsUnique_Γ h (hU'U hs) (hU'U ht)

end NatRepConstruction

/-- **Theorem 7.1.13 (2017: 7.1) (natural representation of `G_x`)**: for every open neighbourhood `V` of `x`
there is a natural representation `(Φ, Γ)` of `G_x` on an open connected neighbourhood
`U ⊆ V` of `x`. -/
theorem theorem_7_1_13 (x : Obj) {V : Set Obj} (hV : IsOpen V) (hx : x ∈ V) :
    ∃ R : X.NaturalRep x, R.U ⊆ V := by
  obtain ⟨-, R, hRV, -⟩ := NatRepConstruction.exists_naturalRep_sheets X x hV hx
  exact ⟨R, hRV⟩

/-- **Theorem 7.6.1 (2017: 7.5)** (p. 344 (2017 p. 253)) is a restatement of Theorem 7.1.13 (2017: 7.1), given in Appendix 7.5.1 with its
proof; the form `Φ(g) = t_g ∘ s_g⁻¹` of the proof is
`NatRepConstruction.exists_naturalRep_sheets`. -/
theorem theorem_7_6_1 (x : Obj) {V : Set Obj} (hV : IsOpen V) (hx : x ∈ V) :
    ∃ R : X.NaturalRep x, R.U ⊆ V :=
  theorem_7_1_13 X x hV hx

/-! ### Smaller neighbourhoods -/

/-- A natural representation restricts, with the same `Φ` and `Γ`, to every smaller open
connected neighbourhood `U' ⊆ U` of `x` invariant under all `Φ(g)`. -/
theorem exists_naturalRep_restrict {x : Obj} (R : X.NaturalRep x) {U' : Set Obj}
    (hU'o : IsOpen U') (hU'c : IsConnected U') (hxU' : x ∈ U') (hU'U : U' ⊆ R.U)
    (hinv : ∀ g, MapsTo (R.Φ g) U' U') :
    ∃ R' : X.NaturalRep x, R'.U = U' ∧ R'.Φ = R.Φ ∧ R'.Γ = R.Γ :=
  ⟨NatRepConstruction.restrict X R U' hU'o hU'c hxU' hU'U hinv, rfl, rfl, rfl⟩

/-- **A natural representation shrinks into every open `V ∋ x`**, with the same `Φ` and `Γ`:
on the connected component of `x` in the invariant open set `{y ∈ U | Φ(g) y ∈ V ∀ g}`. -/
theorem exists_naturalRep_shrink {x : Obj} (R : X.NaturalRep x) {V : Set Obj} (hV : IsOpen V)
    (hx : x ∈ V) : ∃ R' : X.NaturalRep x, R'.U ⊆ V ∩ R.U ∧ R'.Φ = R.Φ ∧ R'.Γ = R.Γ := by
  have := NatRepConstruction.finite_isotropy X x
  set W := ⋂ g, R.U ∩ R.Φ g ⁻¹' V
  have hWo : IsOpen W := isOpen_iInter_of_finite fun g =>
    (R.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn.isOpen_inter_preimage R.isOpen_U hV
  have hxW : x ∈ W := mem_iInter.2 fun g => ⟨R.mem_U, by rw [mem_preimage, R.Φ_self]; exact hx⟩
  have hWU : W ⊆ R.U := fun y hy => (mem_iInter.1 hy 1).1
  have hWV : W ⊆ V := fun y hy => by
    have h1 := (mem_iInter.1 hy 1).2
    rwa [mem_preimage, R.Φ_one y (hWU hy)] at h1
  have hWinv : ∀ g, MapsTo (R.Φ g) W W := fun g y hy => mem_iInter.2 fun h =>
    ⟨R.mapsTo_Φ g (hWU hy), by
      rw [mem_preimage, ← R.Φ_mul h g y (hWU hy)]
      exact (mem_iInter.1 hy (h * g)).2⟩
  -- the connected component of `x` in `W` is open and invariant
  set C := connectedComponentIn W x
  have hCW : C ⊆ W := connectedComponentIn_subset W x
  have hCinv : ∀ g, MapsTo (R.Φ g) C C := fun g y hy => by
    have hpre : IsPreconnected (R.Φ g '' C) :=
      isPreconnected_connectedComponentIn.image _
        ((R.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn.mono (hCW.trans hWU))
    exact hpre.subset_connectedComponentIn ⟨x, mem_connectedComponentIn hxW, R.Φ_self g⟩
      ((hWinv g).mono_left hCW).image_subset ⟨y, hy, rfl⟩
  obtain ⟨R', hR'U, hR'Φ, hR'Γ⟩ := X.exists_naturalRep_restrict R
    (X.PObj.isOpen_connectedComponentIn hWo x) (isConnected_connectedComponentIn_iff.2 hxW)
    (mem_connectedComponentIn hxW) (hCW.trans hWU) hCinv
  exact ⟨R', by rw [hR'U]; exact fun y hy => ⟨hWV (hCW hy), hWU (hCW hy)⟩, hR'Φ, hR'Γ⟩

end EpGroupoid

end Polyfold
