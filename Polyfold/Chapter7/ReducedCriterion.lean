import Polyfold.Chapter7.ReducedNotHausdorff
import Polyfold.Chapter7.Lift

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §7.2 "Effective and Reduced Ep-Groupoids" (pp. 307–323; 2017: pp. 239–244), the items
rewritten or new in the 2021 edition: **Definition 7.2.5** (p. 310), **Lemma 7.2.6** (p. 310),
**Remark 7.2.8** (p. 311), **Lemma 7.2.11** (p. 315), **Propositions 7.2.12, 7.2.13** and
**Theorem 7.2.14** (pp. 317–318; 2017: Proposition 7.10), **Proposition 7.2.17** (p. 320),
**Definition 7.2.18** (= Definition 7.4.1), **Remarks 7.2.19, 7.2.20**, **Proposition 7.2.21**
(p. 321), **Theorem 7.2.22** and **Proposition 7.2.23** (p. 323); Appendix **7.6.3** (p. 348) and
Appendix **7.6.4**, **Theorem 7.6.7** and **Corollary 7.6.8** (pp. 348–351).  Numbers and pages
are the 2021 text's, the 2017 ones in parentheses.

# The reduced ep-groupoid: the Hausdorff criterion and LUC

## The text, paraphrased

(Definition 7.2.5, p. 310 (2017: p. 241)) `T_x ⊆ G_x` is the normal subgroup of the elements
acting trivially on some small `W(x) ⊆ U(x)`, maximal with this property; it does not depend on
`U(x)`.  (Lemma 7.2.6, p. 310) For `φ : x → y`, `g ↦ φ ∘ g ∘ φ⁻¹` maps `T_x` bijectively onto
`T_y`.  (Definition 7.2.7, p. 310 (2017: Definition 7.12)) `𝐗^T`, `φ ∼ φ'`, `𝐗^R` and the
groupoid `(X, 𝐗^R)`.  (Remark 7.2.8, p. 311) `T_R` is the finest topology making `π : 𝐗 → 𝐗^R`
continuous; if `T_R` is Hausdorff, `(X, 𝐗^R)` is naturally an ep-groupoid, and Appendix 7.6.3 gives
an example where it is not.  (Lemma 7.2.9, p. 311) `π` is open and a homeomorphism on sheets of
`s`.  (Proposition 7.2.10, p. 313 (2017: Proposition 7.9)) the natural charts.  (Lemma 7.2.11,
p. 315) If `φ₁, …, φ_k` are the other members of the class of `φ₀`, there are open `U(φᵢ)` and
`U([φ₀])` with (1) disjoint closures, (2) `π : U(φᵢ) → U([φ₀])` homeomorphisms, (3) every `ψ`
with `[ψ] ∈ U([φ₀])` in some `U(φᵢ)`.  (Proposition 7.2.12, p. 317) `(𝐗^R, T_R)` is
paracompact; a footnote recalls that paracompactness does not include Hausdorffness.
(Proposition 7.2.13, p. 318) The natural charts give an M-polyfold structure on `(𝐗^R, T_R)` iff
`T_R` is Hausdorff.  (Theorem 7.2.14, p. 318 (2017: Proposition 7.10)) If `T_R` is Hausdorff,
`(X, 𝐗^R)` is naturally an ep-groupoid.  (Definition 7.2.15, Proposition 7.2.16, p. 319 (2017:
Definition 7.13, Proposition 7.10)) `G_x/T_x`; `X_R` is effective.  (Proposition 7.2.17, p. 320)
`T_R` is Hausdorff iff `𝐗^T` is closed in `𝐗`.  (Definition 7.2.18, p. 321) LUC: every `x` has a
`U(x)` with the natural `G_x`-action such that `ĝ` is the identity on `U(x)` once it is the
identity on a nonempty open `V ⊆ U(x)`.  (Remark 7.2.19) Not every ep-groupoid has LUC
(Appendix 7.6.3).  (Remark 7.2.20) `U(x)` can be taken inside any given `O(x)`.
(Proposition 7.2.21) LUC iff `𝐗^T` is closed.  (Theorem 7.2.22, p. 323) `T_R` Hausdorff, LUC and
`𝐗^T` closed are equivalent.  (Proposition 7.2.23) Under LUC, `X_R` is well defined.

(Appendix 7.6.3, p. 348) Zhou's example: `ℤ/2` acting on the retract of Subsection 1.4.4 by
`(s, f) ↦ (s, −f)`; `cl(𝐗^T) ∖ 𝐗^T` is one point, so `T_R` is not Hausdorff and LUC fails.
(Appendix 7.6.4, pp. 348–351) Under (SLUC) (every `X^i` has LUC): `(𝐗^T)^1 ⊆ (𝐗^1)^T` (7.24);
conversely, for `g ∈ T_x^{X¹}` the map `ĝ` is the identity on the connected `U₁(x) = U(x) ∩ X_1`
by LUC for `X¹`, hence on `U(x)` by the density of `U₁(x)` in `U(x)`; so `(𝐗^T)^1 = (𝐗^1)^T`,
`(𝐗^1)^R = (𝐗^R)^1` as sets, and the identification is an sc-diffeomorphism (Theorem 7.6.7, also
for every `i`).  (Corollary 7.6.8) The same under (ZHOU), which implies (SLUC).

## What is formalized (namespace `Polyfold.EpGroupoid`)

* **Definition 7.2.18** (early in the file, for §7.4): `NaturalRep.HasLUC`, `IsLUC`; witnesses
  `isLUC_trivial`, `isLUC_of_isEffective`, `Examples.isLUC_trivialZ3` (not effective),
  `Examples.isLUC_reflection`; `isLUC_iff_forall_naturalRep` (LUC for one natural
  representation at each `x` gives it for all, via `NaturalRep.hasLUC_of_isClosed`).
* **Definition 7.2.5**: `NaturalRep.kerOn` (`T_x^V`), `definition_7_2_5`.
  **Lemma 7.2.6**: `lemma_7_2_6`, `trivialSubgroupEquiv`.  **Remark 7.2.8**:
  `remark_7_2_8`.
* **Proposition 7.2.12**: `paracompactSpace_of_isOpenMap`,
  `exists_isCompact_preimage_reducedπ_subset`, the instance `paracompactSpace_reducedMor`,
  `proposition_7_2_12`.  **Proposition 7.2.13**: `proposition_7_2_13`.
  **Theorem 7.2.14**: `theorem_7_2_14`.
* **Proposition 7.2.17**: `reducedπ_eq_iff_comp_inv`, `mem_nonEffectivePart_iff_reducedπ`,
  `isClosed_reducedπ_eq_of_isClosed`, `isClosed_nonEffectivePart_of_t2Space`,
  `proposition_7_2_17`.
* **Proposition 7.2.21**: `isClosed_nonEffectivePart_of_isLUC`, `proposition_7_2_21`;
  **Remark 7.2.20**: `remark_7_2_20`; **Theorem 7.2.22**: `theorem_7_2_22`;
  **Proposition 7.2.23**: `proposition_7_2_23`.
* **Lemma 7.2.11**: `IsReducedEvenlyCovered` (its conclusion), `finite_reducedπ_preimage`,
  `lemma_7_2_11` (with `T_R` Hausdorff), `isReducedEvenlyCovered_iff_t2Space`.
* **Appendix 7.6.3, Remark 7.2.19** (for `JumpingRetract.X` of `ReducedNotHausdorff.lean`, our
  analogue of Zhou's example): `JumpingRetract.not_isClosed_nonEffectivePart`,
  `JumpingRetract.not_isLUC`, `Examples.remark_7_2_19`;
  `JumpingRetract.not_isReducedEvenlyCovered`.
* **Appendix 7.6.4**: `mem_nonEffectivePart_liftOne_of_levelVal` ((7.24)),
  `levelVal_mem_nonEffectivePart_of_liftOne` (`T_x^{X¹} ⊆ T_x`), `nonEffectivePart_liftOne_eq`,
  `liftOne_reducedπ_eq_iff`, `reducedLevelOneMap`, `theorem_7_6_7`,
  `corollary_7_6_8`; witness `Examples.theorem_7_6_7_point`.

Already covered elsewhere: Definition 7.2.1 (`IsEffective`, `IsRegular`, `regularSet`), Lemma
7.2.2 (`lemma_7_2_2`), Lemma 7.2.3 (`lemma_7_2_3`), Proposition 7.2.4 (`proposition_7_2_4`), the
intrinsic `T_x` (`trivialSubgroup`, `Effective.lean`), Definition 7.2.7 (`nonEffectivePart`,
`ReducedRel`, `reducedGroupoidStr`), Lemma 7.2.9 (`isOpenMap_reducedπ`,
`isOpenEmbedding_domRestrict_reducedπ`), Proposition 7.2.10 (`reducedAtlas`), Definition 7.2.15
(`EffIsotropy`, `effIsotropyEquivReduced`), Proposition 7.2.16 (`isEffective_reducedEpGroupoid`),
in `Groupoid.lean`, `EpGroupoid.lean`, `Effective.lean` and `Reduced.lean`.

## What the text leaves implicit, and the choices made

* **Paracompactness of `T_R` holds for every ep-groupoid** (Proposition 7.2.12) and is proved
  without the text's refinement argument: `π` is open, and for `q ∈ 𝐗^R` the compact set
  `K = {φ ∈ s⁻¹(cl V) | (s, t)(φ) = (s, t)(q)}` (`(s, t)` is proper on `s⁻¹(cl V)`) has the
  property that every open `N ⊇ K` contains `π⁻¹(O)` for an open `O ∋ q`.  So the instance
  `ParacompactSpace X.ReducedMor` holds outright, and `reducedEpGroupoid` (`Reduced.lean`) now
  needs only `[T2Space X.ReducedMor]`; this settles the paracompactness half of gap G.71.
* **Lemma 7.2.11 does not hold as we read it without a Hausdorff hypothesis.**  Its conclusion at
  every morphism is equivalent to `T_R` Hausdorff (`isReducedEvenlyCovered_iff_t2Space`), and it
  fails at `(1, o₀)` in `JumpingRetract.X`.  The proof of (3) uses the uniqueness of limits in
  `T_R`.  We prove it under `[T2Space X.ReducedMor]`, the setting of Theorem 7.2.14 where it is
  used.  "Homeomorphism onto `U([φ₀])`" is read as: `π(U(φ)) = U([φ₀])` and `π` restricted to
  `U(φ)` is an open embedding.
* Proposition 7.2.17 is proved via the closedness of the relation `[φ] = [ψ]` in `𝐗 × 𝐗` for the
  open quotient map `π` (Mathlib's `t2Space_iff_of_isOpenQuotientMap`), without properness.
* Proposition 7.2.21 is proved by a connectedness argument, giving more: if `𝐗^T` is closed,
  **every** natural representation has the property of Definition 7.2.18
  (`NaturalRep.hasLUC_of_isClosed`; compare 2021 Proposition 7.4.2 and Remark 7.4.3).
* Definition 7.2.5 is read through `NaturalRep.kerOn`: `T_x` contains `T_x^W` for every open
  `W ∋ x` and equals it for every small `W`; the intrinsic `T_x` is `trivialSubgroup`.
* Proposition 7.2.13: an M-polyfold is Hausdorff and paracompact by definition; the statement is
  the equivalence of "some M-polyfold structure with the natural atlas exists" and `T_R`
  Hausdorff.  Remark 7.2.8's "finest topology" is the quotient topology.
* In Definition 7.2.7 the text writes `s([φ]) = t_X(φ)` for the target map, a possible misprint
  for `t([φ])`; `reducedTgt` (`Reduced.lean`) is the target map.
* Appendix 7.6.3: `JumpingRetract.X` (`ReducedNotHausdorff.lean`) is not Zhou's retract but has the
  same features (a `ℤ/2`-action trivial over `t < 0` and moving points arbitrarily close to the
  origin over `t > 0`); we show `(−1, o₀) ∈ cl(𝐗^T) ∖ 𝐗^T` here; `𝐗^T` is computed exactly in
  `GapP2_AZhouRetract.lean`, and Zhou's retract itself is `GapP2_A2ZhouGroupoid.lean` and
  `GapP2_A2Sigma.lean` (2026-11-12).
* Appendix 7.6.4 is formalized for `i = 1` and as sets: the text uses that `U₁(x)` is connected
  in `X¹` and that `U(x) ∩ X_1` is dense in `U(x)` (the density of `X_1` in `X`, gap G.73;
  `Lift.lean` uses `U(x)₁` only with the restricted action); both are explicit hypotheses of
  `levelVal_mem_nonEffectivePart_of_liftOne`, and of (SLUC) only LUC for `X¹` is used.  The
  hypotheses are satisfied by the trivial ep-groupoid of a point (`Examples.pointEpGroupoid`).
  Not in this file: the sc-diffeomorphism `(𝐗^1)^R ≅ (𝐗^R)^1`, the case `i ≥ 2`, and (ZHOU),
  which §7.4 defines: `corollary_7_6_8` takes "(ZHOU) implies LUC for `X¹`" as a hypothesis.
  Since 2026-11-09 the hypotheses hold for every ep-groupoid (`SmoothConnectedReps.lean`), and
  since 2026-11-12 the sc-diffeomorphism and every `i` are `theorem_7_6_7_one`, `EP.theorem_7_6_7`
  and `EP.corollary_7_6_8` (`GapP2_ARaise.lean`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### Definition 7.2.18: the local unique continuation property -/

namespace NaturalRep

variable {X} {x : Obj} (R : X.NaturalRep x)

/-- **The property of 2021 Definition 7.2.18, p. 321, for one natural representation**
`R` of `x`: an element `g ∈ G_x` whose `Φ(g)` is the identity on some nonempty open `V ⊆ U(x)`
acts as the identity on all of `U(x)`. -/
def HasLUC : Prop :=
  ∀ (g : X.Isotropy x) (V : Set Obj), IsOpen V → V.Nonempty → V ⊆ R.U →
    (∀ y ∈ V, R.Φ g y = y) → ∀ y ∈ R.U, R.Φ g y = y

end NaturalRep

/-- **2021 Definition 7.2.18 (= Definition 7.4.1), p. 321 (new in the 2021 edition)**: the
ep-groupoid `X` has the *local unique continuation property* (LUC) if every object `x` has an open
neighbourhood `U(x)` with the natural `G_x`-action (a natural representation, Theorem 7.1.13
[2017: Theorem 7.1.13 (2017: 7.1)]) such that `ĝ = Φ(g)` is the identity on `U(x)` as soon as it is the identity
on a nonempty open subset.  By `isLUC_iff_forall_naturalRep` the choice of `U(x)` does not
matter; by `proposition_7_2_21` LUC means that `𝐗^T` is closed. -/
def IsLUC : Prop := ∀ x : Obj, ∃ R : X.NaturalRep x, R.HasLUC

/-- **LUC is satisfiable**: the trivial ep-groupoid of every M-polyfold has LUC (its
isotropy groups are trivial). -/
theorem isLUC_trivial {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (P : MPolyfold Z) : (trivial P).IsLUC := fun x => by
  obtain ⟨R, -⟩ := (trivial P).theorem_7_1_13 x isOpen_univ (mem_univ x)
  refine ⟨R, fun g _ _ _ _ _ y hy => ?_⟩
  rw [Subsingleton.elim g 1]
  exact R.Φ_one y hy

/-! ### Definition 7.2.5, Lemma 7.2.6 and Remark 7.2.8 -/

namespace NaturalRep

variable {X} {x : Obj} (R : X.NaturalRep x)

/-- `T_x^V = {g ∈ G_x | Φ(g) = id on V ∩ U(x)}`, the subgroup of the elements acting trivially
on `V` (for 2021 Definition 7.2.5). -/
def kerOn (V : Set Obj) : Subgroup (X.Isotropy x) where
  carrier := {g | ∀ y ∈ V ∩ R.U, R.Φ g y = y}
  mul_mem' {g h} hg hh y hy := by
    change R.Φ (g * h) y = y
    rw [R.Φ_mul g h y hy.2, hh y hy, hg y hy]
  one_mem' y hy := R.Φ_one y hy.2
  inv_mem' {g} hg y hy := by
    have h := R.Φ_inv_Φ g hy.2
    rwa [hg y hy] at h

/-- Membership in `T_x^V`. -/
theorem mem_kerOn {V : Set Obj} {g : X.Isotropy x} :
    g ∈ R.kerOn V ↔ ∀ y ∈ V ∩ R.U, R.Φ g y = y :=
  Iff.rfl

/-- Smaller sets have larger `T_x^V`. -/
theorem kerOn_anti {V W : Set Obj} (h : V ⊆ W) : R.kerOn W ≤ R.kerOn V :=
  fun _ hg y hy => hg y ⟨h hy.1, hy.2⟩

/-- `T_x^V` is normal when `V` is `G_x`-invariant. -/
theorem kerOn_normal {V : Set Obj} (hV : ∀ g, MapsTo (R.Φ g) V V) : (R.kerOn V).Normal where
  conj_mem n hn g y hy := by
    have hy' : R.Φ g⁻¹ y ∈ V ∩ R.U := ⟨hV g⁻¹ hy.1, R.mapsTo_Φ g⁻¹ hy.2⟩
    change R.Φ (g * n * g⁻¹) y = y
    rw [R.Φ_mul _ _ y hy.2, R.Φ_mul _ _ _ hy'.2, hn _ hy', R.Φ_Φ_inv g hy.2]

/-- For an open `W ∋ x`, `T_x^W ⊆ T_x`. -/
theorem kerOn_le_trivialSubgroup {W : Set Obj} (hW : IsOpen W) (hxW : x ∈ W) :
    R.kerOn W ≤ X.trivialSubgroup x := fun g hg => by
  refine R.actsTrivially_iff.2 ?_
  filter_upwards [inter_mem (hW.mem_nhds hxW) (R.isOpen_U.mem_nhds R.mem_U)] with y hy
  exact hg y hy

end NaturalRep

/-- **2021 Definition 7.2.5, p. 310** (2017: before Definition 7.12, p. 241): `T_x`
(`trivialSubgroup`, defined intrinsically in `Effective.lean`) is the maximal subgroup acting
trivially on a small `W(x)`: `T_x^W ⊆ T_x` for every open `W ∋ x`, and there is a
`G_x`-invariant open `V ∋ x` in `U(x)` with `T_x^W = T_x` for every open `x ∈ W ⊆ V`.  Since this
holds for every natural representation `R`, `T_x` does not depend on `U(x)`. -/
theorem definition_7_2_5 {x : Obj} (R : X.NaturalRep x) :
    (∀ W : Set Obj, IsOpen W → x ∈ W → R.kerOn W ≤ X.trivialSubgroup x) ∧
    ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧ V ⊆ R.U ∧ (∀ g, MapsTo (R.Φ g) V V) ∧
      ∀ W : Set Obj, IsOpen W → x ∈ W → W ⊆ V → R.kerOn W = X.trivialSubgroup x := by
  have := NatRepConstruction.finite_isotropy X x
  refine ⟨fun W hW hxW => R.kerOn_le_trivialSubgroup hW hxW, ?_⟩
  have hev : ∀ᶠ y in 𝓝 x, ∀ g, g ∈ X.trivialSubgroup x → R.Φ g y = y := by
    refine Filter.eventually_all.2 fun g => ?_
    by_cases hg : g ∈ X.trivialSubgroup x
    · filter_upwards [R.actsTrivially_iff.1 hg] with y hy _ using hy
    · exact Filter.Eventually.of_forall fun _ h => absurd h hg
  set N := interior {y | ∀ g, g ∈ X.trivialSubgroup x → R.Φ g y = y}
  have hxN : x ∈ N := mem_interior_iff_mem_nhds.2 hev
  set V := ⋂ g, R.U ∩ R.Φ g ⁻¹' N
  have hVo : IsOpen V := isOpen_iInter_of_finite fun g =>
    (R.continuousOn_Φ g).isOpen_inter_preimage R.isOpen_U isOpen_interior
  have hxV : x ∈ V := mem_iInter.2 fun g => ⟨R.mem_U, by rw [mem_preimage, R.Φ_self]; exact hxN⟩
  have hVU : V ⊆ R.U := fun y hy => (mem_iInter.1 hy 1).1
  have hVN : V ⊆ N := fun y hy => by
    have h1 := (mem_iInter.1 hy 1).2
    rwa [mem_preimage, R.Φ_one y (hVU hy)] at h1
  have hVinv : ∀ g, MapsTo (R.Φ g) V V := fun g y hy => mem_iInter.2 fun h =>
    ⟨R.mapsTo_Φ g (hVU hy), by
      rw [mem_preimage, ← R.Φ_mul h g y (hVU hy)]
      exact (mem_iInter.1 hy (h * g)).2⟩
  refine ⟨V, hVo, hxV, hVU, hVinv, fun W hW hxW hWV =>
    le_antisymm (R.kerOn_le_trivialSubgroup hW hxW) fun g hg y hy => ?_⟩
  exact interior_subset (hVN (hWV hy.1)) g hg

/-- **2021 Lemma 7.2.6, p. 310 (new in the 2021 edition)**: for `φ : x → y`, the map
`T_x → G_y`, `g ↦ φ ∘ g ∘ φ⁻¹` is injective with image `T_y`. -/
theorem lemma_7_2_6 {x y : Obj} (φ : Mor) (hx : X.src φ = x) (hy : X.tgt φ = y) :
    Injective (fun g : X.trivialSubgroup x => X.isotropyConj φ hx hy g) ∧
      (X.trivialSubgroup x).map (X.isotropyConj φ hx hy).toMonoidHom = X.trivialSubgroup y :=
  ⟨(X.isotropyConj φ hx hy).injective.comp Subtype.val_injective,
    X.map_isotropyConj_trivialSubgroup φ hx hy⟩

/-- 2021 Lemma 7.2.6 as an isomorphism `T_x ≃* T_y`, `g ↦ φ ∘ g ∘ φ⁻¹`. -/
def trivialSubgroupEquiv {x y : Obj} (φ : Mor) (hx : X.src φ = x) (hy : X.tgt φ = y) :
    X.trivialSubgroup x ≃* X.trivialSubgroup y :=
  ((X.isotropyConj φ hx hy).subgroupMap _).trans
    (MulEquiv.subgroupCongr (X.map_isotropyConj_trivialSubgroup φ hx hy))

/-- `trivialSubgroupEquiv` is conjugation by `φ`. -/
theorem trivialSubgroupEquiv_apply {x y : Obj} (φ : Mor) (hx : X.src φ = x)
    (hy : X.tgt φ = y) (g : X.trivialSubgroup x) :
    (X.trivialSubgroupEquiv φ hx hy g : X.Isotropy y) = X.isotropyConj φ hx hy g :=
  rfl

/-- **2021 Remark 7.2.8, p. 311 (new in the 2021 edition)**: the topology `T_R` of `𝐗^R`
(the quotient topology, `Reduced.lean`) is the finest topology for which `π : 𝐗 → 𝐗^R` is
continuous.  The example with `T_R` not Hausdorff is `JumpingRetract.not_t2Space_reducedMor`. -/
theorem remark_7_2_8 :
    Continuous X.reducedπ ∧ ∀ t : TopologicalSpace X.ReducedMor,
      Continuous[_, t] X.reducedπ → (inferInstance : TopologicalSpace X.ReducedMor) ≤ t :=
  ⟨X.continuous_reducedπ, fun _ h => by rw [continuous_iff_coinduced_le] at h⟩

/-! ### Propositions 7.2.12, 7.2.13 and Theorem 7.2.14 -/

/-- **Paracompactness descends along an open continuous surjection
`p : M → Q`** if every `q ∈ Q` has a compact `K ⊆ M` such that every open `N ⊇ K` contains
`p⁻¹(O)` for some open `O ∋ q`.  No separation axiom is needed: the images of a locally finite
precise refinement upstairs form one downstairs. -/
theorem paracompactSpace_of_isOpenMap {M : Type*} {Q : Type*} [TopologicalSpace M]
    [TopologicalSpace Q] [ParacompactSpace M] {p : M → Q} (hpc : Continuous p)
    (hpo : IsOpenMap p) (hps : Surjective p)
    (hK : ∀ q : Q, ∃ K : Set M, IsCompact K ∧ ∀ N : Set M, IsOpen N → K ⊆ N →
      ∃ O : Set Q, IsOpen O ∧ q ∈ O ∧ p ⁻¹' O ⊆ N) :
    ParacompactSpace Q := by
  refine ⟨fun α s hso hsc => ?_⟩
  obtain ⟨v, hvo, hvc, hvl, hvs⟩ := precise_refinement (fun a => p ⁻¹' s a)
    (fun a => (hso a).preimage hpc) (by rw [← preimage_iUnion, hsc, preimage_univ])
  refine ⟨α, fun a => p '' v a, fun a => hpo _ (hvo a), ?_, ?_, fun a => ⟨a, ?_⟩⟩
  · refine eq_univ_of_forall fun q => ?_
    obtain ⟨m, rfl⟩ := hps q
    have hm : m ∈ ⋃ a, v a := by rw [hvc]; exact mem_univ m
    obtain ⟨a, ha⟩ := mem_iUnion.1 hm
    exact mem_iUnion.2 ⟨a, m, ha, rfl⟩
  · intro q
    obtain ⟨K, hKc, hKN⟩ := hK q
    choose U hU hUf using hvl
    obtain ⟨F, -, hKF⟩ := hKc.elim_nhds_subcover (fun m => interior (U m))
      fun m _ => interior_mem_nhds.2 (hU m)
    obtain ⟨O, hOo, hqO, hON⟩ := hKN _ (isOpen_biUnion fun m _ => isOpen_interior) hKF
    refine ⟨O, hOo.mem_nhds hqO, (F.finite_toSet.biUnion fun m _ => hUf m).subset ?_⟩
    rintro a ⟨_, ⟨m', hm', rfl⟩, hm'O⟩
    obtain ⟨m, hmF, hm'U⟩ := mem_iUnion₂.1 (hON hm'O)
    exact mem_iUnion₂.2 ⟨m, hmF, m', hm', interior_subset hm'U⟩
  · exact image_subset_iff.2 (hvs a)

/-- The hypothesis of `paracompactSpace_of_isOpenMap` for
`π : 𝐗 → 𝐗^R`: with `V` from the properness axiom at `s(q)`, `K = {φ ∈ s⁻¹(cl V) | (s φ, t φ) =
(s q, t q)}` is compact and, `(s, t)` being proper hence closed on `s⁻¹(cl V)`, every open
`N ⊇ K` contains `π⁻¹(O)` for an open `O ∋ q`. -/
theorem exists_isCompact_preimage_reducedπ_subset (q : X.ReducedMor) :
    ∃ K : Set Mor, IsCompact K ∧ ∀ N : Set Mor, IsOpen N → K ⊆ N →
      ∃ O : Set X.ReducedMor, IsOpen O ∧ q ∈ O ∧ X.reducedπ ⁻¹' O ⊆ N := by
  obtain ⟨V, hVo, hxV, hV⟩ := X.exists_isProperMap (X.reducedSrc q)
  set S := X.src ⁻¹' closure V
  let P : S → Obj × Obj := fun m => (X.src m.1, X.tgt m.1)
  have hPc : Continuous P :=
    (X.continuous_src.comp continuous_subtype_val).prodMk
      (X.continuous_tgt.comp continuous_subtype_val)
  have hP : IsProperMap P := isProperMap_of_comp_of_t2 hPc continuous_snd hV
  refine ⟨Subtype.val '' (P ⁻¹' {(X.reducedSrc q, X.reducedTgt q)}),
    (hP.isCompact_preimage isCompact_singleton).image continuous_subtype_val, fun N hN hKN => ?_⟩
  -- the image under `P` of the closed set `{m ∈ S | m ∉ N}` misses `(s q, t q)`
  have hA : IsClosed (P '' {m : S | m.1 ∉ N}) :=
    hP.isClosedMap _ (hN.preimage continuous_subtype_val).isClosed_compl
  have hqA : (X.reducedSrc q, X.reducedTgt q) ∈ (P '' {m : S | m.1 ∉ N})ᶜ := by
    rintro ⟨m, hmN, hm⟩
    exact hmN (hKN ⟨m, hm, rfl⟩)
  obtain ⟨V₁, V₂, hV₁, hV₂, hq₁, hq₂, hV₁₂⟩ := isOpen_prod_iff.1 hA.isOpen_compl _ _ hqA
  refine ⟨X.reducedSrc ⁻¹' (V ∩ V₁) ∩ X.reducedTgt ⁻¹' V₂,
    ((hVo.inter hV₁).preimage X.continuous_reducedSrc).inter
      (hV₂.preimage X.continuous_reducedTgt), ⟨⟨hxV, hq₁⟩, hq₂⟩, fun ψ hψ => ?_⟩
  by_contra hψN
  have hψS : ψ ∈ S := subset_closure hψ.1.1
  exact hV₁₂ (mk_mem_prod hψ.1.2 hψ.2) ⟨⟨ψ, hψS⟩, hψN, rfl⟩

/-- `T_R` is paracompact for every ep-groupoid (2021 Proposition 7.2.12). -/
instance paracompactSpace_reducedMor : ParacompactSpace X.ReducedMor :=
  paracompactSpace_of_isOpenMap X.continuous_reducedπ X.isOpenMap_reducedπ
    X.surjective_reducedπ X.exists_isCompact_preimage_reducedπ_subset

/-- **2021 Proposition 7.2.12, p. 317 (new in the 2021 edition)**: `(𝐗^R, T_R)` is
paracompact, in the sense of the footnote on p. 317 (not including Hausdorff), which is Mathlib's
`ParacompactSpace`. -/
theorem proposition_7_2_12 : ParacompactSpace X.ReducedMor := inferInstance

/-- **2021 Proposition 7.2.13, p. 318 (new in the 2021 edition)**: the natural
charts (`reducedAtlas`) define an M-polyfold structure on `(𝐗^R, T_R)` iff `T_R` is Hausdorff.
An M-polyfold is Hausdorff and paracompact by definition; the `if` direction is
`reducedPolyfold`. -/
theorem proposition_7_2_13 :
    (∃ (_ : T2Space X.ReducedMor) (_ : ParacompactSpace X.ReducedMor) (P : MPolyfold X.ReducedMor),
      P.atlas = X.reducedAtlas) ↔ T2Space X.ReducedMor :=
  ⟨fun ⟨h, _, _⟩ => h, fun h => ⟨h, inferInstance, X.reducedPolyfold, rfl⟩⟩

/-- **2021 Theorem 7.2.14, p. 318** (2017: Proposition 7.10, p. 244): if `T_R` is
Hausdorff, `(X, 𝐗^R)` is in a natural way an ep-groupoid: `reducedEpGroupoid` has the groupoid
structure `reducedGroupoidStr`, the object M-polyfold of `X`, the natural atlas on `𝐗^R`, and
`π` gives an ep-functor `X → X_R`. -/
theorem theorem_7_2_14 [T2Space X.ReducedMor] :
    X.reducedEpGroupoid.toGroupoidStr = X.reducedGroupoidStr ∧
    X.reducedEpGroupoid.PObj = X.PObj ∧ X.reducedEpGroupoid.PMor.atlas = X.reducedAtlas ∧
    Nonempty (EpFunctor X X.reducedEpGroupoid) :=
  ⟨rfl, rfl, rfl, ⟨X.reductionFunctor⟩⟩

/-! ### Proposition 7.2.17 -/

/-- `[φ] = [ψ]` iff `t φ = t ψ` and `ψ⁻¹ ∘ φ ∈ 𝐗^T`. -/
theorem reducedπ_eq_iff_comp_inv {φ ψ : Mor} :
    X.reducedπ φ = X.reducedπ ψ ↔
      X.tgt φ = X.tgt ψ ∧ X.comp (X.inv ψ) φ ∈ X.nonEffectivePart := by
  rw [X.reducedπ_eq_iff, reducedRel_iff]
  constructor
  · rintro ⟨k, hk, hc, rfl⟩
    refine ⟨X.tgt_comp _ _ hc, ?_⟩
    rw [GroupoidStr.inv_comp_cancel_left hc]
    exact hk
  · rintro ⟨ht, hk⟩
    have hc : X.src (X.inv ψ) = X.tgt φ := by rw [X.src_inv, ht]
    refine ⟨_, hk, ?_, ?_⟩
    · rw [X.tgt_comp _ _ hc, X.tgt_inv]
    · rw [← X.comp_assoc _ _ _ (X.tgt_inv ψ).symm hc, X.comp_inv,
        GroupoidStr.unit_comp_of_eq ht]

/-- `φ ∈ 𝐗^T` iff `[φ] = [1_{s(φ)}]`. -/
theorem mem_nonEffectivePart_iff_reducedπ {φ : Mor} :
    φ ∈ X.nonEffectivePart ↔ X.reducedπ φ = X.reducedπ (X.unit (X.src φ)) := by
  constructor
  · intro h
    have hst := src_eq_tgt_of_mem_nonEffectivePart h
    refine X.reducedπ_eq_iff_comp_inv.2 ⟨by rw [X.tgt_unit, hst], ?_⟩
    rw [GroupoidStr.inv_unit, GroupoidStr.unit_comp_of_eq hst.symm]
    exact h
  · intro h
    obtain ⟨ht, hk⟩ := X.reducedπ_eq_iff_comp_inv.1 h
    rw [X.tgt_unit] at ht
    rwa [GroupoidStr.inv_unit, GroupoidStr.unit_comp_of_eq ht] at hk

/-- The multiplication is continuous on the fibred product. -/
theorem continuous_comp_fibredProduct :
    Continuous fun p : MPolyfold.fibredProduct X.src X.tgt => X.comp p.1.1 p.1.2 := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor X.PMor
  let _ := (X.PMor.prod X.PMor).paracompactSpace_subtype (MPolyfold.fibredProduct X.src X.tgt)
  have hF := MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src X.isScSmoothMap_tgt
  have hm : (MPolyfold.subPolyfold hF).IsScSmoothMap X.PMor fun p => X.comp p.1.1 p.1.2 :=
    X.isScSmoothComp
  exact continuousOn_univ.1 hm.continuousOn

/-- `(φ, ψ) ↦ ψ⁻¹ ∘ φ` is continuous on `{t φ = t ψ}`. -/
theorem continuousOn_comp_inv :
    ContinuousOn (fun q : Mor × Mor => X.comp (X.inv q.2) q.1) {q | X.tgt q.1 = X.tgt q.2} := by
  rw [continuousOn_iff_continuous_domRestrict]
  let j : {q : Mor × Mor | X.tgt q.1 = X.tgt q.2} → MPolyfold.fibredProduct X.src X.tgt :=
    fun q => ⟨(X.inv q.1.2, q.1.1), by
      change X.src (X.inv q.1.2) = X.tgt q.1.1
      rw [X.src_inv]
      exact q.2.symm⟩
  have hj : Continuous j :=
    ((X.continuous_inv.comp (continuous_snd.comp continuous_subtype_val)).prodMk
      (continuous_fst.comp continuous_subtype_val)).subtype_mk _
  exact X.continuous_comp_fibredProduct.comp hj

/-- If `𝐗^T` is closed, the relation `[φ] = [ψ]` is closed in
`𝐗 × 𝐗`. -/
theorem isClosed_reducedπ_eq_of_isClosed (h : IsClosed X.nonEffectivePart) :
    IsClosed {q : Mor × Mor | X.reducedπ q.1 = X.reducedπ q.2} := by
  have he : {q : Mor × Mor | X.reducedπ q.1 = X.reducedπ q.2} =
      {q : Mor × Mor | X.tgt q.1 = X.tgt q.2} ∩
        (fun q : Mor × Mor => X.comp (X.inv q.2) q.1) ⁻¹' X.nonEffectivePart := by
    ext q
    exact X.reducedπ_eq_iff_comp_inv
  rw [he]
  exact X.continuousOn_comp_inv.preimage_isClosed_of_isClosed
    (isClosed_eq (X.continuous_tgt.comp continuous_fst) (X.continuous_tgt.comp continuous_snd)) h

/-- `π : 𝐗 → 𝐗^R` is an open quotient map (2021 Lemma 7.2.9). -/
theorem isOpenQuotientMap_reducedπ : IsOpenQuotientMap X.reducedπ :=
  ⟨X.surjective_reducedπ, X.continuous_reducedπ, X.isOpenMap_reducedπ⟩

/-- If `T_R` is Hausdorff, `𝐗^T = {φ | [φ] = [1_{s(φ)}]}` is
closed. -/
theorem isClosed_nonEffectivePart_of_t2Space [T2Space X.ReducedMor] :
    IsClosed X.nonEffectivePart := by
  have he : X.nonEffectivePart = {φ | X.reducedπ φ = X.reducedπ (X.unit (X.src φ))} := by
    ext φ
    exact X.mem_nonEffectivePart_iff_reducedπ
  rw [he]
  exact isClosed_eq X.continuous_reducedπ
    (X.continuous_reducedπ.comp (X.continuous_unit.comp X.continuous_src))

/-- **2021 Proposition 7.2.17, p. 320 (new in the 2021 edition)**: `T_R` is
Hausdorff iff the non-effective part `𝐗^T` is closed in `𝐗`. -/
theorem proposition_7_2_17 : T2Space X.ReducedMor ↔ IsClosed X.nonEffectivePart :=
  ⟨fun _ => X.isClosed_nonEffectivePart_of_t2Space, fun h =>
    (t2Space_iff_of_isOpenQuotientMap X.isOpenQuotientMap_reducedπ).2
      (X.isClosed_reducedπ_eq_of_isClosed h)⟩

/-! ### Proposition 7.2.21, Remark 7.2.20, Theorem 7.2.22, Proposition 7.2.23 -/

/-- `{φ | s φ = t φ}` is closed in `𝐗`. -/
theorem isClosed_src_eq_tgt : IsClosed {φ : Mor | X.src φ = X.tgt φ} :=
  isClosed_eq X.continuous_src X.continuous_tgt

/-- `cl 𝐗^T ⊆ {s = t}`. -/
theorem closure_nonEffectivePart_subset :
    closure X.nonEffectivePart ⊆ {φ | X.src φ = X.tgt φ} :=
  closure_minimal (fun _ h => src_eq_tgt_of_mem_nonEffectivePart h) X.isClosed_src_eq_tgt

namespace NaturalRep

variable {X} {x : Obj} (R : X.NaturalRep x)

/-- If `Γ(g, y) ∈ 𝐗^T`, then `Φ(g) = id` near `y`. -/
theorem eventually_Φ_eq_of_Γ_mem {g : X.Isotropy x} {y : Obj} (hy : y ∈ R.U)
    (h : R.Γ g y ∈ X.nonEffectivePart) : ∀ᶠ z in 𝓝 y, z ∈ R.U ∧ R.Φ g z = z := by
  have hc : ContinuousAt (R.Γ g) y := (R.continuousOn_Γ g).continuousAt (R.isOpen_U.mem_nhds hy)
  filter_upwards [hc.eventually (X.mem_nonEffectivePart_iff.1 h), R.isOpen_U.mem_nhds hy]
    with z hz hzU
  refine ⟨hzU, ?_⟩
  rw [← R.tgt_Γ g z hzU, ← hz, R.src_Γ g z hzU]

/-- If `Φ(g) = id` near `y`, then `Γ(g, y) ∈ 𝐗^T`. -/
theorem Γ_mem_of_eventually {g : X.Isotropy x} {y : Obj} (hy : y ∈ R.U)
    (h : ∀ᶠ z in 𝓝 y, R.Φ g z = z) : R.Γ g y ∈ X.nonEffectivePart := by
  obtain ⟨D, hDs, hDo, hyD⟩ := mem_nhds_iff.1 (inter_mem h (R.isOpen_U.mem_nhds hy))
  let h' : X.Isotropy y := ⟨R.Γ g y, R.src_Γ g y hy, (R.tgt_Γ g y hy).trans (hDs hyD).1⟩
  have hT : h' ∈ X.trivialSet y := X.mem_trivialSet_of_section hDo hyD
    ((R.continuousOn_Γ g).mono fun z hz => (hDs hz).2) (fun z hz => R.src_Γ g z (hDs hz).2)
    (fun z hz => (R.tgt_Γ g z (hDs hz).2).trans (hDs hz).1) rfl
  exact ⟨y, h', hT, rfl⟩

/-- **If `𝐗^T` is closed, every natural representation has the property of
Definition 7.2.18**: the set of points near which `Φ(g) = id` is open, and closed in the connected
`U(x)` because `Γ(g, ·)` is continuous and `𝐗^T` closed (compare 2021 Proposition 7.4.2). -/
theorem hasLUC_of_isClosed (h : IsClosed X.nonEffectivePart) : R.HasLUC := by
  intro g V hVo hVne hVU hV
  set u := {y | ∀ᶠ z in 𝓝 y, z ∈ R.U ∧ R.Φ g z = z}
  have huo : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hsub : R.U ⊆ u := by
    refine R.isConnected_U.isPreconnected.subset_of_closure_inter_subset huo ?_ ?_
    · obtain ⟨v, hv⟩ := hVne
      refine ⟨v, hVU hv, ?_⟩
      filter_upwards [hVo.mem_nhds hv] with z hz using ⟨hVU hz, hV z hz⟩
    · rintro y ⟨hyc, hyU⟩
      have hc : ContinuousAt (R.Γ g) y :=
        (R.continuousOn_Γ g).continuousAt (R.isOpen_U.mem_nhds hyU)
      have himg : R.Γ g '' u ⊆ X.nonEffectivePart := by
        rintro _ ⟨y', hy', rfl⟩
        exact R.Γ_mem_of_eventually hy'.self_of_nhds.1 (hy'.mono fun z hz => hz.2)
      exact R.eventually_Φ_eq_of_Γ_mem hyU
        (h.closure_subset_iff.2 himg (mem_closure_image hc hyc))
  intro y hy
  exact (hsub hy).self_of_nhds.2

end NaturalRep

/-- **LUC implies `𝐗^T` closed** (2021 Proposition 7.2.21,
(1) ⇒ (2)): for `φ ∈ cl 𝐗^T`, `g = φ ∈ G_x`; the open sheet `Γ(g, U(x)) ∋ φ` meets `𝐗^T` in
some `Γ(g, y)`, so `Φ(g) = id` near `y`, and LUC gives `Φ(g) = id` on `U(x)`, i.e. `φ ∈ T_x`. -/
theorem isClosed_nonEffectivePart_of_isLUC (h : X.IsLUC) : IsClosed X.nonEffectivePart := by
  refine closure_subset_iff_isClosed.1 fun φ hφ => ?_
  have hst := X.closure_nonEffectivePart_subset hφ
  let g : X.Isotropy (X.src φ) := ⟨φ, rfl, hst.symm⟩
  obtain ⟨R, hR⟩ := h (X.src φ)
  have hgW : φ ∈ R.Γ g '' R.U := by
    have h' := R.Γ_mem_image g R.mem_U
    rwa [R.Γ_self] at h'
  obtain ⟨_, ⟨y, hy, rfl⟩, hψ⟩ := mem_closure_iff.1 hφ _ (R.isOpen_image_Γ g) hgW
  obtain ⟨D, hDs, hDo, hyD⟩ := mem_nhds_iff.1 (R.eventually_Φ_eq_of_Γ_mem hy hψ)
  have htriv := hR g D hDo ⟨y, hyD⟩ (fun z hz => (hDs hz).1) (fun z hz => (hDs hz).2)
  exact ⟨X.src φ, g, ⟨R, htriv⟩, rfl⟩

/-- LUC holds iff every natural representation of every object has the
property of Definition 7.2.18. -/
theorem isLUC_iff_forall_naturalRep :
    X.IsLUC ↔ ∀ (x : Obj) (R : X.NaturalRep x), R.HasLUC := by
  refine ⟨fun h _ R => R.hasLUC_of_isClosed (X.isClosed_nonEffectivePart_of_isLUC h),
    fun h x => ?_⟩
  obtain ⟨R, -⟩ := X.theorem_7_1_13 x isOpen_univ (mem_univ x)
  exact ⟨R, h x R⟩

/-- **2021 Proposition 7.2.21, p. 321 (new in the 2021 edition)**: `X` has LUC iff
`𝐗^T` is closed in `𝐗`. -/
theorem proposition_7_2_21 : X.IsLUC ↔ IsClosed X.nonEffectivePart :=
  ⟨X.isClosed_nonEffectivePart_of_isLUC, fun h => X.isLUC_iff_forall_naturalRep.2
    fun _ R => R.hasLUC_of_isClosed h⟩

/-- **2021 Remark 7.2.20, p. 321 (new in the 2021 edition)**: under LUC, the
neighbourhood `U(x)` of Definition 7.2.18 can be taken inside any open `O ∋ x`. -/
theorem remark_7_2_20 (h : X.IsLUC) (x : Obj) {O : Set Obj} (hO : IsOpen O) (hx : x ∈ O) :
    ∃ R : X.NaturalRep x, R.U ⊆ O ∧ R.HasLUC := by
  obtain ⟨R, hR⟩ := h x
  obtain ⟨R', hR'U, hR'Φ, -⟩ := X.exists_naturalRep_shrink R hO hx
  refine ⟨R', fun y hy => (hR'U hy).1, fun g V hVo hVne hVU hV y hy => ?_⟩
  rw [hR'Φ] at hV ⊢
  exact hR g V hVo hVne (hVU.trans fun z hz => (hR'U hz).2) hV y (hR'U hy).2

/-- **2021 Theorem 7.2.22, p. 323 (new in the 2021 edition)**: equivalent are
(1) `T_R` is Hausdorff, (2) `X` has LUC, (3) `𝐗^T` is closed in `𝐗`. -/
theorem theorem_7_2_22 :
    List.TFAE [T2Space X.ReducedMor, X.IsLUC, IsClosed X.nonEffectivePart] := by
  tfae_have 1 ↔ 3 := X.proposition_7_2_17
  tfae_have 2 ↔ 3 := X.proposition_7_2_21
  tfae_finish

/-- LUC implies `T_R` Hausdorff. -/
theorem t2Space_reducedMor_of_isLUC (h : X.IsLUC) : T2Space X.ReducedMor :=
  X.proposition_7_2_17.2 (X.proposition_7_2_21.1 h)

/-- **2021 Proposition 7.2.23, p. 323 (new in the 2021 edition)**: under LUC the
reduced ep-groupoid `X_R` is well defined: `T_R` is Hausdorff and `reducedEpGroupoid` is an
ep-groupoid (effective, 2021 Proposition 7.2.16) with the ep-functor `X → X_R`. -/
theorem proposition_7_2_23 (h : X.IsLUC) :
    ∃ (_ : T2Space X.ReducedMor), X.reducedEpGroupoid.toGroupoidStr = X.reducedGroupoidStr ∧
      X.reducedEpGroupoid.PObj = X.PObj ∧ X.reducedEpGroupoid.PMor.atlas = X.reducedAtlas ∧
      X.reducedEpGroupoid.IsEffective ∧ Nonempty (EpFunctor X X.reducedEpGroupoid) :=
  haveI := X.t2Space_reducedMor_of_isLUC h
  ⟨inferInstance, rfl, rfl, rfl, X.isEffective_reducedEpGroupoid, ⟨X.reductionFunctor⟩⟩

/-! ### LUC: witnesses -/

/-- The units form a closed subset of `𝐗`. -/
theorem isClosed_range_unit : IsClosed (range X.unit) := by
  have he : range X.unit = {φ | X.unit (X.src φ) = φ} := by
    ext φ
    refine ⟨?_, fun h => ⟨_, h⟩⟩
    rintro ⟨x, rfl⟩
    rw [mem_ofPred_eq, X.src_unit]
  rw [he]
  exact isClosed_eq (X.continuous_unit.comp X.continuous_src) continuous_id

/-- For effective `X`, `𝐗^T` is the set of units. -/
theorem nonEffectivePart_eq_range_unit_of_isEffective (hX : X.IsEffective) :
    X.nonEffectivePart = range X.unit := by
  ext φ
  constructor
  · rintro ⟨x, g, hg, rfl⟩
    obtain rfl : g = 1 :=
      (Subgroup.eq_bot_iff_forall _).1 (X.isEffective_iff_trivialSubgroup_eq_bot.1 hX x) g hg
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact X.unit_mem_nonEffectivePart x

/-- **LUC is satisfiable**: every effective ep-groupoid has LUC. -/
theorem isLUC_of_isEffective (hX : X.IsEffective) : X.IsLUC :=
  X.proposition_7_2_21.2 (by
    rw [X.nonEffectivePart_eq_range_unit_of_isEffective hX]
    exact X.isClosed_range_unit)

namespace Examples

/-- In `trivialZ3EpGroupoid` (`ℤ/3` acting trivially) `𝐗^T = 𝐗`. -/
theorem nonEffectivePart_trivialZ3 : trivialZ3EpGroupoid.nonEffectivePart = univ :=
  eq_univ_of_forall fun _ => trivialZ3EpGroupoid.mem_nonEffectivePart_iff.2
    (Eventually.of_forall fun _ => rfl)

/-- **A non-effective ep-groupoid with LUC**: `trivialZ3EpGroupoid`. -/
theorem isLUC_trivialZ3 : trivialZ3EpGroupoid.IsLUC :=
  trivialZ3EpGroupoid.proposition_7_2_21.2 (by
    rw [nonEffectivePart_trivialZ3]
    exact isClosed_univ)

/-- ... so its `T_R` is Hausdorff (Theorem 7.2.22). -/
theorem t2Space_reducedMor_trivialZ3 : T2Space trivialZ3EpGroupoid.ReducedMor :=
  trivialZ3EpGroupoid.t2Space_reducedMor_of_isLUC isLUC_trivialZ3

/-- The effective `reflectionEpGroupoid` has LUC. -/
theorem isLUC_reflection : reflectionEpGroupoid.IsLUC :=
  reflectionEpGroupoid.isLUC_of_isEffective isEffective_reflection

end Examples

/-! ### Lemma 7.2.11 -/

/-- The class `π⁻¹([φ₀])` is finite (it lies in `φ₀ ∘ G_{s(φ₀)}`). -/
theorem finite_reducedπ_preimage (φ₀ : Mor) : (X.reducedπ ⁻¹' {X.reducedπ φ₀}).Finite := by
  refine ((Set.finite_range fun g : X.Isotropy (X.src φ₀) => g.val).image (X.comp φ₀)).subset ?_
  intro ψ hψ
  obtain ⟨hs, g, -, he⟩ := X.reducedπ_eq_iff.1 hψ
  exact ⟨g.val, ⟨⟨g.val, g.src_val.trans hs, g.tgt_val.trans hs⟩, rfl⟩, he.symm⟩

/-- **The conclusion of 2021 Lemma 7.2.11, p. 315 (new in the 2021 edition)** at
`φ₀`: open `U(φ) ∋ φ` for the members `φ` of the class of `φ₀` and an open `U([φ₀]) ∋ [φ₀]` such
that (1) distinct `U(φ)` have disjoint closures, (2) `π(U(φ)) = U([φ₀])` and `π` is an open
embedding on `U(φ)`, (3) `π⁻¹(U([φ₀]))` is covered by the `U(φ)`. -/
def IsReducedEvenlyCovered (φ₀ : Mor) : Prop :=
  ∃ (U : Mor → Set Mor) (V : Set X.ReducedMor), IsOpen V ∧ X.reducedπ φ₀ ∈ V ∧
    (∀ φ ∈ X.reducedπ ⁻¹' {X.reducedπ φ₀}, IsOpen (U φ) ∧ φ ∈ U φ) ∧
    (X.reducedπ ⁻¹' {X.reducedπ φ₀}).PairwiseDisjoint (fun φ => closure (U φ)) ∧
    (∀ φ ∈ X.reducedπ ⁻¹' {X.reducedπ φ₀},
      X.reducedπ '' U φ = V ∧ IsOpenEmbedding ((U φ).domRestrict X.reducedπ)) ∧
    X.reducedπ ⁻¹' V ⊆ ⋃ φ ∈ X.reducedπ ⁻¹' {X.reducedπ φ₀}, U φ

/-- If `T_R` is Hausdorff, every open `N ⊇ π⁻¹(q)`
contains `π⁻¹(O)` for an open `O ∋ q`. -/
theorem exists_preimage_reducedπ_subset_of_t2Space [T2Space X.ReducedMor] (q : X.ReducedMor)
    {N : Set Mor} (hN : IsOpen N) (hqN : X.reducedπ ⁻¹' {q} ⊆ N) :
    ∃ O : Set X.ReducedMor, IsOpen O ∧ q ∈ O ∧ X.reducedπ ⁻¹' O ⊆ N := by
  obtain ⟨K, hK, hKN⟩ := X.exists_isCompact_preimage_reducedπ_subset q
  have hKc : IsCompact (X.reducedπ '' (K \ N)) := (hK.diff hN).image X.continuous_reducedπ
  have hq : q ∉ X.reducedπ '' (K \ N) := by
    rintro ⟨m, hm, hmq⟩
    exact hm.2 (hqN hmq)
  obtain ⟨O₁, O₂, hO₁, hO₂, hqO₁, hKO₂, hdisj⟩ :=
    SeparatedNhds.of_isCompact_isCompact isCompact_singleton hKc (disjoint_singleton_left.2 hq)
  obtain ⟨O, hO, hqO, hON⟩ := hKN (N ∪ X.reducedπ ⁻¹' O₂)
    (hN.union (hO₂.preimage X.continuous_reducedπ)) fun m hm => by
      by_cases hmN : m ∈ N
      · exact Or.inl hmN
      · exact Or.inr (hKO₂ ⟨m, ⟨hm, hmN⟩, rfl⟩)
  refine ⟨O ∩ O₁, hO.inter hO₁, ⟨hqO, hqO₁ (mem_singleton q)⟩, fun m hm => ?_⟩
  rcases hON hm.1 with h | h
  · exact h
  · exact absurd h (Set.disjoint_left.1 hdisj hm.2)

/-- The conclusion of Lemma 7.2.11 holds when `T_R` is Hausdorff. -/
theorem isReducedEvenlyCovered_of_t2Space [T2Space X.ReducedMor] (φ₀ : Mor) :
    X.IsReducedEvenlyCovered φ₀ := by
  have hF : (X.reducedπ ⁻¹' {X.reducedπ φ₀}).Finite := X.finite_reducedπ_preimage φ₀
  have := X.PMor.metrizableSpace
  obtain ⟨A, hA, hAd⟩ := hF.t2_separation
  have hU₁ : ∀ φ, ∃ U : Set Mor, IsOpen U ∧ φ ∈ U ∧ closure U ⊆ A φ ∧ InjOn X.reducedπ U := by
    intro φ
    obtain ⟨W, V, σ, hφW, hS⟩ := X.isLocalScDiffeo_src φ
    obtain ⟨T, hT, hTc, hTs⟩ := exists_mem_nhds_isClosed_subset ((hA φ).2.mem_nhds (hA φ).1)
    refine ⟨interior T ∩ W, isOpen_interior.inter hS.isScSmoothOn.isOpen,
      ⟨mem_interior_iff_mem_nhds.2 hT, hφW⟩, ?_, (injOn_reducedπ hS).mono inter_subset_right⟩
    exact (closure_mono (inter_subset_left.trans interior_subset)).trans
      (hTc.closure_subset.trans hTs)
  choose U₁ hU₁o hφU₁ hU₁c hU₁i using hU₁
  obtain ⟨O, hO, hqO, hON⟩ := X.exists_preimage_reducedπ_subset_of_t2Space (X.reducedπ φ₀)
    (isOpen_biUnion fun φ _ => hU₁o φ) fun φ hφ => mem_iUnion₂.2 ⟨φ, hφ, hφU₁ φ⟩
  set V := O ∩ ⋂ φ ∈ X.reducedπ ⁻¹' {X.reducedπ φ₀}, X.reducedπ '' U₁ φ
  have hVo : IsOpen V :=
    hO.inter (hF.isOpen_biInter fun φ _ => X.isOpenMap_reducedπ _ (hU₁o φ))
  have hφ₀V : X.reducedπ φ₀ ∈ V := ⟨hqO, mem_iInter₂.2 fun φ hφ => ⟨φ, hφU₁ φ, hφ⟩⟩
  have hUo : ∀ φ, IsOpen (U₁ φ ∩ X.reducedπ ⁻¹' V) := fun φ =>
    (hU₁o φ).inter (hVo.preimage X.continuous_reducedπ)
  refine ⟨fun φ => U₁ φ ∩ X.reducedπ ⁻¹' V, V, hVo, hφ₀V, fun φ hφ => ⟨hUo φ, hφU₁ φ, ?_⟩,
    ?_, fun φ hφ => ⟨?_, ?_⟩, ?_⟩
  · rw [mem_preimage, show X.reducedπ φ = X.reducedπ φ₀ from hφ]
    exact hφ₀V
  · intro φ hφ ψ hψ hne
    exact (hAd hφ hψ hne).mono ((closure_mono inter_subset_left).trans (hU₁c φ))
      ((closure_mono inter_subset_left).trans (hU₁c ψ))
  · refine Subset.antisymm (image_subset_iff.2 fun m hm => hm.2) fun q hq => ?_
    obtain ⟨m, hm, rfl⟩ := mem_iInter₂.1 hq.2 φ hφ
    exact ⟨m, ⟨hm, hq⟩, rfl⟩
  · exact .of_continuous_injective_isOpenMap (X.continuous_reducedπ.comp continuous_subtype_val)
      (injOn_iff_injective.1 ((hU₁i φ).mono inter_subset_left))
      (X.isOpenMap_reducedπ.domRestrict (hUo φ))
  · intro m hm
    obtain ⟨φ, hφ, hmφ⟩ := mem_iUnion₂.1 (hON hm.1)
    exact mem_iUnion₂.2 ⟨φ, hφ, hmφ, hm⟩

/-- Conversely, if the conclusion of Lemma 7.2.11
holds at every unit `1_x`, then `𝐗^T` is closed. -/
theorem isClosed_nonEffectivePart_of_isReducedEvenlyCovered
    (h : ∀ x : Obj, X.IsReducedEvenlyCovered (X.unit x)) : IsClosed X.nonEffectivePart := by
  refine closure_subset_iff_isClosed.1 fun φ hφ => ?_
  obtain ⟨U, V, hVo, hV, hUo, -, hemb, hcov⟩ := h (X.src φ)
  have hF := X.finite_reducedπ_preimage (X.unit (X.src φ))
  have hc : Continuous fun ψ => X.reducedπ (X.unit (X.src ψ)) :=
    X.continuous_reducedπ.comp (X.continuous_unit.comp X.continuous_src)
  set N := (fun ψ => X.reducedπ (X.unit (X.src ψ))) ⁻¹' V
  have hNo : IsOpen N := hVo.preimage hc
  have hsub : N ∩ X.nonEffectivePart ⊆ ⋃ k ∈ X.reducedπ ⁻¹' {X.reducedπ (X.unit (X.src φ))},
      U k ∩ (N ∩ X.nonEffectivePart) := fun ψ hψ => by
    have hψV : X.reducedπ ψ ∈ V := by
      rw [X.mem_nonEffectivePart_iff_reducedπ.1 hψ.2]
      exact hψ.1
    obtain ⟨k, hk, hψk⟩ := mem_iUnion₂.1 (hcov hψV)
    exact mem_iUnion₂.2 ⟨k, hk, hψk, hψ⟩
  have hφc := closure_mono hsub (hNo.inter_closure ⟨(hV : φ ∈ N), hφ⟩)
  rw [hF.closure_biUnion] at hφc
  obtain ⟨k, hk, hφk⟩ := mem_iUnion₂.1 hφc
  obtain ⟨himg, he⟩ := hemb k hk
  have : Nonempty (U k) := ⟨⟨k, (hUo k hk).2⟩⟩
  set H := he.toOpenPartialHomeomorph ((U k).domRestrict X.reducedπ)
  have hrange : range ((U k).domRestrict X.reducedπ) = V := by
    rw [← himg, range_domRestrict]
  let f : Mor → Mor := fun ψ => (H.symm (X.reducedπ (X.unit (X.src ψ)))).1
  have hfc : ContinuousAt f φ := by
    have h' : ContinuousAt H.symm (X.reducedπ (X.unit (X.src φ))) := H.continuousAt_symm (by
      rw [IsOpenEmbedding.toOpenPartialHomeomorph_target, hrange]
      exact hV)
    exact continuous_subtype_val.continuousAt.comp
      (ContinuousAt.comp (f := fun ψ => X.reducedπ (X.unit (X.src ψ))) h' hc.continuousAt)
  have hfD : ∀ ψ ∈ U k ∩ (N ∩ X.nonEffectivePart), ψ = f ψ := fun ψ hψ => by
    change ψ = (H.symm (X.reducedπ (X.unit (X.src ψ)))).1
    rw [← X.mem_nonEffectivePart_iff_reducedπ.1 hψ.2.2]
    exact (congrArg Subtype.val
      (IsOpenEmbedding.toOpenPartialHomeomorph_left_inv _ he (x := ⟨ψ, hψ.1⟩))).symm
  have : (𝓝[U k ∩ (N ∩ X.nonEffectivePart)] φ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hφk
  have h1 : Tendsto f (𝓝[U k ∩ (N ∩ X.nonEffectivePart)] φ) (𝓝 (f φ)) :=
    hfc.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto f (𝓝[U k ∩ (N ∩ X.nonEffectivePart)] φ) (𝓝 φ) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).congr' (eventually_nhdsWithin_of_forall hfD)
  have hφf : φ = f φ := tendsto_nhds_unique h2 h1
  have hr := IsOpenEmbedding.toOpenPartialHomeomorph_right_inv _ he
    (x := X.reducedπ (X.unit (X.src φ))) (by rw [hrange]; exact hV)
  exact X.mem_nonEffectivePart_iff_reducedπ.2 ((congrArg X.reducedπ hφf).trans hr)

/-- **The conclusion of 2021 Lemma 7.2.11 holds at every morphism iff
`T_R` is Hausdorff.**  So Lemma 7.2.11 does not hold as we read it for every ep-groupoid
(`JumpingRetract.not_isReducedEvenlyCovered`). -/
theorem isReducedEvenlyCovered_iff_t2Space :
    (∀ φ₀ : Mor, X.IsReducedEvenlyCovered φ₀) ↔ T2Space X.ReducedMor :=
  ⟨fun h => X.proposition_7_2_17.2
    (X.isClosed_nonEffectivePart_of_isReducedEvenlyCovered fun _ => h _),
    fun _ => X.isReducedEvenlyCovered_of_t2Space⟩

/-- **2021 Lemma 7.2.11, p. 315 (new in the 2021 edition), with `T_R` Hausdorff as a
hypothesis**: the class of `φ₀` is finite and has neighbourhoods as in (1)–(3). -/
theorem lemma_7_2_11 [T2Space X.ReducedMor] (φ₀ : Mor) :
    (X.reducedπ ⁻¹' {X.reducedπ φ₀}).Finite ∧ X.IsReducedEvenlyCovered φ₀ :=
  ⟨X.finite_reducedπ_preimage φ₀, X.isReducedEvenlyCovered_of_t2Space φ₀⟩

/-! ### Appendix 7.6.4: raising the index -/

/-- **(7.24), 2021 p. 349**: `(𝐗^T)^1 ⊆ (𝐗^1)^T`.  If
`φ ∈ 𝐗_1` lies in `𝐗^T`, then `s = t` near `φ` in `𝐗`, hence in `𝐗¹`. -/
theorem mem_nonEffectivePart_liftOne_of_levelVal {φ : X.PMor.Level 1}
    (h : X.PMor.levelVal 1 φ ∈ X.nonEffectivePart) : φ ∈ X.liftOne.nonEffectivePart := by
  rw [X.liftOne.mem_nonEffectivePart_iff]
  filter_upwards [(MPolyfold.continuous_levelVal 1).continuousAt.eventually
    (X.mem_nonEffectivePart_iff.1 h)] with ψ hψ
  exact MPolyfold.level_ext hψ

namespace NaturalRep

variable {X} {x : Obj} (R : X.NaturalRep x)

open Classical in
/-- `Γ(g, ·)` on level `1`, a map `U(x)₁ → 𝐗¹` (`Γ(g, y) ∈ 𝐗_1` for `y ∈ X_1`); a unit
outside `U(x)₁`. -/
def levelOneΓ (g : X.Isotropy x) (y : X.PObj.Level 1) : X.PMor.Level 1 :=
  if hy : X.PObj.levelVal 1 y ∈ R.U then
    X.PMor.levelMk 1 (R.Γ g (X.PObj.levelVal 1 y))
      ((X.mem_levelSet_src_iff _ 1).1 (by rw [R.src_Γ g _ hy]; exact MPolyfold.levelVal_mem y))
  else X.liftOne.unit y

/-- `levelOneΓ` lifts `Γ(g, ·)` on `U(x)₁`. -/
theorem levelVal_levelOneΓ (g : X.Isotropy x) {y : X.PObj.Level 1} (hy : y ∈ R.liftU) :
    X.PMor.levelVal 1 (R.levelOneΓ g y) = R.Γ g (X.PObj.levelVal 1 y) := by
  simp only [levelOneΓ, dif_pos (show X.PObj.levelVal 1 y ∈ R.U from hy),
    MPolyfold.levelVal_levelMk]

/-- `Γ(g, ·)` is continuous on `U(x)₁ ⊆ X¹` into `𝐗¹`
(`IsScSmoothOn.levelOne`). -/
theorem continuousOn_levelOneΓ (g : X.Isotropy x) : ContinuousOn (R.levelOneΓ g) R.liftU :=
  ((R.isScSmoothOn_Γ g).levelOne fun _ hy => R.levelVal_levelOneΓ g hy).continuousOn

/-- `s(Γ(g, y)) = y` in `X¹`. -/
theorem liftOne_src_levelOneΓ (g : X.Isotropy x) {y : X.PObj.Level 1} (hy : y ∈ R.liftU) :
    X.liftOne.src (R.levelOneΓ g y) = y :=
  MPolyfold.level_ext (by rw [liftOne_src_val, R.levelVal_levelOneΓ g hy, R.src_Γ g _ hy])

/-- If `Γ(g, y) ∈ (𝐗¹)^T`, then `Φ(g) = id` near `y` in `X¹`. -/
theorem eventually_of_levelOneΓ_mem (g : X.Isotropy x) {y : X.PObj.Level 1} (hy : y ∈ R.liftU)
    (h : R.levelOneΓ g y ∈ X.liftOne.nonEffectivePart) :
    ∀ᶠ z in 𝓝 y, z ∈ R.liftU ∧ R.Φ g (X.PObj.levelVal 1 z) = X.PObj.levelVal 1 z := by
  have hc : ContinuousAt (R.levelOneΓ g) y :=
    (R.continuousOn_levelOneΓ g).continuousAt (R.isOpen_liftU.mem_nhds hy)
  filter_upwards [hc.eventually (X.liftOne.mem_nonEffectivePart_iff.1 h),
    R.isOpen_liftU.mem_nhds hy] with z hz hzU
  refine ⟨hzU, ?_⟩
  have h' := congrArg (X.PObj.levelVal 1) hz
  rw [liftOne_src_val, liftOne_tgt_val, R.levelVal_levelOneΓ g hzU, R.src_Γ g _ hzU,
    R.tgt_Γ g _ hzU] at h'
  exact h'.symm

/-- If `Φ(g) = id` near `y` in `X¹`, then `Γ(g, y) ∈ (𝐗¹)^T`. -/
theorem levelOneΓ_mem_of_eventually (g : X.Isotropy x) {y : X.PObj.Level 1} (hy : y ∈ R.liftU)
    (h : ∀ᶠ z in 𝓝 y, R.Φ g (X.PObj.levelVal 1 z) = X.PObj.levelVal 1 z) :
    R.levelOneΓ g y ∈ X.liftOne.nonEffectivePart := by
  obtain ⟨D, hDs, hDo, hyD⟩ := mem_nhds_iff.1 (inter_mem h (R.isOpen_liftU.mem_nhds hy))
  have hsrc : ∀ z ∈ D, X.liftOne.src (R.levelOneΓ g z) = z := fun z hz =>
    R.liftOne_src_levelOneΓ g (hDs hz).2
  have htgt : ∀ z ∈ D, X.liftOne.tgt (R.levelOneΓ g z) = z := fun z hz =>
    MPolyfold.level_ext (by
      rw [liftOne_tgt_val, R.levelVal_levelOneΓ g (hDs hz).2, R.tgt_Γ g _ (hDs hz).2]
      exact (hDs hz).1)
  let h' : X.liftOne.Isotropy y := ⟨R.levelOneΓ g y, hsrc y hyD, htgt y hyD⟩
  have hT : h' ∈ X.liftOne.trivialSet y := X.liftOne.mem_trivialSet_of_section hDo hyD
    ((R.continuousOn_levelOneΓ g).mono fun z hz => (hDs hz).2) hsrc htgt rfl
  exact ⟨y, h', hT, rfl⟩

end NaturalRep

/-- **`T_x^{X¹} ⊆ T_x`, 2021 pp. 349–350**, given that
`(𝐗¹)^T` is closed (LUC for `X¹`), and a natural representation `U(x)` with `U(x)₁` connected in
`X¹` and `U(x) ∩ X_1` dense in `U(x)`: `Φ(g)` is the identity near `x` in `X¹`, hence on
`U(x)₁` (connectedness, as in `hasLUC_of_isClosed`), hence on `U(x)` (density). -/
theorem levelVal_mem_nonEffectivePart_of_liftOne (hcl : IsClosed X.liftOne.nonEffectivePart)
    {φ : X.PMor.Level 1} (hφ : φ ∈ X.liftOne.nonEffectivePart)
    (R : X.NaturalRep (X.src (X.PMor.levelVal 1 φ))) (hconn : IsPreconnected R.liftU)
    (hdense : R.U ⊆ closure (R.U ∩ X.PObj.levelSet 1)) :
    X.PMor.levelVal 1 φ ∈ X.nonEffectivePart := by
  have hst : X.liftOne.src φ = X.liftOne.tgt φ := src_eq_tgt_of_mem_nonEffectivePart hφ
  have hst0 : X.src (X.PMor.levelVal 1 φ) = X.tgt (X.PMor.levelVal 1 φ) :=
    congrArg (X.PObj.levelVal 1) hst
  let g : X.Isotropy (X.src (X.PMor.levelVal 1 φ)) := ⟨X.PMor.levelVal 1 φ, rfl, hst0.symm⟩
  have hx₁ : X.liftOne.src φ ∈ R.liftU := R.mem_U
  have hΓx : R.levelOneΓ g (X.liftOne.src φ) = φ :=
    MPolyfold.level_ext ((R.levelVal_levelOneΓ g hx₁).trans (R.Γ_self g))
  set u := {y : X.PObj.Level 1 |
    ∀ᶠ z in 𝓝 y, z ∈ R.liftU ∧ R.Φ g (X.PObj.levelVal 1 z) = X.PObj.levelVal 1 z}
  have huo : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hsub : R.liftU ⊆ u := by
    refine hconn.subset_of_closure_inter_subset huo
      ⟨_, hx₁, R.eventually_of_levelOneΓ_mem g hx₁ (by rw [hΓx]; exact hφ)⟩ ?_
    rintro y ⟨hyc, hyU⟩
    have hc : ContinuousAt (R.levelOneΓ g) y :=
      (R.continuousOn_levelOneΓ g).continuousAt (R.isOpen_liftU.mem_nhds hyU)
    have himg : R.levelOneΓ g '' u ⊆ X.liftOne.nonEffectivePart := by
      rintro _ ⟨y', hy', rfl⟩
      exact R.levelOneΓ_mem_of_eventually g hy'.self_of_nhds.1 (hy'.mono fun z hz => hz.2)
    exact R.eventually_of_levelOneΓ_mem g hyU
      (hcl.closure_subset_iff.2 himg (mem_closure_image hc hyc))
  have hlev : EqOn (R.Φ g) id (R.U ∩ X.PObj.levelSet 1) := fun y hy =>
    (hsub (show X.PObj.levelMk 1 y hy.2 ∈ R.liftU from hy.1)).self_of_nhds.2
  have hall : EqOn (R.Φ g) id R.U := hlev.of_subset_closure
    (R.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn continuousOn_id inter_subset_left hdense
  exact ⟨X.src (X.PMor.levelVal 1 φ), g, ⟨R, fun y hy => hall hy⟩, rfl⟩

/-- The hypotheses that the text uses in Appendix 7.6.4 (2021 p. 349):
every `x ∈ X_1` has a natural representation `U(x)` with `U(x)₁ = U(x) ∩ X_1` connected in `X¹`
and dense in `U(x)`.  Satisfiable: `Examples.hasConnectedDenseLevelOneReps_point`. -/
def HasConnectedDenseLevelOneReps : Prop :=
  ∀ x : X.PObj.Level 1, ∃ R : X.NaturalRep (X.PObj.levelVal 1 x),
    IsPreconnected R.liftU ∧ R.U ⊆ closure (R.U ∩ X.PObj.levelSet 1)

/-- **`(𝐗^T)^1 = (𝐗^1)^T`, 2021 p. 350**, under LUC for `X¹` and
`HasConnectedDenseLevelOneReps`. -/
theorem nonEffectivePart_liftOne_eq (hcl : IsClosed X.liftOne.nonEffectivePart)
    (hR : X.HasConnectedDenseLevelOneReps) :
    X.liftOne.nonEffectivePart = X.PMor.levelVal 1 ⁻¹' X.nonEffectivePart := by
  ext φ
  refine ⟨fun h => ?_, X.mem_nonEffectivePart_liftOne_of_levelVal⟩
  obtain ⟨R, hc, hd⟩ := hR (X.liftOne.src φ)
  exact X.levelVal_mem_nonEffectivePart_of_liftOne hcl h R hc hd

/-- With `(𝐗^T)^1 = (𝐗^1)^T`, morphisms of `𝐗¹` are equivalent in `X¹` iff
they are equivalent in `X`. -/
theorem liftOne_reducedπ_eq_iff
    (hT : X.liftOne.nonEffectivePart = X.PMor.levelVal 1 ⁻¹' X.nonEffectivePart)
    {φ ψ : X.PMor.Level 1} :
    X.liftOne.reducedπ φ = X.liftOne.reducedπ ψ ↔
      X.reducedπ (X.PMor.levelVal 1 φ) = X.reducedπ (X.PMor.levelVal 1 ψ) := by
  rw [X.liftOne.reducedπ_eq_iff_comp_inv, X.reducedπ_eq_iff_comp_inv, hT]
  constructor
  · rintro ⟨ht, hk⟩
    have hc : X.liftOne.src (X.liftOne.inv ψ) = X.liftOne.tgt φ := by
      rw [X.liftOne.src_inv, ht]
    refine ⟨congrArg (X.PObj.levelVal 1) ht, ?_⟩
    rw [mem_preimage, X.liftOne_comp_val hc, X.liftOne_inv_val] at hk
    exact hk
  · rintro ⟨ht, hk⟩
    have ht' : X.liftOne.tgt φ = X.liftOne.tgt ψ := MPolyfold.level_ext ht
    have hc : X.liftOne.src (X.liftOne.inv ψ) = X.liftOne.tgt φ := by
      rw [X.liftOne.src_inv, ht']
    refine ⟨ht', ?_⟩
    rw [mem_preimage, X.liftOne_comp_val hc, X.liftOne_inv_val]
    exact hk

/-- The natural map `(𝐗¹)^R → 𝐗^R`, `[φ]₁ ↦ [φ]`. -/
def reducedLevelOneMap
    (hT : X.liftOne.nonEffectivePart = X.PMor.levelVal 1 ⁻¹' X.nonEffectivePart) :
    X.liftOne.ReducedMor → X.ReducedMor :=
  Quot.lift (fun φ => X.reducedπ (X.PMor.levelVal 1 φ)) fun _ _ h =>
    (X.liftOne_reducedπ_eq_iff hT).1 (Quot.sound h)

/-- **2021 Theorem 7.6.7, p. 351 (new in the 2021 edition), for `i = 1` and as
sets**: under LUC for `X¹` (the part of (SLUC) used) and `HasConnectedDenseLevelOneReps`,
`(𝐗^T)^1 = (𝐗^1)^T`, and `[φ]₁ ↦ [φ]` is a continuous injection `(𝐗¹)^R → 𝐗^R` onto
`π(𝐗_1)`.  The sc-diffeomorphism statement and `i ≥ 2` are `theorem_7_6_7_one` and
`EP.theorem_7_6_7` (`GapP2_ARaise.lean`, 2026-11-12). -/
theorem theorem_7_6_7 (hLUC : X.liftOne.IsLUC)
    (hR : X.HasConnectedDenseLevelOneReps) :
    ∃ hT : X.liftOne.nonEffectivePart = X.PMor.levelVal 1 ⁻¹' X.nonEffectivePart,
      (∀ φ, X.reducedLevelOneMap hT (X.liftOne.reducedπ φ) = X.reducedπ (X.PMor.levelVal 1 φ)) ∧
      Injective (X.reducedLevelOneMap hT) ∧ Continuous (X.reducedLevelOneMap hT) ∧
      range (X.reducedLevelOneMap hT) = X.reducedπ '' X.PMor.levelSet 1 := by
  have hT := X.nonEffectivePart_liftOne_eq (X.liftOne.proposition_7_2_21.1 hLUC) hR
  refine ⟨hT, fun _ => rfl, ?_, ?_, ?_⟩
  · rintro ⟨φ⟩ ⟨ψ⟩ h
    exact (X.liftOne_reducedπ_eq_iff hT).2 h
  · exact continuous_quot_lift _
      (X.continuous_reducedπ.comp (MPolyfold.continuous_levelVal 1))
  · ext q
    constructor
    · rintro ⟨⟨φ⟩, rfl⟩
      exact ⟨_, MPolyfold.levelVal_mem φ, rfl⟩
    · rintro ⟨ψ, hψ, rfl⟩
      exact ⟨X.liftOne.reducedπ (X.PMor.levelMk 1 ψ hψ), rfl⟩

/-- **2021 Corollary 7.6.8, p. 351, for `i = 1` and as sets**, with the
implication from (ZHOU) (defined in §7.4) to LUC for `X¹` as the hypothesis `hSLUC`. -/
theorem corollary_7_6_8 {Zhou : Prop} (hZ : Zhou) (hSLUC : Zhou → X.liftOne.IsLUC)
    (hR : X.HasConnectedDenseLevelOneReps) :
    ∃ hT : X.liftOne.nonEffectivePart = X.PMor.levelVal 1 ⁻¹' X.nonEffectivePart,
      (∀ φ, X.reducedLevelOneMap hT (X.liftOne.reducedπ φ) = X.reducedπ (X.PMor.levelVal 1 φ)) ∧
      Injective (X.reducedLevelOneMap hT) ∧ Continuous (X.reducedLevelOneMap hT) ∧
      range (X.reducedLevelOneMap hT) = X.reducedπ '' X.PMor.levelSet 1 :=
  X.theorem_7_6_7 (hSLUC hZ) hR

namespace Examples

/-- The trivial ep-groupoid of a point. -/
abbrev pointEpGroupoid : EpGroupoid Unit Unit := trivial (discretePolyfold Unit)

/-- `X¹` of the point ep-groupoid has LUC. -/
theorem isLUC_liftOne_point : pointEpGroupoid.liftOne.IsLUC :=
  pointEpGroupoid.liftOne.proposition_7_2_21.2
    (Set.Subsingleton.isClosed fun _ _ _ _ => MPolyfold.level_ext (Subsingleton.elim _ _))

/-- The point ep-groupoid satisfies
`HasConnectedDenseLevelOneReps`. -/
theorem hasConnectedDenseLevelOneReps_point :
    pointEpGroupoid.HasConnectedDenseLevelOneReps := fun x => by
  obtain ⟨R, -⟩ := pointEpGroupoid.theorem_7_1_13 (pointEpGroupoid.PObj.levelVal 1 x) isOpen_univ
    (mem_univ _)
  refine ⟨R, Set.Subsingleton.isPreconnected fun _ _ _ _ =>
    MPolyfold.level_ext (Subsingleton.elim _ _), ?_⟩
  have h1 : pointEpGroupoid.PObj.levelSet 1 = univ := discretePolyfold_levelSet 1
  rw [h1, inter_univ]
  exact subset_closure

/-- **The hypotheses of `theorem_7_6_7` are satisfiable** (the point
ep-groupoid). -/
theorem theorem_7_6_7_point :
    ∃ hT : pointEpGroupoid.liftOne.nonEffectivePart =
        pointEpGroupoid.PMor.levelVal 1 ⁻¹' pointEpGroupoid.nonEffectivePart,
      Injective (pointEpGroupoid.reducedLevelOneMap hT) := by
  obtain ⟨hT, -, hinj, -⟩ :=
    pointEpGroupoid.theorem_7_6_7 isLUC_liftOne_point hasConnectedDenseLevelOneReps_point
  exact ⟨hT, hinj⟩

end Examples

end EpGroupoid

end Polyfold

/-! ### Appendix 7.6.3 and Remark 7.2.19 -/

namespace Polyfold.EpGroupoid.Examples.JumpingRetract

/-- In `JumpingRetract.X` the class of `(1, o₀)` is `{(1, o₀)}`. -/
theorem reducedπ_preimage_one :
    X.reducedπ ⁻¹' {X.reducedπ ((1 : ℤˣ), o₀)} = {((1 : ℤˣ), o₀)} := by
  ext ψ
  simp only [mem_preimage, mem_singleton_iff]
  constructor
  · intro h
    obtain ⟨k, hk, hc, he⟩ := EpGroupoid.reducedRel_iff.1 (X.reducedπ_eq_iff.1 h)
    have hkk := EpGroupoid.src_eq_tgt_of_mem_nonEffectivePart hk
    have hk2 : k.2 = o₀ := hkk.trans hc.symm
    rcases Int.units_eq_one_or k.1 with h1 | h1
    · rw [he]
      change ((1 : ℤˣ) * k.1, k.2) = _
      rw [h1, hk2, one_mul]
    · exfalso
      have hk' : k = ((-1 : ℤˣ), o₀) := Prod.ext h1 hk2
      exact not_mem_nonEffectivePart (hk' ▸ hk)
  · rintro rfl
    rfl

/-- **The conclusion of 2021 Lemma 7.2.11 fails at `(1, o₀)`**:
`[(1, y_n)] = [(−1, y_n)] → [(1, o₀)]`, so (3) puts both `(±1, y_n)` into `U((1, o₀))`, on which
`π` is injective by (2). -/
theorem not_isReducedEvenlyCovered : ¬ X.IsReducedEvenlyCovered ((1 : ℤˣ), o₀) := by
  rintro ⟨U, V, hVo, hV, -, -, hemb, hcov⟩
  rw [reducedπ_preimage_one] at hemb hcov
  obtain ⟨-, hemb⟩ := hemb _ rfl
  have hcov' : X.reducedπ ⁻¹' V ⊆ U ((1 : ℤˣ), o₀) := by simpa using hcov
  have h2 : Tendsto (fun n => X.reducedπ ((1 : ℤˣ), yn n)) atTop
      (𝓝 (X.reducedπ ((1 : ℤˣ), o₀))) :=
    (X.continuous_reducedπ.tendsto _).comp (tendsto_const_nhds.prodMk_nhds tendsto_yn)
  obtain ⟨n, hn⟩ := (h2.eventually (hVo.mem_nhds hV)).exists
  have ha : ((1 : ℤˣ), yn n) ∈ U ((1 : ℤˣ), o₀) := hcov' hn
  have hb : ((-1 : ℤˣ), yn n) ∈ U ((1 : ℤˣ), o₀) := hcov' (by
    rw [mem_preimage, reducedπ_eq]
    exact hn)
  have he := hemb.injective (a₁ := ⟨_, hb⟩) (a₂ := ⟨_, ha⟩) (reducedπ_eq n)
  have h1 : (-1 : ℤˣ) = 1 := congrArg (fun p : U ((1 : ℤˣ), o₀) => p.1.1) he
  exact absurd h1 (by decide)

/-- `(−1, o₀) ∈ cl 𝐗^T` (the point `{1} × {(0, 0)}` of `cl(𝐗^T) ∖ 𝐗^T` in
2021 Appendix 7.6.3). -/
theorem mem_closure_nonEffectivePart : ((-1 : ℤˣ), o₀) ∈ closure X.nonEffectivePart :=
  mem_closure_of_tendsto (tendsto_const_nhds.prodMk_nhds tendsto_yn)
    (Eventually.of_forall mem_nonEffectivePart)

/-- **2021 Appendix 7.6.3, p. 348, for our analogue of Zhou's example**:
`𝐗^T` is not closed. -/
theorem not_isClosed_nonEffectivePart : ¬ IsClosed X.nonEffectivePart := fun h =>
  not_mem_nonEffectivePart (h.closure_subset mem_closure_nonEffectivePart)

/-- **`JumpingRetract.X` does not have LUC**, consistently with Theorem 7.2.22 and
`not_t2Space_reducedMor`. -/
theorem not_isLUC : ¬ X.IsLUC := fun h =>
  not_isClosed_nonEffectivePart (X.proposition_7_2_21.1 h)

end Polyfold.EpGroupoid.Examples.JumpingRetract

namespace Polyfold.EpGroupoid.Examples

/-- **2021 Remark 7.2.19, p. 321 (new in the 2021 edition)**: not every ep-groupoid
has the local unique continuation property (`JumpingRetract.not_isLUC`). -/
theorem remark_7_2_19 :
    ∃ (Obj Mor : Type) (_ : TopologicalSpace Obj) (_ : T2Space Obj) (_ : ParacompactSpace Obj)
      (_ : TopologicalSpace Mor) (_ : T2Space Mor) (_ : ParacompactSpace Mor)
      (X : EpGroupoid Obj Mor), ¬ X.IsLUC :=
  ⟨_, _, _, inferInstance, inferInstance, _, inferInstance, inferInstance, JumpingRetract.X,
    JumpingRetract.not_isLUC⟩

end Polyfold.EpGroupoid.Examples
