import Polyfold.Chapter7.Groupoid
import Polyfold.Chapter5.PartitionsOfUnity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 7: **Definitions 7.3–7.17** (pp. 226–251), the data of **Theorem 7.1** (natural
representation, p. 231) and the claims of pp. 227–228 that Definition 7.5 needs.  There is no
2014 preprint of Part II; numbers and pages are the 2017 text's.  Pages: Definition 7.3 pp.
226–227, 7.4 p. 227, 7.5–7.7 p. 228, 7.8 p. 236, 7.9–7.10 p. 237, 7.11 p. 239, 7.12 p. 241,
7.13 p. 244, 7.14 p. 247, 7.15 p. 249, 7.16 pp. 250–251, 7.17 p. 251.

# Ep-groupoids

## The text, paraphrased

(Definition 7.3) An ep-groupoid is a groupoid `(X, 𝐗)` with M-polyfold structures on `X` and `𝐗`
such that (1) `s, t : 𝐗 → X` are local sc-diffeomorphisms; (2) `u` and `ι` are sc-smooth;
(3) every `x` has an open neighbourhood `V(x)` with `t : s⁻¹(cl_X V(x)) → X` proper; (4) `m` is
sc-smooth on `𝐗 ₛ×ₜ 𝐗`, an M-polyfold since `s` is a local sc-diffeomorphism.  (p. 227)
Every `φ : x → y` has open `U(φ)`, `U(x)`, `U(y)` with `s : U(φ) → U(x)`, `t : U(φ) → U(y)`
sc-diffeomorphisms, and `φ̂ = t ∘ (s|U(φ))⁻¹ : U(x) → U(y)`; for smooth `φ`, `Tφ := Tφ̂(x)`
(Definition 7.4).  (pp. 227–228) `ml(s φ) = ml(φ) = ml(t φ)` and `d_X(s φ) = d_𝐗(φ) = d_X(t φ)`;
(Definition 7.5) `d_{|X|}(|x|) = d_X(x)`.  (Definition 7.6) Tame: `X` is tame.  (Definition 7.7)
`EP`: ep-groupoids and functors sc-smooth on objects and morphisms.  (Theorem 7.1) For every open
`V ∋ x` there are an open `U ⊆ V` of `x`, a homomorphism `Φ : G_x → Diff_sc(U)` and an sc-smooth
`Γ : G_x × U → 𝐗` with `Γ(g, x) = g`, `s Γ(g, y) = y`, `t Γ(g, y) = Φ(g)(y)`, and every `h : y → z`
between points of `U` is `Γ(g, y)` for a unique `g`.  (Definition 7.8) A natural representation
of a finite set `Y` of isomorphic objects: Proposition 7.5's functor.  (Definition 7.9) A local
uniformizer: a fully faithful `Ψ_x : G_x ⋉ U(x) → X` inducing `|U(x)|_{G_x ⋉ U(x)} ≅ π(U(x))`.
(Definition 7.10) An ep-subgroupoid: a saturated sub-M-polyfold `A ⊆ X`.  (Definition 7.11)
Effective: for `x`, `g ∈ G_x ∖ {1_x}` and every open `𝐔(g)` there is `ψ ∈ 𝐔(g)` with `s ψ ≠ t ψ`.
(Definition 7.12) `g` acts trivially if `Φ(g) = 1` for some `U(x)` with the natural action; `T_x`
the elements acting trivially; `𝐗^T = ⋃ T_x`; `φ ∼ φ'` iff `s φ = s φ' = x` and `φ = φ' ∘ g`,
`g ∈ T_x`; `𝐗^R = 𝐗/∼`.  (Definition 7.13) `G_x^eff = G_x/T_x`.  (Definition 7.14) `K ⊆ |X|`
component compact: `K ∩ C` compact for every component `C`.  (Definition 7.15) Paracompact orbit
space.  (Definition 7.16) Sc-smooth partitions of unity: every saturated open cover has a
subordinate sc-smooth partition of unity `(β_λ)`, (1) each point has a saturated open
neighbourhood meeting finitely many `supp β_λ`, (2) each `β_λ` is constant on orbits.
(Definition 7.17) `Q ⊆ X` is proper if `t : s⁻¹(Q) → X` is proper; open `U` has the properness
property if `cl_X(U)` is proper.

## What is formalized

* **Definition 7.3**: `EpGroupoid Obj Mor` (extends `GroupoidStr`); condition (4) literally as
  `IsScSmoothComp`, its sheet form `IsScSmoothCompSheet`, `isScSmoothComp_iff_sheet`;
  `EpGroupoid.isScSmoothMap_src`, `_tgt`, `continuous_src`, `_tgt`, `_unit`, `_inv`,
  `isScSmoothCompSheet`, `continuous_π`.
* **Definition 7.4**: `EpGroupoid.Sheet` (`U(φ)`, `U(x)`, `U(y)` with the inverses of `s` and `t`),
  `exists_sheet`, `sheetAt`, `Sheet.hat`, `Sheet.isScDiffeoOn_hat`, `EpGroupoid.hat` (`φ̂`),
  `hat_src`, `EpGroupoid.tangentMor` (`Tφ`).
* pp. 227–228: `mem_levelSet_src_iff`, `mem_levelSet_tgt_iff`, `degIndex_src`, `degIndex_tgt`,
  `orbitLevel` (`|X_k|`); **Definition 7.5**: `degIndexOrbit`, `degIndexOrbit_π`.
* **Definition 7.6**: `EpGroupoid.IsTame`.  **Definition 7.7**: `EpFunctor`, `EpFunctor.id`,
  `.comp`, `.ext`, the bundled `EP` with `CategoryTheory.LargeCategory EP`.
* **Theorem 7.1, the data**: `EpGroupoid.NaturalRep X x`; `Φ_one`, `Φ_self`, `mapsTo_Φ`,
  `Γ_mem_morOn`, the action of `G_x` on `U` (`MulAction`), `NaturalRep.translationGroupoid`
  (`G_x ⋉ U(x)`).
* **Definition 7.8**: `NaturalRepFinite X Y V`.  **Definition 7.9**: `LocalUniformizer X x`.
* **Definition 7.10**: `IsEpSubgroupoid`, `isEpSubgroupoid_univ`.  **Definition 7.11**:
  `IsEffective` (regular objects: `GroupoidStr.IsRegular`, `regularSet`).
* **Definition 7.12**: `ActsTrivially`, `trivialSet` (`T_x`), `one_mem_trivialSet`,
  `nonEffectivePart` (`𝐗^T`), `ReducedRel`, `ReducedMor` (`𝐗^R`).  **Definition 7.13**:
  `EffIsotropy`.  **Definition 7.14**: `IsComponentCompact`.  **Definition 7.15**:
  `HasParacompactOrbitSpace`.  **Definition 7.16**: `HasScPartitionsOfUnity`.
  **Definition 7.17**: `IsProperSubset`, `HasPropernessProperty`, `exists_hasPropernessProperty`.
* Witnesses (PLAN II.5): `EpGroupoid.trivial P` (`𝐗 = X`, `s = t = id`) for every M-polyfold;
  `isTame_trivial`, `isTame_trivial_rn` (on `ℝⁿ`), `isEffective_trivial`, `regularSet_trivial`,
  `isProperSubset_trivial`, `hasPropernessProperty_trivial`, `trivialOrbitHomeomorph`,
  `hasParacompactOrbitSpace_trivial`, `hasScPartitionsOfUnity_trivial`, `trivialNaturalRep`,
  `actsTrivially_trivial`, `trivialNaturalRepFinite` (for connected `X`, e.g. `ℝⁿ`).

## Reading

* **(1), (2)** are Part I's `IsLocalScDiffeo` and `IsScSmoothMap`.  The text's "in particular all
  structure maps are sc-smooth" is `isScSmoothMap_src`, `isScSmoothMap_tgt`.
* **(3)** (PLAN P3) is `IsProperMap ((s ⁻¹' cl V).domRestrict t)` for *some* open `V ∋ x`,
  existential per point as in the text (a universal reading, "for every neighbourhood", fails for
  the pair groupoid of `ℤ`; PLAN II.5, 4).  Definition 7.17 uses the same form.
* **(4)** (P5) is stated literally on the sub-M-polyfold `𝐗 ₛ×ₜ 𝐗 = fibredProduct src tgt` of
  `𝐗 × 𝐗` (Proposition 2.15 [2.46] of the text; Definition 7.3 cites "[38], Lemma 2.8", possible
  misprint), the paracompactness instances of `𝐗 × 𝐗` and of the subtype supplied inside the
  definition by `paracompactSpace_prod`, `paracompactSpace_subtype` (Theorem 2.2 [2.16]).  The
  **sheet form** `IsScSmoothCompSheet`: for every sc-diffeomorphism `s : W → V` with inverse `σ`,
  `ψ ↦ m(σ(t ψ), ψ)` is sc-smooth on `t⁻¹(V)`.  It is equivalent (`isScSmoothComp_iff_sheet`,
  through `isScDiffeoOn_snd_fibredProduct`); its "for every `σ`" is no vacuity risk, being
  equivalent to the literal (4), which the trivial ep-groupoid satisfies.
* **Definition 7.4.**  `φ̂` depends on the chosen sheet only as a germ; `hat` uses the sheet chosen
  by `sheetAt`.  `Tφ = Tφ̂(s φ)` is read through the chain rule as `Tt ∘ (Ts|T_φ𝐗)⁻¹`
  (`φ̂ = t ∘ (s|U(φ))⁻¹`), with Part I's tangent maps `Ts, Tt : T𝐗 → TX` of the sc-smooth `s`, `t`
  (`MPolyfold.tangentMap`); off the image of `T_φ𝐗` it is the identity (junk).  Its linearity and
  that `Ts` is injective on `T_φ𝐗` are Chapter 8 (§8.1, the tangent `TX`).
* pp. 227–228: the invariance of levels and of `d` along `s` and `t` is proved here (Proposition
  2.7 [2.24] along a sheet), since Definition 7.5 needs it for `Quotient.lift`.
* **Definition 7.6** is `PObj.IsTame` (an equivalent tame atlas exists, Definition 2.19 [2.37]):
  existential, never "every chart is tame" (PLAN II.5, 1).  The text's "then `𝐗` is tame" is
  `LocalDiffeo.lean`.
* **Definition 7.7**: an `EpFunctor` is a `GroupoidFunctor` sc-smooth on objects and on morphisms.
  The remark after it ("sc-smooth on objects suffices") is not formalized here: as we read it, it
  does not hold without continuity on morphisms (PLAN II.6, 1).  `EP` is a `LargeCategory` on
  bundled ep-groupoids (P2).
* **Theorem 7.1's data** (P6) is `NaturalRep`: `U` open and **connected** (as we read it, the
  homomorphism property and the uniqueness of `(Φ, Γ)` need it; PLAN II.6, 3), `Φ g` an
  sc-diffeomorphism of `U` with inverse `Φ g⁻¹`, `Φ(gh) = Φ(g) ∘ Φ(h)` on `U`.  "`Γ` is sc-smooth
  on `G_x × U`" is read on each sheet `{g} × U` (`isScSmoothOn_Γ`); `G_x × U` as an M-polyfold is
  `Discrete.lean`.  `Γ` and `Φ` are total maps whose values off `U` are not used.  That `Γ` is a
  functor `G_x ⋉ U → X` (p. 232) is not a field: it follows from connectedness (`NaturalRep.lean`).
  "`U(x)` equipped with the natural `G_x`-action" (Lemmas 7.3, 7.4, 7.10, Proposition 7.6,
  Definitions 7.9, 7.12) is always a `NaturalRep` datum (PLAN II.5, 6).
* **Definition 7.8**: `NaturalRepFinite X Y V` records Proposition 7.5's functor `f` (`F ψ` for
  morphisms `ψ` between points of `Y`), the neighbourhoods `U(y)` and the components `𝐔(ψ)` with
  the inverses `srcInv ψ` of `s|𝐔(ψ)`; "decomposes into the connected components `𝐔(ψ)`" is read
  as: the `𝐔(ψ)` are open, connected, pairwise disjoint and cover the morphisms between points of
  `⋃ U(y)`.  Property (1) is `natural`.
* **Definition 7.9**: `Ψ_x` is the inclusion on objects (so its image is `U(x)` and `|U(x)| =
  π(U(x))`), full and faithful (Mathlib's `Functor.Full`, `Functor.Faithful` of the bridge);
  "induces a homeomorphism onto `π(U(x))`" is an embedding with range `π(U(x))`.  The text's
  "`Ψ_x ◦ G_x ⋉ U(x) → X`" is read as `Ψ_x : G_x ⋉ U(x) → X` (possible misprint).
* **Definition 7.12**: `T_x` is the *set* `{g | ∃ natural representation with Φ(g) = id on U}`.
  That it is a normal subgroup, the kernel of `Φ` for small `U(x)` (p. 241), needs Theorem 7.1 and
  the uniqueness of `(Φ, Γ)`; it is proved in `Reduced.lean`.  Hence `∼` is `ReducedRel` (a
  relation; an equivalence relation once `T_x` is a subgroup) and `𝐗^R` is `Quot ReducedRel`.
* **Definition 7.13**: `G_x/T_x` is `G_x ⧸ normalClosure(T_x)`, which is `G_x/T_x` once `T_x` is
  shown a normal subgroup.
* **Definition 7.14**: the components of `|X|` are `connectedComponent z`.
* **Definition 7.15**: Mathlib's `ParacompactSpace` does not include Hausdorff, as the text
  stipulates ("We do not require a paracompact space to be Hausdorff").
* **Definition 7.16**: index types `ι : Type u` (as Part I's `AdmitsScPartitionsOfUnity`); `supp`
  is `tsupport`; "βλ(z) = βλ(y) if `y, z` are isomorphic" is `β λ (s φ) = β λ (t φ)`.  The
  hypothesis "for every saturated open cover there is …" is satisfiable:
  `hasScPartitionsOfUnity_trivial` reduces it for the trivial ep-groupoid to Part I's
  `AdmitsScPartitionsOfUnity` (for `ℝⁿ` in `LocalDiffeo.lean`).
* **Witnesses**: the trivial ep-groupoid exists on every M-polyfold; a finite group acting on an
  M-polyfold needs `G × U` as an M-polyfold (`Discrete.lean`) and is in `NonVacuity.lean` (W5).
-/

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u v w

/-! ### Sc-diffeomorphisms between open sets: locality, restriction, composition -/

section Helpers

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

/-- Sc-smoothness on an open set is local. -/
private theorem isScSmoothOn_of_local {f : X → Y} {U : Set X} (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ W : Set X, x ∈ W ∧ P.IsScSmoothOn Q f W) : P.IsScSmoothOn Q f U := by
  have hcont : ContinuousOn f U := fun x hx => by
    obtain ⟨W, hxW, hW⟩ := h x hx
    exact (hW.continuousOn.continuousAt (hW.isOpen.mem_nhds hxW)).continuousWithinAt
  refine MPolyfold.IsScSmoothOn.of_exists_charts hU hcont fun x hx => ?_
  obtain ⟨W, hxW, hW⟩ := h x hx
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  obtain ⟨ψ, hψ, hfx⟩ := Q.exists_isChart_mem_source (f x)
  have hVo : IsOpen ((W ∩ U ∩ φ.source) ∩ f ⁻¹' ψ.source) :=
    (hW.continuousOn.mono fun y hy => hy.1.1).isOpen_inter_preimage
      ((hW.isOpen.inter hU).inter φ.isOpen_source) ψ.isOpen_source
  exact ⟨φ, ψ, _, hφ, hψ, hVo, ⟨⟨⟨hxW, hx⟩, hxφ⟩, hfx⟩, fun y hy => ⟨hy.1.1.2, hy.1.2⟩,
    fun y hy => hy.2, hW.smooth φ ψ hφ hψ _ hVo (fun y hy => ⟨hy.1.1.1, hy.1.2⟩) fun y hy => hy.2⟩

/-- The restriction of an sc-diffeomorphism `U → V` to an open `W ⊆ U`. -/
private theorem isScDiffeoOn_restrict {f : X → Y} {g : Y → X} {U W : Set X} {V : Set Y}
    (h : P.IsScDiffeoOn Q f g U V) (hW : IsOpen W) (hWU : W ⊆ U) :
    P.IsScDiffeoOn Q f g W (V ∩ g ⁻¹' W) where
  isScSmoothOn := h.isScSmoothOn.mono hW hWU
  isScSmoothOn_inv := h.isScSmoothOn_inv.mono
    (h.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage h.isScSmoothOn_inv.isOpen hW)
    inter_subset_left
  mapsTo x hx := ⟨h.mapsTo (hWU hx), by rw [mem_preimage, h.left_inv x (hWU hx)]; exact hx⟩
  mapsTo_inv _ hy := hy.2
  left_inv x hx := h.left_inv x (hWU hx)
  right_inv y hy := h.right_inv y hy.1

/-- The composition of sc-diffeomorphisms `U → V → W`. -/
private theorem isScDiffeoOn_comp {f : X → Y} {g : Y → X} {f' : Y → Z} {g' : Z → Y}
    {U : Set X} {V : Set Y} {W : Set Z} (h : P.IsScDiffeoOn Q f g U V)
    (h' : Q.IsScDiffeoOn S f' g' V W) : P.IsScDiffeoOn S (f' ∘ f) (g ∘ g') U W where
  isScSmoothOn := MPolyfold.IsScSmoothOn.comp h'.isScSmoothOn h.isScSmoothOn h.mapsTo
  isScSmoothOn_inv := MPolyfold.IsScSmoothOn.comp h.isScSmoothOn_inv h'.isScSmoothOn_inv
    h'.mapsTo_inv
  mapsTo := h'.mapsTo.comp h.mapsTo
  mapsTo_inv := h.mapsTo_inv.comp h'.mapsTo_inv
  left_inv x hx := by
    simp only [Function.comp_apply, h'.left_inv _ (h.mapsTo hx), h.left_inv x hx]
  right_inv z hz := by
    simp only [Function.comp_apply, h.right_inv _ (h'.mapsTo_inv hz), h'.right_inv z hz]

variable (P) in
private theorem isScDiffeoOn_id : P.IsScDiffeoOn P id id univ univ :=
  ⟨MPolyfold.isScSmoothMap_id, MPolyfold.isScSmoothMap_id, mapsTo_id _, mapsTo_id _,
    fun _ _ => rfl, fun _ _ => rfl⟩

end Helpers

/-! ### Condition (4) of Definition 7.3 and its sheet form -/

section Composition

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **Definition 7.3 (4)**, literally: the multiplication `m(φ, ψ) = φ ∘ ψ` is sc-smooth on the
fibred product `𝐗 ₛ×ₜ 𝐗 = {(φ, ψ) | s φ = t ψ}`, a sub-M-polyfold of `𝐗 × 𝐗` since `s` is a local
sc-diffeomorphism (Proposition 2.15 [2.46], `MPolyfold.isSubMPolyfold_fibredProduct`). -/
def IsScSmoothComp (PObj : MPolyfold Obj) (PMor : MPolyfold Mor) (src tgt : Mor → Obj)
    (comp : Mor → Mor → Mor) (hs : PMor.IsLocalScDiffeo PObj src)
    (ht : PMor.IsScSmoothMap PObj tgt) : Prop :=
  letI := MPolyfold.paracompactSpace_prod PMor PMor
  letI := (PMor.prod PMor).paracompactSpace_subtype (MPolyfold.fibredProduct src tgt)
  (MPolyfold.subPolyfold (MPolyfold.isSubMPolyfold_fibredProduct hs ht)).IsScSmoothMap PMor
    fun p => comp p.1.1 p.1.2

/-- **Definition 7.3 (4), sheet form**: for every sc-diffeomorphism `s : W → V` (a sheet of `s`)
with inverse `σ`, the map `ψ ↦ m(σ(t ψ), ψ)` is sc-smooth on `t⁻¹(V)`. -/
def IsScSmoothCompSheet (PObj : MPolyfold Obj) (PMor : MPolyfold Mor) (src tgt : Mor → Obj)
    (comp : Mor → Mor → Mor) : Prop :=
  ∀ (σ : Obj → Mor) (W : Set Mor) (V : Set Obj), PMor.IsScDiffeoOn PObj src σ W V →
    PMor.IsScSmoothOn PMor (fun ψ => comp (σ (tgt ψ)) ψ) (tgt ⁻¹' V)

/-- **The literal condition (4) and its sheet form are equivalent.** -/
theorem isScSmoothComp_iff_sheet {PObj : MPolyfold Obj} {PMor : MPolyfold Mor}
    {src tgt : Mor → Obj} {comp : Mor → Mor → Mor} (hs : PMor.IsLocalScDiffeo PObj src)
    (ht : PMor.IsScSmoothMap PObj tgt) :
    IsScSmoothComp PObj PMor src tgt comp hs ht ↔ IsScSmoothCompSheet PObj PMor src tgt comp := by
  let _ := MPolyfold.paracompactSpace_prod PMor PMor
  let _ := (PMor.prod PMor).paracompactSpace_subtype (MPolyfold.fibredProduct src tgt)
  have hA := MPolyfold.isSubMPolyfold_fibredProduct hs ht
  have htc : Continuous tgt := continuousOn_univ.1 ht.continuousOn
  constructor
  · intro h σ W V hd
    have h' : (MPolyfold.subPolyfold hA).IsScSmoothMap PMor fun p => comp p.1.1 p.1.2 := h
    refine isScSmoothOn_of_local (hd.isScSmoothOn_inv.isOpen.preimage htc) fun ψ hψ => ?_
    let a₀ : MPolyfold.fibredProduct src tgt := ⟨(σ (tgt ψ), ψ), hd.right_inv _ hψ⟩
    have hD := MPolyfold.isScDiffeoOn_snd_fibredProduct hA hd ht a₀
    refine ⟨tgt ⁻¹' V, hψ, ?_⟩
    refine (MPolyfold.IsScSmoothOn.comp h' hD.isScSmoothOn_inv (mapsTo_univ _ _)).congr
      fun y hy => ?_
    simp only [Function.comp_apply]
    rw [(MPolyfold.fibredSubDataL hd ht).retractInto_val a₀ ⟨hd.mapsTo_inv hy, hy⟩]
    rfl
  · intro h
    change (MPolyfold.subPolyfold hA).IsScSmoothMap PMor _
    refine isScSmoothOn_of_local isOpen_univ fun a _ => ?_
    have ha : src a.1.1 = tgt a.1.2 := a.2
    obtain ⟨W, V, σ, haW, hd⟩ := hs a.1.1
    have hD := MPolyfold.isScDiffeoOn_snd_fibredProduct hA hd ht a
    refine ⟨Subtype.val ⁻¹' (W ×ˢ (tgt ⁻¹' V)), ⟨haW, ?_⟩, ?_⟩
    · change tgt a.1.2 ∈ V
      rw [← ha]
      exact hd.mapsTo haW
    · refine (MPolyfold.IsScSmoothOn.comp (h σ W V hd) hD.isScSmoothOn
        fun b hb => hb.2).congr fun b hb => ?_
      have hb' : src b.1.1 = tgt b.1.2 := b.2
      simp only [Function.comp_apply]
      rw [← hb', hd.left_inv _ hb.1]

end Composition

/-! ### Definition 7.3 -/

/-- **Definition 7.3 (ep-groupoid)**: a groupoid with M-polyfold structures `PObj` on the objects
and `PMor` on the morphisms such that (1) `s, t` are local sc-diffeomorphisms, (2) `u` and `ι` are
sc-smooth, (3) every object `x` has an open `V(x) ∋ x` with `t : s⁻¹(cl V(x)) → X` proper, and
(4) `m` is sc-smooth on `𝐗 ₛ×ₜ 𝐗`. -/
structure EpGroupoid (Obj Mor : Type u) [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    extends GroupoidStr Obj Mor where
  /-- The M-polyfold structure of the object space `X`. -/
  PObj : MPolyfold Obj
  /-- The M-polyfold structure of the morphism space `𝐗`. -/
  PMor : MPolyfold Mor
  isLocalScDiffeo_src : PMor.IsLocalScDiffeo PObj src
  isLocalScDiffeo_tgt : PMor.IsLocalScDiffeo PObj tgt
  isScSmoothMap_unit : PObj.IsScSmoothMap PMor unit
  isScSmoothMap_inv : PMor.IsScSmoothMap PMor inv
  exists_isProperMap : ∀ x : Obj, ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧
    IsProperMap ((src ⁻¹' closure V).domRestrict tgt)
  isScSmoothComp : IsScSmoothComp PObj PMor src tgt comp isLocalScDiffeo_src
    isLocalScDiffeo_tgt.isScSmoothMap

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! #### The structure maps -/

theorem isScSmoothMap_src : X.PMor.IsScSmoothMap X.PObj X.src :=
  X.isLocalScDiffeo_src.isScSmoothMap

theorem isScSmoothMap_tgt : X.PMor.IsScSmoothMap X.PObj X.tgt :=
  X.isLocalScDiffeo_tgt.isScSmoothMap

theorem continuous_src : Continuous X.src := X.isLocalScDiffeo_src.continuous

theorem continuous_tgt : Continuous X.tgt := X.isLocalScDiffeo_tgt.continuous

theorem continuous_unit : Continuous X.unit := continuousOn_univ.1 X.isScSmoothMap_unit.continuousOn

theorem continuous_inv : Continuous X.inv := continuousOn_univ.1 X.isScSmoothMap_inv.continuousOn

/-- Condition (4) in the sheet form. -/
theorem isScSmoothCompSheet : IsScSmoothCompSheet X.PObj X.PMor X.src X.tgt X.comp :=
  (isScSmoothComp_iff_sheet _ _).1 X.isScSmoothComp

/-- The orbit space carries the quotient topology (p. 229); `π` is continuous. -/
theorem continuous_π : Continuous X.π := continuous_quot_mk

/-! #### Definition 7.4: sheets, `φ̂` and `Tφ` -/

/-- **A sheet** (before Definition 7.4): an open `𝐔 ⊆ 𝐗` on which `s` and `t` are
sc-diffeomorphisms onto open `U, U' ⊆ X`, with the inverses `(s|𝐔)⁻¹`, `(t|𝐔)⁻¹`. -/
structure Sheet where
  /-- The open set `𝐔 = U(φ)` of morphisms. -/
  carrier : Set Mor
  /-- `s(𝐔) = U(x)`. -/
  srcSet : Set Obj
  /-- `t(𝐔) = U(y)`. -/
  tgtSet : Set Obj
  /-- `(s|𝐔)⁻¹ : U(x) → 𝐔`. -/
  srcInv : Obj → Mor
  /-- `(t|𝐔)⁻¹ : U(y) → 𝐔`. -/
  tgtInv : Obj → Mor
  isScDiffeoOn_src : X.PMor.IsScDiffeoOn X.PObj X.src srcInv carrier srcSet
  isScDiffeoOn_tgt : X.PMor.IsScDiffeoOn X.PObj X.tgt tgtInv carrier tgtSet

variable {X} in
/-- `φ̂ = t ∘ (s|𝐔)⁻¹ : U(x) → U(y)` of a sheet (Definition 7.4). -/
def Sheet.hat (S : X.Sheet) : Obj → Obj := fun y => X.tgt (S.srcInv y)

variable {X} in
/-- `φ̂` is an sc-diffeomorphism `U(x) → U(y)`, with inverse `s ∘ (t|𝐔)⁻¹`. -/
theorem Sheet.isScDiffeoOn_hat (S : X.Sheet) :
    X.PObj.IsScDiffeoOn X.PObj S.hat (fun z => X.src (S.tgtInv z)) S.srcSet S.tgtSet :=
  isScDiffeoOn_comp S.isScDiffeoOn_src.symm S.isScDiffeoOn_tgt

/-- Every morphism lies in a sheet (p. 227). -/
theorem exists_sheet (φ : Mor) : ∃ S : X.Sheet, φ ∈ S.carrier := by
  obtain ⟨W₁, V₁, σ, h₁, hd₁⟩ := X.isLocalScDiffeo_src φ
  obtain ⟨W₂, V₂, τ, h₂, hd₂⟩ := X.isLocalScDiffeo_tgt φ
  have hW : IsOpen (W₁ ∩ W₂) := hd₁.isScSmoothOn.isOpen.inter hd₂.isScSmoothOn.isOpen
  exact ⟨⟨W₁ ∩ W₂, _, _, σ, τ, isScDiffeoOn_restrict hd₁ hW inter_subset_left,
    isScDiffeoOn_restrict hd₂ hW inter_subset_right⟩, h₁, h₂⟩

/-- The sheet chosen at `φ`. -/
def sheetAt (φ : Mor) : X.Sheet := (X.exists_sheet φ).choose

theorem mem_sheetAt (φ : Mor) : φ ∈ (X.sheetAt φ).carrier := (X.exists_sheet φ).choose_spec

theorem src_mem_sheetAt (φ : Mor) : X.src φ ∈ (X.sheetAt φ).srcSet :=
  (X.sheetAt φ).isScDiffeoOn_src.mapsTo (X.mem_sheetAt φ)

theorem tgt_mem_sheetAt (φ : Mor) : X.tgt φ ∈ (X.sheetAt φ).tgtSet :=
  (X.sheetAt φ).isScDiffeoOn_tgt.mapsTo (X.mem_sheetAt φ)

/-- **Definition 7.4**: the local sc-diffeomorphism `φ̂ = t ∘ (s|U(φ))⁻¹ : U(x) → U(y)` associated
with `φ : x → y` (in the chosen sheet; `isScDiffeoOn_hat`). -/
def hat (φ : Mor) : Obj → Obj := (X.sheetAt φ).hat

theorem isScDiffeoOn_hat (φ : Mor) :
    X.PObj.IsScDiffeoOn X.PObj (X.hat φ) (fun z => X.src ((X.sheetAt φ).tgtInv z))
      (X.sheetAt φ).srcSet (X.sheetAt φ).tgtSet :=
  (X.sheetAt φ).isScDiffeoOn_hat

/-- `φ̂(x) = y`. -/
theorem hat_src (φ : Mor) : X.hat φ (X.src φ) = X.tgt φ := by
  change X.tgt ((X.sheetAt φ).srcInv (X.src φ)) = X.tgt φ
  rw [(X.sheetAt φ).isScDiffeoOn_src.left_inv φ (X.mem_sheetAt φ)]

open scoped Classical in
/-- **Definition 7.4**: the tangent `Tφ : T_{s φ}X → T_{t φ}X`, `Tφ = Tφ̂(s φ)`, read through the
chain rule as `Tt ∘ (Ts|T_φ𝐗)⁻¹` with the tangent maps `Ts, Tt : T𝐗 → TX` (Part I's
`MPolyfold.tangentMap`); the identity off `Ts(T_φ𝐗)`. -/
def tangentMor (φ : Mor) (h : X.PObj.TangentSpace) : X.PObj.TangentSpace :=
  if hv : ∃ v : X.PMor.TangentSpace, X.PMor.levelVal 1 (X.PMor.tangentProj v) = φ ∧
      MPolyfold.tangentMap X.isScSmoothMap_src v = h then
    MPolyfold.tangentMap X.isScSmoothMap_tgt hv.choose
  else h

/-! #### Levels and the degeneracy index (pp. 227–228), Definition 7.5 -/

/-- `ml(s φ) = ml(φ)`: `s φ ∈ X_m ⟺ φ ∈ 𝐗_m`. -/
theorem mem_levelSet_src_iff (φ : Mor) (m : ℕ) :
    X.src φ ∈ X.PObj.levelSet m ↔ φ ∈ X.PMor.levelSet m := by
  obtain ⟨W, V, σ, hφ, hd⟩ := X.isLocalScDiffeo_src φ
  refine ⟨fun h => ?_, fun h => hd.isScSmoothOn.mapsTo_levelSet m ⟨hφ, h⟩⟩
  have := hd.isScSmoothOn_inv.mapsTo_levelSet m ⟨hd.mapsTo hφ, h⟩
  rwa [hd.left_inv φ hφ] at this

/-- `ml(t φ) = ml(φ)`. -/
theorem mem_levelSet_tgt_iff (φ : Mor) (m : ℕ) :
    X.tgt φ ∈ X.PObj.levelSet m ↔ φ ∈ X.PMor.levelSet m := by
  obtain ⟨W, V, τ, hφ, hd⟩ := X.isLocalScDiffeo_tgt φ
  refine ⟨fun h => ?_, fun h => hd.isScSmoothOn.mapsTo_levelSet m ⟨hφ, h⟩⟩
  have := hd.isScSmoothOn_inv.mapsTo_levelSet m ⟨hd.mapsTo hφ, h⟩
  rwa [hd.left_inv φ hφ] at this

/-- `d_𝐗(φ) = d_X(s φ)` (Proposition 2.7 [2.24]). -/
theorem degIndex_src (φ : Mor) : X.PMor.degIndex φ = X.PObj.degIndex (X.src φ) := by
  obtain ⟨W, V, σ, hφ, hd⟩ := X.isLocalScDiffeo_src φ
  exact proposition_2_24 hd hφ

/-- `d_𝐗(φ) = d_X(t φ)`. -/
theorem degIndex_tgt (φ : Mor) : X.PMor.degIndex φ = X.PObj.degIndex (X.tgt φ) := by
  obtain ⟨W, V, τ, hφ, hd⟩ := X.isLocalScDiffeo_tgt φ
  exact proposition_2_24 hd hφ

/-- The filtration `|X_k| = π(X_k)` of the orbit space (p. 228). -/
def orbitLevel (k : ℕ) : Set X.OrbitSpace := X.π '' X.PObj.levelSet k

/-- **Definition 7.5**: the induced degeneracy index `d_{|X|}(|x|) = d_X(x)`. -/
def degIndexOrbit : X.OrbitSpace → ℕ :=
  Quotient.lift X.PObj.degIndex <| by
    rintro _ _ ⟨φ, rfl, rfl⟩
    rw [← X.degIndex_src, X.degIndex_tgt]

@[simp]
theorem degIndexOrbit_π (x : Obj) : X.degIndexOrbit (X.π x) = X.PObj.degIndex x := rfl

/-! #### Definition 7.6 -/

/-- **Definition 7.6**: the ep-groupoid is **tame** if the object M-polyfold is tame
(Definition 2.19 [2.37]: an equivalent atlas of tame retracts exists). -/
def IsTame : Prop := X.PObj.IsTame

/-! #### Definition 7.17 -/

/-- **Definition 7.17**: `Q ⊆ X` is **proper** if `t : s⁻¹(Q) → X` is proper. -/
def IsProperSubset (Q : Set Obj) : Prop := IsProperMap ((X.src ⁻¹' Q).domRestrict X.tgt)

/-- **Definition 7.17**: the open `U` has the **properness property** if `cl_X(U)` is proper. -/
def HasPropernessProperty (U : Set Obj) : Prop := IsOpen U ∧ X.IsProperSubset (closure U)

/-- Definition 7.3 (3): every object has an open neighbourhood with the properness property. -/
theorem exists_hasPropernessProperty (x : Obj) : ∃ V, x ∈ V ∧ X.HasPropernessProperty V := by
  obtain ⟨V, hVo, hxV, hV⟩ := X.exists_isProperMap x
  exact ⟨V, hxV, hVo, hV⟩

/-! #### Theorem 7.1: the data of a natural representation -/

/-- **The data of Theorem 7.1** (a natural representation of `G_x`): an open connected
neighbourhood `U` of `x`, a homomorphism `Φ : G_x → Diff_sc(U)` (`Φ g` an sc-diffeomorphism of
`U` with inverse `Φ g⁻¹`, `Φ(gh) = Φ(g) ∘ Φ(h)`) and `Γ : G_x × U → 𝐗`, sc-smooth on each sheet
`{g} × U`, with (1) `Γ(g, x) = g`, (2) `s Γ(g, y) = y`, `t Γ(g, y) = Φ(g)(y)`, (3) every morphism
`h` between points of `U` is `Γ(g, s h)` for a unique `g`. -/
structure NaturalRep (x : Obj) where
  /-- The neighbourhood `U = U(x)`. -/
  U : Set Obj
  isOpen_U : IsOpen U
  isConnected_U : IsConnected U
  mem_U : x ∈ U
  /-- The natural action `Φ : G_x → Diff_sc(U)`. -/
  Φ : X.Isotropy x → Obj → Obj
  /-- The map `Γ : G_x × U → 𝐗`. -/
  Γ : X.Isotropy x → Obj → Mor
  isScDiffeoOn_Φ : ∀ g, X.PObj.IsScDiffeoOn X.PObj (Φ g) (Φ g⁻¹) U U
  Φ_mul : ∀ g h, ∀ y ∈ U, Φ (g * h) y = Φ g (Φ h y)
  isScSmoothOn_Γ : ∀ g, X.PObj.IsScSmoothOn X.PMor (Γ g) U
  Γ_self : ∀ g, Γ g x = g.val
  src_Γ : ∀ g, ∀ y ∈ U, X.src (Γ g y) = y
  tgt_Γ : ∀ g, ∀ y ∈ U, X.tgt (Γ g y) = Φ g y
  existsUnique_Γ : ∀ h : Mor, X.src h ∈ U → X.tgt h ∈ U → ∃! g, Γ g (X.src h) = h

namespace NaturalRep

variable {X} {x : Obj} (R : X.NaturalRep x)

theorem mapsTo_Φ (g : X.Isotropy x) : MapsTo (R.Φ g) R.U R.U := (R.isScDiffeoOn_Φ g).mapsTo

theorem Φ_one (y : Obj) (hy : y ∈ R.U) : R.Φ 1 y = y := by
  have h1 := (R.isScDiffeoOn_Φ 1).left_inv y hy
  rw [inv_one] at h1
  have h2 := R.Φ_mul 1 1 y hy
  rw [mul_one] at h2
  rw [h2]
  exact h1

/-- `Φ(g)(x) = x`. -/
theorem Φ_self (g : X.Isotropy x) : R.Φ g x = x := by
  rw [← R.tgt_Γ g x R.mem_U, R.Γ_self]
  exact g.tgt_val

theorem Γ_mem_morOn (g : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) : R.Γ g y ∈ X.morOn R.U :=
  ⟨by rw [R.src_Γ g y hy]; exact hy, by rw [R.tgt_Γ g y hy]; exact R.mapsTo_Φ g hy⟩

/-- The action `g * y = Φ(g)(y)` of `G_x` on `U`. -/
instance : MulAction (X.Isotropy x) R.U where
  smul g y := ⟨R.Φ g y, R.mapsTo_Φ g y.2⟩
  one_smul y := Subtype.ext (R.Φ_one y y.2)
  mul_smul g h y := Subtype.ext (R.Φ_mul g h y y.2)

theorem smul_val (g : X.Isotropy x) (y : R.U) : ((g • y : R.U) : Obj) = R.Φ g y := rfl

/-- **The translation groupoid** `G_x ⋉ U(x)` (p. 232). -/
def translationGroupoid : GroupoidStr R.U (X.Isotropy x × R.U) :=
  GroupoidStr.translation (X.Isotropy x) R.U

end NaturalRep

/-! #### Definition 7.8 -/

/-- **Definition 7.8** (Proposition 7.5): a natural representation of a finite set `Y` of
objects on neighbourhoods contained in `V`: mutually disjoint connected open `U(y) ⊆ V`, for every
morphism `ψ : y → y'` between points of `Y` an sc-diffeomorphism `F ψ : U(y) → U(y')`, functorial,
and connected open `𝐔(ψ) ∋ ψ` decomposing the morphisms between points of `⋃ U(y)`, such that
(1) `G_y` acts on `U(y)` by the natural action, (2) `s : 𝐔(ψ) → U(y)` and `t : 𝐔(ψ) → U(y')` are
sc-diffeomorphisms, (3) `F ψ = t ∘ (s|𝐔(ψ))⁻¹`. -/
structure NaturalRepFinite (Y : Finset Obj) (V : Set Obj) where
  /-- The neighbourhoods `U(y)`. -/
  U : Obj → Set Obj
  /-- The functor on morphisms, `F ψ = f(ψ)`. -/
  F : Mor → Obj → Obj
  /-- The components `𝐔(ψ)`. -/
  sheet : Mor → Set Mor
  /-- `(s|𝐔(ψ))⁻¹`. -/
  srcInv : Mor → Obj → Mor
  isOpen_U : ∀ y ∈ Y, IsOpen (U y)
  isConnected_U : ∀ y ∈ Y, IsConnected (U y)
  mem_U : ∀ y ∈ Y, y ∈ U y
  U_subset : ∀ y ∈ Y, U y ⊆ V
  pairwiseDisjoint_U : (Y : Set Obj).PairwiseDisjoint U
  isScDiffeoOn_F : ∀ ψ ∈ X.morOn Y,
    X.PObj.IsScDiffeoOn X.PObj (F ψ) (F (X.inv ψ)) (U (X.src ψ)) (U (X.tgt ψ))
  F_comp : ∀ φ ∈ X.morOn Y, ∀ ψ ∈ X.morOn Y, X.src φ = X.tgt ψ →
    ∀ z ∈ U (X.src ψ), F (X.comp φ ψ) z = F φ (F ψ z)
  F_unit : ∀ y ∈ Y, ∀ z ∈ U y, F (X.unit y) z = z
  isOpen_sheet : ∀ ψ ∈ X.morOn Y, IsOpen (sheet ψ)
  isConnected_sheet : ∀ ψ ∈ X.morOn Y, IsConnected (sheet ψ)
  mem_sheet : ∀ ψ ∈ X.morOn Y, ψ ∈ sheet ψ
  pairwiseDisjoint_sheet : (X.morOn Y).PairwiseDisjoint sheet
  morOn_eq : X.morOn (⋃ y ∈ Y, U y) = ⋃ ψ ∈ X.morOn Y, sheet ψ
  isScDiffeoOn_src : ∀ ψ ∈ X.morOn Y,
    X.PMor.IsScDiffeoOn X.PObj X.src (srcInv ψ) (sheet ψ) (U (X.src ψ))
  isScDiffeoOn_tgt : ∀ ψ ∈ X.morOn Y,
    ∃ τ : Obj → Mor, X.PMor.IsScDiffeoOn X.PObj X.tgt τ (sheet ψ) (U (X.tgt ψ))
  F_eq : ∀ ψ ∈ X.morOn Y, ∀ z ∈ U (X.src ψ), F ψ z = X.tgt (srcInv ψ z)
  natural : ∀ y ∈ Y, ∃ R : X.NaturalRep y, R.U = U y ∧ ∀ g, ∀ z ∈ U y, R.Φ g z = F g.val z

/-! #### Definition 7.9 -/

/-- **Definition 7.9 (local uniformizer)**: a natural representation `U(x)` and a fully faithful
functor `Ψ_x : G_x ⋉ U(x) → X`, the inclusion on objects, inducing a homeomorphism of
`|U(x)|_{G_x ⋉ U(x)}` onto `π(U(x))`. -/
structure LocalUniformizer (x : Obj) where
  /-- `U(x)` with the natural `G_x`-action. -/
  rep : X.NaturalRep x
  /-- The functor `Ψ_x`. -/
  Ψ : GroupoidFunctor rep.translationGroupoid X.toGroupoidStr
  obj_eq : ∀ y, Ψ.obj y = (y : Obj)
  full : Ψ.toFunctor.Full
  faithful : Ψ.toFunctor.Faithful
  isEmbedding_orbitMap : IsEmbedding Ψ.orbitMap
  range_orbitMap : range Ψ.orbitMap = X.π '' rep.U

/-! #### Definition 7.10 -/

/-- **Definition 7.10**: the full subcategory on `A ⊆ X` is an **ep-subgroupoid** if (1) `A` is a
sub-M-polyfold of `X` and (2) `A` is saturated. -/
structure IsEpSubgroupoid (A : Set Obj) : Prop where
  isSubMPolyfold : X.PObj.IsSubMPolyfold A
  isSaturated : X.IsSaturated A

theorem isEpSubgroupoid_univ : X.IsEpSubgroupoid univ :=
  ⟨X.PObj.isSubMPolyfold_univ, X.isSaturated_univ⟩

/-! #### Definition 7.11 -/

/-- **Definition 7.11**: `X` is **effective** if for every `x`, every `g ∈ G_x ∖ {1_x}` and every
open neighbourhood `𝐔(g)` of `g` in `𝐗` there is `ψ ∈ 𝐔(g)` with `s ψ ≠ t ψ`.  (Regular objects:
`GroupoidStr.IsRegular`, `GroupoidStr.regularSet`.) -/
def IsEffective : Prop :=
  ∀ (x : Obj) (g : X.Isotropy x), g ≠ 1 → ∀ W : Set Mor, IsOpen W → g.val ∈ W →
    ∃ ψ ∈ W, X.src ψ ≠ X.tgt ψ

/-! #### Definitions 7.12 and 7.13 -/

/-- `g ∈ G_x` **acts trivially** (p. 241): `Φ(g) = 1` on `U` for some natural representation. -/
def ActsTrivially {x : Obj} (g : X.Isotropy x) : Prop :=
  ∃ R : X.NaturalRep x, ∀ y ∈ R.U, R.Φ g y = y

/-- `T_x ⊆ G_x`, the elements acting trivially (p. 241; a normal subgroup, `Reduced.lean`). -/
def trivialSet (x : Obj) : Set (X.Isotropy x) := {g | X.ActsTrivially g}

theorem one_mem_trivialSet {x : Obj} (R : X.NaturalRep x) : (1 : X.Isotropy x) ∈ X.trivialSet x :=
  ⟨R, R.Φ_one⟩

/-- **Definition 7.12**: the **non-effective part** `𝐗^T = {φ ∈ T_x | x ∈ X}`. -/
def nonEffectivePart : Set Mor :=
  {φ | ∃ (x : Obj) (g : X.Isotropy x), g ∈ X.trivialSet x ∧ φ = g.val}

/-- **Definition 7.12**: `φ ∼ φ'` if (1) `s φ = s φ' = x` and (2) `φ = φ' ∘ g` for some
`g ∈ T_x`. -/
def ReducedRel (φ φ' : Mor) : Prop :=
  X.src φ = X.src φ' ∧
    ∃ g : X.Isotropy (X.src φ), g ∈ X.trivialSet (X.src φ) ∧ φ = X.comp φ' g.val

/-- **Definition 7.12**: the **reduced morphisms** `𝐗^R`, the classes `[φ]` of `∼`. -/
def ReducedMor : Type u := Quot X.ReducedRel

/-- **Definition 7.13**: the **effective isotropy group** `G_x^eff = G_x/T_x`. -/
abbrev EffIsotropy (x : Obj) : Type u := X.Isotropy x ⧸ Subgroup.normalClosure (X.trivialSet x)

/-! #### Definitions 7.14–7.16 -/

/-- **Definition 7.14**: `K ⊆ |X|` is **component compact** if its intersection with every
connected component of `|X|` is compact. -/
def IsComponentCompact (K : Set X.OrbitSpace) : Prop :=
  ∀ z : X.OrbitSpace, IsCompact (K ∩ connectedComponent z)

/-- **Definition 7.15**: an ep-groupoid **with paracompact orbit space**: (1)–(4) and (5) `|X|`
is paracompact. -/
def HasParacompactOrbitSpace : Prop := ParacompactSpace X.OrbitSpace

/-- **Definition 7.16**: an ep-groupoid **with sc-smooth partitions of unity**: for every
saturated open cover `(U_λ)` of `X` there is a subordinate sc-smooth partition of unity `(β_λ)`
with (1) every point has a saturated open neighbourhood meeting only finitely many `supp β_λ`, and
(2) `β_λ(z) = β_λ(y)` for isomorphic `y, z`. -/
def HasScPartitionsOfUnity : Prop :=
  ∀ (ι : Type u) (U : ι → Set Obj), (∀ i, IsOpen (U i)) → (∀ i, X.IsSaturated (U i)) →
    ⋃ i, U i = univ →
    ∃ β : PartitionOfUnity ι Obj, β.IsSubordinate U ∧ X.PObj.IsScSmoothPartitionOfUnity β ∧
      (∀ x, ∃ W : Set Obj, IsOpen W ∧ X.IsSaturated W ∧ x ∈ W ∧
        {i | (W ∩ tsupport (β i)).Nonempty}.Finite) ∧
      ∀ i φ, β i (X.src φ) = β i (X.tgt φ)

end EpGroupoid

/-! ### Definition 7.7: the category `EP` -/

/-- **Definition 7.7**: a morphism of `EP`, a functor sc-smooth on the object spaces and on the
morphism spaces. -/
structure EpFunctor {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor')
    extends GroupoidFunctor X.toGroupoidStr Y.toGroupoidStr where
  isScSmoothMap_obj : X.PObj.IsScSmoothMap Y.PObj obj
  isScSmoothMap_mor : X.PMor.IsScSmoothMap Y.PMor mor

namespace EpFunctor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {Obj'' Mor'' : Type w} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Z : EpGroupoid Obj'' Mor''}

theorem ext {F F' : EpFunctor X Y} (h₁ : F.obj = F'.obj) (h₂ : F.mor = F'.mor) : F = F' := by
  cases F with
  | mk F _ _ =>
    cases F' with
    | mk F' _ _ =>
      cases GroupoidFunctor.ext h₁ h₂
      rfl

variable (X) in
/-- The identity of `EP`. -/
def id : EpFunctor X X where
  toGroupoidFunctor := GroupoidFunctor.id X.toGroupoidStr
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor := MPolyfold.isScSmoothMap_id

/-- The composition `F ∘ E` in `EP`. -/
def comp (F : EpFunctor Y Z) (E : EpFunctor X Y) : EpFunctor X Z where
  toGroupoidFunctor := F.toGroupoidFunctor.comp E.toGroupoidFunctor
  isScSmoothMap_obj := F.isScSmoothMap_obj.comp E.isScSmoothMap_obj
  isScSmoothMap_mor := F.isScSmoothMap_mor.comp E.isScSmoothMap_mor

end EpFunctor

/-- A bundled ep-groupoid, an object of the category `EP` (Definition 7.7). -/
structure EP : Type (u + 1) where
  /-- The object set. -/
  Obj : Type u
  /-- The morphism set. -/
  Mor : Type u
  [instTopObj : TopologicalSpace Obj]
  [instT2Obj : T2Space Obj]
  [instParaObj : ParacompactSpace Obj]
  [instTopMor : TopologicalSpace Mor]
  [instT2Mor : T2Space Mor]
  [instParaMor : ParacompactSpace Mor]
  /-- The ep-groupoid. -/
  X : EpGroupoid Obj Mor

attribute [instance] EP.instTopObj EP.instT2Obj EP.instParaObj EP.instTopMor EP.instT2Mor
  EP.instParaMor

/-- **Definition 7.7**: the category `EP` of ep-groupoids and sc-smooth functors. -/
instance : LargeCategory EP.{u} where
  Hom A B := EpFunctor A.X B.X
  id A := EpFunctor.id A.X
  comp E F := F.comp E
  id_comp _ := EpFunctor.ext rfl rfl
  comp_id _ := EpFunctor.ext rfl rfl
  assoc _ _ _ := EpFunctor.ext rfl rfl

/-! ### Witnesses: the trivial ep-groupoid of an M-polyfold -/

namespace EpGroupoid

section Trivial

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)

private theorem isLocalScDiffeo_id : P.IsLocalScDiffeo P id := fun x =>
  ⟨univ, univ, id, mem_univ x, isScDiffeoOn_id P⟩

/-- **The trivial ep-groupoid** of an M-polyfold `Z`: `𝐗 = X = Z`, all structure maps the
identity (PLAN II.5). -/
def trivial : EpGroupoid Z Z where
  toGroupoidStr := GroupoidStr.trivial Z
  PObj := P
  PMor := P
  isLocalScDiffeo_src := isLocalScDiffeo_id P
  isLocalScDiffeo_tgt := isLocalScDiffeo_id P
  isScSmoothMap_unit := MPolyfold.isScSmoothMap_id
  isScSmoothMap_inv := MPolyfold.isScSmoothMap_id
  exists_isProperMap x := ⟨univ, isOpen_univ, mem_univ x,
    (isClosed_closure.preimage continuous_id).isClosedEmbedding_subtypeVal.isProperMap⟩
  isScSmoothComp := by
    let _ := MPolyfold.paracompactSpace_prod P P
    let _ := (P.prod P).paracompactSpace_subtype
      (MPolyfold.fibredProduct (GroupoidStr.trivial Z).src (GroupoidStr.trivial Z).tgt)
    exact (MPolyfold.isScSmoothMap_fst P P).comp (MPolyfold.subPolyfold_inclusion_isScSmooth _)

instance (x : Z) : Subsingleton ((trivial P).Isotropy x) :=
  ⟨fun g h => GroupoidStr.Isotropy.ext (g.src_val.trans h.src_val.symm)⟩

/-- The trivial ep-groupoid of a tame M-polyfold is tame. -/
theorem isTame_trivial (h : P.IsTame) : (trivial P).IsTame := h

/-- The trivial ep-groupoid of `ℝⁿ` is tame. -/
theorem isTame_trivial_rn (n : ℕ) : (trivial (rnPolyfold n)).IsTame := rnPolyfold_isTame

/-- The trivial ep-groupoid is effective (vacuously: all isotropy groups are trivial). -/
theorem isEffective_trivial : (trivial P).IsEffective :=
  fun _ g hg => absurd (Subsingleton.elim g 1) hg

theorem regularSet_trivial : (trivial P).regularSet = univ :=
  eq_univ_of_forall fun _ g => Subsingleton.elim g 1

/-- In the trivial ep-groupoid every closed set is proper. -/
theorem isProperSubset_trivial {Q : Set Z} (hQ : IsClosed Q) : (trivial P).IsProperSubset Q :=
  (hQ.preimage continuous_id).isClosedEmbedding_subtypeVal.isProperMap

theorem hasPropernessProperty_trivial {U : Set Z} (hU : IsOpen U) :
    (trivial P).HasPropernessProperty U :=
  ⟨hU, isProperSubset_trivial P isClosed_closure⟩

/-- The orbit space of the trivial ep-groupoid is `Z`. -/
def trivialOrbitHomeomorph : (trivial P).OrbitSpace ≃ₜ Z where
  toFun := Quotient.lift id <| by
    rintro _ _ ⟨φ, rfl, rfl⟩
    rfl
  invFun := (trivial P).π
  left_inv z := Quotient.inductionOn z fun _ => rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id.quotient_lift _
  continuous_invFun := continuous_quot_mk

/-- The trivial ep-groupoid has paracompact orbit space. -/
theorem hasParacompactOrbitSpace_trivial : (trivial P).HasParacompactOrbitSpace :=
  (trivialOrbitHomeomorph P).isClosedEmbedding.paracompactSpace

/-- If `Z` admits sc-smooth partitions of unity, the trivial ep-groupoid has sc-smooth partitions
of unity (Definition 7.16 is satisfiable). -/
theorem hasScPartitionsOfUnity_trivial (h : P.AdmitsScPartitionsOfUnity) :
    (trivial P).HasScPartitionsOfUnity := by
  intro ι U hUo _ hcov
  obtain ⟨β, hsub, hsm⟩ := h ι U hUo hcov
  refine ⟨β, hsub, hsm, fun x => ?_, fun _ _ => rfl⟩
  obtain ⟨t, ht, hfin⟩ := β.locallyFinite x
  refine ⟨interior t, isOpen_interior, GroupoidStr.isSaturated_trivial _,
    mem_interior_iff_mem_nhds.2 ht, hfin.subset fun i hi => ?_⟩
  have hi' : (tsupport (β i) ∩ interior t).Nonempty := by
    rw [inter_comm]
    exact hi
  obtain ⟨y, hy⟩ := (closure_inter_open_nonempty_iff isOpen_interior).1 hi'
  exact ⟨y, hy.1, interior_subset hy.2⟩

section Connected

variable [ConnectedSpace Z]

/-- The natural representation of the trivial ep-groupoid of a connected M-polyfold (`U = Z`,
`Φ = id`, `Γ = id`): the data of Theorem 7.1 is satisfiable. -/
def trivialNaturalRep (x : Z) : (trivial P).NaturalRep x where
  U := univ
  isOpen_U := isOpen_univ
  isConnected_U := isConnected_univ
  mem_U := mem_univ x
  Φ _ := id
  Γ _ := id
  isScDiffeoOn_Φ _ := isScDiffeoOn_id P
  Φ_mul _ _ _ _ := rfl
  isScSmoothOn_Γ _ := MPolyfold.isScSmoothMap_id
  Γ_self g := g.src_val.symm
  src_Γ _ _ _ := rfl
  tgt_Γ _ _ _ := rfl
  existsUnique_Γ _ _ _ := ⟨1, rfl, fun g _ => Subsingleton.elim g 1⟩

theorem actsTrivially_trivial {x : Z} (g : (trivial P).Isotropy x) :
    (trivial P).ActsTrivially g :=
  ⟨trivialNaturalRep P x, fun _ _ => rfl⟩

/-- A natural representation of a one-point set in the trivial ep-groupoid of a connected
M-polyfold (Definition 7.8 is satisfiable). -/
def trivialNaturalRepFinite (y : Z) : (trivial P).NaturalRepFinite {y} univ where
  U _ := univ
  F _ := id
  sheet _ := univ
  srcInv _ := id
  isOpen_U _ _ := isOpen_univ
  isConnected_U _ _ := isConnected_univ
  mem_U _ _ := mem_univ _
  U_subset _ _ := subset_univ _
  pairwiseDisjoint_U := by
    rw [Finset.coe_singleton]
    exact pairwiseDisjoint_singleton _ _
  isScDiffeoOn_F _ _ := isScDiffeoOn_id P
  F_comp _ _ _ _ _ _ _ := rfl
  F_unit _ _ _ _ := rfl
  isOpen_sheet _ _ := isOpen_univ
  isConnected_sheet _ _ := isConnected_univ
  mem_sheet _ _ := mem_univ _
  pairwiseDisjoint_sheet := by
    refine Set.Subsingleton.pairwise ?_ _
    rintro a ⟨ha, -⟩ b ⟨hb, -⟩
    rw [Finset.coe_singleton] at ha hb
    exact ha.trans hb.symm
  morOn_eq := by
    have h1 : ∀ z : Z, z ∈ ⋃ y' ∈ ({y} : Finset Z), (univ : Set Z) :=
      fun _ => mem_iUnion₂.2 ⟨y, Finset.mem_singleton_self y, mem_univ _⟩
    have h2 : y ∈ (trivial P).morOn ↑({y} : Finset Z) := by
      rw [Finset.coe_singleton]
      exact ⟨rfl, rfl⟩
    ext z
    exact ⟨fun _ => mem_iUnion₂.2 ⟨y, h2, mem_univ _⟩, fun _ => ⟨h1 _, h1 _⟩⟩
  isScDiffeoOn_src _ _ := isScDiffeoOn_id P
  isScDiffeoOn_tgt _ _ := ⟨id, isScDiffeoOn_id P⟩
  F_eq _ _ _ _ := rfl
  natural y' _ := ⟨trivialNaturalRep P y', rfl, fun _ _ _ => rfl⟩

end Connected

end Trivial

end EpGroupoid

end Polyfold
