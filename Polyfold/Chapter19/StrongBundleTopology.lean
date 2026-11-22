import Polyfold.Chapter19.StrongBundleTransition

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.6 "A Strong Bundle Version" (pp. 897–899): **Definition 19.6.7** (the natural topology
`T̄` on `|E|`), **Theorem 19.6.8**, **Proposition 19.6.9**, **Definition 19.6.10** (the natural
topology on `M(Ψ̄, Ψ̄')`), **Theorem 19.6.11** and **Lemma 19.6.12**.  Numbers and pages are the
2021 text's.

# The natural topologies of a basic strong bundle construction

## The text, paraphrased

(Definition 19.6.7) `Û ⊂ |E|` belongs to `T̄` if for every `z̄ ∈ Û` there are `α` with
`|α| = |P|(z̄)`, `Ψ̄ ∈ F̄(α)`, `a ∈ K` with `|Ψ̄(a)| = z̄` and an open `V̂ ∋ a` with
`|Ψ̄(V̂)| ⊂ Û`.  (Theorem 19.6.8) (1) `T̄` is a topology; (2) `|Ψ̄(Ŵ)|` is open for open `Ŵ ⊂ K`;
(3) `|Ψ̄| : |G ⋉ K| → |E|` is a homeomorphism onto an open set; (4) every `z ∈ |S|` has an open
`V` with `|P|⁻¹(V)` metrizable; (5) `|P|` is continuous.  (Proposition 19.6.9) `T` is metrizable
iff `T̄` is.  (Definition 19.6.10) `Ŵ ⊂ M(Ψ̄, Ψ̄')` is open if for `h̄ = (a, φ̂, a') ∈ Ŵ` there is
an open `V̂` in `K` with `F̄_h(V̂) ⊂ Ŵ`.  (Theorem 19.6.11) this is a topology, locally
metrizable and regular Hausdorff, with (1) `s`, (2) `t` local homeomorphisms, (3) `u`
continuous, (4) `ι` a homeomorphism, (5) `m` continuous, (6) the map `M(Ψ̄, Ψ̄') → M(Ψ, Ψ')`
continuous; the projection `p` is continuous.  (Lemma 19.6.12) under the properness condition,
`T̄_{Ψ̄,Ψ̄'}` is metrizable.

## What is formalized (namespace `Polyfold.GroupoidalCategory.BasicStrongBundleConstruction`)

`B : C.BasicStrongBundleConstruction μ`; `hB : B.base.U.HasClassUniformizers` (every
isomorphism class of `S` contains an object with a uniformizer: `F(α) ≠ ∅`, the standing reading
of §17.1; it is needed already for Theorem 19.2.2 (1), see `theorem_19_2_2_empty_family`).  `hBE hB`
is the corresponding fact for `E_μ`.

* `BarOpen` (**Definition 19.6.7**, as printed), `definition_19_6_7` (`BarOpen` is the natural
  openness `NatOpen` of the uniformizer construction `toE` of `E_μ`), `topE hB` (`T̄`),
  `topS hB` (`T`), `isOpen_topE_iff`.
* **Theorem 19.6.8**: `theorem_19_6_8_one`, `theorem_19_6_8_two`,
  `theorem_19_6_8_three`, `theorem_19_6_8_four`, `theorem_19_6_8_five`; with
  `StrongBundleStr.orbitProj_preimage_range` (`|P|⁻¹(|Ψ(O)|) = |Ψ̄(K)|`).
* `continuous_zeroOrbit`, `isEmbedding_zeroOrbit` (the zero section `|S| → |E|` is an
  embedding), **Proposition 19.6.9**: `proposition_19_6_9` (`⇒` by `metrizableSpace_of_pullback`
  along `|P|` with (4), (5); `⇐` through the zero section).
* `BarOpenTr` (**Definition 19.6.10**, as printed), `definition_19_6_10` (it is the openness of
  the transition data `toETD` of `E_μ`), `MBar Ψ̄ Ψ̄'` (`M(Ψ̄, Ψ̄')` with `T̄_{Ψ̄,Ψ̄'}`),
  `topology_MBar` (independent of the representative).
* **Theorem 19.6.11**: `theorem_19_6_11` (topology, regular, Hausdorff, locally metrizable),
  `theorem_19_6_11_one` … `theorem_19_6_11_five`, `theorem_19_6_11_six` (`p` continuous).
* **Lemma 19.6.12**: `lemma_19_6_12` (without the properness condition), `lemma_19_6_12_book`.

## Readings

* Definition 19.6.10: "an open neighborhood `V̂` of `h̄` in `K`" is read as an open
  neighbourhood of `a = s(h̄)` in `K` inside `K|V(p(a))`, and `F̄_h` as `F̄_{p(h̄)}`.
* Theorem 19.6.11 (6): "`m : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')`" is read as the projection `p` (the next
  sentence of the text), for the natural topologies.
* Lemma 19.6.12 holds without the properness condition: the transition sets are metrizable for
  any transition data (Chapter 19's `TransitionData.metrizableSpace`); the printed form is
  `lemma_19_6_12_book`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

universe u

namespace GroupoidalCategory

variable {C : GroupoidalCategory.{u}}

open GroupoidStr (TransitionSet)

namespace StrongBundleStr

variable {μ : C.BanFunctor} {Ψe : μ.cat.Uniformizer} (S : StrongBundleStr μ Ψe)

/-- `|Ψ̄|` on classes: `|Ψ̄|(|a|) = |Ψ̄(a)|`, so its image is `{|Ψ̄(a)|}`. -/
theorem range_orbitMap : range Ψe.functor.orbitMap = range fun a => μ.cat.π (Ψe.obj a) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    induction w using Quotient.inductionOn with
    | h a => exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨(GroupoidStr.translation Ψe.G Ψe.O).π a, rfl⟩

/-- **`|P|⁻¹(|Ψ(O)|) = |Ψ̄(K)|`**: an object over a class of `|Ψ(O)|` is isomorphic to one in
the image of `Ψ̄` (by the fibre isomorphisms `K_o ≅ μ(Ψ(o))`). -/
theorem orbitProj_preimage_range :
    μ.orbitProj ⁻¹' range (fun o => C.π (S.toBase.obj o)) =
      range fun a => μ.cat.π (Ψe.obj a) := by
  ext z
  induction z using Quotient.inductionOn with
  | h e =>
    constructor
    · rintro ⟨o, ho⟩
      obtain ⟨e', he', he'e⟩ := μ.exists_mem_fiber_of_π_eq (α := S.toBase.obj o) ho.symm
      let v : S.p ⁻¹' {o} := (S.fiberCLE o).symm ⟨e', he'⟩
      have hv : Ψe.obj v = e' := by
        rw [← S.fiberCLE_apply o v, ContinuousLinearEquiv.apply_symm_apply]
      exact ⟨v, show μ.cat.π (Ψe.obj v) = _ by rw [hv]; exact he'e⟩
    · rintro ⟨a, ha⟩
      have ha' : μ.cat.π (Ψe.obj a) = μ.cat.π e := ha
      refine ⟨S.p a, ?_⟩
      change C.π (S.toBase.obj (S.p a)) = μ.orbitProj (μ.cat.π e)
      rw [← S.P_obj', ← ha']
      rfl

end StrongBundleStr

namespace BasicStrongBundleConstruction

variable {μ : C.BanFunctor} (B : C.BasicStrongBundleConstruction μ)

/-- Every class of `E_μ` meets the uniformizer construction `toE` when every class of `S` meets
`F`. -/
theorem hBE (hB : B.base.U.HasClassUniformizers) : B.toE.U.HasClassUniformizers :=
  B.U.hasClassUniformizers_toE_iff.2 hB

/-- The natural topology `T` on `|S|` of the underlying basic construction. -/
abbrev topS (hB : B.base.U.HasClassUniformizers) : TopologicalSpace C.OrbitSpace :=
  B.base.natTop hB

/-- **The natural topology `T̄` on `|E|`** (Definition 19.6.7, Theorem 19.6.8 (1)). -/
abbrev topE (hB : B.base.U.HasClassUniformizers) : TopologicalSpace μ.cat.OrbitSpace :=
  B.toE.natTop (B.hBE hB)

/-! ### Definition 19.6.7 and Theorem 19.6.8 -/

/-- **2021 Definition 19.6.7, p. 897**, as printed: `Û ⊂ |E|` belongs to `T̄` if for every
`z̄ ∈ Û` there are an object `α` with `|α| = |P|(z̄)`, `Ψ̄ ∈ F̄(α)`, `a ∈ K` with `|Ψ̄(a)| = z̄`
and an open `V̂ ∋ a` in `K` with `|Ψ̄(V̂)| ⊂ Û`. -/
def BarOpen (W : Set μ.cat.OrbitSpace) : Prop :=
  ∀ z ∈ W, ∃ α : C.Obj, C.π α = μ.orbitProj z ∧ ∃ Ψe ∈ B.U.F α, ∃ a : Ψe.O,
    μ.cat.π (Ψe.obj a) = z ∧ ∃ V : Set Ψe.O, IsOpen V ∧ a ∈ V ∧
      (fun q => μ.cat.π (Ψe.obj q)) '' V ⊆ W

/-- **Definition 19.6.7 is the natural openness (Definition 19.2.1) of the uniformizer
construction `toE` of `E_μ`.** -/
theorem definition_19_6_7 {W : Set μ.cat.OrbitSpace} : B.BarOpen W ↔ B.toE.U.NatOpen W := by
  constructor
  · intro h z hz
    obtain ⟨α, hα, Ψe, hΨe, a, ha, V, hV, haV, hsub⟩ := h z hz
    refine ⟨Ψe.obj a, ha, Ψe, ⟨α, hΨe, ?_, a, rfl⟩, a, rfl, V, hV, haV, hsub⟩
    rw [hα, ← ha]; rfl
  · intro h z hz
    obtain ⟨x, rfl, Ψe, ⟨α, hΨe, hαx, -⟩, a, ha, V, hV, haV, hsub⟩ := h z hz
    exact ⟨α, hαx, Ψe, hΨe, a, by rw [ha], V, hV, haV, hsub⟩

theorem isOpen_topE_iff (hB : B.base.U.HasClassUniformizers) {W : Set μ.cat.OrbitSpace} :
    IsOpen[B.topE hB] W ↔ B.BarOpen W := B.definition_19_6_7.symm

/-- **2021 Theorem 19.6.8 (1), p. 897**, under `HasClassUniformizers` (`F(α) ≠ ∅`, the standing
reading of §17.1): `T̄` is a topology on `|E|`. -/
theorem theorem_19_6_8_one (hB : B.base.U.HasClassUniformizers) :
    B.BarOpen univ ∧ (∀ W₁ W₂, B.BarOpen W₁ → B.BarOpen W₂ → B.BarOpen (W₁ ∩ W₂)) ∧
      ∀ S : Set (Set μ.cat.OrbitSpace), (∀ W ∈ S, B.BarOpen W) → B.BarOpen (⋃₀ S) := by
  obtain ⟨h1, h2, h3⟩ := B.toE.theorem_19_2_2_one (B.hBE hB)
  simp only [definition_19_6_7]
  exact ⟨h1, h2, h3⟩

/-- **2021 Theorem 19.6.8 (2), p. 897**: for `Ψ̄ ∈ F̄(α)` and open `Ŵ ⊂ K`, `|Ψ̄(Ŵ)|` is open in
`|E|`. -/
theorem theorem_19_6_8_two (hB : B.base.U.HasClassUniformizers) {α : C.Obj}
    {Ψe : μ.cat.Uniformizer} (hΨe : Ψe ∈ B.U.F α) {V : Set Ψe.O} (hV : IsOpen V) :
    IsOpen[B.topE hB] ((fun q => μ.cat.π (Ψe.obj q)) '' V) := by
  obtain ⟨o, ho⟩ := B.U.isAt α Ψe hΨe
  exact B.toE.theorem_19_2_2_two (B.hBE hB) (B.U.mem_toE hΨe ho) hV

/-- **2021 Theorem 19.6.8 (3), p. 897**: for `Ψ̄ ∈ F̄(α)`, `|Ψ̄| : |G ⋉ K| → |E|` is a
homeomorphism onto an open set. -/
theorem theorem_19_6_8_three (hB : B.base.U.HasClassUniformizers) {α : C.Obj}
    {Ψe : μ.cat.Uniformizer} (hΨe : Ψe ∈ B.U.F α) :
    @IsOpenEmbedding _ _ _ (B.topE hB) Ψe.functor.orbitMap := by
  obtain ⟨o, ho⟩ := B.U.isAt α Ψe hΨe
  exact (B.toE.theorem_19_2_2_three (B.hBE hB) (B.U.mem_toE hΨe ho)).1

/-- **2021 Theorem 19.6.8 (4), p. 897**: every `z ∈ |S|` has an open neighbourhood `V` (the
image `|Ψ(O)|` of a uniformizer at `z`) such that `|P|⁻¹(V)` is metrizable for `T̄`. -/
theorem theorem_19_6_8_four (hB : B.base.U.HasClassUniformizers) (z : C.OrbitSpace) :
    ∃ V : Set C.OrbitSpace, IsOpen[B.topS hB] V ∧ z ∈ V ∧
      @MetrizableSpace (μ.orbitProj ⁻¹' V) (@instTopologicalSpaceSubtype _ _ (B.topE hB)) := by
  let _i := B.topE hB
  obtain ⟨α, rfl, _, Ψe, hΨe, rfl⟩ := hB z
  obtain ⟨o, ho⟩ := B.U.isAt α Ψe hΨe
  have hset := (B.U.str Ψe ⟨α, hΨe⟩).orbitProj_preimage_range
  rw [← image_univ] at hset
  refine ⟨_, B.base.theorem_19_2_2_two hB ⟨Ψe, hΨe, rfl⟩ isOpen_univ,
    ⟨o, trivial, congrArg C.π ho⟩, ?_⟩
  rw [hset, ← StrongBundleStr.range_orbitMap (Ψe := Ψe)]
  have he := B.theorem_19_6_8_three hB hΨe
  have := metrizableSpace_translation_orbitSpace Ψe.smooth_smul
  exact he.isEmbedding.toHomeomorph.symm.isEmbedding.metrizableSpace

/-- **2021 Theorem 19.6.8 (5), p. 897**: `|P| : |E| → |S|` is continuous for `T̄` and `T`. -/
theorem theorem_19_6_8_five (hB : B.base.U.HasClassUniformizers) :
    Continuous[B.topE hB, B.topS hB] μ.orbitProj := by
  let _i₁ := B.topE hB
  let _i₂ := B.topS hB
  refine continuous_def.2 fun W hW => ?_
  change B.toE.U.NatOpen _
  intro z hz
  obtain ⟨x, hx, Ψe, α, hα, hαx, a, ha⟩ := B.hBE hB z
  have hc := B.base.continuous_π_obj hB (Ψ := (B.U.str Ψe ⟨α, hα⟩).toBase) ⟨Ψe, hα, rfl⟩
  refine ⟨x, hx, Ψe, ⟨α, hα, hαx, a, ha⟩, a, ha,
    (B.U.str Ψe ⟨α, hα⟩).p ⁻¹' ((fun q => C.π ((B.U.str Ψe ⟨α, hα⟩).toBase.obj q)) ⁻¹' W),
    (hW.preimage hc).preimage (B.U.str Ψe ⟨α, hα⟩).continuous_p, ?_, ?_⟩
  · change C.π ((B.U.str Ψe ⟨α, hα⟩).toBase.obj ((B.U.str Ψe ⟨α, hα⟩).p a)) ∈ W
    rw [← (B.U.str Ψe ⟨α, hα⟩).P_obj', ha, ← μ.orbitProj_π, hx]
    exact hz
  · rintro _ ⟨q, hq, rfl⟩
    change C.π (μ.P (Ψe.obj q)) ∈ W
    rw [(B.U.str Ψe ⟨α, hα⟩).P_obj']
    exact hq

/-! ### Proposition 19.6.9 -/

/-- **The zero section `|S| → |E|`, `|α| ↦ |(α, 0)|`, is continuous** for `T` and `T̄`. -/
theorem continuous_zeroOrbit (hB : B.base.U.HasClassUniformizers) :
    Continuous[B.topS hB, B.topE hB] μ.zeroOrbit := by
  let _i₁ := B.topS hB
  let _i₂ := B.topE hB
  refine continuous_def.2 fun W hW => ?_
  change B.base.U.NatOpen _
  intro z hz
  obtain ⟨α, rfl, _, Ψe, hΨe, rfl⟩ := hB z
  obtain ⟨o, ho⟩ := B.U.isAt α Ψe hΨe
  have hz' : Continuous (fiberZero (B.U.str Ψe ⟨α, hΨe⟩).p) :=
    continuousOn_univ.1 (B.U.str Ψe ⟨α, hΨe⟩).B.isScSmoothSection_fiberZero.2.continuousOn
  have hc := (B.toE.continuous_π_obj (B.hBE hB) (B.U.mem_toE hΨe ho)).comp hz'
  refine ⟨α, rfl, _, ⟨Ψe, hΨe, rfl⟩, o, ho, _, hW.preimage hc, ?_, ?_⟩
  · change μ.cat.π (Ψe.obj (fiberZero (B.U.str Ψe ⟨α, hΨe⟩).p o)) ∈ W
    rw [StrongBundleStr.obj_fiberZero, ho]
    exact hz
  · rintro _ ⟨q, hq, rfl⟩
    change μ.cat.π (μ.zero ((B.U.str Ψe ⟨α, hΨe⟩).toBase.obj q)) ∈ W
    rw [← StrongBundleStr.obj_fiberZero]
    exact hq

/-- **The zero section `|S| → |E|` is a topological embedding** (with left inverse `|P|`). -/
theorem isEmbedding_zeroOrbit (hB : B.base.U.HasClassUniformizers) :
    @IsEmbedding _ _ (B.topS hB) (B.topE hB) μ.zeroOrbit := by
  let _i₁ := B.topS hB
  let _i₂ := B.topE hB
  exact Function.LeftInverse.isEmbedding (f := μ.orbitProj) μ.orbitProj_zeroOrbit
    (B.theorem_19_6_8_five hB) (B.continuous_zeroOrbit hB)

/-- **2021 Proposition 19.6.9, p. 898**: `T` is metrizable iff `T̄` is.  (`⇒`: `|P|` is
continuous and `|P|⁻¹(V)` is metrizable over the open sets `V` of Theorem 19.6.8 (4), so
`|E|` is metrizable over the paracompact `|S|`; `⇐`: the zero section embeds `|S|` into `|E|`.) -/
theorem proposition_19_6_9 (hB : B.base.U.HasClassUniformizers) :
    @MetrizableSpace _ (B.topS hB) ↔ @MetrizableSpace _ (B.topE hB) := by
  let _i₁ := B.topS hB
  let _i₂ := B.topE hB
  constructor
  · intro hm
    have := paracompactSpace_of_metrizableSpace C.OrbitSpace
    let _ := metrizableSpaceMetric C.OrbitSpace
    exact metrizableSpace_of_pullback μ.orbitProj (B.theorem_19_6_8_five hB)
      (B.theorem_19_6_8_four hB)
  · intro hm
    exact (B.isEmbedding_zeroOrbit hB).metrizableSpace

/-! ### Definition 19.6.10, Theorem 19.6.11, Lemma 19.6.12 -/

/-- **2021 Definition 19.6.10, p. 898**, as printed (with `F̄_h = F̄_{p(h̄)}` for the
representative `F̄`): `Ŵ ⊂ M(Ψ̄, Ψ̄')` is open if for every `h̄ ∈ Ŵ` there is an open
`V̂ ∋ s(h̄)` in `K|V(p(s(h̄)))` with `F̄_h(V̂) ⊂ Ŵ`. -/
def BarOpenTr (Ψ Ψ' : B.U.Unif) (W : Set (Ψ.1.Trans Ψ'.1)) : Prop :=
  ∀ h ∈ W, ∃ V : Set Ψ.1.O, IsOpen V ∧ h.src ∈ V ∧
    V ⊆ (B.U.strU Ψ).p ⁻¹'
      B.rep.toTD.dom (B.U.baseUnif Ψ) (B.U.baseUnif Ψ') ((B.U.strU Ψ).proj (B.U.strU Ψ') h) ∧
      B.U.mapBar B.rep.toTD Ψ Ψ' ((B.U.strU Ψ).proj (B.U.strU Ψ') h) '' V ⊆ W

/-- **Definition 19.6.10 is the openness `T^F_{Ψ̄,Ψ̄'}` (Lemma 19.3.1) of the transition data
`toETD` of `E_μ`.** -/
theorem definition_19_6_10 (Ψ Ψ' : B.U.Unif) (W : Set (Ψ.1.Trans Ψ'.1)) :
    B.BarOpenTr Ψ Ψ' W ↔ B.rep.toETD.IsOpenTr (B.U.toEUnif Ψ) (B.U.toEUnif Ψ') W :=
  Iff.rfl

/-- `M(Ψ̄, Ψ̄')` with its natural topology `T̄_{Ψ̄,Ψ̄'}`. -/
abbrev MBar (Ψ Ψ' : B.toE.U.Unif) : Type u := B.rep.toETD.Tr Ψ Ψ'

/-- `T̄_{Ψ̄,Ψ̄'}` is the topology of the transition construction of `E_μ` (Definition 19.3.2):
it does not depend on the representative. -/
theorem topology_MBar (Ψ Ψ' : B.toE.U.Unif) :
    B.toE.𝓕.topology Ψ Ψ' = B.rep.toETD.topology Ψ Ψ' :=
  (B.toE.definition_19_3_2 B.toE_rep Ψ Ψ').1

/-- **2021 Theorem 19.6.11, p. 898, first assertions**: `T̄_{Ψ̄,Ψ̄'}` is a topology, and
`M(Ψ̄, Ψ̄')` is regular, Hausdorff and locally metrizable. -/
theorem theorem_19_6_11 (Ψ Ψ' : B.toE.U.Unif) :
    (B.rep.toETD.IsOpenTr Ψ Ψ' univ ∧
      (∀ W₁ W₂, B.rep.toETD.IsOpenTr Ψ Ψ' W₁ → B.rep.toETD.IsOpenTr Ψ Ψ' W₂ →
        B.rep.toETD.IsOpenTr Ψ Ψ' (W₁ ∩ W₂)) ∧
      ∀ S : Set (Set (Ψ.1.Trans Ψ'.1)), (∀ W ∈ S, B.rep.toETD.IsOpenTr Ψ Ψ' W) →
        B.rep.toETD.IsOpenTr Ψ Ψ' (⋃₀ S)) ∧
    RegularSpace (B.MBar Ψ Ψ') ∧ T2Space (B.MBar Ψ Ψ') ∧
      ∀ h : B.MBar Ψ Ψ', ∃ W : Set (B.MBar Ψ Ψ'), IsOpen W ∧ h ∈ W ∧ MetrizableSpace W :=
  ⟨B.rep.toETD.isOpenTr_topology Ψ Ψ', B.rep.toETD.regularSpace Ψ Ψ', B.rep.toETD.t2Space Ψ Ψ',
    B.rep.toETD.exists_isOpen_metrizableSpace Ψ Ψ'⟩

/-- **2021 Theorem 19.6.11 (1), p. 898**: `s : M(Ψ̄, Ψ̄') → K` is a local homeomorphism. -/
theorem theorem_19_6_11_one (Ψ Ψ' : B.toE.U.Unif) :
    IsLocalHomeomorph fun h : B.MBar Ψ Ψ' => (h : Ψ.1.Trans Ψ'.1).src :=
  B.rep.toETD.isLocalHomeomorph_src Ψ Ψ'

/-- **2021 Theorem 19.6.11 (2), p. 898**: `t : M(Ψ̄, Ψ̄') → K'` is a local homeomorphism. -/
theorem theorem_19_6_11_two (Ψ Ψ' : B.toE.U.Unif) :
    IsLocalHomeomorph fun h : B.MBar Ψ Ψ' => (h : Ψ.1.Trans Ψ'.1).tgt :=
  B.rep.toETD.isLocalHomeomorph_tgt Ψ Ψ'

/-- **2021 Theorem 19.6.11 (3), p. 898**: `u : K → M(Ψ̄, Ψ̄)` is continuous. -/
theorem theorem_19_6_11_three (Ψ : B.toE.U.Unif) :
    Continuous fun a : Ψ.1.O =>
      (B.rep.toETD.toTr (TransitionSet.unit a : Ψ.1.Trans Ψ.1) : B.MBar Ψ Ψ) :=
  B.rep.toETD.continuous_unit Ψ

/-- **2021 Theorem 19.6.11 (4), p. 898**: `ι : M(Ψ̄, Ψ̄') → M(Ψ̄', Ψ̄)` is a homeomorphism. -/
def theorem_19_6_11_four (Ψ Ψ' : B.toE.U.Unif) : B.MBar Ψ Ψ' ≃ₜ B.MBar Ψ' Ψ :=
  B.rep.toETD.invHomeomorph Ψ Ψ'

theorem theorem_19_6_11_four_apply (Ψ Ψ' : B.toE.U.Unif) (h : B.MBar Ψ Ψ') :
    B.theorem_19_6_11_four Ψ Ψ' h = (h : Ψ.1.Trans Ψ'.1).inv := rfl

/-- **2021 Theorem 19.6.11 (5), p. 899**: `m : M(Ψ̄', Ψ̄'') ₛ×ₜ M(Ψ̄, Ψ̄') → M(Ψ̄, Ψ̄'')` is
continuous. -/
theorem theorem_19_6_11_five (Ψ Ψ' Ψ'' : B.toE.U.Unif) :
    Continuous (B.rep.toETD.mulMap Ψ Ψ' Ψ'') :=
  B.rep.toETD.continuous_mulMap

/-- **2021 Theorem 19.6.11 (6), p. 899** (read as the projection): `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` is
continuous for the natural topologies (on `M(Ψ, Ψ')` the one of the underlying transition data
`F`, the natural topology of Definition 19.3.2 by `base_rep`). -/
theorem theorem_19_6_11_six (Ψ Ψ' : B.toE.U.Unif) :
    Continuous fun h : B.MBar Ψ Ψ' =>
      (B.rep.toTD.toTr ((B.U.strU (B.U.ofE Ψ)).proj (B.U.strU (B.U.ofE Ψ')) h) :
        B.rep.toTD.Tr (B.U.baseUnif (B.U.ofE Ψ)) (B.U.baseUnif (B.U.ofE Ψ'))) := by
  refine continuous_iff_continuousAt.2 fun h₀ => ?_
  obtain ⟨h, rfl⟩ : ∃ h : Ψ.1.Trans Ψ'.1, B.rep.toETD.toTr h = h₀ := ⟨h₀, rfl⟩
  set S := B.U.strU (B.U.ofE Ψ)
  set S' := B.U.strU (B.U.ofE Ψ')
  have hev : (fun g : B.MBar Ψ Ψ' => B.rep.toTD.toTr (S.proj S' g)) =ᶠ[𝓝 (B.rep.toETD.toTr h)]
      fun g => B.rep.toTD.toTr
        (B.rep.toTD.map (B.U.baseUnif (B.U.ofE Ψ)) (B.U.baseUnif (B.U.ofE Ψ')) (S.proj S' h)
          (S.p (g : Ψ.1.Trans Ψ'.1).src)) := by
    filter_upwards [(B.rep.toETD.sheet Ψ Ψ' h).open_target.mem_nhds
      (B.rep.toETD.mem_sheet_target Ψ Ψ' h)] with g hg
    obtain ⟨q, hq, rfl⟩ := hg
    change B.rep.toTD.toTr (S.proj S' (B.U.mapBar B.rep.toTD _ _ (S.proj S' h) q)) =
      B.rep.toTD.toTr (B.rep.toTD.map (B.U.baseUnif (B.U.ofE Ψ)) (B.U.baseUnif (B.U.ofE Ψ'))
        (S.proj S' h) (S.p (B.U.mapBar B.rep.toTD _ _ (S.proj S' h) q).src))
    rw [StrongBundleUniformizerConstruction.proj_mapBar,
      StrongBundleUniformizerConstruction.definition_19_6_4_A_src hq]
  refine ContinuousAt.congr ?_ hev.symm
  have h1 : ContinuousAt (fun g : B.MBar Ψ Ψ' => S.p (g : Ψ.1.Trans Ψ'.1).src)
      (B.rep.toETD.toTr h) :=
    (S.continuous_p.comp (B.rep.toETD.continuous_src Ψ Ψ')).continuousAt
  exact ContinuousAt.comp (g := fun q => B.rep.toTD.toTr (B.rep.toTD.map
      (B.U.baseUnif (B.U.ofE Ψ)) (B.U.baseUnif (B.U.ofE Ψ')) (S.proj S' h) q))
    (B.rep.toTD.continuousAt_map (B.U.baseUnif (B.U.ofE Ψ)) (B.U.baseUnif (B.U.ofE Ψ'))
      (S.proj S' h)
      (B.rep.toTD.mem_dom (B.U.baseUnif (B.U.ofE Ψ)) (B.U.baseUnif (B.U.ofE Ψ')) (S.proj S' h))) h1

/-- **2021 Lemma 19.6.12, p. 899**: `T̄_{Ψ̄,Ψ̄'}` is metrizable.  This holds without the
properness condition of the text (the transition sets of any transition data are
metrizable). -/
theorem lemma_19_6_12 (Ψ Ψ' : B.toE.U.Unif) : MetrizableSpace (B.MBar Ψ Ψ') :=
  B.rep.toETD.metrizableSpace Ψ Ψ'

/-- **2021 Lemma 19.6.12, p. 899**, as printed: if the underlying basic construction satisfies the
properness condition, `T̄_{Ψ̄,Ψ̄'}` is metrizable. -/
theorem lemma_19_6_12_book (hB : B.base.U.HasClassUniformizers) (_hv : B.base.PropernessV2 hB)
    (Ψ Ψ' : B.toE.U.Unif) : MetrizableSpace (B.MBar Ψ Ψ') :=
  B.lemma_19_6_12 Ψ Ψ'

end BasicStrongBundleConstruction

end GroupoidalCategory

end Polyfold
