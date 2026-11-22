import Polyfold.Chapter17.PolyfoldLevels
import Polyfold.Chapter17.AdmissibleTripleBasic
import Polyfold.Chapter8.TangentLocal
import Polyfold.Chapter2.TangentMapLinear

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.2 (pp. 767–770): **Lemma 17.2.1**, **Definitions 17.2.2, 17.2.3**, **Proposition 17.2.4** and
**Proposition 17.2.5**.  Numbers and pages are the 2021 text's.

# Tangent vectors and tangent spaces of a polyfold `C = (C, F, M)`

## The text, paraphrased

(pp. 767–768) For an object `α` of `C¹` and `Ψ, Ψ' ∈ F(α)`, `Ψ(q) = α = Ψ'(q')`, the element
`(q, 1_α, q') ∈ M(Ψ, Ψ')` has an admissible triple `(U(q), U(q, 1_α, q'), U(q'))`, and
`σ = t ∘ (s|U(q, 1_α, q'))⁻¹ : U(q) → U(q')` is an sc-diffeomorphism.  `(α, Ψ, h) ∼ (α, Ψ', h')`
for `h ∈ T_qO`, `h' ∈ T_{q'}O'` iff `Tσ(h) = h'`.  (**Lemma 17.2.1**) This is an equivalence
relation: `σ = id` for `(q, 1_α, q)`, the `σ`s of `(q, 1_α, q')` and `(q', 1_α, q)` are inverse,
and `σ' ∘ σ = σ''` near `q`.  (**Definition 17.2.2**) A tangent vector at `α` is a class
`[α, Ψ, h]`.  (**Definition 17.2.3**) `T_αC` is the set of these classes, a vector space with
`[α, Ψ, h] + λ[α, Ψ, k] = [α, Ψ, h + λk]`.  (**Proposition 17.2.4**) `T_αC` is a Banachable space:
`S_Ψ : T_αC → T_qO`, `[α, Ψ, h] ↦ h`, is a topological linear isomorphism, independent of `Ψ`
since `S_{Ψ'} ∘ S_Ψ⁻¹ = Tσ(q)`; for smooth `α`, `T_αC` is sc-Banachable.  (pp. 769–770) For
`φ : α → α'` on level `1`, `Tφ[α, Ψ, h] = [α', Ψ', Tσ(h)]` (17.31), `σ` the sc-diffeomorphism of
`(q₀, φ, q₀') ∈ M(Ψ, Ψ')`; `Tψ ∘ Tφ = T(ψ ∘ φ)`.  (**Proposition 17.2.5**) `μ_C : C¹ → Ban`,
`α ↦ T_αC`, `φ ↦ Tφ`, is a functor (17.32).

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* **The local sc-diffeomorphism of an admissible triple** `AdmissibleTriple.sigma`
  (`σ = t ∘ (s|U)⁻¹`), `AdmissibleTriple.isScDiffeoOn_sigma`, `sigma_src`, the germ statements
  `AdmissibleTriple.sigma_eqOn` (two triples give the same `σ` on `s(U ∩ U')`) and
  `AdmissibleTriple.exists_srcInv_eq` (a continuous local section of `s` through `a` agrees with
  `(s|U)⁻¹` near `s(a)`).
* **The tangent of an element of a transition set**: `transMap a : TO → TO'`, `Tσ` for the
  chosen triple, independent of the triple (`transMap_eq`, `transMap_eq_of_mem`); the laws
  `transMap_unit` (`σ = id` near `q` for `(q, 1, q)`), **`transMap_comp`** (`σ_{a ∘ b} = σ_a ∘ σ_b`
  near `s(b)`, from the continuity of `m`, Definition 17.1.8 (c)), `transMap_inv_transMap`; on
  the fibres a topological linear isomorphism `transTangent a : T_qO ≃L[ℝ] T_{q'}O'`
  (`Tσ(q)`, Theorem 2.3.16 on fibres).
* **Lemma 17.2.1**: `TangentTuple α` (the tuples `(α, Ψ, h)`), `TangentRel`, `lemma_17_2_1`.
* **Definitions 17.2.2, 17.2.3**: `TangentSpaceAt α` (`T_αC`, the quotient),
  `tangentVector` (`[α, Ψ, h]`, Definition 17.2.2).
* **Proposition 17.2.4**: `tangentChart` (`S_Ψ : T_αC ≃ T_qO`, for every `Ψ ∈ F(α)`); the linear
  and topological structure of `T_αC` for `α` in `TangentObj` (transported along `S_Ψ` of a
  reference uniformizer); `proposition_17_2_4` (`S_Ψ` is a topological linear isomorphism for
  every `Ψ ∈ F(α)`, and `S_{Ψ'} ∘ S_Ψ⁻¹ = Tσ(q)`), `definition_17_2_3` (the text's formula
  `[α, Ψ, h] + λ[α, Ψ, k] = [α, Ψ, h + λk]` for every `Ψ`), `proposition_17_2_4_banachable`
  (a complete norm inducing the topology), `proposition_17_2_4_sc` (for smooth `α`, the charts
  of `T_αC` through every `Ψ` and every chart of `O` are sc-subspaces, and the transition
  between two of them is an sc-operator).
* **Proposition 17.2.5**: `tangentMorAt φ` (`Tφ`, (17.31), for any choice of `Ψ, Ψ'`:
  `tangentMorAt_mk`), `tangentMorCLE` (a topological linear isomorphism), `tangentMorAt_unit`,
  `tangentMorAt_comp`, `proposition_17_2_5`.

## Readings

* The tuples `(α, Ψ, h)` are read with `Ψ ∈ F(α)` and `h ∈ TO` lying over the point `q` with
  `Ψ(q) = α` (unique, since `Ψ` is injective on objects).  `α` on level `1` is then automatic
  for a nonempty set of tuples: `T_αC = ∅` unless `α ∈ C¹` and `F(α) ≠ ∅` (`TangentObj`).
* `σ` is attached to an element `a ∈ M(Ψ, Ψ')` through a chosen admissible triple; `Tσ` at the
  points over `s(a)` does not depend on the triple (`transMap_eq`), as the text uses implicitly.
* "Banachable" is read as: a topological vector space whose topology is induced by a complete
  norm (`proposition_17_2_4_banachable`); the norm is a definition, not an instance (as for
  `T_xX` in Chapter 2).  "sc-Banachable (using an obvious definition)" is read through the
  charts: every chart `T_αC → T_qO → T_{φ(q)}O_φ ⊆ E` has an sc-subspace as image, and the
  changes of charts are sc-operators.
* `μ_C : C¹ → Ban` is formalized by its object map `α ↦ T_αC` and its morphism map
  `φ ↦ Tφ : T_αC ≃L[ℝ] T_{α'}C` with the functor laws; the category `Ban` itself is not built.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

universe u

namespace Polyfold

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

theorem levelVal_tangentProj_of_mem {X : Type*} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] {P : MPolyfold X} {x : P.Level 1} {h : P.TangentSpace}
    (hh : h ∈ P.tangentFiber x) : P.levelVal 1 (P.tangentProj h) = P.levelVal 1 x := by
  rw [MPolyfold.tangentProj_eq_of_mem_fiber hh]

/-! ### The local sc-diffeomorphism `σ` of an admissible triple -/

namespace AdmissibleTriple

variable {Ψ Ψ' : S.Unif} {a : S.Tr Ψ Ψ'} (T : S.AdmissibleTriple a)

/-- **`σ = t ∘ (s|U(o, φ, o'))⁻¹ : U(o) → U(o')`** of an admissible triple (2021 p. 768). -/
def sigma : Ψ.1.O → Ψ'.1.O := fun p => (T.srcInv p).tgt

/-- `σ⁻¹ = s ∘ (t|U(o, φ, o'))⁻¹`. -/
def sigmaInv : Ψ'.1.O → Ψ.1.O := fun p => (T.tgtInv p).src

/-- `σ : U(o) → U(o')` is an sc-diffeomorphism (2021 p. 768). -/
theorem isScDiffeoOn_sigma :
    Ψ.1.P.IsScDiffeoOn Ψ'.1.P T.sigma T.sigmaInv T.srcSet T.tgtSet :=
  MPolyfold.IsScDiffeoOn.comp T.isScDiffeoOn_tgt T.isScDiffeoOn_src.symm

theorem isScSmoothOn_sigma : Ψ.1.P.IsScSmoothOn Ψ'.1.P T.sigma T.srcSet :=
  T.isScDiffeoOn_sigma.isScSmoothOn

theorem sigma_eq {b : S.Tr Ψ Ψ'} (hb : b ∈ T.carrier) : T.sigma b.src = b.tgt := by
  change (T.srcInv b.src).tgt = b.tgt
  rw [T.srcInv_eq hb]

/-- `σ(o) = o'`. -/
theorem sigma_src : T.sigma a.src = a.tgt := T.sigma_eq T.mem_carrier

/-- **Germ independence**: two admissible triples (of possibly different elements) give the
same `σ` on `s(U ∩ U')` (Lemma 17.1.13). -/
theorem sigma_eqOn {a₁ a₂ : S.Tr Ψ Ψ'} (T₁ : S.AdmissibleTriple a₁) (T₂ : S.AdmissibleTriple a₂) :
    EqOn T₁.sigma T₂.sigma ((fun b : S.Tr Ψ Ψ' => b.src) '' (T₁.carrier ∩ T₂.carrier)) := by
  rintro _ ⟨b, hb, rfl⟩
  rw [T₁.sigma_eq hb.1, T₂.sigma_eq hb.2]

theorem isOpen_src_image {W : Set (S.Tr Ψ Ψ')} (hW : IsOpen W) :
    IsOpen ((fun b : S.Tr Ψ Ψ' => b.src) '' W) :=
  (S.isLocalScDiffeo_trSrc Ψ Ψ').isOpenMap W hW

/-- **A continuous local section of `s` through `a` is `(s|U)⁻¹` near `s(a)`.** -/
theorem exists_srcInv_eq {f : Ψ.1.O → S.Tr Ψ Ψ'} {W : Set Ψ.1.O} (hW : IsOpen W)
    (haW : a.src ∈ W) (hf : ContinuousOn f W) (hfs : ∀ p ∈ W, (f p).src = p)
    (hfa : f a.src = a) :
    ∃ W' : Set Ψ.1.O, IsOpen W' ∧ a.src ∈ W' ∧ W' ⊆ W ∩ T.srcSet ∧
      ∀ p ∈ W', T.srcInv p = f p := by
  refine ⟨W ∩ f ⁻¹' T.carrier, hf.isOpen_inter_preimage hW T.isOpen_carrier,
    ⟨haW, by rw [mem_preimage, hfa]; exact T.mem_carrier⟩, fun p hp => ⟨hp.1, ?_⟩,
    fun p hp => ?_⟩
  · rw [← hfs p hp.1]
    exact T.isScDiffeoOn_src.mapsTo hp.2
  · conv_lhs => rw [← hfs p hp.1]
    exact T.srcInv_eq hp.2

end AdmissibleTriple

/-! ### The tangent `Tσ` of an element of a transition set -/

variable (S)

/-- The chosen admissible triple of `a ∈ M(Ψ, Ψ')`. -/
def triple {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ') : S.AdmissibleTriple a :=
  (S.exists_admissibleTriple a).some

/-- **`Tσ : TO → TO'`** for `a ∈ M(Ψ, Ψ')`, `σ` the sc-diffeomorphism of an admissible triple of
`a` (2021 pp. 768, 769: `Tσ(h)` for `h` over `s(a)`; elsewhere a value without meaning). -/
def transMap {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ') : Ψ.1.P.TangentSpace → Ψ'.1.P.TangentSpace :=
  MPolyfold.tangentMapOn (S.triple a).isScSmoothOn_sigma

variable {S}

/-- **`Tσ(h)` does not depend on the admissible triple**: for every triple `T` of `a` and `h`
over `s(a)`. -/
theorem transMap_eq {Ψ Ψ' : S.Unif} {a : S.Tr Ψ Ψ'} (T : S.AdmissibleTriple a)
    {h : Ψ.1.P.TangentSpace} (hh : Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj h) = a.src) :
    S.transMap a h = MPolyfold.tangentMapOn T.isScSmoothOn_sigma h := by
  set W := (fun b : S.Tr Ψ Ψ' => b.src) '' ((S.triple a).carrier ∩ T.carrier)
  have hWo : IsOpen W := AdmissibleTriple.isOpen_src_image
    ((S.triple a).isOpen_carrier.inter T.isOpen_carrier)
  have hW1 : W ⊆ (S.triple a).srcSet := by
    rintro _ ⟨b, hb, rfl⟩; exact (S.triple a).isScDiffeoOn_src.mapsTo hb.1
  have hW2 : W ⊆ T.srcSet := by
    rintro _ ⟨b, hb, rfl⟩; exact T.isScDiffeoOn_src.mapsTo hb.2
  exact MPolyfold.tangentMapOn_congr _ _ hWo hW1 hW2
    (AdmissibleTriple.sigma_eqOn (S.triple a) T)
    (show _ ∈ W by rw [hh]; exact ⟨a, ⟨(S.triple a).mem_carrier, T.mem_carrier⟩, rfl⟩)

/-- **`Tσ_b = Tσ` on a sheet**: for a triple `T` of `a` and `b` in its sheet `U(a)`, the tangent
of `b` at `s(b)` is `Tσ` for the `σ` of `a` (the germ of `σ` near `s(b)` is that of `b`). -/
theorem transMap_eq_of_mem {Ψ Ψ' : S.Unif} {a b : S.Tr Ψ Ψ'} (T : S.AdmissibleTriple a)
    (hb : b ∈ T.carrier) {h : Ψ.1.P.TangentSpace}
    (hh : Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj h) = b.src) :
    S.transMap b h = MPolyfold.tangentMapOn T.isScSmoothOn_sigma h := by
  exact transMap_eq ⟨T.srcSet, T.carrier, T.tgtSet, T.srcInv, T.tgtInv, hb, T.isScDiffeoOn_src,
      T.isScDiffeoOn_tgt⟩ hh

/-- `Tσ(h)` lies over `t(a)` for `h` over `s(a)`. -/
theorem base_transMap {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ') {h : Ψ.1.P.TangentSpace}
    (hh : Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj h) = a.src) :
    Ψ'.1.P.levelVal 1 (Ψ'.1.P.tangentProj (S.transMap a h)) = a.tgt := by
  have hmem : h ∈ Ψ.1.P.tangentPreimage (S.triple a).srcSet := by
    rw [MPolyfold.mem_tangentPreimage, hh]; exact (S.triple a).src_mem
  rw [transMap, MPolyfold.levelVal_tangentProj_tangentMapOn _ hmem, hh,
    (S.triple a).sigma_src]

/-- **`σ = id` near `q` for `(q, 1, q)`** (2021 p. 768, the proof of Lemma 17.2.1): `Tσ(h) = h`. -/
theorem transMap_unit {Ψ : S.Unif} (q : Ψ.1.O) {h : Ψ.1.P.TangentSpace}
    (hh : Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj h) = q) :
    S.transMap (S.toTr (GroupoidStr.TransitionSet.unit q) : S.Tr Ψ Ψ) h = h := by
  set a : S.Tr Ψ Ψ := S.toTr (GroupoidStr.TransitionSet.unit q)
  set T := S.triple a
  have hu := S.isScSmoothMap_trUnit Ψ
  obtain ⟨W', hW'o, hqW', hW'sub, hW'eq⟩ := T.exists_srcInv_eq (f := fun p =>
      S.toTr (GroupoidStr.TransitionSet.unit p)) isOpen_univ (mem_univ _)
    hu.continuousOn (fun p _ => rfl) rfl
  have hid : EqOn T.sigma id W' := fun p hp => by
    change (T.srcInv p).tgt = p
    rw [hW'eq p hp]; rfl
  have hmem : h ∈ Ψ.1.P.tangentPreimage W' := by
    rw [MPolyfold.mem_tangentPreimage, hh]; exact hqW'
  have h1 := MPolyfold.tangentMapOn_eqOn_id (T.isScSmoothOn_sigma.mono hW'o
    (fun p hp => (hW'sub hp).2)) hid hmem
  exact (MPolyfold.tangentMapOn_congr _ (T.isScSmoothOn_sigma.mono hW'o
    (fun p hp => (hW'sub hp).2)) hW'o (fun p hp => (hW'sub hp).2)
    subset_rfl (eqOn_refl _ _) hmem).trans h1

/-- **`σ_{a ∘ b} = σ_a ∘ σ_b` near `s(b)`, hence `T(σ_{a ∘ b}) = Tσ_a ∘ Tσ_b`** (2021 p. 768, the
transitivity in the proof of Lemma 17.2.1, and p. 770).  The text's "for `p` near `q`" is proved
with the continuity of the multiplication `m` (Definition 17.1.8 (c)): `p ↦ m((s|U(a))⁻¹(σ_b p),
(s|U(b))⁻¹ p)` is a continuous local section of `s` through `a ∘ b`. -/
theorem transMap_comp {Ψ Ψ' Ψ'' : S.Unif} (a : S.Tr Ψ' Ψ'') (b : S.Tr Ψ Ψ')
    (hab : C.toGroupoidStr.src a.mor = C.toGroupoidStr.tgt b.mor) (hs : a.src = b.tgt)
    {h : Ψ.1.P.TangentSpace} (hh : Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj h) = b.src) :
    S.transMap (S.toTr (GroupoidStr.TransitionSet.comp a b hab) : S.Tr Ψ Ψ'') h =
      S.transMap a (S.transMap b h) := by
  set Ta := S.triple a
  set Tb := S.triple b
  set ab : S.Tr Ψ Ψ'' := S.toTr (GroupoidStr.TransitionSet.comp a b hab)
  set Tab := S.triple ab
  let _ := MPolyfold.paracompactSpace_prod (S.transPolyfold Ψ' Ψ'') (S.transPolyfold Ψ Ψ')
  set d := MPolyfold.fibredSubDataL Ta.isScDiffeoOn_src
    (S.isLocalScDiffeo_trTgt Ψ Ψ').isScSmoothMap
  let a₀ : MPolyfold.fibredProduct (fun x : S.Tr Ψ' Ψ'' => x.src)
      (fun y : S.Tr Ψ Ψ' => y.tgt) := ⟨(a, b), hs⟩
  have hm := (S.isScSmoothMap_trMul Ψ Ψ' Ψ'').isScSmoothOn_sheet Ta.isScDiffeoOn_src a₀
  set F : S.Tr Ψ Ψ' → S.Tr Ψ Ψ'' := fun y =>
    S.toTr (GroupoidStr.TransitionSet.mul (d.retractInto a₀ (Ta.srcInv y.tgt, y))) with hFdef
  have hFc : ContinuousOn F ((fun y : S.Tr Ψ Ψ' => y.tgt) ⁻¹' Ta.srcSet) :=
    (show (S.transPolyfold Ψ Ψ').IsScSmoothOn (S.transPolyfold Ψ Ψ'') F _ from hm).continuousOn
  have hFval : ∀ y : S.Tr Ψ Ψ', ∀ hy : y.tgt ∈ Ta.srcSet,
      F y = S.toTr (GroupoidStr.TransitionSet.comp (Ta.srcInv y.tgt) y
        (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt (Ta.src_srcInv hy))) := by
    intro y hy
    have hv := d.retractInto_val a₀ (x := (Ta.srcInv y.tgt, y)) ⟨Ta.srcInv_mem hy, hy⟩
    refine GroupoidStr.TransitionSet.ext ?_ ?_ ?_
    · exact congrArg (fun p : S.Tr Ψ' Ψ'' × S.Tr Ψ Ψ' => p.2.src) hv
    · exact congrArg (fun p : S.Tr Ψ' Ψ'' × S.Tr Ψ Ψ' =>
        C.toGroupoidStr.comp p.1.mor p.2.mor) hv
    · exact congrArg (fun p : S.Tr Ψ' Ψ'' × S.Tr Ψ Ψ' => p.1.tgt) hv
  -- the section `f = F ∘ (s|U(b))⁻¹` on `W`
  set W : Set Ψ.1.O := Tb.srcSet ∩ Tb.srcInv ⁻¹' ((fun y : S.Tr Ψ Ψ' => y.tgt) ⁻¹' Ta.srcSet)
  have hsrcInvc : ContinuousOn Tb.srcInv Tb.srcSet :=
    Tb.isScDiffeoOn_src.isScSmoothOn_inv.continuousOn
  have hWo : IsOpen W := hsrcInvc.isOpen_inter_preimage Tb.isOpen_srcSet
    (Ta.isOpen_srcSet.preimage (S.continuous_trTgt Ψ Ψ'))
  have hbW : b.src ∈ W := by
    refine ⟨Tb.src_mem, ?_⟩
    change (Tb.srcInv b.src).tgt ∈ Ta.srcSet
    rw [Tb.srcInv_eq Tb.mem_carrier, ← hs]
    exact Ta.src_mem
  have hfc : ContinuousOn (F ∘ Tb.srcInv) W :=
    hFc.comp (hsrcInvc.mono inter_subset_left) fun p hp => hp.2
  have hfval : ∀ p (hp : p ∈ W), (F ∘ Tb.srcInv) p = S.toTr (GroupoidStr.TransitionSet.comp
      (Ta.srcInv (Tb.srcInv p).tgt) (Tb.srcInv p)
      (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt (Ta.src_srcInv hp.2))) :=
    fun p hp => hFval _ hp.2
  have hfs : ∀ p ∈ W, ((F ∘ Tb.srcInv) p).src = p := fun p hp => by
    rw [hfval p hp]; exact Tb.src_srcInv hp.1
  have hfa : (F ∘ Tb.srcInv) ab.src = ab := by
    have hab' : ab.src = b.src := rfl
    rw [hab', hfval _ hbW]
    have hb : Tb.srcInv b.src = b := Tb.srcInv_eq Tb.mem_carrier
    have ha : Ta.srcInv b.tgt = a := by rw [← hs]; exact Ta.srcInv_eq Ta.mem_carrier
    refine GroupoidStr.TransitionSet.ext ?_ ?_ ?_
    · exact congrArg (fun y : S.Tr Ψ Ψ' => y.src) hb
    · change C.toGroupoidStr.comp (Ta.srcInv (Tb.srcInv b.src).tgt).mor (Tb.srcInv b.src).mor =
        C.toGroupoidStr.comp a.mor b.mor
      rw [hb, ha]
    · change (Ta.srcInv (Tb.srcInv b.src).tgt).tgt = a.tgt
      rw [hb, ha]
  obtain ⟨W', hW'o, hW', hW'sub, hW'eq⟩ := Tab.exists_srcInv_eq hWo hbW hfc hfs hfa
  have hcomp : EqOn Tab.sigma (Ta.sigma ∘ Tb.sigma) W' := fun p hp => by
    change (Tab.srcInv p).tgt = (Ta.srcInv (Tb.srcInv p).tgt).tgt
    rw [hW'eq p hp, hfval p (hW'sub hp).1]
    rfl
  have hW'b : W' ⊆ Tb.srcSet := fun p hp => (hW'sub hp).1.1
  have hmaps : MapsTo Tb.sigma W' Ta.srcSet := fun p hp => (hW'sub hp).1.2
  have hmem : h ∈ Ψ.1.P.tangentPreimage W' := by
    rw [MPolyfold.mem_tangentPreimage, hh]; exact hW'
  have hbmono := Tb.isScSmoothOn_sigma.mono hW'o hW'b
  have h1 := MPolyfold.tangentMapOn_congr Tab.isScSmoothOn_sigma
    (Ta.isScSmoothOn_sigma.comp hbmono hmaps) hW'o (fun p hp => (hW'sub hp).2) subset_rfl
    hcomp hmem
  have h2 := MPolyfold.tangentMapOn_comp Ta.isScSmoothOn_sigma hbmono hmaps hmem
  have h3 := MPolyfold.tangentMapOn_congr hbmono Tb.isScSmoothOn_sigma hW'o subset_rfl hW'b
    (eqOn_refl _ _) hmem
  change MPolyfold.tangentMapOn Tab.isScSmoothOn_sigma h =
    MPolyfold.tangentMapOn Ta.isScSmoothOn_sigma (MPolyfold.tangentMapOn Tb.isScSmoothOn_sigma h)
  rw [h1, h2, Function.comp_apply, h3]

/-- `transMap` respects equality of elements (with possibly different proofs of the side
conditions). -/
theorem transMap_congr {Ψ Ψ' : S.Unif} {a b : S.Tr Ψ Ψ'} (h : a = b) :
    S.transMap a = S.transMap b := by subst h; rfl

/-- `transMap_comp` for any element `c` with the entries of `a ∘ b`. -/
theorem transMap_comp' {Ψ Ψ' Ψ'' : S.Unif} (a : S.Tr Ψ' Ψ'') (b : S.Tr Ψ Ψ') (c : S.Tr Ψ Ψ'')
    (hc₁ : c.src = b.src) (hc₂ : c.mor = C.toGroupoidStr.comp a.mor b.mor) (hc₃ : c.tgt = a.tgt)
    (hs : a.src = b.tgt) {h : Ψ.1.P.TangentSpace}
    (hh : Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj h) = b.src) :
    S.transMap c h = S.transMap a (S.transMap b h) :=
  (congrFun (transMap_congr (GroupoidStr.TransitionSet.ext hc₁ hc₂ hc₃ :
    c = S.toTr (GroupoidStr.TransitionSet.comp a b
      (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt hs)))) h).trans
    (transMap_comp a b _ hs hh)

/-- `Tσ_{a⁻¹} ∘ Tσ_a = id` over `s(a)` (2021 p. 768, the symmetry in Lemma 17.2.1). -/
theorem transMap_inv_transMap {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ') {h : Ψ.1.P.TangentSpace}
    (hh : Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj h) = a.src) :
    S.transMap (S.toTr (GroupoidStr.TransitionSet.inv a) : S.Tr Ψ' Ψ) (S.transMap a h) = h := by
  rw [← transMap_comp (S.toTr (GroupoidStr.TransitionSet.inv a)) a
    (C.toGroupoidStr.src_inv a.mor) rfl hh,
    transMap_congr (GroupoidStr.TransitionSet.inv_comp a)]
  exact transMap_unit a.src hh

theorem transMap_transMap_inv {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ') {h : Ψ'.1.P.TangentSpace}
    (hh : Ψ'.1.P.levelVal 1 (Ψ'.1.P.tangentProj h) = a.tgt) :
    S.transMap a (S.transMap (S.toTr (GroupoidStr.TransitionSet.inv a) : S.Tr Ψ' Ψ) h) = h := by
  have := transMap_inv_transMap (S := S) (S.toTr (GroupoidStr.TransitionSet.inv a)) hh
  rwa [transMap_congr (GroupoidStr.TransitionSet.inv_inv a)] at this

/-- `Tσ` maps the fibre over `s(a)` into the fibre over `t(a)`. -/
theorem transMap_mem_fiber {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ') {x : Ψ.1.P.Level 1}
    {y : Ψ'.1.P.Level 1} (hx : Ψ.1.P.levelVal 1 x = a.src) (hy : Ψ'.1.P.levelVal 1 y = a.tgt)
    {h : Ψ.1.P.TangentSpace} (hh : h ∈ Ψ.1.P.tangentFiber x) :
    S.transMap a h ∈ Ψ'.1.P.tangentFiber y := by
  have hb : Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj h) = a.src := by
    rw [MPolyfold.tangentProj_eq_of_mem_fiber hh, hx]
  change Ψ'.1.P.tangentProj (S.transMap a h) = y
  exact MPolyfold.level_ext ((base_transMap a hb).trans hy.symm)

variable (S) in
/-- **`Tσ(q) : T_qO →L[ℝ] T_{q'}O'`** for `a = (q, φ, q') ∈ M(Ψ, Ψ')` with `q` on level `1`:
the tangent of `σ` on the fibre (Theorem 2.3.16 on fibres). -/
def transTangentCLM {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ') {x : Ψ.1.P.Level 1} {y : Ψ'.1.P.Level 1}
    (hx : Ψ.1.P.levelVal 1 x = a.src) (hy : Ψ'.1.P.levelVal 1 y = a.tgt) :
    Ψ.1.P.tangentFiber x →L[ℝ] Ψ'.1.P.tangentFiber y :=
  MPolyfold.tangentMapOnCLM (S.triple a).isScSmoothOn_sigma
    (show Ψ.1.P.levelVal 1 x ∈ (S.triple a).srcSet by rw [hx]; exact (S.triple a).src_mem)
    (by rw [hx, (S.triple a).sigma_src, hy])

theorem transTangentCLM_apply {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ') {x : Ψ.1.P.Level 1}
    {y : Ψ'.1.P.Level 1} (hx : Ψ.1.P.levelVal 1 x = a.src) (hy : Ψ'.1.P.levelVal 1 y = a.tgt)
    (v : Ψ.1.P.tangentFiber x) :
    (S.transTangentCLM a hx hy v : Ψ'.1.P.TangentSpace) = S.transMap a v.1 :=
  MPolyfold.tangentMapOnCLM_apply _ _ _ v

variable (S) in
/-- **`Tσ(q) : T_qO ≃L[ℝ] T_{q'}O'`**, a topological linear isomorphism with inverse the
tangent of `a⁻¹` (2021 p. 769: "`Tσ(q)(h)` is a topological linear isomorphism"). -/
def transTangent {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ') {x : Ψ.1.P.Level 1} {y : Ψ'.1.P.Level 1}
    (hx : Ψ.1.P.levelVal 1 x = a.src) (hy : Ψ'.1.P.levelVal 1 y = a.tgt) :
    Ψ.1.P.tangentFiber x ≃L[ℝ] Ψ'.1.P.tangentFiber y :=
  ContinuousLinearEquiv.equivOfInverse (S.transTangentCLM a hx hy)
    (S.transTangentCLM (S.toTr (GroupoidStr.TransitionSet.inv a) : S.Tr Ψ' Ψ) hy hx)
    (fun v => Subtype.ext ((transTangentCLM_apply _ hy hx _).trans
      ((congrArg _ (transTangentCLM_apply a hx hy v)).trans
        (transMap_inv_transMap a (by erw [MPolyfold.tangentProj_eq_of_mem_fiber v.2, hx])))))
    (fun v => Subtype.ext ((transTangentCLM_apply a hx hy _).trans
      ((congrArg _ (transTangentCLM_apply _ hy hx v)).trans
        (transMap_transMap_inv a (by erw [MPolyfold.tangentProj_eq_of_mem_fiber v.2, hy])))))

theorem transTangent_apply {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ') {x : Ψ.1.P.Level 1}
    {y : Ψ'.1.P.Level 1} (hx : Ψ.1.P.levelVal 1 x = a.src) (hy : Ψ'.1.P.levelVal 1 y = a.tgt)
    (v : Ψ.1.P.tangentFiber x) :
    (S.transTangent a hx hy v : Ψ'.1.P.TangentSpace) = S.transMap a v.1 :=
  transTangentCLM_apply a hx hy v

/-! ### The elements `(q, 1_α, q')` -/

variable (S) in
/-- **The element `(q, 1_α, q') ∈ M(Ψ, Ψ')`** for `Ψ(q) = α = Ψ'(q')` (2021 p. 767). -/
def unitTr {Ψ Ψ' : S.Unif} {α : C.Obj} (q : Ψ.1.O) (q' : Ψ'.1.O) (hq : Ψ.1.obj q = α)
    (hq' : Ψ'.1.obj q' = α) : S.Tr Ψ Ψ' :=
  ⟨q, C.toGroupoidStr.unit α, q', (C.toGroupoidStr.src_unit α).trans hq.symm,
    (C.toGroupoidStr.tgt_unit α).trans hq'.symm⟩

theorem unitTr_self {Ψ : S.Unif} {α : C.Obj} (q : Ψ.1.O) (hq : Ψ.1.obj q = α) :
    S.unitTr q q hq hq = S.toTr (GroupoidStr.TransitionSet.unit q) := by
  subst hq; rfl

theorem unitTr_comp {Ψ Ψ' Ψ'' : S.Unif} {α : C.Obj} (q : Ψ.1.O) (q' : Ψ'.1.O) (q'' : Ψ''.1.O)
    (hq : Ψ.1.obj q = α) (hq' : Ψ'.1.obj q' = α) (hq'' : Ψ''.1.obj q'' = α) :
    S.toTr (GroupoidStr.TransitionSet.comp (S.unitTr q' q'' hq' hq'') (S.unitTr q q' hq hq')
      (by simp [unitTr])) = S.unitTr q q'' hq hq'' :=
  GroupoidStr.TransitionSet.ext rfl (GroupoidStr.comp_unit_of_eq (C.toGroupoidStr.src_unit α)) rfl

theorem unitTr_inv {Ψ Ψ' : S.Unif} {α : C.Obj} (q : Ψ.1.O) (q' : Ψ'.1.O)
    (hq : Ψ.1.obj q = α) (hq' : Ψ'.1.obj q' = α) :
    S.toTr (GroupoidStr.TransitionSet.inv (S.unitTr q q' hq hq')) = S.unitTr q' q hq' hq :=
  GroupoidStr.TransitionSet.ext rfl (C.toGroupoidStr.inv_unit α) rfl

theorem transMap_unitTr_congr {Ψ Ψ' : S.Unif} {α : C.Obj} {q₁ q₂ : Ψ.1.O} {q₁' q₂' : Ψ'.1.O}
    (h : q₁ = q₂) (h' : q₁' = q₂') (hq₁ : Ψ.1.obj q₁ = α) (hq₁' : Ψ'.1.obj q₁' = α)
    (hq₂ : Ψ.1.obj q₂ = α) (hq₂' : Ψ'.1.obj q₂' = α) :
    S.transMap (S.unitTr q₁ q₁' hq₁ hq₁') = S.transMap (S.unitTr q₂ q₂' hq₂ hq₂') := by
  subst h; subst h'; rfl

/-- `Tσ` for `(q', 1, q'') ∘ (q, 1, q') = (q, 1, q'')`. -/
theorem transMap_unitTr_comp {Ψ Ψ' Ψ'' : S.Unif} {α : C.Obj} (q : Ψ.1.O) (q' : Ψ'.1.O)
    (q'' : Ψ''.1.O) (hq : Ψ.1.obj q = α) (hq' : Ψ'.1.obj q' = α) (hq'' : Ψ''.1.obj q'' = α)
    {h : Ψ.1.P.TangentSpace} (hh : Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj h) = q) :
    S.transMap (S.unitTr q' q'' hq' hq'') (S.transMap (S.unitTr q q' hq hq') h) =
      S.transMap (S.unitTr q q'' hq hq'') h := by
  rw [← transMap_comp _ _ (by simp [unitTr]) rfl hh,
    transMap_congr (unitTr_comp q q' q'' hq hq' hq'')]

theorem transMap_unitTr_self {Ψ : S.Unif} {α : C.Obj} (q : Ψ.1.O) (hq : Ψ.1.obj q = α)
    {h : Ψ.1.P.TangentSpace} (hh : Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj h) = q) :
    S.transMap (S.unitTr q q hq hq) h = h := by
  rw [transMap_congr (unitTr_self q hq)]; exact transMap_unit q hh

/-! ### Lemma 17.2.1 and Definitions 17.2.2, 17.2.3 -/

variable (S) in
/-- **The tuples `(α, Ψ, h)`** of 2021 p. 767: `Ψ ∈ F(α)` and `h ∈ T_qO` with `Ψ(q) = α`. -/
structure TangentTuple (α : C.Obj) where
  /-- The uniformizer `Ψ`. -/
  unif : S.Unif
  mem : unif.1 ∈ S.F α
  /-- The vector `h ∈ TO`. -/
  vec : unif.1.P.TangentSpace
  /-- `h` lies over the point `q` with `Ψ(q) = α`. -/
  obj_eq : unif.1.obj (unif.1.P.levelVal 1 (unif.1.P.tangentProj vec)) = α

namespace TangentTuple

variable {α : C.Obj}

/-- The point `q = τ(h)` with `Ψ(q) = α`. -/
abbrev base (t : S.TangentTuple α) : t.unif.1.O :=
  t.unif.1.P.levelVal 1 (t.unif.1.P.tangentProj t.vec)

/-- `(q, 1_α, q') ∈ M(Ψ, Ψ')` for two tuples. -/
abbrev tr (t t' : S.TangentTuple α) : S.Tr t.unif t'.unif :=
  S.unitTr t.base t'.base t.obj_eq t'.obj_eq

end TangentTuple

variable (S) in
/-- **The relation `(α, Ψ, h) ∼ (α, Ψ', h')`** iff `Tσ(h) = h'`, `σ` the sc-diffeomorphism of
`(q, 1_α, q') ∈ M(Ψ, Ψ')` (2021 p. 768). -/
def TangentRel (α : C.Obj) (t t' : S.TangentTuple α) : Prop := S.transMap (t.tr t') t.vec = t'.vec

/-- **Lemma 17.2.1** (2021 p. 768): `∼` is an equivalence relation. -/
theorem lemma_17_2_1 (α : C.Obj) : Equivalence (S.TangentRel α) where
  refl t := transMap_unitTr_self t.base t.obj_eq rfl
  symm {t t'} h := by
    change S.transMap (t'.tr t) t'.vec = t.vec
    rw [← h, ← transMap_congr (unitTr_inv t.base t'.base t.obj_eq t'.obj_eq)]
    exact transMap_inv_transMap _ rfl
  trans {t t' t''} h h' := by
    change S.transMap (t.tr t'') t.vec = t''.vec
    have hb : t'.base = t'.unif.1.P.levelVal 1 (t'.unif.1.P.tangentProj
        (S.transMap (t.tr t') t.vec)) := by rw [h]
    rw [← h', ← h, ← transMap_unitTr_comp t.base t'.base t''.base t.obj_eq t'.obj_eq t''.obj_eq rfl]

variable (S) in
/-- The setoid of Lemma 17.2.1. -/
def tangentSetoid (α : C.Obj) : Setoid (S.TangentTuple α) := ⟨S.TangentRel α, lemma_17_2_1 α⟩

variable (S) in
/-- **Definition 17.2.3** (2021 p. 769): **the tangent space `T_αC`**, the set of classes
`[α, Ψ, h]`. -/
def TangentSpaceAt (α : C.Obj) : Type (u + 1) := Quotient (S.tangentSetoid α)

variable (S) in
/-- **Definition 17.2.2** (2021 p. 768): **the tangent vector `[α, Ψ, h]`**. -/
def tangentVector {α : C.Obj} (t : S.TangentTuple α) : S.TangentSpaceAt α :=
  Quotient.mk (S.tangentSetoid α) t

theorem tangentVector_eq_iff {α : C.Obj} {t t' : S.TangentTuple α} :
    S.tangentVector t = S.tangentVector t' ↔ S.TangentRel α t t' := Quotient.eq

theorem tangentVector_surjective (α : C.Obj) : Surjective (S.tangentVector (α := α)) :=
  Quotient.mk_surjective

/-! ### Proposition 17.2.4: the charts `S_Ψ` -/

/-- The point `q` with `Ψ(q) = α`, for `Ψ ∈ F(α)`. -/
def pointOf {α : C.Obj} {Ψ : S.Unif} (hΨ : Ψ.1 ∈ S.F α) : Ψ.1.O :=
  (S.isAt α Ψ.1 hΨ).choose

theorem obj_pointOf {α : C.Obj} {Ψ : S.Unif} (hΨ : Ψ.1 ∈ S.F α) : Ψ.1.obj (pointOf hΨ) = α :=
  (S.isAt α Ψ.1 hΨ).choose_spec

/-- The point `q` is unique (`Ψ` is injective on objects). -/
theorem eq_pointOf {α : C.Obj} {Ψ : S.Unif} (hΨ : Ψ.1 ∈ S.F α) {q : Ψ.1.O}
    (hq : Ψ.1.obj q = α) : q = pointOf hΨ :=
  Ψ.1.injective_obj (hq.trans (obj_pointOf hΨ).symm)

theorem pointOf_mem {α : C.Obj} {Ψ : S.Unif} (hΨ : Ψ.1 ∈ S.F α) (hα : S.HasRegularity 1 α) :
    pointOf hΨ ∈ Ψ.1.P.levelSet 1 :=
  (regularity_eq_of_mem hΨ (obj_pointOf hΨ) 1).1 hα

variable (S) in
/-- **`α` carries tangent vectors**: `α ∈ C¹` and `F(α) ≠ ∅`. -/
def TangentObj (α : C.Obj) : Prop := S.HasRegularity 1 α ∧ (S.F α).Nonempty

/-- `T_αC = ∅` unless `α ∈ C¹` and `F(α) ≠ ∅`. -/
theorem tangentObj_of_tangentSpaceAt {α : C.Obj} (e : S.TangentSpaceAt α) : S.TangentObj α := by
  obtain ⟨t, -⟩ := tangentVector_surjective α e
  exact ⟨(regularity_eq_of_mem t.mem t.obj_eq 1).2 (MPolyfold.levelVal_mem _), ⟨_, t.mem⟩⟩

variable (S) in
/-- **The chart `S_Ψ : T_αC → T_qO`**, `[α, Ψ', h'] ↦ Tσ(h')` for `σ` of `(q', 1_α, q)` (2021
p. 769; on the classes `[α, Ψ, h]` it is `h ↦ h`, `tangentChart_mk_self`), for every
`Ψ ∈ F(α)` and the level-`1` point `x` with `Ψ(x) = α`. -/
def tangentChart {α : C.Obj} (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) : S.TangentSpaceAt α ≃ Ψ.1.P.tangentFiber x where
  toFun := Quotient.lift (fun t : S.TangentTuple α =>
      (⟨S.transMap (S.unitTr t.base (Ψ.1.P.levelVal 1 x) t.obj_eq hx) t.vec,
        transMap_mem_fiber _ rfl rfl rfl⟩ : Ψ.1.P.tangentFiber x))
    fun t t' (h : S.transMap (t.tr t') t.vec = t'.vec) => Subtype.ext (by
      change _ = S.transMap _ t'.vec
      rw [← h, transMap_unitTr_comp _ _ _ _ _ _ rfl])
  invFun v := S.tangentVector ⟨Ψ, hΨ, v.1, (levelVal_tangentProj_of_mem v.2).symm ▸ hx⟩
  left_inv := by
    refine Quotient.ind fun t => ?_
    refine Quotient.sound ((lemma_17_2_1 α).symm ?_)
    change S.transMap (S.unitTr _ _ _ _) _ = S.transMap (S.unitTr _ _ _ _) _
    exact congrFun (transMap_unitTr_congr rfl
      (base_transMap (S.unitTr t.base (Ψ.1.P.levelVal 1 x) t.obj_eq hx) rfl) _ _ _ _) _
  right_inv v := Subtype.ext ((congrFun (transMap_unitTr_congr
    (levelVal_tangentProj_of_mem v.2) rfl _ _ hx hx) v.1).trans
    (transMap_unitTr_self (S := S) (Ψ := Ψ) _ hx (levelVal_tangentProj_of_mem v.2)))

theorem tangentChart_mk {α : C.Obj} (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) (t : S.TangentTuple α) :
    (S.tangentChart Ψ hΨ x hx (S.tangentVector t) : Ψ.1.P.TangentSpace) =
      S.transMap (S.unitTr t.base (Ψ.1.P.levelVal 1 x) t.obj_eq hx) t.vec := rfl

theorem tangentChart_symm_apply {α : C.Obj} (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) (v : Ψ.1.P.tangentFiber x) :
    (S.tangentChart Ψ hΨ x hx).symm v =
      S.tangentVector ⟨Ψ, hΨ, v.1, (levelVal_tangentProj_of_mem v.2).symm ▸ hx⟩ :=
  rfl

/-- **`S_Ψ[α, Ψ, h] = h`** (2021 p. 769). -/
theorem tangentChart_mk_self {α : C.Obj} (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) (v : Ψ.1.P.tangentFiber x) :
    S.tangentChart Ψ hΨ x hx (S.tangentVector ⟨Ψ, hΨ, v.1,
      (levelVal_tangentProj_of_mem v.2).symm ▸ hx⟩) = v :=
  (S.tangentChart Ψ hΨ x hx).apply_symm_apply v

/-- **The change of charts `S_{Ψ'} ∘ S_Ψ⁻¹ = Tσ(q)`** (2021 p. 769), `σ` of `(q, 1_α, q')`. -/
theorem tangentChart_symm_trans {α : C.Obj} (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F α)
    (x' : Ψ'.1.P.Level 1) (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α) (v : Ψ.1.P.tangentFiber x) :
    S.tangentChart Ψ' hΨ' x' hx' ((S.tangentChart Ψ hΨ x hx).symm v) =
      S.transTangent (S.unitTr (Ψ.1.P.levelVal 1 x) (Ψ'.1.P.levelVal 1 x') hx hx') rfl rfl v := by
  exact Subtype.ext ((congrFun (transMap_unitTr_congr
    (levelVal_tangentProj_of_mem v.2) rfl _ _ hx hx') v.1).trans (transTangent_apply _ _ _ v).symm)

/-! ### The Banach structure of `T_αC` -/

variable (S) in
/-- A reference uniformizer `Ψ_α ∈ F(α)`. -/
def refUnif {α : C.Obj} (hα : S.TangentObj α) : S.Unif :=
  ⟨Set.Nonempty.some hα.2, α, Set.Nonempty.some_mem hα.2⟩

theorem refUnif_mem {α : C.Obj} (hα : S.TangentObj α) : (S.refUnif hα).1 ∈ S.F α :=
  Set.Nonempty.some_mem hα.2

variable (S) in
/-- The level-`1` point `q_α` of `Ψ_α` with `Ψ_α(q_α) = α`. -/
def refPoint {α : C.Obj} (hα : S.TangentObj α) : (S.refUnif hα).1.P.Level 1 :=
  (S.refUnif hα).1.P.levelMk 1 (pointOf (refUnif_mem hα)) (pointOf_mem (refUnif_mem hα) hα.1)

theorem obj_refPoint {α : C.Obj} (hα : S.TangentObj α) :
    (S.refUnif hα).1.obj ((S.refUnif hα).1.P.levelVal 1 (S.refPoint hα)) = α :=
  obj_pointOf (refUnif_mem hα)

variable (S) in
/-- The reference chart `S_{Ψ_α} : T_αC ≃ T_{q_α}O_α`. -/
def refChart {α : C.Obj} (hα : S.TangentObj α) :
    S.TangentSpaceAt α ≃ (S.refUnif hα).1.P.tangentFiber (S.refPoint hα) :=
  S.tangentChart (S.refUnif hα) (refUnif_mem hα) (S.refPoint hα) (obj_refPoint hα)

section Banach

variable (α : C.Obj) [hα : Fact (S.TangentObj α)]

/-- **The vector space structure of `T_αC`** (2021 p. 769), through `S_{Ψ_α}`; by
`definition_17_2_3` it is the text's `[α, Ψ, h] + λ[α, Ψ, k] = [α, Ψ, h + λk]` for every `Ψ`. -/
instance : AddCommGroup (S.TangentSpaceAt α) := (S.refChart hα.out).addCommGroup

instance : Module ℝ (S.TangentSpaceAt α) := (S.refChart hα.out).module ℝ

/-- The topology of `T_αC`, through `S_{Ψ_α}` (by `proposition_17_2_4` the one of every `S_Ψ`). -/
instance : TopologicalSpace (S.TangentSpaceAt α) :=
  TopologicalSpace.induced (S.refChart hα.out) inferInstance

variable (S) in
/-- `S_{Ψ_α}` as a topological linear isomorphism. -/
def refChartCLE :
    S.TangentSpaceAt α ≃L[ℝ] (S.refUnif hα.out).1.P.tangentFiber (S.refPoint hα.out) :=
  { (S.refChart hα.out).linearEquiv ℝ with
    continuous_toFun := continuous_induced_dom
    continuous_invFun := continuous_induced_rng.2 (by
      change Continuous ((S.refChart hα.out) ∘ (S.refChart hα.out).symm)
      rw [Equiv.self_comp_symm]; exact continuous_id) }

theorem coe_refChartCLE : ⇑(S.refChartCLE α) = S.refChart hα.out := rfl

variable (S) in
/-- **`S_Ψ : T_αC ≃L[ℝ] T_qO`** for every `Ψ ∈ F(α)` (Proposition 17.2.4): `S_{Ψ_α}` followed by
`Tσ(q_α)` of `(q_α, 1_α, q)`. -/
def tangentChartCLE (Ψ : S.Unif) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) : S.TangentSpaceAt α ≃L[ℝ] Ψ.1.P.tangentFiber x :=
  (S.refChartCLE α).trans (S.transTangent (S.unitTr _ _ (obj_refPoint hα.out) hx) rfl rfl)

theorem coe_tangentChartCLE (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) :
    ⇑(S.tangentChartCLE α Ψ x hx) = S.tangentChart Ψ hΨ x hx := by
  funext e
  have h := tangentChart_symm_trans (S := S) _ (refUnif_mem hα.out) (S.refPoint hα.out)
    (obj_refPoint hα.out) Ψ hΨ x hx (S.refChart hα.out e)
  have he : (S.refChart hα.out).symm (S.refChart hα.out e) = e := Equiv.symm_apply_apply _ _
  exact h.symm.trans (congrArg _ he)

/-- **Proposition 17.2.4** (2021 p. 769): for every `Ψ ∈ F(α)` and `Ψ(q) = α`, `S_Ψ` is a
topological linear isomorphism `T_αC ≃L[ℝ] T_qO`, and `S_{Ψ'} ∘ S_Ψ⁻¹ = Tσ(q)` for `σ` of
`(q, 1_α, q')`; so the structure does not depend on `Ψ`. -/
theorem proposition_17_2_4 (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) :
    (∃ E : S.TangentSpaceAt α ≃L[ℝ] Ψ.1.P.tangentFiber x, ⇑E = S.tangentChart Ψ hΨ x hx) ∧
      ∀ (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F α) (x' : Ψ'.1.P.Level 1)
        (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α) (v : Ψ.1.P.tangentFiber x),
        S.tangentChart Ψ' hΨ' x' hx' ((S.tangentChart Ψ hΨ x hx).symm v) =
          S.transTangent (S.unitTr _ _ hx hx') rfl rfl v :=
  ⟨⟨S.tangentChartCLE α Ψ x hx, coe_tangentChartCLE α Ψ hΨ x hx⟩,
    fun Ψ' hΨ' x' hx' v => tangentChart_symm_trans Ψ hΨ x hx Ψ' hΨ' x' hx' v⟩

/-- **The vector space structure of Definition 17.2.3** (2021 p. 769):
`[α, Ψ, h] + λ[α, Ψ, k] = [α, Ψ, h + λk]`, for every `Ψ ∈ F(α)`. -/
theorem definition_17_2_3 (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) (l : ℝ) (h k : Ψ.1.P.tangentFiber x) :
    (S.tangentChart Ψ hΨ x hx).symm h + l • (S.tangentChart Ψ hΨ x hx).symm k =
      (S.tangentChart Ψ hΨ x hx).symm (h + l • k) := by
  have hc : ∀ v, (S.tangentChart Ψ hΨ x hx).symm v = (S.tangentChartCLE α Ψ x hx).symm v :=
    fun v => (S.tangentChart Ψ hΨ x hx).symm_apply_eq.2 (by
      rw [← coe_tangentChartCLE α Ψ hΨ x hx]
      exact ((S.tangentChartCLE α Ψ x hx).apply_symm_apply v).symm)
  rw [hc, hc, hc, map_add, map_smul]

variable (S) in
/-- **The Banach norm of `T_αC` through `S_Ψ` and a chart `φ` of `O` around `q`** (2021 p. 769,
"a Banachable space"; Remark 1.1.2).  Not an instance: it depends on `(Ψ, φ)` up to
equivalence. -/
abbrev tangentNormedAddCommGroup (Ψ : S.Unif) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) {φ : MChart Ψ.1.O} (hφ : Ψ.1.P.IsChart φ)
    (hxφ : Ψ.1.P.levelVal 1 x ∈ φ.source) : NormedAddCommGroup (S.TangentSpaceAt α) :=
  NormedAddCommGroup.induced (S.TangentSpaceAt α) _
    ((S.tangentChartCLE α Ψ x hx).trans
      (MPolyfold.tangentFiberContinuousLinearEquiv hφ hxφ)).toLinearEquiv.toLinearMap
    (LinearEquiv.injective _)

/-- **Proposition 17.2.4, "Banachable"** (2021 p. 769): the norm through any `Ψ ∈ F(α)` and any
chart induces the topology of `T_αC`, and it is complete. -/
theorem proposition_17_2_4_banachable (Ψ : S.Unif) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) {φ : MChart Ψ.1.O} (hφ : Ψ.1.P.IsChart φ)
    (hxφ : Ψ.1.P.levelVal 1 x ∈ φ.source) :
    @UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
        (S.tangentNormedAddCommGroup α Ψ x hx hφ hxφ).toPseudoMetricSpace) =
      (inferInstance : TopologicalSpace (S.TangentSpaceAt α)) ∧
    @CompleteSpace (S.TangentSpaceAt α) (@PseudoMetricSpace.toUniformSpace _
        (S.tangentNormedAddCommGroup α Ψ x hx hφ hxφ).toPseudoMetricSpace) := by
  set L := (S.tangentChartCLE α Ψ x hx).trans (MPolyfold.tangentFiberContinuousLinearEquiv hφ hxφ)
  refine ⟨(UniformSpace.toTopologicalSpace_comap).trans L.toHomeomorph.isInducing.eq_induced.symm,
    ?_⟩
  let _ := S.tangentNormedAddCommGroup α Ψ x hx hφ hxφ
  exact (IsometryEquiv.completeSpace_iff
    ⟨L.toLinearEquiv.toEquiv, Isometry.of_dist_eq fun _ _ => rfl⟩).2 inferInstance

omit hα in
/-- **Proposition 17.2.4, smooth objects** (2021 p. 769): for a smooth `α`, every chart
`T_αC → T_qO → T_{φ(q)}O_φ ⊆ E` (through any `Ψ ∈ F(α)` and any chart `φ` of `O`) has an
sc-subspace of `E` as image, and the change between two such charts is the restriction of an
sc-operator.  This is the sc-Banachable structure of `T_αC`, independent of the charts. -/
theorem proposition_17_2_4_sc (hs : S.IsSmoothObj α) (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α)
    (x : Ψ.1.P.Level 1) (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) {φ : MChart Ψ.1.O}
    (hφ : Ψ.1.P.IsChart φ) (hxφ : Ψ.1.P.levelVal 1 x ∈ φ.source) :
    φ.model.E.IsScSubspace (MPolyfold.tangentFiberModel hφ hxφ) ∧
      ∀ (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F α) (x' : Ψ'.1.P.Level 1)
        (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α) {φ' : MChart Ψ'.1.O}
        (hφ' : Ψ'.1.P.IsChart φ') (hxφ' : Ψ'.1.P.levelVal 1 x' ∈ φ'.source),
        ∃ L : φ.model.E 0 →L[ℝ] φ'.model.E 0, IsScOperator L ∧
          ∀ e : S.TangentSpaceAt α,
            (MPolyfold.tangentFiberEquiv hφ' hxφ' (S.tangentChart Ψ' hΨ' x' hx' e) :
              φ'.model.E 0) =
              L (MPolyfold.tangentFiberEquiv hφ hxφ (S.tangentChart Ψ hΨ x hx e)) := by
  have hsm : ∀ (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
      (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α), Ψ.1.P.levelVal 1 x ∈ Ψ.1.P.smoothSet :=
    fun Ψ hΨ x hx => mem_iInter.2 fun m => (regularity_eq_of_mem hΨ hx m).1 (hs m)
  refine ⟨MPolyfold.isScSubspace_tangentFiberModel hφ hxφ (hsm Ψ hΨ x hx),
    fun Ψ' hΨ' x' hx' φ' hφ' hxφ' => ?_⟩
  set a := S.unitTr (Ψ.1.P.levelVal 1 x) (Ψ'.1.P.levelVal 1 x') hx hx'
  have hxU : Ψ.1.P.levelVal 1 x ∈ (S.triple a).srcSet := (S.triple a).src_mem
  have hxy : (S.triple a).sigma (Ψ.1.P.levelVal 1 x) = Ψ'.1.P.levelVal 1 x' :=
    (S.triple a).sigma_src
  obtain ⟨L, hL, hLs⟩ := MPolyfold.exists_clm_tangentMapOnFiber (S.triple a).isScSmoothOn_sigma
    hxU hxy hφ hφ' hxφ hxφ'
  refine ⟨L, hLs (hsm Ψ hΨ x hx), fun e => ?_⟩
  have h := tangentChart_symm_trans Ψ hΨ x hx Ψ' hΨ' x' hx' (S.tangentChart Ψ hΨ x hx e)
  rw [Equiv.symm_apply_apply] at h
  rw [h, ← hL]
  exact congrArg (fun w => (MPolyfold.tangentFiberEquiv hφ' hxφ' w : φ'.model.E 0))
    (MPolyfold.tangentMapOnCLM_eq _ _ _ _)

end Banach

/-! ### Proposition 17.2.5: the functor `μ_C : C¹ → Ban` -/

variable (S) in
/-- **The element `(q, φ, q') ∈ M(Ψ, Ψ')`** for `φ : α → α'`, `Ψ(q) = α`, `Ψ'(q') = α'`. -/
def morTr {Ψ Ψ' : S.Unif} {α α' : C.Obj} (q : Ψ.1.O) (φ : C.Mor) (q' : Ψ'.1.O)
    (hq : Ψ.1.obj q = α) (hs : C.toGroupoidStr.src φ = α) (hq' : Ψ'.1.obj q' = α')
    (ht : C.toGroupoidStr.tgt φ = α') : S.Tr Ψ Ψ' :=
  ⟨q, φ, q', hs.trans hq.symm, ht.trans hq'.symm⟩

theorem transMap_morTr_congr {Ψ Ψ' : S.Unif} {α α' : C.Obj} {φ : C.Mor} {q₁ q₂ : Ψ.1.O}
    {q₁' q₂' : Ψ'.1.O} (h : q₁ = q₂) (h' : q₁' = q₂') (hq₁ : Ψ.1.obj q₁ = α)
    (hs : C.toGroupoidStr.src φ = α) (hq₁' : Ψ'.1.obj q₁' = α') (ht : C.toGroupoidStr.tgt φ = α')
    (hq₂ : Ψ.1.obj q₂ = α) (hq₂' : Ψ'.1.obj q₂' = α') :
    S.transMap (S.morTr q₁ φ q₁' hq₁ hs hq₁' ht) =
      S.transMap (S.morTr q₂ φ q₂' hq₂ hs hq₂' ht) := by
  subst h; subst h'; rfl

theorem tangentVector_mk_congr {α : C.Obj} {Ψ : S.Unif} {hΨ : Ψ.1 ∈ S.F α}
    {v w : Ψ.1.P.TangentSpace} (h : v = w)
    (hv : Ψ.1.obj (Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj v)) = α)
    (hw : Ψ.1.obj (Ψ.1.P.levelVal 1 (Ψ.1.P.tangentProj w)) = α) :
    S.tangentVector ⟨Ψ, hΨ, v, hv⟩ = S.tangentVector ⟨Ψ, hΨ, w, hw⟩ := by
  subst h; rfl

variable (S) in
/-- **`Tφ : T_αC → T_{α'}C`, `Tφ[α, Ψ, h] = [α', Ψ', Tσ(h)]`** (2021 (17.31), p. 770), `σ` of
`(q, φ, q') ∈ M(Ψ, Ψ')`, for a chosen `Ψ' ∈ F(α')` and `Ψ'(q') = α'` (independent of the choice:
`tangentMorAt_indep`). -/
def tangentMorAt {α α' : C.Obj} (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F α') (x' : Ψ'.1.P.Level 1)
    (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α') : S.TangentSpaceAt α → S.TangentSpaceAt α' :=
  Quotient.lift (fun t : S.TangentTuple α => S.tangentVector ⟨Ψ', hΨ',
      S.transMap (S.morTr t.base φ (Ψ'.1.P.levelVal 1 x') t.obj_eq hs hx' ht) t.vec,
      (congrArg Ψ'.1.obj (base_transMap _ rfl)).trans hx'⟩)
    fun t t' (h : S.transMap (t.tr t') t.vec = t'.vec) => tangentVector_mk_congr
      ((transMap_comp' (S.morTr t'.base φ (Ψ'.1.P.levelVal 1 x') t'.obj_eq hs hx' ht) (t.tr t')
        _ rfl (GroupoidStr.comp_unit_of_eq hs).symm rfl rfl rfl).trans (congrArg _ h)) _ _

/-- **(17.31)**: `Tφ[α, Ψ, h] = [α', Ψ', Tσ(h)]`. -/
theorem tangentMorAt_mk {α α' : C.Obj} (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F α') (x' : Ψ'.1.P.Level 1)
    (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α') (t : S.TangentTuple α) :
    S.tangentMorAt φ hs ht Ψ' hΨ' x' hx' (S.tangentVector t) = S.tangentVector ⟨Ψ', hΨ',
      S.transMap (S.morTr t.base φ (Ψ'.1.P.levelVal 1 x') t.obj_eq hs hx' ht) t.vec,
      (congrArg Ψ'.1.obj (base_transMap _ rfl)).trans hx'⟩ := rfl

/-- `Tφ` does not depend on the choice of `Ψ' ∈ F(α')` (2021 p. 770, implicit). -/
theorem tangentMorAt_indep {α α' : C.Obj} (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (Ψ₁ : S.Unif) (hΨ₁ : Ψ₁.1 ∈ S.F α') (x₁ : Ψ₁.1.P.Level 1)
    (hx₁ : Ψ₁.1.obj (Ψ₁.1.P.levelVal 1 x₁) = α') (Ψ₂ : S.Unif) (hΨ₂ : Ψ₂.1 ∈ S.F α')
    (x₂ : Ψ₂.1.P.Level 1) (hx₂ : Ψ₂.1.obj (Ψ₂.1.P.levelVal 1 x₂) = α') :
    S.tangentMorAt φ hs ht Ψ₁ hΨ₁ x₁ hx₁ = S.tangentMorAt φ hs ht Ψ₂ hΨ₂ x₂ hx₂ := by
  funext e
  obtain ⟨t, rfl⟩ := tangentVector_surjective α e
  refine Quotient.sound ?_
  change S.transMap (S.unitTr _ _ _ _) (S.transMap _ t.vec) = S.transMap _ t.vec
  exact (congrFun (transMap_unitTr_congr (base_transMap _ rfl) (base_transMap _ rfl) _ _ hx₁ hx₂)
    _).trans (transMap_comp' (S.unitTr (Ψ₁.1.P.levelVal 1 x₁) (Ψ₂.1.P.levelVal 1 x₂) hx₁ hx₂)
    (S.morTr t.base φ (Ψ₁.1.P.levelVal 1 x₁) t.obj_eq hs hx₁ ht)
    (S.morTr t.base φ (Ψ₂.1.P.levelVal 1 x₂) t.obj_eq hs hx₂ ht) rfl
    (GroupoidStr.unit_comp_of_eq ht).symm rfl rfl rfl).symm

/-- **`T(1_α) = id`** (Proposition 17.2.5). -/
theorem tangentMorAt_unit {α : C.Obj} (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F α) (x' : Ψ'.1.P.Level 1)
    (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α) :
    S.tangentMorAt (C.toGroupoidStr.unit α) (C.toGroupoidStr.src_unit α)
      (C.toGroupoidStr.tgt_unit α) Ψ' hΨ' x' hx' = id := by
  funext e
  obtain ⟨t, rfl⟩ := tangentVector_surjective α e
  refine Quotient.sound ((lemma_17_2_1 α).symm ?_)
  change S.transMap (S.unitTr _ _ _ _) t.vec = S.transMap _ t.vec
  exact congrFun (transMap_unitTr_congr (S := S) (Ψ := t.unif) (Ψ' := Ψ') rfl
    (base_transMap (S.morTr t.base (C.toGroupoidStr.unit α) (Ψ'.1.P.levelVal 1 x') t.obj_eq
      (C.toGroupoidStr.src_unit α) hx' (C.toGroupoidStr.tgt_unit α)) rfl) t.obj_eq _ t.obj_eq hx')
    t.vec

/-- **`Tψ ∘ Tφ = T(ψ ∘ φ)`** (2021 p. 770, Proposition 17.2.5). -/
theorem tangentMorAt_comp {α α' α'' : C.Obj} (φ ψ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (hs' : C.toGroupoidStr.src ψ = α')
    (ht' : C.toGroupoidStr.tgt ψ = α'') (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F α')
    (x' : Ψ'.1.P.Level 1) (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α') (Ψ'' : S.Unif)
    (hΨ'' : Ψ''.1 ∈ S.F α'') (x'' : Ψ''.1.P.Level 1)
    (hx'' : Ψ''.1.obj (Ψ''.1.P.levelVal 1 x'') = α'') :
    S.tangentMorAt (C.toGroupoidStr.comp ψ φ)
        ((C.toGroupoidStr.src_comp ψ φ (hs'.trans ht.symm)).trans hs)
        ((C.toGroupoidStr.tgt_comp ψ φ (hs'.trans ht.symm)).trans ht') Ψ'' hΨ'' x'' hx'' =
      S.tangentMorAt ψ hs' ht' Ψ'' hΨ'' x'' hx'' ∘ S.tangentMorAt φ hs ht Ψ' hΨ' x' hx' := by
  funext e
  obtain ⟨t, rfl⟩ := tangentVector_surjective α e
  refine tangentVector_mk_congr ?_ _ _
  change _ = S.transMap _ (S.transMap _ t.vec)
  exact (transMap_comp' (S.morTr (Ψ'.1.P.levelVal 1 x') ψ (Ψ''.1.P.levelVal 1 x'') hx' hs' hx'' ht')
    (S.morTr t.base φ (Ψ'.1.P.levelVal 1 x') t.obj_eq hs hx' ht) _ rfl rfl rfl rfl rfl).trans
    (congrFun (transMap_morTr_congr
      (base_transMap (S.morTr t.base φ (Ψ'.1.P.levelVal 1 x') t.obj_eq hs hx' ht) rfl) rfl
      ((congrArg Ψ'.1.obj (base_transMap _ rfl)).trans hx') hs' hx'' ht' hx' hx'').symm _)

variable (S) in
/-- **`Tφ : T_αC ≃L[ℝ] T_{α'}C`**, a bounded linear isomorphism (Proposition 17.2.5):
`S_{Ψ_{α'}}⁻¹ ∘ Tσ(q_α) ∘ S_{Ψ_α}` for `σ` of `(q_α, φ, q_{α'})`. -/
def tangentMorCLE {α α' : C.Obj} [hα : Fact (S.TangentObj α)] [hα' : Fact (S.TangentObj α')]
    (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α') :
    S.TangentSpaceAt α ≃L[ℝ] S.TangentSpaceAt α' :=
  ((S.refChartCLE α).trans (S.transTangent (S.morTr _ φ _ (obj_refPoint hα.out) hs
    (obj_refPoint hα'.out) ht) rfl rfl)).trans (S.refChartCLE α').symm

theorem coe_tangentMorCLE {α α' : C.Obj} [hα : Fact (S.TangentObj α)]
    [hα' : Fact (S.TangentObj α')] (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') :
    ⇑(S.tangentMorCLE φ hs ht) = S.tangentMorAt φ hs ht (S.refUnif hα'.out)
      (refUnif_mem hα'.out) (S.refPoint hα'.out) (obj_refPoint hα'.out) := by
  funext e
  obtain ⟨t, rfl⟩ := tangentVector_surjective α e
  refine tangentVector_mk_congr ?_ _ _
  refine (transTangent_apply (S.morTr _ φ _ (obj_refPoint hα.out) hs (obj_refPoint hα'.out) ht)
    rfl rfl ((S.refChartCLE α) (S.tangentVector t))).trans ?_
  exact (transMap_comp' (S.morTr _ φ _ (obj_refPoint hα.out) hs (obj_refPoint hα'.out) ht)
    (S.unitTr t.base _ t.obj_eq (obj_refPoint hα.out))
    (S.morTr t.base φ _ t.obj_eq hs (obj_refPoint hα'.out) ht) rfl
    (GroupoidStr.comp_unit_of_eq hs).symm rfl rfl rfl).symm

/-- **Proposition 17.2.5** (2021 p. 770): **`μ_C : C¹ → Ban`** is a functor: every `φ : α → α'`
between objects with tangent spaces has a bounded linear isomorphism `Tφ : T_αC ≃L[ℝ] T_{α'}C`
given by (17.31) for every choice of `Ψ' ∈ F(α')`, with `T(1_α) = id` and
`T(ψ ∘ φ) = Tψ ∘ Tφ`. -/
theorem proposition_17_2_5 :
    (∀ (α α' : C.Obj) [Fact (S.TangentObj α)] [Fact (S.TangentObj α')] (φ : C.Mor)
        (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α') (Ψ' : S.Unif)
        (hΨ' : Ψ'.1 ∈ S.F α') (x' : Ψ'.1.P.Level 1) (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α'),
        ⇑(S.tangentMorCLE φ hs ht) = S.tangentMorAt φ hs ht Ψ' hΨ' x' hx') ∧
      (∀ (α : C.Obj) [Fact (S.TangentObj α)],
        S.tangentMorCLE (C.toGroupoidStr.unit α) (C.toGroupoidStr.src_unit α)
          (C.toGroupoidStr.tgt_unit α) = ContinuousLinearEquiv.refl ℝ _) ∧
      ∀ (α α' α'' : C.Obj) [Fact (S.TangentObj α)] [Fact (S.TangentObj α')]
        [Fact (S.TangentObj α'')] (φ ψ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
        (ht : C.toGroupoidStr.tgt φ = α') (hs' : C.toGroupoidStr.src ψ = α')
        (ht' : C.toGroupoidStr.tgt ψ = α''),
        S.tangentMorCLE (C.toGroupoidStr.comp ψ φ)
            ((C.toGroupoidStr.src_comp ψ φ (hs'.trans ht.symm)).trans hs)
            ((C.toGroupoidStr.tgt_comp ψ φ (hs'.trans ht.symm)).trans ht') =
          (S.tangentMorCLE φ hs ht).trans (S.tangentMorCLE ψ hs' ht') := by
  refine ⟨fun α α' _ _ φ hs ht Ψ' hΨ' x' hx' => (coe_tangentMorCLE φ hs ht).trans
    (tangentMorAt_indep _ _ _ _ _ _ _ _ _ _ _), fun α _ => ?_,
    fun α α' α'' _ _ _ φ ψ hs ht hs' ht' => ?_⟩
  · refine ContinuousLinearEquiv.ext ?_
    rw [coe_tangentMorCLE, tangentMorAt_unit]; rfl
  · refine ContinuousLinearEquiv.ext ?_
    change ⇑(S.tangentMorCLE _ _ _) = ⇑(S.tangentMorCLE ψ hs' ht') ∘ ⇑(S.tangentMorCLE φ hs ht)
    rw [coe_tangentMorCLE, coe_tangentMorCLE, coe_tangentMorCLE,
      tangentMorAt_comp φ ψ hs ht hs' ht']

end GCT.PolyfoldConstruction

end Polyfold
