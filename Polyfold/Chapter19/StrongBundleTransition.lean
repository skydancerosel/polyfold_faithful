import Polyfold.Chapter19.StrongBundleUniformizer
import Polyfold.Chapter10.StrongBundleLocalIso

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.6 "A Strong Bundle Version" (pp. 894–896): the lift `F̄_h` of the transition data (p. 894,
(19.10)), **Definition 19.6.4** (transition requirements for strong bundles), restriction and
equivalence (p. 896), **Definition 19.6.5** (strong bundle transition construction) and
**Definition 19.6.6** (basic strong bundle construction).  Numbers and pages are the 2021 text's.

# Strong bundle transition data

## The text, paraphrased

(p. 894) A representative `F` of the transition construction associates to `h = (o, φ, o')` a
map `F_h(u) = (u, φ_u, f_h(u))` on `V(o)`; the lift is `F̄_h(a) := (a, φ_{p(a)}, a'(a))` with
`Ψ̄'(a'(a)) = φ̂_{p(a)}(Ψ̄(a))`, defined on `K|V(o)`, with `p(F̄_h(a)) = F_h(p(a))`, and
`f̄_h := t ∘ F̄_h : K|V(o) → K'` covers `f_h` ((19.10)).
(Definition 19.6.4) (A) `f̄_h` is a strong bundle isomorphism onto an open image covering
`f_h`, `s(F̄_h(a)) = a`, and for `Ψ̄ = Ψ̄'`, `h = (o, Ψ(g, o), g ∗ o)`:
`F̄_h(a) = (a, Ψ(g, p(a)), g ∗ a)`; (B) stability, (C) identity, (D) inversion,
(E) multiplication, (F) the M-Hausdorff property of the underlying `F_h`.
(p. 896) A restriction replaces `V(o)` by an open `W(o) ⊂ V(o)` and `K|V(o)` by `K|W(o)`;
`F̄`, `F̄'` are equivalent if they have a common identical restriction.
(Definition 19.6.5) A strong bundle transition construction is an equivalence class of bundle
transition data; a representative `F̄` induces a representative `F` of the underlying
construction. (Definition 19.6.6) A basic strong bundle construction for `(S, μ)` is a pair
`(F̄, 𝓕̄)`.

## What is formalized

* `StrongBundleStr.liftMap` (the lift of a map `V(o) → M(Ψ, Ψ')` to `K|V(o) → M(Ψ̄, Ψ̄')`),
  `StrongBundleUniformizerConstruction.mapBar F` (**`F̄_h`**, p. 894), `fmapBar` (**`f̄_h`**),
  `proj_mapBar` (`p(F̄_h(a)) = F_h(p(a))`), `p_fmapBar` (`f̄_h` covers `f_h`), `obj_fmapBar`
  (`Ψ̄'(a'(a)) = φ̂_{p(a)}(Ψ̄(a))`), `mapBar_eq_iff` ((19.10): `F̄_h(a)` is the element of
  `M(Ψ̄, Ψ̄')` with source `a` over `F_h(p(a))`).
* **Definition 19.6.4**: `BundleTransitionData Fb` (the underlying transition data `F` and (A),
  `f̄_h` a strong bundle isomorphism `K|V(o) → K'|f_h(V(o))` covering `f_h`, in the sense of
  Chapter 10's `IsLocalIso₂`).  The remaining requirements hold for the lift of any transition
  data and are theorems: `definition_19_6_4_A_src`, `definition_19_6_4_A_hat`,
  `definition_19_6_4_A_hat_fmap`, `definition_19_6_4_B`, `definition_19_6_4_C`,
  `definition_19_6_4_D`, `definition_19_6_4_E`, `definition_19_6_4_F`.
* `BundleTransitionData.toETD`: the lift `F̄` as transition data of the uniformizer construction
  `toE` of `E_μ`, `h̄ ↦ F̄_{p(h̄)}` on `K|V(s(p(h̄)))` (so §§19.2–19.5 apply to `E_μ`).
* `BundleTransitionData.restrict` (restriction, p. 896), `BundleTransitionData.Equiv` (as
  printed: a common identical restriction of `F` and `F̄`), `equiv_iff` (equivalent iff the
  underlying `F` are), `toETD_equiv`.
* **Definition 19.6.5**: `StrongBundleTransitionConstruction Fb`, `toBaseTC` (the induced
  transition construction of `F`), `toETC`.
* **Definition 19.6.6**: `BasicStrongBundleConstruction μ`, with `base` (the underlying basic
  construction `(F, 𝓕)` of `S`), `toE` (the basic construction of `E_μ`), `rep`, `base_rep`,
  `toE_rep`.

## Readings

* The lift `F̄_h` is determined by `F` (p. 894), so bundle transition data are transition data
  `F` of the underlying uniformizer construction whose lifts satisfy (A).  We prove that the
  lifts satisfy the rest of (A) and (B)–(F) for every `F`.
* "`f̄_h` is a strong bundle isomorphism onto an open image covering `f_h`": we read it as a
  strong bundle isomorphism `K|V(o) → K'|f_h(V(o))` covering the sc-diffeomorphism
  `f_h : V(o) → f_h(V(o))` (Chapter 10's `IsLocalIso₂`); its image `K'|f_h(V(o))` is open.
* `F̄_h` is indexed by `h ∈ M(Ψ, Ψ')` as in the text; the transition data of `E_μ` are indexed by
  `h̄ ∈ M(Ψ̄, Ψ̄')` and use `F̄_{p(h̄)}`.
* "Equivalent provided they have a common identical restriction": for every `h` an open
  `W(o)` inside both domains on which `F_h = F'_h` and `F̄_h = F̄'_h` on `K|W(o)`
  (`BundleTransitionData.Equiv`); the second identity follows from the first (`equiv_iff`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace GroupoidalCategory

variable {C : GroupoidalCategory.{u}}

open GroupoidStr (TransitionSet)

/-! ### The lift of a map `V(o) → M(Ψ, Ψ')` -/

namespace StrongBundleStr

variable {μ : C.BanFunctor} {Ψe Ψe' : μ.cat.Uniformizer} (S : StrongBundleStr μ Ψe)
  (S' : StrongBundleStr μ Ψe')

open scoped Classical in
/-- The lift `a ↦ (a, φ_{p(a)}, Ψ̄'⁻¹(φ̂_{p(a)}(Ψ̄(a))))` of a map `u ↦ (u, φ_u, f(u))` into
`M(Ψ, Ψ')` (its values matter where `s(Fk(p(a))) = p(a)`). -/
def liftMap (Fk : S.O → S.toBase.Trans S'.toBase) (a : Ψe.O) : Ψe.Trans Ψe' :=
  if hq : (Fk (S.p a)).src = S.p a then S.lift S' (Fk (S.p a)) a hq.symm
  else S.lift S' (Fk (S.p a)) (fiberZero S.p (Fk (S.p a)).src)
    (isSection_fiberZero (P := S.p) _)

variable {S S'} {Fk : S.O → S.toBase.Trans S'.toBase} {a : Ψe.O}

theorem liftMap_of (hq : (Fk (S.p a)).src = S.p a) :
    S.liftMap S' Fk a = S.lift S' (Fk (S.p a)) a hq.symm := dif_pos hq

theorem src_liftMap (hq : (Fk (S.p a)).src = S.p a) : (S.liftMap S' Fk a).src = a := by
  rw [liftMap_of hq]; rfl

theorem proj_liftMap : S.proj S' (S.liftMap S' Fk a) = Fk (S.p a) := by
  unfold liftMap; split_ifs <;> exact S.proj_lift S' _ _ _

theorem p_tgt_liftMap : S'.p (S.liftMap S' Fk a).tgt = (Fk (S.p a)).tgt :=
  congrArg TransitionSet.tgt (proj_liftMap (Fk := Fk) (a := a))

theorem liftMap_eq_iff (hq : (Fk (S.p a)).src = S.p a) {h : Ψe.Trans Ψe'} :
    S.liftMap S' Fk a = h ↔ h.src = a ∧ S.proj S' h = Fk (S.p a) := by
  rw [liftMap_of hq, eq_comm]; exact S.eq_lift_iff S' hq.symm

theorem liftMap_congr {Fk' : S.O → S.toBase.Trans S'.toBase} (h : Fk (S.p a) = Fk' (S.p a)) :
    S.liftMap S' Fk a = S.liftMap S' Fk' a := by
  unfold liftMap
  by_cases hq : (Fk (S.p a)).src = S.p a
  · have hq' : (Fk' (S.p a)).src = S.p a := by rwa [← h]
    rw [dif_pos hq, dif_pos hq']
    exact S.lift_congr S' h rfl _ _
  · have hq' : ¬(Fk' (S.p a)).src = S.p a := by rwa [← h]
    rw [dif_neg hq, dif_neg hq']
    exact S.lift_congr S' h (by rw [h]) _ _

/-- `Ψ̄'(a'(a)) = φ̂_{p(a)}(Ψ̄(a))` (p. 894). -/
theorem obj_tgt_liftMap (hq : (Fk (S.p a)).src = S.p a) :
    Ψe'.obj (S.liftMap S' Fk a).tgt = μ.act ⟨((Fk (S.p a)).mor, Ψe.obj a),
      (S.P_obj' a).trans ((congrArg S.toBase.obj hq.symm).trans (Fk (S.p a)).src_mor.symm)⟩ := by
  rw [liftMap_of hq]; exact S.obj_lift_tgt S' _ _ _

end StrongBundleStr

namespace StrongBundleUniformizerConstruction

variable {μ : C.BanFunctor} (Fb : StrongBundleUniformizerConstruction μ)

/-! ### The lift `F̄_h` (p. 894) -/

section Lift

variable (F : Fb.base.TransitionData)

/-- **2021 p. 894: the lift `F̄_h : K|V(o) → M(Ψ̄, Ψ̄')`** of `F_h`, `h ∈ M(Ψ, Ψ')`:
`F̄_h(a) = (a, φ_{p(a)}, a'(a))`, `Ψ̄'(a'(a)) = φ̂_{p(a)}(Ψ̄(a))`. -/
def mapBar (Ψ Ψ' : Fb.Unif) (k : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1) (a : Ψ.1.O) :
    Ψ.1.Trans Ψ'.1 :=
  (Fb.strU Ψ).liftMap (Fb.strU Ψ') (F.map (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') k) a

/-- **2021 p. 895: `f̄_h := t ∘ F̄_h : K|V(o) → K'`.** -/
def fmapBar (Ψ Ψ' : Fb.Unif) (k : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1) (a : Ψ.1.O) :
    Ψ'.1.O :=
  (Fb.mapBar F Ψ Ψ' k a).tgt

variable {Fb F} {Ψ Ψ' Ψ'' : Fb.Unif} {k : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1}
  {a : Ψ.1.O}

theorem src_map_p (hq : (Fb.strU Ψ).p a ∈ F.dom _ _ k) :
    (F.map _ _ k ((Fb.strU Ψ).p a)).src = (Fb.strU Ψ).p a :=
  F.src_map _ _ k _ hq

/-- **`p(F̄_h(a)) = F_h(p(a))`** (p. 894). -/
theorem proj_mapBar :
    (Fb.strU Ψ).proj (Fb.strU Ψ') (Fb.mapBar F Ψ Ψ' k a) = F.map _ _ k ((Fb.strU Ψ).p a) :=
  StrongBundleStr.proj_liftMap

/-- **`f̄_h` covers `f_h`**: `p'(f̄_h(a)) = f_h(p(a))` (p. 895). -/
theorem p_fmapBar : (Fb.strU Ψ').p (Fb.fmapBar F Ψ Ψ' k a) = F.fmap _ _ k ((Fb.strU Ψ).p a) :=
  StrongBundleStr.p_tgt_liftMap

/-- **2021 Definition 19.6.4 (A), p. 895**: `s(F̄_h(a)) = a` for `a ∈ K|V(o)`. -/
theorem definition_19_6_4_A_src (hq : (Fb.strU Ψ).p a ∈ F.dom _ _ k) :
    (Fb.mapBar F Ψ Ψ' k a).src = a :=
  StrongBundleStr.src_liftMap (src_map_p hq)

/-- **(19.10)**: `F̄_h(a)` is the element of `M(Ψ̄, Ψ̄')` with source `a` over `F_h(p(a))`. -/
theorem mapBar_eq_iff (hq : (Fb.strU Ψ).p a ∈ F.dom _ _ k) {h : Ψ.1.Trans Ψ'.1} :
    Fb.mapBar F Ψ Ψ' k a = h ↔
      h.src = a ∧ (Fb.strU Ψ).proj (Fb.strU Ψ') h = F.map _ _ k ((Fb.strU Ψ).p a) :=
  StrongBundleStr.liftMap_eq_iff (src_map_p hq)

/-- `Ψ̄'(f̄_h(a)) = φ̂_{p(a)}(Ψ̄(a))` (p. 894). -/
theorem obj_fmapBar (hq : (Fb.strU Ψ).p a ∈ F.dom _ _ k) :
    Ψ'.1.obj (Fb.fmapBar F Ψ Ψ' k a) = μ.act ⟨((F.map _ _ k ((Fb.strU Ψ).p a)).mor, Ψ.1.obj a),
      ((Fb.strU Ψ).P_obj' a).trans ((congrArg (Fb.strU Ψ).toBase.obj (src_map_p hq).symm).trans
        (F.map _ _ k ((Fb.strU Ψ).p a)).src_mor.symm)⟩ :=
  StrongBundleStr.obj_tgt_liftMap (src_map_p hq)

theorem mapBar_congr {F' : Fb.base.TransitionData}
    (h : F.map _ _ k ((Fb.strU Ψ).p a) = F'.map _ _ k ((Fb.strU Ψ).p a)) :
    Fb.mapBar F Ψ Ψ' k a = Fb.mapBar F' Ψ Ψ' k a :=
  StrongBundleStr.liftMap_congr h

/-- **2021 Definition 19.6.4 (A), p. 895, the special form**: for `Ψ̄ = Ψ̄'` and
`h = (o, Ψ(g, o), g ∗ o)`, `F̄_h(a) = (a, Ψ(g, p(a)), g ∗ a)` for `a ∈ K|V(o)`. -/
theorem definition_19_6_4_A_hat (g : Ψ.1.G) (o : (Fb.strU Ψ).O)
    (hq : (Fb.strU Ψ).p a ∈ F.dom _ _ ((Fb.baseUnif Ψ).1.hat (g, o))) :
    Fb.mapBar F Ψ Ψ ((Fb.baseUnif Ψ).1.hat (g, o)) a = Ψ.1.hat (g, a) := by
  refine (mapBar_eq_iff hq).2 ⟨rfl, ?_⟩
  rw [StrongBundleStr.proj_hat]
  exact (F.map_hat (Fb.baseUnif Ψ) (g, o) _ hq).symm

/-- **2021 Definition 19.6.4 (A), p. 895**: in particular `f̄_h(a) = g ∗ a`, covering
`f_h(p(a)) = g ∗ p(a) = p(g ∗ a)`. -/
theorem definition_19_6_4_A_hat_fmap (g : Ψ.1.G) (o : (Fb.strU Ψ).O)
    (hq : (Fb.strU Ψ).p a ∈ F.dom _ _ ((Fb.baseUnif Ψ).1.hat (g, o))) :
    Fb.fmapBar F Ψ Ψ ((Fb.baseUnif Ψ).1.hat (g, o)) a = g • a ∧
      F.fmap _ _ ((Fb.baseUnif Ψ).1.hat (g, o)) ((Fb.strU Ψ).p a) = (Fb.strU Ψ).p (g • a) := by
  refine ⟨by rw [fmapBar, definition_19_6_4_A_hat g o hq]; rfl, ?_⟩
  rw [UniformizerConstruction.TransitionData.fmap, F.map_hat (Fb.baseUnif Ψ) (g, o) _ hq,
    (Fb.strU Ψ).p_smul]
  rfl

/-- **2021 Definition 19.6.4 (B), p. 895** (stability): `F̄_{F_h(q)}(a) = F̄_h(a)` for `q ∈ V(o)`
and `p(a) ∈ V(o) ∩ V(q)`. -/
theorem definition_19_6_4_B {q : (Fb.strU Ψ).O} (hq : q ∈ F.dom _ _ k)
    (ha : (Fb.strU Ψ).p a ∈ F.dom _ _ (F.map _ _ k q) ∩ F.dom _ _ k) :
    Fb.mapBar F Ψ Ψ' (F.map _ _ k q) a = Fb.mapBar F Ψ Ψ' k a :=
  StrongBundleStr.liftMap_congr (F.stability _ _ k q hq _ ha)

/-- **2021 Definition 19.6.4 (C), p. 895** (identity): `F̄_{u(o)}(a) = (a, 1_{Ψ(p(a))}, a) = u(a)`
for `p(a) ∈ V(o)`. -/
theorem definition_19_6_4_C (o : (Fb.strU Ψ).O)
    (hq : (Fb.strU Ψ).p a ∈ F.dom _ _ (TransitionSet.unit o : (Fb.baseUnif Ψ).1.Trans _)) :
    Fb.mapBar F Ψ Ψ (TransitionSet.unit o) a = TransitionSet.unit a := by
  refine (mapBar_eq_iff hq).2 ⟨rfl, ?_⟩
  rw [StrongBundleStr.proj_unit]
  exact (F.identity (Fb.baseUnif Ψ) o _ hq).symm

/-- **2021 Definition 19.6.4 (D), p. 895** (inversion): `F̄_{ι(h)}(f̄_h(a)) = ι(F̄_h(a))` for `a`
with `p(a) ∈ W(o)`, i.e. `p(a) ∈ V(o)` and `f_h(p(a)) ∈ V(o')`. -/
theorem definition_19_6_4_D (hq : (Fb.strU Ψ).p a ∈ F.dom _ _ k)
    (hq' : F.fmap _ _ k ((Fb.strU Ψ).p a) ∈ F.dom _ _ k.inv) :
    Fb.mapBar F Ψ' Ψ k.inv (Fb.fmapBar F Ψ Ψ' k a) = (Fb.mapBar F Ψ Ψ' k a).inv := by
  have hq2 : (Fb.strU Ψ').p (Fb.fmapBar F Ψ Ψ' k a) ∈ F.dom _ _ k.inv := by
    rw [p_fmapBar]; exact hq'
  refine (mapBar_eq_iff hq2).2 ⟨rfl, ?_⟩
  rw [StrongBundleStr.proj_inv, proj_mapBar, p_fmapBar]
  exact (F.inversion _ _ k _ hq hq').symm

/-- **2021 Definition 19.6.4 (E), p. 896** (multiplication): for `s(h') = t(h)`,
`m(F̄_{h'}(f̄_h(a)), F̄_h(a)) = F̄_{m(h', h)}(a)` for `p(a) ∈ W(o) ∩ V̂(o)` (`hc` is the
composability of the two elements, a consequence of the hypotheses). -/
theorem definition_19_6_4_E {k' : (Fb.baseUnif Ψ').1.Trans (Fb.baseUnif Ψ'').1}
    (hk : k'.src = k.tgt) (hq : (Fb.strU Ψ).p a ∈ F.dom _ _ k)
    (hq' : F.fmap _ _ k ((Fb.strU Ψ).p a) ∈ F.dom _ _ k')
    (hm : (Fb.strU Ψ).p a ∈
      F.dom _ _ (TransitionSet.comp k' k (TransitionSet.mor_composable_of_src_eq_tgt hk)))
    (hc : μ.cat.toGroupoidStr.src (Fb.mapBar F Ψ' Ψ'' k' (Fb.fmapBar F Ψ Ψ' k a)).mor =
      μ.cat.toGroupoidStr.tgt (Fb.mapBar F Ψ Ψ' k a).mor) :
    TransitionSet.comp (Fb.mapBar F Ψ' Ψ'' k' (Fb.fmapBar F Ψ Ψ' k a)) (Fb.mapBar F Ψ Ψ' k a) hc =
      Fb.mapBar F Ψ Ψ'' (TransitionSet.comp k' k (TransitionSet.mor_composable_of_src_eq_tgt hk))
        a := by
  have e1 : (Fb.strU Ψ).proj (Fb.strU Ψ') (Fb.mapBar F Ψ Ψ' k a) =
      F.map _ _ k ((Fb.strU Ψ).p a) := proj_mapBar
  have e2 : (Fb.strU Ψ').proj (Fb.strU Ψ'') (Fb.mapBar F Ψ' Ψ'' k' (Fb.fmapBar F Ψ Ψ' k a)) =
      F.map _ _ k' (F.map _ _ k ((Fb.strU Ψ).p a)).tgt := by
    rw [proj_mapBar, p_fmapBar]; rfl
  symm
  refine (mapBar_eq_iff hm).2 ⟨definition_19_6_4_A_src hq, ?_⟩
  rw [(Fb.strU Ψ).proj_comp (Fb.strU Ψ') (Fb.strU Ψ'') _ _ hc,
    ← F.multiplication _ _ _ k k' hk _ hq hq' hm]
  congr 1

/-- **2021 Definition 19.6.4 (F), p. 896** (M-Hausdorff): for `h₁ ≠ h₂` in `M(Ψ, Ψ')` with the
same source `o`, the images of `K|W` under `F̄_{h₁}`, `F̄_{h₂}` are disjoint for a small open
`W ∋ o` (from the M-Hausdorff property of the underlying `F_h`). -/
theorem definition_19_6_4_F {k₁ k₂ : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1} (hne : k₁ ≠ k₂)
    (hs : k₁.src = k₂.src) :
    ∃ W : Set (Fb.strU Ψ).O, IsOpen W ∧ k₁.src ∈ W ∧ W ⊆ F.dom _ _ k₁ ∩ F.dom _ _ k₂ ∧
      Disjoint (Fb.mapBar F Ψ Ψ' k₁ '' ((Fb.strU Ψ).p ⁻¹' W))
        (Fb.mapBar F Ψ Ψ' k₂ '' ((Fb.strU Ψ).p ⁻¹' W)) := by
  obtain ⟨W, hW, ho, hsub, hdisj⟩ := F.hausdorff _ _ k₁ k₂ hne hs
  refine ⟨W, hW, ho, hsub, Set.disjoint_left.2 ?_⟩
  rintro _ ⟨b, hb, rfl⟩ ⟨b', hb', e⟩
  have e' := congrArg ((Fb.strU Ψ).proj (Fb.strU Ψ')) e
  rw [proj_mapBar, proj_mapBar] at e'
  exact Set.disjoint_left.1 hdisj ⟨_, hb, rfl⟩ ⟨_, hb', e'⟩

end Lift

/-! ### Definition 19.6.4: bundle transition data -/

/-- **2021 Definition 19.6.4, p. 895**: **bundle transition data** (a lift `F̄` of transition data
`F` satisfying the transition requirements for strong bundles): transition data `F` of the
underlying uniformizer construction such that (A) for every `h ∈ M(Ψ, Ψ')`,
`f̄_h : K|V(o) → K'` is a strong bundle isomorphism onto the open `K'|f_h(V(o))` covering
`f_h`.  The rest of (A) and (B)–(F) hold for every lift (`definition_19_6_4_A_src`, …,
`definition_19_6_4_F`). -/
structure BundleTransitionData : Type (u + 1) where
  /-- The underlying transition data `F`. -/
  toTD : Fb.base.TransitionData
  /-- (A) `f̄_h` is a strong bundle isomorphism onto an open image covering `f_h`. -/
  diffeo_bar : ∀ (Ψ Ψ' : Fb.Unif) (k : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1),
    ∃ (g : (Fb.strU Ψ').O → (Fb.strU Ψ).O) (Φinv : Ψ'.1.O → Ψ.1.O),
      (Fb.strU Ψ).B.IsLocalIso₂ (Fb.strU Ψ').B (toTD.fmap _ _ k) g (Fb.fmapBar toTD Ψ Ψ' k) Φinv
        (toTD.dom _ _ k) (toTD.fmap _ _ k '' toTD.dom _ _ k)

namespace BundleTransitionData

variable {Fb} (Fbar : Fb.BundleTransitionData)

/-- `f̄_h : K|V(o) → K'` is an sc-diffeomorphism onto an open image (on the M-polyfolds `K`). -/
theorem isScDiffeoOn_fmapBar (Ψ Ψ' : Fb.Unif) (k : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1) :
    ∃ Φinv : Ψ'.1.O → Ψ.1.O, Ψ.1.P.IsScDiffeoOn Ψ'.1.P (Fb.fmapBar Fbar.toTD Ψ Ψ' k) Φinv
      ((Fb.strU Ψ).p ⁻¹' Fbar.toTD.dom _ _ k)
      (Fb.fmapBar Fbar.toTD Ψ Ψ' k '' ((Fb.strU Ψ).p ⁻¹' Fbar.toTD.dom _ _ k)) := by
  obtain ⟨g, Φinv, hL⟩ := Fbar.diffeo_bar Ψ Ψ' k
  have hz := hL.zero
  rw [(Fb.strU Ψ).toMPolyfold0_eq, (Fb.strU Ψ').toMPolyfold0_eq] at hz
  refine ⟨Φinv, ?_⟩
  rw [hz.image_eq]
  exact hz

/-- **Restriction (p. 896)**: replacing every `V(o)` by a smaller open `W(o)` (and `K|V(o)` by
`K|W(o)`) gives again bundle transition data. -/
def restrict (Q : ∀ (Ψ Ψ' : Fb.base.Unif), Ψ.1.Trans Ψ'.1 → Set Ψ.1.O)
    (hQo : ∀ (Ψ Ψ' : Fb.base.Unif) h, IsOpen (Q Ψ Ψ' h))
    (hQm : ∀ (Ψ Ψ' : Fb.base.Unif) (h : Ψ.1.Trans Ψ'.1), h.src ∈ Q Ψ Ψ' h)
    (hQs : ∀ (Ψ Ψ' : Fb.base.Unif) h, Q Ψ Ψ' h ⊆ Fbar.toTD.dom Ψ Ψ' h) :
    Fb.BundleTransitionData where
  toTD := Fbar.toTD.restrict Q hQo hQm hQs
  diffeo_bar Ψ Ψ' k := by
    obtain ⟨g, Φinv, hL⟩ := Fbar.diffeo_bar Ψ Ψ' k
    exact ⟨g, Φinv, hL.restrict_image (hQo _ _ _) (hQs _ _ _)⟩

/-- **Equivalence (p. 896)**, as printed: `F̄` and `F̄'` have a common identical restriction:
for every `h` an open `W(o) ∋ o` inside both domains with `F_h = F'_h` on `W(o)` and
`F̄_h = F̄'_h` on `K|W(o)`. -/
def Equiv (F₁ F₂ : Fb.BundleTransitionData) : Prop :=
  ∀ (Ψ Ψ' : Fb.Unif) (k : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1),
    ∃ W : Set (Fb.strU Ψ).O, IsOpen W ∧ k.src ∈ W ∧ W ⊆ F₁.toTD.dom _ _ k ∩ F₂.toTD.dom _ _ k ∧
      EqOn (F₁.toTD.map _ _ k) (F₂.toTD.map _ _ k) W ∧
      EqOn (Fb.mapBar F₁.toTD Ψ Ψ' k) (Fb.mapBar F₂.toTD Ψ Ψ' k) ((Fb.strU Ψ).p ⁻¹' W)

/-- **Bundle transition data are equivalent iff the underlying transition data are** (the lifts
are determined by `F`). -/
theorem equiv_iff {F₁ F₂ : Fb.BundleTransitionData} : F₁.Equiv F₂ ↔ F₁.toTD.Equiv F₂.toTD := by
  constructor
  · intro e Ψb Ψb' k
    obtain ⟨Ψ₀, α, Ψe, hΨe, rfl⟩ := Ψb
    obtain ⟨Ψ₀', α', Ψe', hΨe', rfl⟩ := Ψb'
    obtain ⟨W, hW, ho, hs, he, -⟩ := e ⟨Ψe, α, hΨe⟩ ⟨Ψe', α', hΨe'⟩ k
    exact ⟨W, hW, ho, hs, he⟩
  · intro e Ψ Ψ' k
    obtain ⟨W, hW, ho, hs, he⟩ := e (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') k
    exact ⟨W, hW, ho, hs, he, fun a ha => mapBar_congr (he ha)⟩

variable (Fb) in
/-- The equivalence relation of p. 896 on bundle transition data. -/
def setoid : Setoid Fb.BundleTransitionData where
  r := Equiv
  iseqv := ⟨fun _ => equiv_iff.2 (UniformizerConstruction.TransitionData.equiv_refl _),
    fun e => equiv_iff.2 (equiv_iff.1 e).symm,
    fun e e' => equiv_iff.2 ((equiv_iff.1 e).trans (equiv_iff.1 e'))⟩

/-- A restriction is equivalent to the original bundle transition data. -/
theorem equiv_restrict (Q : ∀ (Ψ Ψ' : Fb.base.Unif), Ψ.1.Trans Ψ'.1 → Set Ψ.1.O)
    (hQo : ∀ (Ψ Ψ' : Fb.base.Unif) h, IsOpen (Q Ψ Ψ' h))
    (hQm : ∀ (Ψ Ψ' : Fb.base.Unif) (h : Ψ.1.Trans Ψ'.1), h.src ∈ Q Ψ Ψ' h)
    (hQs : ∀ (Ψ Ψ' : Fb.base.Unif) h, Q Ψ Ψ' h ⊆ Fbar.toTD.dom Ψ Ψ' h) :
    Fbar.Equiv (Fbar.restrict Q hQo hQm hQs) :=
  equiv_iff.2 (Fbar.toTD.equiv_restrict Q hQo hQm hQs)

/-! #### The lift as transition data of `E_μ` -/

/-- `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` for members of the uniformizer construction `toE` of `E_μ`. -/
abbrev projE {Ψ Ψ' : Fb.toE.Unif} (h : Ψ.1.Trans Ψ'.1) :
    (Fb.baseUnif (Fb.ofE Ψ)).1.Trans (Fb.baseUnif (Fb.ofE Ψ')).1 :=
  (Fb.strU (Fb.ofE Ψ)).proj (Fb.strU (Fb.ofE Ψ')) h

/-- **The lift `F̄` as transition data of `E_μ`**: for `h̄ ∈ M(Ψ̄, Ψ̄')`, the map
`F̄_{p(h̄)} : K|V(p(s(h̄))) → M(Ψ̄, Ψ̄')`.  Its properties are (A)–(F) of Definition 19.6.4. -/
def toETD : Fb.toE.TransitionData where
  dom Ψ Ψ' h := (Fb.strU (Fb.ofE Ψ)).p ⁻¹' Fbar.toTD.dom _ _ (projE h)
  map Ψ Ψ' h := Fb.mapBar Fbar.toTD (Fb.ofE Ψ) (Fb.ofE Ψ') (projE h)
  isOpen_dom Ψ Ψ' h := (Fbar.toTD.isOpen_dom _ _ _).preimage (Fb.strU (Fb.ofE Ψ)).continuous_p
  mem_dom Ψ Ψ' h := Fbar.toTD.mem_dom _ _ (projE h)
  map_src Ψ Ψ' h := (mapBar_eq_iff (Fbar.toTD.mem_dom _ _ (projE h))).2
    ⟨rfl, (Fbar.toTD.map_src _ _ (projE h)).symm⟩
  src_map Ψ Ψ' h q hq := definition_19_6_4_A_src hq
  diffeo Ψ Ψ' h := Fbar.isScDiffeoOn_fmapBar (Fb.ofE Ψ) (Fb.ofE Ψ') (projE h)
  map_hat Ψ pr q hq := by
    have e : projE (Ψ.1.hat pr) =
        (Fb.baseUnif (Fb.ofE Ψ)).1.hat (pr.1, (Fb.strU (Fb.ofE Ψ)).p pr.2) :=
      (Fb.strU (Fb.ofE Ψ)).proj_hat pr.1 pr.2
    change (Fb.strU (Fb.ofE Ψ)).p q ∈ Fbar.toTD.dom _ _ (projE (Ψ.1.hat pr)) at hq
    change Fb.mapBar Fbar.toTD (Fb.ofE Ψ) (Fb.ofE Ψ) (projE (Ψ.1.hat pr)) q = _
    rw [e] at hq ⊢
    exact definition_19_6_4_A_hat (Fb := Fb) (F := Fbar.toTD) (Ψ := Fb.ofE Ψ) (a := q) pr.1 _ hq
  stability Ψ Ψ' h q hq a ha := by
    have e : projE (Fb.mapBar Fbar.toTD (Fb.ofE Ψ) (Fb.ofE Ψ') (projE h) q) =
        Fbar.toTD.map _ _ (projE h) ((Fb.strU (Fb.ofE Ψ)).p q) := proj_mapBar
    change (Fb.strU (Fb.ofE Ψ)).p a ∈
      Fbar.toTD.dom _ _ (projE (Fb.mapBar Fbar.toTD (Fb.ofE Ψ) (Fb.ofE Ψ') (projE h) q)) ∩
        Fbar.toTD.dom _ _ (projE h) at ha
    change Fb.mapBar Fbar.toTD (Fb.ofE Ψ) (Fb.ofE Ψ')
      (projE (Fb.mapBar Fbar.toTD (Fb.ofE Ψ) (Fb.ofE Ψ') (projE h) q)) a = _
    rw [e] at ha ⊢
    exact definition_19_6_4_B hq ha
  identity Ψ o q hq := by
    have e : projE (TransitionSet.unit o : Ψ.1.Trans Ψ.1) =
        TransitionSet.unit ((Fb.strU (Fb.ofE Ψ)).p o) := (Fb.strU (Fb.ofE Ψ)).proj_unit o
    change (Fb.strU (Fb.ofE Ψ)).p q ∈
      Fbar.toTD.dom _ _ (projE (TransitionSet.unit o : Ψ.1.Trans Ψ.1)) at hq
    change Fb.mapBar Fbar.toTD (Fb.ofE Ψ) (Fb.ofE Ψ)
      (projE (TransitionSet.unit o : Ψ.1.Trans Ψ.1)) q = _
    rw [e] at hq ⊢
    exact definition_19_6_4_C _ hq
  inversion Ψ Ψ' h q hq hq' := by
    have hq'' : Fbar.toTD.fmap _ _ (projE h) ((Fb.strU (Fb.ofE Ψ)).p q) ∈
        Fbar.toTD.dom _ _ (projE h).inv := by
      have := hq'
      change (Fb.strU (Fb.ofE Ψ')).p (Fb.fmapBar Fbar.toTD _ _ (projE h) q) ∈
        Fbar.toTD.dom _ _ (projE h).inv at this
      rwa [p_fmapBar] at this
    exact definition_19_6_4_D hq hq''
  multiplication Ψ Ψ' Ψ'' h h' hh q hq hq' hm := by
    have hk : (projE h').src = (projE h).tgt := congrArg (Fb.strU (Fb.ofE Ψ')).p hh
    have e : projE (TransitionSet.comp h' h (TransitionSet.mor_composable_of_src_eq_tgt hh)) =
        TransitionSet.comp (projE h') (projE h) (TransitionSet.mor_composable_of_src_eq_tgt hk) :=
      (Fb.strU (Fb.ofE Ψ)).proj_comp (Fb.strU (Fb.ofE Ψ')) (Fb.strU (Fb.ofE Ψ'')) _ _ _
    have hq'' : Fbar.toTD.fmap _ _ (projE h) ((Fb.strU (Fb.ofE Ψ)).p q) ∈
        Fbar.toTD.dom _ _ (projE h') := by
      have := hq'
      change (Fb.strU (Fb.ofE Ψ')).p (Fb.fmapBar Fbar.toTD _ _ (projE h) q) ∈
        Fbar.toTD.dom _ _ (projE h') at this
      rwa [p_fmapBar] at this
    change (Fb.strU (Fb.ofE Ψ)).p q ∈ Fbar.toTD.dom _ _
      (projE (TransitionSet.comp h' h (TransitionSet.mor_composable_of_src_eq_tgt hh))) at hm
    change _ = Fb.mapBar Fbar.toTD (Fb.ofE Ψ) (Fb.ofE Ψ'')
      (projE (TransitionSet.comp h' h (TransitionSet.mor_composable_of_src_eq_tgt hh))) q
    rw [e] at hm ⊢
    exact definition_19_6_4_E hk hq hq'' hm _
  hausdorff Ψ Ψ' h₁ h₂ hne hs := by
    have hne' : projE h₁ ≠ projE h₂ := fun e =>
      hne ((Fb.strU (Fb.ofE Ψ)).eq_of_proj (Fb.strU (Fb.ofE Ψ')) hs e)
    obtain ⟨W, hW, ho, hsub, hdisj⟩ :=
      definition_19_6_4_F (F := Fbar.toTD) hne' (congrArg (Fb.strU (Fb.ofE Ψ)).p hs)
    exact ⟨_, hW.preimage (Fb.strU (Fb.ofE Ψ)).continuous_p, ho,
      fun _ ha => hsub ha, hdisj⟩

@[simp] theorem toETD_map {Ψ Ψ' : Fb.toE.Unif} (h : Ψ.1.Trans Ψ'.1) :
    Fbar.toETD.map Ψ Ψ' h = Fb.mapBar Fbar.toTD (Fb.ofE Ψ) (Fb.ofE Ψ') (projE h) := rfl

@[simp] theorem toETD_dom {Ψ Ψ' : Fb.toE.Unif} (h : Ψ.1.Trans Ψ'.1) :
    Fbar.toETD.dom Ψ Ψ' h = (Fb.strU (Fb.ofE Ψ)).p ⁻¹' Fbar.toTD.dom _ _ (projE h) := rfl

/-- Equivalent underlying transition data give equivalent transition data of `E_μ`. -/
theorem toETD_equiv {F₁ F₂ : Fb.BundleTransitionData} (e : F₁.toTD.Equiv F₂.toTD) :
    F₁.toETD.Equiv F₂.toETD := fun Ψ Ψ' h => by
  obtain ⟨W, hW, ho, hs, he⟩ := e _ _ (projE h)
  exact ⟨_, hW.preimage (Fb.strU (Fb.ofE Ψ)).continuous_p, ho, fun _ ha => hs ha,
    fun _ ha => mapBar_congr (he ha)⟩

end BundleTransitionData

/-! ### Definitions 19.6.5 and 19.6.6 -/

/-- **2021 Definition 19.6.5, p. 896**: a **strong bundle transition construction**: an
equivalence class of bundle transition data. -/
def StrongBundleTransitionConstruction : Type (u + 1) :=
  Quotient (BundleTransitionData.setoid Fb)

variable {Fb}

/-- **2021 p. 896: a representative `F̄` induces a representative `F` of the underlying transition
construction.** -/
def StrongBundleTransitionConstruction.toBaseTC (𝓕b : Fb.StrongBundleTransitionConstruction) :
    Fb.base.TransitionConstruction :=
  Quotient.map BundleTransitionData.toTD
    (fun _ _ e => BundleTransitionData.equiv_iff.1 e) 𝓕b

/-- The transition construction of `E_μ` induced by a strong bundle transition construction. -/
def StrongBundleTransitionConstruction.toETC (𝓕b : Fb.StrongBundleTransitionConstruction) :
    Fb.toE.TransitionConstruction :=
  Quotient.map BundleTransitionData.toETD
    (fun _ _ e => BundleTransitionData.toETD_equiv (BundleTransitionData.equiv_iff.1 e)) 𝓕b

end StrongBundleUniformizerConstruction

variable (C) in
/-- **2021 Definition 19.6.6, p. 896**: a **basic strong bundle construction** `(F̄, 𝓕̄)` for
`(S, μ)`: a strong bundle uniformizer construction `F̄` and an associated strong bundle transition
construction `𝓕̄`. -/
structure BasicStrongBundleConstruction (μ : C.BanFunctor) : Type (u + 1) where
  /-- The strong bundle uniformizer construction `F̄`. -/
  U : StrongBundleUniformizerConstruction μ
  /-- The strong bundle transition construction `𝓕̄`. -/
  𝓕 : U.StrongBundleTransitionConstruction

namespace BasicStrongBundleConstruction

variable {μ : C.BanFunctor} (B : C.BasicStrongBundleConstruction μ)

/-- **The underlying basic construction `(F, 𝓕)` of `S`.** -/
abbrev base : C.BasicConstruction := ⟨B.U.base, B.𝓕.toBaseTC⟩

/-- **The basic construction of `E_μ`** formed by the functors `Ψ̄` and the lifts `F̄`. -/
abbrev toE : μ.cat.BasicConstruction := ⟨B.U.toE, B.𝓕.toETC⟩

/-- A representative `F̄` of `𝓕̄`. -/
def rep : B.U.BundleTransitionData := Quotient.out B.𝓕

theorem mk_rep : (⟦B.rep⟧ : B.U.StrongBundleTransitionConstruction) = B.𝓕 := Quotient.out_eq _

/-- The underlying transition data of the representative represent `𝓕`. -/
theorem base_rep : (⟦B.rep.toTD⟧ : B.U.base.TransitionConstruction) = B.base.𝓕 := by
  change _ = StrongBundleUniformizerConstruction.StrongBundleTransitionConstruction.toBaseTC B.𝓕
  rw [← B.mk_rep]; rfl

/-- The lift of the representative represents the transition construction of `E_μ`. -/
theorem toE_rep : (⟦B.rep.toETD⟧ : B.U.toE.TransitionConstruction) = B.toE.𝓕 := by
  change _ = StrongBundleUniformizerConstruction.StrongBundleTransitionConstruction.toETC B.𝓕
  rw [← B.mk_rep]; rfl

end BasicStrongBundleConstruction

end GroupoidalCategory

end Polyfold
