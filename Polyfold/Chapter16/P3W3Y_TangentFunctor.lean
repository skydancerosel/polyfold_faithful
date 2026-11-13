import Polyfold.Chapter16.P3W3Y_PolyfoldMaps

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.2, pp. 719–720: **Theorem 16.2.4** (2017: Theorem 16.1), the tangent functor.  Numbers and
pages are the 2021 text's.

# The tangent functor

## The text, paraphrased

(Theorem 16.2.4) On the polyfold category `P` there is a natural functor `T`: `(Z, c) ↦ T(Z, c)`
and `f̂ = [(f, 𝔣)] ↦ T f̂ = [(Tf, T𝔣)] : T(Z, c) → T(W, d)`, `Tf` given on representatives by
`|k| = |T𝔣|(|h|)`; "one easily verifies that `T` is a functor".

## What is formalized

* `PSHom.ofGen'`: a generalized map `𝔣 : X → Y` with `f := β ∘ |𝔣| ∘ α⁻¹`.
* **The tangent functor on `PS`**: `PolyfoldStructure.tangentSelf` (`(TX, Id_{|TX|})`, (ZHOU) and
  paracompactness by Proposition 8.1.16 and Theorem 8.1.15) and `PSCat.tangentFunctor :
  PSCat.{u} ⥤ PSCat.{max u 1}`, `(f, 𝔣) ↦ (|T𝔣|, T𝔣)` (a Mathlib `Functor`).
* **Theorem 16.2.4 on sc-smooth maps**: `MapRep.tangent` (`(Tf, T𝔣) : (TX, Tα) → (TY, Tβ)`),
  `ScMap.tangent : ScMap c d → ScMap (Tc) (Td)`, well defined on the classes of Definition 16.1.6
  (`MapRep.tangent_equiv`); `ScMap.tangent_toFun` (`Tf ∘ Tα = Tβ ∘ |T𝔣|`, the text's formula
  `|k| = |T𝔣|(|h|)`), `ScMap.tangent_id` (`T 1 = 1`), `ScMap.tangent_mk_comp` (`T` of the
  composite of representatives with a common middle structure is the composite of the tangents),
  and, for effective middle polyfolds, `ScMap.tangent_comp` (`T(ĝ ∘ f̂) = Tĝ ∘ Tf̂`, assuming
  `Td` effective too).  `theorem_16_2_4` collects these.
* Not formalized: that `T` preserves effectiveness (so that `T` is a Mathlib functor of
  `EffPolyfold`); by `not_definition_16_1_10` there is no category with all polyfolds as objects
  and the sc-smooth maps of Definition 16.1.8 as morphisms.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization EPLocalization.EPLoc

variable {Z W V : Type u} [TopologicalSpace Z] [TopologicalSpace W] [TopologicalSpace V]

namespace PSHom

variable {p : PolyfoldStructure Z} {q : PolyfoldStructure W} {r : PolyfoldStructure V}

/-- The morphism `(β ∘ |𝔣| ∘ α⁻¹, 𝔣)` of `PS` of a generalized map `𝔣 : X → Y`. -/
def ofGen' (g : EPLoc.of p.X ⟶ EPLoc.of q.X) : PSHom p q :=
  ⟨⇑q.β ∘ orbitMap g ∘ ⇑p.β.symm, g, by
    rw [Function.comp_assoc, Function.comp_assoc, p.β.symm_comp_self, Function.comp_id]⟩

@[simp] theorem ofGen'_gen (g : EPLoc.of p.X ⟶ EPLoc.of q.X) : (ofGen' g).gen = g := rfl

theorem ofGen'_comp (g : EPLoc.of p.X ⟶ EPLoc.of q.X) (g' : EPLoc.of q.X ⟶ EPLoc.of r.X) :
    ofGen' (g ≫ g') = (ofGen' g).comp (ofGen' g') :=
  ext rfl

theorem ofGen'_id (p : PolyfoldStructure Z) : ofGen' (𝟙 (EPLoc.of p.X)) = id p := ext rfl

end PSHom

/-! ### The tangent functor on `PS` -/

namespace PolyfoldStructure

/-- The polyfold structure `(TX, Id)` on `|TX|`. -/
def tangentSelf (p : PolyfoldStructure Z) :
    PolyfoldStructure p.X.tangentAny.X.OrbitSpace where
  X := p.X.tangentAny
  paracompact := p.tangent_paracompact
  isZhou := p.tangent_isZhou
  β := Homeomorph.refl _

end PolyfoldStructure

/-- **The tangent functor on the category `PS`** (2021 p. 719): `(X, α) ↦ (TX, Id_{|TX|})`,
`(f, 𝔣) ↦ (|T𝔣|, T𝔣)`. -/
def PSCat.tangentFunctor : PSCat.{u} ⥤ PSCat.{max u 1} where
  obj A := ⟨_, A.p.tangentSelf⟩
  map a := PSHom.ofGen' (tangentHom (PSHom.gen a))
  map_id A := PSHom.ext (tangentHom_id A.p.X)
  map_comp a b := PSHom.ext (tangentHom_comp (PSHom.gen a) (PSHom.gen b))

@[simp] theorem PSCat.tangentFunctor_map_gen {A B : PSCat.{u}} (a : A ⟶ B) :
    (PSCat.tangentFunctor.map a).gen = tangentHom (PSHom.gen a) := rfl

/-! ### Theorem 16.2.4 on sc-smooth maps of polyfolds -/

namespace PolyfoldClass

variable {c : PolyfoldClass Z} {d : PolyfoldClass W} {e : PolyfoldClass V}

/-- `(𝔥, Id) : (X, α) → (X', α')` over the identity gives `(T𝔥, Id) : (TX, Tα) → (TX', Tα')`
over the identity (16.5). -/
theorem tangent_isIdIso {p p' : PolyfoldStructure Z} (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (hp' : (⟦p'⟧ : PolyfoldClass Z) = c) {h : PSHom p p'} (hh : h.IsIdIso) :
    (PSHom.ofGen' (q := tangentStructure p' hp') (p := tangentStructure p hp)
      (tangentHom h.gen)).IsIdIso := by
  refine ⟨?_, isGeneralizedIso_tangentHom hh.2⟩
  change ⇑(tangentHomeomorph p' hp') ∘ orbitMap (tangentHom h.gen) ∘
    ⇑(tangentHomeomorph p hp).symm = _root_.id
  have e := tangentMap_comp hp hp' hh.2 hh.β_eq
  funext v
  change tangentMap p' hp' (orbitMap (tangentHom h.gen) ((tangentHomeomorph p hp).symm v)) = v
  exact (congrFun e _).trans ((tangentHomeomorph p hp).apply_symm_apply v)

namespace MapRep

/-- **The tangent of a representative**: `(Tf, T𝔣) : (TX, Tα) → (TY, Tβ)` (2021 p. 720). -/
def tangent (a : MapRep c d) : MapRep c.tangent d.tangent :=
  ⟨tangentStructure a.p a.hp, definition_16_2_3 a.p a.hp, tangentStructure a.q a.hq,
    definition_16_2_3 a.q a.hq, PSHom.ofGen' (tangentHom a.φ.gen)⟩

/-- **`T` respects Definition 16.1.6.** -/
theorem tangent_equiv {a b : MapRep c d} (hab : a ≈ b) : a.tangent ≈ b.tangent := by
  obtain ⟨h, k, hh, hk, he⟩ := hab
  refine ⟨_, _, tangent_isIdIso a.hp b.hp hh, tangent_isIdIso a.hq b.hq hk, PSHom.ext ?_⟩
  change tangentHom h.gen ≫ tangentHom b.φ.gen = tangentHom a.φ.gen ≫ tangentHom k.gen
  rw [← tangentHom_comp, ← tangentHom_comp]
  exact congrArg tangentHom (congrArg PSHom.gen he)

end MapRep

namespace ScMap

/-- **2021 Theorem 16.2.4, p. 719: the tangent `T f̂ = [(Tf, T𝔣)] : T(Z, c) → T(W, d)`** of an
sc-smooth map. -/
def tangent (F : ScMap c d) : ScMap c.tangent d.tangent :=
  Quotient.map MapRep.tangent (fun _ _ h => MapRep.tangent_equiv h) F

/-- `T[(f, 𝔣)] = [(Tf, T𝔣)]` on every representative. -/
theorem tangent_mk (p : PolyfoldStructure Z) (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (q : PolyfoldStructure W) (hq : (⟦q⟧ : PolyfoldClass W) = d) (φ : PSHom p q) :
    tangent (mk p hp q hq φ) = mk (tangentStructure p hp) (definition_16_2_3 p hp)
      (tangentStructure q hq) (definition_16_2_3 q hq) (PSHom.ofGen' (tangentHom φ.gen)) :=
  rfl

/-- **The text's formula** (2021 p. 720): `Tf ∘ Tα = Tβ ∘ |T𝔣|` for every representative
(`Tf[(z, (X, α), h)] = [(f(z), (Y, β), k)]` with `|k| = |T𝔣|(|h|)`). -/
theorem tangent_toFun (p : PolyfoldStructure Z) (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (q : PolyfoldStructure W) (hq : (⟦q⟧ : PolyfoldClass W) = d) (φ : PSHom p q) :
    (tangent (mk p hp q hq φ)).toFun ∘ tangentMap p hp =
      tangentMap q hq ∘ orbitMap (tangentHom φ.gen) :=
  (PSHom.ofGen' (p := tangentStructure p hp) (q := tangentStructure q hq)
    (tangentHom φ.gen)).comm

/-- **`T 1_{(Z,c)} = 1_{T(Z,c)}`.** -/
theorem tangent_id (c : PolyfoldClass Z) : tangent (id c) = id c.tangent := by
  rw [ScMap.id_eq (c := c.tangent) _ (definition_16_2_3 c.out (Quotient.out_eq c))]
  exact congrArg (mk _ _ _ _) (PSHom.ext (tangentHom_id _))

/-- **`T` of the composite of representatives is the composite of the tangents** (`T` is a
functor on representatives with a common middle structure). -/
theorem tangent_mk_comp (p : PolyfoldStructure Z) (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (q : PolyfoldStructure W) (hq : (⟦q⟧ : PolyfoldClass W) = d) (r : PolyfoldStructure V)
    (hr : (⟦r⟧ : PolyfoldClass V) = e) (a : PSHom p q) (b : PSHom q r) :
    tangent (mk p hp r hr (a.comp b)) =
      mk (tangentStructure p hp) (definition_16_2_3 p hp) (tangentStructure r hr)
        (definition_16_2_3 r hr)
        ((PSHom.ofGen' (p := tangentStructure p hp) (q := tangentStructure q hq)
          (tangentHom a.gen)).comp
          (PSHom.ofGen' (p := tangentStructure q hq) (q := tangentStructure r hr)
            (tangentHom b.gen))) := by
  rw [tangent_mk]
  congr 1
  exact PSHom.ext (tangentHom_comp a.gen b.gen)

/-- **`T(ĝ ∘ f̂) = Tĝ ∘ T f̂`** for an effective middle polyfold `(W, d)` with `T(W, d)` effective
(Definition 16.1.10 is then well defined on both sides). -/
theorem tangent_comp (hd : d.IsEffective) (hTd : d.tangent.IsEffective) (F : ScMap c d)
    (G : ScMap d e) : tangent (comp hd F G) = comp hTd (tangent F) (tangent G) := by
  obtain ⟨p, hp⟩ := Quotient.exists_rep c
  obtain ⟨q, hq⟩ := Quotient.exists_rep d
  obtain ⟨r, hr⟩ := Quotient.exists_rep e
  obtain ⟨a, rfl⟩ := exists_rep F p hp q hq
  obtain ⟨b, rfl⟩ := exists_rep G q hq r hr
  rw [comp_mk hd, tangent_mk_comp p hp q hq r hr a b, tangent_mk, tangent_mk, comp_mk hTd]

end ScMap

/-- **2021 Theorem 16.2.4, p. 719 (2017: Theorem 16.1)**, in the form we prove: `T` is defined on
sc-smooth maps of polyfolds (well defined on the classes of Definition 16.1.6), satisfies
`Tf ∘ Tα = Tβ ∘ |T𝔣|`, `T 1 = 1`, and `T` of the composite of representatives with a common
middle structure is the composite of the tangents; on `PS` it is a functor
(`PSCat.tangentFunctor`). -/
theorem theorem_16_2_4 (c : PolyfoldClass Z) :
    ScMap.tangent (ScMap.id c) = ScMap.id c.tangent ∧
    (∀ (d : PolyfoldClass W) (p : PolyfoldStructure Z) (hp : (⟦p⟧ : PolyfoldClass Z) = c)
      (q : PolyfoldStructure W) (hq : (⟦q⟧ : PolyfoldClass W) = d) (φ : PSHom p q),
      (ScMap.tangent (ScMap.mk p hp q hq φ)).toFun ∘ tangentMap p hp =
        tangentMap q hq ∘ orbitMap (tangentHom φ.gen)) ∧
    (∀ (d : PolyfoldClass W) (e : PolyfoldClass V) (p : PolyfoldStructure Z)
      (hp : (⟦p⟧ : PolyfoldClass Z) = c) (q : PolyfoldStructure W)
      (hq : (⟦q⟧ : PolyfoldClass W) = d) (r : PolyfoldStructure V)
      (hr : (⟦r⟧ : PolyfoldClass V) = e) (a : PSHom p q) (b : PSHom q r),
      ScMap.tangent (ScMap.mk p hp r hr (a.comp b)) =
        ScMap.mk (tangentStructure p hp) (definition_16_2_3 p hp) (tangentStructure r hr)
          (definition_16_2_3 r hr)
          ((PSHom.ofGen' (p := tangentStructure p hp) (q := tangentStructure q hq)
            (tangentHom a.gen)).comp
            (PSHom.ofGen' (p := tangentStructure q hq) (q := tangentStructure r hr)
              (tangentHom b.gen)))) :=
  ⟨ScMap.tangent_id c, fun _ => ScMap.tangent_toFun, fun _ _ => ScMap.tangent_mk_comp⟩

end PolyfoldClass

end Polyfold
