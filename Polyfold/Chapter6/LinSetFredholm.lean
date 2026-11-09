import Polyfold.Chapter6.LinSet
import Polyfold.Chapter3.LinearizationChartsScG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.2, **Definition 6.2.1**
(p. 239; preprint: Definition 6.1, p. 201): **the operators of `Lin(f, x)` are sc-Fredholm, all of
one index, on every level**.  Closes gap G.64 (Findings, Chapter 6, item 40).

# `Lin(f, x)` consists of sc-Fredholm operators

## The text, paraphrased

(Definition 6.2.1) At a smooth point `x`, `Lin(f, x)` is the set of the operators
`(f − s)'(x) + a : T_xX → Y_x`, `s` an sc⁺-section with `s(x) = f(x)` and `a` an sc⁺-operator;
they are sc-Fredholm operators, all with the same Fredholm index.

## What is formalized

* `ChartPoint.exists_isScFredholm_of_mem_linSet`: **every `L ∈ Lin(f, x)`** (read at a chart
  point, `ChartPoint.linSet`) **is level `0` of an sc-Fredholm operator `S : T_zO → K_z`**
  between the sc-subspaces `T_zO` and `K_z` with their induced sc-structures, and every level
  `S_m` is Fredholm of index `ind L`.
* `ChartPoint.definition_6_2_1_linSet_isScFredholm`: the same with **one index `i` for all members**
  of `Lin(f, x)` and all levels.

## Proof

For `L = (f + s)'(x) + a`: `f + s` is sc-Fredholm (Theorem 3.1.15, `theorem_3_1_18_preprint`) with a zero at
`x`, so its linearization restricted to `T_zO → K_z` is sc-Fredholm in every chart
(`StrongBundle.linAt_isScFredholm`, row V3.96); `a` is level `0` of an sc⁺-operator
(`IsScPlusOp`), and an sc-Fredholm operator plus an sc⁺-operator is sc-Fredholm of the same index
on every level (Proposition 1.1.11, `proposition_1_1_11_preprint`, `proposition_1_1_11_index_lvl`).  The
level-`0` operator is `L` read through `(T_zO)₀ = T_zO` and `(K_z)₀ = K_z`
(`ScBanach.levelSubZeroEquiv`), so the indices agree (`isFredholm_iff_of_conj`).

## Reading

As in `LinSet.lean`, `T_xX` and `Y_x` are read in a chart as `T_zO` and `K_z` (gaps G.6, G.7,
G.13); "sc-Fredholm operator `T_xX → Y_x`" is an sc-Fredholm operator between these sc-subspaces
with the induced sc-structures (`ScBanach.ofSubspace`), whose level `0` is the member of `Lin(f, x)`.
No hypothesis is added: smoothness of `x` follows from `(f + s)(x) = 0`.
-/

open Set Function Module

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x)

/-- **2021 Definition 6.2.1, p. 239: a member of `Lin(f, x)` is an sc-Fredholm operator**
(preprint: Definition 6.1, p. 201).  For `L ∈ Lin(f, x)` (at the chart point `p`) there is an
sc-Fredholm operator `S : T_zO → K_z` between the sc-subspaces `T_zO`, `K_z` with their induced
sc-structures whose level `0` is `L`, and every level `S_m` is Fredholm of index `ind L`. -/
theorem exists_isScFredholm_of_mem_linSet (hf : B.IsScFredholmSection f)
    {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) :
    ∃ (hT : p.c.φ.model.E.IsScSubspace p.T) (hK : p.c.F.IsScSubspace p.K)
      (S : ScOperator (p.c.φ.model.E.ofSubspace hT) (p.c.F.ofSubspace hK)),
      (∀ v : (p.c.φ.model.E.ofSubspace hT) 0,
        ((S 0 v).1 : p.c.F 0) = (L ⟨v.1, v.2⟩ : p.c.F 0)) ∧
      IsScFredholm S ∧ ∀ m, (S m).IsFredholm ∧ fredholmIndex (S m) = fredholmIndex L := by
  obtain ⟨s, hs, hx, a, ha, hLv⟩ := hL
  have hF := theorem_3_1_18_preprint hf hs
  obtain ⟨hD, hT, hK, hTK, hDeq, hsc, -⟩ :=
    StrongBundle.linAt_isScFredholm hF hx p.isChart p.mem_source p.toBase_z p.mem_U
  obtain ⟨hT', hK', Sa, hSa⟩ := ha
  set D := hD.toScOperator.restrict hT hK hTK with hDdef
  set S : ScOperator (p.c.φ.model.E.ofSubspace hT) (p.c.F.ofSubspace hK) :=
    D + Sa.toScOperator with hSdef
  have h0 : ∀ v : (p.c.φ.model.E.ofSubspace hT) 0,
      ((S 0 v).1 : p.c.F 0) = (L ⟨v.1, v.2⟩ : p.c.F 0) := fun v => by
    rw [hLv ⟨v.1, v.2⟩, ← hDeq v, ← hSa v]
    rfl
  have hconj : ∀ v, L (p.c.φ.model.E.levelSubZeroEquiv p.T v) =
      p.c.F.levelSubZeroEquiv p.K (S 0 v) := fun v => Subtype.ext (h0 v).symm
  have hS0 := proposition_1_1_11_index_lvl hsc Sa 0
  have hidx : fredholmIndex L = fredholmIndex (S 0) :=
    (isFredholm_iff_of_conj (L := S 0) (L' := L) hconj).2 hS0.1
  refine ⟨hT, hK, S, h0, proposition_1_1_11_preprint hsc Sa, fun m => ?_⟩
  obtain ⟨hFm, him⟩ := proposition_1_1_11_index_lvl hsc Sa m
  exact ⟨hFm, by rw [him, hidx, hS0.2]⟩

variable (f) in
/-- **2021 Definition 6.2.1: the members of `Lin(f, x)` are sc-Fredholm operators, all with the
same Fredholm index**: there is one `i` such that every `L ∈ Lin(f, x)` is level `0` of an
sc-Fredholm `S : T_zO → K_z` with every level `S_m` Fredholm of index `i`
(`exists_isScFredholm_of_mem_linSet` and `exists_index_linSet`). -/
theorem definition_6_2_1_linSet_isScFredholm (hf : B.IsScFredholmSection f) :
    ∃ i : ℤ, ∀ L ∈ p.linSet f,
      ∃ (hT : p.c.φ.model.E.IsScSubspace p.T) (hK : p.c.F.IsScSubspace p.K)
        (S : ScOperator (p.c.φ.model.E.ofSubspace hT) (p.c.F.ofSubspace hK)),
        (∀ v : (p.c.φ.model.E.ofSubspace hT) 0,
          ((S 0 v).1 : p.c.F 0) = (L ⟨v.1, v.2⟩ : p.c.F 0)) ∧
        IsScFredholm S ∧ ∀ m, (S m).IsFredholm ∧ fredholmIndex (S m) = i := by
  obtain ⟨i, hi⟩ := p.exists_index_linSet hf
  refine ⟨i, fun L hL => ?_⟩
  obtain ⟨hT, hK, S, h0, hS, hm⟩ := p.exists_isScFredholm_of_mem_linSet hf hL
  exact ⟨hT, hK, S, h0, hS, fun m => ⟨(hm m).1, (hm m).2.trans (hi L hL).2⟩⟩

end ChartPoint

end Polyfold
