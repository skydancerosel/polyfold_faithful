import Polyfold.Chapter5.BookFormIFT
import Polyfold.Chapter3.GermCalculus

/-!
Hofer–Wysocki–Zehnder, *Applications of Polyfold Theory I: The Polyfolds of Gromov–Witten
Theory* (Memoirs AMS 248, no. 1179, 2017), §2.3: **Definition 2.43** (basic germs, p. 42),
**Definition 2.44** (Fredholm germs, p. 42), **Definition 2.45** (polyfold Fredholm sections,
p. 42), **Proposition 2.42** (p. 41) and **Theorem 2.46** (the implicit function theorem,
pp. 42–43), in the memoir's form, proved from the book *Polyfold and Fredholm Theory* (Springer
2021).

# Basic germs, Fredholm germs and the implicit function theorem of the memoir

## The text, paraphrased

(Definition 2.43) A basic germ is an sc-smooth germ `f : O(ℝⁿ ⊕ W, 0) → (ℝᴺ ⊕ W, 0)` whose
`W`-part is `w − B(a, w)` with `|B(a, w) − B(a, w')|_m ≤ ε|w − w'|_m` near `0` on every level, for
every `ε > 0`.  (Definition 2.44) For `x ∈ X_∞`, `(f, x)` is a Fredholm germ if there is a germ
of an sc⁺-section `s` near `x` with `s(x) = f(x)` such that, in strong bundle coordinates mapping
`x` to `0`, the push-forward `Φ_*(f − s)` has a filled version equivalent to a basic germ.
(Definition 2.45) A polyfold Fredholm section is regularizing and a Fredholm germ at every smooth
point.  (Proposition 2.42) If `(g, 0)` fills `(f, 0)`, then `g + s ∘ r` fills `f + s` for every
sc⁺-section `s` of `K → O`.  (Theorem 2.46) If `f` is a Fredholm section, `f(x) = 0` and
`f'(x)` is onto, there is an open `U ∋ x` such that `S_U = {y ∈ U | f(y) = 0}` has a natural
smooth manifold structure induced from `X`, and `S_U ⊆ X_∞`.

## The book statements used

Definition 3.1.7 (2021 p. 92, basic germ on `O(C̃ ⊕ W, 0)`, `C̃ ⊆ ℝⁿ` a partial quadrant,
`f(0) = 0`), Definition 3.1.11 (p. 96: fill `f` first, then subtract an sc⁺-section `s` with
`s(0) = g(0)`), Lemma 3.1.20 (p. 99), Theorem 1.3.5 (p. 33, corner invariance at level-`1`
points), Definition 2.5.2 (p. 64, tame retraction), Theorem 3.1.22 (p. 100, assumes `d_X ≡ 0`)
and Theorem 3.1.26 (p. 103, good position).

## What is formalized

* `IsBasicGermMemoir` (Definition 2.43) is the book's `IsBasicGerm` with `C̃ = ℝⁿ`;
  `memoir_definition_2_43_B_zero`: `B(0, 0) = 0` follows from `f(0) = 0`.
  `IsConjugateToBasicGermMemoir`: "equivalent to a germ in `C_basic`".
* `memoir_conj_iff`: for `0 ∈ U ⊆ C`, being conjugated to a memoir basic germ is the same as
  `C = E` together with the book's conjugation (`IsConjugateToBasicGerm`).  The memoir's basic
  germs have no quadrant factor, and an sc-diffeomorphism of germs preserves `d_C` at `0`
  (Theorem 1.3.5); so the conjugation forces `d_C(0) = 0`, i.e. `C = E`.
* `memoir_proposition_2_42`: Proposition 2.42 for the 2021 filling (germ reading), from
  `IsFillingGerm.add_section`.
* `StrongBundle.IsFredholmGermMemoir` (Definition 2.44, in the memoir's order: subtract `s`, then
  fill), `StrongBundle.IsFredholmSectionMemoir` (Definition 2.45).
* `memoir_definition_2_44_isScFredholmGermTame2021`: a memoir Fredholm germ is a book sc-Fredholm
  germ (2021 Definition 3.1.11) in a **tame** chart, with `d_X(x) = 0`; the bridge between the two
  orders of operations is Proposition 2.42.
* **`memoir_theorem_2_46`**: Theorem 2.46 as printed (no hypothesis `d_X ≡ 0`, no good position):
  there are `U ∋ x` and `d` such that `S_U ⊆ X_∞`, `S_U` is a sub-M-polyfold whose induced
  structure is that of a `d`-dimensional manifold without boundary, and `f'(y)` is onto of index
  `d` at every `y ∈ S_U`.
* Witness: `memoir_theorem_2_46_hypotheses` — the graph section of a `C^∞` map `φ : ℝⁿ → ℝᵏ` is a
  memoir Fredholm section of the trivial bundle.

## What the text leaves implicit, and the choices made

* **`f(0) = 0` in Definition 2.43** is read from the notation `(ℝᴺ ⊕ W, 0)`; then `B(0, 0) = 0`
  (`memoir_definition_2_43_B_zero`).  The sc⁰-continuity of `B` is part of the book's notion; it
  follows from the sc-smoothness of `f` and is kept as in the book.
* **The germ of an sc⁺-section** `s` of Definition 2.44 is written in the chart in which
  `Φ_*(f − s)` is filled: its principal part `ŝ : E₀ → F₁` with `ŝ ∘ r` sc-smooth into `F¹` on the
  chart's `U` (Definition 2.24) and `(z, ŝ(z)) ∈ K` on `O`.  A germ near `x` is defined on the
  domain of some chart centred at `x`, since charts may be shrunk.
* **Theorem 2.46 and `d_X ≡ 0`.**  The two statements differ: the book's Theorem 3.1.22 assumes
  `d_X ≡ 0`, the memoir does not.  With the memoir's Definition 2.43 the hypothesis is not needed:
  a memoir Fredholm germ at `y` forces `d_X(y) = 0` and a tame chart, so the good position needed
  by Theorem 3.1.26 reduces to surjectivity, and `S_U` (made of smooth points) has no boundary.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace GWMemoir

open Polyfold StrongRetr

/-! ### Partial quadrants with `d_C(0) = 0`, and tameness when `C = E` -/

section Quadrant

variable {E : ScBanach} {C : Set (E 0)}

/-- A partial quadrant with `d_C(0) = 0` is the whole space: `d_C(0)` is the number `n` of
quadrant coordinates of a presentation `E ≅ ℝⁿ ⊕ W`. -/
theorem eq_univ_of_degIndex_zero (hC : IsPartialQuadrant E C) (h0 : (0 : E 0) ∈ C)
    (hd : degIndex E C 0 = 0) : C = univ := by
  obtain ⟨n, W, T, hT⟩ := hC
  rw [degIndex_eq T hT h0] at hd
  have hn : n = 0 := by
    simpa [degIndexWith, quadrantDeg] using hd
  subst hn
  rw [hT]
  ext x
  simp only [mem_preimage, mem_univ, iff_true]
  intro i
  exact i.elim0

/-- **A retraction of an open subset of `E` (`C = E`) is tame** (2021 Definition 2.5.2): every
presentation of `C = E` has `n = 0`, so `d_C ≡ 0` and `E_x = E`, and `A = (1 − Dr(x))E` is an
sc-complement of `T_xO = Dr(x)E`. -/
theorem isTame_of_eq_univ (R : ScRetraction E C) (hC : C = univ) : R.IsTame := by
  intro n W T hT
  have hn : n = 0 := by
    by_contra hn
    have hmem : (T 0).symm ((fun _ => (-1 : ℝ)), 0) ∈ C := by rw [hC]; exact mem_univ _
    rw [hT] at hmem
    have := hmem ⟨0, Nat.pos_of_ne_zero hn⟩
    simp at this
    linarith
  subst hn
  refine ⟨fun x _ => ?_, fun x hx hs => ⟨_, R.isScSplitting_range_scDeriv hx hs, fun v _ => ?_⟩⟩
  · have hmem : ∀ y : E 0, y ∈ C := fun y => by rw [hC]; exact mem_univ _
    rw [degIndex_eq T hT (hmem _), degIndex_eq T hT (hmem _)]
    simp [degIndexWith, quadrantDeg]
  · rw [mem_minimalSubspaceWith]
    intro i
    exact i.elim0

/-- `d(0)` is preserved by the base of a strong bundle isomorphism onto a germ on an open set
(`C' = E'`), Theorem 1.3.5 at the level-`1` point `0`: `d_C(0) = d_{E'}(0) = 0`. -/
theorem degIndex_zero_of_strongBundleIso {F E' F' : ScBanach} {U : Set (E 0)} {U' : Set (E' 0)}
    {Ψ : E 0 × F 0 → E' 0 × F' 0} {Ψ' : E' 0 × F' 0 → E 0 × F 0} {C' : Set (E' 0)}
    (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U') (h0 : (0 : E 0) ∈ U)
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) :
    degIndex E C 0 = degIndex E' C' 0 := by
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have := theorem_1_3_5_lvl1 hU hU' (hΨ.toFun.base_isScSmooth hU).isSc1
    (hΨ.invFun.base_isScSmooth hU').isSc1 (fun u hu => hΨ.toFun.base_mem hu)
    (fun u hu => hΨ.invFun.base_mem hu) (fun u hu => hΨ.base_base hu)
    (fun u hu => hΨ.base_base' hu) h01
  rwa [map_zero, hψ0] at this

end Quadrant

/-! ### Definition 2.43: basic germs without quadrant factor -/

section Basic

variable {Pn : Type} [NormedAddCommGroup Pn] [NormedSpace ℝ Pn] [FiniteDimensional ℝ Pn]
  {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] {W : ScBanach}


/-- **Memoir Definition 2.43, p. 42 (basic germ, the class `C_basic`)**: an sc-smooth germ
`f : O(ℝⁿ ⊕ W, 0) → (ℝᴺ ⊕ W, 0)` with `W`-part `w − B(a, w)` and the contraction estimate on every
level.  It is the book's basic germ (2021 Definition 3.1.7, p. 92) on `O(C̃ ⊕ W, 0)` with
`C̃ = ℝⁿ`: the memoir has no quadrant factor.  (`f(0) = 0` is the notation `(ℝᴺ ⊕ W, 0)`.) -/
abbrev IsBasicGermMemoir (G : ScNbhdGerm (ScBanach.paramProd Pn W) ((univ : Set Pn) ×ˢ univ))
    (f : Pn × W 0 → Q × W 0) (B : Pn × W 0 → W 0) : Prop :=
  IsBasicGerm (univ : Set Pn) G f B

omit [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] in
/-- **Memoir Definition 2.43**: `B(0, 0) = 0` is not an extra condition — it follows from
`f(0) = 0` and `P ∘ f(a, w) = w − B(a, w)` at `0`. -/
theorem memoir_definition_2_43_B_zero {G : ScNbhdGerm (ScBanach.paramProd Pn W) ((univ : Set Pn) ×ˢ univ)}
    {f : Pn × W 0 → Q × W 0} {B : Pn × W 0 → W 0} (hf0 : f 0 = 0)
    (hsnd : ∀ x ∈ G.U 0, (f x).2 = x.2 - B x) : B (0, 0) = 0 := by
  have h := hsnd 0 (G.zero_mem 0)
  rw [hf0] at h
  have h' : (0 : W 0) = 0 - B (0, 0) := h
  rw [zero_sub, eq_comm, neg_eq_zero] at h'
  exact h'

end Basic

section Conj

variable {E F : ScBanach} {C U : Set (E 0)}

/-- **Memoir Definition 2.44, "equivalent to a germ belonging to `C_basic`"**: the principal part
`k : U → F` is conjugated, by a strong bundle isomorphism `Ψ : U ◁ F → U' ◁ (ℝᴺ ⊕ W)` with
`ψ(0) = 0` and `U'` open in `ℝⁿ ⊕ W`, to a memoir basic germ (Definition 2.43).  This is the book's
`IsConjugateToBasicGerm` (2021 Definition 3.1.11, second paragraph) with `C̃ = ℝⁿ`. -/
def IsConjugateToBasicGermMemoir (U : Set (E 0)) (k : E 0 → F 0) : Prop :=
  ∃ (Pn Q : Type) (_ : NormedAddCommGroup Pn) (_ : NormedSpace ℝ Pn) (_ : FiniteDimensional ℝ Pn)
    (_ : NormedAddCommGroup Q) (_ : NormedSpace ℝ Q) (_ : FiniteDimensional ℝ Q)
    (W : ScBanach) (U' : Set ((ScBanach.paramProd Pn W) 0))
    (Ψ : E 0 × F 0 → (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0)
    (Ψ' : (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0 → E 0 × F 0)
    (G : ScNbhdGerm (ScBanach.paramProd Pn W) ((univ : Set Pn) ×ˢ univ))
    (h : Pn × W 0 → Q × W 0) (Bc : Pn × W 0 → W 0),
    IsRelOpenInQuadrant (ScBanach.paramProd Pn W) ((univ : Set Pn) ×ˢ univ) U' ∧
    IsStrongBundleIso U U' Ψ Ψ' ∧ IsStrongBundleMap.base Ψ 0 = 0 ∧ G.U 0 ⊆ U' ∧
    IsBasicGermMemoir G h Bc ∧
    ∀ᶠ u in 𝓝 (0 : E 0), u ∈ U → (Ψ (u, k u)).2 = h (IsStrongBundleMap.base Ψ u)

/-- A memoir conjugation is a book conjugation (`C̃ = ℝⁿ` is a partial quadrant). -/
theorem IsConjugateToBasicGermMemoir.isConjugateToBasicGerm {k : E 0 → F 0}
    (h : IsConjugateToBasicGermMemoir U k) : IsConjugateToBasicGerm U k := by
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, U', Ψ, Ψ', G, hb, Bc, hU', hΨ, h0, hG, hh, hev⟩ := h
  exact ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, univ, U', Ψ, Ψ', G, hb, Bc,
    isPartialQuadrant_univ _, hU', hΨ, h0, hG, hh, hev⟩

/-- A memoir conjugation forces `C = E`: the base `ψ` of `Ψ` is an sc-diffeomorphism onto an open
subset of `ℝⁿ ⊕ W` with `ψ(0) = 0`, so `d_C(0) = 0` (Theorem 1.3.5). -/
theorem IsConjugateToBasicGermMemoir.eq_univ (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U)
    {k : E 0 → F 0} (h : IsConjugateToBasicGermMemoir U k) : C = univ := by
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, U', Ψ, Ψ', G, hb, Bc, hU', hΨ, hψ0, -, -, -⟩ := h
  have hd := degIndex_zero_of_strongBundleIso hU hU' h0 hΨ hψ0
  rw [univ_prod_univ, TrivialBundle.univ_degIndex_eq_zero] at hd
  exact eq_univ_of_degIndex_zero hU.isPartialQuadrant (hU.subset_quadrant h0) hd

/-- **Memoir Definition 2.44 versus 2021 Definition 3.1.11, the conjugation**: for `0 ∈ U ⊆ C`,
`k` is conjugated to a memoir basic germ (no quadrant factor) if and only if `C = E` and `k` is
conjugated to a book basic germ.  In the book's conjugation with `C = E` the quadrant `C̃` is
forced to be `ℝⁿ`, again by Theorem 1.3.5. -/
theorem memoir_conj_iff (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U) {k : E 0 → F 0} :
    IsConjugateToBasicGermMemoir U k ↔ C = univ ∧ IsConjugateToBasicGerm U k := by
  refine ⟨fun h => ⟨h.eq_univ hU h0, h.isConjugateToBasicGerm⟩, ?_⟩
  rintro ⟨hC, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, hb, Bc, hCt, hU', hΨ, hψ0, hG,
    hh, hev⟩
  have hd := degIndex_zero_of_strongBundleIso hU hU' h0 hΨ hψ0
  rw [hC, TrivialBundle.univ_degIndex_eq_zero] at hd
  have h0' : (0 : (ScBanach.paramProd Pn W) 0) ∈ Ct ×ˢ univ :=
    hU'.subset_quadrant (hψ0 ▸ hΨ.toFun.base_mem h0)
  have hprod := eq_univ_of_degIndex_zero hU'.isPartialQuadrant h0' hd.symm
  have hCt' : Ct = univ := by
    ext a
    refine ⟨fun _ => mem_univ _, fun _ => ?_⟩
    have : ((a, 0) : Pn × W 0) ∈ Ct ×ˢ univ := hprod ▸ mem_univ _
    exact this.1
  subst hCt'
  exact ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, U', Ψ, Ψ', G, hb, Bc, hU', hΨ, hψ0, hG, hh, hev⟩

end Conj

/-! ### Proposition 2.42: fillings of `f + s` -/

section Prop242

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-- **Memoir Proposition 2.42, p. 41**, for the 2021 filling (Definition 3.1.4 in the germ
reading): if `(g, 0)` is a filled version of `(f, 0)` and `s` is a section of `K → O` with `s ∘ r`
sc-smooth on `U` (an sc⁺-section of `K → O` seen in `F`), then `(g + s ∘ r, 0)` is a filled version
of `(f + s, 0)`.  This is 2021 Lemma 3.1.20 (p. 99), `IsFillingGerm.add_section`. -/
theorem memoir_proposition_2_42 (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) {fb g s : E 0 → F 0} (hfg : IsFilling2021 hU hR h0 fb g)
    (hs : IsScSmooth U fun u => s (r R u)) (hsK : ∀ x ∈ r R '' U, (x, s x) ∈ R '' (U ×ˢ univ)) :
    IsFilling2021 hU hR h0 (fun x => fb x + s x) (fun y => g y + s (r R y)) := by
  have hsK' : ∀ x ∈ r R '' U, (x, s (r R x)) ∈ R '' (U ×ˢ univ) := fun x hx => by
    rw [r_eq_self hR hx]; exact hsK x hx
  have h := hfg.isFillingGerm.add_section hU hR h0 hs hsK'
  refine (isFilling2021_iff.2 ⟨hfg.r_zero, h.congr hU hR h0 (fun x hx => ?_) (fun y hy => ?_)⟩)
  · simp only [r_eq_self hR hx]
  · simp only [r_r hR hy]

end Prop242

/-! ### Definition 2.40 and Proposition 2.41: fillings and the filler -/

section Prop241

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-- **Memoir Definition 2.40, p. 39 (filling)**: the memoir's filling is the 2021 filling (2021
Definition 3.1.4, p. 91, germ reading, `r(0) = 0` assumed, `f(0) = 0` not required). -/
abbrev IsFillingMemoir (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) (fb g : E 0 → F 0) : Prop :=
  IsFilling2021 hU hR h0 fb g

/-- **Memoir Proposition 2.41, pp. 40–41 (Filler)**, with `f(0) = 0`: for a filling `g` of `f`
with derivative family `Dg`, `f'(0) = Dg(0)|_{T₀O} : Dr(0)E → ρ(0)F` satisfies (1) `f'(0)` onto iff
`Dg(0)` onto, and `ker f'(0) = ker Dg(0)` (every `w ∈ ker Dg(0)` lies in `T₀O`); (2) `f'(0)` is
Fredholm iff `Dg(0)` is, with the same index.  The book's Proposition 3.1.5 (2021 p. 91) states
(1) without the kernel identity, which is in the displayed discussion after Definition 3.1.4;
here it comes from the injectivity of `(1 − ρ(0))Dg(0)` on `ker Dr(0)`. -/
theorem memoir_proposition_2_41 (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) {fb g : E 0 → F 0} (hfg : IsFillingMemoir hU hR h0 fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) {G₁ : ScNbhdGerm E C} (hG : G₁.U 0 ⊆ U)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G₁ g Dg) :
    ∃ h1 : ∀ x, ρCLM hR h0 (Dg 0 (scDeriv U (r R) 0 x)) = Dg 0 (scDeriv U (r R) 0 x),
      ((Surjective (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1) ↔
          Surjective (Dg 0)) ∧
        ∀ w : E 0, Dg 0 w = 0 ↔ ∃ v : ↥(rangeS (scDeriv U (r R) 0)),
          fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1 v = 0 ∧ (v : E 0) = w) ∧
        (ContinuousLinearMap.IsFredholm
            (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1) ↔
          ContinuousLinearMap.IsFredholm (Dg 0)) ∧
        fredholmIndex (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1) =
          fredholmIndex (Dg 0) := by
  obtain ⟨h1, hsurj, hF, hind⟩ := proposition_3_1_5 hU hR h0 hfg hfb0 hfK hG hg
  have h0O : (0 : E 0) ∈ r R '' U := ⟨0, h0, hfg.r_zero⟩
  have hg0 : g 0 = 0 := by rw [← hfg.eq_on.self_of_nhds h0O, hfb0]
  obtain ⟨Φ, hΦ⟩ := hfg.isFillingGerm.exists_kerEquiv hU hR h0 hg0 h0O hg
  refine ⟨h1, ⟨hsurj, fun w => ⟨fun hw => ?_, ?_⟩⟩, hF, hind⟩
  · have hpw := fillerRestrict_mem_range_of (scDeriv_r_idem hU hR h0O) h1 Φ hΦ w
      (by rw [hw, map_zero, sub_zero])
    exact ⟨⟨w, ⟨w, hpw⟩⟩, Subtype.ext hw, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact congrArg Subtype.val hv

end Prop241

/-! ### Definitions 2.44, 2.45 and Theorem 2.46 -/

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open Polyfold.StrongBundle


variable (B) in
/-- **Memoir Definition 2.39, p. 39 (regularizing section)**: `x ∈ X_m` and `f(x) ∈ Y_{m,m+1}`
imply `x ∈ X_{m+1}` (the book's Definition 3.1.16 (2), 2021 p. 97). -/
def IsRegularizingMemoir (f : X → Y) : Prop :=
  ∀ m, ∀ x ∈ PX.levelSet m, f x ∈ B.doubleLevel m (m + 1) → x ∈ PX.levelSet (m + 1)

/-- **Memoir Definition 2.39, the observation after it**: if `f ∈ Γ(P)` is regularizing and
`s ∈ Γ⁺(P)`, then `f + s` is regularizing (the proof of the book's `regularizing_sectionAdd`). -/
theorem memoir_definition_2_39_add {s : X → Y} (hf : B.IsScSmoothSection f)
    (hreg : IsRegularizingMemoir B f) (hs : B.IsScPlusSection s) :
    IsRegularizingMemoir B (sectionAdd P f s) := by
  intro m x hx hfs
  have hfsec := hf.1
  refine hreg m x hx fun c hc hmem => ?_
  have hxV : x ∈ c.φ.source := by rw [c.source_eq, mem_preimage, hfsec x] at hmem; exact hmem
  have h1 := hfs c hc (c.mem_source_of_proj (by rw [(hfsec.sectionAdd hs.1) x]; exact hxV))
  refine ⟨?_, ?_⟩
  · rw [c.fst_apply (by rw [hfsec]; exact hxV), hfsec]
    exact (PX.mem_levelSet_iff c.isChart hxV).1 hx
  · have hsx := hs.snd_mem_range (B.isChart_of_mem hc) hxV hx
    have heq : (c (f x)).2 = (c (sectionAdd P f s x)).2 - (c (s x)).2 := by
      rw [sectionAdd_apply hfsec hs.1, c.snd_add hxV]
      change (c (f x)).2 = (c (f x)).2 + (c (s x)).2 - (c (s x)).2
      abel
    obtain ⟨a, ha⟩ := h1.2
    obtain ⟨b, hb⟩ := hsx
    exact ⟨a - b, by rw [map_sub, ha, hb, heq]⟩

variable (B) in
/-- **Memoir Definition 2.44, p. 42 (Fredholm germ)**, in the memoir's order of operations: `x₀`
is smooth and there are a strong bundle chart `c` centred at `x₀`, the principal part
`ŝ : E₀ → F₁` of a germ of an sc⁺-section `s` of `K → O` (`ŝ ∘ r` sc-smooth into `F¹` on `U`,
`(z, ŝ(z)) ∈ K` on `O`) with `s(x₀) = f(x₀)`, and a filled version `g` (2021 Definition 3.1.4) of
the push-forward `Φ_*(f − s)` which is equivalent to a memoir basic germ (Definition 2.43). -/
def IsFredholmGermMemoir (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (s : c.φ.model.E 0 → c.F 1) (g : c.φ.model.E 0 → c.F 0),
    IsScSmooth (F := c.F.shift) c.U (fun u => s (r c.R u)) ∧
    (∀ z ∈ c.φ.model.O, (z, c.F.toBase 1 (s z)) ∈ c.K) ∧
    c.F.toBase 1 (s 0) = c.principal f 0 ∧
    IsFilling2021 c.relOpen c.isRetraction h0 (fun z => c.principal f z - c.F.toBase 1 (s z)) g ∧
    IsConjugateToBasicGermMemoir c.U g

variable (B) in
/-- **Memoir Definition 2.45, p. 42 (polyfold Fredholm section)**: an sc-smooth section which is
regularizing (Definition 2.39) and a memoir Fredholm germ (Definition 2.44) at every smooth
point. -/
structure IsFredholmSectionMemoir (f : X → Y) : Prop where
  isScSmooth : B.IsScSmoothSection f
  regularizing : ∀ m, ∀ x ∈ PX.levelSet m, f x ∈ B.doubleLevel m (m + 1) → x ∈ PX.levelSet (m + 1)
  germ : ∀ x ∈ PX.smoothSet, IsFredholmGermMemoir B f x

/-- **Memoir Definition 2.44 ⟹ 2021 Definition 3.1.11 in a tame chart.**  From the memoir data
`(ŝ, g)` in a chart `c`: by Proposition 2.42, `g + ŝ ∘ r` fills `f̂`; the book's sc⁺-section is
`ŝ ∘ r`, with value `f̂(0) = g(0) + ŝ(0)` at `0`, and `(g + ŝ ∘ r) − ŝ ∘ r = g` is conjugated to a
basic germ.  The memoir conjugation forces `C = E` (`IsConjugateToBasicGermMemoir.eq_univ`), so
`c` is a tame chart (`isTame_of_eq_univ`). -/
theorem memoir_definition_2_44_isScFredholmGermTame2021 {x₀ : X}
    (h : IsFredholmGermMemoir B f x₀) : B.IsScFredholmGermTame2021 f x₀ := by
  obtain ⟨hxs, c, hc, hxV, hφ0, h0, s, g, hsm, hsK, hs0, hfill, hconj⟩ := h
  have hU := c.relOpen.isScDomain
  have hC : c.φ.model.C = univ := hconj.eq_univ c.relOpen h0
  have hsr : IsScSmooth c.U fun u => c.F.toBase 1 (s (r c.R u)) := hsm.toBase_shift hU
  have hsK' : ∀ x ∈ r c.R '' c.U, (x, c.F.toBase 1 (s x)) ∈ c.R '' (c.U ×ˢ univ) :=
    fun x hx => hsK x (c.r_image ▸ hx)
  have h42 := memoir_proposition_2_42 c.relOpen c.isRetraction h0 hfill hsr hsK'
  have hfill' : IsFilling2021 c.relOpen c.isRetraction h0 (c.principal f)
      (fun y => g y + c.F.toBase 1 (s (r c.R y))) := by
    refine isFilling2021_iff.2 ⟨h42.r_zero, h42.isFillingGerm.congr c.relOpen c.isRetraction h0
      (fun x _ => by simp) (fun y _ => rfl)⟩
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := zero_mem_O_of_chart hxV hφ0
  have hg0 : g 0 = 0 := by
    have := hfill.eq_on.self_of_nhds h0O
    rw [← this, hs0, sub_self]
  refine ⟨hxs, c, ⟨hc, isTame_of_eq_univ _ hC⟩, hxV, hφ0, h0, _, fun u => s (r c.R u), hfill',
    ⟨ScNbhdGerm.ofSet c.relOpen.relOpen h0, fun _ hu => hu,
      hsm.isScSmoothGerm c.isQuadrantLike c.relOpen.relOpen h0⟩, ?_, ?_⟩
  · simp only [hg0, zero_add]
  · exact hconj.isConjugateToBasicGerm.congr fun u _ => by simp


/-- **Memoir Definition 2.44, the remark after it**: if `(f, x)` is a Fredholm germ and `s₀` is an
sc⁺-section, then `(f + s₀, x)` is a Fredholm germ, with the same filled version: the data
`(ŝ, g)` of `f` give the data `(ŝ + ŝ₀, g)` of `f + s₀`, since
`(f + s₀) − (s + s₀) = f − s`. -/
theorem memoir_definition_2_44_add {s₀ : X → Y} {x₀ : X} (hfs : IsSection P f)
    (h : IsFredholmGermMemoir B f x₀) (hs₀ : B.IsScPlusSection s₀) :
    IsFredholmGermMemoir B (sectionAdd P f s₀) x₀ := by
  obtain ⟨hxs, c, hc, hxV, hφ0, h0, s, g, hsm, hsK, hs0, hfill, hconj⟩ := h
  have hU := c.relOpen.isScDomain
  have hlift : IsScSmooth (F := c.F.shift) c.U fun u => c.principalLift s₀ (r c.R u) :=
    (((hs₀.isScSmoothRetractMap_one hc).comp_isScSmooth (c.isRetraction.baseRetraction c.relOpen)
      c.base_retract).snd hU).congr hU fun _ _ => rfl
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := c.r_image ▸ zero_mem_O_of_chart hxV hφ0
  refine ⟨hxs, c, hc, hxV, hφ0, h0, fun z => s z + c.principalLift s₀ z, g, hsm.add hU hlift,
    fun z hz => ?_, ?_, ?_, hconj⟩
  · rw [map_add]
    refine c.add_mem_K (hsK z hz) ?_
    rw [hs₀.toBase_principalLift hc hz]
    exact hs₀.mem_K hc hz
  · rw [map_add, hs₀.toBase_principalLift hc h0O, c.principal_sectionAdd hfs hs₀.1 h0O, hs0]
  · refine isFilling2021_iff.2 ⟨hfill.r_zero, hfill.isFillingGerm.congr c.relOpen c.isRetraction h0
      (fun z hz => ?_) (fun y _ => rfl)⟩
    have hz' : z ∈ c.φ.model.O := c.r_image ▸ hz
    rw [map_add, hs₀.toBase_principalLift hc hz', c.principal_sectionAdd hfs hs₀.1 hz']
    abel

/-- **A memoir Fredholm germ at `x₀` forces `d_X(x₀) = 0`**: in the chart of the germ data
`C = E`, so `d_X(x₀) ≤ d_C(φ(x₀)) = 0`. -/
theorem IsFredholmGermMemoir.degIndex_eq_zero {x₀ : X} (h : IsFredholmGermMemoir B f x₀) :
    PX.degIndex x₀ = 0 := by
  obtain ⟨-, c, -, hxV, hφ0, h0, s, g, -, -, -, -, hconj⟩ := h
  have hC : c.φ.model.C = univ := hconj.eq_univ c.relOpen h0
  have hle := PX.degIndex_le c.isChart hxV
  rw [MPolyfold.chartDegIndex, hφ0, hC, TrivialBundle.univ_degIndex_eq_zero] at hle
  exact Nat.le_zero.1 hle

/-- **A memoir Fredholm section is a 2021 sc-Fredholm section with tame germ data** (Definitions
2.45 ⟹ 3.1.16 with Definition 3.6.3 in tame charts). -/
theorem IsFredholmSectionMemoir.isScFredholmSectionTame2021 (hf : IsFredholmSectionMemoir B f) :
    B.IsScFredholmSectionTame2021 f where
  isScSmooth := hf.isScSmooth
  regularizing := hf.regularizing
  germ x hx := (memoir_definition_2_44_isScFredholmGermTame2021 (hf.germ x hx)).isScFredholmGerm2021
  germTame x hx := memoir_definition_2_44_isScFredholmGermTame2021 (hf.germ x hx)

/-- A zero of a memoir Fredholm section is a smooth point (regularity). -/
theorem IsFredholmSectionMemoir.mem_smoothSet_of_isZeroAt (hf : IsFredholmSectionMemoir B f)
    {x : X} (hx : IsZeroAt P f x) : x ∈ PX.smoothSet :=
  (isScFredholmSectionTame2021_iff.1 hf.isScFredholmSectionTame2021).mem_smoothSet_of_isZeroAt hx


/-- **Memoir, the statement after Definition 2.45 (p. 42)**: if `f` is a memoir Fredholm section
and `f(x₀) = 0`, then `f'(x₀)` is a linear sc-Fredholm operator: in every strong bundle chart around
`x₀`, at the level-`1` point `z` over `φ(x₀)`, `Lin(z) : T_zO → K_z` is the restriction of an
sc-operator to sc-subspaces and is sc-Fredholm (2021 Theorem 3.1.22, first conclusion, and
Proposition 3.6.5). -/
theorem memoir_linearization_isScFredholm (hf : IsFredholmSectionMemoir B f) {x₀ : X}
    (hx₀ : IsZeroAt P f x₀) :
    ∀ c : StrongBundleChart PX P, B.IsChart c → x₀ ∈ c.φ.source →
      ∀ (z : c.φ.model.E 1) (_ : c.φ.model.E.toBase 1 z = c.φ x₀)
        (hzU : c.φ.model.E.toBase 1 z ∈ c.U),
        ∃ (hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z))
          (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
          (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
          (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
            hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU)),
          (∀ x : (c.φ.model.E.ofSubspace hT) 0,
            ((hD.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) =
              linAt c.U c.R (c.principal f) z ⟨x.1, x.2⟩) ∧
          IsScFredholm (hD.toScOperator.restrict hT hK hTK) := by
  have hT := isScFredholmSectionTame2021_iff.1 hf.isScFredholmSectionTame2021
  intro c hc hxV z hz hzU
  obtain ⟨hD, hT', hK, hTK, h1, h2, -⟩ :=
    StrongBundle.linAt_isScFredholm hT.toIsScFredholmSection hx₀ hc hxV hz hzU
  exact ⟨hD, hT', hK, hTK, h1, h2⟩

/-- **Memoir Theorem 2.46, pp. 42–43 (implicit function theorem), as printed.**  Let `f` be a
memoir Fredholm section (Definition 2.45), `f(x₀) = 0` and `f'(x₀)` onto (`IsLinSurjAt`).  Then
there are an open `U ∋ x₀` and `d` such that `S_U = {y ∈ U | f(y) = 0}` lies in `X_∞`, is a
sub-M-polyfold of `X` whose induced structure is that of a `d`-dimensional manifold without
boundary, and `f'(y)` is onto of index `d` at every `y ∈ S_U`.

No hypothesis `d_X ≡ 0` (2021 Theorem 3.1.22, p. 100) and no good position (Theorem 3.1.26,
p. 103) is needed: a memoir Fredholm germ at `y` gives `d_X(y) = 0` and a tame chart
(`memoir_definition_2_44_isScFredholmGermTame2021`), so surjectivity is good position at `x₀`
(`isGoodPositionGerm_of_isLinSurjAt`), Theorem 3.1.26 gives the manifold with corners, and its
boundary is empty since `S_U` consists of smooth points, at which `d_X = 0` (Lemma 2.4.6). -/
theorem memoir_theorem_2_46 (hf : IsFredholmSectionMemoir B f) {x₀ : X} (hx₀ : IsZeroAt P f x₀)
    (hsurj : B.IsLinSurjAt f x₀) :
    ∃ (U : Set X) (d : ℕ), IsOpen U ∧ x₀ ∈ U ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet ∧ B.IsSurjLinOfIndex f y d) ∧
      ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d ∧
          (MPolyfold.subPolyfold hsub).IsWithoutBoundary := by
  have hT := isScFredholmSectionTame2021_iff.1 hf.isScFredholmSectionTame2021
  have hx₀s := hf.mem_smoothSet_of_isZeroAt hx₀
  have hg := isGoodPositionGerm_of_isLinSurjAt hT hx₀ (hf.germ x₀ hx₀s).degIndex_eq_zero hsurj
  obtain ⟨U, d, hUo, hxU, hgood, hsm, hsub, -, hman⟩ := theorem_3_1_26_index hT hx₀ hg
  have := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
  refine ⟨U, d, hUo, hxU, fun y hy hy0 => ⟨hsm y hy hy0, (hgood y hy hy0).2⟩, hsub, hman,
    fun y => ?_⟩
  have h1 := lemma_2_4_6 hsub y
  rw [(hf.germ y.1 (hsm y.1 y.2.1 y.2.2)).degIndex_eq_zero] at h1
  exact Nat.le_zero.1 h1

end Bundle

/-! ### The hypotheses of Theorem 2.46 are satisfiable -/

section Witness

open TrivialBundle

variable {n k : ℕ} {φ : (Fin n → ℝ) → (Fin k → ℝ)}

/-- **The graph section of a `C^∞` map `φ : ℝⁿ → ℝᵏ` has a memoir Fredholm germ** (Definition
2.44) at every `x₀`: in the translation chart centred at `x₀` (`U = ℝⁿ`, `R = id`), `ŝ ≡ φ(x₀)`,
and the filled version of `Φ_*(f − s)` is `u ↦ φ(u + x₀) − φ(x₀)` itself, conjugated to a memoir
basic germ (`W = 0`, `B = 0`). -/
theorem isFredholmGermMemoir_graphSection (hφ : ContDiff ℝ ∞ φ) (x₀ : Fin n → ℝ) :
    IsFredholmGermMemoir (bundle n k) (graphSection φ) x₀ := by
  obtain ⟨hfill, hs, hs0, hconj⟩ := germData_graphSection (k := k) hφ x₀
  have h0O : (0 : (chart (k := k) x₀).φ.model.E 0) ∈ r (chart (k := k) x₀).R '' (chart x₀).U :=
    ⟨0, mem_univ _, rfl⟩
  have hneg : IsScSmooth (E := rnSc n) (F := rnSc k) univ fun _ => -φ x₀ :=
    isScSmooth_of_bijective_toBase (bijective_toBase_const _) (bijective_toBase_const _)
      (isScDomain_univ _) contDiffOn_const
  have h42 := memoir_proposition_2_42 (chart (k := k) x₀).relOpen (chart x₀).isRetraction
    (mem_univ 0) (hfill.isFilling2021 h0O) (s := fun _ => -φ x₀) hneg
    (fun z _ => ⟨(z, -φ x₀), ⟨mem_univ _, mem_univ _⟩, rfl⟩)
  have hι : ∀ v : Fin k → ℝ, (rnSc k).toBase 1 v = v := ScBanach.const_toBase _ 1
  refine ⟨by rw [rnPolyfold_smoothSet]; exact mem_univ x₀, chart x₀, isChart_chart x₀,
    mem_univ x₀, sub_self x₀, mem_univ 0, fun _ => φ x₀, fun u => loc φ x₀ u - φ x₀, hs,
    fun z _ => ⟨(z, _), ⟨mem_univ _, mem_univ _⟩, rfl⟩, hs0, ?_, ?_⟩
  · refine isFilling2021_iff.2 ⟨h42.r_zero, h42.isFillingGerm.congr (chart (k := k) x₀).relOpen
      (chart x₀).isRetraction (mem_univ 0) (fun z _ => ?_) (fun y _ => ?_)⟩
    · simp only [sub_eq_add_neg]; exact congrArg _ (congrArg _ (hι _)).symm
    · rfl
  · exact (memoir_conj_iff (chart (k := k) x₀).relOpen (mem_univ 0)).2 ⟨rfl, hconj⟩

/-- **The hypotheses of Theorem 2.46 are met**: the graph section of a `C^∞` map `φ : ℝⁿ → ℝᵏ` is
a memoir Fredholm section (Definition 2.45) of the trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ`. -/
theorem memoir_theorem_2_46_hypotheses (hφ : ContDiff ℝ ∞ φ) :
    IsFredholmSectionMemoir (bundle n k) (graphSection φ) where
  isScSmooth := isScSmoothSection_graphSection hφ
  regularizing m x _ _ := by rw [rnPolyfold_levelSet]; exact mem_univ x
  germ x _ := isFredholmGermMemoir_graphSection hφ x

end Witness

end GWMemoir
