import Polyfold.Chapter7.NonVacuity
import Polyfold.Chapter7.LocalDiffeo
import Polyfold.Chapter7.OrbitTopology
import Polyfold.Chapter6.OrientableNbhd

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 7, §7.5 "Paracompact Orbit Spaces", the sentence after **Definition 7.5.1**
(p. 340; 2017: Definition 7.15, p. 249): "It is presently not known whether the property (5) is a
consequence of the properties (1)–(4)."  Numbers and pages are the 2021 text's, the 2017 ones in
parentheses.  The project records this open question of the text without a gap (Findings,
Chapter 7, item 113).

# Property (5) does not follow from properties (1)–(4): an ep-groupoid with a non-paracompact
orbit space

## The text, paraphrased

(Definition 7.1.3, pp. 288–289) An ep-groupoid is a groupoid with M-polyfold structures on the
objects and the morphisms such that (1) `s, t` are local sc-diffeomorphisms, (2) `u, ι` are
sc-smooth, (3) every `x` has an open `V(x)` with `t : s⁻¹(cl V(x)) → X` proper, (4) `m` is
sc-smooth.  (Definition 7.5.1, p. 340) An ep-groupoid has paracompact orbit space if, in
addition, (5) `|X|` is paracompact.  (p. 340) "We have seen in Lemma 7.3.4 an ep-groupoid `X`
always has an Hausdorff orbit space `|X|`.  It is presently not known whether the property (5)
is a consequence of the properties (1)–(4).  If `X` has a second countable topology we have
already seen that (1)–(4) imply (5)."

## The answer

**No.**  The orbit space of an ep-groupoid is a Hausdorff space that is locally the quotient of
an M-polyfold by a finite group, hence locally metrizable; a non-metrizable manifold is such a
space, and it is the orbit space of the Čech groupoid of an atlas.  The example formalized here
is the Čech groupoid of the atlas of a **Prüfer-type surface** (R. Calabi–M. Rosenlicht,
*Complex analytic manifolds without countable base*, Proc. AMS 4 (1953), after Prüfer; also
T. Radó, 1925): the charts are the planes `ℝ²`, one for each `a` in an uncountable index set
`ι ⊂ ℝ`, and the chart `a` is glued to the chart `b` along the open upper half-planes by
`(u, y) ↦ (u + (a − b)/y, y)`.  In the canonical coordinates `(X, l)` with `y = e^l`,
`X = u + a e^{−l}` the gluing is the identity, so the quotient `Z` is `H ∪ ⨆_a L_a`, the open
upper half-plane `H` together with one closed lower half-plane `L_a = {y ≤ 0}` for each `a`,
every `L_a` attached to `H` along its own copy of the real axis.

* The object space `X = ι × ℝ²` and the morphism space `𝐗 = (ι ⊕ {(a, b) | a ≠ b}) × ℝ²` are
  disjoint unions of copies of `ℝ²` over discrete sets, hence M-polyfolds (`discretePolyfold`
  times `rnPolyfold 2`), metrizable and paracompact.  The sheet `inl a` carries the units of the
  chart `a`; the sheet `inr (a, b)` carries the morphisms from `(a, chartPt (c a) p)` to
  `(b, chartPt (c b) p)`, `p` the canonical coordinates, `chartPt a (X, l) = (X − a e^{−l}, e^l)`.
* The groupoid has at most one morphism between any two objects (`mk x y`), so composition,
  units and inverses are `mk (s ψ) (t φ)`, `mk x x`, `mk (t φ) (s φ)`, and the groupoid laws
  reduce to `mk (s φ) (t φ) = φ` and `s (mk x y) = x`, `t (mk x y) = y` for isomorphic `x, y`
  (`Rel`).
* **(1)** `s` and `t` restricted to a sheet are the identity (units) or `p ↦ chartPt a p`, a
  diffeomorphism of `ℝ²` onto the open upper half-plane with inverse `canon a`; **(2)**, **(4)**
  are checked sheet by sheet (`isScSmoothOn_prod_discrete_iff`, the sheet form
  `IsScSmoothCompSheet` of (4)); **(3)** with `V(x) = {a} × B(q, 1)`: a morphism over `cl V(x)`
  with target in a compact `K` lies in one of finitely many sheets, and on the sheet `(a, b)`,
  `a ≠ b`, both `e^l` and `(a − b) e^{−l}` are bounded, so the canonical coordinates are bounded.
* **Not (5)**: the points `d_a = |(a, 0)|` are the only points of their orbits; the open sets
  `W_a = |X| ∖ {d_b | b ≠ a}` cover `|X|`, and `d_a` lies in `W_b` only for `b = a`.  A locally
  finite open refinement `(t_β)` therefore has a member `t_{β(a)} ∋ d_a` for every `a`, with
  `a ↦ β(a)` injective.  Every neighbourhood of `d_a` contains `|(a, (0, y))|` for small `y > 0`,
  which is `|(a₀, q)|` for a point `q` of the fixed chart `a₀`, hence also a point `|(a₀, r)|`
  with `r ∈ ℚ²`.  Local finiteness at the countably many points `|(a₀, r)|` leaves room for only
  countably many `β(a)`, so `ι` would be countable.  With `ι = ℝ` (discrete) this is absurd.

## What is formalized (namespace `Polyfold.EpGroupoid.Examples.Pruefer`)

* The coordinate changes `chartPt`, `canon` and their calculus (`canon_chartPt`,
  `chartPt_canon`, `contDiff_chartPt`, `contDiffOn_canon`); the general lemma
  `Polyfold.isScSmoothOn_rn_rn_of_contDiffOn` (a `C^∞` map on an open subset of `ℝᵐ` is sc-smooth
  there).
* `src`, `tgt`, `mk`, `Rel`, `rel_src_tgt`, `src_mk`, `tgt_mk`, `mk_src_tgt`, the groupoid
  `groupoidStr ι c` and `isomorphic_iff_rel`.
* The M-polyfolds `PObj`, `PMor`; `isScDiffeoOn_inl_sheet`, `isScDiffeoOn_inr_sheet`,
  `isLocalScDiffeo_src`, `isLocalScDiffeo_tgt`, `isScSmoothMap_unit`, `isScSmoothMap_inv`,
  `isScSmoothCompSheet`, `exists_isProperMap`; **the ep-groupoid** `epGroupoid ι c hc`
  (Definition 7.1.3 (1)–(4)) for every discrete `ι` and injective `c : ι → ℝ`.
* `exists_rat_mem_of_mem` (the density step) and **`not_paracompactSpace_orbitSpace`**: for
  uncountable `ι` the orbit space is not paracompact.
* `DiscR` (`ℝ` with the discrete topology), `pruefer : EpGroupoid (DiscR × ℝ²) (… × ℝ²)`,
  `pruefer_not_hasParacompactOrbitSpace` (**not (5)**), `t2Space_orbitSpace_pruefer` (Lemma 7.3.4
  holds, as the text says), and the summary
  **`exists_epGroupoid_not_hasParacompactOrbitSpace`**: there is an ep-groupoid without
  paracompact orbit space, so property (5) is not a consequence of properties (1)–(4).

## Reading

* The text's "(1)–(4)" are the four conditions of Definition 7.1.3 as formalized in
  `EpGroupoid` (`EpGroupoid.lean`), including the existential reading of (3) and the sheet
  form of (4); the M-polyfold structures of the object and morphism spaces are included in "(1)",
  and, as the text and `Remark 7.5.2` make explicit, no second countability is assumed.
* The example is consistent with the text's own remark: its object space is not second
  countable (it has uncountably many components), which is exactly what the text's proof of (5)
  from second countability uses.
* The example is finite-dimensional, without boundary, and has at most one morphism between any
  two objects (it is the groupoid of an equivalence relation), so every object is regular;
  nothing in the question asks for more.  Regularity, effectiveness and tameness are not needed
  here and are not proved.
* No possible misprint was found in the passages used here.
-/

open Set Function Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

/-- A `C^∞` map on an open `W ⊆ ℝᵐ` is sc-smooth on `W` as a map of the M-polyfolds `ℝᵐ → ℝⁿ`
(the open-set form of `isScSmoothMap_rn_rn_of_contDiff`). -/
theorem isScSmoothOn_rn_rn_of_contDiffOn {m n : ℕ} {σ : (Fin m → ℝ) → Fin n → ℝ}
    {W : Set (Fin m → ℝ)} (hW : IsOpen W) (hσ : ContDiffOn ℝ ∞ σ W) :
    (rnPolyfold m).IsScSmoothOn (rnPolyfold n) σ W := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts hW hσ.continuousOn fun x hx => ⟨rnChart m 0,
    rnChart n 0, W, isChart_rnChart 0, isChart_rnChart 0, hW, hx, subset_inter subset_rfl
    (subset_univ _), mapsTo_univ _ _, ?_⟩
  have himg : (⇑(rnChart m 0).toPartialEquiv) '' W = W := by
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      show s - 0 ∈ W
      rwa [sub_zero]
    · intro hr
      exact ⟨r, hr, sub_zero r⟩
  rw [himg, rnChart_model_O]
  change IsScSmoothRetractMap (rnSc m) univ W (rnSc n) univ univ (fun r => σ (r + 0) - 0)
  have hU : IsRelOpenInQuadrant (rnSc m) univ W :=
    ⟨isPartialQuadrant_univ _, W, hW, (inter_univ _).symm⟩
  refine (isScSmoothRetractMap_iff_exists hU.isScRetract).2
    ⟨mapsTo_univ _ _, ScRetraction.id hU, image_id W, ?_⟩
  have hσ' : ContDiffOn ℝ ∞ (fun r : Fin m → ℝ => σ (r + 0) - 0) W :=
    (hσ.comp (contDiff_id.add contDiff_const).contDiffOn fun r hr => by simpa using hr).sub
      contDiffOn_const
  exact IsScSmooth.of_contDiffOn_finiteDimensional (V := Fin n → ℝ) hU.isScDomain
    (f := (fun r : Fin m → ℝ => σ (r + 0) - 0) ∘ (ScRetraction.id hU).toFun) hσ'

namespace EpGroupoid

namespace Examples

namespace Pruefer

/-! ### The coordinate changes -/

/-- The plane `ℝ²`. -/
abbrev E2 := Fin 2 → ℝ

/-- The chart-`a` coordinates `(X − a e^{−l}, e^l)` of the canonical point `(X, l)`. -/
def chartPt (a : ℝ) (p : E2) : E2 := ![p 0 - a * Real.exp (-(p 1)), Real.exp (p 1)]

/-- The canonical coordinates `(u + a / y, log y)` of the chart-`a` point `(u, y)`, `y > 0`. -/
def canon (a : ℝ) (q : E2) : E2 := ![q 0 + a / q 1, Real.log (q 1)]

@[simp] lemma chartPt_zero (a : ℝ) (p : E2) : chartPt a p 0 = p 0 - a * Real.exp (-(p 1)) := rfl

@[simp] lemma chartPt_one (a : ℝ) (p : E2) : chartPt a p 1 = Real.exp (p 1) := rfl

@[simp] lemma canon_zero (a : ℝ) (q : E2) : canon a q 0 = q 0 + a / q 1 := rfl

@[simp] lemma canon_one (a : ℝ) (q : E2) : canon a q 1 = Real.log (q 1) := rfl

lemma chartPt_one_pos (a : ℝ) (p : E2) : 0 < chartPt a p 1 := Real.exp_pos _

/-- `E2` is determined by its two coordinates. -/
lemma E2.ext {p q : E2} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma canon_chartPt (a : ℝ) (p : E2) : canon a (chartPt a p) = p := by
  refine E2.ext ?_ ?_
  · rw [canon_zero, chartPt_zero, chartPt_one, Real.exp_neg, div_eq_mul_inv]
    ring
  · rw [canon_one, chartPt_one, Real.log_exp]

lemma chartPt_canon (a : ℝ) {q : E2} (hq : 0 < q 1) : chartPt a (canon a q) = q := by
  refine E2.ext ?_ ?_
  · rw [chartPt_zero, canon_zero, canon_one, Real.exp_neg, Real.exp_log hq, div_eq_mul_inv]
    ring
  · rw [chartPt_one, canon_one, Real.exp_log hq]

lemma chartPt_injective (a : ℝ) : Injective (chartPt a) := fun p p' h => by
  rw [← canon_chartPt a p, h, canon_chartPt]

lemma canon_injOn (a : ℝ) {q q' : E2} (hq : 0 < q 1) (hq' : 0 < q' 1)
    (h : canon a q = canon a q') : q = q' := by
  rw [← chartPt_canon a hq, h, chartPt_canon a hq']

lemma contDiff_chartPt (a : ℝ) : ContDiff ℝ ∞ (chartPt a) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ fun p : E2 => p 0 - a * Real.exp (-(p 1))
    fun_prop
  · change ContDiff ℝ ∞ fun p : E2 => Real.exp (p 1)
    fun_prop

/-- The open upper half-plane `{y > 0}`. -/
lemma isOpen_pos : IsOpen {q : E2 | 0 < q 1} := isOpen_lt continuous_const (continuous_apply 1)

lemma contDiffOn_canon (a : ℝ) : ContDiffOn ℝ ∞ (canon a) {q : E2 | 0 < q 1} := by
  intro q hq
  have hq' : (0 : ℝ) < q 1 := hq
  apply ContDiffAt.contDiffWithinAt
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun q : E2 => q 0 + a / q 1) q
    exact (contDiff_apply ℝ ℝ 0).contDiffAt.add
      (contDiffAt_const.div (contDiff_apply ℝ ℝ 1).contDiffAt hq'.ne')
  · change ContDiffAt ℝ ∞ (fun q : E2 => Real.log (q 1)) q
    exact (Real.contDiffAt_log.2 hq'.ne').comp q (contDiff_apply ℝ ℝ 1).contDiffAt

theorem isScSmoothMap_chartPt (a : ℝ) :
    (rnPolyfold 2).IsScSmoothMap (rnPolyfold 2) (chartPt a) :=
  isScSmoothMap_rn_rn_of_contDiff (contDiff_chartPt a)

theorem isScSmoothOn_canon (a : ℝ) :
    (rnPolyfold 2).IsScSmoothOn (rnPolyfold 2) (canon a) {q : E2 | 0 < q 1} :=
  isScSmoothOn_rn_rn_of_contDiffOn isOpen_pos (contDiffOn_canon a)

/-! ### The groupoid -/

variable (ι : Type)

/-- The index set of the sheets of the morphism space: `inl a` the units of the chart `a`,
`inr (a, b)`, `a ≠ b`, the morphisms from the chart `a` to the chart `b`. -/
abbrev MorIdx : Type := ι ⊕ {q : ι × ι // q.1 ≠ q.2}

variable (c : ι → ℝ)

/-- The source: `(a, q)` on the unit sheet, `(a, chartPt (c a) p)` on the sheet `(a, b)`. -/
def src : MorIdx ι × E2 → ι × E2
  | (Sum.inl a, q) => (a, q)
  | (Sum.inr ⟨⟨a, _⟩, _⟩, p) => (a, chartPt (c a) p)

/-- The target: `(a, q)` on the unit sheet, `(b, chartPt (c b) p)` on the sheet `(a, b)`. -/
def tgt : MorIdx ι × E2 → ι × E2
  | (Sum.inl a, q) => (a, q)
  | (Sum.inr ⟨⟨_, b⟩, _⟩, p) => (b, chartPt (c b) p)

open Classical in
/-- The unique candidate for a morphism `x → y`: the unit if the charts agree, otherwise the
point of the sheet `(x.1, y.1)` with the canonical coordinates of `x`. -/
def mk (x y : ι × E2) : MorIdx ι × E2 :=
  if h : x.1 = y.1 then (Sum.inl x.1, x.2) else (Sum.inr ⟨(x.1, y.1), h⟩, canon (c x.1) x.2)

/-- Two objects are related if they are equal or both lie in the upper half-plane with the
same canonical coordinates. -/
def Rel (x y : ι × E2) : Prop :=
  x = y ∨ (0 < x.2 1 ∧ 0 < y.2 1 ∧ canon (c x.1) x.2 = canon (c y.1) y.2)

variable {ι c}

@[simp] lemma src_inl (a : ι) (q : E2) : src ι c (Sum.inl a, q) = (a, q) := rfl

@[simp] lemma src_inr (i : {q : ι × ι // q.1 ≠ q.2}) (p : E2) :
    src ι c (Sum.inr i, p) = (i.1.1, chartPt (c i.1.1) p) := by
  obtain ⟨⟨a, b⟩, h⟩ := i
  rfl

@[simp] lemma tgt_inl (a : ι) (q : E2) : tgt ι c (Sum.inl a, q) = (a, q) := rfl

@[simp] lemma tgt_inr (i : {q : ι × ι // q.1 ≠ q.2}) (p : E2) :
    tgt ι c (Sum.inr i, p) = (i.1.2, chartPt (c i.1.2) p) := by
  obtain ⟨⟨a, b⟩, h⟩ := i
  rfl

lemma mk_of_eq {x y : ι × E2} (h : x.1 = y.1) : mk ι c x y = (Sum.inl x.1, x.2) := dif_pos h

lemma mk_of_ne {x y : ι × E2} (h : x.1 ≠ y.1) :
    mk ι c x y = (Sum.inr ⟨(x.1, y.1), h⟩, canon (c x.1) x.2) := dif_neg h

lemma mk_self (x : ι × E2) : mk ι c x x = (Sum.inl x.1, x.2) := mk_of_eq rfl

lemma rel_refl (x : ι × E2) : Rel ι c x x := Or.inl rfl

lemma Rel.symm {x y : ι × E2} (h : Rel ι c x y) : Rel ι c y x := by
  rcases h with rfl | ⟨hx, hy, h⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hy, hx, h.symm⟩

lemma Rel.trans {x y z : ι × E2} (hxy : Rel ι c x y) (hyz : Rel ι c y z) : Rel ι c x z := by
  rcases hxy with rfl | ⟨hx, hy, hxy⟩
  · exact hyz
  rcases hyz with rfl | ⟨-, hz, hyz⟩
  · exact Or.inr ⟨hx, hy, hxy⟩
  · exact Or.inr ⟨hx, hz, hxy.trans hyz⟩

/-- A related pair with different charts lies in the upper half-plane. -/
lemma Rel.pos_of_ne {x y : ι × E2} (h : Rel ι c x y) (hne : x.1 ≠ y.1) :
    0 < x.2 1 ∧ 0 < y.2 1 ∧ canon (c x.1) x.2 = canon (c y.1) y.2 := by
  rcases h with rfl | h
  · exact absurd rfl hne
  · exact h

lemma rel_src_tgt (φ : MorIdx ι × E2) : Rel ι c (src ι c φ) (tgt ι c φ) := by
  obtain ⟨i | ⟨⟨a, b⟩, h⟩, p⟩ := φ
  · exact Or.inl rfl
  · rw [src_inr, tgt_inr]
    exact Or.inr ⟨chartPt_one_pos (c a) p, chartPt_one_pos (c b) p, by
      rw [canon_chartPt, canon_chartPt]⟩

lemma src_mk {x y : ι × E2} (h : Rel ι c x y) : src ι c (mk ι c x y) = x := by
  by_cases hxy : x.1 = y.1
  · rw [mk_of_eq hxy, src_inl]
  · rw [mk_of_ne hxy, src_inr, chartPt_canon _ (h.pos_of_ne hxy).1]

lemma tgt_mk {x y : ι × E2} (h : Rel ι c x y) : tgt ι c (mk ι c x y) = y := by
  by_cases hxy : x.1 = y.1
  · rw [mk_of_eq hxy, tgt_inl]
    rcases h with rfl | ⟨hx, hy, h⟩
    · rfl
    · rw [hxy] at h
      exact Prod.ext hxy (canon_injOn _ hx hy h)
  · obtain ⟨-, hy, h⟩ := h.pos_of_ne hxy
    rw [mk_of_ne hxy, tgt_inr, h, chartPt_canon _ hy]

lemma mk_src_tgt (φ : MorIdx ι × E2) : mk ι c (src ι c φ) (tgt ι c φ) = φ := by
  obtain ⟨i | ⟨⟨a, b⟩, h⟩, p⟩ := φ
  · exact mk_self _
  · rw [src_inr, tgt_inr, mk_of_ne h, canon_chartPt]

variable (ι c) in
/-- **The Čech groupoid of the Prüfer atlas**: composition `φ ∘ ψ = mk (s ψ) (t φ)`, units
`mk x x`, inverses `mk (t φ) (s φ)`. -/
def groupoidStr : GroupoidStr (ι × E2) (MorIdx ι × E2) where
  src := src ι c
  tgt := tgt ι c
  comp φ ψ := mk ι c (src ι c ψ) (tgt ι c φ)
  unit x := mk ι c x x
  inv φ := mk ι c (tgt ι c φ) (src ι c φ)
  src_comp φ ψ h := src_mk ((rel_src_tgt ψ).trans (h ▸ rel_src_tgt φ))
  tgt_comp φ ψ h := tgt_mk ((rel_src_tgt ψ).trans (h ▸ rel_src_tgt φ))
  comp_assoc φ ψ χ h₁ h₂ := by
    rw [tgt_mk ((rel_src_tgt ψ).trans (h₁ ▸ rel_src_tgt φ)),
      src_mk ((rel_src_tgt χ).trans (h₂ ▸ rel_src_tgt ψ))]
  src_unit x := src_mk (rel_refl x)
  tgt_unit x := tgt_mk (rel_refl x)
  comp_unit φ := by rw [src_mk (rel_refl _), mk_src_tgt]
  unit_comp φ := by rw [tgt_mk (rel_refl _), mk_src_tgt]
  src_inv φ := src_mk (rel_src_tgt φ).symm
  tgt_inv φ := tgt_mk (rel_src_tgt φ).symm
  comp_inv φ := by rw [src_mk (rel_src_tgt φ).symm]
  inv_comp φ := by rw [tgt_mk (rel_src_tgt φ).symm]

/-- Isomorphic objects are the related ones. -/
theorem isomorphic_iff_rel {x y : ι × E2} : (groupoidStr ι c).Isomorphic x y ↔ Rel ι c x y := by
  constructor
  · rintro ⟨φ, rfl, rfl⟩
    exact rel_src_tgt φ
  · intro h
    exact ⟨mk ι c x y, src_mk h, tgt_mk h⟩

theorem π_eq_π_iff_rel {x y : ι × E2} :
    (groupoidStr ι c).π x = (groupoidStr ι c).π y ↔ Rel ι c x y :=
  (groupoidStr ι c).π_eq_π_iff.trans isomorphic_iff_rel

/-- An object on the real axis `y = 0` is the only point of its orbit. -/
theorem rel_axis_iff {x : ι × E2} {b : ι} : Rel ι c x (b, 0) ↔ x = (b, 0) := by
  refine ⟨fun h => ?_, fun h => h ▸ rel_refl _⟩
  rcases h with h | ⟨-, h0, -⟩
  · exact h
  · exact absurd h0 (lt_irrefl _)

/-! ### The M-polyfold structures -/

variable [TopologicalSpace ι] [DiscreteTopology ι]

instance : ParacompactSpace (ι × E2) := paracompactSpace_of_metrizableSpace _

instance : ParacompactSpace (MorIdx ι × E2) := paracompactSpace_of_metrizableSpace _

variable (ι) in
/-- The object M-polyfold `ι × ℝ²`: `#ι` copies of the plane. -/
abbrev PObj : MPolyfold (ι × E2) := (discretePolyfold ι).prod (rnPolyfold 2)

variable (ι) in
/-- The morphism M-polyfold `(ι ⊕ {(a, b) | a ≠ b}) × ℝ²`. -/
abbrev PMor : MPolyfold (MorIdx ι × E2) := (discretePolyfold (MorIdx ι)).prod (rnPolyfold 2)

/-- A map which is `(inl a, q) ↦ (a, q)` on the unit sheet of `a` is an sc-diffeomorphism from
that sheet onto `{a} × ℝ²`. -/
theorem isScDiffeoOn_inl_sheet (F : MorIdx ι × E2 → ι × E2) (a : ι)
    (hF : ∀ q, F (Sum.inl a, q) = (a, q)) :
    (PMor ι).IsScDiffeoOn (PObj ι) F (fun x => (Sum.inl a, x.2)) ({Sum.inl a} ×ˢ univ)
      ({a} ×ˢ univ) where
  isScSmoothOn := by
    refine (((isScSmoothMap_sheet a).comp (MPolyfold.isScSmoothMap_snd _ _)).mono
      (isOpen_sheet _) (subset_univ _)).congr fun ψ hψ => ?_
    obtain ⟨i, q⟩ := ψ
    have hi : i = Sum.inl a := hψ.1
    subst hi
    exact (hF q).symm
  isScSmoothOn_inv := ((isScSmoothMap_sheet (Sum.inl a)).comp
    (MPolyfold.isScSmoothMap_snd _ _)).mono (isOpen_sheet _) (subset_univ _)
  mapsTo := fun ψ hψ => by
    obtain ⟨i, q⟩ := ψ
    have hi : i = Sum.inl a := hψ.1
    subst hi
    rw [hF]
    exact ⟨rfl, mem_univ _⟩
  mapsTo_inv := fun _ _ => ⟨rfl, mem_univ _⟩
  left_inv := fun ψ hψ => by
    obtain ⟨i, q⟩ := ψ
    have hi : i = Sum.inl a := hψ.1
    subst hi
    rw [hF]
  right_inv := fun x hx => by
    obtain ⟨a', q⟩ := x
    have ha : a' = a := hx.1
    subst ha
    exact hF q

/-- A map which is `(inr i, p) ↦ (e, chartPt (c e) p)` on the sheet `i` is an sc-diffeomorphism
from that sheet onto `{e} × {y > 0}`, with inverse `x ↦ (inr i, canon (c e) x.2)`. -/
theorem isScDiffeoOn_inr_sheet (F : MorIdx ι × E2 → ι × E2) (i : {q : ι × ι // q.1 ≠ q.2})
    (e : ι) (hF : ∀ p, F (Sum.inr i, p) = (e, chartPt (c e) p)) :
    (PMor ι).IsScDiffeoOn (PObj ι) F (fun x => (Sum.inr i, canon (c e) x.2))
      ({Sum.inr i} ×ˢ univ) ({e} ×ˢ {q : E2 | 0 < q 1}) where
  isScSmoothOn := by
    refine (((isScSmoothMap_sheet e).comp ((isScSmoothMap_chartPt (c e)).comp
      (MPolyfold.isScSmoothMap_snd _ _))).mono (isOpen_sheet _) (subset_univ _)).congr
      fun ψ hψ => ?_
    obtain ⟨j, p⟩ := ψ
    have hj : j = Sum.inr i := hψ.1
    subst hj
    exact (hF p).symm
  isScSmoothOn_inv := MPolyfold.IsScSmoothOn.comp (isScSmoothMap_sheet (Sum.inr i))
    (MPolyfold.IsScSmoothOn.comp (isScSmoothOn_canon (c e))
      ((MPolyfold.isScSmoothMap_snd _ _).mono ((isOpen_discrete _).prod isOpen_pos)
        (subset_univ _)) fun x hx => hx.2) (mapsTo_univ _ _)
  mapsTo := fun ψ hψ => by
    obtain ⟨j, p⟩ := ψ
    have hj : j = Sum.inr i := hψ.1
    subst hj
    rw [hF]
    exact ⟨rfl, chartPt_one_pos (c e) p⟩
  mapsTo_inv := fun _ _ => ⟨rfl, mem_univ _⟩
  left_inv := fun ψ hψ => by
    obtain ⟨j, p⟩ := ψ
    have hj : j = Sum.inr i := hψ.1
    subst hj
    rw [hF]
    change (Sum.inr i, canon (c e) (chartPt (c e) p)) = (Sum.inr i, p)
    rw [canon_chartPt]
  right_inv := fun x hx => by
    obtain ⟨e', q⟩ := x
    have he : e' = e := hx.1
    subst he
    rw [hF]
    change (e', chartPt (c e') (canon (c e') q)) = (e', q)
    rw [chartPt_canon _ hx.2]

/-- **(1) for `s`**: the source is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_src : (PMor ι).IsLocalScDiffeo (PObj ι) (src ι c) := fun φ =>
  match φ with
  | (Sum.inl a, _) => ⟨{Sum.inl a} ×ˢ univ, {a} ×ˢ univ, fun x => (Sum.inl a, x.2),
      ⟨rfl, mem_univ _⟩, isScDiffeoOn_inl_sheet (src ι c) a fun q => src_inl a q⟩
  | (Sum.inr i, _) => ⟨{Sum.inr i} ×ˢ univ, {i.1.1} ×ˢ {q : E2 | 0 < q 1},
      fun x => (Sum.inr i, canon (c i.1.1) x.2), ⟨rfl, mem_univ _⟩,
      isScDiffeoOn_inr_sheet (src ι c) i i.1.1 fun p => src_inr i p⟩

/-- **(1) for `t`**: the target is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_tgt : (PMor ι).IsLocalScDiffeo (PObj ι) (tgt ι c) := fun φ =>
  match φ with
  | (Sum.inl a, _) => ⟨{Sum.inl a} ×ˢ univ, {a} ×ˢ univ, fun x => (Sum.inl a, x.2),
      ⟨rfl, mem_univ _⟩, isScDiffeoOn_inl_sheet (tgt ι c) a fun q => tgt_inl a q⟩
  | (Sum.inr i, _) => ⟨{Sum.inr i} ×ˢ univ, {i.1.2} ×ˢ {q : E2 | 0 < q 1},
      fun x => (Sum.inr i, canon (c i.1.2) x.2), ⟨rfl, mem_univ _⟩,
      isScDiffeoOn_inr_sheet (tgt ι c) i i.1.2 fun p => tgt_inr i p⟩

theorem isScSmoothMap_src : (PMor ι).IsScSmoothMap (PObj ι) (src ι c) :=
  (isLocalScDiffeo_src (c := c)).isScSmoothMap

theorem isScSmoothMap_tgt : (PMor ι).IsScSmoothMap (PObj ι) (tgt ι c) :=
  (isLocalScDiffeo_tgt (c := c)).isScSmoothMap

theorem continuous_src : Continuous (src ι c) := (isLocalScDiffeo_src (c := c)).continuous

theorem continuous_tgt : Continuous (tgt ι c) := (isLocalScDiffeo_tgt (c := c)).continuous

/-- **(2) for `u`**: the unit map `x ↦ (inl x.1, x.2)` is sc-smooth. -/
theorem isScSmoothMap_unit : (PObj ι).IsScSmoothMap (PMor ι) (groupoidStr ι c).unit :=
  isScSmoothMap_prod_discrete_iff.2 fun a =>
    (isScSmoothMap_sheet (Sum.inl a)).congr fun q _ => (mk_self (a, q)).symm

/-- **(2) for `ι`**: the inverse is sc-smooth (the identity on the unit sheets,
`(inr (a, b), p) ↦ (inr (b, a), p)` on the others). -/
theorem isScSmoothMap_inv : (PMor ι).IsScSmoothMap (PMor ι) (groupoidStr ι c).inv := by
  refine isScSmoothMap_prod_discrete_iff.2 fun i => ?_
  rcases i with a | ⟨⟨a, b⟩, h⟩
  · exact (isScSmoothMap_sheet (Sum.inl a)).congr fun q _ => (mk_self (a, q)).symm
  · refine (isScSmoothMap_sheet (Sum.inr ⟨(b, a), Ne.symm h⟩)).congr fun p _ => ?_
    change (Sum.inr ⟨(b, a), Ne.symm h⟩, p) =
      mk ι c (tgt ι c (Sum.inr ⟨(a, b), h⟩, p)) (src ι c (Sum.inr ⟨(a, b), h⟩, p))
    rw [src_inr, tgt_inr, mk_of_ne (Ne.symm h), canon_chartPt]

/-- **(4)** in the sheet form: for an sc-diffeomorphism `σ : V → W` inverting `s`, the map
`ψ ↦ σ(t ψ) ∘ ψ = mk (s ψ) (t (σ (t ψ)))` is sc-smooth on `t⁻¹(V)`.  Near `ψ₀` the chart indices
`a` of `s ψ` and `d` of `t (σ (t ψ))` are constant, and the map is `ψ ↦ (inl a, (s ψ).2)` if
`a = d` and `ψ ↦ (inr (a, d), canon (c a) (s ψ).2)` otherwise. -/
theorem isScSmoothCompSheet :
    IsScSmoothCompSheet (PObj ι) (PMor ι) (src ι c) (tgt ι c) (groupoidStr ι c).comp := by
  intro σ W V hd
  change (PMor ι).IsScSmoothOn (PMor ι)
    (fun ψ => mk ι c (src ι c ψ) (tgt ι c (σ (tgt ι c ψ)))) (tgt ι c ⁻¹' V)
  have hV : IsOpen V := hd.isScSmoothOn_inv.isOpen
  have hT : IsOpen (tgt ι c ⁻¹' V) := hV.preimage continuous_tgt
  have hcont : ContinuousOn (fun ψ => (tgt ι c (σ (tgt ι c ψ))).1) (tgt ι c ⁻¹' V) :=
    continuous_fst.comp_continuousOn (continuous_tgt.comp_continuousOn
      (hd.isScSmoothOn_inv.continuousOn.comp continuous_tgt.continuousOn (mapsTo_preimage _ _)))
  refine MPolyfold.IsScSmoothOn.of_locally hT fun ψ₀ hψ₀ => ?_
  set a := (src ι c ψ₀).1 with ha
  set d := (tgt ι c (σ (tgt ι c ψ₀))).1 with hd'
  set N := (tgt ι c ⁻¹' V ∩ (fun ψ => (tgt ι c (σ (tgt ι c ψ))).1) ⁻¹' {d}) ∩
    (fun ψ => (src ι c ψ).1) ⁻¹' {a} with hN
  have hNo : IsOpen N := (hcont.isOpen_inter_preimage hT (isOpen_discrete _)).inter
    ((isOpen_discrete _).preimage (continuous_fst.comp continuous_src))
  have hψ₀N : ψ₀ ∈ N := ⟨⟨hψ₀, rfl⟩, rfl⟩
  have hNsub : N ⊆ tgt ι c ⁻¹' V := fun ψ hψ => hψ.1.1
  -- on `N`, `s ψ` and `t (σ (t ψ))` are related, with charts `a` and `d`
  have hrel : ∀ ψ ∈ N, Rel ι c (src ι c ψ) (tgt ι c (σ (tgt ι c ψ))) := fun ψ hψ => by
    have h := rel_src_tgt (c := c) (σ (tgt ι c ψ))
    rw [hd.right_inv _ hψ.1.1] at h
    exact (rel_src_tgt ψ).trans h
  have hsnd : (PMor ι).IsScSmoothOn (rnPolyfold 2) (fun ψ => (src ι c ψ).2) N :=
    ((MPolyfold.isScSmoothMap_snd _ _).comp isScSmoothMap_src).mono hNo (subset_univ _)
  refine ⟨N, hNo, hψ₀N, hNsub, ?_⟩
  by_cases had : a = d
  · refine (MPolyfold.IsScSmoothOn.comp (isScSmoothMap_sheet (Sum.inl a)) hsnd
      (mapsTo_univ _ _)).congr fun ψ hψ => ?_
    have h1 : (src ι c ψ).1 = a := hψ.2
    have h2 : (tgt ι c (σ (tgt ι c ψ))).1 = d := hψ.1.2
    change (Sum.inl a, (src ι c ψ).2) = mk ι c (src ι c ψ) (tgt ι c (σ (tgt ι c ψ)))
    rw [mk_of_eq (by rw [h1, h2]; exact had), h1]
  · have hpos : MapsTo (fun ψ => (src ι c ψ).2) N {q : E2 | 0 < q 1} := fun ψ hψ => by
      have h1 : (src ι c ψ).1 = a := hψ.2
      have h2 : (tgt ι c (σ (tgt ι c ψ))).1 = d := hψ.1.2
      exact ((hrel ψ hψ).pos_of_ne (by rw [h1, h2]; exact had)).1
    refine (MPolyfold.IsScSmoothOn.comp (isScSmoothMap_sheet (Sum.inr ⟨(a, d), had⟩))
      (MPolyfold.IsScSmoothOn.comp (isScSmoothOn_canon (c a)) hsnd hpos)
      (mapsTo_univ _ _)).congr fun ψ hψ => ?_
    have h1 : (src ι c ψ).1 = a := hψ.2
    have h2 : (tgt ι c (σ (tgt ι c ψ))).1 = d := hψ.1.2
    change (Sum.inr ⟨(a, d), had⟩, canon (c a) (src ι c ψ).2) =
      mk ι c (src ι c ψ) (tgt ι c (σ (tgt ι c ψ)))
    rw [mk_of_ne (by rw [h1, h2]; exact had)]
    simp only [h1, h2]

/-! ### (3) Properness -/

omit [TopologicalSpace ι] [DiscreteTopology ι] in
/-- The set of canonical coordinates of the morphisms of the sheet `(a, b)` whose source lies
over `cl B(q₀, 1)` and whose target lies in `{‖·‖ ≤ R}` is bounded, hence compact: `e^l` and
`(c a − c b) e^{−l}` are bounded. -/
theorem isCompact_sheetSet {a b : ι} (hab : c a ≠ c b) (q₀ : E2) (R : ℝ) :
    IsCompact {p : E2 | chartPt (c a) p ∈ Metric.closedBall q₀ 1 ∧
      chartPt (c b) p ∈ Metric.closedBall 0 R} := by
  refine Metric.isCompact_of_isClosed_isBounded
    ((Metric.isClosed_closedBall.preimage (contDiff_chartPt _).continuous).inter
      (Metric.isClosed_closedBall.preimage (contDiff_chartPt _).continuous)) ?_
  set M : ℝ := ‖q₀‖ + 1 with hM
  set δ : ℝ := |c a - c b| with hδ
  have hδpos : 0 < δ := abs_pos.2 (sub_ne_zero.2 hab)
  set M' : ℝ := (|R| + M) / δ with hM'
  have hM0 : 0 ≤ M := by positivity
  have hM'0 : 0 ≤ M' := by positivity
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨M + M' + |c a| * M', fun p ⟨hp1, hp2⟩ => ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at hp1 hp2
  rw [sub_zero] at hp2
  set e : ℝ := Real.exp (-(p 1)) with he
  have he0 : 0 < e := Real.exp_pos _
  -- the two coordinates of the chart points
  have hA0 : |chartPt (c a) p 0| ≤ M := by
    have h1 : |chartPt (c a) p 0 - q₀ 0| ≤ 1 := by
      have := norm_le_pi_norm (chartPt (c a) p - q₀) 0
      simpa [Real.norm_eq_abs] using this.trans hp1
    have h2 : |q₀ 0| ≤ ‖q₀‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm q₀ 0
    calc |chartPt (c a) p 0| = |(chartPt (c a) p 0 - q₀ 0) + q₀ 0| := by ring_nf
      _ ≤ |chartPt (c a) p 0 - q₀ 0| + |q₀ 0| := abs_add_le _ _
      _ ≤ 1 + ‖q₀‖ := add_le_add h1 h2
      _ = M := by rw [hM, add_comm]
  have hA1 : Real.exp (p 1) ≤ M := by
    have h1 : |chartPt (c a) p 1 - q₀ 1| ≤ 1 := by
      have := norm_le_pi_norm (chartPt (c a) p - q₀) 1
      simpa [Real.norm_eq_abs] using this.trans hp1
    have h2 : |q₀ 1| ≤ ‖q₀‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm q₀ 1
    rw [chartPt_one] at h1
    have := (abs_le.1 h1).2
    have := (abs_le.1 h2).2
    linarith
  have hB0 : |chartPt (c b) p 0| ≤ |R| := by
    have := norm_le_pi_norm (chartPt (c b) p) 0
    simp only [Real.norm_eq_abs] at this
    exact this.trans (hp2.trans (le_abs_self R))
  -- `(c a − c b) e ≤ |R| + M`
  have hE : δ * e ≤ |R| + M := by
    have h : chartPt (c b) p 0 - chartPt (c a) p 0 = (c a - c b) * e := by
      rw [chartPt_zero, chartPt_zero]
      ring
    calc δ * e = |(c a - c b) * e| := by rw [abs_mul, abs_of_pos he0]
      _ = |chartPt (c b) p 0 - chartPt (c a) p 0| := by rw [h]
      _ ≤ |chartPt (c b) p 0| + |chartPt (c a) p 0| := abs_sub _ _
      _ ≤ |R| + M := add_le_add hB0 hA0
  have heM' : e ≤ M' := by
    rw [hM', le_div_iff₀ hδpos, mul_comm]
    exact hE
  -- the bounds on the canonical coordinates
  have hp1le : p 1 ≤ M := by
    have := Real.add_one_le_exp (p 1)
    linarith
  have hp1ge : -M' ≤ p 1 := by
    have := Real.add_one_le_exp (-(p 1))
    linarith
  have hp0 : |p 0| ≤ M + |c a| * M' := by
    have h : p 0 = chartPt (c a) p 0 + c a * e := by
      rw [chartPt_zero]
      ring
    calc |p 0| = |chartPt (c a) p 0 + c a * e| := by rw [h]
      _ ≤ |chartPt (c a) p 0| + |c a * e| := abs_add_le _ _
      _ = |chartPt (c a) p 0| + |c a| * e := by rw [abs_mul, abs_of_pos he0]
      _ ≤ M + |c a| * M' := add_le_add hA0 (mul_le_mul_of_nonneg_left heM' (abs_nonneg _))
  rw [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i
  · change |p 0| ≤ M + M' + |c a| * M'
    linarith
  · change |p 1| ≤ M + M' + |c a| * M'
    rw [abs_le]
    constructor <;> nlinarith [abs_nonneg (c a)]

/-- **(3)**: with `V(x) = {a} × B(q₀, 1)`, `t : s⁻¹(cl V(x)) → X` is proper.  The preimage of a
compact `K` is closed and contained in the finite union of the compact sets
`{inl a} × cl B(q₀, 1)` and `{inr (a, b)} × (sheet set)`, `b` in the finite image of `K` in `ι`. -/
theorem exists_isProperMap (hc : Injective c) (x : ι × E2) :
    ∃ V : Set (ι × E2), IsOpen V ∧ x ∈ V ∧
      IsProperMap ((src ι c ⁻¹' closure V).domRestrict (tgt ι c)) := by
  classical
  obtain ⟨a, q₀⟩ := x
  refine ⟨{a} ×ˢ Metric.ball q₀ 1, (isOpen_discrete _).prod Metric.isOpen_ball,
    ⟨rfl, Metric.mem_ball_self one_pos⟩, ?_⟩
  have hcl : closure ({a} ×ˢ Metric.ball q₀ 1 : Set (ι × E2)) ⊆
      {a} ×ˢ Metric.closedBall q₀ 1 := by
    rw [closure_prod_eq, closure_singleton]
    exact prod_mono subset_rfl Metric.closure_ball_subset_closedBall
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_tgt.comp continuous_subtype_val, fun K hK => ?_⟩
  rw [Subtype.isCompact_iff]
  set S : Set (MorIdx ι × E2) :=
    {φ | src ι c φ ∈ closure ({a} ×ˢ Metric.ball q₀ 1 : Set (ι × E2)) ∧ tgt ι c φ ∈ K} with hS
  have himg : Subtype.val '' (Set.domRestrict
      (src ι c ⁻¹' closure ({a} ×ˢ Metric.ball q₀ 1 : Set (ι × E2))) (tgt ι c) ⁻¹' K) = S := by
    ext φ
    constructor
    · rintro ⟨⟨φ, hφ⟩, hK, rfl⟩
      exact ⟨hφ, hK⟩
    · intro hφ
      exact ⟨⟨φ, hφ.1⟩, hφ.2, rfl⟩
  rw [himg]
  have hclosed : IsClosed S := (isClosed_closure.preimage continuous_src).inter
    (hK.isClosed.preimage continuous_tgt)
  -- the bound on `K` and its finite set of charts
  obtain ⟨r, hr⟩ := (hK.image continuous_snd).isBounded.subset_closedBall 0
  set R : ℝ := max r 0 with hR
  have hKR : ∀ z ∈ K, ‖z.2‖ ≤ R := fun z hz => by
    have := hr ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set F : Set ι := Prod.fst '' K with hF
  have hFfin : F.Finite := (hK.image continuous_fst).finite_of_discrete
  -- the compact superset
  set T : Set (MorIdx ι × E2) := ({Sum.inl a} ×ˢ Metric.closedBall q₀ 1) ∪
    ⋃ b ∈ F, (if h : a = b then ∅ else {Sum.inr ⟨(a, b), h⟩} ×ˢ
      {p : E2 | chartPt (c a) p ∈ Metric.closedBall q₀ 1 ∧
        chartPt (c b) p ∈ Metric.closedBall 0 R}) with hT
  have hTc : IsCompact T := by
    refine (isCompact_singleton.prod (isCompact_closedBall q₀ 1)).union
      (hFfin.isCompact_biUnion fun b _ => ?_)
    split_ifs with h
    · exact isCompact_empty
    · exact isCompact_singleton.prod (isCompact_sheetSet (fun h' => h (hc h')) q₀ R)
  refine hTc.of_isClosed_subset hclosed fun φ hφ => ?_
  obtain ⟨hφs, hφt⟩ := hφ
  have hφs' := hcl hφs
  obtain ⟨i | ⟨⟨a', b⟩, h⟩, p⟩ := φ
  · rw [src_inl] at hφs'
    obtain ⟨rfl, hp⟩ := hφs'
    exact Or.inl ⟨rfl, hp⟩
  · rw [src_inr] at hφs'
    rw [tgt_inr] at hφt
    obtain ⟨rfl, hp⟩ := hφs'
    refine Or.inr (mem_iUnion₂.2 ⟨b, ⟨_, hφt, rfl⟩, ?_⟩)
    rw [dif_neg h]
    refine ⟨rfl, hp, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hKR _ hφt

/-! ### The ep-groupoid -/

variable (ι c) in
/-- **The Čech groupoid of the Prüfer atlas is an ep-groupoid** (Definition 7.1.3, pp. 288–289
(2017: Definition 7.3, pp. 226–227)): objects `ι × ℝ²`, morphisms `(ι ⊕ {(a, b) | a ≠ b}) × ℝ²`,
for a discrete `ι` and an injective `c : ι → ℝ`. -/
def epGroupoid (hc : Injective c) : EpGroupoid (ι × E2) (MorIdx ι × E2) where
  toGroupoidStr := groupoidStr ι c
  PObj := PObj ι
  PMor := PMor ι
  isLocalScDiffeo_src := isLocalScDiffeo_src
  isLocalScDiffeo_tgt := isLocalScDiffeo_tgt
  isScSmoothMap_unit := isScSmoothMap_unit
  isScSmoothMap_inv := isScSmoothMap_inv
  exists_isProperMap := exists_isProperMap hc
  isScSmoothComp := (isScSmoothComp_iff_sheet _ _).2 isScSmoothCompSheet

theorem epGroupoid_toGroupoidStr (hc : Injective c) :
    (epGroupoid ι c hc).toGroupoidStr = groupoidStr ι c := rfl

/-! ### The orbit space is not paracompact -/

omit [DiscreteTopology ι] in
/-- **The density step**: every open set of the orbit space containing `|(a, 0)|` contains a
point `|(a₀, r)|` with `r ∈ ℚ²`, for any fixed chart `a₀`: it contains `|(a, (0, y))|` for small
`y > 0`, which is `|(a₀, q)|` with `q = chartPt (c a₀) (canon (c a) (0, y))`. -/
theorem exists_rat_mem_of_mem (a₀ a : ι) {U : Set (groupoidStr ι c).OrbitSpace} (hU : IsOpen U)
    (hd : (groupoidStr ι c).π (a, 0) ∈ U) :
    ∃ r : ℚ × ℚ, (groupoidStr ι c).π (a₀, ![(r.1 : ℝ), (r.2 : ℝ)]) ∈ U := by
  have hπ : Continuous (groupoidStr ι c).π := continuous_quot_mk
  have hU' : IsOpen ((groupoidStr ι c).π ⁻¹' U) := hU.preimage hπ
  obtain ⟨u, v, -, hv, hau, h0v, huv⟩ := isOpen_prod_iff.1 hU' a 0 hd
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hv 0 h0v
  set y : ℝ := ε / 2 with hy
  have hypos : 0 < y := by positivity
  set q : E2 := ![0, y] with hq
  have hq1 : q 1 = y := rfl
  have hqball : q ∈ Metric.ball (0 : E2) ε := by
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hε]
    intro i
    fin_cases i
    · change ‖(0 : ℝ)‖ < ε
      simpa using hε
    · change ‖y‖ < ε
      rw [Real.norm_eq_abs, abs_of_pos hypos]
      linarith
  have h1 : (a, q) ∈ (groupoidStr ι c).π ⁻¹' U := huv ⟨hau, hball hqball⟩
  set q' : E2 := chartPt (c a₀) (canon (c a) q) with hq'
  have hrel : Rel ι c (a, q) (a₀, q') :=
    Or.inr ⟨hypos, chartPt_one_pos (c a₀) _, by rw [hq', canon_chartPt]⟩
  have h2 : (a₀, q') ∈ (groupoidStr ι c).π ⁻¹' U := by
    change (groupoidStr ι c).π (a₀, q') ∈ U
    rw [← π_eq_π_iff_rel.2 hrel]
    exact h1
  obtain ⟨u', v', -, hv', ha₀u', hq'v', huv'⟩ := isOpen_prod_iff.1 hU' a₀ q' h2
  obtain ⟨δ, hδ, hball'⟩ := Metric.isOpen_iff.1 hv' q' hq'v'
  obtain ⟨r₁, hr₁⟩ := exists_rat_near (q' 0) hδ
  obtain ⟨r₂, hr₂⟩ := exists_rat_near (q' 1) hδ
  refine ⟨(r₁, r₂), huv' ⟨ha₀u', hball' ?_⟩⟩
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hδ]
  intro i
  fin_cases i
  · change ‖(r₁ : ℝ) - q' 0‖ < δ
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact hr₁
  · change ‖(r₂ : ℝ) - q' 1‖ < δ
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact hr₂

/-- **The orbit space is not paracompact** for an uncountable index set `ι`.  The cover
`W_a = {z | ∀ b, z = |(b, 0)| → b = a}` has no locally finite open refinement: a refinement has
an injective choice `a ↦ β(a)` of members containing `|(a, 0)|`, each meeting the countable set
`{|(a₀, r)| : r ∈ ℚ²}`, at whose points only finitely many members pass. -/
theorem not_paracompactSpace_orbitSpace [Uncountable ι] (a₀ : ι) :
    ¬ ParacompactSpace (groupoidStr ι c).OrbitSpace := by
  intro hpc
  set G := groupoidStr ι c with hG
  -- the cover
  set W : ι → Set G.OrbitSpace := fun a => {z | ∀ b, z = G.π (b, 0) → b = a} with hW
  have hWpre : ∀ a, G.π ⁻¹' W a = {x | x.2 ≠ 0} ∪ {x | x.1 = a} := fun a => by
    ext x
    change (∀ b, G.π x = G.π (b, 0) → b = a) ↔ (x.2 ≠ 0 ∨ x.1 = a)
    constructor
    · intro h
      by_cases hx : x.2 = 0
      · exact Or.inr (h x.1 (by rw [← hx]))
      · exact Or.inl hx
    · rintro (h | h) b hb
      · rw [π_eq_π_iff_rel, rel_axis_iff] at hb
        exact absurd (congrArg Prod.snd hb) h
      · rw [π_eq_π_iff_rel, rel_axis_iff] at hb
        rw [← h, hb]
  have hWopen : ∀ a, IsOpen (W a) := fun a => by
    rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
    change IsOpen (G.π ⁻¹' W a)
    rw [hWpre]
    exact (isOpen_ne_fun continuous_snd continuous_const).union
      ((isOpen_discrete ({a} : Set ι)).preimage continuous_fst)
  have hWcover : ⋃ a, W a = univ := by
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    by_cases hx : x.2 = 0
    · exact mem_iUnion.2 ⟨x.1, fun b hb => by
        change G.π x = G.π (b, 0) at hb
        rw [π_eq_π_iff_rel, rel_axis_iff] at hb
        rw [hb]⟩
    · exact mem_iUnion.2 ⟨a₀, fun b hb => by
        change G.π x = G.π (b, 0) at hb
        rw [π_eq_π_iff_rel, rel_axis_iff] at hb
        exact absurd (congrArg Prod.snd hb) hx⟩
  obtain ⟨β, t, htopen, htcover, htlf, htref⟩ :=
    hpc.locallyFinite_refinement ι W hWopen hWcover
  -- the member containing `|(a, 0)|`
  have hmem : ∀ a, ∃ b, G.π (a, 0) ∈ t b := fun a =>
    mem_iUnion.1 (htcover.symm ▸ mem_univ (G.π (a, 0)))
  choose bOf hbOf using hmem
  have hind : ∀ a a', G.π (a, 0) ∈ t (bOf a') → a = a' := fun a a' h => by
    obtain ⟨a'', ha''⟩ := htref (bOf a')
    have h1 : a = a'' := ha'' h a rfl
    have h2 : a' = a'' := ha'' (hbOf a') a' rfl
    rw [h1, h2]
  have hinj : Injective bOf := fun a a' h => hind a a' (h ▸ hbOf a)
  -- the rational points
  choose rOf hrOf using fun a => exists_rat_mem_of_mem a₀ a (htopen (bOf a)) (hbOf a)
  set T : Set ((ℚ × ℚ) × β) := {x | G.π (a₀, ![(x.1.1 : ℝ), (x.1.2 : ℝ)]) ∈ t x.2} with hT
  have hTc : T.Countable := by
    have : T = ⋃ r : ℚ × ℚ, {r} ×ˢ {b | G.π (a₀, ![(r.1 : ℝ), (r.2 : ℝ)]) ∈ t b} := by
      ext ⟨r, b⟩
      simp [hT]
    rw [this]
    exact countable_iUnion fun r => (countable_singleton r).prod (htlf.point_finite _).countable
  have hf : Injective fun a => (rOf a, bOf a) := fun a a' h => hinj (congrArg Prod.snd h)
  have hpre : (fun a => (rOf a, bOf a)) ⁻¹' T = univ := eq_univ_of_forall fun a => hrOf a
  have : (univ : Set ι).Countable := by
    rw [← hpre]
    exact hTc.preimage_of_injOn hf.injOn
  exact not_countable (countable_univ_iff.1 this)

/-! ### The concrete example: `ι = ℝ` with the discrete topology -/

/-- `ℝ` with the discrete topology, the index set of the charts. -/
def DiscR : Type := ℝ

instance : TopologicalSpace DiscR := ⊥

instance : DiscreteTopology DiscR := ⟨rfl⟩

instance : DecidableEq DiscR := inferInstanceAs (DecidableEq ℝ)

instance : Uncountable DiscR := inferInstanceAs (Uncountable ℝ)

instance : Inhabited DiscR := ⟨((0 : ℝ) : DiscR)⟩

/-- The underlying real number. -/
def DiscR.val (a : DiscR) : ℝ := a

lemma DiscR.val_injective : Injective DiscR.val := fun _ _ h => h

/-- **The Prüfer ep-groupoid**: the Čech groupoid of the Prüfer atlas indexed by `ℝ`. -/
def pruefer : EpGroupoid (DiscR × E2) (MorIdx DiscR × E2) :=
  epGroupoid DiscR DiscR.val DiscR.val_injective

/-- **Property (5) fails for the Prüfer ep-groupoid** (Definition 7.5.1, p. 340 (2017: 7.15,
p. 249)): its orbit space is not paracompact. -/
theorem pruefer_not_hasParacompactOrbitSpace : ¬ pruefer.HasParacompactOrbitSpace :=
  not_paracompactSpace_orbitSpace default

/-- Lemma 7.3.4 (p. 325 (2017: Lemma 7.6, p. 243)) applies: the orbit space is Hausdorff. -/
theorem t2Space_orbitSpace_pruefer : T2Space pruefer.OrbitSpace := pruefer.lemma_7_3_4

/-- **Answer to the question of p. 340 (2017: p. 249)**: property (5) of Definition 7.5.1 is
**not** a consequence of properties (1)–(4) of Definition 7.1.3.  There is an ep-groupoid, with
object space `ℝ_discrete × ℝ²` and morphism space `(ℝ_discrete ⊕ {(a, b) | a ≠ b}) × ℝ²`, whose
(Hausdorff) orbit space is not paracompact. -/
theorem exists_epGroupoid_not_hasParacompactOrbitSpace :
    ∃ X : EpGroupoid (DiscR × E2) (MorIdx DiscR × E2), ¬ X.HasParacompactOrbitSpace :=
  ⟨pruefer, pruefer_not_hasParacompactOrbitSpace⟩

end Pruefer

end Examples

end EpGroupoid

end Polyfold
