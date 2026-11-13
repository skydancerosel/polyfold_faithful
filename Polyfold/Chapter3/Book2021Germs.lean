import Polyfold.Chapter3.TameGermData
import Polyfold.Chapter3.TameGermsG
import Polyfold.Chapter3.LocalCompactness
import Polyfold.Chapter3.SectionCompactnessG
import Polyfold.Chapter3.FredholmSectionsG
import Polyfold.Chapter3.ParamPerturbationG
import Polyfold.Chapter3.FredholmGermLinearizationG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941;
2014 preprint), Chapter 3: the items whose statement changed in the 2021 edition.
**Definition 3.1.4** (p. 91) and **Definition 3.6.1** (p. 134), the filling (2017: Definitions 3.4
and 3.13; preprint: Definitions 3.4 and 3.48), and **Theorem 3.5.1** (p. 118, local regularity and
compactness; 2017: Theorem 3.11; preprint: Theorem 3.40).  Numbers and pages are the 2021 text's,
the 2017 and preprint ones in parentheses.

# The 2021 filling (no tameness) and the sequential form of Theorem 3.5.1

## The text, paraphrased

(Definition 3.1.4, p. 91 (2017: Definition 3.4)) Let `K = R(U ◁ F) → O` be a strong local bundle,
`U ⊆ C ⊆ E` relatively open around `0`, `R(u, h) = (r(u), ρ(u)h)` a strong bundle retraction
covering the retraction `r : U → U` onto `O = r(U)`, with `r(0) = 0`.  An sc-smooth section germ
`(f, 0)` of `K → O` has a filling if an sc-smooth section germ `(g, 0)` of `U ◁ F → U` satisfies:
(1) `f = g` on `O` near `0`; (2) a point `y ∈ U` near `0` with `g(y) = ρ(r(y))g(y)` lies in `O`;
(3) the linearization at `0` of `y ↦ [1 − ρ(r(y))]g(y)`, restricted to `ker Dr(0)`, is a
topological linear isomorphism onto `ker ρ(0)`.  **The 2017 text (and the 2014 preprint) asks
`r` to be a tame retraction; the 2021 text does not.**  (Definition 3.6.1, p. 134 (2017:
Definition 3.13)) the same definition, repeated in §3.6, with `r` "the sc-smooth retraction"
(2017: "the tame retraction").

(Theorem 3.5.1, p. 118 (2017: Theorem 3.11)) Let `f = h + s : U → F` with `h` a basic germ and `s`
an sc⁺-germ, `f(0) = 0 = s(0)`, and `S = {f = 0}`.  There are nested relatively open neighbourhoods
`U ⊃ O(0) ⊃ O(1) ⊃ …` of `0` in `C` on level `0` with `cl_{C₀}(S ∩ O(m)) ⊆ C_m`.  **New in 2021:**
if `(a_k, w_k) ∈ S` converges to `0` in `E₀`, then for every `m` there is `k₀(m)` such that
`(a_k, w_k) ∈ C_m` for `k ≥ k₀(m)` and this tail converges to `0` on level `m`.

## What is formalized

* `Polyfold.IsFilling2021` (**Definitions 3.1.4 and 3.6.1**), `Polyfold.HasFilling2021`;
  `Polyfold.IsFilling2017` (the 2017 Definitions 3.4 and 3.13: the same with a tame `r`).
* **How they relate to the project's notion.**  The project's `IsFillingGerm` (germ reading of
  preprint Definitions 3.4/3.6) never asked `r` to be tame; it is the 2021 definition without the
  standing assumption `r(0) = 0` (`isFilling2021_iff`), and that assumption holds whenever
  `0 ∈ O` (`IsFillingGerm.isFilling2021`), in particular in every chart centred at a point of `X`.
  `IsFilling2017.isFilling2021` (2017 ⟹ 2021); **the converse fails**:
  `exists_isFilling2021_not_isFilling2017`, with the corner example below.  Satisfiability:
  `CornerFilling.isFilling2021_gc` and `isFilling2017_id`, `isFilling2017_rn`.
* **The corner example** (`Polyfold.CornerFilling`): `E = ℝ ⊕ ℝ`, `C = U = [0, ∞) × ℝ`, `F = ℝ`,
  `R((a, b), h) = ((0, b), 0)` (so `r(a, b) = (0, b)`, `O = {0} × ℝ`, `ρ ≡ 0`), the zero section
  `f̂ = 0`, and `g(a, b) = a`.  It is a 2021 filling (`isFilling2021_gc`), `r` is not tame
  (`not_isTame_r`: `d(1, 0) = 0`, `d(r(1, 0)) = d(0) = 1`).
* **Bundle level.**  `StrongBundle.IsScFredholmGerm2021` (**Definition 3.1.11 = 3.6.3** with the
  2021 filling), `StrongBundle.IsScFredholmSection2021` (**Definition 3.1.16 = 3.6.4**), and
  `StrongBundle.IsScFredholmGerm2017` (the 2017 filling).  `isScFredholmGerm2021_iff`: the 2021
  germ is the project's `IsScFredholmGerm`; `isScFredholmSection2021_iff`: the 2021 section is
  `IsScFredholmSection`; `isScFredholmGerm2017_iff`: the 2017 germ is `IsScFredholmGermTame`.
  Satisfiability: `isScFredholmSection2021_graphSection`, `isScFredholmGerm2017_graphSection`.
* **The 2021 theorems whose proofs do not use tameness**, restated for the 2021 definitions:
  `proposition_3_1_5` (Proposition 3.1.5), `theorem_3_1_13` (Theorem 3.1.13),
  `corollary_3_1_15` (Corollary 3.1.15), `theorem_3_1_18` (Theorem 3.1.18),
  `theorem_3_1_21` (Theorem 3.1.21), `proposition_3_6_5` (Proposition 3.6.5).
* **Where the proofs of the 2021 implicit function theorems use tameness**:
  `theorem_3_6_8_tame_step` (see below).
* `Polyfold.theorem_3_5_1` (**Theorem 3.5.1**, both conclusions), from
  `theorem_3_1_13_local` and `corollary_3_1_15_local`.

## What the text leaves implicit, and the choices made

* **Which proofs use the tameness of `r`.**  Proposition 3.1.5 (the filler), Theorem 3.1.13 and
  Corollary 3.1.15 (local compactness), Theorem 3.1.18 (sc⁺-perturbations), Theorem 3.1.21
  (parametrized perturbations) and Proposition 3.6.5 (`Tf(x)` is sc-Fredholm) were proved in the
  project for the untamed germ data `IsScFredholmGerm`; they hold for the 2021 definitions as
  printed.  Theorem 3.6.8 (and with it Theorems 3.1.22, 3.1.26, Corollary 3.1.27, Theorems 3.6.10
  and 3.6.11) does use it: its proof (p. 138) passes from good position of `ker Tf̃(0)` to the
  partial cone `C₀O = T₀O ∩ C` in `T₀O` to good position of `ker Dg(0)` to `C` in `E` through the
  sc-complement `ker Dr(0) ⊆ E₀` of `T₀O` given by Proposition 2.5.3 for a tame retract, the
  hypothesis `hK : (1 − Dr(0))E ⊆ E₀` of `theorem_3_6_8_linear`.  **The step does not go through
  without it**: in the corner example the filling, `f̂(0) = 0`, `Dg(0)` onto, and good position of
  `ker Tf̃(0)` in `T₀O` (`IsGoodPositionAtGerm`) all hold, `hK` fails, and `ker Dg(0) = 0 ⊕ ℝ` is
  not in good position to `C` in `E` (`theorem_3_6_8_tame_step`).  Since `X = ℝ` there has no
  boundary, tameness of the chart enters even the proof of Theorem 3.6.10 (`∂X = ∅`).  The
  example's solution set `O ≅ ℝ` is still a manifold.  For untamed germ data the conclusions do
  not hold as we read it: `UntamedCorner.theorem_3_6_8_untamed_not` and
  `UntamedCorner.theorem_3_1_22_untamed_not` (`GapP1_UntamedBundleTheorem.lean`) give a tame strong
  bundle over `ℝ` with a 2021 sc-Fredholm section whose solution set near a zero in good position
  is a closed half-line, and germ data in a compatible chart need not move to a tame one
  (`UntamedCorner.isScFredholmGerm2021_not_tame`; Findings, Chapter 3, items 353, 388).
* **`r(0) = 0`** is a field of `IsFilling2021`; the text "assumes" it.  In the project's charts it
  follows from `c.φ x₀ = 0` and `0 ∈ O = r(U)`.
* **Theorem 3.5.1.**  As in `theorem_3_1_13_local`, the basic germ `h` and the sc⁺-germ `s` live on
  one germ of neighbourhoods `G`, `U = G₀`, and of `s` only its level-wise continuity into `F¹`
  (an sc⁰-germ into `F¹`) is used.  The sets `O(m)` are `O'(m) ∩ G₀` with `O'(m)` open in `E₀`,
  so relatively open in `C` and inside `U`; the closure is taken in `E₀` and lies in `C` because
  `C` is closed.  "`(a_k, w_k) ∈ C_m` and converges on level `m`" is stated with level-`m` lifts
  `y_k ∈ E_m`, `ι_m(y_k) = (a_k, w_k)` for `k` large, `y_k → 0` in `E_m`.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

open StrongRetr

/-! ### Definitions 3.1.4 and 3.6.1: the filling, 2021 and 2017 -/

section Filling

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-- **2021 Definition 3.1.4, p. 91, and Definition 3.6.1, p. 134** (2017: Definitions 3.4 and 3.13;
preprint: Definitions 3.4 and 3.48, changed: no tameness of `r`): for the strong local bundle
`K = R(U ◁ F) → O`, `R(u, h) = (r(u), ρ(u)h)` covering the sc-smooth retraction `r : U → U` onto
`O = r(U)` with `r(0) = 0`, the sc-smooth section germ `(g, 0)` of `U ◁ F → U` (an sc-smooth germ on
an sc-germ of neighbourhoods `G` of `0` in `C`, `G₀ ⊆ U`) is a **filling** of the section germ with
principal part `f̂` if (1) `f̂ = g` on `O` near `0`, (2) `y ∈ U` near `0` with `g(y) = ρ(r(y))g(y)`
lies in `O`, (3) the linearization `Dk(0)` of `k(y) = [1 − ρ(r(y))]g(y)` restricted to
`ker Dr(0)` is a topological linear isomorphism onto `ker ρ(0)`. -/
structure IsFilling2021 (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) (fb g : E 0 → F 0) : Prop where
  r_zero : r R 0 = 0
  eq_on : ∀ᶠ x in 𝓝 (0 : E 0), x ∈ r R '' U → fb x = g x
  mem_of_fixed : ∀ᶠ y in 𝓝 (0 : E 0), y ∈ U → g y = ρ R (r R y) (g y) → y ∈ r R '' U
  germ : ∃ G : ScNbhdGerm E C, G.U 0 ⊆ U ∧ IsScSmoothGerm G g ∧
    ∃ Dk : E 1 → E 0 →L[ℝ] F 0, IsSc1GermWith G (fillDefect R g) Dk ∧
      ∃ Φ : LinearMap.ker ((scDeriv U (r R) (0 : E 1) : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0)
          ≃L[ℝ] LinearMap.ker ((ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0),
        ∀ v : LinearMap.ker ((scDeriv U (r R) (0 : E 1) : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0),
          ((Φ v : LinearMap.ker ((ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0)) : F 0) =
            Dk 0 (v : E 0)

/-- **2021 Definition 3.1.4, p. 91**: the section germ with principal part `f̂` **possesses a
filling**. -/
def HasFilling2021 (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) (fb : E 0 → F 0) : Prop :=
  ∃ g, IsFilling2021 hU hR h0 fb g

/-- **The 2017 filling** (2017 Definitions 3.4 and 3.13, p. 59 and p. 98; preprint Definitions 3.4
and 3.48), for comparison with 2021 Definitions 3.1.4 and 3.6.1: the same data, with the base
retraction `r` **tame** (2021 Definition 2.5.2, for every presentation of `C`). -/
structure IsFilling2017 (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) (fb g : E 0 → F 0) : Prop extends IsFilling2021 hU hR h0 fb g where
  tame : (hR.baseRetraction hU).IsTame

variable {hU : IsRelOpenInQuadrant E C U} {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U}
  {fb g : E 0 → F 0}

/-- **The 2021 filling is the project's `IsFillingGerm` plus the standing assumption `r(0) = 0`**
(2021 Definition 3.1.4 versus the germ reading of preprint Definitions 3.4/3.6, in which tameness
was never required). -/
theorem isFilling2021_iff :
    IsFilling2021 hU hR h0 fb g ↔ r R 0 = 0 ∧ IsFillingGerm hU hR h0 fb g :=
  ⟨fun h => ⟨h.r_zero, h.eq_on, h.mem_of_fixed, h.germ⟩,
    fun ⟨h1, h2⟩ => ⟨h1, h2.eq_on, h2.mem_of_fixed, h2.germ⟩⟩

/-- A 2021 filling is a filling in the project's germ reading. -/
theorem IsFilling2021.isFillingGerm (h : IsFilling2021 hU hR h0 fb g) :
    IsFillingGerm hU hR h0 fb g :=
  (isFilling2021_iff.1 h).2

/-- **Project ⟹ 2021**: a filling in the project's germ reading is a 2021 filling as soon as
`0 ∈ O = r(U)` (then `r(0) = 0`). -/
theorem IsFillingGerm.isFilling2021 (h : IsFillingGerm hU hR h0 fb g)
    (h0O : (0 : E 0) ∈ r R '' U) : IsFilling2021 hU hR h0 fb g :=
  isFilling2021_iff.2 ⟨r_eq_self hR h0O, h⟩

/-- **Project (whole-chart filled version) ⟹ 2021.** -/
theorem IsFilledVersion.isFilling2021 (h : IsFilledVersion hU hR h0 fb g)
    (h0O : (0 : E 0) ∈ r R '' U) : IsFilling2021 hU hR h0 fb g :=
  (h.isFillingGerm hU hR h0).isFilling2021 h0O

/-- **2017 ⟹ 2021**: a 2017 filling (tame `r`) is a 2021 filling. -/
theorem IsFilling2017.isFilling2021 (h : IsFilling2017 hU hR h0 fb g) :
    IsFilling2021 hU hR h0 fb g :=
  h.toIsFilling2021

/-- The 2017 filling is the 2021 filling with a tame base retraction. -/
theorem isFilling2017_iff :
    IsFilling2017 hU hR h0 fb g ↔ (hR.baseRetraction hU).IsTame ∧ IsFilling2021 hU hR h0 fb g :=
  ⟨fun h => ⟨h.tame, h.toIsFilling2021⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩

/-- **Satisfiability of the 2017 filling** (hence of the 2021 one): with the identity strong
bundle retraction (tame, `ScRetraction.id_isTame`) every sc-smooth `g` fills itself. -/
theorem isFilling2017_id (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U) {g : E 0 → F 0}
    (hg : IsScSmooth U g) :
    IsFilling2017 hU (isStrongBundleRetraction_id_of_relOpen hU) h0 g g :=
  ⟨(isFilledVersion_id hU h0 hg).isFilling2021 ⟨0, h0, rfl⟩,
    (ScRetraction.id_isTame hU).congr rfl fun _ _ => rfl⟩

/-- A concrete instance: `E = F = ℝ`, `U = ℝ`, `R = id`, `g = 0`. -/
theorem isFilling2017_rn :
    IsFilling2017 (rn_relOpen_univ 1) (isStrongBundleRetraction_id_of_relOpen (F := rnSc 1)
      (rn_relOpen_univ 1)) (mem_univ 0) 0 0 :=
  isFilling2017_id _ _ (isScSmooth_of_bijective_toBase (bijective_toBase_const _)
    (bijective_toBase_const _) (isScDomain_univ _) contDiffOn_const)

end Filling

/-! ### The corner example: a 2021 filling over a non-tame retraction -/

namespace CornerFilling

open HalfSpaceBundle

/-- The model `ℝ ⊕ ℝ` (constant sc-structure) with the half-plane `[0, ∞) × ℝ`. -/
abbrev Ec : ScBanach := halfSpaceSc 1

/-- The half-plane `H = [0, ∞) × ℝ`, the partial quadrant and the domain `U`. -/
abbrev Hc : Set (Ec 0) := quadrant 1 (rnSc 1) 0

/-- The fibre `F = ℝ`. -/
abbrev Fc : ScBanach := rnSc 1

lemma relOpen_Hc : IsRelOpenInQuadrant Ec Hc Hc := relOpen_H 1

lemma zero_mem_Hc : (0 : Ec 0) ∈ Hc := fun _ => le_rfl

/-- **The strong bundle retraction** `R((a, b), h) = ((0, b), 0)` of `H ◁ ℝ`: it covers
`r(a, b) = (0, b)` (retract `O = {0} × ℝ`) with `ρ ≡ 0`. -/
def Rc : Ec 0 × Fc 0 → Ec 0 × Fc 0 := fun q => (((0 : Fin 1 → ℝ), q.1.2), 0)

lemma bijective_toBase_EF (j : ℕ) : Bijective ((Ec.prod Fc).toBase j) :=
  bijective_toBase_prod bijective_toBase_E (bijective_toBase_const _) j

lemma bijective_toBase_EF1 (j : ℕ) : Bijective ((Ec.prod Fc.shift).toBase j) :=
  bijective_toBase_prod bijective_toBase_E (bijective_toBase_shift (bijective_toBase_const _)) j

lemma contDiff_Rc : ContDiff ℝ ∞ Rc :=
  (contDiff_const.prodMk contDiff_fst.snd).prodMk contDiff_const

lemma isStrongBundleRetraction_Rc : IsStrongBundleRetraction (E := Ec) (F := Fc) Hc Rc where
  mapsTo _ _ := ⟨fun _ => le_rfl, mem_univ _⟩
  fst_independent _ _ _ _ := rfl
  fiber_linear _ _ := ⟨fun _ _ => (add_zero 0).symm, fun _ _ => (smul_zero _).symm⟩
  preserves_filtration j l _ _ _ _ _ _ :=
    ⟨(bijective_toBase_E j).2 _, (bijective_toBase_const _ l).2 _⟩
  isScSmooth_zero := isScSmooth_of_bijective_toBase bijective_toBase_EF bijective_toBase_EF
    (relOpen_Hc.prod_univ Fc).isScDomain contDiff_Rc.contDiffOn
  isScSmooth_one := by
    have hU := (relOpen_Hc.prod_univ Fc.shift).isScDomain
    refine (isScSmooth_of_bijective_toBase bijective_toBase_EF1 bijective_toBase_EF1 hU
      (f := Rc) contDiff_Rc.contDiffOn).congr hU fun p _ => ?_
    refine Prod.ext rfl ?_
    change (0 : Fin 1 → ℝ) = invFun ((rnSc 1).toBase 1) 0
    have := leftInverse_invFun ((rnSc 1).toBase_injective 1) (0 : Fin 1 → ℝ)
    rw [map_zero] at this
    exact this.symm
  idem _ _ := rfl

/-- The filling `g(a, b) = a`. -/
def gc : Ec 0 → Fc 0 := fun u => u.1

lemma isScSmooth_gc : IsScSmooth Hc gc :=
  isScSmooth_of_bijective_toBase bijective_toBase_E (bijective_toBase_const _)
    relOpen_Hc.isScDomain contDiff_fst.contDiffOn

/-- `Dr(0)(a, b) = (0, b)`. -/
def Lr : Ec 0 →L[ℝ] Ec 0 :=
  (ContinuousLinearMap.inr ℝ (Fin 1 → ℝ) (Fin 1 → ℝ)).comp
    (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) (Fin 1 → ℝ))

/-- `Dg(0)(a, b) = a`. -/
def Lg : Ec 0 →L[ℝ] Fc 0 := ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) (Fin 1 → ℝ)

lemma scDeriv_r : scDeriv Hc (r Rc) (0 : Ec 1) = Lr :=
  scDeriv_zero_eq_of_hasFDerivAt relOpen_Hc
    ((isStrongBundleRetraction_Rc.baseRetraction relOpen_Hc).isScSmooth.isSc1) zero_mem_Hc
    Lr.hasFDerivAt

lemma scDeriv_g : scDeriv Hc gc (0 : Ec 1) = Lg :=
  scDeriv_zero_eq_of_hasFDerivAt relOpen_Hc isScSmooth_gc.isSc1 zero_mem_Hc Lg.hasFDerivAt

lemma fillDefect_gc : fillDefect Rc gc = gc := funext fun _ => sub_zero _

lemma mem_ker_scDeriv_r {v : Ec 0} :
    v ∈ LinearMap.ker ((scDeriv Hc (r Rc) (0 : Ec 1) : Ec 0 →L[ℝ] Ec 0) : Ec 0 →ₗ[ℝ] Ec 0) ↔
      v.2 = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, scDeriv_r]
  constructor
  · intro h; exact congrArg Prod.snd h
  · intro h; exact Prod.ext rfl h

lemma ρCLM_Rc (h : Fc 0) : ρCLM isStrongBundleRetraction_Rc zero_mem_Hc h = 0 := rfl

/-- The linear isomorphism `ker Dr(0) = ℝ ⊕ 0 → ker ρ(0) = ℝ`, `(a, 0) ↦ a`, i.e. `Dk(0)` on
`ker Dr(0)` (condition (3)). -/
def kerMap : LinearMap.ker ((scDeriv Hc (r Rc) (0 : Ec 1) : Ec 0 →L[ℝ] Ec 0) : Ec 0 →ₗ[ℝ] Ec 0)
    →ₗ[ℝ] LinearMap.ker ((ρCLM isStrongBundleRetraction_Rc zero_mem_Hc : Fc 0 →L[ℝ] Fc 0) :
      Fc 0 →ₗ[ℝ] Fc 0) :=
  LinearMap.codRestrict _ ((Lg : Ec 0 →ₗ[ℝ] Fc 0).comp (Submodule.subtype _))
    fun _ => LinearMap.mem_ker.2 (ρCLM_Rc _)

lemma kerMap_bijective : Bijective kerMap := by
  constructor
  · intro v w hvw
    have h1 : (v : Ec 0).1 = (w : Ec 0).1 := congrArg Subtype.val hvw
    have h2 : (v : Ec 0).2 = (w : Ec 0).2 := by
      rw [mem_ker_scDeriv_r.1 v.2, mem_ker_scDeriv_r.1 w.2]
    exact Subtype.ext (Prod.ext h1 h2)
  · intro h
    exact ⟨⟨(h.1, 0), mem_ker_scDeriv_r.2 rfl⟩, Subtype.ext rfl⟩

/-- `g(a, b) = a` is a filled version (whole-chart) of the zero section of `K → O = {0} × ℝ`. -/
theorem isFilledVersion_gc :
    IsFilledVersion relOpen_Hc isStrongBundleRetraction_Rc zero_mem_Hc 0 gc := by
  refine ⟨isScSmooth_gc, ⟨Eventually.of_forall fun x hx => ?_,
    Eventually.of_forall fun y hy hfix => ⟨y, hy, Prod.ext hfix.symm rfl⟩,
    (fillDefect_isScSmooth relOpen_Hc isStrongBundleRetraction_Rc isScSmooth_gc).isSc1,
    ⟨(LinearEquiv.ofBijective kerMap kerMap_bijective).toContinuousLinearEquiv, fun v => ?_⟩⟩⟩
  · obtain ⟨u, -, rfl⟩ := hx; rfl
  · change Lg (v : Ec 0) = scDeriv Hc (fillDefect Rc gc) 0 (v : Ec 0)
    rw [fillDefect_gc, scDeriv_g]

lemma zero_mem_O : (0 : Ec 0) ∈ r Rc '' Hc := ⟨0, zero_mem_Hc, rfl⟩

/-- **The corner filling is a 2021 filling** (2021 Definition 3.1.4): `r(0) = 0`; (1) `g = 0` on
`O = {0} × ℝ`; (2) `g(y) = ρ(r(y))g(y) = 0` forces `y ∈ O`; (3) `k = g` and
`Dk(0) : ker Dr(0) = ℝ ⊕ 0 → ker ρ(0) = ℝ` is `(a, 0) ↦ a`. -/
theorem isFilling2021_gc :
    IsFilling2021 relOpen_Hc isStrongBundleRetraction_Rc zero_mem_Hc 0 gc :=
  isFilledVersion_gc.isFilling2021 zero_mem_O

/-- **The base retraction `r(a, b) = (0, b)` is not tame** (2021 Definition 2.5.2 (1) fails):
`d_C(1, 0) = 0` while `d_C(r(1, 0)) = d_C(0) = 1`. -/
theorem not_isTame_r : ¬ (isStrongBundleRetraction_Rc.baseRetraction relOpen_Hc).IsTame := by
  intro h
  have hT := h 1 (rnSc 1) (ScIso.refl _) (by ext; rfl)
  have hp : halfLineOne (rnSc 1) ∈ (isStrongBundleRetraction_Rc.baseRetraction relOpen_Hc).U :=
    fun _ => zero_le_one
  have hdeg := hT.degIndex_apply _ hp
  change degIndex Ec Hc (0 : Ec 0) = degIndex Ec Hc (halfLineOne (rnSc 1)) at hdeg
  rw [degIndex_quadrant zero_mem_Hc, degIndex_quadrant (fun _ => zero_le_one), quadrantDeg_zero]
    at hdeg
  have hq : quadrantDeg (halfLineOne (rnSc 1)) = 0 := by
    simp [quadrantDeg, halfLineOne]
  omega

/-- The corner filling is not a 2017 filling. -/
theorem not_isFilling2017_gc :
    ¬ IsFilling2017 relOpen_Hc isStrongBundleRetraction_Rc zero_mem_Hc 0 gc :=
  fun h => not_isTame_r h.tame

lemma ker_Lg_eq_range_Lr :
    LinearMap.ker (Lg : Ec 0 →ₗ[ℝ] Fc 0) = LinearMap.range (Lr : Ec 0 →ₗ[ℝ] Ec 0) := by
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hv; exact ⟨v, Prod.ext hv.symm rfl⟩
  · rintro ⟨w, rfl⟩; rfl

/-- **The germ is in good position in the chart** (`IsGoodPositionAtGerm`, the chart form of 2021
Definition 3.6.6): `Tf̃(0) : T₀O → K₀ = 0` is onto, and its kernel `T₀O = 0 ⊕ ℝ` is in good
position to the partial cone `T₀O ∩ C = T₀O` in `T₀O`. -/
theorem isGoodPositionAtGerm_gc :
    IsGoodPositionAtGerm relOpen_Hc isStrongBundleRetraction_Rc zero_mem_Hc
      (scDeriv Hc gc (0 : Ec 1)) := by
  rw [scDeriv_g]
  refine ⟨fun y hy => ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := hy
    exact ⟨0, Submodule.zero_mem _, by rw [map_zero]; exact (ρCLM_Rc z).symm⟩
  · rw [scDeriv_r]
    have hsub : ∀ x : LinearMap.ker (Lg : Ec 0 →ₗ[ℝ] Fc 0), (x : Ec 0) ∈ Hc := fun x _ => by
      have : (x : Ec 0).1 = 0 := LinearMap.mem_ker.1 x.2
      rw [this]; exact le_rfl
    refine ⟨ker_Lg_eq_range_Lr.le, ⟨0, ?_⟩, ⊥, bot_le, inf_bot_eq _, ?_, 1, one_pos,
      fun x _ p hp _ => ?_⟩
    · have : (Subtype.val ⁻¹' Hc : Set (LinearMap.ker (Lg : Ec 0 →ₗ[ℝ] Fc 0))) = univ :=
        eq_univ_of_forall hsub
      rw [this, interior_univ]; exact mem_univ _
    · rw [sup_bot_eq, ker_Lg_eq_range_Lr]
    · rw [(Submodule.mem_bot ℝ).1 hp, add_zero]

/-- **`ker Dg(0) = 0 ⊕ ℝ` is not in good position to `C = [0, ∞) × ℝ` in `E`**: a complement `P`
contains some `p` with first coordinate `1` (write `(1, 0) = n + p`), while every good complement
lies in `{a = 0}` (preprint Lemma 3.65 = 2021 Lemma 3.8.8, `lemma_3_8_8`: the index of the first
coordinate is in `Σ`, as `(0, 1) ∈ N ∩ C`). -/
theorem not_isInGoodPosition_gc :
    ¬ IsInGoodPosition Ec Hc (LinearMap.ker (scDeriv Hc gc (0 : Ec 1) : Ec 0 →ₗ[ℝ] Fc 0)) := by
  rw [scDeriv_g]
  rintro ⟨-, P, hP⟩
  obtain ⟨ε, hε, hgood⟩ := hP.exists_eps
  have hv : (((fun _ => 1 : Fin 1 → ℝ), (0 : Fin 1 → ℝ)) : Ec 0) ∈
      LinearMap.ker (Lg : Ec 0 →ₗ[ℝ] Fc 0) ⊔ P := by
    rw [hP.isCompl.sup_eq_top]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hv
  have hy1 : y.1 = 0 := LinearMap.mem_ker.1 hy
  have hz1 : z.1 0 = 1 := by
    have := congrArg (fun q : Ec 0 => q.1 0) hyz
    simp only [Prod.fst_add, Pi.add_apply, hy1] at this
    have h' : (0 : ℝ) + z.1 0 = 1 := this
    linarith
  have h0 : (0 : Fin 1) ∈ vanIdx (coordFun ((ScIso.refl Ec) 0))
      (LinearMap.ker (Lg : Ec 0 →ₗ[ℝ] Fc 0)) := by
    refine (mem_vanIdx _ _).2 ⟨⟨((0 : Fin 1 → ℝ), fun _ => 1), rfl⟩, fun _ => le_rfl, ?_, rfl⟩
    intro h
    have := congrArg (fun q : LinearMap.ker (Lg : Ec 0 →ₗ[ℝ] Fc 0) => (q : Ec 0).2 0) h
    simp at this
  have := lemma_3_8_8 (coordFun ((ScIso.refl Ec) 0)) (LinearMap.ker (Lg : Ec 0 →ₗ[ℝ] Fc 0)) P hε
    (fun x hx p hp hle => hgood x hx p hp hle) hz h0
  rw [coordFun_apply] at this
  change z.1 0 = 0 at this
  rw [hz1] at this
  exact one_ne_zero this

/-- **The tameness hypothesis `hK : (1 − Dr(0))E ⊆ E₀` of `theorem_3_6_8_linear` fails**:
`(1 − Dr(0))(1, 0) = (1, 0) ∉ E₀ = 0 ⊕ ℝ`. -/
theorem not_range_le_minimalSubspace :
    ¬ LinearMap.range (ContinuousLinearMap.id ℝ (Ec 0) - scDeriv Hc (r Rc) (0 : Ec 1) :
        Ec 0 →ₗ[ℝ] Ec 0) ≤ minimalSubspaceWith (ScIso.refl Ec) 0 := by
  intro h
  have hmem := h ⟨((fun _ => 1 : Fin 1 → ℝ), (0 : Fin 1 → ℝ)), rfl⟩
  rw [mem_minimalSubspaceWith] at hmem
  have := hmem 0 rfl
  rw [scDeriv_r] at this
  change (1 : ℝ) - 0 = 0 at this
  norm_num at this

end CornerFilling

open CornerFilling in
/-- **2017 ⟸ 2021 fails** (2021 Definition 3.1.4 versus 2017 Definition 3.4): there is a 2021
filling which is not a 2017 filling (the corner example, `r(a, b) = (0, b)` on `[0, ∞) × ℝ`). -/
theorem exists_isFilling2021_not_isFilling2017 :
    ∃ (E F : ScBanach) (C U : Set (E 0)) (R : E 0 × F 0 → E 0 × F 0)
      (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U)
      (fb g : E 0 → F 0), IsFilling2021 hU hR h0 fb g ∧ ¬ IsFilling2017 hU hR h0 fb g :=
  ⟨Ec, Fc, Hc, Hc, Rc, relOpen_Hc, isStrongBundleRetraction_Rc, zero_mem_Hc, 0, gc,
    isFilling2021_gc, not_isFilling2017_gc⟩

open CornerFilling in
/-- **Where the proof of 2021 Theorem 3.6.8 (p. 138) uses tameness** (2017: Theorem 3.13;
preprint: Theorem 3.54; and with it Theorems 3.1.22, 3.1.26, Corollary 3.1.27, Theorems 3.6.10 and
3.6.11).  The step "`ker Tf̃(0)` in good position to `C₀O` in `T₀O` ⟹ `ker Dg(0)` in good position
to `C` in `E`" uses the sc-complement `ker Dr(0) ⊆ E₀` of `T₀O` which Proposition 2.5.3 gives for a
tame retract — in the project, the hypothesis `hK` of `theorem_3_6_8_linear`.  With a 2021 filling
over a non-tame retraction it fails: in the corner example every other hypothesis of
`theorem_3_6_8_linear` holds (`0 ∈ O`, `f̂(0) = 0`, `f̂` a section of `K`, `g` sc¹ on `U` with
`Dg(0)`, good position of the germ in the chart), `Dg(0)` is onto, but `r` is not tame, `hK`
fails, and `ker Dg(0)` is not in good position to `C`. -/
theorem theorem_3_6_8_tame_step :
    IsFilling2021 relOpen_Hc isStrongBundleRetraction_Rc zero_mem_Hc 0 gc ∧
    ¬ (isStrongBundleRetraction_Rc.baseRetraction relOpen_Hc).IsTame ∧
    (0 : Ec 0) ∈ r Rc '' Hc ∧ (0 : Ec 0 → Fc 0) 0 = 0 ∧
    (∀ x ∈ r Rc '' Hc, (x, (0 : Ec 0 → Fc 0) x) ∈ Rc '' (Hc ×ˢ univ)) ∧
    IsSc1GermWith (ScNbhdGerm.ofSet relOpen_Hc.relOpen zero_mem_Hc) gc (scDeriv Hc gc) ∧
    Hc = (ScIso.refl Ec) 0 ⁻¹' quadrant 1 (rnSc 1) 0 ∧
    IsGoodPositionAtGerm relOpen_Hc isStrongBundleRetraction_Rc zero_mem_Hc
      (scDeriv Hc gc (0 : Ec 1)) ∧
    Surjective (scDeriv Hc gc (0 : Ec 1)) ∧
    ¬ LinearMap.range (ContinuousLinearMap.id ℝ (Ec 0) - scDeriv Hc (r Rc) (0 : Ec 1) :
        Ec 0 →ₗ[ℝ] Ec 0) ≤ minimalSubspaceWith (ScIso.refl Ec) 0 ∧
    ¬ IsInGoodPosition Ec Hc (LinearMap.ker (scDeriv Hc gc (0 : Ec 1) : Ec 0 →ₗ[ℝ] Fc 0)) := by
  refine ⟨isFilling2021_gc, not_isTame_r, zero_mem_O, rfl, ?_,
    isScSmooth_gc.isSc1.isSc1GermWith_ofSet relOpen_Hc.relOpen zero_mem_Hc, by ext; rfl,
    isGoodPositionAtGerm_gc, ?_, not_range_le_minimalSubspace, not_isInGoodPosition_gc⟩
  · rintro x ⟨u, -, rfl⟩
    exact ⟨(r Rc u, 0), ⟨fun _ => le_rfl, mem_univ _⟩, rfl⟩
  · rw [scDeriv_g]
    intro h
    exact ⟨(h, 0), rfl⟩

/-! ### Definitions 3.1.11 = 3.6.3 and 3.1.16 = 3.6.4 with the 2021 filling -/

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

namespace StrongBundle

variable (B) in
/-- **2021 Definition 3.6.3, p. 135 (= Definition 3.1.11, p. 96)** (2017: Definitions 3.14 and 3.7;
preprint: Definitions 3.50 and 3.11), with the 2021 filling: `(f, x₀)` is an **sc-Fredholm germ**
if `x₀` is smooth and there is a strong bundle chart centred at `x₀` in which the principal part has
a filling `g` (`IsFilling2021`, no tameness) and a local sc⁺-section `s` with `s(0) = g(0)` such
that `g − s` is conjugated near `0` to a basic germ. -/
def IsScFredholmGerm2021 (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFilling2021 c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u))

variable (B) in
/-- **The 2017 sc-Fredholm germ** (2017 Definitions 3.7 and 3.14, with the 2017 filling of
Definitions 3.4/3.13: a tame retraction), for comparison with 2021 Definitions 3.1.11 and 3.6.3. -/
def IsScFredholmGerm2017 (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFilling2017 c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u))

variable (B) in
/-- **2021 Definition 3.6.4, p. 135 (= Definition 3.1.16, p. 97)** (2017: Definitions 3.15 and
3.8; preprint: Definitions 3.51 and 3.14), with the 2021 filling: `f` is sc-smooth, regularizing,
and an sc-Fredholm germ (`IsScFredholmGerm2021`) at every smooth point. -/
structure IsScFredholmSection2021 (f : X → Y) : Prop where
  isScSmooth : B.IsScSmoothSection f
  regularizing : ∀ m, ∀ x ∈ PX.levelSet m, f x ∈ B.doubleLevel m (m + 1) → x ∈ PX.levelSet (m + 1)
  germ : ∀ x ∈ PX.smoothSet, B.IsScFredholmGerm2021 f x

omit [T2Space Y] [ParacompactSpace Y] in
lemma zero_mem_O_of_chart {c : StrongBundleChart PX P} {x₀ : X} (hxV : x₀ ∈ c.φ.source)
    (hφ0 : c.φ x₀ = 0) : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := by
  rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model x₀ hxV

/-- **The 2021 sc-Fredholm germ is the project's `IsScFredholmGerm`** (the germ reading of
preprint Definition 3.11, which never asked for tameness); `r(0) = 0` holds in a chart centred at
`x₀`. -/
theorem isScFredholmGerm2021_iff {x₀ : X} :
    B.IsScFredholmGerm2021 f x₀ ↔ B.IsScFredholmGerm f x₀ := by
  constructor
  · rintro ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩
    exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill.isFillingGerm, hsm, hs0, hconj⟩
  · rintro ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩
    exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill.isFilling2021 (zero_mem_O_of_chart hxV hφ0),
      hsm, hs0, hconj⟩

/-- **The 2017 sc-Fredholm germ is the project's `IsScFredholmGermTame`** (germ data in a
compatible chart with a tame base retraction). -/
theorem isScFredholmGerm2017_iff {x₀ : X} :
    B.IsScFredholmGerm2017 f x₀ ↔ B.IsScFredholmGermTame f x₀ := by
  constructor
  · rintro ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩
    exact ⟨hs, c, ⟨hc, hfill.tame⟩, hxV, hφ0, h0, g, s, hfill.isFilling2021.isFillingGerm, hsm,
      hs0, hconj⟩
  · rintro ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩
    exact ⟨hs, c, hc.1, hxV, hφ0, h0, g, s,
      ⟨hfill.isFilling2021 (zero_mem_O_of_chart hxV hφ0), hc.2⟩, hsm, hs0, hconj⟩

/-- **2017 ⟹ 2021** for sc-Fredholm germs.  (The converse does not hold:
`UntamedCorner.isScFredholmGerm2021_not_2017`; Findings, Chapter 3, items 353, 388.) -/
theorem IsScFredholmGerm2017.isScFredholmGerm2021 {x₀ : X} (h : B.IsScFredholmGerm2017 f x₀) :
    B.IsScFredholmGerm2021 f x₀ :=
  isScFredholmGerm2021_iff.2 (isScFredholmGerm2017_iff.1 h).isScFredholmGerm

/-- **The 2021 sc-Fredholm section is the project's `IsScFredholmSection`.** -/
theorem isScFredholmSection2021_iff :
    B.IsScFredholmSection2021 f ↔ B.IsScFredholmSection f :=
  ⟨fun h => ⟨h.isScSmooth, h.regularizing, fun x hx => isScFredholmGerm2021_iff.1 (h.germ x hx)⟩,
    fun h => ⟨h.isScSmooth, h.regularizing, fun x hx => isScFredholmGerm2021_iff.2 (h.germ x hx)⟩⟩

end StrongBundle

/-! ### The 2021 theorems whose proofs do not use tameness -/

open StrongBundle

/-- **2021 Theorem 3.1.13, p. 97 (local compactness for sc-Fredholm germs)** (2017: Theorem 3.1;
preprint: Theorem 3.12), for the 2021 definitions: `theorem_3_1_13_preprint`. -/
theorem theorem_3_1_13 (hf : IsSection P f) {x₀ : X} (hg : B.IsScFredholmGerm2021 f x₀)
    (hx₀ : IsZeroAt P f x₀) :
    ∃ O : ℕ → Set X, (∀ i, IsOpen (O i)) ∧ (∀ i, x₀ ∈ O i) ∧ (∀ i, O (i + 1) ⊆ O i) ∧
      ∀ i, ∃ K : Set (PX.Level i), IsCompact K ∧
        PX.levelVal i '' K = closure {x ∈ O i | IsZeroAt P f x} :=
  theorem_3_1_13_preprint hf (isScFredholmGerm2021_iff.1 hg) hx₀

/-- **2021 Corollary 3.1.15, p. 97** (2017: Corollary 3.1; preprint: Corollary 3.13), for the 2021
definitions: `corollary_3_1_15_preprint`. -/
theorem corollary_3_1_15 (hf : IsSection P f) {x₀ : X} (hg : B.IsScFredholmGerm2021 f x₀)
    (hx₀ : IsZeroAt P f x₀) {x : ℕ → X} (hx : ∀ n, IsZeroAt P f (x n))
    (hlim : Tendsto x atTop (𝓝 x₀)) (m : ℕ) :
    ∃ y₀ : PX.Level m, PX.levelVal m y₀ = x₀ ∧ ∃ y : ℕ → PX.Level m,
      (∀ᶠ n in atTop, PX.levelVal m (y n) = x n) ∧ Tendsto y atTop (𝓝 y₀) :=
  corollary_3_1_15_preprint hf (isScFredholmGerm2021_iff.1 hg) hx₀ hx hlim m

/-- **2021 Theorem 3.1.18, p. 98 (stability under sc⁺-perturbations)** (2017: Theorem 3.2;
preprint: Theorem 3.15), for the 2021 definitions: `theorem_3_1_18_preprint`. -/
theorem theorem_3_1_18 {s : X → Y} (hf : B.IsScFredholmSection2021 f)
    (hs : B.IsScPlusSection s) : B.IsScFredholmSection2021 (sectionAdd P f s) :=
  isScFredholmSection2021_iff.2 (theorem_3_1_18_preprint (isScFredholmSection2021_iff.1 hf) hs)

/-- **2021 Theorem 3.1.21, p. 100 (parametrized perturbations)** (2017: Theorem 3.3; preprint:
Theorem 3.18), for the 2021 definitions: `theorem_3_1_21'`. -/
theorem theorem_3_1_21 {n : ℕ} (hf : B.IsScFredholmSection2021 f) {s : Fin n → X → Y}
    (hs : ∀ i, B.IsScPlusSection (s i)) :
    haveI := MPolyfold.paracompactSpace_prod (rnPolyfold n) PX
    haveI := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin n → ℝ) × X → X))
      ((rnPolyfold n).prod PX) B
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmSection2021
      (paramSection f hf.isScSmooth.1 s fun i => (hs i).1) := by
  have := MPolyfold.paracompactSpace_prod (rnPolyfold n) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin n → ℝ) × X → X))
    ((rnPolyfold n).prod PX) B
  exact isScFredholmSection2021_iff.2 (theorem_3_1_21_preprint (isScFredholmSection2021_iff.1 hf) hs)

/-- **2021 Proposition 3.6.5, p. 135 (`Tf(x)` is sc-Fredholm at a zero)** (2017: Proposition 3.5;
preprint: Proposition 3.52), for the 2021 definitions: `proposition_3_6_5_preprint`. -/
theorem proposition_3_6_5 (hf : IsSection P f) {x₀ : X} (hg : B.IsScFredholmGerm2021 f x₀)
    (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
      (_ : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
      (G : ScNbhdGerm c.φ.model.E c.φ.model.C) (_ : G.U 0 ⊆ c.U) (_ : IsScSmoothGerm G g)
      (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0) (_ : IsSc1GermWith G g Dg)
      (h1 : ∀ x, ρCLM c.isRetraction h0 (Dg 0 (scDeriv c.U (r c.R) 0 x)) =
        Dg 0 (scDeriv c.U (r c.R) 0 x)) (n N : ℕ),
      ContinuousLinearMap.IsFredholm (Dg 0) ∧ fredholmIndex (Dg 0) = n - N ∧
      ContinuousLinearMap.IsFredholm
        (fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0) (Dg 0) h1) ∧
      fredholmIndex (fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0) (Dg 0) h1) =
        n - N :=
  proposition_3_6_5_preprint hf (isScFredholmGerm2021_iff.1 hg) hx₀

/-! ### Satisfiability of the bundle-level definitions -/

/-- **The 2021 sc-Fredholm section is satisfiable**: the graph section of a `C^∞` map
`φ : ℝⁿ → ℝᵏ`, for the trivial bundle `bundleEven n k` of `TameGermData.lean`. -/
theorem isScFredholmSection2021_graphSection {n k : ℕ} {φ : (Fin n → ℝ) → (Fin k → ℝ)}
    (hφ : ContDiff ℝ ∞ φ) :
    (TrivialBundle.bundleEven n k).IsScFredholmSection2021 (TrivialBundle.graphSection φ) :=
  isScFredholmSection2021_iff.2
    (TrivialBundle.isScFredholmSectionTame_graphSection_even hφ).toIsScFredholmSection

/-- **The 2017 sc-Fredholm germ is satisfiable** (same example, tame germ data). -/
theorem isScFredholmGerm2017_graphSection {n k : ℕ} {φ : (Fin n → ℝ) → (Fin k → ℝ)}
    (hφ : ContDiff ℝ ∞ φ) (x₀ : Fin n → ℝ) :
    (TrivialBundle.bundleEven n k).IsScFredholmGerm2017 (TrivialBundle.graphSection φ) x₀ :=
  isScFredholmGerm2017_iff.2
    ((TrivialBundle.isScFredholmSectionTame_graphSection_even hφ).germTame x₀
      (by rw [TrivialBundle.rnPolyfold_smoothSet]; exact mem_univ x₀))

end Bundle

/-! ### Proposition 3.1.5 for the 2021 filling -/

section Filler

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0} {G₁ : ScNbhdGerm E C}

/-- **2021 Proposition 3.1.5, p. 93 (the filler)** (2017: Proposition 3.1; preprint: Proposition
3.5), for the 2021 filling: if `g` fills the section `f̂` of `K → O` and `f̂(0) = 0`, then (1)
`Tf̂(0) : T₀O → K₀` is onto iff `Dg(0)` is, (2) one is Fredholm iff the other is, with equal
indices (`IsFillingGerm.proposition_3_1_5`; `0 ∈ O` from `r(0) = 0`, `g(0) = 0` from (1)). -/
theorem proposition_3_1_5 (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) {fb g : E 0 → F 0}
    (hfg : IsFilling2021 hU hR h0 fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) (hG : G₁.U 0 ⊆ U)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G₁ g Dg) :
    ∃ h1 : ∀ x, ρCLM hR h0 (Dg 0 (scDeriv U (r R) 0 x)) = Dg 0 (scDeriv U (r R) 0 x),
      (Surjective (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1) ↔
          Surjective (Dg 0)) ∧
        (ContinuousLinearMap.IsFredholm
            (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1) ↔
          ContinuousLinearMap.IsFredholm (Dg 0)) ∧
        fredholmIndex (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1) =
          fredholmIndex (Dg 0) := by
  have h0O : (0 : E 0) ∈ r R '' U := ⟨0, h0, hfg.r_zero⟩
  have hg0 : g 0 = 0 := by rw [← hfg.eq_on.self_of_nhds h0O, hfb0]
  exact hfg.isFillingGerm.proposition_3_1_5 hU hR h0 hg0 h0O hfK hG hg

end Filler

/-! ### Theorem 3.5.1 (local regularity and compactness), with the 2021 sequential conclusion -/

section LocalRegularity

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P} {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)}
  {B : P × W 0 → W 0} {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  {h : P × W 0 → Q × W 0} {s : P × W 0 → Q × W 1}

/-- A zero of `h + s` (`h` basic) solves `w = B(a, w) − P∘s(a, w)` (the `W`-component). -/
lemma IsBasicGerm.solves (hh : IsBasicGerm Ct G h B) {x : (ScBanach.paramProd P W) 0}
    (hx : x ∈ {x ∈ G.U 0 | h x + (ScBanach.paramProd Q W).toBase 1 (s x) = 0}) :
    x ∈ G.U 0 ∧ x.2 = B x - W.toBase 1 (s x).2 := by
  refine ⟨hx.1, ?_⟩
  have h2 := congrArg Prod.snd hx.2
  rw [ScBanach.paramProd_toBase] at h2
  change (h x).2 + W.toBase 1 (s x).2 = 0 at h2
  rw [hh.snd_eq x hx.1] at h2
  have : x.2 - B x + W.toBase 1 (s x).2 = 0 := h2
  rw [sub_add_eq_add_sub, sub_eq_zero] at this
  exact eq_sub_of_add_eq this

/-- **2021 Theorem 3.5.1, p. 118 (local regularity and compactness)** (2017: Theorem 3.11;
preprint: Theorem 3.40; the sequential conclusion is new in 2021).  Let `h : O(C̃ ⊕ W, 0) → Q ⊕ W`
be a basic germ on the germ `G` (`C̃` closed, `C = C̃ × W`, `U = G₀`) and `s` an sc⁺-germ on `G`
with `s(0) = 0`; let `S = {x ∈ U | h(x) + s(x) = 0}`.  Then:
* there are nested relatively open neighbourhoods `O(0) ⊃ O(1) ⊃ …` of `0` in `C`, inside `U`,
  with `cl(S ∩ O(m)) ⊆ C_m` (the closure lies in `C` and in the image of `E_m`);
* **(new in 2021)** if `x_k ∈ S` and `x_k → 0` in `E₀`, then for every `m` there are `y_k ∈ E_m`
  with `ι_m(y_k) = x_k` for `k` large (so `x_k ∈ C_m`) and `y_k → 0` in `E_m`. -/
theorem theorem_3_5_1 (hh : IsBasicGerm Ct G h B) (hCt : IsClosed Ct)
    (hs : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := (ScBanach.paramProd Q W).shift) G s)
    (hs0 : s 0 = 0) :
    (∃ O : ℕ → Set ((ScBanach.paramProd P W) 0),
      (∀ m, ∃ V, IsOpen V ∧ O m = V ∩ G.U 0) ∧ (∀ m, (0 : P × W 0) ∈ O m) ∧
      (∀ m, O (m + 1) ⊆ O m) ∧
      ∀ m, ∀ x ∈ closure ({x ∈ G.U 0 | h x + (ScBanach.paramProd Q W).toBase 1 (s x) = 0} ∩ O m),
        x ∈ Ct ×ˢ (univ : Set (W 0)) ∧ x ∈ range ((ScBanach.paramProd P W).toBase m)) ∧
    ∀ x : ℕ → (ScBanach.paramProd P W) 0,
      (∀ k, x k ∈ {x ∈ G.U 0 | h x + (ScBanach.paramProd Q W).toBase 1 (s x) = 0}) →
      Tendsto x atTop (𝓝 0) → ∀ m, ∃ y : ℕ → (ScBanach.paramProd P W) m,
        (∀ᶠ k in atTop, (ScBanach.paramProd P W).toBase m (y k) = x k) ∧ Tendsto y atTop (𝓝 0) := by
  have hs' : IsSc0Germ (E := ScBanach.paramProd P W) (F := (ScBanach.paramProd Q W).shift) G s :=
    hs 0
  -- the `W`-component of `s` is an sc⁺-germ (level-wise continuous into `W¹`)
  have hsW : IsSc0Germ (E := ScBanach.paramProd P W) (F := W.shift) G (fun x => (s x).2) :=
    (ScBanach.sndOp (ScBanach.const Q) W.shift).isSc0Germ _ |>.comp hs' (G.mapsToGerm_full _)
  have hsW0 : (s 0).2 = 0 := by rw [hs0]; rfl
  refine ⟨?_, fun x hx hlim m =>
    corollary_3_1_15_local hh.contraction hCt hsW hsW0 (fun k => hh.solves (hx k)) hlim m⟩
  obtain ⟨O, hO, h0, hnest, hK⟩ := theorem_3_1_13_local hh hCt hs' hs0
  have hCcl : IsClosed (Ct ×ˢ (univ : Set (W 0))) := hCt.prod isClosed_univ
  refine ⟨fun m => O m ∩ G.U 0, fun m => ⟨O m, hO m, rfl⟩, fun m => ⟨h0 m, G.zero_mem 0⟩,
    fun m => inter_subset_inter_left _ (hnest m), fun m x hx => ⟨?_, ?_⟩⟩
  · refine hCcl.closure_subset_iff.2 (fun y hy => ?_) hx
    have := G.U_subset 0 hy.1.1
    rw [ScBanach.lvlSet_zero] at this
    exact this
  · obtain ⟨K, -, hKeq⟩ := hK m
    have hx' : x ∈ closure ({x ∈ G.U 0 | h x + (ScBanach.paramProd Q W).toBase 1 (s x) = 0} ∩
        O m) :=
      closure_mono (inter_subset_inter_right _ inter_subset_left) hx
    rw [hKeq] at hx'
    obtain ⟨z, -, rfl⟩ := hx'
    exact ⟨z, rfl⟩

end LocalRegularity

end Polyfold
