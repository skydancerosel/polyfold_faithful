import GWMemoir.ReductionsRegularity
import Polyfold.Chapter17.BundleModelStructure

/-!
# The strong polyfold bundle `p : W → Z` (Memoir Theorem 1.10)

HWZ, *Applications of Polyfold Theory I* (Memoirs AMS 248, no. 1179), §3.6 (pp. 91–98): the lifted
families `q̂ ↦ α̂_q̂` over the good uniformizing families (built with the hat gluing, Theorem 2.50,
and the splicing `ρ_a`), the strong bundle `E → X` over the object M-polyfold, the structure map
`μ : X ₛ×_p E → E` of **Proposition 3.39** (a strong bundle map covering `t`, a surjective local
sc-diffeomorphism, linear on the fibres, with `μ(1, e) = e` and `μ(Φ ∘ Ψ, e) = μ(Φ, μ(Ψ, e))`),
and the homeomorphism `|Γ| : |E| → W` covering `|p| : |X| → Z`, which give **Theorem 1.10**.

Read through the book (2021): a vector bundle GCT `P : E → C` over the GCT of the stable maps
(Definition 17.7.1), a compatible strong bundle uniformizer construction (Definition 17.7.3; the
lifted families), the strong polyfold bundle construction of Definition 17.7.4, its bundle model
(§17.7, `bundleModelStructure`), and Definition 16.3.1 / 16.3.4 for `|P| : |E| → |C|`.

## What is formalized

* `Proposition_3_39 Fb`: for a strong bundle uniformizer construction `F̄` compatible with the
  polyfold structure `S`, the structure map of the transition sets, `t̄ : M(Ψ̄, Ψ̄') = s*K → K'`,
  is a strong bundle map covering `t` and a local strong bundle isomorphism.  This is
  Proposition 3.39 (1) on the transition sets; (2), (3) hold for the pull-back form
  (`modelMu_unit`, `modelMu_comp` of the book).  `ofProposition_3_39`: the strong polyfold
  bundle construction of Definition 17.7.4.
* `HasBundleUniformizers Fb`: every object `α` carries a strong bundle uniformizer of `F̄(α)`
  (the memoir lifts every good uniformizing family); `exists_bundleCoveringFamily`: then a
  covering family of strong bundle uniformizers exists (index set `|C|`).
* `bundleOf hZ hE Q c` (`bundleModelBundle` with the local regularity property from
  `isLRLocal_of_isEffective`), `bundleOf_eq` (independent of the covering family),
  `polyfold_bundleOf` (its base is the polyfold `c_C` of `S`, Theorem 17.1.26).
* `strongPolyfoldBundle_of_3_39`: for a polyfold construction with (ZHOU) that is effective,
  Proposition 3.39 and bundle uniformizers at every object give a strong polyfold bundle on
  `|P| : |E| → |C|` over `c_C`, independent of the covering family; witness
  `strongPolyfoldBundle_of_3_39_reflection` (the reflection bundle of the book, with `−1` acting
  on the fibre by `−1`).
* **`memoir_theorem_1_10`**: with the named propositions of `memoir_polyfold_structure`
  (Proposition 3.10, Theorems 3.13, 3.22, 1.6 (second countability)) and, for the bundle,
  Proposition 3.39 and the lifted families, the strong polyfold bundle structure on
  `|P| : |E| → Z`.

## Readings

* The memoir constructs `μ` directly (Proposition 3.39) and does not go through bundle
  transition data (2021 Definition 19.6.4) and Theorem 19.6.13.  Definition 17.7.4 asks for the
  same data as Proposition 3.39 (1) in the pull-back form `M(Ψ̄, Ψ̄') = s*K`, so the named
  proposition is stated there and Theorem 19.6.13 is not used.  (The book's library has no map
  from a basic strong bundle construction of §19.6 to a strong polyfold bundle construction of
  §17.7: the Banach functors of the two chapters are different structures.)
* The local regularity property of Definition 16.3.1 is not in the memoir's Definition 2.38;
  it follows from (ZHOU) and effectiveness (Propositions 7.4.22, 8.4.3 of the book), both of
  which `memoir_polyfold_structure` gives for `Z`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace GWMemoir

open Polyfold Polyfold.GCT Polyfold.GCT.VectorBundle

universe u

section General

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}

open StrongBundleUniformizerConstruction in
/-- **Memoir Proposition 3.39 (1)**, on the transition sets (p. 95): the structure map
`t̄ : M(Ψ̄, Ψ̄') → K'` (in the pull-back form `s*K`) is a strong bundle map covering `t` and a
local strong bundle isomorphism. -/
structure Proposition_3_39 (Fb : V.StrongBundleUniformizerConstruction S) : Prop where
  isStrongBundleMap : ∀ Ψ Ψ' : Fb.Unif,
    (Fb.transBundle Ψ Ψ').IsStrongBundleMap Ψ'.1.B (fun a => a.tgt) (Fb.transT Ψ Ψ')
  isLocalStrongBundleIso : ∀ (Ψ Ψ' : Fb.Unif) (a : S.Tr (Fb.baseUnif Ψ) (Fb.baseUnif Ψ')),
    ∃ (W : Set (S.Tr (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))) (W' : Set Ψ'.1.base.O), a ∈ W ∧
      (Fb.transBundle Ψ Ψ').IsStrongBundleIsoOn Ψ'.1.B (isStrongBundleMap Ψ Ψ') W W'

/-- The strong polyfold bundle construction (Definition 17.7.4) of Proposition 3.39. -/
def ofProposition_3_39 (Fb : V.StrongBundleUniformizerConstruction S)
    (h : Proposition_3_39 Fb) : V.StrongPolyfoldBundleConstruction S where
  toStrongBundleUniformizerConstruction := Fb
  isStrongBundleMap_trans := h.isStrongBundleMap
  isLocalStrongBundleIso_trans := h.isLocalStrongBundleIso

/-- A strong polyfold bundle construction satisfies Proposition 3.39. -/
theorem proposition_3_39_of
    (Q : V.StrongPolyfoldBundleConstruction S) :
    Proposition_3_39 Q.toStrongBundleUniformizerConstruction :=
  ⟨Q.isStrongBundleMap_trans, Q.isLocalStrongBundleIso_trans⟩

/-- Every object carries a strong bundle uniformizer of `F̄` (the lifted families of §3.6). -/
def HasBundleUniformizers (Fb : V.StrongBundleUniformizerConstruction S) : Prop :=
  ∀ α, (Fb.F α).Nonempty

open StrongPolyfoldBundleConstruction in
/-- **A covering family of strong bundle uniformizers exists** when every object carries one:
for every class `z ∈ |C|` a member of `F̄(α)`, `α` a representative of `z`. -/
theorem exists_bundleCoveringFamily (Q : V.StrongPolyfoldBundleConstruction S)
    (h : HasBundleUniformizers Q.toStrongBundleUniformizerConstruction) :
    Nonempty Q.BundleCoveringFamily := by
  classical
  let Ψ : C.toGroupoidStr.OrbitSpace → Q.Unif := fun z =>
    ⟨(h (Quotient.out z)).some, Quotient.out z, (h (Quotient.out z)).some_mem⟩
  refine ⟨⟨C.toGroupoidStr.OrbitSpace, Ψ, eq_univ_of_forall fun z => mem_iUnion.2 ⟨z, ?_⟩⟩⟩
  have hat := S.isAt _ _ (Q.base_mem _ _ (h (Quotient.out z)).some_mem)
  have := (Q.modelBase Ψ z).1.mem_footprint_of_isAt hat
  rwa [show C.toGroupoidStr.π (Quotient.out z) = z from Quotient.out_eq z] at this

variable (hZ : S.IsZhou) (hE : S.IsEffective) (Q : V.StrongPolyfoldBundleConstruction S)

/-- **The strong polyfold bundle `|P| : |E| → |C|` of a covering family** (Definition 16.3.4 for
the bundle model of §17.7), with the local regularity property from (ZHOU) and effectiveness. -/
def bundleOf (c : Q.BundleCoveringFamily) : StrongPolyfoldBundle V.proj.orbitMap :=
  Q.bundleModelBundle hZ c (StrongPolyfoldBundleConstruction.isLRLocal_of_isEffective hZ hE c)

/-- `bundleOf` does not depend on the covering family. -/
theorem bundleOf_eq (c c' : Q.BundleCoveringFamily) : bundleOf hZ hE Q c = bundleOf hZ hE Q c' :=
  Q.bundleModelBundle_eq hZ c c' _ _

/-- The base of `bundleOf` is the polyfold `c_C` of `S` (Theorem 17.1.26). -/
theorem polyfold_bundleOf (c : Q.BundleCoveringFamily) :
    (bundleOf hZ hE Q c).polyfold = S.polyfoldClass hZ :=
  S.polyfoldClass_eq hZ c.base

/-- **Proposition 3.39 and the lifted families give a strong polyfold bundle** over the polyfold
`c_C` of an effective polyfold construction with (ZHOU), independent of the covering family. -/
theorem strongPolyfoldBundle_of_3_39 (Fb : V.StrongBundleUniformizerConstruction S)
    (h339 : Proposition_3_39 Fb) (hF : HasBundleUniformizers Fb) :
    ∃ W : StrongPolyfoldBundle V.proj.orbitMap, W.polyfold = S.polyfoldClass hZ ∧
      ∀ c : (ofProposition_3_39 Fb h339).BundleCoveringFamily,
        W = bundleOf hZ hE (ofProposition_3_39 Fb h339) c := by
  obtain ⟨c⟩ := exists_bundleCoveringFamily (ofProposition_3_39 Fb h339) hF
  exact ⟨bundleOf hZ hE _ c, polyfold_bundleOf hZ hE _ c, fun c' => bundleOf_eq hZ hE _ c c'⟩

end General

/-! ### Witness: the reflection bundle -/

section Witness

open PolyfoldConstruction ReflectionBundle

/-- **The hypotheses of `strongPolyfoldBundle_of_3_39` hold in a non-degenerate case**: the
reflection bundle `ℝ × ℝ → ℝ` over `ℤ/2 ⋉ ℝ` of the book (non-trivial isotropy at `0`, acting on
the fibre by `−1`) satisfies Proposition 3.39 and has bundle uniformizers at every object. -/
theorem strongPolyfoldBundle_of_3_39_reflection :
    ∃ W : StrongPolyfoldBundle reflV.proj.orbitMap,
      W.polyfold = reflectionConstruction.polyfoldClass reflection_isZhou ∧
      ∀ c : (ofProposition_3_39 reflQ.toStrongBundleUniformizerConstruction
          (proposition_3_39_of reflQ)).BundleCoveringFamily,
        W = bundleOf reflection_isZhou reflection_isEffective _ c :=
  strongPolyfoldBundle_of_3_39 reflection_isZhou reflection_isEffective _ (proposition_3_39_of reflQ)
    fun _ => ⟨_, mem_singleton _⟩

end Witness

/-! ### Memoir Theorem 1.10 -/

section GW

open GroupoidalCategory GroupoidalCategory.BasicConstruction

variable {C : GroupoidalCategory.{1}} {U : C.UniformizerConstruction} {CS : CSPred U}
  (h310 : U.HasClassUniformizers) (H : Theorem_3_13 U CS) (hCS : CSClosed U CS)
  (hPF : PointFinite U)
  (h322 : Theorem_3_22 U (gwTransitionData H hCS hPF))
  (h16 : Theorem_1_6_sc U (gwTransitionData H hCS hPF) h310)

include h322 h16 in
/-- The metrizable natural topology of `Z` (Theorems 3.22 and 1.6). -/
theorem gwMetrizable :
    @TopologicalSpace.MetrizableSpace C.OrbitSpace
      ((basicOf U (gwTransitionData H hCS hPF)).natTop h310) :=
  metrizable_of_theorem_3_22 U _ h310 h322 h16

/-- **The GCT `Z` of stable curves** with its natural topology (Theorem 19.5.3 (1)). -/
abbrev gwGCT : GCT.{1} :=
  (basicOf U (gwTransitionData H hCS hPF)).toGCTOfMetrizable h310 (gwMetrizable h310 H hCS hPF h322 h16)

/-- **The polyfold construction of `Z`** (Theorem 19.5.3 (2)). -/
abbrev gwPolyfoldConstruction : (gwGCT h310 H hCS hPF h322 h16).PolyfoldConstruction :=
  toPolyfoldConstruction (gwMetrizable h310 H hCS hPF h322 h16)

variable {h310 H hCS hPF h322 h16}

/-- **Memoir Theorem 1.10, from the named propositions** (§3.6, pp. 91–98, through 2021
Definitions 17.7.4, 16.3.1, 16.3.4): with Proposition 3.10, Theorems 3.13, 3.22, 1.6 (second
countability) and the faithfulness of the actions (the hypotheses of `memoir_polyfold_structure`),
and for the bundle a vector bundle GCT `P : E → Z` with a compatible strong bundle uniformizer
construction `F̄` (the lifted families) satisfying Proposition 3.39, the bundle `|P| : |E| → Z`
carries a strong polyfold bundle structure over the polyfold structure of `Z`, independent of
the covering family. -/
theorem memoir_theorem_1_10
    (hTF : ∀ (α : C.Obj), ∀ Ψ ∈ U.F α, ∀ y : Ψ.P.SmoothLevel, IsTangentFaithfulAt Ψ y)
    (hLF : ∀ (α : C.Obj), ∀ Ψ ∈ U.F α, IsLocallyFaithful Ψ)
    {V : (gwGCT h310 H hCS hPF h322 h16).VectorBundle}
    (Fb : V.StrongBundleUniformizerConstruction (gwPolyfoldConstruction h310 H hCS hPF h322 h16))
    (h339 : Proposition_3_39 Fb) (hF : HasBundleUniformizers Fb) :
    ∃ (hZ : (gwPolyfoldConstruction h310 H hCS hPF h322 h16).IsZhou)
      (W : StrongPolyfoldBundle V.proj.orbitMap),
      W.polyfold = (gwPolyfoldConstruction h310 H hCS hPF h322 h16).polyfoldClass hZ ∧
      ∀ c : (ofProposition_3_39 Fb h339).BundleCoveringFamily,
        W = bundleOf hZ (isEffective_toPolyfoldConstruction _ hLF) _ c := by
  have hz := isZhou_of_forall_isTangentFaithfulAt (basicOf U (gwTransitionData H hCS hPF)) h310 hTF
  have hZ := proposition_19_5_7 (gwMetrizable h310 H hCS hPF h322 h16) hz
  exact ⟨hZ, strongPolyfoldBundle_of_3_39 hZ (isEffective_toPolyfoldConstruction _ hLF) Fb h339 hF⟩

end GW

end GWMemoir
