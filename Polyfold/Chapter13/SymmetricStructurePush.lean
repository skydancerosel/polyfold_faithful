import Polyfold.Chapter13.MultisectionPullback
import Polyfold.Chapter10.EquivalenceLR

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.4, pp. 625–626: the local push-forward of symmetric sc⁺-section structures behind
**Theorem 13.4.3** (2017: Theorem 13.4).

# Pushing local symmetric structures along a strong bundle equivalence

## The text, paraphrased

(Proof of Theorem 13.4.3) For `y = F(x_y)` the structure on `U'(y) = F(U(x_y))` is
`s'ʸᵢ = Φ ∘ s^{x_y}ᵢ ∘ (F|U(x_y))⁻¹` with `G'_y` acting on `I'_y = I_{x_y}` through
`F⁻¹ : G'_y → G_{x_y}`; points `y ∉ F(X)` are reached afterwards by Proposition 13.4.2, which
moves structures along a morphism `ψ : q → y` by `t ∘ (s|U(ψ))⁻¹` and `μ(ψ, ·)` (the formula
`sˣᵢ(D_x(q)) = μ((s|O(ψ_x))⁻¹(q), s^{q_x}ᵢ(q))`).

## What is formalized (namespace `Polyfold.SBLocalization`)

Both moves at once: for every `y ∈ X'` a morphism `σ_y : F(x_y) → y` and the chart
`Q = t ∘ (s|U(σ_y))⁻¹ ∘ F` of Chapter 10 (`EpFunctor.TransportChart`, with the family
`ψ_u : F(u) → Q(u)`).  For `y = F(x)` and `σ_y = 1` this is the text's `F|U(x_y)`.
* `PushChart F y` and the choice `pushChart hF y`; `conjEquiv` (`G_{x_y} ≅ G'_y`,
  `g ↦ ψ ∘ F(g) ∘ ψ⁻¹`, Remark 10.1.12).
* `IsPushNbhd T N N'`: `U'(y) ⊆ Q(U(x_y))` with
  `Γ'(ψ F(g) ψ⁻¹, z) = ψ_{g ∗ u} ∘ F(Γ(g, u)) ∘ ψ_u⁻¹` for `u = Q⁻¹(z)`;
  `exists_isPushNbhd` (with the properness property).
* `pushSec T s` (`z ↦ μ'(ψ_u, Φ(s(u)))`, `u = Q⁻¹(z)`), `isScPlusSectionOn_pushSec`.
* `pushStructure`: the symmetric structure of `Φ_*Λ` on `U'(y)`, `I'_y = I_{x_y}`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A C : SEP.{u}}

/-! ### `μ` along compositions -/

namespace PushChart

theorem fibAct_comp {ψ χ : A.Mor} {v : A.W} (hv : A.P v = A.X.src χ)
    (h : A.X.src ψ = A.X.tgt χ) : fibAct (A.X.comp ψ χ) v = fibAct ψ (fibAct χ v) := by
  rw [fibAct_of (hv.trans (A.X.src_comp ψ χ h).symm), fibAct_of hv,
    fibAct_of ((A.E.P_μ _).trans h.symm)]
  exact A.E.μ_comp ψ χ v hv h

theorem fibAct_unit {y : A.Obj} {v : A.W} (hv : A.P v = y) : fibAct (A.X.unit y) v = v := by
  subst hv
  rw [fibAct_of (A.X.src_unit _).symm]
  exact A.E.μ_unit v

theorem fibAct_inv_fibAct {ψ : A.Mor} {v : A.W} (hv : A.P v = A.X.src ψ) :
    fibAct (A.X.inv ψ) (fibAct ψ v) = v := by
  rw [← fibAct_comp hv (A.X.src_inv ψ), A.X.inv_comp, fibAct_unit hv]

theorem fibAct_fibAct_inv {ψ : A.Mor} {v : A.W} (hv : A.P v = A.X.tgt ψ) :
    fibAct ψ (fibAct (A.X.inv ψ) v) = v := by
  rw [← fibAct_comp (hv.trans (A.X.src_inv ψ).symm) (A.X.tgt_inv ψ).symm, A.X.comp_inv,
    fibAct_unit hv]

theorem π_fibAct {ψ : A.Mor} {v : A.W} (hv : A.P v = A.X.src ψ) :
    A.E.toEpGroupoid.π (fibAct ψ v) = A.E.toEpGroupoid.π v := by
  rw [fibAct_of hv, EpStrongBundle.π_μ]

end PushChart

/-! ### The chart at `y` -/

variable {F : C ⟶ A} (hF : SEP.equivalences F)

/-- **The chart at `y ∈ X'`**: a point `x_y ∈ X` and the transport chart
`Q = t ∘ (s|U(σ_y))⁻¹ ∘ F` along a morphism `σ_y : F(x_y) → y`. -/
structure PushChart (F : C ⟶ A) (y : A.Obj) where
  /-- The point `x_y`. -/
  x : C.Obj
  /-- The chart along `σ_y : F(x_y) → y`. -/
  T : (SEP.Hom.ϕ F).TransportChart x y

/-- A chosen chart at every `y` (`F` is essentially surjective and a local sc-diffeomorphism). -/
def pushChart (y : A.Obj) : PushChart F y :=
  have h := (sbe hF).isEquivalence_base.exists_iso y
  ⟨h.choose, ((SEP.Hom.ϕ F).exists_transportChart (sbe hF).isEquivalence_base.isLocalScDiffeo_obj
    h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2).choose⟩

/-- **`G_{x_y} ≅ G'_y`**, `g ↦ ψ ∘ F(g) ∘ ψ⁻¹` (Remark 10.1.12). -/
def conjEquiv {x : C.Obj} {y : A.Obj} (T : (SEP.Hom.ϕ F).TransportChart x y) :
    C.X.Isotropy x ≃* A.X.Isotropy y :=
  MulEquiv.ofBijective T.conj (T.bijective_conj (sbe hF).isEquivalence_base)

@[simp] theorem conjEquiv_apply {x : C.Obj} {y : A.Obj} (T : (SEP.Hom.ϕ F).TransportChart x y)
    (g : C.X.Isotropy x) : conjEquiv hF T g = T.conj g := rfl

/-! ### Adapted neighbourhoods -/

/-- **`U'(y)` adapted to `U(x_y)` along the chart** `T`: `U'(y) ⊆ Q(U(x_y))` (with the
`G_{x_y}`-orbits of `Q⁻¹(U'(y))` inside the chart), and the natural actions are intertwined:
`Γ'(ψ F(g) ψ⁻¹, z) = ψ_{g ∗ u} ∘ F(Γ(g, u)) ∘ ψ_u⁻¹` for `u = Q⁻¹(z)` (2021 (10.2)–(10.3)). -/
structure IsPushNbhd {x : C.Obj} {y : A.Obj} (T : (SEP.Hom.ϕ F).TransportChart x y)
    (N : C.X.NatNbhd x) (N' : A.X.NatNbhd y) : Prop where
  subset_W' : N'.U ⊆ T.W'
  Qinv_mem : ∀ {z}, z ∈ N'.U → T.Qinv z ∈ N.U
  Φ_mem_W : ∀ z ∈ N'.U, ∀ g, N.rep.Φ g (T.Qinv z) ∈ T.W
  Γ_eq : ∀ g, ∀ z ∈ N'.U, N'.rep.Γ (T.conj g) z =
    A.X.comp (A.X.comp (T.ψ (N.rep.Φ g (T.Qinv z))) ((SEP.Hom.ϕ F).mor (N.rep.Γ g (T.Qinv z))))
      (A.X.inv (T.ψ (T.Qinv z)))

namespace TransportChartLemmas

variable {x : C.Obj} {y : A.Obj} (T : (SEP.Hom.ϕ F).TransportChart x y) (N : C.X.NatNbhd x)

theorem src_ψ_eq_tgt {g : C.X.Isotropy x} {u : C.Obj} (hu : u ∈ N.U)
    (hgu : N.rep.Φ g u ∈ T.W) :
    A.X.src (T.ψ (N.rep.Φ g u)) = A.X.tgt ((SEP.Hom.ϕ F).mor (N.rep.Γ g u)) := by
  rw [T.src_ψ _ hgu, (SEP.Hom.ϕ F).tgt_mor, N.tgt_Γ g hu]

theorem src_comp_eq_tgt_inv {g : C.X.Isotropy x} {u : C.Obj} (hu : u ∈ N.U)
    (huW : u ∈ T.W) (hgu : N.rep.Φ g u ∈ T.W) :
    A.X.src (A.X.comp (T.ψ (N.rep.Φ g u)) ((SEP.Hom.ϕ F).mor (N.rep.Γ g u))) =
      A.X.tgt (A.X.inv (T.ψ u)) := by
  rw [A.X.src_comp _ _ (src_ψ_eq_tgt T N hu hgu), (SEP.Hom.ϕ F).src_mor, N.src_Γ g hu,
    A.X.tgt_inv, T.src_ψ u huW]

end TransportChartLemmas

namespace IsPushNbhd

variable {hF} {x : C.Obj} {y : A.Obj} {T : (SEP.Hom.ϕ F).TransportChart x y}
  {N : C.X.NatNbhd x} {N' : A.X.NatNbhd y} (h : IsPushNbhd T N N')
include h

theorem Qinv_mem_W {z : A.Obj} (hz : z ∈ N'.U) : T.Qinv z ∈ T.W :=
  T.isScDiffeoOn_Q.mapsTo_inv (h.subset_W' hz)

theorem Q_Qinv {z : A.Obj} (hz : z ∈ N'.U) : T.Q (T.Qinv z) = z :=
  T.isScDiffeoOn_Q.right_inv z (h.subset_W' hz)

theorem tgt_ψ_Qinv {z : A.Obj} (hz : z ∈ N'.U) : A.X.tgt (T.ψ (T.Qinv z)) = z := by
  rw [T.tgt_ψ _ (h.Qinv_mem_W hz), h.Q_Qinv hz]

theorem src_ψ_Qinv {z : A.Obj} (hz : z ∈ N'.U) :
    A.X.src (T.ψ (T.Qinv z)) = (SEP.Hom.ϕ F).obj (T.Qinv z) :=
  T.src_ψ _ (h.Qinv_mem_W hz)

/-- `ψ F(g) ψ⁻¹ ∗ z = Q(g ∗ Q⁻¹(z))`. -/
theorem Φ_eq (g : C.X.Isotropy x) {z : A.Obj} (hz : z ∈ N'.U) :
    N'.rep.Φ (T.conj g) z = T.Q (N.rep.Φ g (T.Qinv z)) := by
  have e := congrArg A.X.tgt (h.Γ_eq g z hz)
  rw [N'.tgt_Γ _ hz, A.X.tgt_comp _ _ (TransportChartLemmas.src_comp_eq_tgt_inv T N
      (h.Qinv_mem hz) (h.Qinv_mem_W hz) (h.Φ_mem_W z hz g)),
    A.X.tgt_comp _ _ (TransportChartLemmas.src_ψ_eq_tgt T N (h.Qinv_mem hz) (h.Φ_mem_W z hz g)),
    T.tgt_ψ _ (h.Φ_mem_W z hz g)] at e
  exact e

theorem Qinv_Φ (g : C.X.Isotropy x) {z : A.Obj} (hz : z ∈ N'.U) :
    T.Qinv (N'.rep.Φ (T.conj g) z) = N.rep.Φ g (T.Qinv z) := by
  rw [h.Φ_eq g hz, T.isScDiffeoOn_Q.left_inv _ (h.Φ_mem_W z hz g)]

/-- **The intertwining identity** `Γ'(ψ F(g) ψ⁻¹, z) ∘ ψ_u = ψ_{g ∗ u} ∘ F(Γ(g, u))`. -/
theorem Γ_comp_ψ (g : C.X.Isotropy x) {z : A.Obj} (hz : z ∈ N'.U) :
    A.X.comp (N'.rep.Γ (T.conj g) z) (T.ψ (T.Qinv z)) =
      A.X.comp (T.ψ (N.rep.Φ g (T.Qinv z))) ((SEP.Hom.ϕ F).mor (N.rep.Γ g (T.Qinv z))) := by
  rw [h.Γ_eq g z hz, A.X.comp_assoc _ _ _ (TransportChartLemmas.src_comp_eq_tgt_inv T N
      (h.Qinv_mem hz) (h.Qinv_mem_W hz) (h.Φ_mem_W z hz g)) (A.X.src_inv _), A.X.inv_comp]
  have e := TransportChartLemmas.src_comp_eq_tgt_inv T N (h.Qinv_mem hz) (h.Qinv_mem_W hz)
      (h.Φ_mem_W z hz g)
  rw [A.X.tgt_inv] at e
  exact A.X.comp_unit_of_eq e

end IsPushNbhd

/-- **Adapted neighbourhoods exist** (with the properness property): inside `Q(W₀)`, `W₀` the
invariant core of `U(x_y)` in the chart, the two lifts `z ↦ Γ'(ψ F(g) ψ⁻¹, z)` and
`z ↦ ψ_{g ∗ u} ∘ F(Γ(g, u)) ∘ ψ_u⁻¹` through `s` agree at `y`, hence on an open set, made
invariant afterwards. -/
theorem exists_isPushNbhd {x : C.Obj} {y : A.Obj} (T : (SEP.Hom.ϕ F).TransportChart x y)
    (N : C.X.NatNbhd x) :
    ∃ N' : A.X.NatNbhd y, IsPushNbhd T N N' ∧ A.X.IsProperSubset (closure N'.U) := by
  set W₀ := N.invariantCore T.W with hW₀def
  have hW₀ : IsOpen W₀ := N.isOpen_invariantCore T.isOpen_W
  have hQinv : ContinuousOn T.Qinv T.W' := T.isScDiffeoOn_Q.isScSmoothOn_inv.continuousOn
  set O' := T.W' ∩ T.Qinv ⁻¹' W₀ with hO'def
  have hO' : IsOpen O' := hQinv.isOpen_inter_preimage T.isOpen_W' hW₀
  have hQx : T.Qinv y = x := by
    have e := T.isScDiffeoOn_Q.left_inv x T.mem_W
    rwa [T.Q_self] at e
  have hyO' : y ∈ O' :=
    ⟨T.mem_W', by rw [mem_preimage, hQx]; exact N.mem_invariantCore T.mem_W⟩
  obtain ⟨N₀, hN₀O, hprop⟩ := A.X.exists_natNbhd_isProperSubset y hO' hyO'
  have hW' : ∀ z ∈ N₀.U, z ∈ T.W' := fun z hz => (hN₀O hz).1
  have hu : ∀ z ∈ N₀.U, T.Qinv z ∈ W₀ := fun z hz => (hN₀O hz).2
  have huN : ∀ z ∈ N₀.U, T.Qinv z ∈ N.U := fun z hz => (N.invariantCore_subset _ (hu z hz)).1
  have huW : ∀ z ∈ N₀.U, T.Qinv z ∈ T.W := fun z hz =>
    T.isScDiffeoOn_Q.mapsTo_inv (hW' z hz)
  have hgW : ∀ z ∈ N₀.U, ∀ g, N.rep.Φ g (T.Qinv z) ∈ T.W := fun z hz g =>
    (N.invariantCore_subset _ (N.mapsTo_Φ_invariantCore _ g (hu z hz))).2
  have hQinv₀ : ContinuousOn T.Qinv N₀.U := hQinv.mono hW'
  set e : C.X.Isotropy x → A.Obj → A.Mor := fun g z =>
    A.X.comp (A.X.comp (T.ψ (N.rep.Φ g (T.Qinv z))) ((SEP.Hom.ϕ F).mor (N.rep.Γ g (T.Qinv z))))
      (A.X.inv (T.ψ (T.Qinv z))) with hedef
  set E : Set A.Obj := N₀.U ∩ ⋂ g, {z | z ∈ N₀.U ∧ N₀.rep.Γ (T.conj g) z = e g z} with hEdef
  have hE : IsOpen E := by
    refine N₀.isOpen_U.inter (isOpen_iInter_of_finite fun g => ?_)
    have h1 : ContinuousOn (fun z => T.ψ (N.rep.Φ g (T.Qinv z))) N₀.U :=
      T.continuousOn_ψ.comp ((N.rep.continuousOn_Φ g).comp hQinv₀ fun z hz =>
        N.U_subset (huN z hz)) fun z hz => hgW z hz g
    have h2 : ContinuousOn (fun z => (SEP.Hom.ϕ F).mor (N.rep.Γ g (T.Qinv z))) N₀.U :=
      (SEP.Hom.ϕ F).continuous_mor.comp_continuousOn
        ((N.rep.isScSmoothOn_Γ g).continuousOn.comp hQinv₀ fun z hz => N.U_subset (huN z hz))
    have h3 : ContinuousOn (fun z => A.X.inv (T.ψ (T.Qinv z))) N₀.U :=
      A.X.continuous_inv.comp_continuousOn (T.continuousOn_ψ.comp hQinv₀ huW)
    have he : ContinuousOn (e g) N₀.U :=
      A.X.continuousOn_comp_of (A.X.continuousOn_comp_of h1 h2 fun z hz =>
        TransportChartLemmas.src_ψ_eq_tgt T N (huN z hz) (hgW z hz g)) h3 fun z hz =>
          TransportChartLemmas.src_comp_eq_tgt_inv T N (huN z hz) (huW z hz) (hgW z hz g)
    refine A.X.isOpen_setOf_eq_of_src N₀.isOpen_U
      ((N₀.rep.isScSmoothOn_Γ _).continuousOn.mono N₀.U_subset) he fun z hz => ?_
    rw [N₀.src_Γ _ hz, hedef, A.X.src_comp _ _ (TransportChartLemmas.src_comp_eq_tgt_inv T N
      (huN z hz) (huW z hz) (hgW z hz g)), A.X.src_inv, T.tgt_ψ _ (huW z hz),
      T.isScDiffeoOn_Q.right_inv z (hW' z hz)]
  have hyE : y ∈ E := ⟨N₀.mem_U, mem_iInter.2 fun g => ⟨N₀.mem_U, by
    rw [N₀.rep.Γ_self, hedef]
    simp only
    rw [hQx, N.rep.Φ_self, N.rep.Γ_self, T.ψ_self, T.conj_val]⟩⟩
  obtain ⟨N', hrep, hsub⟩ := N₀.exists_restrict_subset hE hyE
  refine ⟨N', ⟨fun z hz => hW' z (hsub hz).1, fun hz => huN _ (hsub hz).1,
    fun z hz => hgW z (hsub hz).1, fun g z hz => ?_⟩,
    isProperMap_domRestrict_of_subset_of_isClosed A.X.continuous_src hprop
      (closure_mono fun z hz => (hsub hz).1) isClosed_closure⟩
  rw [hrep]
  exact (mem_iInter.1 (hsub hz).2.2 g).2

/-! ### The pushed sections -/

/-- **The pushed section** `z ↦ μ'(ψ_u, Φ(s(u)))`, `u = Q⁻¹(z)`. -/
def pushSec {x : C.Obj} {y : A.Obj} (T : (SEP.Hom.ϕ F).TransportChart x y)
    (s : C.Obj → C.W) : A.Obj → A.W :=
  transportSection (T.ψ ∘ T.Qinv) ((SEP.Hom.Φ F).obj ∘ s ∘ T.Qinv)

namespace IsPushNbhd

variable {x : C.Obj} {y : A.Obj} {T : (SEP.Hom.ϕ F).TransportChart x y}
  {N : C.X.NatNbhd x} {N' : A.X.NatNbhd y} (h : IsPushNbhd T N N')
include hF h

theorem P_obj {s : C.Obj → C.W} (hs : ∀ u ∈ N.U, C.P (s u) = u) {z : A.Obj} (hz : z ∈ N'.U) :
    A.P ((SEP.Hom.Φ F).obj (s (T.Qinv z))) = A.X.src (T.ψ (T.Qinv z)) := by
  have e := (PullMap.ofEquivalence hF).covers (s (T.Qinv z))
  simp only [PullMap.ofEquivalence_Φ, PullMap.ofEquivalence_ϕ] at e
  rw [e, hs _ (h.Qinv_mem hz), h.src_ψ_Qinv hz]

theorem pushSec_eq {s : C.Obj → C.W} (hs : ∀ u ∈ N.U, C.P (s u) = u) {z : A.Obj}
    (hz : z ∈ N'.U) :
    pushSec T s z = fibAct (T.ψ (T.Qinv z)) ((SEP.Hom.Φ F).obj (s (T.Qinv z))) := by
  rw [pushSec, transportSection_of_mem (h.P_obj hF hs hz), fibAct_of (h.P_obj hF hs hz)]; rfl

/-- **The pushed section of an sc⁺-section on `U(x_y)` is an sc⁺-section on `U'(y)`.** -/
theorem isScPlusSectionOn_pushSec {s : C.Obj → C.W} (hs : IsScPlusSectionOn C s N.U) :
    IsScPlusSectionOn A (pushSec T s) N'.U := by
  obtain ⟨hsec, G, hG, hGs⟩ := hs
  have hFs := (sbe hF).isStrongBundleFunctor.isStrongBundleMap_obj
  have hQ : A.X.PObj.IsScSmoothOn C.X.PObj T.Qinv N'.U :=
    T.isScDiffeoOn_Q.isScSmoothOn_inv.mono N'.isOpen_U h.subset_W'
  refine isScPlusSectionOn_transportSection
    (G := oneRestrict C.B A.B (SEP.Hom.Φ F).obj hFs.mapsTo_oneSet ∘ G ∘ T.Qinv)
    (MPolyfold.IsScSmoothOn.comp T.isScSmoothOn_ψ hQ fun z hz => h.Qinv_mem_W hz)
    (fun z hz => ?_)
    (MPolyfold.IsScSmoothOn.comp hFs.isScSmoothMap_one
      (MPolyfold.IsScSmoothOn.comp hGs hQ fun z hz => h.Qinv_mem hz) (mapsTo_univ _ _))
    (fun z hz => h.P_obj hF hsec hz) fun z hz => h.tgt_ψ_Qinv hz
  change A.B.oneVal (oneRestrict C.B A.B _ _ (G (T.Qinv z))) = (SEP.Hom.Φ F).obj (s (T.Qinv z))
  rw [oneVal_oneRestrict, hG _ (h.Qinv_mem hz)]

end IsPushNbhd

/-! ### The pushed symmetric structure -/

/-- **The pushed symmetric structure** of `Φ_*Λ` on `U'(y)` (proof of Theorem 13.4.3):
`I'_y = I_{x_y}`, `h(i) = (ψ F(·) ψ⁻¹)⁻¹(h)(i)`, `s'ᵢ(z) = μ'(ψ_u, Φ(sᵢ(u)))`. -/
def pushStructure {x : C.Obj} {y : A.Obj} {T : (SEP.Hom.ϕ F).TransportChart x y}
    {N : C.X.NatNbhd x} {N' : A.X.NatNbhd y} (h : IsPushNbhd T N N') {Λ : C.W → ℚ≥0}
    (hΛ : IsWFunctor C Λ) (S : SymmetricStructureOn C Λ N) :
    SymmetricStructureOn A (pushMult F hF Λ) N' where
  I := S.I
  fintype := S.fintype
  mulAction := MulAction.compHom S.I (conjEquiv hF T).symm.toMonoidHom
  s i := pushSec T (S.s i)
  isScPlusSectionOn i := h.isScPlusSectionOn_pushSec hF (S.isScPlusSectionOn i)
  equivariant k i z hz := by
    obtain ⟨g, rfl⟩ := (conjEquiv hF T).surjective k
    have hgi : (conjEquiv hF T).symm (conjEquiv hF T g) • i = g • i := by
      rw [MulEquiv.symm_apply_apply]
    change pushSec T (S.s ((conjEquiv hF T).symm (conjEquiv hF T g) • i)) _ = _
    rw [hgi, conjEquiv_apply]
    have hgz := N'.Φ_mem (T.conj g) hz
    have hu := h.Qinv_mem hz
    rw [h.pushSec_eq hF (fun u hu => S.P_s _ hu) hgz, h.pushSec_eq hF (fun u hu => S.P_s _ hu) hz,
      h.Qinv_Φ g hz, S.equivariant g i _ hu]
    have hsrc : C.P (S.s i (T.Qinv z)) = C.X.src (N.rep.Γ g (T.Qinv z)) := by
      rw [S.P_s i hu, N.src_Γ g hu]
    have e1 := (PullMap.ofEquivalence hF).obj_fibAct hsrc
    simp only [PullMap.ofEquivalence_Φ, PullMap.ofEquivalence_ϕ] at e1
    have hv := h.P_obj hF (fun u hu => S.P_s i hu) hz
    have hv1 : A.P ((SEP.Hom.Φ F).obj (S.s i (T.Qinv z))) =
        A.X.src ((SEP.Hom.ϕ F).mor (N.rep.Γ g (T.Qinv z))) := by
      rw [hv, h.src_ψ_Qinv hz, (SEP.Hom.ϕ F).src_mor, N.src_Γ g hu]
    rw [e1, ← PushChart.fibAct_comp hv1
        (TransportChartLemmas.src_ψ_eq_tgt T N hu (h.Φ_mem_W z hz g)), ← h.Γ_comp_ψ g hz,
      PushChart.fibAct_comp hv (by rw [N'.src_Γ _ hz, h.tgt_ψ_Qinv hz])]
  rep w' hw' := by
    set z := A.P w' with hzdef
    have hu := h.Qinv_mem hw'
    set u := T.Qinv z with hudef
    have hw'1 : A.P w' = A.X.src (A.X.inv (T.ψ u)) := by
      rw [A.X.src_inv]; exact (h.tgt_ψ_Qinv hw').symm
    set m := fibAct (A.X.inv (T.ψ u)) w' with hmdef
    have hm : A.P m = (SEP.Hom.ϕ F).obj u := by
      rw [hmdef, P_fibAct hw'1, A.X.tgt_inv]; exact h.src_ψ_Qinv hw'
    set M := PullMap.ofEquivalence hF
    set v : C.W := ((M.fiberEquiv u).symm ⟨m, hm⟩).1 with hvdef
    have hΦv : (SEP.Hom.Φ F).obj v = m := by
      change M.Φ v = m
      rw [hvdef, ← PullMap.fiberEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
    have hPv : C.P v = u := ((M.fiberEquiv u).symm ⟨m, hm⟩).2
    have hπ : A.E.toEpGroupoid.π ((SEP.Hom.Φ F).obj v) = A.E.toEpGroupoid.π w' := by
      rw [hΦv, hmdef, PushChart.π_fibAct hw'1]
    rw [pushMult_eq hF hΛ hπ, S.rep v (by rw [hPv]; exact hu), hPv]
    have e : (Finset.univ.filter fun i => S.s i u = v) =
        Finset.univ.filter fun i => pushSec T (S.s i) z = w' := by
      refine Finset.filter_congr fun i _ => ?_
      rw [h.pushSec_eq hF (fun u hu => S.P_s _ hu) hw']
      have hPs : A.P ((SEP.Hom.Φ F).obj (S.s i u)) = A.X.src (T.ψ u) :=
        h.P_obj hF (fun u hu => S.P_s _ hu) hw'
      constructor
      · intro e
        rw [e, hΦv, hmdef, PushChart.fibAct_fibAct_inv (h.tgt_ψ_Qinv hw').symm]
      · intro e
        refine M.eq_of_obj_eq ((S.P_s i hu).trans hPv.symm) ?_
        change (SEP.Hom.Φ F).obj (S.s i u) = (SEP.Hom.Φ F).obj v
        rw [hΦv, hmdef, ← e, PushChart.fibAct_inv_fibAct hPs]
    rw [e]

@[simp] theorem pushStructure_I {x : C.Obj} {y : A.Obj} {T : (SEP.Hom.ϕ F).TransportChart x y}
    {N : C.X.NatNbhd x} {N' : A.X.NatNbhd y} (h : IsPushNbhd T N N') {Λ : C.W → ℚ≥0}
    (hΛ : IsWFunctor C Λ) (S : SymmetricStructureOn C Λ N) :
    (pushStructure hF h hΛ S).I = S.I := rfl

end SBLocalization

end Polyfold
