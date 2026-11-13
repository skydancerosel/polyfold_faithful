import Polyfold.Chapter6.SectionOrientation
import Polyfold.Chapter3.FredholmPullbackIso

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 592–593: the chart-level part of **Lemma 12.5.1** (2017: Lemma 12.2,
§12.5): linearizations and their determinant orientations are carried along a local strong
bundle isomorphism.

# Chart points carried along a local strong bundle isomorphism

## The text, paraphrased

(Proof of Lemma 12.5.1, p. 592) A morphism `φ : x → x'` between smooth points extends to an
sc-diffeomorphism `φ̂ : U(x) → U(x')`, lifted to a strong bundle isomorphism `Φ̂`; for a local
sc⁺-section `s₀` at `x` with `s₀(x) = f(x)`, `s₁ = Φ̂_* s₀` is one at `x'` with
`μ(φ, (f − s₀)'(x) ∘ Tφ⁻¹) = (f − s₁)'(x')`.

## What is formalized

The project reads `Lin(f, x)` in a chart point (`ChartPoint`, `LinSet.lean`) and compares chart
points at one point by `ChartPoint.orTransfer` (`ChartTransfer.lean`).  Here a local strong
bundle isomorphism `L : Y|U → Y|U'` (`StrongBundle.LocalIso`, with base map `ϕ : U → U'`) is
used to move chart points from `x = ϕ(x')` to `x'`:

* `LocalIso.pullPt L p`: for a chart point `p` at `x` whose chart lies in `U'`, the chart point
  at `x'` of the transported chart `Ψ' ∘ Φ` (`LocalIso.transportChart`), with the same model, the
  same retraction and the same level-`1` point `z`.  Its spaces `T_zO`, `K_z` are those of `p`.
* `LocalIso.linSet_pullPt`: **if `f = Ψ ∘ f ∘ ϕ` on `U`, then `Lin(f, x')` read in `pullPt L p`
  is `Lin(f, x)` read in `p`** (the identity `μ(φ, (f − s₀)'(x) ∘ Tφ⁻¹) = (f − s₁)'(x')` of the
  text, read in the transported chart, where `Tφ` and `μ(φ, ·)` become identities).
* `LocalIso.transferT_pullPt`, `transferK_pullPt`: the identifications `orTransfer` between two
  pulled chart points are those between the original ones.
* `LocalIso.transferT_pullPt_pullPt`, `transferK_pullPt_pullPt`: if two composite local
  isomorphisms agree near `x''`, the identification between the two chart points they produce is
  the identity.

## Reading

The sections in `Lin(f, x)` are global sc⁺-sections (`LinSet.lean`).  The text's local section
`s₁ = Φ̂_* s₀` is replaced by any global sc⁺-section through `x'`: two linearizations differ by an
sc⁺-operator (the derivative of the difference of the two local representatives of the
sc⁺-sections, `exists_isScPlusOp_pullPt`).  That a global sc⁺-section through `x'` exists is the
hypothesis `B.HasScPlusSectionsThrough`, under which Part I proves that `Lin(f, x)` is not
empty (`ChartPoint.linSet_nonempty`; it holds with sc-smooth bump functions,
`MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Module

noncomputable section

namespace Polyfold

open StrongRetr

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- The difference of two sc-operators is an sc-operator. -/
private theorem isScOperator_sub {E F : ScBanach} {S T : E 0 →L[ℝ] F 0} (hS : IsScOperator S)
    (hT : IsScOperator T) : IsScOperator (S - T) := fun m => by
  obtain ⟨Sm, hSm⟩ := hS m
  obtain ⟨Tm, hTm⟩ := hT m
  exact ⟨Sm - Tm, fun x => by simp [hSm, hTm]⟩

namespace StrongBundle.LocalIso

variable {U U' : Set X} (L : LocalIso B B U U')

/-- **The chart point at `x'` carried from a chart point `p` at `x = ϕ(x')`**: the chart point of
the transported chart `Ψ' ∘ Φ` (`transportChart`) with the level-`1` point `z` of `p`. -/
def pullPt {x x' : X} (p : ChartPoint B x) (hsub : p.c.φ.source ⊆ U') (hx' : x' ∈ U)
    (hϕ : L.ϕ x' = x) : ChartPoint B x' where
  c := L.transportChart p.c hsub
  isChart := L.isChart_transportChart p.c hsub p.isChart
  mem_source := ⟨hx', by rw [Set.mem_preimage, hϕ]; exact p.mem_source⟩
  z := p.z
  toBase_z := by
    change p.c.φ.model.E.toBase 1 p.z = p.c.φ (L.ϕ x')
    rw [hϕ]; exact p.toBase_z

variable {x x' : X} (p : ChartPoint B x) (hsub : p.c.φ.source ⊆ U') (hx' : x' ∈ U)
  (hϕ : L.ϕ x' = x)

@[simp] lemma pullPt_c : (L.pullPt p hsub hx' hϕ).c = L.transportChart p.c hsub := rfl

@[simp] lemma pullPt_z : (L.pullPt p hsub hx' hϕ).z = p.z := rfl

/-- The spaces `T_zO` of `p` and of the carried chart point coincide. -/
lemma pullPt_T : (L.pullPt p hsub hx' hϕ).T = p.T := rfl

/-- The spaces `K_z` of `p` and of the carried chart point coincide. -/
lemma pullPt_K : (L.pullPt p hsub hx' hϕ).K = p.K := rfl

/-! ### `Lin(f, x)` is carried to `Lin(f, x')` -/

variable {L p hsub hx' hϕ}

/-- **The linearizations at `x` and at `x'` differ by an sc⁺-operator**: for sc⁺-sections `s₀`,
`s` with `(f + s₀)(x) = 0` and `(f + s)(x') = 0`, the linearization of `f + s` read in the
carried chart point is that of `f + s₀` in `p` plus an sc⁺-operator `b : T_zO → K_z`.  In the
carried chart the principal part of `f` is that of `f` in `p` (`principal_transportChart`), so
`b = ι ∘ D(ŝ₁ ∘ r − ŝ₀₁ ∘ r)(z)` for the level-`1` lifts of the principal parts of `s` and `s₀`. -/
theorem exists_isScPlusOp_pullPt (hf : B.IsScFredholmSection f)
    (hfL : EqOn f (L.Ψ ∘ f ∘ L.ϕ) U) (hx' : x' ∈ U) (hϕ : L.ϕ x' = x)
    (hxs : x ∈ PX.smoothSet) {s s₀ : X → Y} (hs : B.IsScPlusSection s) (hs₀ : B.IsScPlusSection s₀)
    (hz : IsZeroAt P (sectionAdd P f s) x') (hz₀ : IsZeroAt P (sectionAdd P f s₀) x) :
    ∃ b : ↥p.T →L[ℝ] ↥p.K, p.IsScPlusOp b ∧ ∀ v,
      linAt p.c.U p.c.R ((L.transportChart p.c hsub).principal (sectionAdd P f s)) p.z v =
        linAt p.c.U p.c.R (p.c.principal (sectionAdd P f s₀)) p.z v + (b v : p.c.F 0) := by
  set q := L.pullPt p hsub hx' hϕ with hq
  have hfs := hf.isScSmooth
  have hfsec : IsSection P f := hfs.1
  have hg := hfs.sectionAdd hs
  have hg₀ := hfs.sectionAdd hs₀
  have hk : IsSc1 p.c.U (p.c.principal f ∘ r p.c.R) := hfs.isSc1_principal_comp_r p.isChart
  have hg' : IsSc1 p.c.U ((L.transportChart p.c hsub).principal (sectionAdd P f s) ∘ r p.c.R) :=
    hg.isSc1_principal_comp_r q.isChart
  have hg₀' : IsSc1 p.c.U (p.c.principal (sectionAdd P f s₀) ∘ r p.c.R) :=
    hg₀.isSc1_principal_comp_r p.isChart
  have hl₁ : IsScSmooth (F := p.c.F.shift) p.c.U
      ((L.transportChart p.c hsub).principalLift s ∘ r p.c.R) :=
    (((hs.isScSmoothRetractMap_one q.isChart).comp_isScSmooth
      (q.c.isRetraction.baseRetraction q.c.relOpen) q.c.base_retract).snd
      q.c.relOpen.isScDomain).congr q.c.relOpen.isScDomain fun _ _ => rfl
  have hl₀ : IsScSmooth (F := p.c.F.shift) p.c.U (p.c.principalLift s₀ ∘ r p.c.R) :=
    (((hs₀.isScSmoothRetractMap_one p.isChart).comp_isScSmooth
      (p.c.isRetraction.baseRetraction p.c.relOpen) p.c.base_retract).snd
      p.c.relOpen.isScDomain).congr p.c.relOpen.isScDomain fun _ _ => rfl
  have hO : ∀ u ∈ p.c.U, r p.c.R u ∈ p.c.φ.model.O := fun u hu => p.c.r_mem_O hu
  have hO' : ∀ u ∈ p.c.U, r p.c.R u ∈ (L.transportChart p.c hsub).φ.model.O := fun u hu => by
    rw [L.transportChart_model_O]; exact p.c.r_mem_O hu
  have hkey : ∀ w ∈ (L.transportChart p.c hsub).φ.model.O,
      (L.transportChart p.c hsub).principal (sectionAdd P f s) w =
        (L.transportChart p.c hsub).principal f w +
          (L.transportChart p.c hsub).F.toBase 1 ((L.transportChart p.c hsub).principalLift s w) :=
      fun w hw => by
    rw [(L.transportChart p.c hsub).principal_sectionAdd hfsec hs.1 hw,
      hs.toBase_principalLift (L.isChart_transportChart p.c hsub p.isChart) hw]
  have hpf : ∀ w ∈ p.c.φ.model.O, (L.transportChart p.c hsub).principal f w = p.c.principal f w :=
    fun w hw => L.principal_transportChart p.c hsub hfL hfsec hw
  have e₁ := scDeriv_add_toBase_one_apply p.c.relOpen hk hg' hl₁.isSc1 (fun u hu =>
      (hkey (r p.c.R u) (hO' u hu)).trans
        (congrArg (· + p.c.F.toBase 1 ((L.transportChart p.c hsub).principalLift s (r p.c.R u)))
          (hpf (r p.c.R u) (hO u hu)))) p.mem_U
  have e₀ := scDeriv_add_toBase_one_apply p.c.relOpen hk hg₀' hl₀.isSc1 (fun u hu => by
      simp only [Function.comp_apply]
      rw [p.c.principal_sectionAdd hfsec hs₀.1 (hO u hu),
        hs₀.toBase_principalLift p.isChart (hO u hu)]) p.mem_U
  set D := scDeriv (F := p.c.F.shift) p.c.U ((L.transportChart p.c hsub).principalLift s ∘ r p.c.R)
      p.z - scDeriv (F := p.c.F.shift) p.c.U (p.c.principalLift s₀ ∘ r p.c.R) p.z with hDdef
  have hD : IsScOperator (E := p.c.φ.model.E) (F := p.c.F.shift) D :=
    isScOperator_sub (hl₁.isSc1.isSc1With_scDeriv.scOperator_deriv p.mem_U (p.z_mem_smoothLvl hxs))
      (hl₀.isSc1.isSc1With_scDeriv.scOperator_deriv p.mem_U (p.z_mem_smoothLvl hxs))
  have hsum : ∀ v, p.c.F.toBase 1 (D v) +
      scDeriv p.c.U (p.c.principal (sectionAdd P f s₀) ∘ r p.c.R) p.z v =
        scDeriv p.c.U ((L.transportChart p.c hsub).principal (sectionAdd P f s) ∘ r p.c.R) p.z v :=
    fun v => (show p.c.F.toBase 1 (D v) +
        scDeriv p.c.U (p.c.principal (sectionAdd P f s₀) ∘ r p.c.R) p.z v =
          scDeriv p.c.U (p.c.principal f ∘ r p.c.R) p.z v + p.c.F.toBase 1
            (scDeriv (F := p.c.F.shift) p.c.U ((L.transportChart p.c hsub).principalLift s ∘
              r p.c.R) p.z v) by
      rw [e₀ v, hDdef, sub_apply, map_sub]; abel).trans (e₁ v).symm
  have hDK : ∀ v, p.c.F.toBase 1 (D v) ∈ p.K := fun v => by
    have hm := sub_mem (q.scDeriv_mem_K hg hz v) (p.scDeriv_mem_K hg₀ hz₀ v)
    rw [eq_sub_of_add_eq (hsum v)]
    exact hm
  let b : ↥p.T →L[ℝ] ↥p.K :=
    (((p.c.F.toBase 1).comp D).comp p.T.subtypeL).codRestrict p.K fun v => hDK v
  refine ⟨b, p.isScPlusOp_of_shift (p.isScSubspace_T hxs) (p.isScSubspace_K hxs) hD
    (fun v _ => hDK v) (fun v => rfl), fun v => ?_⟩
  exact (hsum v).symm.trans (add_comm _ _)

/-- **`Lin(f, x')` read in the carried chart point is `Lin(f, x)` read in `p`** (Lemma 12.5.1 (1)
in the transported chart, where `Tφ` and `μ(φ, ·)` are identities), for `f = Ψ ∘ f ∘ ϕ` on `U`
and sc⁺-sections through the smooth fibre points (Part I's reading of `Lin(f, x) ≠ ∅`). -/
theorem linSet_pullPt (hf : B.IsScFredholmSection f) (hfL : EqOn f (L.Ψ ∘ f ∘ L.ϕ) U)
    (hsec : B.HasScPlusSectionsThrough) (hxs : x ∈ PX.smoothSet) (hx's : x' ∈ PX.smoothSet) :
    (L.pullPt p hsub hx' hϕ).linSet f = p.linSet f := by
  obtain ⟨-, s₀, hs₀, hz₀, -⟩ := p.linSet_nonempty hf hxs hsec
  obtain ⟨-, s₁, hs₁, hz₁, -⟩ := (L.pullPt p hsub hx' hϕ).linSet_nonempty hf hx's hsec
  ext (T : ↥p.T →L[ℝ] ↥p.K)
  constructor
  · rintro ⟨s, hs, hz, a, ha, hT⟩
    let a' : ↥p.T →L[ℝ] ↥p.K := a
    have ha' : p.IsScPlusOp a' := ha
    have h1 : ∀ v, (T v : p.c.F 0) = linAt p.c.U p.c.R ((L.transportChart p.c hsub).principal
      (sectionAdd P f s)) p.z v + (a' v : p.c.F 0) := hT
    obtain ⟨b, hb, hbv⟩ := exists_isScPlusOp_pullPt hf hfL hx' hϕ hxs hs hs₀ hz hz₀
    refine (p.mem_linSet_iff hf hs₀ hz₀ T).2 ⟨b + a', hb.add ha', fun v => ?_⟩
    rw [h1 v, hbv v, add_apply, Submodule.coe_add]
    abel
  · intro hT
    obtain ⟨a, ha, hTa⟩ := (p.mem_linSet_iff hf hs₀ hz₀ T).1 hT
    obtain ⟨b, hb, hbv⟩ := exists_isScPlusOp_pullPt hf hfL hx' hϕ hxs hs₁ hs₀ hz₁ hz₀
    let a' : ↥p.T →L[ℝ] ↥p.K := a + (-1 : ℝ) • b
    have ha' : p.IsScPlusOp a' := ha.add (hb.smul (-1))
    have key : ∀ v, (T v : p.c.F 0) = linAt p.c.U p.c.R ((L.transportChart p.c hsub).principal
        (sectionAdd P f s₁)) p.z v + (a' v : p.c.F 0) := fun v => by
      rw [hTa v, hbv v]
      simp only [a', add_apply, smul_apply, Submodule.coe_add, Submodule.coe_smul]
      module
    exact ⟨s₁, hs₁, hz₁, a', ha', key⟩

/-! ### The identifications between carried chart points -/

section Transfer


/-- **The base derivatives between two carried chart points are those between the original
ones**: the base transition of the carried charts is `φ_b ∘ ϕ ∘ ϕ⁻¹ ∘ φ_a⁻¹ = φ_b ∘ φ_a⁻¹`. -/
theorem baseDeriv_pullPt (L : LocalIso B B U U') {a b : ChartPoint B x} (ha : a.c.φ.source ⊆ U')
    (hb : b.c.φ.source ⊆ U') (hx' : x' ∈ U) (hϕ : L.ϕ x' = x) (v : a.c.φ.model.E 0) :
    (L.pullPt a ha hx' hϕ).baseDeriv (L.pullPt b hb hx' hϕ) v = a.baseDeriv b v := by
  set a' := L.pullPt a ha hx' hϕ with ha'
  set b' := L.pullPt b hb hx' hϕ with hb'
  set R₁₃ := (a.baseRet b).restrict (a'.isOpen_overlapW b') with hR₁₃
  have hV₁ : R₁₃.U ⊆ (a.baseRet b).U := inter_subset_left
  have hV₃ : R₁₃.U ⊆ (a'.baseRet b').U := fun u hu => ⟨(a.baseRet_U_subset b) hu.1, hu.2⟩
  have hzV : a.z ∈ a.c.φ.model.E.lvlSet R₁₃.U 1 := ⟨a.z_mem_baseRet b, (a'.z_mem_baseRet b').2⟩
  have heq : EqOn (a'.c.φ.transition b'.c.φ ∘ a'.baseRet b')
      (a.c.φ.transition b.c.φ ∘ a.baseRet b) R₁₃.U := by
    intro u hu
    obtain ⟨y, hy, hy', hyu⟩ := a'.exists_eq_of_mem_baseRet b' (hV₃ hu)
    have hyu' : r a.c.R u = a.c.φ (L.ϕ y) := hyu
    change b.c.φ (L.ϕ (L.g (a.c.φ.symm (r a.c.R u)))) = b.c.φ (a.c.φ.symm (r a.c.R u))
    rw [hyu', a.c.φ.symm_apply_apply hy.2, L.base.left_inv y hy.1]
  exact congrArg (fun T : a.c.φ.model.E 0 →L[ℝ] b.c.φ.model.E 0 => T v)
    (scDeriv_eq_of_eqOn_relOpen R₁₃.relOpen (a'.isSc1_transition b') (a.isSc1_transition b) hV₃ hV₁
      heq hzV)

/-- **The fibre transitions between two carried chart points are those between the original
ones**: `Φ_b ∘ Φ ∘ Ψ ∘ Φ_a⁻¹ = Φ_b ∘ Φ_a⁻¹` over `x`. -/
theorem fiberMap_pullPt (L : LocalIso B B U U') {a b : ChartPoint B x} (ha : a.c.φ.source ⊆ U')
    (hb : b.c.φ.source ⊆ U') (hx' : x' ∈ U) (hϕ : L.ϕ x' = x) (k : a.c.F 0) :
    (L.pullPt a ha hx' hϕ).fiberMap (L.pullPt b hb hx' hϕ) k = a.fiberMap b k := by
  set w : a.c.φ.model.E 0 × a.c.F 0 :=
    (a.c.φ.model.E.toBase 1 a.z, ρ a.c.R (a.c.φ.model.E.toBase 1 a.z) k) with hw
  have hwK : w ∈ a.c.toPartialEquiv.target := by
    rw [a.c.target_eq]; exact a.c.mem_K_ρ a.toBase_z_mem_O k
  have hsrc := a.c.toPartialEquiv.map_target hwK
  have hU' : P (a.c.toPartialEquiv.symm w) ∈ U' := by
    rw [a.c.source_eq] at hsrc; exact ha hsrc
  change (b.c (L.Φ (L.Ψ (a.c.toPartialEquiv.symm w)))).2 = (b.c (a.c.toPartialEquiv.symm w)).2
  rw [L.zero.right_inv _ hU']

/-- `T_xX` read in two carried chart points: the identification is that of the original chart
points. -/
theorem transferT_pullPt (L : LocalIso B B U U') {a b : ChartPoint B x} (ha : a.c.φ.source ⊆ U')
    (hb : b.c.φ.source ⊆ U') (hx' : x' ∈ U) (hϕ : L.ϕ x' = x) (v : ↥a.T) :
    (Subtype.val ((L.pullPt a ha hx' hϕ).transferT (L.pullPt b hb hx' hϕ) v) : b.c.φ.model.E 0) =
      a.transferT b v :=
  baseDeriv_pullPt L ha hb hx' hϕ v

/-- `Y_x` read in two carried chart points: the identification is that of the original chart
points. -/
theorem transferK_pullPt (L : LocalIso B B U U') {a b : ChartPoint B x} (ha : a.c.φ.source ⊆ U')
    (hb : b.c.φ.source ⊆ U') (hx' : x' ∈ U) (hϕ : L.ϕ x' = x) (k : ↥a.K) :
    (Subtype.val ((L.pullPt a ha hx' hϕ).transferK (L.pullPt b hb hx' hϕ) k) : b.c.F 0) =
      a.transferK b k :=
  fiberMap_pullPt L ha hb hx' hϕ k

end Transfer

/-! ### Two composite carried chart points that agree near the point -/

section Compose

variable {U₂ U₂' U₃ U₃' : Set X}

/-- **Germ agreement of two local isomorphisms near `x''`**: on an open `N ∋ x''` inside `U₂`
and `U₃`, the composite `L ∘ L₂` and `L₃` have the same base map and the same bundle map. -/
structure GermAgree (L : LocalIso B B U U') (L₂ : LocalIso B B U₂ U₂')
    (L₃ : LocalIso B B U₃ U₃') (x'' : X) : Prop where
  exists_nhds : ∃ N : Set X, IsOpen N ∧ x'' ∈ N ∧ N ⊆ U₂ ∧ N ⊆ U₃ ∧
    (∀ y ∈ N, L.ϕ (L₂.ϕ y) = L₃.ϕ y) ∧ ∀ w, P w ∈ N → L.Φ (L₂.Φ w) = L₃.Φ w

/-- **Two composite carried chart points with the same germ**: the base derivative from the
chart point carried by `L₃` to the one carried by `L` and then `L₂` is `Dr(z)`, as from a chart
point to itself (`ChartPoint.baseDeriv_self`). -/
theorem baseDeriv_pullPt_pullPt {L : LocalIso B B U U'} {L₂ : LocalIso B B U₂ U₂'}
    {L₃ : LocalIso B B U₃ U₃'} {x'' : X} (p : ChartPoint B x) (hx' : x' ∈ U) (hϕ : L.ϕ x' = x)
    (h₁ : p.c.φ.source ⊆ U')
    (h₂ : (L.pullPt p h₁ hx' hϕ).c.φ.source ⊆ U₂') (hx'' : x'' ∈ U₂) (hϕ₂ : L₂.ϕ x'' = x')
    (h₃ : p.c.φ.source ⊆ U₃') (hx''₃ : x'' ∈ U₃) (hϕ₃ : L₃.ϕ x'' = x)
    (hG : GermAgree L L₂ L₃ x'') (v : p.c.φ.model.E 0) :
    (L₃.pullPt p h₃ hx''₃ hϕ₃).baseDeriv (L₂.pullPt (L.pullPt p h₁ hx' hϕ) h₂ hx'' hϕ₂) v =
      p.baseDeriv p v := by
  obtain ⟨N, hNo, hxN, hN₂, hN₃, hNϕ, -⟩ := hG.exists_nhds
  set a₃ := L₃.pullPt p h₃ hx''₃ hϕ₃ with ha₃
  set a₁₂ := L₂.pullPt (L.pullPt p h₁ hx' hϕ) h₂ hx'' hϕ₂ with ha₁₂
  obtain ⟨G, hGo, hG⟩ := a₃.c.φ.exists_isOpen_image_eq (s := N ∩ a₃.c.φ.source)
    inter_subset_right (hNo.inter a₃.c.φ.isOpen_source)
  set R' := (a₃.baseRet a₁₂).restrict hGo with hR'
  have hV₁ : R'.U ⊆ (a₃.baseRet a₁₂).U := inter_subset_left
  have hV₂ : R'.U ⊆ p.c.U := fun u hu => (a₃.baseRet_U_subset a₁₂) hu.1
  have hzG : r p.c.R (p.c.φ.model.E.toBase 1 p.z) ∈ G := by
    rw [p.r_toBase_z]
    have : a₃.c.φ x'' ∈ a₃.c.φ '' (N ∩ a₃.c.φ.source) := ⟨x'', ⟨hxN, a₃.mem_source⟩, rfl⟩
    rw [hG] at this
    have h' : a₃.c.φ x'' = p.c.φ.model.E.toBase 1 p.z := a₃.toBase_z.symm
    rw [h'] at this
    exact this.2
  have hzV : p.z ∈ p.c.φ.model.E.lvlSet R'.U 1 := ⟨a₃.z_mem_baseRet a₁₂, hzG⟩
  have hr1 : IsSc1 p.c.U (r p.c.R) := (r_isScSmooth p.c.relOpen p.c.isRetraction).isSc1
  have heq : EqOn (a₃.c.φ.transition a₁₂.c.φ ∘ a₃.baseRet a₁₂) (r p.c.R) R'.U := by
    intro u hu
    obtain ⟨y, hy, hy', hyu⟩ := a₃.exists_eq_of_mem_baseRet a₁₂ (hV₁ hu)
    have hrG : r p.c.R u ∈ a₃.c.φ.model.O ∩ G :=
      ⟨(Set.ext_iff.1 (L₃.transportChart_model_O p.c h₃) _).2 (p.c.r_mem_O (hV₂ hu)), hu.2⟩
    rw [← hG] at hrG
    obtain ⟨y₂, ⟨hy₂N, hy₂s⟩, hy₂u⟩ := hrG
    have hyy : y₂ = y := by
      have e : a₃.c.φ y₂ = a₃.c.φ y := hy₂u.trans hyu
      rw [← a₃.c.φ.symm_apply_apply hy₂s, ← a₃.c.φ.symm_apply_apply hy, e]
    subst hyy
    have hyu' : r p.c.R u = p.c.φ (L₃.ϕ y₂) := hyu
    change p.c.φ (L.ϕ (L₂.ϕ (L₃.g (p.c.φ.symm (r p.c.R u))))) = r p.c.R u
    rw [hyu', p.c.φ.symm_apply_apply hy.2, L₃.base.left_inv y₂ hy.1, hNϕ y₂ hy₂N]
  have := scDeriv_eq_of_eqOn_relOpen R'.relOpen (a₃.isSc1_transition a₁₂) hr1 hV₁ hV₂ heq hzV
  rw [p.baseDeriv_self]
  exact congrArg (fun T : p.c.φ.model.E 0 →L[ℝ] p.c.φ.model.E 0 => T v) this

/-- **Two composite carried chart points with the same germ**: the fibre transition between them
over `x''` is the identity on `K_z` (`ChartPoint.fiberMap_self`). -/
theorem fiberMap_pullPt_pullPt {L : LocalIso B B U U'} {L₂ : LocalIso B B U₂ U₂'}
    {L₃ : LocalIso B B U₃ U₃'} {x'' : X} (p : ChartPoint B x) (hx' : x' ∈ U) (hϕ : L.ϕ x' = x)
    (h₁ : p.c.φ.source ⊆ U')
    (h₂ : (L.pullPt p h₁ hx' hϕ).c.φ.source ⊆ U₂') (hx'' : x'' ∈ U₂) (hϕ₂ : L₂.ϕ x'' = x')
    (h₃ : p.c.φ.source ⊆ U₃') (hx''₃ : x'' ∈ U₃) (hϕ₃ : L₃.ϕ x'' = x)
    (hG : GermAgree L L₂ L₃ x'') (k : p.c.F 0) :
    (L₃.pullPt p h₃ hx''₃ hϕ₃).fiberMap (L₂.pullPt (L.pullPt p h₁ hx' hϕ) h₂ hx'' hϕ₂) k =
      p.fiberMap p k := by
  obtain ⟨N, -, hxN, -, -, -, hNΦ⟩ := hG.exists_nhds
  set w : p.c.φ.model.E 0 × p.c.F 0 :=
    (p.c.φ.model.E.toBase 1 p.z, ρ p.c.R (p.c.φ.model.E.toBase 1 p.z) k) with hw
  have hwK : w ∈ p.c.toPartialEquiv.target := by
    rw [p.c.target_eq]; exact p.c.mem_K_ρ p.toBase_z_mem_O k
  have hsrc := p.c.toPartialEquiv.map_target hwK
  have hPx : P (p.c.toPartialEquiv.symm w) = x := by
    have h1 := p.c.covers _ hsrc
    rw [p.c.toPartialEquiv.right_inv hwK] at h1
    have h2 : p.c.φ.model.E.toBase 1 p.z = p.c.φ (P (p.c.toPartialEquiv.symm w)) := h1
    rw [p.c.source_eq] at hsrc
    rw [p.toBase_z] at h2
    rw [← p.c.φ.symm_apply_apply hsrc, ← h2, p.c.φ.symm_apply_apply p.mem_source]
  have hU₃' : P (p.c.toPartialEquiv.symm w) ∈ U₃' := by rw [hPx]; exact h₃ p.mem_source
  have hPΨ : P (L₃.Ψ (p.c.toPartialEquiv.symm w)) ∈ N := by
    rw [L₃.covers_inv _ hU₃', hPx, ← hϕ₃, L₃.base.left_inv _ hx''₃]; exact hxN
  change (p.c (L.Φ (L₂.Φ (L₃.Ψ (p.c.toPartialEquiv.symm w))))).2 =
    (p.c (p.c.toPartialEquiv.symm w)).2
  rw [hNΦ _ hPΨ, L₃.zero.right_inv _ hU₃']

/-- The identification of `T_xX` between the two composite carried chart points is the
identity. -/
theorem transferT_pullPt_pullPt {L : LocalIso B B U U'} {L₂ : LocalIso B B U₂ U₂'}
    {L₃ : LocalIso B B U₃ U₃'} {x'' : X} (p : ChartPoint B x) (hx' : x' ∈ U) (hϕ : L.ϕ x' = x)
    (h₁ : p.c.φ.source ⊆ U')
    (h₂ : (L.pullPt p h₁ hx' hϕ).c.φ.source ⊆ U₂') (hx'' : x'' ∈ U₂) (hϕ₂ : L₂.ϕ x'' = x')
    (h₃ : p.c.φ.source ⊆ U₃') (hx''₃ : x'' ∈ U₃) (hϕ₃ : L₃.ϕ x'' = x)
    (hG : GermAgree L L₂ L₃ x'') (v : ↥p.T) :
    (Subtype.val ((L₃.pullPt p h₃ hx''₃ hϕ₃).transferT
      (L₂.pullPt (L.pullPt p h₁ hx' hϕ) h₂ hx'' hϕ₂) v) : p.c.φ.model.E 0) = v :=
  (baseDeriv_pullPt_pullPt p hx' hϕ h₁ h₂ hx'' hϕ₂ h₃ hx''₃ hϕ₃ hG v).trans
    (congrArg Subtype.val (p.transferT_self_apply v))

/-- The identification of `Y_x` between the two composite carried chart points is the
identity. -/
theorem transferK_pullPt_pullPt {L : LocalIso B B U U'} {L₂ : LocalIso B B U₂ U₂'}
    {L₃ : LocalIso B B U₃ U₃'} {x'' : X} (p : ChartPoint B x) (hx' : x' ∈ U) (hϕ : L.ϕ x' = x)
    (h₁ : p.c.φ.source ⊆ U')
    (h₂ : (L.pullPt p h₁ hx' hϕ).c.φ.source ⊆ U₂') (hx'' : x'' ∈ U₂) (hϕ₂ : L₂.ϕ x'' = x')
    (h₃ : p.c.φ.source ⊆ U₃') (hx''₃ : x'' ∈ U₃) (hϕ₃ : L₃.ϕ x'' = x)
    (hG : GermAgree L L₂ L₃ x'') (k : ↥p.K) :
    (Subtype.val ((L₃.pullPt p h₃ hx''₃ hϕ₃).transferK
      (L₂.pullPt (L.pullPt p h₁ hx' hϕ) h₂ hx'' hϕ₂) k) : p.c.F 0) = k :=
  (fiberMap_pullPt_pullPt p hx' hϕ h₁ h₂ hx'' hϕ₂ h₃ hx''₃ hϕ₃ hG k).trans
    (congrArg Subtype.val (p.transferK_self_apply k))

end Compose

end StrongBundle.LocalIso

end Polyfold
