import Polyfold.Chapter13.StrongBundlePullMap

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.4, pp. 621–628: **Theorem 13.4.1** (pull-back of structurable sc⁺-multisections along a strong
bundle equivalence, with the canonical structure) and **Theorem 13.4.4** (pull-back along a proper
strong bundle covering) (2017: Theorems 13.3 and 13.5).

# Structurable sc⁺-multisections pull back

## The text, paraphrased

(Theorem 13.4.1) For a strong bundle equivalence `Φ : W → W'` covering `F : X → X'` and a
structurable `Λ'`, `Φ^*Λ' = Λ' ∘ Φ` is structurable, and a structured `Λ'` gives a canonical
structure on `Φ^*Λ'`.  *Proof*: take `U(x)` with the natural `G_x`-action, the properness
property, `F : U(x) → F(U(x))` an sc-diffeomorphism and `F(U(x)) ⊆ U'(F(x))`; `F` maps the
components of `𝒰(x, y)` into components of `𝒰'(F(x), F(y))`, so `(U(x))` is a good system;
`I_x := I'_{F(x)}`, `τ_{x,y}(φ) := τ'_{F(x),F(y)}(F(φ))`, `Φ(sˣᵢ(z)) = s'^{F(x)}ᵢ(F(z))`.
(Theorem 13.4.4) The same for a proper strong bundle covering, with `G_y` acting on `I_y = I_x`
through `F`, after `F(Γ_Y(g, z)) = Γ_X(F(g), F(z))`.

## What is formalized (namespace `Polyfold.SBLocalization`)

For pull-back data `M : PullMap C A` (`StrongBundlePullMap`):
* `PullMap.exists_isLocalRepOn_pull`, `PullMap.isScPlusMultisection_pull`: `Λ' ∘ Φ` is an
  sc⁺-multisection.
* `PullMap.IsPullNbhd N N'`: `F` injective on `U(x)`, `F(U(x)) ⊆ U'(F(x))` and
  `F(Γ(g, z)) = Γ'(F(g), F(z))` on `U(x)`; `PullMap.exists_isPullNbhd` (inside every open set,
  with the properness property).  The identity for `Γ` is obtained on the set where two
  continuous lifts through `s` agree, which is open, and then made invariant.
* `PullMap.PullData 𝒰'`: a good system on `X` with these properties over `𝒰'`;
  `PullMap.exists_pullData` (inside any open neighbourhoods): the condition (3) of good systems is
  `isDiffeoComponent_of_isPull`, the argument of the text.
* `PullMap.pullStructure` (the symmetric structures `Φ(sᵢ(z)) = s'ᵢ(F(z))`, `G_x` acting through
  `F : G_x → G'_{F(x)}`), `PullMap.pullDecoration`, `PullMap.pullTau`
  (`τ_{x,y}(φ) = τ'_{F(x),F(y)}(F(φ))`), `PullMap.pullTuple`, `PullMap.isStructurable_pull`.
* Canonicity: `PullMap.pullTuple_equiv` (equivalent structured tuples pull back to equivalent
  ones, whatever the choices), `PullMap.pullStructured` (the map of structured
  sc⁺-multisections), `PullMap.forget_pullStructured`.
* **Theorem 13.4.1**: `theorem_13_4_1`, `theorem_13_4_1_structured`.
* **Theorem 13.4.4**: `theorem_13_4_4`, `theorem_13_4_4_structured`.

No hypothesis beyond the text's is used; in particular no paracompactness: the good system on
`X` is built point by point, as in the proof.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A C : SEP.{u}} (M : PullMap C A)

namespace PullMap

/-! ### The pulled-back functor is an sc⁺-multisection -/

/-- **A local representation pulls back**: `(sᵢ, σᵢ)` on `O'` gives `(pullSec sᵢ, σᵢ)` on
`F⁻¹(O')`. -/
theorem exists_isLocalRepOn_pull {Λ' : A.W → ℚ≥0} {O' : Set A.Obj} (hO' : IsOpen O') {k : ℕ}
    {s' : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (h : IsLocalRepOn A Λ' O' s' σ) :
    IsLocalRepOn C (M.pull Λ') (M.ϕ.obj ⁻¹' O') (fun i => M.pullSec (s' i)) σ := by
  have hO : IsOpen (M.ϕ.obj ⁻¹' O') := hO'.preimage M.ϕ.continuous_obj'
  refine ⟨h.1, fun i => M.isScPlusSectionOn_pullSec (h.2.1 i) hO fun z hz => hz, h.2.2.1,
    fun w hw => ?_⟩
  have hw' : A.P (M.Φ w) ∈ O' := by rw [M.covers]; exact hw
  rw [pull_apply, h.2.2.2 _ hw', M.covers]
  refine Finset.sum_congr rfl fun i _ => if_congr ?_ rfl rfl
  have e := M.pullSec_eq_iff (s' := s' i) ((h.2.1 i).1 _ hw) (w := w) rfl
  exact ⟨fun h1 => (e.2 h1.symm).symm, fun h1 => (e.1 h1.symm).symm⟩

/-- **`Φ^*Λ'` is an sc⁺-multisection** when `Λ'` is one. -/
theorem isScPlusMultisection_pull {Λ' : A.W → ℚ≥0} (h : IsScPlusMultisection A Λ') :
    IsScPlusMultisection C (M.pull Λ') := by
  refine ⟨M.isWFunctor_pull h.1, fun x => ?_⟩
  obtain ⟨R, k, s', σ, hr⟩ := h.2 (M.ϕ.obj x)
  exact hasLocalSectionStructure_of_isLocalRepOn (R.isOpen_U.preimage M.ϕ.continuous_obj')
    R.mem_U (M.exists_isLocalRepOn_pull R.isOpen_U hr)

/-! ### Neighbourhoods carried by `F` -/

/-- **A neighbourhood `U(x)` adapted to `U'(F(x))`** (the conditions of the proof of Theorem
13.4.1): `F` is injective on `U(x)`, `F(U(x)) ⊆ U'(F(x))`, and `F(Γ(g, z)) = Γ'(F(g), F(z))` for
`z ∈ U(x)` (the identity of the proof of Theorem 13.4.4). -/
structure IsPullNbhd {x : C.Obj} (N : C.X.NatNbhd x) (N' : A.X.NatNbhd (M.ϕ.obj x)) : Prop where
  injOn : InjOn M.ϕ.obj N.U
  mapsTo : MapsTo M.ϕ.obj N.U N'.U
  Γ_eq : ∀ g, ∀ y ∈ N.U,
    M.ϕ.mor (N.rep.Γ g y) = N'.rep.Γ (M.ϕ.isotropyHom x g) (M.ϕ.obj y)

variable {M}

/-- `F(g ∗ z) = F(g) ∗ F(z)`. -/
theorem IsPullNbhd.Φ_eq {x : C.Obj} {N : C.X.NatNbhd x} {N' : A.X.NatNbhd (M.ϕ.obj x)}
    (h : M.IsPullNbhd N N') (g : C.X.Isotropy x) {y : C.Obj} (hy : y ∈ N.U) :
    M.ϕ.obj (N.rep.Φ g y) = N'.rep.Φ (M.ϕ.isotropyHom x g) (M.ϕ.obj y) := by
  have e := congrArg A.X.tgt (h.Γ_eq g y hy)
  rwa [M.ϕ.tgt_mor, N.tgt_Γ g hy, N'.tgt_Γ _ (h.mapsTo hy)] at e

variable (M)

/-- **Adapted neighbourhoods exist** inside every open `V ∋ x`, with the properness property:
`F` is a local sc-diffeomorphism, and `z ↦ F(Γ(g, z))`, `z ↦ Γ'(F(g), F(z))` are continuous lifts
of `F` through `s` agreeing at `x`, so they agree on an open set, made invariant afterwards. -/
theorem exists_isPullNbhd {x : C.Obj} (N' : A.X.NatNbhd (M.ϕ.obj x)) {V : Set C.Obj}
    (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ N : C.X.NatNbhd x, M.IsPullNbhd N N' ∧ C.X.IsProperSubset (closure N.U) ∧ N.U ⊆ V := by
  obtain ⟨U₀, U₀', g₀, hxU₀, hd⟩ := M.isLocalScDiffeo_obj x
  set O : Set C.Obj := V ∩ U₀ ∩ M.ϕ.obj ⁻¹' N'.U with hOdef
  have hO : IsOpen O :=
    (hV.inter hd.isOpen_source).inter (N'.isOpen_U.preimage M.ϕ.continuous_obj')
  have hxO : x ∈ O := ⟨⟨hxV, hxU₀⟩, N'.mem_U⟩
  obtain ⟨N₀, hN₀O, hprop⟩ := C.X.exists_natNbhd_isProperSubset x hO hxO
  set E : Set C.Obj := N₀.U ∩ ⋂ g, {y | y ∈ N₀.U ∧
    M.ϕ.mor (N₀.rep.Γ g y) = N'.rep.Γ (M.ϕ.isotropyHom x g) (M.ϕ.obj y)} with hEdef
  have hE : IsOpen E := by
    refine N₀.isOpen_U.inter (isOpen_iInter_of_finite fun g => ?_)
    refine A.X.isOpen_setOf_eq_of_src N₀.isOpen_U
      (M.ϕ.continuous_mor.comp_continuousOn
        ((N₀.rep.isScSmoothOn_Γ g).continuousOn.mono N₀.U_subset))
      ((N'.rep.isScSmoothOn_Γ _).continuousOn.comp M.ϕ.continuous_obj'.continuousOn
        fun y hy => N'.U_subset (hN₀O hy).2) fun y hy => ?_
    rw [M.ϕ.src_mor, N₀.src_Γ g hy, N'.src_Γ _ (hN₀O hy).2]
  have hxE : x ∈ E := ⟨N₀.mem_U, mem_iInter.2 fun g => ⟨N₀.mem_U, by
    rw [N₀.rep.Γ_self, N'.rep.Γ_self]; rfl⟩⟩
  obtain ⟨N, hrep, hsub⟩ := N₀.exists_restrict_subset hE hxE
  have hNO : ∀ y ∈ N.U, y ∈ O := fun y hy => hN₀O (hsub hy).1
  refine ⟨N, ⟨fun a ha b hb e => ?_, fun y hy => (hNO y hy).2, fun g y hy => ?_⟩,
    isProperMap_domRestrict_of_subset_of_isClosed C.X.continuous_src hprop
      (closure_mono fun y hy => (hsub hy).1) isClosed_closure,
    fun y hy => (hNO y hy).1.1⟩
  · rw [← hd.left_inv a (hNO a ha).1.2, e, hd.left_inv b (hNO b hb).1.2]
  · rw [hrep]
    exact (mem_iInter.1 (hsub hy).2.2 g).2

/-- `F` maps `𝒰(S, T)` into `𝒰'(S', T')` when it maps `S`, `T` into `S'`, `T'`. -/
theorem mem_morBetween {S T : Set C.Obj} {S' T' : Set A.Obj} (hS : MapsTo M.ϕ.obj S S')
    (hT : MapsTo M.ϕ.obj T T') {φ : C.Mor} (hφ : φ ∈ C.X.morBetween S T) :
    M.ϕ.mor φ ∈ A.X.morBetween S' T' :=
  ⟨by rw [M.ϕ.src_mor]; exact hS hφ.1, by rw [M.ϕ.tgt_mor]; exact hT hφ.2⟩

/-- **`F` maps components into components**: the component of `φ` in `𝒰(S, T)` goes into the
component of `F(φ)` in `𝒰'(S', T')`. -/
theorem mapsTo_connectedComponentIn {S T : Set C.Obj} {S' T' : Set A.Obj}
    (hS : MapsTo M.ϕ.obj S S') (hT : MapsTo M.ϕ.obj T T') {φ : C.Mor}
    (hφ : φ ∈ C.X.morBetween S T) :
    MapsTo M.ϕ.mor (connectedComponentIn (C.X.morBetween S T) φ)
      (connectedComponentIn (A.X.morBetween S' T') (M.ϕ.mor φ)) := by
  intro ψ hψ
  have hpre := (isPreconnected_connectedComponentIn :
    IsPreconnected (connectedComponentIn (C.X.morBetween S T) φ)).image
    M.ϕ.mor M.ϕ.continuous_mor.continuousOn
  refine hpre.subset_connectedComponentIn ⟨φ, mem_connectedComponentIn hφ, rfl⟩ ?_
    ⟨ψ, hψ, rfl⟩
  rintro _ ⟨χ, hχ, rfl⟩
  exact M.mem_morBetween hS hT (connectedComponentIn_subset _ _ hχ)

/-- **Condition (3) of good systems is carried back** (proof of Theorem 13.4.1): on a component
`Σ` of `𝒰(x, x')`, `s` is injective because `F(Σ)` lies in a component of `𝒰'(F(x), F(x'))`,
`F` is injective on `U(x')` and faithful; the same for `t`. -/
theorem isDiffeoComponent_of_isPull (𝒰' : A.X.GoodSystem) {x x' : C.Obj} {N : C.X.NatNbhd x}
    {N₁ : C.X.NatNbhd x'} (h : M.IsPullNbhd N (𝒰'.nbhd (M.ϕ.obj x)))
    (h₁ : M.IsPullNbhd N₁ (𝒰'.nbhd (M.ϕ.obj x'))) {φ : C.Mor}
    (hφ : φ ∈ C.X.morBetween N.U N₁.U) :
    C.X.IsDiffeoComponent (connectedComponentIn (C.X.morBetween N.U N₁.U) φ) := by
  have hmaps := M.mapsTo_connectedComponentIn h.mapsTo h₁.mapsTo hφ
  have hφ' : M.ϕ.mor φ ∈ 𝒰'.mor (M.ϕ.obj x) (M.ϕ.obj x') :=
    M.mem_morBetween h.mapsTo h₁.mapsTo hφ
  have hsub : ∀ {ψ}, ψ ∈ connectedComponentIn (C.X.morBetween N.U N₁.U) φ →
      ψ ∈ C.X.morBetween N.U N₁.U := fun hψ => connectedComponentIn_subset _ _ hψ
  refine (isDiffeoComponent_iff_injOn (isOpen_connectedComponentIn_mor C.X
    (isOpen_morBetween N.isOpen_U N₁.isOpen_U) φ)).2
    ⟨fun ψ₁ hψ₁ ψ₂ hψ₂ e => ?_, fun ψ₁ hψ₁ ψ₂ hψ₂ e => ?_⟩
  · have e' : M.ϕ.mor ψ₁ = M.ϕ.mor ψ₂ := 𝒰'.injOn_src_comp hφ' (hmaps hψ₁) (hmaps hψ₂)
      (by rw [M.ϕ.src_mor, M.ϕ.src_mor, e])
    have et : C.X.tgt ψ₁ = C.X.tgt ψ₂ := h₁.injOn (hsub hψ₁).2 (hsub hψ₂).2
      (by rw [← M.ϕ.tgt_mor, ← M.ϕ.tgt_mor, e'])
    exact M.mor_injective _ _ e et e'
  · have e' : M.ϕ.mor ψ₁ = M.ϕ.mor ψ₂ := 𝒰'.injOn_tgt_comp hφ' (hmaps hψ₁) (hmaps hψ₂)
      (by rw [M.ϕ.tgt_mor, M.ϕ.tgt_mor, e])
    have es : C.X.src ψ₁ = C.X.src ψ₂ := h.injOn (hsub hψ₁).1 (hsub hψ₂).1
      (by rw [← M.ϕ.src_mor, ← M.ϕ.src_mor, e'])
    exact M.mor_injective _ _ es e e'

variable {M} in
/-- **`F` intertwines the bi-actions**: `F(g' ∗ φ ∗ g) = F(g') ∗ F(φ) ∗ F(g)`. -/
theorem IsPullNbhd.mor_biact {x x' : C.Obj} {N : C.X.NatNbhd x} {N₁ : C.X.NatNbhd x'}
    {N' : A.X.NatNbhd (M.ϕ.obj x)} {N₁' : A.X.NatNbhd (M.ϕ.obj x')} (h : M.IsPullNbhd N N')
    (h₁ : M.IsPullNbhd N₁ N₁') {φ : C.Mor} (hφ : φ ∈ C.X.morBetween N.U N₁.U)
    (g' : C.X.Isotropy x') (g : C.X.Isotropy x) :
    M.ϕ.mor (biact N N₁ g' φ g) =
      biact N' N₁' (M.ϕ.isotropyHom x' g') (M.ϕ.mor φ) (M.ϕ.isotropyHom x g) := by
  have hy : N.rep.Φ g⁻¹ (C.X.src φ) ∈ N.U := N.Φ_mem g⁻¹ hφ.1
  have h1 : C.X.src φ = C.X.tgt (N.rep.Γ g (N.rep.Φ g⁻¹ (C.X.src φ))) := by
    rw [N.tgt_Γ g hy, N.Φ_Φ_inv g hφ.1]
  have h2 : C.X.src (N₁.rep.Γ g' (C.X.tgt φ)) =
      C.X.tgt (C.X.comp φ (N.rep.Γ g (N.rep.Φ g⁻¹ (C.X.src φ)))) := by
    rw [N₁.src_Γ g' hφ.2, C.X.tgt_comp _ _ h1]
  unfold biact
  rw [M.ϕ.mor_comp _ _ h2, M.ϕ.mor_comp _ _ h1, h₁.Γ_eq g' _ hφ.2, h.Γ_eq g _ hy,
    h.Φ_eq g⁻¹ hφ.1, map_inv, M.ϕ.tgt_mor, M.ϕ.src_mor]

/-! ### Good systems carried by `F` -/

/-- **A good system on `X` adapted to the good system `𝒰'` on `X'`** (proof of Theorem 13.4.1). -/
structure PullData (𝒰' : A.X.GoodSystem) where
  /-- The good system `(U(x))` on `X`. -/
  𝒰 : C.X.GoodSystem
  isPull : ∀ x, M.IsPullNbhd (𝒰.nbhd x) (𝒰'.nbhd (M.ϕ.obj x))

/-- **Adapted good systems exist** inside any open neighbourhoods `V(x)` (no paracompactness
needed: each `U(x)` is chosen separately, and condition (3) comes from `𝒰'`). -/
theorem exists_pullData (𝒰' : A.X.GoodSystem) (V : C.Obj → Set C.Obj) (hV : ∀ x, IsOpen (V x))
    (hxV : ∀ x, x ∈ V x) : ∃ P : M.PullData 𝒰', ∀ x, P.𝒰.U x ⊆ V x := by
  choose N hN hprop hsub using fun x => M.exists_isPullNbhd (𝒰'.nbhd (M.ϕ.obj x)) (hV x) (hxV x)
  exact ⟨⟨⟨N, hprop, fun x x' φ hφ => M.isDiffeoComponent_of_isPull 𝒰' (hN x) (hN x') hφ⟩, hN⟩,
    hsub⟩

/-- A chosen adapted good system. -/
def somePullData (𝒰' : A.X.GoodSystem) : M.PullData 𝒰' :=
  (M.exists_pullData 𝒰' (fun _ => univ) (fun _ => isOpen_univ) fun _ => mem_univ _).choose

namespace PullData

variable {M} {𝒰' : A.X.GoodSystem} (P : M.PullData 𝒰')

theorem mapsTo (x : C.Obj) : MapsTo M.ϕ.obj (P.𝒰.U x) (𝒰'.U (M.ϕ.obj x)) := (P.isPull x).mapsTo

theorem mor_mem {x y : C.Obj} {φ : C.Mor} (hφ : φ ∈ P.𝒰.mor x y) :
    M.ϕ.mor φ ∈ 𝒰'.mor (M.ϕ.obj x) (M.ϕ.obj y) :=
  M.mem_morBetween (P.mapsTo x) (P.mapsTo y) hφ

theorem mapsTo_comp {x y : C.Obj} {φ : C.Mor} (hφ : φ ∈ P.𝒰.mor x y) :
    MapsTo M.ϕ.mor (P.𝒰.comp x y φ) (𝒰'.comp (M.ϕ.obj x) (M.ϕ.obj y) (M.ϕ.mor φ)) :=
  M.mapsTo_connectedComponentIn (P.mapsTo x) (P.mapsTo y) hφ

theorem mor_biact {x y : C.Obj} {φ : C.Mor} (hφ : φ ∈ P.𝒰.mor x y) (g' : C.X.Isotropy y)
    (g : C.X.Isotropy x) :
    M.ϕ.mor (P.𝒰.biact x y g' φ g) = 𝒰'.biact (M.ϕ.obj x) (M.ϕ.obj y)
      (M.ϕ.isotropyHom y g') (M.ϕ.mor φ) (M.ϕ.isotropyHom x g) :=
  (P.isPull x).mor_biact (P.isPull y) hφ g' g

end PullData

/-! ### The pulled-back symmetric structures and correspondences -/

variable {M}

/-- **The pulled-back symmetric structure** (proof of Theorem 13.4.1): `I_x = I'_{F(x)}` with
`g(i) = F(g)(i)`, and `Φ(sᵢ(z)) = s'ᵢ(F(z))`. -/
def pullStructure {Λ' : A.W → ℚ≥0} {x : C.Obj} {N : C.X.NatNbhd x}
    {N' : A.X.NatNbhd (M.ϕ.obj x)} (hN : M.IsPullNbhd N N') (S' : SymmetricStructureOn A Λ' N') :
    SymmetricStructureOn C (M.pull Λ') N where
  I := S'.I
  fintype := S'.fintype
  mulAction := MulAction.compHom S'.I (M.ϕ.isotropyHom x)
  s i := M.pullSec (S'.s i)
  isScPlusSectionOn i := M.isScPlusSectionOn_pullSec (S'.isScPlusSectionOn i) N.isOpen_U hN.mapsTo
  equivariant g i y hy := by
    have hy' := hN.mapsTo hy
    have hgy := N.Φ_mem g hy
    have hsrc : C.P (M.pullSec (S'.s i) y) = C.X.src (N.rep.Γ g y) := by
      rw [M.P_pullSec, N.src_Γ g hy]
    refine M.eq_of_obj_eq ?_ ?_
    · rw [M.P_pullSec, P_fibAct hsrc, N.tgt_Γ g hy]
    · rw [M.obj_pullSec (S'.P_s _ (hN.mapsTo hgy)), M.obj_fibAct hsrc,
        M.obj_pullSec (S'.P_s _ hy'), hN.Φ_eq g hy, hN.Γ_eq g y hy]
      exact S'.equivariant (M.ϕ.isotropyHom x g) i (M.ϕ.obj y) hy'
  rep w hw := by
    have hw' : A.P (M.Φ w) ∈ N'.U := by rw [M.covers]; exact hN.mapsTo hw
    rw [pull_apply, S'.rep (M.Φ w) hw', M.covers]
    have e : (Finset.univ.filter fun i => S'.s i (M.ϕ.obj (C.P w)) = M.Φ w) =
        Finset.univ.filter fun i => M.pullSec (S'.s i) (C.P w) = w :=
      Finset.filter_congr fun i _ => (M.pullSec_eq_iff (S'.P_s i (hN.mapsTo hw)) rfl).symm
    rw [e]

@[simp] theorem pullStructure_I {Λ' : A.W → ℚ≥0} {x : C.Obj} {N : C.X.NatNbhd x}
    {N' : A.X.NatNbhd (M.ϕ.obj x)} (hN : M.IsPullNbhd N N') (S' : SymmetricStructureOn A Λ' N') :
    (pullStructure hN S').I = S'.I := rfl

/-- **The pulled-back system of symmetric structures** `(𝒰, S)`. -/
def pullDecoration {Λ' : A.W → ℚ≥0} (D' : Decoration A Λ') (P : M.PullData D'.𝒰) :
    Decoration C (M.pull Λ') :=
  ⟨P.𝒰, fun x => pullStructure (P.isPull x) (D'.S (M.ϕ.obj x))⟩

/-- The bi-action on `J(x, y)` through `F` is the bi-action of `F(g')`, `F(g)`. -/
theorem biact_compHom {α β : Type u} {G G' H H' : Type*} [Group G] [Group G'] [Group H]
    [Group H'] [MulAction H α] [MulAction H' β] (f : G →* H) (f' : G' →* H') (g' : G')
    (τ : IndexCorr α β) (g : G) :
    @IndexCorr.biact α β G G' _ _ (MulAction.compHom α f) (MulAction.compHom β f') g' τ g =
      IndexCorr.biact (f' g') τ (f g) := by
  unfold IndexCorr.biact
  congr 1
  · ext i
    change f g⁻¹ • i = (f g)⁻¹ • i
    rw [map_inv]
  · ext i
    rfl

/-- `[I ←id I →g I]` through `F` is `[I ←id I →F(g) I]`. -/
theorem ofPerm_compHom {α : Type u} [Fintype α] {G H : Type*} [Group G] [Group H]
    [MulAction H α] (f : G →* H) (g : G) :
    @IndexCorr.ofPerm α G _ _ (MulAction.compHom α f) g = IndexCorr.ofPerm (f g) :=
  congrArg IndexCorr.ofEquiv (Equiv.ext fun _ => rfl)

/-- **The pulled-back correspondences** `τ_{x,y}(φ) = τ'_{F(x),F(y)}(F(φ))` (proof of Theorem
13.4.1; Theorem 13.4.4: `τ_{y,y'}(φ) = τ_{x,x'}(F(φ))`). -/
def pullTau {Λ' : A.W → ℚ≥0} {D' : Decoration A Λ'} (t' : D'.Tau) (P : M.PullData D'.𝒰) :
    (pullDecoration D' P).Tau where
  τ x y φ := t'.τ (M.ϕ.obj x) (M.ϕ.obj y) (M.ϕ.mor φ)
  isCorrespondence x y :=
    { locallyConstant := fun φ hφ =>
        (M.ϕ.continuous_mor.tendsto φ).eventually
          ((t'.isCorrespondence _ _).locallyConstant _ (P.mor_mem hφ))
      finite := (t'.isCorrespondence _ _).finite.subset (by
        rintro _ ⟨φ, hφ, rfl⟩
        exact ⟨M.ϕ.mor φ, P.mor_mem hφ, rfl⟩)
      biact := fun φ hφ g' g => by
        change t'.τ _ _ (M.ϕ.mor (P.𝒰.biact x y g' φ g)) = _
        rw [P.mor_biact hφ, (t'.isCorrespondence _ _).biact _ (P.mor_mem hφ)]
        exact (biact_compHom _ _ g' _ g).symm
      compat := fun φ hφ => IndexCorr.sat_mono (fun i j H ψ hψ => by
          have hψm : ψ ∈ P.𝒰.mor x y := P.𝒰.comp_subset x y φ hψ
          have hsrc : C.P (M.pullSec ((D'.S (M.ϕ.obj x)).s i) (C.X.src ψ)) = C.X.src ψ :=
            M.P_pullSec _ _
          change M.pullSec ((D'.S (M.ϕ.obj y)).s j) (C.X.tgt ψ) =
            fibAct ψ (M.pullSec ((D'.S (M.ϕ.obj x)).s i) (C.X.src ψ))
          refine M.eq_of_obj_eq ?_ ?_
          · rw [M.P_pullSec, P_fibAct hsrc]
          · rw [M.obj_pullSec ((D'.S _).P_s j (P.mapsTo y hψm.2)), M.obj_fibAct hsrc,
              M.obj_pullSec ((D'.S _).P_s i (P.mapsTo x hψm.1)), ← M.ϕ.tgt_mor,
              ← M.ϕ.src_mor]
            exact H (M.ϕ.mor ψ) (P.mapsTo_comp hφ hψ))
        ((t'.isCorrespondence _ _).compat _ (P.mor_mem hφ)) }
  diag x g y hy := by
    change t'.τ _ _ (M.ϕ.mor ((P.𝒰.nbhd x).rep.Γ g y)) = _
    rw [(P.isPull x).Γ_eq g y hy, t'.diag _ _ _ ((P.isPull x).mapsTo hy)]
    exact (ofPerm_compHom _ g).symm
  swap x y φ hφ := by
    change t'.τ _ _ (M.ϕ.mor φ) = (t'.τ _ _ (M.ϕ.mor (C.X.inv φ))).swap
    rw [t'.swap _ _ _ (P.mor_mem hφ), M.ϕ.mor_inv]

/-- **The pulled-back structured tuple** `(Φ^*Λ', 𝒰, S, τ)`. -/
def pullTuple (T' : StructuredTuple A) (P : M.PullData T'.dec.𝒰) : StructuredTuple C :=
  ⟨⟨M.pull T'.Λ, M.isScPlusMultisection_pull T'.isScPlusMultisection, pullDecoration T'.dec P⟩,
    pullTau T'.tau P⟩

@[simp] theorem pullTuple_Λ (T' : StructuredTuple A) (P : M.PullData T'.dec.𝒰) :
    (pullTuple T' P).Λ = M.pull T'.Λ := rfl

variable (M)

/-- **Pull-backs of structurable sc⁺-multisections are structurable.** -/
theorem isStructurable_pull {Λ' : A.W → ℚ≥0} (h : IsStructurable A Λ') :
    IsStructurable C (M.pull Λ') := by
  obtain ⟨hΛ', D', ⟨t'⟩⟩ := h
  exact ⟨M.isScPlusMultisection_pull hΛ', pullDecoration D' (M.somePullData D'.𝒰),
    ⟨pullTau t' (M.somePullData D'.𝒰)⟩⟩

variable {M}

/-- **The canonical structure** (Theorem 13.4.1, last sentence): equivalent structured tuples pull
back to equivalent structured tuples, whatever adapted good systems are used. -/
theorem pullTuple_equiv {T₁ T₂ : StructuredTuple A} (h : T₁.Equiv T₂) (P₁ : M.PullData T₁.dec.𝒰)
    (P₂ : M.PullData T₂.dec.𝒰) : (pullTuple T₁ P₁).Equiv (pullTuple T₂ P₂) := by
  obtain ⟨hΛ, 𝒰'', hsub, hI, hτ⟩ := h
  obtain ⟨𝒲, h𝒲⟩ := P₁.𝒰.exists_subset_inter
    (fun x => P₂.𝒰.U x ∩ M.ϕ.obj ⁻¹' 𝒰''.U (M.ϕ.obj x))
    (fun x => (P₂.𝒰.isOpen_U x).inter ((𝒰''.isOpen_U _).preimage M.ϕ.continuous_obj'))
    fun x => ⟨P₂.𝒰.mem_U x, 𝒰''.mem_U _⟩
  refine ⟨congrArg M.pull hΛ, 𝒲, fun x y hy => ⟨(h𝒲 x hy).1, (h𝒲 x hy).2.1⟩,
    fun x => hI (M.ϕ.obj x), fun x x' φ hφ => ?_⟩
  exact hτ _ _ (M.ϕ.mor φ) ⟨by rw [M.ϕ.src_mor]; exact (h𝒲 x hφ.1).2.2,
    by rw [M.ϕ.tgt_mor]; exact (h𝒲 x' hφ.2).2.2⟩

variable (M)

/-- **The canonical pull-back of structured sc⁺-multisections** `[Λ', 𝒰', S', τ'] ↦
[Φ^*Λ', 𝒰, S, τ]` (well defined by `pullTuple_equiv`). -/
def pullStructured : StructuredMultisection A → StructuredMultisection C :=
  Quotient.lift (fun T' : StructuredTuple A =>
      (Quotient.mk _ (pullTuple T' (M.somePullData T'.dec.𝒰)) : StructuredMultisection C))
    fun _ _ h => Quotient.sound (pullTuple_equiv h _ _)

theorem pullStructured_mk (T' : StructuredTuple A) (P : M.PullData T'.dec.𝒰) :
    M.pullStructured (Quotient.mk _ T') = Quotient.mk _ (pullTuple T' P) :=
  Quotient.sound (pullTuple_equiv (StructuredTuple.equivalence.refl T') _ _)

/-- The underlying functor of the canonical pull-back is `Φ^*Λ'`. -/
theorem forget_pullStructured (L : StructuredMultisection A) :
    (M.pullStructured L).forget = M.pull L.forget :=
  Quotient.inductionOn L fun _ => rfl

end PullMap

/-! ### Theorems 13.4.1 and 13.4.4 -/

/-- **2021 Theorem 13.4.1, p. 621 (2017: Theorem 13.3)**: for a strong bundle equivalence
`Φ : W → W'` covering `F : X → X'` and a structurable sc⁺-multisection functor `Λ'` on `W'`,
`Φ^*Λ' = Λ' ∘ Φ` is structurable.  As printed, no added hypothesis. -/
theorem theorem_13_4_1 {F : C ⟶ A} (hF : SEP.equivalences F) {Λ' : A.W → ℚ≥0}
    (h : IsStructurable A Λ') : IsStructurable C (pullMult F Λ') :=
  (PullMap.ofEquivalence hF).isStructurable_pull h

/-- **2021 Theorem 13.4.1, the canonical structure**: a structured `[Λ', 𝒰', S', τ']` gives the
structured `[Φ^*Λ', 𝒰, S, τ]` with `I_x = I'_{F(x)}`, `Φ(sˣᵢ(z)) = s'^{F(x)}ᵢ(F(z))`,
`τ_{x,y}(φ) = τ'_{F(x),F(y)}(F(φ))`, for every good system `(U(x))` adapted to `𝒰'`; its class
does not depend on the representative of `[Λ', 𝒰', S', τ']` nor on the adapted good system. -/
theorem theorem_13_4_1_structured {F : C ⟶ A} (hF : SEP.equivalences F) :
    ∃ pull : StructuredMultisection A → StructuredMultisection C,
      (∀ L, (pull L).forget = pullMult F L.forget) ∧
      ∀ (T' : StructuredTuple A) (P : (PullMap.ofEquivalence hF).PullData T'.dec.𝒰),
        pull (Quotient.mk _ T') = Quotient.mk _ (PullMap.pullTuple T' P) ∧
        (PullMap.pullTuple T' P).Λ = pullMult F T'.Λ ∧
        (∀ x, ((PullMap.pullTuple T' P).dec.S x).I = (T'.dec.S ((SEP.Hom.ϕ F).obj x)).I) ∧
        ∀ x y φ, (PullMap.pullTuple T' P).tau.τ x y φ =
          T'.tau.τ ((SEP.Hom.ϕ F).obj x) ((SEP.Hom.ϕ F).obj y) ((SEP.Hom.ϕ F).mor φ) :=
  ⟨(PullMap.ofEquivalence hF).pullStructured,
    (PullMap.ofEquivalence hF).forget_pullStructured,
    fun T' P => ⟨(PullMap.ofEquivalence hF).pullStructured_mk T' P, rfl, fun _ => rfl,
      fun _ _ _ => rfl⟩⟩

/-- **2021 Theorem 13.4.4, p. 626 (2017: Theorem 13.5)**: for a proper strong bundle covering
`Φ : E → W` covering the proper covering functor `F : Y → X` (2021 Definition 8.5.9) and a
structurable sc⁺-multisection functor `Λ` on `W`, `Φ^*Λ = Λ ∘ Φ` is structurable.  As printed,
no added hypothesis. -/
theorem theorem_13_4_4 {F : EpFunctor C.X A.X} {Φ : C.W → A.W}
    (hΦ : C.E.IsProperStrongBundleCovering2021 A.E F Φ) {Λ : A.W → ℚ≥0}
    (h : IsStructurable A Λ) : IsStructurable C (Λ ∘ Φ) :=
  (PullMap.ofCovering hΦ).isStructurable_pull h

/-- **Theorem 13.4.4, structured form** (the proof: `I_y = I_x`, `G_y` acting through `F`,
`Φ(sʸᵢ(z)) = sˣᵢ(F(z))`, `τ_{y,y'}(φ) = τ_{x,x'}(F(φ))`), with the same canonicity as
Theorem 13.4.1. -/
theorem theorem_13_4_4_structured {F : EpFunctor C.X A.X} {Φ : C.W → A.W}
    (hΦ : C.E.IsProperStrongBundleCovering2021 A.E F Φ) :
    ∃ pull : StructuredMultisection A → StructuredMultisection C,
      (∀ L, (pull L).forget = L.forget ∘ Φ) ∧
      ∀ (T : StructuredTuple A) (P : (PullMap.ofCovering hΦ).PullData T.dec.𝒰),
        pull (Quotient.mk _ T) = Quotient.mk _ (PullMap.pullTuple T P) ∧
        (∀ y, ((PullMap.pullTuple T P).dec.S y).I = (T.dec.S (F.obj y)).I) ∧
        ∀ y y' φ, (PullMap.pullTuple T P).tau.τ y y' φ = T.tau.τ (F.obj y) (F.obj y') (F.mor φ) :=
  ⟨(PullMap.ofCovering hΦ).pullStructured, (PullMap.ofCovering hΦ).forget_pullStructured,
    fun T P => ⟨(PullMap.ofCovering hΦ).pullStructured_mk T P, fun _ => rfl, fun _ _ _ => rfl⟩⟩

end SBLocalization

end Polyfold
