import Polyfold.Chapter17.LevelStructures
import Polyfold.Chapter17.SubpolyfoldStructure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17:
a family of polyfold structures (**Definition 17.1.8, 2021 p. 747**) on a translation GCT, used for
**Theorem 17.1.28** (2021 p. 766) and **Proposition 17.3.6** (2021 p. 786) in
`Examples/EveryUniformizer/Level.lean` and `EveryUniformizerSub.lean`.

# Two uniformizers and a gauge

`Z3 = ℤ/3` acts trivially on an M-polyfold `U`; `C = Z3 ⋉ U` (Definition 17.1.2).  For `D ⊆ U`
the functors `Ψ_b : Z3 ⋉ U → C` (`b : Bool`) are the identity on objects and
`(g, x) ↦ (g, x)` (`b = false`), resp. `(g, x) ↦ (g, x)` for `x ∈ D` and `(g⁻¹, x)` for `x ∉ D`
(`b = true`); both are local uniformizers at every point (`unif`), and they differ as soon as
`D ≠ U` (`unif_false_ne_true`).

For a function `c : U → Z3` (the gauge, not necessarily continuous) put `γ(Ψ_true) = c`,
`γ(Ψ_false) = 1`, and give `M(Ψ_b, Ψ_b')` the structure of `Z3 × U` transported along
`ρ(q, (k, q), q) = (k · γ(Ψ_b')(q)⁻¹ · γ(Ψ_b)(q), q)` (`gRho`).  Since `Z3` is commutative, `ρ`
turns `s, t, u, ι, m` into the structure maps of the ep-groupoid `Z3 ⋉ U`, so (a)–(c) of
Definition 17.1.8 hold (`gaugeConstruction`).  On `M(Ψ_false, Ψ_true)` the identities
`(q, (1, q), q)` have `ρ`-image `(c(q)⁻¹, q)` (`gRho_false_true`): the structures on
`M(Ψ_false, Ψ_false)` and `M(Ψ_false, Ψ_true)` agree over their common set only where `c` is
locally constant.

## Main declarations (namespace `Polyfold.GCT.PolyfoldConstruction.EveryUniformizer`)

* `twFunctor`, `unif`, `unif_false_ne_true`, `gaugeF`.
* `gRho`, `gTop`, `gM`, `gaugeConstruction` (Definition 17.1.8), `gaugeConstruction_hasUniformizers`.
* `gRho_false_true`, `continuous_gRho`, `exists_continuous_cast` (moving a transition set of a
  polyfold structure along an equality of uniformizers).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

universe u

open Set Function Topology

noncomputable section

namespace Polyfold.GCT.PolyfoldConstruction.EveryUniformizer

/-- `ℤ/3`. -/
abbrev Z3 : Type := Multiplicative (ZMod 3)

/-- A generator of `ℤ/3`. -/
abbrev gen : Z3 := Multiplicative.ofAdd 1

theorem gen_ne_one : gen ≠ 1 := by decide

theorem gen_inv_ne_one : gen⁻¹ ≠ 1 := by decide

theorem gen_inv_ne_gen : gen⁻¹ ≠ gen := by decide

variable {U : Type} [TopologicalSpace U] [T2Space U] [ParacompactSpace U]

/-- The trivial action of `ℤ/3`. -/
scoped instance (priority := low) trivAction : MulAction Z3 U where
  smul _ y := y
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem smul_eq (g : Z3) (x : U) : g • x = x := rfl

variable (P : MPolyfold U)

theorem hP : ∀ g : Z3, P.IsScSmoothMap P fun y : U => g • y := fun _ => MPolyfold.isScSmoothMap_id

/-- The GCT `ℤ/3 ⋉ U` (trivial action). -/
abbrev C : GCT.{0} := GCT.translation Z3 U (hP P)

/-! ### The functors `Ψ_b` -/

variable (D : Set U)

open scoped Classical in
/-- `g ↦ g⁻¹` off `D` (for `b = true`), the identity otherwise. -/
def tw (b : Bool) (x : U) (g : Z3) : Z3 := if b = true ∧ x ∉ D then g⁻¹ else g

theorem tw_mul (b : Bool) (x : U) (g h : Z3) : tw D b x (g * h) = tw D b x g * tw D b x h := by
  unfold tw; split_ifs <;> simp [mul_comm]

theorem tw_one (b : Bool) (x : U) : tw D b x 1 = 1 := by
  unfold tw; split_ifs <;> simp

theorem tw_tw (b : Bool) (x : U) (g : Z3) : tw D b x (tw D b x g) = g := by
  unfold tw; split_ifs <;> simp

theorem tw_of_mem (b : Bool) {x : U} (hx : x ∈ D) (g : Z3) : tw D b x g = g := by
  unfold tw; rw [if_neg (fun h => h.2 hx)]

theorem tw_false (x : U) (g : Z3) : tw D false x g = g := by
  unfold tw; rw [if_neg (fun h => Bool.false_ne_true h.1)]

theorem tw_true_of_not_mem {x : U} (hx : x ∉ D) (g : Z3) : tw D true x g = g⁻¹ := by
  unfold tw; rw [if_pos ⟨rfl, hx⟩]

/-- `Ψ_b : Z3 ⋉ U → C`, `x ↦ x`, `(g, x) ↦ (tw_b(x)(g), x)`. -/
def twFunctor (b : Bool) :
    GroupoidFunctor (GroupoidStr.translation Z3 U) (C P).toGroupoidStr where
  obj x := x
  mor p := (tw D b p.2 p.1, p.2)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp p q h := by
    have h' : p.2 = q.2 := h
    change (tw D b q.2 (p.1 * q.1), q.2) = (tw D b p.2 p.1 * tw D b q.2 q.1, q.2)
    rw [tw_mul, h']
  mor_unit x := by
    change (tw D b x 1, x) = (1, x)
    rw [tw_one]

theorem orbitMap_twFunctor (b : Bool) : (twFunctor P D b).orbitMap = id :=
  funext fun z => Quotient.inductionOn z fun _ => rfl

/-- **The local uniformizer `Ψ_b`** (Definition 17.1.3): `O = U`, `G = Z3`, the functor
`twFunctor`; full, faithful, injective on objects, `|Ψ_b| = id`. -/
abbrev unif (b : Bool) : (C P).LocalUniformizer where
  O := U
  P := P
  G := Z3
  smooth_smul := hP P
  functor := twFunctor P D b
  injective_obj := injective_id
  full := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => by
    have hs' : ψ.2 = x := hs
    have ht' : ψ.2 = x' := ht
    refine ⟨(tw D b x ψ.1, x), rfl, hs'.symm.trans ht', ?_⟩
    · change (tw D b x (tw D b x ψ.1), x) = ψ
      rw [tw_tw, ← hs']
  faithful := (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs _ he => by
    have hs' : φ.2 = φ'.2 := hs
    have h1 : tw D b φ.2 φ.1 = tw D b φ'.2 φ'.1 := congrArg Prod.fst he
    rw [hs'] at h1
    have h2 := congrArg (tw D b φ'.2) h1
    rw [tw_tw, tw_tw] at h2
    exact Prod.ext h2 hs'
  isOpenEmbedding_orbitMap := by
    rw [orbitMap_twFunctor]
    exact IsOpenEmbedding.id

theorem unif_mor (b : Bool) (g : Z3) (x : U) :
    (unif P D b).toUniformizer.mor (g, x) = (tw D b x g, x) := rfl

theorem unif_false_ne_true {x₁ : U} (hx₁ : x₁ ∉ D) : unif P D false ≠ unif P D true := by
  intro h
  have h1 : HEq (unif P D false).functor (unif P D true).functor := by rw [h]
  have h2 : twFunctor P D false = twFunctor P D true := eq_of_heq h1
  have h3 := congrArg Prod.fst (congrFun (congrArg GroupoidFunctor.mor h2) (gen, x₁))
  change tw D false x₁ gen = tw D true x₁ gen at h3
  rw [tw_false, tw_true_of_not_mem D hx₁] at h3
  exact gen_inv_ne_gen h3.symm

/-- `F(x) = {Ψ_false, Ψ_true}` (Definition 17.1.6). -/
def gaugeF : (C P).Obj → Set (C P).LocalUniformizer := fun _ => range (unif P D)

/-! ### The gauge and the transition structures -/

variable (c : U → Z3)

open scoped Classical in
/-- The gauge `γ(Ψ_true) = c`, `γ(L) = 1` otherwise. -/
def gauge (L : (C P).LocalUniformizer) : U → Z3 := if L = unif P D true then c else 1

/-- `ρ(q, (k, q), q) = (k · γ(L')(q)⁻¹ · γ(L)(q), q)`. -/
def gRho (L L' : (C P).LocalUniformizer) (a : L.Trans L') : Z3 × U :=
  ((a.mor : Z3 × U).1 * (gauge P D c L' (a.mor : Z3 × U).2)⁻¹ * gauge P D c L (a.mor : Z3 × U).2,
    (a.mor : Z3 × U).2)

/-- The topology of `M(L, L')`, induced by `ρ`. -/
@[instance_reducible]
def gTop (L L' : (C P).LocalUniformizer) : TopologicalSpace (L.Trans L') :=
  TopologicalSpace.induced (gRho P D c L L') inferInstance

theorem continuous_gRho (L L' : (C P).LocalUniformizer) :
    @Continuous _ _ (gTop P D c L L') _ (gRho P D c L L') :=
  @continuous_induced_dom _ _ _ _

theorem injective_gRho (L L' : (C P).LocalUniformizer) : Injective (gRho P D c L L') := by
  intro a a' h
  have h2 : (a.mor : Z3 × U).2 = (a'.mor : Z3 × U).2 := by
    have := congrArg Prod.snd h
    exact this
  have h1 := congrArg Prod.fst h
  simp only [gRho, h2, mul_left_inj] at h1
  have hm : a.mor = a'.mor := Prod.ext h1 h2
  have hs : L.obj a.src = L.obj a'.src :=
    a.src_mor.symm.trans ((congrArg (C P).toGroupoidStr.src hm).trans a'.src_mor)
  have ht : L'.obj a.tgt = L'.obj a'.tgt :=
    a.tgt_mor.symm.trans ((congrArg (C P).toGroupoidStr.tgt hm).trans a'.tgt_mor)
  exact GroupoidStr.TransitionSet.ext (L.injective_obj hs) hm (L'.injective_obj ht)

/-- The inverse of `ρ` on `M(Ψ_b, Ψ_b')`. -/
def gMap (b b' : Bool) (x : Z3 × U) : (unif P D b).Trans (unif P D b') :=
  ⟨x.2, (x.1 * (gauge P D c (unif P D b) x.2)⁻¹ * gauge P D c (unif P D b') x.2, x.2), x.2,
    rfl, rfl⟩

theorem gRho_gMap (b b' : Bool) (x : Z3 × U) : gRho P D c _ _ (gMap P D c b b' x) = x := by
  refine Prod.ext ?_ rfl
  change x.1 * (gauge P D c (unif P D b) x.2)⁻¹ * gauge P D c (unif P D b') x.2 *
    (gauge P D c (unif P D b') x.2)⁻¹ * gauge P D c (unif P D b) x.2 = x.1
  rw [mul_inv_cancel_right, inv_mul_cancel_right]

theorem bijective_gRho (b b' : Bool) : Bijective (gRho P D c (unif P D b) (unif P D b')) :=
  ⟨injective_gRho P D c _ _, fun x => ⟨gMap P D c b b' x, gRho_gMap P D c b b' x⟩⟩

theorem bijective_gRho_of_mem {L L' : (C P).LocalUniformizer} (hL : L ∈ range (unif P D))
    (hL' : L' ∈ range (unif P D)) : Bijective (gRho P D c L L') := by
  obtain ⟨b, rfl⟩ := hL
  obtain ⟨b', rfl⟩ := hL'
  exact bijective_gRho P D c b b'

/-- `ρ` as a homeomorphism `M(L, L') ≃ₜ Z3 × U`. -/
def gHomeo (L L' : (C P).LocalUniformizer) (h : Bijective (gRho P D c L L')) :
    @Homeomorph (L.Trans L') (Z3 × U) (gTop P D c L L') _ :=
  @Equiv.toHomeomorphOfIsInducing _ _ (gTop P D c L L') _ (Equiv.ofBijective _ h)
    (@IsInducing.mk _ _ (gTop P D c L L') _ _ rfl)

theorem gHomeo_apply (L L' : (C P).LocalUniformizer) (h : Bijective (gRho P D c L L'))
    (a : L.Trans L') : gHomeo P D c L L' h a = gRho P D c L L' a := rfl

theorem gT2 (L L' : (C P).LocalUniformizer) : @T2Space (L.Trans L') (gTop P D c L L') :=
  @T2Space.of_injective_continuous _ _ (gTop P D c L L') _ _ _ (injective_gRho P D c L L')
    (continuous_gRho P D c L L')

theorem gPara (L L' : (C P).LocalUniformizer) (h : Bijective (gRho P D c L L')) :
    @ParacompactSpace (L.Trans L') (gTop P D c L L') :=
  letI := gTop P D c L L'
  haveI := MPolyfold.paracompactSpace_prod (discretePolyfold Z3) P
  (gHomeo P D c L L' h).isClosedEmbedding.paracompactSpace

/-- The M-polyfold `M(L, L')`: `Z3 × U` transported along `ρ⁻¹`. -/
def gM (L L' : (C P).LocalUniformizer) (h : Bijective (gRho P D c L L')) :
    @MPolyfold (L.Trans L') (gTop P D c L L') (gT2 P D c L L') (gPara P D c L L' h) :=
  letI := gTop P D c L L'
  haveI := gT2 P D c L L'
  haveI := gPara P D c L L' h
  (EpGroupoid.Examples.actionMorPolyfold Z3 P).transport (gHomeo P D c L L' h).symm

section Axioms

/-- `M(Ψ_b, Ψ_b')` with the topology and the M-polyfold structure of `gM`. -/
@[nolint unusedArguments]
def GT (_c : U → Z3) (b b' : Bool) : Type := (unif P D b).Trans (unif P D b')

variable (b b' b'' : Bool)

instance : TopologicalSpace (GT P D c b b') := gTop P D c (unif P D b) (unif P D b')
instance : T2Space (GT P D c b b') := gT2 P D c (unif P D b) (unif P D b')
instance : ParacompactSpace (GT P D c b b') :=
  gPara P D c (unif P D b) (unif P D b') (bijective_gRho P D c b b')

/-- `ρ` on `M(Ψ_b, Ψ_b')`, as a homeomorphism. -/
def gHomeoB : GT P D c b b' ≃ₜ Z3 × U :=
  gHomeo P D c (unif P D b) (unif P D b') (bijective_gRho P D c b b')

/-- The M-polyfold `M(Ψ_b, Ψ_b')`. -/
def gMb : MPolyfold (GT P D c b b') :=
  (EpGroupoid.Examples.actionMorPolyfold Z3 P).transport (gHomeoB P D c b b').symm

/-- `ρ` on `GT`. -/
abbrev rho : GT P D c b b' → Z3 × U := gRho P D c (unif P D b) (unif P D b')

/-- `ρ⁻¹` on `GT`. -/
abbrev rhoInv : Z3 × U → GT P D c b b' := (gHomeoB P D c b b').symm

theorem rho_rhoInv (x : Z3 × U) : rho P D c b b' (rhoInv P D c b b' x) = x :=
  (gHomeoB P D c b b').apply_symm_apply x

theorem rhoInv_eq {a : GT P D c b b'} {x : Z3 × U} (h : rho P D c b b' a = x) :
    rhoInv P D c b b' x = a :=
  (gHomeoB P D c b b').symm_apply_eq.2 h.symm

theorem gMb_isScDiffeoOn :
    (EpGroupoid.Examples.actionMorPolyfold Z3 P).IsScDiffeoOn (gMb P D c b b')
      (rhoInv P D c b b') (rho P D c b b') univ univ :=
  MPolyfold.isScDiffeoOn_transport (EpGroupoid.Examples.actionMorPolyfold Z3 P)
    (gHomeoB P D c b b').symm

theorem gMb_isLocalScDiffeo_rho :
    (gMb P D c b b').IsLocalScDiffeo (EpGroupoid.Examples.actionMorPolyfold Z3 P)
      (rho P D c b b') := fun _ =>
  ⟨univ, univ, rhoInv P D c b b', mem_univ _, (gMb_isScDiffeoOn P D c b b').symm⟩

theorem rho_snd (a : GT P D c b b') : (rho P D c b b' a).2 = a.src := a.src_mor

theorem rho_snd' (a : GT P D c b b') : (rho P D c b b' a).2 = a.tgt := a.tgt_mor

/-- **(a)**: `s` is a local sc-diffeomorphism. -/
theorem gMb_isLocalScDiffeo_src :
    (gMb P D c b b').IsLocalScDiffeo P fun a : GT P D c b b' => a.src := by
  have h : (fun a : GT P D c b b' => a.src) =
      (GroupoidStr.translation Z3 U).src ∘ rho P D c b b' :=
    funext fun a => (rho_snd P D c b b' a).symm
  rw [h]
  exact EpGroupoid.Examples.action_isLocalScDiffeo_src.comp (gMb_isLocalScDiffeo_rho P D c b b')

/-- **(a)**: `t` is a local sc-diffeomorphism. -/
theorem gMb_isLocalScDiffeo_tgt :
    (gMb P D c b b').IsLocalScDiffeo P fun a : GT P D c b b' => a.tgt := by
  have h : (fun a : GT P D c b b' => a.tgt) =
      (GroupoidStr.translation Z3 U).tgt ∘ rho P D c b b' :=
    funext fun a => (rho_snd' P D c b b' a).symm
  rw [h]
  exact (EpGroupoid.Examples.action_isLocalScDiffeo_tgt (hP P)).comp
    (gMb_isLocalScDiffeo_rho P D c b b')

/-- **(b)**: the unit map is sc-smooth. -/
theorem gMb_isScSmoothMap_unit :
    P.IsScSmoothMap (gMb P D c b b)
      fun q => (GroupoidStr.TransitionSet.unit q : GT P D c b b) := by
  refine ((gMb_isScDiffeoOn P D c b b).isScSmoothOn.comp
    (EpGroupoid.Examples.actionEpGroupoid (hP P)).isScSmoothMap_unit (mapsTo_univ _ _)).congr
    fun q _ => rhoInv_eq P D c b b ?_
  refine Prod.ext ?_ rfl
  change 1 * _ * _ = (1 : Z3)
  rw [one_mul, inv_mul_cancel]

theorem rho_inv (a : GT P D c b b') :
    rho P D c b' b (GroupoidStr.TransitionSet.inv a) =
      (EpGroupoid.Examples.actionEpGroupoid (hP P)).inv (rho P D c b b' a) := by
  refine Prod.ext ?_ rfl
  change (a.mor : Z3 × U).1⁻¹ * (gauge P D c (unif P D b) (a.mor : Z3 × U).2)⁻¹ *
      gauge P D c (unif P D b') (a.mor : Z3 × U).2 =
    ((a.mor : Z3 × U).1 * (gauge P D c (unif P D b') (a.mor : Z3 × U).2)⁻¹ *
      gauge P D c (unif P D b) (a.mor : Z3 × U).2)⁻¹
  generalize (a.mor : Z3 × U).1 = k
  generalize gauge P D c (unif P D b) (a.mor : Z3 × U).2 = x
  generalize gauge P D c (unif P D b') (a.mor : Z3 × U).2 = y
  revert k x y
  decide

/-- **(b)**: the inversion is sc-smooth. -/
theorem gMb_isScSmoothMap_inv :
    (gMb P D c b b').IsScSmoothMap (gMb P D c b' b)
      fun a : GT P D c b b' => (GroupoidStr.TransitionSet.inv a : GT P D c b' b) := by
  have h1 := (EpGroupoid.Examples.actionEpGroupoid (hP P)).isScSmoothMap_inv.comp
    (gMb_isScDiffeoOn P D c b b').isScSmoothOn_inv
  exact ((gMb_isScDiffeoOn P D c b' b).isScSmoothOn.comp h1 (mapsTo_univ _ _)).congr
    fun a _ => rhoInv_eq P D c b' b (rho_inv P D c b b' a)

theorem rho_comp (a : GT P D c b' b'') (a' : GT P D c b b')
    (h : (GroupoidStr.translation Z3 U).src a.mor = (GroupoidStr.translation Z3 U).tgt a'.mor) :
    rho P D c b b'' (GroupoidStr.TransitionSet.comp a a' h : GT P D c b b'') =
      (GroupoidStr.translation Z3 U).comp (rho P D c b' b'' a) (rho P D c b b' a') := by
  have hq : (a.mor : Z3 × U).2 = (a'.mor : Z3 × U).2 := h
  refine Prod.ext ?_ rfl
  change (a.mor : Z3 × U).1 * (a'.mor : Z3 × U).1 *
      (gauge P D c (unif P D b'') (a'.mor : Z3 × U).2)⁻¹ *
      gauge P D c (unif P D b) (a'.mor : Z3 × U).2 =
    (a.mor : Z3 × U).1 * (gauge P D c (unif P D b'') (a.mor : Z3 × U).2)⁻¹ *
      gauge P D c (unif P D b') (a.mor : Z3 × U).2 *
      ((a'.mor : Z3 × U).1 * (gauge P D c (unif P D b') (a'.mor : Z3 × U).2)⁻¹ *
        gauge P D c (unif P D b) (a'.mor : Z3 × U).2)
  rw [hq]
  generalize (a.mor : Z3 × U).1 = k
  generalize (a'.mor : Z3 × U).1 = k'
  generalize gauge P D c (unif P D b) (a'.mor : Z3 × U).2 = x
  generalize gauge P D c (unif P D b') (a'.mor : Z3 × U).2 = y
  generalize gauge P D c (unif P D b'') (a'.mor : Z3 × U).2 = z
  revert k k' x y z
  decide

/-- **(c)**: the multiplication is sc-smooth. -/
theorem gMb_isScSmoothMap_mul :
    MPolyfold.IsScSmoothOnFibredProduct (gMb P D c b' b'') (gMb P D c b b') (gMb P D c b b'')
      (gMb_isLocalScDiffeo_src P D c b' b'') (gMb_isLocalScDiffeo_tgt P D c b b').isScSmoothMap
      fun p => (GroupoidStr.TransitionSet.mul p : GT P D c b b'') := by
  set X := EpGroupoid.Examples.actionEpGroupoid (hP P)
  set PM := EpGroupoid.Examples.actionMorPolyfold Z3 P
  set M₁ := gMb P D c b' b''
  set M₂ := gMb P D c b b'
  have := MPolyfold.paracompactSpace_prod M₁ M₂
  have := (M₁.prod M₂).paracompactSpace_subtype (MPolyfold.fibredProduct
    (fun a : GT P D c b' b'' => (a.src : U)) (fun a : GT P D c b b' => (a.tgt : U)))
  have := MPolyfold.paracompactSpace_prod PM PM
  have := (PM.prod PM).paracompactSpace_subtype (MPolyfold.fibredProduct X.src X.tgt)
  have hA := MPolyfold.isSubMPolyfold_fibredProduct (gMb_isLocalScDiffeo_src P D c b' b'')
    (gMb_isLocalScDiffeo_tgt P D c b b').isScSmoothMap
  have hB := MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src
    X.isLocalScDiffeo_tgt.isScSmoothMap
  have hc : (MPolyfold.subPolyfold hB).IsScSmoothMap PM fun p => X.comp p.1.1 p.1.2 :=
    X.isScSmoothComp
  let Φ : MPolyfold.fibredProduct (fun a : GT P D c b' b'' => (a.src : U))
      (fun a : GT P D c b b' => (a.tgt : U)) → MPolyfold.fibredProduct X.src X.tgt :=
    fun p => ⟨(rho P D c b' b'' p.1.1, rho P D c b b' p.1.2), by
      change (rho P D c b' b'' p.1.1).2 = (rho P D c b b' p.1.2).2
      rw [rho_snd, rho_snd']
      exact p.2⟩
  have hval := MPolyfold.subPolyfold_inclusion_isScSmooth hA
  have hΦ : (MPolyfold.subPolyfold hA).IsScSmoothMap (MPolyfold.subPolyfold hB) Φ := by
    refine MPolyfold.isScSmoothOn_subPolyfold_of_val hB ?_
    refine MPolyfold.IsScSmoothOn.prodMk ?_ ?_
    · exact (gMb_isScDiffeoOn P D c b' b'').isScSmoothOn_inv.comp
        ((MPolyfold.isScSmoothMap_fst M₁ M₂).comp hval) (mapsTo_univ _ _)
    · exact (gMb_isScDiffeoOn P D c b b').isScSmoothOn_inv.comp
        ((MPolyfold.isScSmoothMap_snd M₁ M₂).comp hval) (mapsTo_univ _ _)
  have h2 := (gMb_isScDiffeoOn P D c b b'').isScSmoothOn.comp (hc.comp hΦ) (mapsTo_univ _ _)
  change (MPolyfold.subPolyfold hA).IsScSmoothMap (gMb P D c b b'') _
  refine h2.congr fun p _ => rhoInv_eq P D c b b'' ?_
  exact rho_comp P D c b b' b'' p.1.1 p.1.2 _

end Axioms

/-! ### The polyfold structure -/

/-- **A polyfold structure on `ℤ/3 ⋉ U`** (Definition 17.1.8, 2021 p. 747):
`F(x) = {Ψ_false, Ψ_true}` and `M(Ψ_b, Ψ_b') = Z3 × U` transported along `ρ⁻¹`. -/
def gaugeConstruction : (C P).PolyfoldConstruction where
  F := gaugeF P D
  isAt x L hL := by
    obtain ⟨b, rfl⟩ := hL
    exact ⟨x, rfl⟩
  topM Ψ Ψ' := gTop P D c Ψ.1 Ψ'.1
  t2M Ψ Ψ' := gT2 P D c Ψ.1 Ψ'.1
  paraM Ψ Ψ' := gPara P D c Ψ.1 Ψ'.1 (bijective_gRho_of_mem P D c Ψ.2.choose_spec Ψ'.2.choose_spec)
  M Ψ Ψ' := gM P D c Ψ.1 Ψ'.1 (bijective_gRho_of_mem P D c Ψ.2.choose_spec Ψ'.2.choose_spec)
  isLocalScDiffeo_src := by
    rintro ⟨L, x, b, rfl⟩ ⟨L', x', b', rfl⟩
    exact gMb_isLocalScDiffeo_src P D c b b'
  isLocalScDiffeo_tgt := by
    rintro ⟨L, x, b, rfl⟩ ⟨L', x', b', rfl⟩
    exact gMb_isLocalScDiffeo_tgt P D c b b'
  isScSmoothMap_unit := by
    rintro ⟨L, x, b, rfl⟩
    exact gMb_isScSmoothMap_unit P D c b
  isScSmoothMap_inv := by
    rintro ⟨L, x, b, rfl⟩ ⟨L', x', b', rfl⟩
    exact gMb_isScSmoothMap_inv P D c b b'
  isScSmoothMap_mul := by
    rintro ⟨L, x, b, rfl⟩ ⟨L', x', b', rfl⟩ ⟨L'', x'', b'', rfl⟩
    exact gMb_isScSmoothMap_mul P D c b b' b''

/-- Every `F(x)` is non-empty. -/
theorem gaugeConstruction_hasUniformizers : (gaugeConstruction P D c).HasUniformizers :=
  fun _ => ⟨_, false, rfl⟩

/-- `Ψ_b` as a uniformizer of the construction (at the point `x`). -/
abbrev unifAt (b : Bool) (x : U) : (gaugeConstruction P D c).Unif := ⟨unif P D b, x, b, rfl⟩

theorem gauge_true : gauge P D c (unif P D true) = c := by
  unfold gauge; rw [if_pos rfl]

theorem gauge_false {x₁ : U} (hx₁ : x₁ ∉ D) : gauge P D c (unif P D false) = 1 := by
  unfold gauge; rw [if_neg (unif_false_ne_true P D hx₁)]

/-- On `M(Ψ_false, Ψ_true)`, `ρ(q, (k, q), q) = (k · c(q)⁻¹, q)`. -/
theorem gRho_false_true {x₁ : U} (hx₁ : x₁ ∉ D) (a : (unif P D false).Trans (unif P D true)) :
    gRho P D c _ _ a = ((a.mor : Z3 × U).1 * (c (a.mor : Z3 × U).2)⁻¹, (a.mor : Z3 × U).2) := by
  unfold gRho
  rw [gauge_true, gauge_false P D c hx₁]
  simp

end Polyfold.GCT.PolyfoldConstruction.EveryUniformizer

namespace Polyfold.GCT.PolyfoldConstruction

/-- Moving a transition set of a polyfold structure along an equality of uniformizers: the map
`M(L, L₁) → M(L, L₂)` for `L₁ = L₂` is continuous and keeps the morphisms. -/
theorem exists_continuous_cast {C' : GCT.{u}} (S' : C'.PolyfoldConstruction)
    (L L₁ L₂ : C'.LocalUniformizer) (h : ∃ α, L ∈ S'.F α) (h₁ : ∃ α, L₁ ∈ S'.F α)
    (h₂ : ∃ α, L₂ ∈ S'.F α) (e : L₁ = L₂) :
    ∃ f : L.Trans L₁ → L.Trans L₂,
      @Continuous _ _ (S'.topM ⟨L, h⟩ ⟨L₁, h₁⟩) (S'.topM ⟨L, h⟩ ⟨L₂, h₂⟩) f ∧
        ∀ a, (f a).mor = a.mor := by
  subst e
  exact ⟨id, @continuous_id _ (S'.topM ⟨L, h⟩ ⟨L₁, h₁⟩), fun _ => rfl⟩

end Polyfold.GCT.PolyfoldConstruction
