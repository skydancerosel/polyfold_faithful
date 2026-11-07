import Polyfold
/-! Blind formalization of V6_38 (the text's §6.5, (96) and Lemma 6.31, p. 223).

Text: the sequence (96),
`0 → ker((f − s(·,t))'(φ(t))) → ker F_t'(φ(t), 0) → ℝᵏ → Y_{φ(t)}/R((f − s(·,t))'(φ(t))) → 0`,
with `j` the inclusion, `p` the projection onto `ℝᵏ` and `c(λ) = Σ λᵢ sᵢ(t, φ(t)) + R(·)`, is
exact; `c` is onto by property (P).

Choices:
- Setting: `X Y : Type` (universe 0), a strong bundle `Bd : StrongBundle PX P` (as in
  `RoundTrip/Blind/V5_31.lean`), `f` an sc-Fredholm section.  The point is `x = φ(t)`, the
  section `S` is the slice `s(·, t)` (with `s(φ(t), t) = f(φ(t))`, i.e. `(f − S)(x) = 0`) and
  `σᵢ = sᵢ(·, t)`.  The claim is pointwise linear algebra at `x`, so B quantifies over every point
  `x`, every section `S` with `(f − S)(x) = 0` and all sections `σ₁, …, σ_k` (the text's slices
  of the sc⁺-sections of Proposition 6.28 and Lemma 6.29 are such sections; their sc⁺-property is
  not used by the claim).  `f − S` is the project's `sectionDiff P f S`.
- Everything is read in a chart point `p : ChartPoint Bd x` (chart of the atlas around `x`,
  level-`1` lift `z` of `φ(x)`), over which B quantifies: `T_xX = T_zO = p.T`,
  `Y_x = K_z = p.K ⊆ F`.  `T = (f − S)'(x)` is the project's chart linearization
  `linAt U R (principal (f − S)) z : T_zO → F` (`D((f − S)^ ∘ r)(z)` on `T_zO`); I keep it
  `F`-valued and form the cokernel as `K_z / (R(T) ∩ K_z)` (`comap` of `R(T)` to `K_z`), which is
  `Y_x / R(T)` since `R(T) ⊆ K_z`.  `λ ↦ Σ λᵢ σᵢ(x)` is the project's `ChartPoint.stabPhi`
  (`K_z`-valued; checked with `#print`: `Σ λᵢ σ̂ᵢ(φ(x))`).
- The middle term `ker F_t'(φ(t), 0)`: `F_t(y, λ) = (f − S)(y) + Σ λᵢ σᵢ(y)` has at `(x, 0)` (in
  the product chart) the linearization `(v, λ) ↦ T v + Σ λᵢ σᵢ(x)` on `T_zO × ℝᵏ` (this is the
  item V6_37); B takes the kernel of this operator `T ⊕ φ` (`ContinuousLinearMap.coprod`) as the
  middle term.  `j(v) = (v, 0)`, `p(v, λ) = λ`, `c(λ) = [Σ λᵢ σᵢ(x)]`.
- "exact": `j` injective, `Function.Exact j p`, `Function.Exact p c`, and `c` onto.  The text
  derives the surjectivity of `c` from (P), so that conjunct has (P) as hypothesis; the other
  three are stated without hypothesis (they hold for any `T`, `φ`).
- (P) at `t`: `F_t` is at `(x, 0)` in general position (Definition 5.17) as a section of the
  pull-back `π*P → ℝᵏ × X` (`π = Prod.snd`, the factors in the project's order `ℝᵏ × X`):
  `(Bd.pullback hπ).IsGeneralPositionGerm F_t (0, x)` with `F_t` the project's `paramSection`
  (`F(λ, y) = g(y) + Σ λᵢ σᵢ(y)`, checked with `#print`).  The sc-smoothness `hπ` of `π` and the
  section property of `f − S` (which `paramSection` needs) are quantified over (they are true);
  the paracompactness of `ℝⁿ × X` and of `π*Y` are instance hypotheses, as in the project's own
  definitions (true for M-polyfolds, which are metrizable).
- Nothing looks false to me.
-/
namespace RoundTrip.V6_38
open Polyfold

section
variable {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup N]
  [NormedSpace ℝ N] {k : ℕ}

/-- `j : ker T → ker(T ⊕ φ)`, `v ↦ (v, 0)`. -/
def jMap (T : M →L[ℝ] N) (φ : (Fin k → ℝ) →L[ℝ] N) :
    LinearMap.ker (T : M →ₗ[ℝ] N) →ₗ[ℝ] LinearMap.ker (T.coprod φ : M × (Fin k → ℝ) →ₗ[ℝ] N) :=
  LinearMap.restrict (LinearMap.inl ℝ M (Fin k → ℝ)) (fun v hv => by
    simp only [LinearMap.mem_ker] at hv ⊢
    simp [hv])

/-- `p : ker(T ⊕ φ) → ℝᵏ`, `(v, λ) ↦ λ`. -/
def pMap (T : M →L[ℝ] N) (φ : (Fin k → ℝ) →L[ℝ] N) :
    LinearMap.ker (T.coprod φ : M × (Fin k → ℝ) →ₗ[ℝ] N) →ₗ[ℝ] (Fin k → ℝ) :=
  (LinearMap.snd ℝ M (Fin k → ℝ)).comp
    (LinearMap.ker (T.coprod φ : M × (Fin k → ℝ) →ₗ[ℝ] N)).subtype

end

/-- Lemma 6.31: the sequence (96) is exact; `c` is onto by property (P). -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace ↥(pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (Bd : StrongBundle PX P) (f : X → Y), Bd.IsScFredholmSection f →
    ∀ (x : X) (p : ChartPoint Bd x) (S : X → Y), IsZeroAt P (sectionDiff P f S) x →
    ∀ {k : ℕ} (σ : Fin k → X → Y) (hσ : ∀ i, IsSection P (σ i)),
      -- `T = (f − S)'(x)`, `φ(λ) = Σ λᵢ σᵢ(x)`, and the cokernel map `c`
      let T : ↥p.T →L[ℝ] p.c.F.lvl 0 := linAt p.c.U p.c.R (p.c.principal (sectionDiff P f S)) p.z
      let φ : (Fin k → ℝ) →L[ℝ] p.c.F.lvl 0 := p.K.subtypeL ∘L p.stabPhi σ hσ
      let RT : Submodule ℝ ↥p.K :=
        (LinearMap.range (T : ↥p.T →ₗ[ℝ] p.c.F.lvl 0)).comap p.K.subtype
      let c : (Fin k → ℝ) →ₗ[ℝ] ↥p.K ⧸ RT :=
        RT.mkQ ∘ₗ (p.stabPhi σ hσ : (Fin k → ℝ) →ₗ[ℝ] ↥p.K)
      Function.Injective (jMap T φ) ∧ Function.Exact (jMap T φ) (pMap T φ) ∧
      Function.Exact (pMap T φ) c ∧
      -- `c` is onto by (P): `F_t` in general position at `(0, x)`
      ∀ (hπ : ((rnPolyfold k).prod PX).IsScSmoothMap PX Prod.snd)
        (hg : IsSection P (sectionDiff P f S)),
        (Bd.pullback hπ).IsGeneralPositionGerm (paramSection (sectionDiff P f S) hg σ hσ) (0, x) →
        Function.Surjective c

end RoundTrip.V6_38
