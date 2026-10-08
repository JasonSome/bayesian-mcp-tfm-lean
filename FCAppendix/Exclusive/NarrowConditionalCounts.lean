import FCAppendix.Exclusive.NarrowFiniteClassification
import FCAppendix.Finite.ConditionalCountLaw
import FCAppendix.PayOnce.BinomialContinuity

namespace FCAppendix.Exclusive.Narrow
open MeasureTheory Filter Topology Set
open scoped BigOperators
open PayOnce.ManyProposers

noncomputable def binomialMixtureMass {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (n : ℕ) (P : Ω → ℝ) (j : ℕ) : ℝ :=
  ∫ ω, binomialMass n (P ω) j ∂ν

theorem binomialMixtureMass_error {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (n j : ℕ)
    (P : Ω → ℝ) (hP : Measurable P) (hb : ∀ ω, P ω ∈ Icc (0 : ℝ) 1)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    |binomialMixtureMass ν n P j - binomialMass n p j| ≤
      (n.choose j : ℝ) * ((j : ℝ) + (n - j : ℕ)) * (∫ ω, |P ω - p| ∂ν) := by
  let L : ℝ := (n.choose j : ℝ) * ((j : ℝ) + (n - j : ℕ))
  have hPm : Integrable P ν := Integrable.of_bound hP.aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb ω).1]
      exact (hb ω).2)
  have hm : Integrable (fun ω => binomialMass n (P ω) j) ν :=
    Integrable.of_bound ((continuous_binomialMass n j).measurable.comp hP).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (binomialMass_bounds n j (hb ω)).1]
        exact (binomialMass_bounds n j (hb ω)).2)
  have hi : Integrable (fun ω => |binomialMass n (P ω) j - binomialMass n p j|) ν :=
    (hm.sub (integrable_const _)).abs
  have he : binomialMixtureMass ν n P j - binomialMass n p j =
      ∫ ω, binomialMass n (P ω) j - binomialMass n p j ∂ν := by
    rw [integral_sub hm (integrable_const _)]
    simp [binomialMixtureMass]
  rw [he]
  calc
    _ ≤ ∫ ω, |binomialMass n (P ω) j - binomialMass n p j| ∂ν :=
      abs_integral_le_integral_abs
    _ ≤ ∫ ω, L * |P ω - p| ∂ν :=
      integral_mono_ae hi ((hPm.sub (integrable_const p)).abs.const_mul L)
        (Eventually.of_forall fun ω => binomialMass_abs_sub_le n j (hb ω) hp)
    _ = _ := by rw [integral_const_mul]

theorem binomialMixtureMass_tendsto
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (ν : (t : ℕ) → Measure (Ω t)) [∀ t, IsProbabilityMeasure (ν t)]
    (n : ℕ) (P : (t : ℕ) → Ω t → ℝ)
    (hP : ∀ t, Measurable (P t)) (hb : ∀ t ω, P t ω ∈ Icc (0 : ℝ) 1)
    (p e : ℕ → ℝ) (q : ℝ)
    (hp : ∀ t, p t ∈ Icc (0 : ℝ) 1)
    (herror : ∀ t, ∫ ω, |P t ω - p t| ∂ν t ≤ e t)
    (he : Tendsto e atTop (𝓝 0)) (hpq : Tendsto p atTop (𝓝 q)) (j : ℕ) :
    Tendsto (fun t => binomialMixtureMass (ν t) n (P t) j) atTop
      (𝓝 (binomialMass n q j)) := by
  let L : ℝ := (n.choose j : ℝ) * ((j : ℝ) + (n - j : ℕ))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hgap : ∀ t, |binomialMixtureMass (ν t) n (P t) j - binomialMass n (p t) j| ≤ L * e t := by
    intro t
    exact (binomialMixtureMass_error (ν t) n j (P t) (hP t) (hb t) (hp t)).trans
      (mul_le_mul_of_nonneg_left (herror t) hL)
  have hz : Tendsto (fun t => binomialMixtureMass (ν t) n (P t) j - binomialMass n (p t) j)
      atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    exact squeeze_zero (fun _ => abs_nonneg _) hgap (by simpa using he.const_mul L)
  have hq := (continuous_binomialMass n j).continuousAt.tendsto.comp hpq
  convert hz.add hq using 1 <;> simp

theorem binomial_mass_eq_polynomial (n : ℕ) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (j : Fin (n + 1)) :
    (IndependentCounts.binomial n p hp.1 hp.2).mass j = binomialMass n p j.val := by
  classical
  have he := binomial_prob_eq_binomialMass n p hp.1 hp.2 j.val
  rw [FiniteLaw.prob_eq_expect] at he
  have hf : (fun r : Fin (n + 1) => if r.val = j.val then (1 : ℝ) else 0) =
      (fun r : Fin (n + 1) => if r = j then (1 : ℝ) else 0) := by
    funext r
    simp only [Fin.val_inj]
  rw [hf, FiniteLaw.expect_singleton] at he
  exact he

theorem count_statistics_tendsto_binomial (n : ℕ) (law : ℕ → CountLaw n)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hmass : ∀ j : Fin (n + 1), Tendsto (fun t => (law t).mass j) atTop
      (𝓝 (binomialMass n p j.val))) (test : Fin (n + 1) → ℝ) :
    Tendsto (fun t => (law t).expect test) atTop
      (𝓝 ((IndependentCounts.binomial n p hp.1 hp.2).expect test)) := by
  unfold FiniteLaw.expect
  simp_rw [binomial_mass_eq_polynomial n hp]
  exact tendsto_finsetSum _ (fun j _ => (hmass j).mul_const (test j))

end FCAppendix.Exclusive.Narrow

namespace FCAppendix.Bayes
open MeasureTheory Filter Topology Set Game Exclusive
open scoped BigOperators ProbabilityTheory
open Exclusive.Narrow PayOnce.ManyProposers

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure SupportedActualBinomialKernel (Γ : FiniteGame m n c Seed)
    (i : Fin m) (E : Set ℝ) (P : ℝ → UserProfile m n → ℝ) : Prop where
  measurable : ∀ b, Measurable (P b)
  bounds : ∀ b d, P b d ∈ Icc (0 : ℝ) 1
  supported : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, v ∈ E → a.routeCount = n →
    ∀ j : Fin (n + 1), ((problem Γ i).outcome a).mass j =
      binomialMixtureMass (userProfileLaw Γ) n (P a.bid) j.val

theorem typeOutcome_mass_eq_binomialMixture_of_purity
    (Γ : FiniteGame m n c Seed) (i : Fin m) (E : Set ℝ) (hE : MeasurableSet E)
    (P : ℝ → UserProfile m n → ℝ) (hK : SupportedActualBinomialKernel Γ i E P)
    (beta : ℝ → ℝ)
    (hpure : ∀ᵐ v ∂Γ.F.restrict E, ∀ᵐ a ∂Γ.σ v, a.bid = beta v ∧ a.routeCount = n) :
    ∀ᵐ v ∂Γ.F.restrict E, ∀ j : Fin (n + 1),
      (typeOutcome Γ i v).mass j = binomialMixtureMass (userProfileLaw Γ) n (P (beta v)) j.val := by
  have hs := ae_restrict_of_ae (s := E) hK.supported
  filter_upwards [hs, hpure, ae_restrict_mem hE] with v hv hp hvE
  intro j
  change (∫ a, ((problem Γ i).outcome a).mass j ∂Γ.σ v) = _
  have he : ∀ᵐ a ∂Γ.σ v, ((problem Γ i).outcome a).mass j =
      binomialMixtureMass (userProfileLaw Γ) n (P (beta v)) j.val := by
    filter_upwards [hv, hp] with a ha hpa
    rw [ha hvE hpa.2 j, hpa.1]
  rw [integral_congr_ae he]
  simp

theorem ae_typeOutcome_binomial_limit_changing_identities
    {M C : ℕ → ℕ} {Seeds : ℕ → Type*} [∀ t, MeasurableSpace (Seeds t)]
    (Γ : (t : ℕ) → FiniteGame (M t) n (C t) (Seeds t))
    (ν : Measure ℝ) (T0 : ℕ)
    (P : (t : ℕ) → Fin (M t) → ℝ → UserProfile (M t) n → ℝ)
    (beta p : ℕ → ℝ → ℝ) (pInf : ℝ → ℝ) (err : ℕ → ℝ)
    (hP : ∀ t i b, Measurable (P t i b))
    (hPb : ∀ t i b d, P t i b d ∈ Icc (0 : ℝ) 1)
    (hfinite : ∀ t, T0 ≤ t → ∀ᵐ v ∂ν, ∀ i : Fin (M t), ∀ j : Fin (n + 1),
      (typeOutcome (Γ t) i v).mass j =
        binomialMixtureMass (userProfileLaw (Γ t)) n (P t i (beta t v)) j.val)
    (hpm : ∀ t, T0 ≤ t → ∀ᵐ v ∂ν, p t v ∈ Icc (0 : ℝ) 1)
    (herror : ∀ t, T0 ≤ t → ∀ᵐ v ∂ν, ∀ i : Fin (M t),
      ∫ d, |P t i (beta t v) d - p t v| ∂userProfileLaw (Γ t) ≤ err t)
    (he : Tendsto err atTop (𝓝 0))
    (hp : ∀ᵐ v ∂ν, Tendsto (fun t => p t v) atTop (𝓝 (pInf v))) :
    ∀ᵐ v ∂ν, pInf v ∈ Icc (0 : ℝ) 1 ∧
      ∀ I : (t : ℕ) → Fin (M (t + T0)), ∀ j : Fin (n + 1),
        Tendsto (fun t => (typeOutcome (Γ (t + T0)) (I t) v).mass j) atTop
          (𝓝 (binomialMass n (pInf v) j.val)) := by
  have hf : ∀ᵐ v ∂ν, ∀ t, ∀ i : Fin (M (t + T0)), ∀ j : Fin (n + 1),
      (typeOutcome (Γ (t + T0)) i v).mass j =
        binomialMixtureMass (userProfileLaw (Γ (t + T0))) n (P (t + T0) i (beta (t + T0) v)) j.val :=
    ae_all_iff.mpr fun t => hfinite (t + T0) (by omega)
  have hm : ∀ᵐ v ∂ν, ∀ t, p (t + T0) v ∈ Icc (0 : ℝ) 1 :=
    ae_all_iff.mpr fun t => hpm (t + T0) (by omega)
  have herr : ∀ᵐ v ∂ν, ∀ t, ∀ i : Fin (M (t + T0)),
      ∫ d, |P (t + T0) i (beta (t + T0) v) d - p (t + T0) v|
        ∂userProfileLaw (Γ (t + T0)) ≤ err (t + T0) :=
    ae_all_iff.mpr fun t => herror (t + T0) (by omega)
  filter_upwards [hf, hm, herr, hp] with v hvf hvm hve hvp
  have hvp' := hvp.comp (tendsto_add_atTop_nat T0)
  have hvinf : pInf v ∈ Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hvp' (Eventually.of_forall hvm)
  refine ⟨hvinf, ?_⟩
  intro I j
  have hh := binomialMixtureMass_tendsto
    (fun t => userProfileLaw (Γ (t + T0))) n
    (fun t => P (t + T0) (I t) (beta (t + T0) v))
    (fun t => hP _ _ _) (fun t => hPb _ _ _)
    (fun t => p (t + T0) v) (fun t => err (t + T0)) (pInf v)
    hvm (fun t => hve t (I t)) (he.comp (tendsto_add_atTop_nat T0)) hvp' j.val
  simpa only [← hvf] using hh

end FCAppendix.Bayes
