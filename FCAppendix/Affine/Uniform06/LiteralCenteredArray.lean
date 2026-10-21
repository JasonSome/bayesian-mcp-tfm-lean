import FCAppendix.Affine.Uniform06.MixedWeakLimits
import FCAppendix.Affine.Uniform06.CenteredSourceGap
import FCAppendix.Affine.Uniform06.TiltStability

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralCenteredArray

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform07 FCAppendix.ExponentialTilt
open MixedIntervalLLT MixedWeakLimits MixedCharacteristicGap CenteredSourceGap

abbrev Pair := ℝ × ℝ

def integerSign (p : Pair) : ℤ := if p.2=1 then 1 else if p.2 = -1 then -1 else 0

theorem measurable_integerSign : Measurable integerSign := by
  unfold integerSign
  exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
    measurable_const (Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      measurable_const measurable_const)

theorem integerSign_cast {p : Pair} (hp : p.2 = -1 ∨ p.2=0 ∨ p.2=1) :
    (integerSign p:ℝ)=p.2 := by
  rcases hp with hp | hp | hp <;> norm_num [integerSign,hp]

theorem tilted_support (i : Row) (ν : ProbabilityMeasure ℝ)
    (hν : ∀ᵐ x ∂(ν:Measure ℝ), x ∈ Icc (0:ℝ) 1) (u : ℝ) :
    ∀ᵐ p ∂MixedLaw.tiltedLaw i (ν:Measure ℝ) u,
      p.1 ∈ Icc (0:ℝ) 1 ∧ (integerSign p:ℝ)=p.2 ∧ |p.2| ≤ 1 := by
  have hs := (tilted_absolutelyContinuous (MixedLaw.law i (ν:Measure ℝ))
    (fun p : Pair => u*p.1)).ae_le (MixedLaw.law_support i _ hν)
  filter_upwards [hs] with p hp
  refine ⟨hp.1,integerSign_cast hp.2,?_⟩
  rcases hp.2 with h | h | h <;> simp [h]

def mean (i : Row) (ν : ProbabilityMeasure ℝ)
    (u : ℝ) : ℝ := ∫ p, p.1 ∂MixedLaw.tiltedLaw i (ν:Measure ℝ) u

theorem mean_unit (i : Row) (ν : ProbabilityMeasure ℝ)
    (hν : ∀ᵐ x ∂(ν:Measure ℝ), x ∈ Icc (0:ℝ) 1) (u : ℝ) :
    mean i ν u ∈ Icc (0:ℝ) 1 := by
  letI := MixedLaw.tiltedLaw_probability i (ν:Measure ℝ) hν u
  exact TiltStability.mean_bounds (MixedLaw.tiltedLaw i (ν:Measure ℝ) u)
    measurable_fst ((tilted_support i ν hν u).mono fun _ hp => hp.1)

theorem centered_mean_zero (i : Row) (ν : ProbabilityMeasure ℝ)
    (hν : ∀ᵐ x ∂(ν:Measure ℝ), x ∈ Icc (0:ℝ) 1) (u : ℝ) :
    (∫ p, p.1-mean i ν u ∂MixedLaw.tiltedLaw i (ν:Measure ℝ) u)=0 := by
  letI := MixedLaw.tiltedLaw_probability i (ν:Measure ℝ) hν u
  have hi : Integrable Prod.fst (MixedLaw.tiltedLaw i (ν:Measure ℝ) u) :=
    Integrable.of_mem_Icc 0 1 measurable_fst.aemeasurable
      ((tilted_support i ν hν u).mono fun _ hp => hp.1)
  rw [integral_sub hi (integrable_const _),integral_const]
  simp [mean]

theorem centered_cross_zero (i : Row) (ν : ProbabilityMeasure ℝ)
    (hν : ∀ᵐ x ∂(ν:Measure ℝ), x ∈ Icc (0:ℝ) 1) (u : ℝ) :
    (∫ p, (p.1-mean i ν u)*(integerSign p:ℝ)
      ∂MixedLaw.tiltedLaw i (ν:Measure ℝ) u)=0 := by
  letI := MixedLaw.tiltedLaw_probability i (ν:Measure ℝ) hν u
  have hs := tilted_support i ν hν u
  have hY : Integrable Prod.snd (MixedLaw.tiltedLaw i (ν:Measure ℝ) u) := by
    apply Integrable.of_bound measurable_snd.aestronglyMeasurable 1
    exact hs.mono fun _ hp => by simpa only [Real.norm_eq_abs] using hp.2.2
  have hXY : Integrable (fun p : Pair => p.1*p.2)
      (MixedLaw.tiltedLaw i (ν:Measure ℝ) u) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [hs] with p hp
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hp.1.1]
    exact mul_le_one₀ hp.1.2 (abs_nonneg _) hp.2.2
  calc
    _ = ∫ p, p.1*p.2-mean i ν u*p.2 ∂MixedLaw.tiltedLaw i (ν:Measure ℝ) u := by
      apply integral_congr_ae
      filter_upwards [hs] with p hp
      rw [hp.2.1]
      ring
    _ = 0 := by
      rw [integral_sub hXY (hY.const_mul _),integral_const_mul,
        MixedLaw.tilted_demand_sign_moment i _ hν,
        MixedLaw.tilted_sign_mean i _ hν]
      ring

theorem centered_square_eq_variance (i : Row) (ν : ProbabilityMeasure ℝ)
    (u : ℝ) :
    (∫ p, (p.1-mean i ν u)^2 ∂MixedLaw.tiltedLaw i (ν:Measure ℝ) u)=
      variance Prod.fst (MixedLaw.tiltedLaw i (ν:Measure ℝ) u) := by
  rw [variance_eq_integral measurable_fst.aemeasurable]
  rfl

theorem sign_square_eq_variance (i : Row) (ν : ProbabilityMeasure ℝ)
    (hν : ∀ᵐ x ∂(ν:Measure ℝ), x ∈ Icc (0:ℝ) 1) (u : ℝ) :
    (∫ p, (integerSign p:ℝ)^2 ∂MixedLaw.tiltedLaw i (ν:Measure ℝ) u)=
      variance Prod.snd (MixedLaw.tiltedLaw i (ν:Measure ℝ) u) := by
  rw [variance_eq_integral measurable_snd.aemeasurable,
    MixedLaw.tilted_sign_mean i _ hν]
  simp only [sub_zero]
  exact integral_congr_ae ((tilted_support i ν hν u).mono fun _ hp => congrArg (fun x : ℝ => x^2) hp.2.1)

theorem source_variance_positive (i : Row) (ν : ProbabilityMeasure ℝ)
    (hν : ∀ᵐ x ∂(ν:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    {a b : ℝ} (hab : a < b) (hcomponent : volume.restrict (Ioo a b) ≪ (ν:Measure ℝ))
    (u : ℝ) :
    0 < variance Prod.fst (MixedLaw.tiltedLaw i (ν:Measure ℝ) u) ∧
      0 < variance Prod.snd (MixedLaw.tiltedLaw i (ν:Measure ℝ) u) := by
  letI := MixedLaw.tiltedLaw_probability i (ν:Measure ℝ) hν u
  have ht := integrable_exp_mul_of_bounded (MixedLaw.law i (ν:Measure ℝ))
    measurable_fst.aemeasurable (MixedLaw.demand_bounds i _ hν) u
  have hback : MixedLaw.law i (ν:Measure ℝ) ≪ MixedLaw.tiltedLaw i (ν:Measure ℝ) u :=
    absolutelyContinuous_tilted ht
  have hLp := memLp_of_bounded ((tilted_support i ν hν u).mono fun _ hp => hp.1)
    measurable_fst.aestronglyMeasurable 2
  have hne : variance Prod.fst (MixedLaw.tiltedLaw i (ν:Measure ℝ) u) ≠ 0 := by
    intro hz
    have hc := ae_eq_integral_of_variance_eq_zero hLp hz
    have hphase : ∀ᵐ p ∂MixedLaw.law i (ν:Measure ℝ),
        jointPhase ((1:ℝ),0) p=CharacteristicExpansion.phase (mean i ν u) := by
      filter_upwards [hback.ae_le hc] with p hp
      simpa [jointPhase,mean] using congrArg CharacteristicExpansion.phase hp
    have hh := source_phase_constant_forces_origin i (ν:Measure ℝ) hab hcomponent
      (show (0:ℝ) ∈ Icc (-Real.pi) Real.pi by constructor <;> linarith [Real.pi_pos]) hphase
    have hf := congrArg Prod.fst hh
    norm_num at hf
  refine ⟨lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hne),?_⟩
  rw [MixedLaw.tilted_sign_variance i _ hν]
  exact MixedLaw.tiltedUpperMass_pos i _ u

theorem variance_limits (i : Row)
    (ν : ℕ → ProbabilityMeasure ℝ) (ν0 : ProbabilityMeasure ℝ)
    (hν : ∀ n, ∀ᵐ x ∂(ν n:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    (hν0 : ∀ᵐ x ∂(ν0:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    (hweak : Tendsto ν atTop (𝓝 ν0))
    (u : ℕ → ℝ) {u0 : ℝ} (hu : Tendsto u atTop (𝓝 u0)) :
    Tendsto (fun n => variance Prod.fst (MixedLaw.tiltedLaw i (ν n:Measure ℝ) (u n))) atTop
      (𝓝 (variance Prod.fst (MixedLaw.tiltedLaw i (ν0:Measure ℝ) u0))) ∧
    Tendsto (fun n => variance Prod.snd (MixedLaw.tiltedLaw i (ν n:Measure ℝ) (u n))) atTop
      (𝓝 (variance Prod.snd (MixedLaw.tiltedLaw i (ν0:Measure ℝ) u0))) := by
  letI (n : ℕ) := MixedLaw.tiltedLaw_probability i (ν n:Measure ℝ) (hν n) (u n)
  letI := MixedLaw.tiltedLaw_probability i (ν0:Measure ℝ) hν0 u0
  have hLp (ν : ProbabilityMeasure ℝ) (hν : ∀ᵐ x ∂(ν:Measure ℝ), x ∈ Icc (0:ℝ) 1) (u : ℝ) :
      MemLp Prod.fst 2 (MixedLaw.tiltedLaw i (ν:Measure ℝ) u) := by
    letI := MixedLaw.tiltedLaw_probability i (ν:Measure ℝ) hν u
    exact memLp_of_bounded ((tilted_support i ν hν u).mono fun _ hp => hp.1)
      measurable_fst.aestronglyMeasurable 2
  have hX := tilted_integral_tendsto i ν ν0 hν hν0 hweak u hu Prod.fst continuous_fst
  have hX2 := tilted_integral_tendsto i ν ν0 hν hν0 hweak u hu (fun p => p.1^2) (by fun_prop)
  have hY2 := tilted_integral_tendsto i ν ν0 hν hν0 hweak u hu (fun p => p.2^2) (by fun_prop)
  constructor
  · simp_rw [variance_eq_sub (hLp _ (hν _) _),variance_eq_sub (hLp _ hν0 _)]
    exact hX2.sub (hX.pow 2)
  · simp_rw [variance_eq_integral measurable_snd.aemeasurable,
      MixedLaw.tilted_sign_mean i _ (hν _),MixedLaw.tilted_sign_mean i _ hν0,sub_zero]
    exact hY2

theorem shift_tendsto (n0 : ℕ) : Tendsto (fun n : ℕ => n+n0) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop k] with n hn
  omega

theorem exists_actual_centered_array (i : Row)
    (ν : ℕ → ProbabilityMeasure ℝ) (ν0 : ProbabilityMeasure ℝ)
    (hν : ∀ n, ∀ᵐ x ∂(ν n:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    (hν0 : ∀ᵐ x ∂(ν0:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    (hweak : Tendsto ν atTop (𝓝 ν0))
    (u : ℕ → ℝ) {u0 : ℝ} (hu : Tendsto u atTop (𝓝 u0))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {a b : ℝ} (hab : a < b) (hcomponent : volume.restrict (Ioo a b) ≪ (ν0:Measure ℝ)) :
    ∃ n0 : ℕ, ∃ A : CenteredArray Pair,
      A.N=(fun n => N (n+n0)) ∧
      A.law=(fun n => MixedLaw.tiltedLaw i (ν (n+n0):Measure ℝ) (u (n+n0))) ∧
      A.X=(fun n p => p.1-mean i (ν (n+n0)) (u (n+n0))) ∧
      A.Y=(fun _ => integerSign) ∧
      A.vX=variance Prod.fst (MixedLaw.tiltedLaw i (ν0:Measure ℝ) u0) ∧
      A.vY=variance Prod.snd (MixedLaw.tiltedLaw i (ν0:Measure ℝ) u0) ∧
      A.CompactGap := by
  let vX := variance Prod.fst (MixedLaw.tiltedLaw i (ν0:Measure ℝ) u0)
  let vY := variance Prod.snd (MixedLaw.tiltedLaw i (ν0:Measure ℝ) u0)
  have hv := source_variance_positive i ν0 hν0 hab hcomponent u0
  let ell := min vX vY/2
  have hell : 0 < ell := half_pos (lt_min hv.1 hv.2)
  have hellX : ell < vX := by dsimp [ell]; linarith [min_le_left vX vY]
  have hellY : ell < vY := by dsimp [ell]; linarith [min_le_right vX vY]
  have hlim := variance_limits i ν ν0 hν hν0 hweak u hu
  have hevent : ∀ᶠ n in atTop, 0 < N n ∧
      ell ≤ variance Prod.fst (MixedLaw.tiltedLaw i (ν n:Measure ℝ) (u n)) ∧
      ell ≤ variance Prod.snd (MixedLaw.tiltedLaw i (ν n:Measure ℝ) (u n)) := by
    filter_upwards [hN.eventually_ge_atTop 1,hlim.1.eventually_const_le hellX,
      hlim.2.eventually_const_le hellY] with n hn hx hy
    exact ⟨by omega,hx,hy⟩
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp hevent
  have ht (n : ℕ) := hn0 (n+n0) (by omega)
  let row := fun n => MixedLaw.tiltedLaw i (ν (n+n0):Measure ℝ) (u (n+n0))
  let d := fun n => (Real.sqrt (N (n+n0):ℝ))⁻¹
  letI (n : ℕ) : IsProbabilityMeasure (row n) :=
    MixedLaw.tiltedLaw_probability i _ (hν _) _
  have hmarket : Tendsto (fun n => N (n+n0)) atTop atTop := hN.comp (shift_tendsto n0)
  have hd0 : Tendsto d atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hmarket))
  let A : CenteredArray Pair := {
    law := row
    probability := fun n => inferInstance
    X := fun n p => p.1-mean i (ν (n+n0)) (u (n+n0))
    Y := fun _ => integerSign
    N := fun n => N (n+n0)
    d := d
    measurable_X := fun _ => measurable_fst.sub_const _
    measurable_Y := fun _ => measurable_integerSign
    bounded := by
      intro n
      have hm := mean_unit i (ν (n+n0)) (hν _) (u (n+n0))
      filter_upwards [tilted_support i (ν (n+n0)) (hν _) (u (n+n0))] with p hp
      refine ⟨?_,?_⟩
      · rw [abs_le]
        constructor <;> linarith [hp.1.1,hp.1.2,hm.1,hm.2]
      · rw [hp.2.1]
        exact hp.2.2
    mean_X := fun n => centered_mean_zero i _ (hν _) _
    mean_Y := by
      intro n
      calc
        _ = ∫ p, p.2 ∂row n := integral_congr_ae
          ((tilted_support i (ν (n+n0)) (hν _) (u (n+n0))).mono fun _ hp => hp.2.1)
        _ = 0 := MixedLaw.tilted_sign_mean i _ (hν _) _
    covariance := fun n => centered_cross_zero i _ (hν _) _
    d_nonneg := fun n => inv_nonneg.mpr (Real.sqrt_nonneg _)
    d_zero := hd0
    scale := by
      intro n
      have hpos : (0:ℝ) < N (n+n0) := Nat.cast_pos.mpr (ht n).1
      dsimp only [d]
      rw [inv_pow,Real.sq_sqrt hpos.le,mul_inv_cancel₀ hpos.ne']
    market := hmarket
    vX := vX
    vY := vY
    lowerVariance := ell
    lowerVariance_pos := hell
    variance_X_lower := by
      intro n
      rw [centered_square_eq_variance]
      exact (ht n).2.1
    variance_Y_lower := by
      intro n
      rw [sign_square_eq_variance i _ (hν _)]
      exact (ht n).2.2
    variance_X_limit := by
      change Tendsto (fun n => ∫ p, (p.1-mean i (ν (n+n0)) (u (n+n0)))^2 ∂row n)
        atTop (𝓝 vX)
      simp_rw [row,centered_square_eq_variance]
      exact hlim.1.comp (shift_tendsto n0)
    variance_Y_limit := by
      change Tendsto (fun n => ∫ p, (integerSign p:ℝ)^2 ∂row n) atTop (𝓝 vY)
      simp_rw [row,sign_square_eq_variance i _ (hν _)]
      exact hlim.2.comp (shift_tendsto n0) }
  have hrow (n : ℕ) : uncenteredRow A (fun _ p => p.1) (fun _ => measurable_fst) n=
      tiltedProbability i (ν (n+n0)) (hν _) (u (n+n0)) := by
    apply Subtype.ext
    change (row n).map (fun p : Pair => (p.1,(integerSign p:ℝ)))=row n
    calc
      (row n).map (fun p : Pair => (p.1,(integerSign p:ℝ))) = (row n).map id := Measure.map_congr
        ((tilted_support i (ν (n+n0)) (hν _) (u (n+n0))).mono fun p hp =>
          Prod.ext rfl hp.2.1)
      _ = row n := Measure.map_id
  have hweakrow : Tendsto (uncenteredRow A (fun _ p => p.1) (fun _ => measurable_fst)) atTop
      (𝓝 (tiltedProbability i ν0 hν0 u0)) := by
    have heq : uncenteredRow A (fun _ p => p.1) (fun _ => measurable_fst) =
        fun n => tiltedProbability i (ν (n+n0)) (hν _) (u (n+n0)) := funext hrow
    rw [heq]
    exact (tiltedProbability_tendsto i ν ν0 hν hν0 hweak u hu).comp (shift_tendsto n0)
  have hback : MixedLaw.law i (ν0:Measure ℝ) ≪
      (tiltedProbability i ν0 hν0 u0:Measure Pair) :=
    absolutelyContinuous_tilted (integrable_exp_mul_of_bounded (MixedLaw.law i (ν0:Measure ℝ))
      measurable_fst.aemeasurable (MixedLaw.demand_bounds i _ hν0) u0)
  refine ⟨n0,A,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  apply compactGap_of_uncentered_source_limit A (fun _ p => p.1) (fun _ => measurable_fst)
    (fun n => mean i (ν (n+n0)) (u (n+n0)))
    (fun n => (tilted_support i (ν (n+n0)) (hν _) (u (n+n0))).mono fun _ hp =>
      by simpa only [abs_of_nonneg hp.1.1] using hp.1.2)
    (fun _ => Eventually.of_forall fun _ => rfl) i (ν0:Measure ℝ)
    (tiltedProbability i ν0 hν0 u0) hweakrow hback hab hcomponent

end FCAppendix.Affine.Uniform06.LiteralCenteredArray
