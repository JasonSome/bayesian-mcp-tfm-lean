import FCAppendix.Affine.Uniform06.ValueEnvelope
import FCAppendix.Affine.Uniform06.SourcePivotalRates
import FCAppendix.Affine.Uniform06.PureUnionUpper

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.PureEnvelope

open MeasureTheory Set
open FCAppendix.Affine.Uniform07
open scoped BigOperators

def boundaryDerivative (N k : ℕ) (p0 w : ℝ) : ℝ :=
  ((N:ℝ)+1)*PiBinomial.pmf N (p0-w) k

theorem rank_hasDerivAt (N k : ℕ) (hk : k ≤ N) (p0 w : ℝ) :
    HasDerivAt (fun u => Bayes.binomBelow (N+1) (p0-u) (k+1))
      (boundaryDerivative N k p0 w) w := by
  have h := (BinomialPivotal.hasDerivAt_binomBelow N k hk (p0-w)).comp w
    ((hasDerivAt_id w).const_sub p0)
  convert! h using 1
  simp [boundaryDerivative]
  ring

theorem continuous_boundaryDerivative (N k : ℕ) (p0 : ℝ) :
    Continuous (boundaryDerivative N k p0) := by
  unfold boundaryDerivative PiBinomial.pmf
  fun_prop

theorem rank_area (N k : ℕ) (hk : k ≤ N) {p0 v g : ℝ}
    (hv : 0 ≤ v) (hg : 0 < g)
    (hp : ∀ w ∈ Icc (0:ℝ) v, p0-w ∈ Ioo (0:ℝ) 1)
    (hgap : ∀ w ∈ Icc (0:ℝ) v,
      g*((N:ℝ)+1) ≤ ((N:ℝ)+1)*(p0-w)-k) :
    (∫ w in (0:ℝ)..v, Bayes.binomBelow (N+1) (p0-w) (k+1)) ≤
      Bayes.binomBelow (N+1) (p0-v) (k+1)/(g*((N:ℝ)+1)) := by
  let Q := fun w => Bayes.binomBelow (N+1) (p0-w) (k+1)
  have hQcont : Continuous Q := by
    unfold Q Bayes.binomBelow PiBinomial.pmf
    fun_prop
  have hQ0 : 0 < Q 0 := Bayes.binomBelow_pos _ _ (by omega) _ (hp 0 ⟨le_rfl,hv⟩)
  have hbound (w : ℝ) (hw : w ∈ Icc (0:ℝ) v) :
      g*((N:ℝ)+1)*Q w ≤ boundaryDerivative N k p0 w :=
    BinomialPivotal.pivotal_mass_lower_of_gap N k hk (hp w hw) hg.le (hgap w hw)
  have hint := intervalIntegral.integral_mono_on hv
    ((hQcont.const_mul (g*((N:ℝ)+1))).intervalIntegrable (μ := volume) 0 v)
    ((continuous_boundaryDerivative N k p0).intervalIntegrable (μ := volume) 0 v) hbound
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun w (_ : w ∈ uIcc (0:ℝ) v) => rank_hasDerivAt N k hk p0 w)
    ((continuous_boundaryDerivative N k p0).intervalIntegrable (μ := volume) 0 v)
  rw [intervalIntegral.integral_const_mul,hFTC] at hint
  apply (le_div_iff₀ (mul_pos hg (by positivity))).mpr
  change (∫ w in (0:ℝ)..v, Q w)*(g*((N:ℝ)+1)) ≤ Q v
  nlinarith

theorem source_rank_area (i : Row) {m : ℕ} (hm : 4 ≤ m)
    {v : ℝ} (hv : 0 ≤ v) (hvM : v ≤ RankCutoff.Mstar i) :
    (∫ w in (0:ℝ)..v,
      Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) w) ≤
      (20000/(m:ℝ))*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) v := by
  have hc := PhysicalRates.capacity_positive (by omega : 3 ≤ m)
  have hcm := PhysicalRates.capacity_strictly_below_rivals hm
  have hN : m-2+1=m-1 := by omega
  have hK : capacity m-1+1=capacity m := by omega
  have hNreal : ((m-2:ℕ):ℝ)+1=(m:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 2 ≤ m)]
    norm_num
    ring
  have hKreal : ((capacity m-1:ℕ):ℝ)=(capacity m:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ capacity m)]
    norm_num
  have hparam (w : ℝ) (hw : w ∈ Icc (0:ℝ) v) :=
    SourcePivotalRates.source_prefix_rank_parameter i hw.1 (hw.2.trans hvM)
  have hgap (w : ℝ) (hw : w ∈ Icc (0:ℝ) v) :
      (1/10000:ℝ)*(((m-2:ℕ):ℝ)+1) ≤
        (((m-2:ℕ):ℝ)+1)*((1+cutoff i)/2-w)-(capacity m-1:ℕ) := by
    rw [hNreal,hKreal]
    have hmul := mul_le_mul_of_nonneg_left (hparam w hw).2
      (show 0 ≤ (m:ℝ)-1 by
        have h1 : (1:ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
        linarith)
    have hcap := (PhysicalRates.capacity_floor_bounds m).2
    have hr : rho ≤ 1 := by norm_num [rho]
    nlinarith
  have harea := rank_area (m-2) (capacity m-1) (by omega)
    hv (by norm_num : (0:ℝ) < 1/10000) (fun w hw => (hparam w hw).1) hgap
  rw [hN,hK,hNreal] at harea
  have hq := Bayes.binomBelow_pos (m-1) (capacity m) hc
    ((1+cutoff i)/2-v) (hparam v ⟨hv,le_rfl⟩).1
  have hmR : (4:ℝ) ≤ m := by exact_mod_cast hm
  have hcoef : (1:ℝ)/((1/10000)*((m:ℝ)-1)) ≤ 20000/(m:ℝ) := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<1/10000) (by linarith : (0:ℝ)<(m:ℝ)-1))
      (by linarith : (0:ℝ) < m)).mpr
    nlinarith
  change (∫ w in (0:ℝ)..v, Bayes.binomBelow (m-1) (((1+cutoff i)/2)-w) (capacity m)) ≤ _
  exact harea.trans (by
    change _ ≤ (20000/(m:ℝ))*Bayes.binomBelow (m-1) (((1+cutoff i)/2)-v) (capacity m)
    simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using
      mul_le_mul_of_nonneg_right hcoef hq.le)

theorem integrate_actual_envelope
    {v A Uzero : ℝ} (hv : 0 ≤ v) (_hA : 0 ≤ A)
    (U Q B SP SC : ℝ → ℝ)
    (hU : U v-Uzero=∫ w in (0:ℝ)..v, SP (B w)+SC (B w))
    (hQ : IntervalIntegrable Q volume 0 v)
    (hS : IntervalIntegrable (fun w => SP (B w)+SC (B w)) volume 0 v)
    (hpure : ∀ᵐ w ∂volume.restrict (Icc (0:ℝ) v), SP (B w) ≤ A*Q w)
    (hcanon : ∀ᵐ w ∂volume.restrict (Icc (0:ℝ) v), SC (B w) ≤ SC (B v)) :
    U v ≤ Uzero+A*(∫ w in (0:ℝ)..v, Q w)+v*SC (B v) := by
  have hh := intervalIntegral.integral_mono_ae_restrict hv hS
    ((hQ.const_mul A).add intervalIntegrable_const) (by
      filter_upwards [hpure,hcanon] with w hw hc
      exact add_le_add hw hc)
  rw [intervalIntegral.integral_add (hQ.const_mul A) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at hh
  simp only [sub_zero,smul_eq_mul] at hh
  linarith

theorem source_actual_envelope (i : Row) {m : ℕ} (hm : 4 ≤ m)
    {v : ℝ} (hv : 0 ≤ v) (hvM : v ≤ RankCutoff.Mstar i)
    (U B SP SC : ℝ → ℝ)
    (hU : U v=∫ w in (0:ℝ)..v, SP (B w)+SC (B w))
    (hS : IntervalIntegrable (fun w => SP (B w)+SC (B w)) volume 0 v)
    (hpure : ∀ᵐ w ∂volume.restrict (Icc (0:ℝ) v),
      SP (B w) ≤ 2*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) w)
    (hcanon : ∀ᵐ w ∂volume.restrict (Icc (0:ℝ) v), SC (B w) ≤ SC (B v)) :
    U v ≤ (40000/(m:ℝ))*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) v+
      v*SC (B v) := by
  have hQcont : Continuous (Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)) := by
    unfold Rank.pureRank Bayes.binomBelow PiBinomial.pmf
    fun_prop
  have hh := integrate_actual_envelope hv (by norm_num : (0:ℝ) ≤ 2)
    U (Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)) B SP SC
    (Uzero := 0) (by simpa using hU) (hQcont.intervalIntegrable (μ := volume) 0 v) hS hpure hcanon
  have harea := mul_le_mul_of_nonneg_left (source_rank_area i hm hv hvM)
    (by norm_num : (0:ℝ) ≤ 2)
  simp only [zero_add] at hh
  have hcoeff : 2*((20000/(m:ℝ))*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) v)=
      (40000/(m:ℝ))*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) v := by ring
  rw [hcoeff] at harea
  linarith

theorem integrate_actual_envelope_with_remainder
    {v A Uzero e : ℝ} (hv : 0 ≤ v) (_hA : 0 ≤ A)
    (U Q B SP SC : ℝ → ℝ)
    (hU : U v-Uzero=∫ w in (0:ℝ)..v, SP (B w)+SC (B w))
    (hQ : IntervalIntegrable Q volume 0 v)
    (hS : IntervalIntegrable (fun w => SP (B w)+SC (B w)) volume 0 v)
    (hpure : ∀ᵐ w ∂volume.restrict (Icc (0:ℝ) v), SP (B w) ≤ A*Q w+e)
    (hcanon : ∀ᵐ w ∂volume.restrict (Icc (0:ℝ) v), SC (B w) ≤ SC (B v)) :
    U v ≤ Uzero+A*(∫ w in (0:ℝ)..v, Q w)+v*e+v*SC (B v) := by
  have hh := intervalIntegral.integral_mono_ae_restrict hv hS
    (((hQ.const_mul A).add intervalIntegrable_const).add intervalIntegrable_const) (by
      filter_upwards [hpure,hcanon] with w hw hc
      exact add_le_add hw hc)
  rw [intervalIntegral.integral_add ((hQ.const_mul A).add intervalIntegrable_const)
      intervalIntegrable_const,
    intervalIntegral.integral_add (hQ.const_mul A) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const,
    intervalIntegral.integral_const] at hh
  simp only [sub_zero,smul_eq_mul] at hh
  linarith

theorem source_actual_envelope_with_remainder (i : Row) {m : ℕ} (hm : 4 ≤ m)
    {v : ℝ} (hv : 0 ≤ v) (hvM : v ≤ RankCutoff.Mstar i)
    (U B SP SC : ℝ → ℝ)
    (hU : U v=∫ w in (0:ℝ)..v, SP (B w)+SC (B w))
    (hS : IntervalIntegrable (fun w => SP (B w)+SC (B w)) volume 0 v)
    (hpure : ∀ᵐ w ∂volume.restrict (Icc (0:ℝ) v),
      SP (B w) ≤ 2*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) w+
        Real.exp (-(9/1000000:ℝ)*m))
    (hcanon : ∀ᵐ w ∂volume.restrict (Icc (0:ℝ) v), SC (B w) ≤ SC (B v)) :
    U v ≤ (40000/(m:ℝ))*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) v+
      v*Real.exp (-(9/1000000:ℝ)*m)+v*SC (B v) := by
  have hQcont : Continuous (Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)) := by
    unfold Rank.pureRank Bayes.binomBelow PiBinomial.pmf
    fun_prop
  have hh := integrate_actual_envelope_with_remainder hv (by norm_num : (0:ℝ) ≤ 2)
    U (Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)) B SP SC
    (Uzero := 0) (by simpa using hU) (hQcont.intervalIntegrable (μ := volume) 0 v) hS hpure hcanon
  have harea := mul_le_mul_of_nonneg_left (source_rank_area i hm hv hvM)
    (by norm_num : (0:ℝ) ≤ 2)
  have hcoeff : 2*((20000/(m:ℝ))*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) v)=
      (40000/(m:ℝ))*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) v := by ring
  rw [hcoeff] at harea
  simp only [zero_add] at hh
  linarith

theorem source_rank_pure_upper_ae (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hatom : NullSingletonClass (G.map Prod.snd)) (B : ℝ → ℝ)
    {v : ℝ} (hvM : v ≤ RankCutoff.Mstar i)
    (hB : ∀ᵐ w ∂volume.restrict (Icc (0:ℝ) v),
      0 < B w ∧ PureRankCounts.sourceRank (cutoff i) (G.map Prod.snd) (B w)=w) :
    ∀ᵐ w ∂volume.restrict (Icc (0:ℝ) v),
      PurePivotalSource.expectedUnequalPureFirst (m-1) (capacity m) (kappa i)
        (cutoff i) (G.map Prod.snd) (B w) ≤
      2*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) w+
        Real.exp (-(9/1000000:ℝ)*m) := by
  letI := hatom
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  filter_upwards [hB,ae_restrict_mem measurableSet_Icc] with w hw hwI
  have hh := PureUnionUpper.source_pure_union_upper i hm (G.map Prod.snd) hw.1
    (measure_singleton (B w)) (by rw [hw.2]; exact hwI.2.trans hvM)
  simpa only [hw.2] using hh

end FCAppendix.Affine.Uniform06.PureEnvelope
