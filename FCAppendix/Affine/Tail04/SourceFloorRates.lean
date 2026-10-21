import FCAppendix.Affine.Tail04.SourceMovingMenuRates
import FCAppendix.Affine.Tail04.SourceCommonMenuError
import FCAppendix.Affine.Tail04.OriginalUpperSource
import FCAppendix.Affine.Tail04.OriginalMovingUpperEnvelope
import FCAppendix.Affine.Tail04.SourceBoundaryCost

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceFloorRates
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open OriginalValues SourceMovingScalarGuards SourceMovingMenuRates
open SourceTailTaylor SourceTailCapGap SourceBoundaryCost MenuError

def capacity (N : ℕ) : ℕ := iidCapacity (99/200) N

lemma capacity_eq (N : ℕ) : capacity N=marketCapacity (N+1) := by
  simp only [capacity,iidCapacity,marketCapacity,Nat.cast_add,Nat.cast_one]

def q (P : ValueParameters) (N : ℕ) : ℝ :=
  OriginalMovingUpperEnvelope.q P (cutoff N) (N+1) (capacity N) (cutoff N)

lemma q_bounds (P : ValueParameters) (N : ℕ) : 0≤ q P N ∧ q P N≤1 := by
  simpa only [q,OriginalMovingUpperEnvelope.q,Nat.add_sub_cancel,Set.mem_Icc] using
    Existence.RankEnvelope.rank_bounds (P.movingUpperMeasure (cutoff N)) N (capacity N)
      (by norm_num : 2≤2) (OriginalMovingUpperEnvelope.measure_mass_le_one P (cutoff N))
      (cutoff N)

lemma q_pos (P : ValueParameters) (N : ℕ) (hc : 0< capacity N) : 0< q P N := by
  simpa only [q,OriginalMovingUpperEnvelope.q,Nat.add_sub_cancel] using
    Existence.RankEnvelope.rank_pos (P.movingUpperMeasure (cutoff N)) N (capacity N) hc
      (by norm_num : 2≤2) (OriginalMovingUpperEnvelope.measure_mass_le_one P (cutoff N))
      (cutoff N)

lemma deficit_eq (P : ValueParameters) (N : ℕ) :
    1-q P N=originalMovingDeficit
      (fun n=> P.movingUpperMeasure (movingThreshold n)) (N+1) := by
  simp only [q,OriginalMovingUpperEnvelope.q,originalMovingDeficit,cutoff,capacity_eq]

theorem scaled_deficit (P : ValueParameters) :
    Tendsto (fun N=> cutoff N^2*(1-q P N)) atTop (𝓝 0) := by
  have hz : ∀ᶠ m : ℕ in atTop,0≤(0:ℝ) ∧ (0:ℝ)≤ movingThreshold m :=
    Eventually.of_forall (fun m=>⟨le_rfl,Real.rpow_nonneg (Nat.cast_nonneg m) _⟩)
  have hh := (P.originalMovingUpper_scaled_limits (fun _=>0) hz).1.comp
    (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def,cutoff,←deficit_eq] using hh

theorem q_tendsto (P : ValueParameters) : Tendsto (q P) atTop (𝓝 1) := by
  have hd : Tendsto (fun N=>1-q P N) atTop (𝓝 0) := by
    apply squeeze_zero (fun N=> sub_nonneg.mpr (q_bounds P N).2) _ (scaled_deficit P)
    intro N
    have ht := movingThreshold_ge_one (N+1) (by omega)
    change 1≤ cutoff N at ht
    have hs : 1≤ cutoff N^2 := by nlinarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs
      (sub_nonneg.mpr (q_bounds P N).2)
  simpa only [sub_zero,sub_sub_cancel] using (tendsto_const_nhds (x:=(1:ℝ))).sub hd

theorem scaled_inverse_correction (P : ValueParameters) :
    Tendsto (fun N=> cutoff N^2*(1/q P N-1)) atTop (𝓝 0) := by
  have hh := (scaled_deficit P).div (q_tendsto P) (by norm_num : (1:ℝ)≠0)
  have hh0 : Tendsto (fun N=> (cutoff N^2*(1-q P N))/q P N) atTop (𝓝 0) := by
    simpa only [zero_div,Pi.div_apply] using! hh
  apply hh0.congr'
  filter_upwards [(q_tendsto P).eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1))] with N hq
  field_simp [hq.ne']

def error (P : ValueParameters) (ξ : ℝ) (N : ℕ) : ℝ :=
  (cutoff N+2*Central.B ξ)*rate (SourceCommonMenuError.commonCoefficient P ξ)
    (lowMass P.theta) P.bulkWeight N

lemma error_nonneg (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) (N : ℕ) :
    0≤ error P ξ N := by
  have ht := movingThreshold_pos (N+1) (by omega)
  have hB : 0< Central.B ξ := by unfold Central.B;linarith
  exact mul_nonneg (by change 0≤ movingThreshold (N+1)+2*Central.B ξ;linarith)
    (rate_nonneg (SourceCommonMenuError.commonCoefficient_nonnegative P hξ) P.bulkWeight_pos.le N)

theorem scaled_error (P : ValueParameters) (ξ : ℝ) :
    Tendsto (fun N=> cutoff N*error P ξ N) atTop (𝓝 0) := by
  have hs : 0< lowMass P.theta := P.low_mass_pos
  have hmain := scaled_rate_tendsto (K:=SourceCommonMenuError.commonCoefficient P ξ)
    hs P.bulkWeight_pos
  have hinv : Tendsto (fun N=>2*Central.B ξ/cutoff N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop cutoff_tendsto
  have hh := ((tendsto_const_nhds (x:=(1:ℝ))).add hinv).mul hmain
  convert! hh using 1
  · funext N
    have ht := movingThreshold_pos (N+1) (by omega)
    change 0< cutoff N at ht
    unfold error
    field_simp [ht.ne']
  · simp

lemma boundary_ratio (B : ℝ) :
    Tendsto (fun N=> cutoff N/(cutoff N-B)) atTop (𝓝 1) := by
  have hh : Tendsto (fun N=>1-B/cutoff N) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_const_nhds.div_atTop cutoff_tendsto :
        Tendsto (fun N=> B/cutoff N) atTop (𝓝 0))
  have hi := (tendsto_const_nhds (x:=(1:ℝ))).div hh (by norm_num : (1:ℝ)≠0)
  have hi0 : Tendsto (fun N=> 1/(1-B/cutoff N)) atTop (𝓝 1) := by
    simpa only [div_one,Pi.div_apply] using! hi
  apply hi0.congr'
  filter_upwards [cutoff_tendsto.eventually_gt_atTop B] with N hN
  have ht := movingThreshold_pos (N+1) (by omega)
  change 0< cutoff N at ht
  field_simp [ht.ne',(sub_pos.mpr hN).ne']

structure Budgets (P : ValueParameters) (ξ Amin Amax k : ℝ) (N : ℕ) : Prop where
  above_endpoint : Central.B ξ< cutoff N
  comparison_room : endpointRadius Amin/cutoff N≤ Central.B ξ-1
  lower : 1/(4*Amin*(cutoff N-Central.B ξ))+error P ξ N+
    cutoff N*(1/q P N-1)< k/cutoff N
  upper : taylorConstant ξ (endpointRadius Amin)/cutoff N^2+error P ξ N<
    1/(4*Amax*cutoff N)

theorem eventually_budgets (P : ValueParameters) {ξ Amin Amax k : ℝ}
    (hξ : 0< ξ) (_hmin : 0< Amin) (hmax : 0< Amax)
    (hk : 1/(4*Amin)< k) :
    ∀ᶠ N in atTop,Budgets P ξ Amin Amax k N := by
  have hB : 0< Central.B ξ-1 := by unfold Central.B;linarith
  have hfirst : Tendsto (fun N=> cutoff N/(4*Amin*(cutoff N-Central.B ξ)))
      atTop (𝓝 (1/(4*Amin))) := by
    convert! (boundary_ratio (Central.B ξ)).div_const (4*Amin) using 1
    funext N
    rw [div_div]
    congr 1
    ring
  have hlow := (hfirst.add (scaled_error P ξ)).add (scaled_inverse_correction P)
  have hlow' : Tendsto (fun N=> cutoff N*(1/(4*Amin*(cutoff N-Central.B ξ))+
      error P ξ N+cutoff N*(1/q P N-1))) atTop (𝓝 (1/(4*Amin))) := by
    convert! hlow using 1
    · funext N
      ring
    · ring
  have hTaylor : Tendsto (fun N=> taylorConstant ξ (endpointRadius Amin)/cutoff N)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop cutoff_tendsto
  have hup' : Tendsto (fun N=> cutoff N*
      (taylorConstant ξ (endpointRadius Amin)/cutoff N^2+error P ξ N))
      atTop (𝓝 0) := by
    have hh := hTaylor.add (scaled_error P ξ)
    convert! hh using 1
    · funext N
      have ht := movingThreshold_pos (N+1) (by omega)
      change 0< cutoff N at ht
      field_simp [ht.ne']
    · ring
  have hroom : Tendsto (fun N=> endpointRadius Amin/cutoff N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop cutoff_tendsto
  have hbound : 0<1/(4*Amax) := by positivity
  filter_upwards [cutoff_tendsto.eventually_gt_atTop (Central.B ξ),
    hroom.eventually (gt_mem_nhds hB),hlow'.eventually (gt_mem_nhds hk),
    hup'.eventually (gt_mem_nhds hbound)] with N hN hr hl hu
  have ht := movingThreshold_pos (N+1) (by omega)
  change 0< cutoff N at ht
  refine ⟨hN,hr.le,?_,?_⟩
  · apply (lt_div_iff₀ ht).mpr
    nlinarith only [hl]
  · have he : 1/(4*Amax*cutoff N)=(1/(4*Amax))/cutoff N := by ring
    rw [he]
    apply (lt_div_iff₀ ht).mpr
    nlinarith only [hu]

end FCAppendix.Affine.Tail04.SourceFloorRates
