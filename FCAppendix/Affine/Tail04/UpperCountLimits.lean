import FCAppendix.Affine.Tail04.FixedUpperAdaptation
import FCAppendix.Affine.Tail04.UpperOriginal
import FCAppendix.Finite.ConditionalCountLaw
import FCAppendix.Finite.PPIRankTypes

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes Classical
open Existence.RankEnvelope
open scoped BigOperators

def upperSingletonCount (p : ℝ) (hp0 : 0≤ p) (hp1 : p≤1) : CountLaw 2 :=
  (IndependentCounts.bernoulli p hp0 hp1).map
    (fun z => if z then (1:Fin 3) else 0)

theorem upperSingletonCount_expect (p : ℝ) (hp0 : 0≤ p) (hp1 : p≤1)
    (f : Fin 3 → ℝ) :
    (upperSingletonCount p hp0 hp1).expect f = (1-p)*f 0+p*f 1 := by
  unfold upperSingletonCount
  rw [FiniteLaw.expect_map,IndependentCounts.expect_bernoulli]
  simp

theorem upperSingletonCount_statistics (p : ℝ) (hp0 : 0≤ p) (hp1 : p≤1) :
    (upperSingletonCount p hp0 hp1).success=p ∧
    (upperSingletonCount p hp0 hp1).load=p ∧
    (upperSingletonCount p hp0 hp1).duplicates=0 := by
  have hS : (upperSingletonCount p hp0 hp1).success=p := by
    rw [CountLaw.success,upperSingletonCount_expect]
    norm_num [successIndicator]
  have hL : (upperSingletonCount p hp0 hp1).load=p := by
    rw [CountLaw.load,upperSingletonCount_expect]
    norm_num
  exact ⟨hS,hL,by rw [CountLaw.duplicates,hS,hL];ring⟩

section NativeCount
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem native_singleton_count_expect (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) (a : JointAction 2) (hk : a.routeCount=1) (f : Fin 3 → ℝ) :
    ((problem Γ i).outcome a).expect f =
      (1-meanAcceptProb Γ i a.bid)*f 0+meanAcceptProb Γ i a.bid*f 1 := by
  have hs : (∫ ω, successIndicator (focalCount Γ i a ω).val ∂sampleLaw Γ) =
      meanAcceptProb Γ i a.bid := by
    simpa only [problem_outcome,CountLaw.success,CountLaw.expect_ofMeasure] using
      singleton_success Γ (by norm_num) i a hk
  have he : (fun ω => f (focalCount Γ i a ω)) =
      fun ω => f 0+(f 1-f 0)*successIndicator (focalCount Γ i a ω).val := by
    funext ω
    have hb : (focalCount Γ i a ω).val≤1 := by
      simpa only [hk] using focalCount_le Γ i a ω
    have hz : focalCount Γ i a ω=0 ∨ focalCount Γ i a ω=1 := by
      have hh : (focalCount Γ i a ω).val=0 ∨ (focalCount Γ i a ω).val=1 := by omega
      exact hh.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
    rcases hz with hz | hz <;> simp [hz,successIndicator]
  have hi := CountLaw.integrable_comp (sampleLaw Γ) (focalCount Γ i a)
    (measurable_focalCount Γ i a) (fun r => successIndicator r.val)
  rw [problem_outcome,CountLaw.expect_ofMeasure,he,
    integral_add (integrable_const (f 0)) (hi.const_mul (f 1-f 0)),
    integral_const_mul,hs]
  simp only [integral_const,probReal_univ,one_smul]
  ring

theorem native_singleton_count_law (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) (a : JointAction 2) (hk : a.routeCount=1)
    (p : ℝ) (hp0 : 0≤ p) (hp1 : p≤1) (hmean : meanAcceptProb Γ i a.bid=p) :
    (problem Γ i).outcome a = upperSingletonCount p hp0 hp1 := by
  apply FiniteLaw.ext
  intro r
  have hh : ∀ f : Fin 3 → ℝ,
      ((problem Γ i).outcome a).expect f=(upperSingletonCount p hp0 hp1).expect f := by
    intro f
    rw [native_singleton_count_expect Γ i a hk f,hmean,upperSingletonCount_expect]
  simpa only [FiniteLaw.expect_singleton] using hh (fun z => if z=r then 1 else 0)

theorem native_original_upper_mean_at_value (Γ : FiniteGame m 2 c Seed)
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hm : 2≤ m) (hc : 1≤ c) (hcm : c< m) (hmass : mu.real univ≤1)
    (t R : ℝ) (hR : 0< R) (hRt : R< t) (hsupport : ∀ᵐ v ∂mu, t≤ v)
    (hmean : ∀ (i : Fin m) (y : ℝ), R≤ y →
      meanAcceptProb Γ i y=
        bidRank mu (m-1) c 2 (bid (rank mu (m-1) c 2) t R) y)
    (i : Fin m) (v : ℝ) (hv : t≤ v) :
    meanAcceptProb Γ i (Hybrid.upperAction (bid (rank mu (m-1) c 2) t R) v).bid =
      rank mu (m-1) c 2 v := by
  let q := rank mu (m-1) c 2
  let b := bid q t R
  have he : m-2+1=m-1 := by omega
  have hqmono : Monotone q := by
    simpa only [q,he] using
      rank_monotone mu (r := m-2) hc (by omega) (by norm_num) hmass
  have hqpos : ∀ x, 0< q x := fun x => rank_pos mu _ _ hc (by norm_num) hmass x
  have hb : Continuous b := continuous_bid (continuous_rank mu _ _ _)
    (fun x => (hqpos x).ne') t R
  have hfloor : R≤ b v := floor_le_bid hqmono hRt.le (hqpos t) hv
  have hact : (Hybrid.upperAction b v).bid=b v := max_eq_left (hR.le.trans hfloor)
  letI : NullSingletonClass (mu.map b) := by
    simpa only [b,q,he] using rank_atomless_bid mu (r := m-2) hc
      (by omega) (by norm_num) hmass hRt hsupport
  rw [hact,hmean i (b v) hfloor]
  exact bidRank_at_report mu hb.measurable hv
    (bid_monotoneOn hqmono hRt.le (hqpos t)) hsupport (m-1) c 2

theorem native_original_upper_count_expect (Γ : FiniteGame m 2 c Seed)
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hm : 2≤ m) (hc : 1≤ c) (hcm : c< m) (hmass : mu.real univ≤1)
    (t R : ℝ) (hR : 0< R) (hRt : R< t) (hsupport : ∀ᵐ v ∂mu, t≤ v)
    (hmean : ∀ (i : Fin m) (y : ℝ), R≤ y →
      meanAcceptProb Γ i y=
        bidRank mu (m-1) c 2 (bid (rank mu (m-1) c 2) t R) y)
    (i : Fin m) (v : ℝ) (hv : t≤ v) (f : Fin 3 → ℝ) :
    ((problem Γ i).outcome
      (Hybrid.upperAction (bid (rank mu (m-1) c 2) t R) v)).expect f =
      (1-rank mu (m-1) c 2 v)*f 0+rank mu (m-1) c 2 v*f 1 := by
  rw [native_singleton_count_expect Γ i _ rfl f,
    native_original_upper_mean_at_value Γ mu hm hc hcm hmass t R hR hRt hsupport hmean i v hv]

theorem native_original_upper_conditional_expect (Γ : FiniteGame m 2 c Seed)
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hm : 2≤ m) (hc : 1≤ c) (hcm : c< m) (hmass : mu.real univ≤1)
    (t R : ℝ) (hR : 0< R) (hRt : R< t) (hsupport : ∀ᵐ v ∂mu, t≤ v)
    (hmean : ∀ (i : Fin m) (y : ℝ), R≤ y →
      meanAcceptProb Γ i y=
        bidRank mu (m-1) c 2 (bid (rank mu (m-1) c 2) t R) y)
    (v : ℝ) (hv : t≤ v)
    (hσ : Γ.σ v=Measure.dirac (Hybrid.upperAction (bid (rank mu (m-1) c 2) t R) v))
    (f : Fin 3 → ℝ) :
    (conditionalTypeCountLaw Γ (by omega) v).expect f =
      (1-rank mu (m-1) c 2 v)*f 0+rank mu (m-1) c 2 v*f 1 := by
  rw [conditionalTypeCountLaw_expect,hσ]
  have hterm (i : Fin m) :
      (∫ act, ((problem Γ i).outcome act).expect f
        ∂Measure.dirac (Hybrid.upperAction (bid (rank mu (m-1) c 2) t R) v)) =
        (1-rank mu (m-1) c 2 v)*f 0+rank mu (m-1) c 2 v*f 1 := by
    rw [integral_dirac]
    exact native_original_upper_count_expect Γ mu hm hc hcm hmass t R hR hRt
      hsupport hmean i v hv f
  simp_rw [hterm]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hmR : (m:ℝ)≠0 := by exact_mod_cast (by omega : m≠0)
  field_simp

theorem native_original_upper_conditional_law (Γ : FiniteGame m 2 c Seed)
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hm : 2≤ m) (hc : 1≤ c) (hcm : c< m) (hmass : mu.real univ≤1)
    (t R : ℝ) (hR : 0< R) (hRt : R< t) (hsupport : ∀ᵐ v ∂mu, t≤ v)
    (hmean : ∀ (i : Fin m) (y : ℝ), R≤ y →
      meanAcceptProb Γ i y=
        bidRank mu (m-1) c 2 (bid (rank mu (m-1) c 2) t R) y)
    (v : ℝ) (hv : t≤ v)
    (hσ : Γ.σ v=Measure.dirac (Hybrid.upperAction (bid (rank mu (m-1) c 2) t R) v)) :
    conditionalTypeCountLaw Γ (by omega) v =
      upperSingletonCount (rank mu (m-1) c 2 v)
        (rank_bounds mu (m-1) c (by norm_num) hmass v).1
        (rank_bounds mu (m-1) c (by norm_num) hmass v).2 := by
  apply FiniteLaw.ext
  intro r
  have he := native_original_upper_conditional_expect Γ mu hm hc hcm hmass
    t R hR hRt hsupport hmean v hv hσ (fun z => if z=r then 1 else 0)
  rw [←upperSingletonCount_expect (rank mu (m-1) c 2 v)
    (rank_bounds mu (m-1) c (by norm_num) hmass v).1
    (rank_bounds mu (m-1) c (by norm_num) hmass v).2
    (fun z : Fin 3 => if z=r then 1 else 0)] at he
  simpa only [FiniteLaw.expect_singleton] using he

end NativeCount

theorem original_fixed_upper_bid_tendsto
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hmass : mu.real univ≤7/10) (t R M hTail : ℝ)
    (hR : 0< R) (hRt : R< t) (htM : t≤ M) (hh : hTail∈Icc (0:ℝ) 1)
    (hsupport : ∀ᵐ v ∂mu, t≤ v)
    (hrelative : ∀ v, M≤ v → mu.real (Ioi v)=hTail*powerTail M 10 v)
    (v : ℝ) (hv : t≤ v) :
    Tendsto (fun m : ℕ => bid (rank mu (m-1) (marketCapacity m) 2) t R v)
      atTop (𝓝 R) := by
  have hq := original_fixed_rank_tendsto_one mu hmass t
  have hE := original_fixed_error_tendsto_zero mu hmass t R M hTail
    (hR.trans hRt) hRt.le htM hh hrelative
  have hupper : Tendsto (fun m : ℕ => R+
      error (rank mu (m-1) (marketCapacity m) 2) t R/
        rank mu (m-1) (marketCapacity m) 2 t) atTop (𝓝 R) := by
    simpa only [zero_div,add_zero,Pi.div_apply] using
      (tendsto_const_nhds (x := R)).add (hE.div hq (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_ge_atTop (200:ℕ)] with m hm
    exact ((original_fixed_upper_envelope mu hmass t R M hTail hR hRt htM hh
      hsupport hrelative m hm).error_bounds v hv).2.1
  · filter_upwards [eventually_ge_atTop (200:ℕ)] with m hm
    exact ((original_fixed_upper_envelope mu hmass t R M hTail hR hRt htM hh
      hsupport hrelative m hm).error_bounds v hv).2.2

section Family
variable {Seed : Type*} [MeasurableSpace Seed]

theorem native_original_fixed_upper_conditional_tendsto
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hmass : mu.real univ≤7/10) (t R : ℝ) (hR : 0< R) (hRt : R< t)
    (hsupport : ∀ᵐ v ∂mu, t≤ v)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hN200 : ∀ k, 200≤ N k)
    (Γ : ∀ k, FiniteGame (N k) 2 (marketCapacity (N k)) Seed)
    (hmean : ∀ k (i : Fin (N k)) (y : ℝ), R≤ y →
      meanAcceptProb (Γ k) i y=
        bidRank mu (N k-1) (marketCapacity (N k)) 2
          (bid (rank mu (N k-1) (marketCapacity (N k)) 2) t R) y)
    (hσ : ∀ k v, t≤ v → (Γ k).σ v=
      Measure.dirac (Hybrid.upperAction
        (bid (rank mu (N k-1) (marketCapacity (N k)) 2) t R) v)) :
    ∀ v, t≤ v → ∀ f : Fin 3 → ℝ,
      Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (by have := hN200 k;omega) v).expect f)
        atTop (𝓝 (f 1)) := by
  intro v hv f
  have hq := (original_fixed_rank_tendsto_one mu hmass v).comp hN
  have he : (fun k => (conditionalTypeCountLaw (Γ k) (by have := hN200 k;omega) v).expect f) =
      fun k => (1-rank mu (N k-1) (marketCapacity (N k)) 2 v)*f 0+
        rank mu (N k-1) (marketCapacity (N k)) 2 v*f 1 := by
    funext k
    have hcap := capacity_bounds (N k) (hN200 k)
    exact native_original_upper_conditional_expect (Γ k) mu (by have := hN200 k;omega)
      hcap.2.2.1 hcap.2.2.2 (hmass.trans (by norm_num))
      t R hR hRt hsupport (hmean k) v hv (hσ k v hv) f
  rw [he]
  simpa only [sub_self,zero_mul,one_mul,zero_add,Function.comp_def] using
    (((tendsto_const_nhds (x := (1:ℝ))).sub hq).mul_const (f 0)).add (hq.mul_const (f 1))

end Family
end FCAppendix.Affine.Tail04
