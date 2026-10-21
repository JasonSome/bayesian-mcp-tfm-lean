import FCAppendix.Affine.Hybrid.UpperLaw
import FCAppendix.Affine.Hybrid.UpperFiniteError

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology
open Game Bayes Existence.RankEnvelope

theorem eventually_capacity_valid (c : ℕ→ℕ) {rho : ℝ}
    (h0 : 0< rho) (h1 : rho<1)
    (hc : Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) atTop (𝓝 rho)) :
    ∀ᶠm in atTop,2 ≤ m ∧ 1 ≤ c m ∧ c m < m := by
  filter_upwards [eventually_ge_atTop 2,
    hc.eventually (Ioi_mem_nhds h0),hc.eventually (Iio_mem_nhds h1)]
    with m hm hlo hhi
  have hmpos : (0:ℝ)< m := Nat.cast_pos.mpr (by omega)
  have hcpos : (0:ℝ)< c m := (div_pos_iff_of_pos_right hmpos).mp hlo
  have hclt : (c m:ℝ)< m := (div_lt_one hmpos).mp hhi
  have hcNat : 0< c m := by exact_mod_cast hcpos
  exact ⟨hm,by omega,by exact_mod_cast hclt⟩

theorem weighted_upper_contact_le (FH : ProbabilityMeasure ℝ) (h t : ℝ)
    (hh : 0 ≤ h) :
    contactTail (ENNReal.ofReal h • (FH : Measure ℝ)) 2 t ≤ h/2 := by
  letI : IsFiniteMeasure (ENNReal.ofReal h • (FH : Measure ℝ)) := by
    constructor
    simp only [Measure.smul_apply,smul_eq_mul,measure_univ,mul_one]
    exact ENNReal.ofReal_lt_top
  have hmass : (ENNReal.ofReal h • (FH : Measure ℝ)).real univ=h := by
    simp only [Measure.real,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one,
      ENNReal.toReal_ofReal hh]
  have htail : (ENNReal.ofReal h • (FH : Measure ℝ)).real (Ioi t) ≤
      (ENNReal.ofReal h • (FH : Measure ℝ)).real univ := by
    exact measureReal_mono (subset_univ _)
  unfold contactTail
  rw [hmass] at htail
  simpa only [Nat.cast_ofNat] using div_le_div_of_nonneg_right htail (by norm_num : (0:ℝ)≤2)

theorem construct_actual_upper_law (FH : ProbabilityMeasure ℝ)
    [NullSingletonClass (FH : Measure ℝ)]
    (h : ℝ) (hh : 0< h) (hh1 : h ≤ 1)
    (m c : ℕ) (hm : 2 ≤ m) (hc : 1 ≤ c) (hcm : c < m)
    (t R H : ℝ) (hR : 0< R) (hRt : R< t)
    (hsupport : ∀ᵐv ∂(FH : Measure ℝ),v∈ Icc t H) :
    let mu:=ENNReal.ofReal h • (FH : Measure ℝ)
    let q:=rank mu (m-1) c 2
    let b:=bid q t R
    ∃PH : ProbabilityMeasure (ℝ×JointAction 2),
      (PH : Measure (ℝ×JointAction 2)).map Prod.fst=(FH : Measure ℝ) ∧
      (PH : Measure (ℝ×JointAction 2)).map (fun x=> x.2.bid)=(FH : Measure ℝ).map b ∧
      (∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),R ≤ x.2.bid ∧ x.2.routeCount=1) ∧
      (∀ y : ℝ,(PH : Measure (ℝ×JointAction 2)) {x | x.2.bid=y}=0) := by
  have he : m-2+1=m-1 := by omega
  simpa only [he] using exists_upper_joint FH h hh hh1 (m-2) c hc (by omega)
    t R H hR hRt hsupport

theorem upper_source_error_limits (FH : ProbabilityMeasure ℝ)
    [NullSingletonClass (FH : Measure ℝ)]
    (h rho : ℝ) (hh : 0< h) (hh1 : h ≤ 1) (hlo : h/2< rho) (hrho1 : rho<1)
    (c : ℕ→ℕ) (hc : Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) atTop (𝓝 rho))
    (t R H : ℝ) (hRt : R ≤ t)
    (hsupport : ∀ᵐv ∂(FH : Measure ℝ),v∈ Icc t H) :
    let mu:=ENNReal.ofReal h • (FH : Measure ℝ)
    Tendsto (fun m=> rank mu (m-1) (c m) 2 t) atTop (𝓝 1) ∧
      Tendsto (fun m=> error (rank mu (m-1) (c m) 2) t R) atTop (𝓝 0) := by
  let mu:=ENNReal.ofReal h • (FH : Measure ℝ)
  letI : IsFiniteMeasure mu := by
    constructor
    simp only [mu,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one]
    exact ENNReal.ofReal_lt_top
  letI : NullSingletonClass mu :=
    ⟨fun v=> by simp only [mu,Measure.smul_apply,smul_eq_mul,measure_singleton,mul_zero]⟩
  have hmass : mu.real univ ≤ 1 := by
    simpa only [mu,Measure.real,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one,
      ENNReal.toReal_ofReal hh.le] using hh1
  have hgap : contactTail mu 2 t< rho :=
    (weighted_upper_contact_le FH h t hh.le).trans_lt hlo
  have hrho0 : 0< rho := (half_pos hh).trans hlo
  obtain ⟨M0,hM0⟩ := eventually_atTop.mp (eventually_capacity_valid c hrho0 hrho1 hc)
  let N : ℕ→ℕ := fun k=> k+M0-1
  let C : ℕ→ℕ := fun k=> c (k+M0)
  have hvalid (k : ℕ) : 2 ≤ k+M0 ∧ 1 ≤ C k ∧ C k< k+M0 := hM0 _ (by omega)
  have hN : Tendsto N atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp (tendsto_add_atTop_nat M0)
  have hC0 (k : ℕ) : 1 ≤ C k := (hvalid k).2.1
  have hCN (k : ℕ) : C k ≤ N k := by
    dsimp only [N]
    have := (hvalid k).2.2
    omega
  have hden (k : ℕ) : (N k:ℝ)+1=(k+M0:ℕ) := by
    have hn : N k+1=k+M0 := by dsimp [N];have := (hvalid k).1;omega
    exact_mod_cast hn
  have hdensity : Tendsto (fun k=>(C k:ℝ)/((N k:ℝ)+1)) atTop (𝓝 rho) := by
    simpa only [hden,C,Function.comp_def] using hc.comp (tendsto_add_atTop_nat M0)
  have hsMu : ∀ᵐv ∂mu,v ≤ H :=
    Measure.ae_smul_measure (hsupport.mono (fun _ hv=> hv.2)) _
  obtain ⟨v,hv⟩ := hsupport.exists
  have htH : t ≤ H := hv.1.trans hv.2
  have hq := rank_floor_tendsto_one mu hmass N C hN
    (fun k=>(hCN k).trans (Nat.le_succ _)) rho t hdensity hgap
  have hE := upper_error_tendsto_zero mu hmass N C hN hC0 hCN rho t R H
    hRt htH hsMu hdensity hgap
  dsimp only
  exact ⟨(tendsto_add_atTop_iff_nat M0).mp hq,
    (tendsto_add_atTop_iff_nat M0).mp hE⟩

theorem eventually_actual_upper_hidden_guard (FH : ProbabilityMeasure ℝ)
    [NullSingletonClass (FH : Measure ℝ)]
    (h rho eta : ℝ) (hh : 0< h) (hh1 : h ≤ 1) (hlo : h/2< rho)
    (hrho1 : rho<1) (heta : 0< eta)
    (c : ℕ→ℕ) (hc : Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) atTop (𝓝 rho))
    (t R H : ℝ) (hR : 0< R) (hRt : R< t)
    (hsupport : ∀ᵐv ∂(FH : Measure ℝ),v∈ Icc t H) :
    ∀ᶠm in atTop,
      error (rank (ENNReal.ofReal h • (FH : Measure ℝ)) (m-1) (c m) 2) t R <
        eta*R*(1-2*(1-rank (ENNReal.ofReal h • (FH : Measure ℝ)) (m-1) (c m) 2 t)) := by
  obtain ⟨hq,hE⟩ := upper_source_error_limits FH h rho hh hh1 hlo hrho1 c hc
    t R H hRt.le hsupport
  have hd : Tendsto
      (fun m=>1-rank (ENNReal.ofReal h • (FH : Measure ℝ)) (m-1) (c m) 2 t)
      atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x:=(1:ℝ))).sub hq
  exact eventually_upper_hidden_guard hE hd heta hR

end FCAppendix.Affine.Hybrid.Native02
