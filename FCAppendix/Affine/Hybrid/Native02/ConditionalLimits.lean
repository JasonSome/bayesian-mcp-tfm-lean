import FCAppendix.Finite.ConditionalCountLaw
import FCAppendix.Probability.IndependentCounts
import FCAppendix.Affine.Hybrid.Native02.NullTypes

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open scoped BigOperators

def activeLimitLaw (z q : ℝ) (hz0 : 0≤ z) (hz1 : z≤1)
    (hq0 : 0≤ q) (hq1 : q≤1) : CountLaw 2 :=
  FiniteLaw.mixture (FiniteLaw.dirac (1 : Fin 3))
    (IndependentCounts.binomial 2 q hq0 hq1) z hz0 hz1

theorem activeLimitLaw_success (z q : ℝ) (hz0 : 0≤ z) (hz1 : z≤1)
    (hq0 : 0≤ q) (hq1 : q≤1) :
    (activeLimitLaw z q hz0 hz1 hq0 hq1).success=z+(1-z)*(2*q-q^2) := by
  unfold activeLimitLaw CountLaw.success
  rw [FiniteLaw.expect_mixture,FiniteLaw.expect_dirac]
  change z*1+(1-z)*(IndependentCounts.binomial 2 q hq0 hq1).success=_
  rw [IndependentCounts.binomial_success]
  ring

theorem activeLimitLaw_load (z q : ℝ) (hz0 : 0≤ z) (hz1 : z≤1)
    (hq0 : 0≤ q) (hq1 : q≤1) :
    (activeLimitLaw z q hz0 hz1 hq0 hq1).load=z+2*(1-z)*q := by
  unfold activeLimitLaw CountLaw.load
  rw [FiniteLaw.expect_mixture,FiniteLaw.expect_dirac]
  change z*((1:Fin 3).val:ℝ)+(1-z)*(IndependentCounts.binomial 2 q hq0 hq1).load=_
  rw [show ((1:Fin 3).val:ℝ)=1 by norm_num]
  rw [IndependentCounts.binomial_load]
  norm_num
  ring

theorem activeLimitLaw_duplicates (z q : ℝ) (hz0 : 0≤ z) (hz1 : z≤1)
    (hq0 : 0≤ q) (hq1 : q≤1) :
    (activeLimitLaw z q hz0 hz1 hq0 hq1).duplicates=(1-z)*q^2 := by
  unfold CountLaw.duplicates
  rw [activeLimitLaw_load,activeLimitLaw_success]
  ring

theorem two_count_success (P : CountLaw 2) : P.success=P.mass 1+P.mass 2 := by
  norm_num [CountLaw.success,FiniteLaw.expect,Fin.sum_univ_succ,successIndicator]

theorem two_count_load (P : CountLaw 2) : P.load=P.mass 1+2*P.mass 2 := by
  norm_num [CountLaw.load,FiniteLaw.expect,Fin.sum_univ_succ]
  ring

theorem two_count_zero_mass (P : CountLaw 2) : P.mass 0=1-P.success := by
  have ht := P.total
  norm_num [Fin.sum_univ_succ] at ht
  rw [two_count_success]
  linarith

theorem two_count_duplicate_mass (P : CountLaw 2) : P.duplicates=P.mass 2 := by
  unfold CountLaw.duplicates
  rw [two_count_load,two_count_success]
  ring

theorem two_count_one_mass (P : CountLaw 2) : P.mass 1=P.success-P.duplicates := by
  rw [two_count_success,two_count_duplicate_mass]
  ring

theorem count_zero_limit_of_success (P : ℕ→ CountLaw 2)
    (h : Tendsto (fun k=>(P k).success) atTop (𝓝 0)) :
    ∀ r,Tendsto (fun k=>(P k).mass r) atTop (𝓝 ((FiniteLaw.dirac (0:Fin 3)).mass r)) := by
  have h1 : Tendsto (fun k=>(P k).mass 1) atTop (𝓝 0) := by
    apply squeeze_zero (fun k=>(P k).nonneg 1) _ h
    intro k
    rw [two_count_success]
    linarith [(P k).nonneg 2]
  have h2 : Tendsto (fun k=>(P k).mass 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun k=>(P k).nonneg 2) _ h
    intro k
    rw [two_count_success]
    linarith [(P k).nonneg 1]
  intro r
  have hval : r.val=0 ∨ r.val=1 ∨ r.val=2 := by have h:=r.isLt; omega
  rcases hval with hr|hr|hr
  · rw [show r=0 from Fin.ext hr]
    rw [show (FiniteLaw.dirac (0:Fin 3)).mass 0=1 by simp [FiniteLaw.dirac]]
    simpa only [two_count_zero_mass,sub_zero] using
      (tendsto_const_nhds (x:=(1:ℝ))).sub h
  · rw [show r=1 from Fin.ext hr]
    simpa only [FiniteLaw.dirac,show (1:Fin 3)≠0 by decide,if_false] using h1
  · rw [show r=2 from Fin.ext hr]
    simpa only [FiniteLaw.dirac,show (2:Fin 3)≠0 by decide,if_false] using h2

theorem count_one_limit_of_success_duplicates (P : ℕ→ CountLaw 2)
    (hs : Tendsto (fun k=>(P k).success) atTop (𝓝 1))
    (hd : Tendsto (fun k=>(P k).duplicates) atTop (𝓝 0)) :
    ∀ r,Tendsto (fun k=>(P k).mass r) atTop (𝓝 ((FiniteLaw.dirac (1:Fin 3)).mass r)) := by
  intro r
  have hval : r.val=0 ∨ r.val=1 ∨ r.val=2 := by have h:=r.isLt; omega
  rcases hval with hr|hr|hr
  · rw [show r=0 from Fin.ext hr]
    rw [show (FiniteLaw.dirac (1:Fin 3)).mass 0=0 by simp [FiniteLaw.dirac]]
    simpa only [two_count_zero_mass,sub_self] using (tendsto_const_nhds (x:=(1:ℝ))).sub hs
  · rw [show r=1 from Fin.ext hr]
    rw [show (FiniteLaw.dirac (1:Fin 3)).mass 1=1 by simp [FiniteLaw.dirac]]
    simpa only [two_count_one_mass,sub_zero] using hs.sub hd
  · rw [show r=2 from Fin.ext hr]
    simpa only [two_count_duplicate_mass,FiniteLaw.dirac,show (2:Fin 3)≠1 by decide,
      if_false] using hd

theorem typeOutcome_expect_le_of_supported_actions {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (G : FiniteGame m 2 c Seed) (i : Fin m) (v B : ℝ)
    (f : Fin 3→ℝ) (h : ∀ᵐa ∂G.σ v,((problem G i).outcome a).expect f≤ B) :
    (typeOutcome G i v).expect f≤ B := by
  rw [typeOutcome_expect]
  have hi := FiniteLaw.integrable_expect (G.σ v) (problem G i).outcome
    (measurable_outcome_mass G i) f
  have hh := integral_mono_ae hi (integrable_const B) h
  simpa only [integral_const,probReal_univ,one_smul] using hh

theorem typeOutcome_expect_ge_of_supported_actions {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (G : FiniteGame m 2 c Seed) (i : Fin m) (v B : ℝ)
    (f : Fin 3→ℝ) (h : ∀ᵐa ∂G.σ v,B≤((problem G i).outcome a).expect f) :
    B≤(typeOutcome G i v).expect f := by
  rw [typeOutcome_expect]
  have hi := FiniteLaw.integrable_expect (G.σ v) (problem G i).outcome
    (measurable_outcome_mass G i) f
  have hh := integral_mono_ae (integrable_const B) hi h
  simpa only [integral_const,probReal_univ,one_smul] using hh

theorem conditional_low_limit_of_uniform_raw_bound {M C : ℕ→ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (G : ∀ k,FiniteGame (M k) 2 (C k) Seed) (v d : ℝ)
    (hσ : ∀ k,∀ᵐa ∂(G k).σ v,a.bid≤ d)
    (e : ℕ→ℝ) (he : Tendsto e atTop (𝓝 0))
    (hraw : ∀ᶠk in atTop,∀ i : Fin (M k),∀ a : JointAction 2,a.bid≤ d→
      ((problem (G k) i).outcome a).success≤ e k) :
    ∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>(typeOutcome (G k) (i k) v).mass r)
        atTop (𝓝 ((FiniteLaw.dirac (0:Fin 3)).mass r)) := by
  intro i
  apply count_zero_limit_of_success
  apply squeeze_zero' (Eventually.of_forall (fun k=>(typeOutcome (G k) (i k) v).success_nonneg)) _ he
  filter_upwards [hraw] with k hk
  apply typeOutcome_expect_le_of_supported_actions (G k) (i k) v (e k)
    (fun r=> successIndicator r.val)
  exact (hσ k).mono (fun a ha=> hk (i k) a ha)

theorem singleton_outcome_duplicates_zero {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (G : FiniteGame m 2 c Seed) (i : Fin m)
    (a : JointAction 2) (ha : a.routeCount=1) :
    ((problem G i).outcome a).duplicates=0 := by
  have h := load_le_routeCount_mul_success G i a
  rw [ha,Nat.cast_one,one_mul] at h
  unfold CountLaw.duplicates
  exact sub_eq_zero.mpr (le_antisymm h ((problem G i).outcome a).success_le_load)

theorem conditional_upper_limit_of_floor {M C : ℕ→ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (G : ∀ k,FiniteGame (M k) 2 (C k) Seed) (v R : ℝ)
    (hσ : ∀ k,∀ᵐa ∂(G k).σ v,R≤ a.bid ∧ a.routeCount=1)
    (q : ℕ→ℝ) (hq : Tendsto q atTop (𝓝 1))
    (hraw : ∀ k,∀ i : Fin (M k),∀ a : JointAction 2,R≤ a.bid→ a.routeCount=1→
      q k≤((problem (G k) i).outcome a).success) :
    ∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>(typeOutcome (G k) (i k) v).mass r)
        atTop (𝓝 ((FiniteLaw.dirac (1:Fin 3)).mass r)) := by
  intro i
  apply count_one_limit_of_success_duplicates
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le hq tendsto_const_nhds
    · intro k
      apply typeOutcome_expect_ge_of_supported_actions (G k) (i k) v (q k)
        (fun r=> successIndicator r.val)
      exact (hσ k).mono (fun a ha=> hraw k (i k) a ha.1 ha.2)
    · exact fun k=>(typeOutcome (G k) (i k) v).success_le_one
  · have hd : ∀ k,(typeOutcome (G k) (i k) v).duplicates=0 := by
      intro k
      rw [CountLaw.duplicates_eq_expect,typeOutcome_expect]
      have hz : (fun a : JointAction 2=>((problem (G k) (i k)).outcome a).expect
          (fun r=>(r.val:ℝ)-successIndicator r.val))=ᵐ[(G k).σ v]fun _=>0 := by
        filter_upwards [hσ k] with a ha
        rw [←CountLaw.duplicates_eq_expect,singleton_outcome_duplicates_zero (G k) (i k) a ha.2]
      rw [integral_congr_ae hz,integral_zero]
    simpa only [hd] using (tendsto_const_nhds (x:=(0:ℝ)))

theorem uniform_of_all_changing_identities {A : ℕ→ Type*}
    (hne : ∀ k,Nonempty (A k)) (f : ∀ k,A k→ℝ) (l : ℝ)
    (h : ∀ i : ∀ k,A k,Tendsto (fun k=> f k (i k)) atTop (𝓝 l)) :
    ∀ eps>0,∀ᶠk in atTop,∀ i : A k,|f k i-l|< eps := by
  classical
  intro eps heps
  let i : ∀ k,A k := fun k=>
    if hb : ∃j : A k,eps≤|f k j-l| then Classical.choose hb
    else Classical.choice (hne k)
  have hi : ∀ᶠk in atTop,|f k (i k)-l|< eps := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp (h i)) eps heps
  filter_upwards [hi] with k hk
  intro j
  by_contra hj
  have hb : ∃j : A k,eps≤|f k j-l| := ⟨j,le_of_not_gt hj⟩
  have hbad := Classical.choose_spec hb
  have heq : i k=Classical.choose hb := dif_pos hb
  rw [heq] at hk
  exact (not_lt_of_ge hbad) hk

theorem finite_average_tendsto_of_changing_identities {M : ℕ→ℕ}
    (hm : ∀ k,0< M k) (f : ∀ k,Fin (M k)→ℝ) (l : ℝ)
    (h : ∀ i : ∀ k,Fin (M k),Tendsto (fun k=> f k (i k)) atTop (𝓝 l)) :
    Tendsto (fun k=>(∑i,f k i)/(M k:ℝ)) atTop (𝓝 l) := by
  have hu := uniform_of_all_changing_identities
    (fun k=>⟨⟨0,hm k⟩⟩) f l h
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  filter_upwards [hu (eps/2) (half_pos heps)] with k hk
  have hMk : (0:ℝ)< M k := by exact_mod_cast hm k
  have hid : (∑i,f k i)/(M k:ℝ)-l=(∑i,(f k i-l))/(M k:ℝ) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp [hMk.ne']
  rw [Real.dist_eq,hid,abs_div,abs_of_pos hMk]
  have hb : |∑i : Fin (M k),(f k i-l)|≤(M k:ℝ)*(eps/2) := by
    calc
      _≤∑i : Fin (M k),|f k i-l| := Finset.abs_sum_le_sum_abs _ _
      _≤∑_i : Fin (M k),eps/2 := Finset.sum_le_sum (fun i _=>(hk i).le)
      _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hb' : |∑i : Fin (M k),(f k i-l)|/(M k:ℝ)≤ eps/2 :=
    (div_le_iff₀ hMk).2 (by simpa only [mul_comm] using hb)
  exact hb'.trans_lt (by linarith)

theorem conditional_average_mass_tendsto {M C : ℕ→ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (G : ∀ k,FiniteGame (M k) 2 (C k) Seed) (hm : ∀ k,0< M k)
    (v : ℝ) (L : CountLaw 2)
    (h : ∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>(typeOutcome (G k) (i k) v).mass r) atTop (𝓝 (L.mass r))) :
    ∀ r,Tendsto (fun k=>(conditionalTypeCountLaw (G k) (hm k) v).mass r)
      atTop (𝓝 (L.mass r)) := by
  intro r
  exact finite_average_tendsto_of_changing_identities hm
    (fun k i=>(typeOutcome (G k) i v).mass r) (L.mass r) (fun i=> h i r)

theorem finiteLaw_expect_tendsto {Ω : Type*} [Fintype Ω]
    (P : ℕ→ FiniteLaw Ω) (L : FiniteLaw Ω)
    (h : ∀ r,Tendsto (fun k=>(P k).mass r) atTop (𝓝 (L.mass r))) (f : Ω→ℝ) :
    Tendsto (fun k=>(P k).expect f) atTop (𝓝 (L.expect f)) := by
  unfold FiniteLaw.expect
  exact tendsto_finsetSum _ (fun r _=>(h r).mul_const (f r))

theorem original_conditional_expect_integral_limit {M C : ℕ→ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (G : ∀ k,FiniteGame (M k) 2 (C k) Seed) (hm : ∀ k,0< M k)
    (F : Measure ℝ) [IsFiniteMeasure F] (L : ℝ→ CountLaw 2)
    (h : ∀ᵐv ∂F,∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>(typeOutcome (G k) (i k) v).mass r) atTop (𝓝 ((L v).mass r)))
    (f : Fin 3→ℝ) :
    Tendsto (fun k=>∫v,(conditionalTypeCountLaw (G k) (hm k) v).expect f ∂F)
      atTop (𝓝 (∫v,(L v).expect f ∂F)) := by
  have hmeas (k : ℕ) : AEStronglyMeasurable
      (fun v=>(conditionalTypeCountLaw (G k) (hm k) v).expect f) F :=
    (measurable_conditionalTypeCountLaw_expect (G k) (hm k) f).aestronglyMeasurable
  have hb (k : ℕ) : ∀ᵐv ∂F,
      ‖(conditionalTypeCountLaw (G k) (hm k) v).expect f‖≤∑r,‖f r‖ :=
    ae_of_all _ (fun v=>(conditionalTypeCountLaw (G k) (hm k) v).norm_expect_le_sum_norm f)
  have hv : ∀ᵐv ∂F,Tendsto
      (fun k=>(conditionalTypeCountLaw (G k) (hm k) v).expect f)
      atTop (𝓝 ((L v).expect f)) := by
    filter_upwards [h] with v hv
    exact finiteLaw_expect_tendsto _ _ (conditional_average_mass_tendsto G hm v (L v) hv) f
  exact tendsto_integral_of_dominated_convergence (fun _ : ℝ=>∑r,‖f r‖)
    hmeas (integrable_const _) hb hv

theorem actual_aggregate_limits {M C : ℕ→ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (G : ∀ k,FiniteGame (M k) 2 (C k) Seed) (hm : ∀ k,0< M k)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ k,(G k).F=F)
    (L : ℝ→ CountLaw 2)
    (h : ∀ᵐv ∂F,∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>(typeOutcome (G k) (i k) v).mass r) atTop (𝓝 ((L v).mass r))) :
    Tendsto (fun k=> finiteCoverage (G k)) atTop (𝓝 (∫v,(L v).success ∂F)) ∧
    Tendsto (fun k=> finiteLoad (G k)) atTop (𝓝 (∫v,(L v).load ∂F)) ∧
    Tendsto (fun k=> finiteLoad (G k)-finiteCoverage (G k))
      atTop (𝓝 (∫v,(L v).duplicates ∂F)) := by
  have hs := original_conditional_expect_integral_limit G hm F L h
    (fun r=> successIndicator r.val)
  have hl := original_conditional_expect_integral_limit G hm F L h
    (fun r=>(r.val:ℝ))
  have hd := original_conditional_expect_integral_limit G hm F L h
    (fun r=>(r.val:ℝ)-successIndicator r.val)
  constructor
  · convert! hs using 1
    ext k
    rw [←hF k]
    exact (integral_conditionalTypeCountLaw_success (G k) (hm k)).symm
  constructor
  · convert! hl using 1
    ext k
    rw [←hF k]
    exact (integral_conditionalTypeCountLaw_load (G k) (hm k)).symm
  · have hd' : Tendsto
        (fun k=>∫v,(conditionalTypeCountLaw (G k) (hm k) v).duplicates ∂F)
        atTop (𝓝 (∫v,(L v).duplicates ∂F)) := by
      simpa only [←CountLaw.duplicates_eq_expect] using hd
    convert! hd' using 1
    ext k
    rw [←hF k,integral_conditionalTypeCountLaw_duplicates]

theorem actual_multiplicity_limit {M C : ℕ→ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (G : ∀ k,FiniteGame (M k) 2 (C k) Seed) {rho Q : ℝ}
    (hQ : 0< Q)
    (hload : Tendsto (fun k=> finiteLoad (G k)) atTop (𝓝 (2*rho)))
    (hcover : Tendsto (fun k=> finiteCoverage (G k)) atTop (𝓝 Q)) :
    Tendsto (fun k=> finiteLoad (G k)/finiteCoverage (G k))
      atTop (𝓝 (2*rho/Q)) :=
  hload.div hcover hQ.ne'

end FCAppendix.Affine.Hybrid.Native02
