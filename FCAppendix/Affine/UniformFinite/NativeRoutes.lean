import FCAppendix.Affine.UniformFinite.NativeRestrictedIC
import FCAppendix.Affine.UniformFinite.LocalInformation
import FCAppendix.Finite.SingletonDeviation

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Uniform05
open scoped BigOperators

namespace NativeRoutes
variable {M c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem zero_route_payoff (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (v : ℝ) (act : JointAction 2) (hroute : act.routeCount=0) :
    (problem Γ a).payoff v act=0 := by
  change ((problem Γ a).outcome act).utility v act.bid Γ.g Γ.A Γ.G=0
  rw [problem_outcome,CountLaw.utility,CountLaw.expect_ofMeasure]
  have hzero (ω : Sample M 2 Seed) : (focalCount Γ a act ω).val=0 := by
    have h:=focalCount_le Γ a act ω
    omega
  simp_rw [hzero,userPayoff_zero v act.bid Γ.g Γ.A.charge Γ.G.charge Γ.A.zero Γ.G.zero]
  simp

def namedCount (Γ : FiniteGame M 2 c Seed) (a : Fin M) (b : ℝ) (j : Fin 2)
    (ω : Background M 2 Seed) : Fin 3 := if Accepts Γ a b j ω then 1 else 0

lemma measurable_namedCount (Γ : FiniteGame M 2 c Seed) (a : Fin M) (b : ℝ)
    (j : Fin 2) : Measurable (namedCount Γ a b j) :=
  Measurable.ite (measurableSet_accepts Γ a b j) measurable_const measurable_const

def namedOutcome (Γ : FiniteGame M 2 c Seed) (a : Fin M) (b : ℝ) (j : Fin 2) : CountLaw 2 :=
  CountLaw.ofMeasure (backgroundLaw Γ) (namedCount Γ a b j)
    (measurable_namedCount Γ a b j)

lemma namedOutcome_expect (Γ : FiniteGame M 2 c Seed) (a : Fin M) (b : ℝ)
    (j : Fin 2) (f : Fin 3→ℝ) :
    (namedOutcome Γ a b j).expect f=
      ∫ω,f (namedCount Γ a b j ω)∂backgroundLaw Γ :=
  CountLaw.expect_ofMeasure _ _ _ _

theorem namedCount_is_actual (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (b : ℝ) (hb : 0≤ b) (j : Fin 2) (ω : Background M 2 Seed) :
    (namedCount Γ a b j ω).val=
      inclusionCount (deviate (drawsRealization ω.1) a b hb {j}) Γ.policy ω.2 a := by
  have ho : observe (deviate (drawsRealization ω.1) a b hb {j}) j=
      presentList ω a b j := by
    funext l
    by_cases hl : l=a
    · subst l
      simp [observe,deviate,presentList]
    · simp [observe,deviate,presentList,hl]
  have hmem : (a∈allocation (deviate (drawsRealization ω.1) a b hb {j}) Γ.policy ω.2 j)
      ↔Accepts Γ a b j ω := by
    change a∈(Γ.policy j (observe (deviate (drawsRealization ω.1) a b hb {j}) j) (ω.2 j)).val↔_
    rw [ho]
  rw [inclusionCount_eq_sum,Fin.sum_univ_two]
  fin_cases j
  · change (a∈allocation (deviate (drawsRealization ω.1) a b hb {0}) Γ.policy ω.2 0)↔
      Accepts Γ a b 0 ω at hmem
    have hnone:=LocalInformation.intervention_nonrecipient_rejects
      (drawsRealization ω.1) a b hb Γ.policy ω.2 {0} 1 (by simp)
    by_cases hA : Accepts Γ a b 0 ω <;> simp [namedCount,hnone,hmem,hA]
  · change (a∈allocation (deviate (drawsRealization ω.1) a b hb {1}) Γ.policy ω.2 1)↔
      Accepts Γ a b 1 ω at hmem
    have hnone:=LocalInformation.intervention_nonrecipient_rejects
      (drawsRealization ω.1) a b hb Γ.policy ω.2 {1} 0 (by simp)
    by_cases hA : Accepts Γ a b 1 ω <;> simp [namedCount,hnone,hmem,hA]

theorem namedOutcome_success (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (b : ℝ) (j : Fin 2) : (namedOutcome Γ a b j).success=acceptProb Γ a b j := by
  rw [CountLaw.success,namedOutcome_expect]
  have he : (fun ω : Background M 2 Seed=> successIndicator (namedCount Γ a b j ω).val)=
      Set.indicator {ω | Accepts Γ a b j ω} (fun _=>1) := by
    funext ω
    by_cases h : Accepts Γ a b j ω <;> simp [namedCount,successIndicator,h,Set.indicator]
  rw [he,integral_indicator_const (μ:=backgroundLaw Γ) 1 (measurableSet_accepts Γ a b j)]
  simp only [smul_eq_mul,mul_one,acceptProb]

theorem namedOutcome_duplicate (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (b : ℝ) (j : Fin 2) : (namedOutcome Γ a b j).duplicates=0 := by
  rw [CountLaw.duplicates_eq_expect,namedOutcome_expect]
  have he (ω : Background M 2 Seed) :
      ((namedCount Γ a b j ω).val:ℝ)-successIndicator (namedCount Γ a b j ω).val=0 := by
    by_cases h : Accepts Γ a b j ω <;> simp [namedCount,successIndicator,h]
  simp_rw [he]
  simp

theorem namedOutcome_utility (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (v b : ℝ) (j : Fin 2) :
    (namedOutcome Γ a b j).utility v b Γ.g Γ.A Γ.G=
      (v-Γ.g-b)*acceptProb Γ a b j := by
  rw [CountLaw.utility,namedOutcome_expect]
  have he (ω : Background M 2 Seed) :
      userPayoff v b Γ.g Γ.A.charge Γ.G.charge (namedCount Γ a b j ω).val=
      (v-Γ.g-b)*successIndicator (namedCount Γ a b j ω).val := by
    by_cases h : Accepts Γ a b j ω <;>
      simp [namedCount,h,userPayoff,successIndicator,Γ.A.zero,Γ.G.zero,
        Γ.A.one (by norm_num),Γ.G.one (by norm_num)]; ring
  simp_rw [he]
  rw [integral_const_mul]
  have hs:=namedOutcome_success Γ a b j
  rw [CountLaw.success,namedOutcome_expect] at hs
  exact congrArg (fun x=>(v-Γ.g-b)*x) hs

theorem singleton_payoff_eq_broadcast_load (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (v : ℝ) (single full : JointAction 2) (hs : single.routeCount=1)
    (hf : full.routeCount=2) (hb : single.bid=full.bid) :
    (problem Γ a).payoff v single=
      (v-Γ.g-full.bid)*((problem Γ a).outcome full).load/2 := by
  rw [singleton_payoff Γ (by norm_num) a single hs v,load_eq_mean Γ (by norm_num) a full,hf,hb]
  norm_num; ring

theorem singleton_payoff_eq_broadcast_counts (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (v : ℝ) (single full : JointAction 2) (hs : single.routeCount=1)
    (hf : full.routeCount=2) (hb : single.bid=full.bid) :
    (problem Γ a).payoff v single=(v-Γ.g-full.bid)*
      (((problem Γ a).outcome full).success+((problem Γ a).outcome full).duplicates)/2 := by
  rw [singleton_payoff_eq_broadcast_load Γ a v single full hs hf hb]
  simp only [CountLaw.duplicates]
  ring

theorem singleton_outcome_expect (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (single : JointAction 2) (hs : single.routeCount=1) (f : Fin 3→ℝ) :
    ((problem Γ a).outcome single).expect f=
      ((namedOutcome Γ a single.bid 0).expect f+
        (namedOutcome Γ a single.bid 1).expect f)/2 := by
  let μ:=(problem Γ a).outcome single
  have hK (ω : Sample M 2 Seed) : (focalCount Γ a single ω).val≤1 := by
    simpa only [hs] using focalCount_le Γ a single ω
  have he (r : Fin 3) (hr : r.val≤1) :
      f r=f 0+(f 1-f 0)*successIndicator r.val := by
    fin_cases r <;> simp_all [successIndicator]
  have hfull : μ.expect f=f 0+(f 1-f 0)*μ.success := by
    rw [show μ=(problem Γ a).outcome single from rfl,problem_outcome,CountLaw.expect_ofMeasure,
      CountLaw.success,CountLaw.expect_ofMeasure]
    simp_rw [he _ (hK _)]
    rw [integral_add (integrable_const _) ((CountLaw.integrable_comp _ _
      (measurable_focalCount Γ a single) (fun r=> successIndicator r.val)).const_mul _),
      integral_const_mul,integral_const,probReal_univ,smul_eq_mul,one_mul]
  have hn (j : Fin 2) : (namedOutcome Γ a single.bid j).expect f=
      f 0+(f 1-f 0)*acceptProb Γ a single.bid j := by
    rw [namedOutcome_expect]
    have hnval (ω : Background M 2 Seed) : (namedCount Γ a single.bid j ω).val≤1 := by
      by_cases h : Accepts Γ a single.bid j ω <;> simp [namedCount,h]
    simp_rw [he _ (hnval _)]
    have hi:=CountLaw.integrable_comp (backgroundLaw Γ) (namedCount Γ a single.bid j)
      (measurable_namedCount Γ a single.bid j) (fun r=> successIndicator r.val)
    rw [integral_add (integrable_const _) (hi.const_mul _),integral_const_mul,
      integral_const,probReal_univ,smul_eq_mul,one_mul]
    have hs:=namedOutcome_success Γ a single.bid j
    rw [CountLaw.success,namedOutcome_expect] at hs
    exact congrArg (fun x=>f 0+(f 1-f 0)*x) hs
  have hload:=load_le_routeCount_mul_success Γ a single
  have hls : μ.load=μ.success := by
    apply le_antisymm
    · simpa only [hs,Nat.cast_one,one_mul] using hload
    · exact μ.success_le_load
  have hmean : μ.success=meanAcceptProb Γ a single.bid := by
    rw [← hls,show μ=(problem Γ a).outcome single from rfl,
      load_eq_mean Γ (by norm_num) a single,hs,Nat.cast_one,one_mul]
  rw [hfull,hn 0,hn 1,hmean,meanAcceptProb,Fin.sum_univ_two]
  norm_num; ring

theorem named_success_le_broadcast_success (Γ : FiniteGame M 2 c Seed) (a : Fin M)
    (full : JointAction 2) (hf : full.routeCount=2) (j : Fin 2) :
    acceptProb Γ a full.bid j≤((problem Γ a).outcome full).success := by
  let f : Sample M 2 Seed→ℝ:=fun ω=> if Accepts Γ a full.bid j ω.1 then 1 else 0
  have hi : Integrable f (sampleLaw Γ) := by
    apply Integrable.of_bound (C:=1)
    · exact (Measurable.ite (measurable_fst (measurableSet_accepts Γ a full.bid j))
        measurable_const measurable_const).aestronglyMeasurable
    · apply ae_of_all
      intro ω
      dsimp only [f]
      split_ifs <;> norm_num
  have hint : (∫ω,f ω∂sampleLaw Γ)=acceptProb Γ a full.bid j := by
    change (∫ω : Sample M 2 Seed,
      (if Accepts Γ a full.bid j ω.1 then (1:ℝ) else 0)
      ∂(backgroundLaw Γ).prod (permLaw 2))=acceptProb Γ a full.bid j
    have hfst:=integral_fun_fst (μ:=backgroundLaw Γ) (ν:=permLaw 2)
      (fun ω : Background M 2 Seed=> if Accepts Γ a full.bid j ω then (1:ℝ) else 0)
    simp only [probReal_univ,one_smul] at hfst
    calc
      _=(∫ω : Background M 2 Seed,
        (if Accepts Γ a full.bid j ω then (1:ℝ) else 0)∂backgroundLaw Γ) := by
        convert! hfst using 1
      _=acceptProb Γ a full.bid j := by
        have he : (fun ω : Background M 2 Seed=> if Accepts Γ a full.bid j ω then (1:ℝ) else 0)=
            Set.indicator {ω | Accepts Γ a full.bid j ω} (fun _=>1) := by
          funext ω
          simp only [Set.indicator,Set.mem_setOf_eq]
        rw [he,integral_indicator_const (μ:=backgroundLaw Γ) 1
          (measurableSet_accepts Γ a full.bid j)]
        simp only [smul_eq_mul,mul_one,acceptProb]
  rw [← hint,problem_outcome,CountLaw.success,CountLaw.expect_ofMeasure]
  apply integral_mono hi (CountLaw.integrable_comp _ _ (measurable_focalCount Γ a full)
    (fun r=> successIndicator r.val))
  intro ω
  by_cases h : Accepts Γ a full.bid j ω.1
  · have hm : a∈allocation (deviated a full ω) Γ.policy ω.1.2 j :=
      (mem_allocation_deviated_iff Γ a full ω j).mpr ⟨by rw [hf,Hybrid.firstK_full_two];simp,h⟩
    have hk : 0<(focalCount Γ a full ω).val := by
      change 0<(accepted (deviated a full ω) Γ.policy ω.1.2 a).card
      exact Finset.card_pos.mpr ⟨j,by simpa only [accepted,Finset.mem_filter,
        Finset.mem_univ,true_and] using hm⟩
    simp [f,h,successIndicator,Nat.ne_of_gt hk]
  · simp only [f,if_neg h]
    exact successIndicator_nonneg _

theorem named_payoff_le_broadcast_success (Γ : FiniteGame M 2 c Seed) (hg : Γ.g=0)
    (a : Fin M) (v T : ℝ) (hv : v≤ T) (hT : 0≤ T)
    (full : JointAction 2) (hf : full.routeCount=2) (j : Fin 2) :
    (namedOutcome Γ a full.bid j).utility v full.bid Γ.g Γ.A Γ.G≤
      T*((problem Γ a).outcome full).success := by
  have hu:=(namedOutcome Γ a full.bid j).utility_le_net_success v full.bid Γ.g Γ.A Γ.G
    full.bid_nonneg Γ.g_nonneg
  rw [hg,sub_zero,namedOutcome_success] at hu
  have hn : 0≤ acceptProb Γ a full.bid j := measureReal_nonneg
  rw [hg]
  exact hu.trans ((mul_le_mul_of_nonneg_right hv hn).trans
    (mul_le_mul_of_nonneg_left (named_success_le_broadcast_success Γ a full hf j) hT))

theorem singleton_payoff_le_broadcast_success (Γ : FiniteGame M 2 c Seed) (hg : Γ.g=0)
    (a : Fin M) (v T : ℝ) (hv : v≤ T) (hT : 0≤ T)
    (single full : JointAction 2) (hs : single.routeCount=1)
    (hf : full.routeCount=2) (hb : single.bid=full.bid) :
    (problem Γ a).payoff v single≤ T*((problem Γ a).outcome full).success := by
  rw [singleton_payoff Γ (by norm_num) a single hs v,hg,sub_zero,hb]
  have hn : 0≤ meanAcceptProb Γ a full.bid := by
    unfold meanAcceptProb acceptProb
    positivity
  have hvb : v-full.bid≤ T:=sub_le_self v full.bid_nonneg |>.trans hv
  exact (mul_le_mul_of_nonneg_right hvb hn).trans
    (mul_le_mul_of_nonneg_left (meanAcceptProb_le_success Γ (by norm_num) a full (by omega)) hT)

end NativeRoutes

namespace NativeIndexed
variable {M : ℕ} [NeZero M]

lemma value_difference (i : Row) (G : RestrictedLaw i) (a : Fin M)
    (v w : ℝ) (own : Bid i) :
    utility i G a v own-utility i G a w own=
      (v-w)*(NativeProfile.indexedLaw i G a own).success := by
  simp only [utility,CountLaw.utility_eq]
  ring

theorem success_positive_eq_raw (i : Row) (N : ℕ) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (a : Fin (N+1)) (own : Bid i) (hown : 0<(own:ℝ)) :
    (NativeProfile.indexedLaw i G a own).success=rawSuccess i N G own := by
  have h:=value_difference i G a 1 0 own
  rw [utility_positive_eq_raw i N G a 1 own hown,
    utility_positive_eq_raw i N G a 0 own hown,raw_value_difference] at h
  simpa only [sub_zero,one_mul] using h.symm

theorem zero_le_of_positive_source_bound (i : Row) (N : ℕ) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (a : Fin (N+1)) (v : Value i) (C D : ℝ) (hD : 0< D)
    (hbound : ∀b : Bid i,0<(b:ℝ)→(b:ℝ)< D→ rawUtility i N G v b≤ C) :
    utility i G a v (Noisy.zeroBid i)≤ C := by
  let q : ℕ→ unitInterval:=noiseSchedule 1
  let b : ℕ→ Bid i:=fun n=>⟨cap i*(q n:ℝ),
    mul_nonneg (cap_pos i).le (q n).property.1,
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left (q n).property.2 (cap_pos i).le⟩
  have hb (n : ℕ) : 0<(b n:ℝ) :=
    mul_pos (cap_pos i) (noiseSchedule_pos 1 (by norm_num) n)
  have ht : Tendsto (fun n=>(b n:ℝ)) atTop (𝓝 0) := by
    have hq : Tendsto (fun n=>(q n:ℝ)) atTop (𝓝 0) :=
      continuous_subtype_val.continuousAt.tendsto.comp (noiseSchedule_tendsto_zero 1)
    simpa only [mul_zero] using hq.const_mul (cap i)
  apply le_of_forall_pos_le_add
  intro err herr
  obtain ⟨r,hr,h⟩:=zero_right_bound (M:=N+1) i herr
  have he : ∀ᶠn in atTop,utility i G a v (Noisy.zeroBid i)≤ C+(1+eta i)*(b n:ℝ)+err := by
    filter_upwards [ht.eventually (Iio_mem_nhds hD),ht.eventually (Iio_mem_nhds hr)] with n hn hrn
    have hpos:=hbound (b n) (hb n) hn
    have hz:=h G inferInstance a v (b n) (hb n) hrn
    rw [utility_positive_eq_raw i N G a v (b n) (hb n)] at hz
    linarith
  have hlim : Tendsto (fun n=> C+(1+eta i)*(b n:ℝ)+err) atTop (𝓝 (C+err)) := by
    simpa only [mul_zero,add_zero] using
      (tendsto_const_nhds.add (ht.const_mul (1+eta i))).add_const err
  exact ge_of_tendsto hlim he

@[simp] lemma utility_zero_bid (i : Row) (G : RestrictedLaw i) (a : Fin M) (v : ℝ) :
    utility i G a v (Noisy.zeroBid i)=v*(NativeProfile.indexedLaw i G a (Noisy.zeroBid i)).success := by
  simp only [utility,CountLaw.utility_eq,show ((Noisy.zeroBid i):ℝ)=0 by rfl,zero_mul,sub_zero]

end NativeIndexed
end FCAppendix.Affine.UniformFinite
