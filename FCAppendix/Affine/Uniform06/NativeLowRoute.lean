import FCAppendix.Finite.SingletonDeviation
import FCAppendix.Affine.Uniform06.LowRoute
import FCAppendix.Affine.Uniform06.SourceRankRates

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.NativeLowRoute

open MeasureTheory ProbabilityTheory Set Game Bayes
open FCAppendix.Affine.Uniform07
open scoped BigOperators

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def arrival (j : Fin 2) : Set (UserDraw 2) :=
  {d | j ∈ firstK d.2 d.1.2.routeCount}

theorem measurableSet_arrival (j : Fin 2) : MeasurableSet (arrival j) := by
  simpa [arrival] using (measurableSet_reach j (B := (univ : Set ℝ)) MeasurableSet.univ)

theorem arrival_probability (Γ : FiniteGame m 2 c Seed) (j : Fin 2) :
    (userLaw Γ).real (arrival j)=
      (∫ p : ℝ × JointAction 2, (p.2.routeCount:ℝ) ∂Γ.F ⊗ₘ Γ.σ)/2 := by
  classical
  let f : UserDraw 2 → ℝ := fun d => if d ∈ arrival j then 1 else 0
  have hf : Measurable f := measurable_const.piecewise (measurableSet_arrival j) measurable_const
  have hi : Integrable f (userLaw Γ) := Integrable.of_bound hf.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun d => by unfold f; split_ifs <;> norm_num)
  have heq := integral_indicator_const (μ := userLaw Γ) (1:ℝ) (measurableSet_arrival j)
  simp only [smul_eq_mul,mul_one] at heq
  rw [← heq]
  change (∫ d, f d ∂userLaw Γ)=_
  rw [userLaw,integral_prod _ hi]
  have he (p : ℝ × JointAction 2) :
      (∫ τ : Equiv.Perm (Fin 2), f (p,τ) ∂permLaw 2)=(p.2.routeCount:ℝ)/2 := by
    have hp := permLaw_mem_firstK 2 p.2.routeCount (by norm_num) p.2.routeCount_le j
    norm_num only [Nat.cast_ofNat] at hp
    rw [← hp, ← integral_indicator_one (MeasurableSet.of_discrete)]
    rfl
  simp_rw [he]
  rw [integral_div]

theorem source_arrival_probability (i : Row) (Γ : FiniteGame m 2 c Seed)
    (hroutes : ∀ᵐ p ∂Γ.F ⊗ₘ Γ.σ, 1 ≤ p.2.routeCount)
    (hlower : (Γ.F ⊗ₘ Γ.σ).real {p | p.2.routeCount=2}=cutoff i)
    (j : Fin 2) : (userLaw Γ).real (arrival j)=(1+cutoff i)/2 := by
  let E : Set (ℝ × JointAction 2) := {p | p.2.routeCount=2}
  have hE : MeasurableSet E := measurableSet_eq_fun
    ((measurable_routeCount 2).comp measurable_snd) measurable_const
  have hcount : (∫ p : ℝ × JointAction 2, (p.2.routeCount:ℝ) ∂Γ.F ⊗ₘ Γ.σ)=
      ∫ p, 1+E.indicator (fun _ => (1:ℝ)) p ∂Γ.F ⊗ₘ Γ.σ := by
    apply integral_congr_ae
    filter_upwards [hroutes] with p hp
    have htop := p.2.routeCount_le
    by_cases h2 : p.2.routeCount=2
    · norm_num [E,h2]
    · have h1 : p.2.routeCount=1 := by omega
      simp [E,h1]
  rw [arrival_probability Γ j,hcount,integral_add (integrable_const _)
    ((integrable_const (1:ℝ)).indicator hE),integral_const,integral_indicator_const 1 hE]
  simp only [probReal_univ,smul_eq_mul,mul_one]
  change (1+(Γ.F ⊗ₘ Γ.σ).real E)/2=(1+cutoff i)/2
  rw [hlower]

theorem half_receipt_lower (A : Schedule 2) :
    ∀ r : ℕ, 0 < r → r ≤ 2 → (1/2:ℝ)*(r:ℝ) ≤ A.charge r := by
  intro r hr hr2
  have hl := A.lower r hr hr2
  have hR : (r:ℝ) ≤ 2 := by exact_mod_cast hr2
  linarith

theorem acceptProb_ge_arrival_rank (Γ : FiniteGame m 2 c Seed)
    (hpolicy : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (focal : Fin m) (j : Fin 2) {b : ℝ} (hb : 0 < b) :
    binomBelow (m-1) ((userLaw Γ).real (arrival j)) c ≤ acceptProb Γ focal b j := by
  have hr := ae_receipt_rank_bounds Γ j (hpolicy j) focal (1/2) (by norm_num)
    (half_receipt_lower Γ.A) b hb
  have hinclusion : {ω : Background m 2 Seed | rivals focal (arrival j) ω< c}
      ≤ᵐ[backgroundLaw Γ] {ω | Accepts Γ focal b j ω} := by
    filter_upwards [hr] with ω hω hcount
    apply hω.1
    have hle : rivals focal (atLeastAt j ((1/2)*b)) ω ≤ rivals focal (arrival j) ω := by
      classical
      rw [rivals_eq_card,rivals_eq_card]
      apply Finset.card_le_card
      intro k hk
      obtain ⟨hk,hreach⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨hk,hreach.1⟩
    exact hle.trans_lt hcount
  rw [← prob_rivals_lt Γ focal (arrival j) (measurableSet_arrival j) c,acceptProb]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hinclusion)

theorem source_meanAccept_ge_Lm (i : Row) (Γ : FiniteGame m 2 (capacity m) Seed)
    (hpolicy : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hroutes : ∀ᵐ p ∂Γ.F ⊗ₘ Γ.σ, 1 ≤ p.2.routeCount)
    (hlower : (Γ.F ⊗ₘ Γ.σ).real {p | p.2.routeCount=2}=cutoff i)
    (focal : Fin m) {b : ℝ} (hb : 0 < b) :
    SourceRankRates.Lm i m ≤ meanAcceptProb Γ focal b := by
  have h (j : Fin 2) := acceptProb_ge_arrival_rank Γ hpolicy focal j hb
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 2)))
    (fun j _ => by simpa only [source_arrival_probability i Γ hroutes hlower j] using h j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  unfold meanAcceptProb
  norm_num only [Nat.cast_ofNat]
  change binomBelow (m-1) ((1+cutoff i)/2) (capacity m) ≤ _
  linarith

def oneAction (b : ℝ) : JointAction 2 := ⟨max b 0,le_max_right _ _,1,by norm_num⟩
def twoAction (b : ℝ) : JointAction 2 := ⟨max b 0,le_max_right _ _,2,le_rfl⟩
def oneUtility (Γ : FiniteGame m 2 c Seed) (focal : Fin m) (v b : ℝ) : ℝ :=
  (problem Γ focal).payoff v (oneAction b)
def twoUtility (Γ : FiniteGame m 2 c Seed) (focal : Fin m) (v b : ℝ) : ℝ :=
  (problem Γ focal).payoff v (twoAction b)
def duplicates (Γ : FiniteGame m 2 c Seed) (focal : Fin m) (b : ℝ) : ℝ :=
  ((problem Γ focal).outcome (twoAction b)).duplicates

theorem oneUtility_eq (Γ : FiniteGame m 2 c Seed) (focal : Fin m)
    (hg : Γ.g=0) (v : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    oneUtility Γ focal v b=(v-b)*meanAcceptProb Γ focal b := by
  simpa [oneUtility,oneAction,hg,max_eq_left hb] using
    singleton_payoff Γ (by norm_num) focal (oneAction b) rfl v

theorem source_half_bid_benchmark (i : Row) (Γ : FiniteGame m 2 (capacity m) Seed)
    (hpolicy : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hroutes : ∀ᵐ p ∂Γ.F ⊗ₘ Γ.σ, 1 ≤ p.2.routeCount)
    (hlower : (Γ.F ⊗ₘ Γ.σ).real {p | p.2.routeCount=2}=cutoff i)
    (hg : Γ.g=0) (focal : Fin m) {v : ℝ} (hv : 0 < v) :
    v*SourceRankRates.Lm i m/2 ≤ oneUtility Γ focal v (v/2) := by
  rw [oneUtility_eq Γ focal hg v (by positivity)]
  have hq := source_meanAccept_ge_Lm i Γ hpolicy hroutes hlower focal (half_pos hv)
  have hh := mul_le_mul_of_nonneg_left hq (half_pos hv).le
  nlinarith

theorem exact_two_minus_one (Γ : FiniteGame m 2 c Seed) (focal : Fin m)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1) (hg : Γ.g=0)
    (v : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    twoUtility Γ focal v b-oneUtility Γ focal v b=
      oneUtility Γ focal v b-((v-b)+η*b)*duplicates Γ focal b := by
  let P := (problem Γ focal).outcome (twoAction b)
  have hload : P.load=2*meanAcceptProb Γ focal b := by
    simpa [P,twoAction,max_eq_left hb] using load_eq_mean Γ (by norm_num) focal (twoAction b)
  have hsum : P.success+P.duplicates=2*meanAcceptProb Γ focal b := by
    unfold CountLaw.duplicates
    linarith
  have htwo : twoUtility Γ focal v b=(v-b)*P.success-η*b*P.duplicates := by
    change P.utility v (twoAction b).bid Γ.g Γ.A Γ.G=_
    rw [CountLaw.utility_eq,hA,CountLaw.charge_affine,hg]
    simp only [twoAction,max_eq_left hb,zero_mul,sub_zero]
    ring
  rw [htwo,oneUtility_eq Γ focal hg v hb]
  change _=(v-b)*meanAcceptProb Γ focal b-((v-b)+η*b)*P.duplicates
  nlinarith [congrArg (fun x : ℝ => (v-b)*x) hsum]

theorem meanAccept_nonnegative (Γ : FiniteGame m 2 c Seed) (focal : Fin m) (b : ℝ) :
    0 ≤ meanAcceptProb Γ focal b := by
  unfold meanAcceptProb acceptProb
  positivity

theorem source_tiny_value_improving_broadcast (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (Γ : FiniteGame m 2 (capacity m) Seed)
    (hpolicy : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hroutes : ∀ᵐ p ∂Γ.F ⊗ₘ Γ.σ, 1 ≤ p.2.routeCount)
    (hlower : (Γ.F ⊗ₘ Γ.σ).real {p | p.2.routeCount=2}=cutoff i)
    (hA : Γ.A=Schedule.affine 2 (eta i) (eta_pos i).le
      (by cases i <;> norm_num [eta,etaQ])) (hg : Γ.g=0)
    (focal : Fin m) {v : ℝ} (hv : 0 < v) (hvlow : v ≤ (501/1000)*cutoff i)
    (hq : ContinuousOn (meanAcceptProb Γ focal) (Icc (0:ℝ) v))
    (hdup : ∀ b ∈ Icc (0:ℝ) ((501/1000)*cutoff i),
      duplicates Γ focal b < SourceRankRates.Lm i m/2) :
    ∃ bStar ∈ Ico (0:ℝ) v, 0 < twoUtility Γ focal v bStar ∧
      ∀ b ≥ 0, oneUtility Γ focal v b < twoUtility Γ focal v bStar := by
  let L := SourceRankRates.Lm i m
  have hL : 0 < L := Bayes.binomBelow_pos (m-1) (capacity m)
    (PhysicalRates.capacity_positive (by omega)) _ (SourceRankRates.source_rank_parameter i)
  have hc : ContinuousOn (fun b => (v-b)*meanAcceptProb Γ focal b) (Icc (0:ℝ) v) :=
    (continuousOn_const.sub continuousOn_id).mul hq
  obtain ⟨bStar,hb,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) v).Nonempty from ⟨0,le_rfl,hv.le⟩) hc
  have hbase := source_half_bid_benchmark i Γ hpolicy hroutes hlower hg focal hv
  have hmaxhalf := hmax (show v/2 ∈ Icc (0:ℝ) v by constructor <;> linarith)
  rw [oneUtility_eq Γ focal hg v (by positivity)] at hbase
  have hlowerStar : v*L/2 ≤ oneUtility Γ focal v bStar := by
    rw [oneUtility_eq Γ focal hg v hb.1]
    exact hbase.trans hmaxhalf
  have hpositive : 0 < oneUtility Γ focal v bStar := (show 0 < v*L/2 by positivity).trans_le hlowerStar
  have hbv : bStar < v := by
    by_contra hn
    have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hn))
      (meanAccept_nonnegative Γ focal bStar)
    rw [oneUtility_eq Γ focal hg v hb.1] at hpositive
    linarith
  have hsmall := hdup bStar ⟨hb.1,hbv.le.trans hvlow⟩
  have hD0 : 0 ≤ duplicates Γ focal bStar := CountLaw.duplicates_nonneg _
  have hη : eta i ≤ 1 := by cases i <;> norm_num [eta,etaQ]
  have hcost : ((v-bStar)+eta i*bStar)*duplicates Γ focal bStar ≤ v*duplicates Γ focal bStar := by
    apply mul_le_mul_of_nonneg_right _ hD0
    nlinarith [mul_le_mul_of_nonneg_right hη hb.1]
  have hgap := exact_two_minus_one Γ focal (eta_pos i).le hη hA hg v hb.1
  have hstrict : oneUtility Γ focal v bStar < twoUtility Γ focal v bStar := by
    have hp := mul_pos hv (sub_pos.mpr hsmall)
    nlinarith
  refine ⟨bStar,⟨hb.1,hbv⟩,hpositive.trans hstrict,?_⟩
  intro b hb0
  by_cases hbv' : b ≤ v
  · have hh := hmax ⟨hb0,hbv'⟩
    change (v-b)*meanAcceptProb Γ focal b ≤ (v-bStar)*meanAcceptProb Γ focal bStar at hh
    rw [← oneUtility_eq Γ focal hg v hb0,← oneUtility_eq Γ focal hg v hb.1] at hh
    exact hh.trans_lt hstrict
  · have hbad : oneUtility Γ focal v b ≤ 0 := by
      rw [oneUtility_eq Γ focal hg v hb0]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge hbv'))
        (meanAccept_nonnegative Γ focal b)
    exact hbad.trans_lt (hpositive.trans hstrict)

def oneSup (Γ : FiniteGame m 2 c Seed) (focal : Fin m) (v : ℝ) : ℝ :=
  sSup ((oneUtility Γ focal v) '' Ici (0:ℝ))

theorem oneUtility_upper (Γ : FiniteGame m 2 c Seed) (focal : Fin m)
    (hg : Γ.g=0) {v : ℝ} (hv : 0 ≤ v) (b : ℝ) : oneUtility Γ focal v b ≤ v := by
  let P := (problem Γ focal).outcome (oneAction b)
  have hh := P.utility_le_positive_part v (oneAction b).bid Γ.g Γ.A Γ.G
    (oneAction b).bid_nonneg Γ.g_nonneg
  change P.utility v (oneAction b).bid Γ.g Γ.A Γ.G ≤ v
  simpa only [hg,sub_zero,max_eq_left hv] using hh

theorem oneSup_bdd (Γ : FiniteGame m 2 c Seed) (focal : Fin m)
    (hg : Γ.g=0) {v : ℝ} (hv : 0 ≤ v) :
    BddAbove ((oneUtility Γ focal v) '' Ici (0:ℝ)) := by
  refine ⟨v,?_⟩
  rintro _ ⟨b,hb,rfl⟩
  exact oneUtility_upper Γ focal hg hv b

theorem oneUtility_le_oneSup (Γ : FiniteGame m 2 c Seed) (focal : Fin m)
    (hg : Γ.g=0) {v : ℝ} (hv : 0 ≤ v) {b : ℝ} (hb : 0 ≤ b) :
    oneUtility Γ focal v b ≤ oneSup Γ focal v :=
  le_csSup (oneSup_bdd Γ focal hg hv) ⟨b,hb,rfl⟩

theorem source_tiny_value_strict_all_singletons (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (Γ : FiniteGame m 2 (capacity m) Seed)
    (hpolicy : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hroutes : ∀ᵐ p ∂Γ.F ⊗ₘ Γ.σ, 1 ≤ p.2.routeCount)
    (hlower : (Γ.F ⊗ₘ Γ.σ).real {p | p.2.routeCount=2}=cutoff i)
    (hA : Γ.A=Schedule.affine 2 (eta i) (eta_pos i).le
      (by cases i <;> norm_num [eta,etaQ])) (hg : Γ.g=0)
    (focal : Fin m) {v : ℝ} (hv : 0 < v) (hvlow : v ≤ (501/1000)*cutoff i)
    (hdup : ∀ b ∈ Icc (0:ℝ) ((501/1000)*cutoff i),
      duplicates Γ focal b ≤ SourceRankRates.Lm i m/10) :
    ∃ bStar ∈ Ico (0:ℝ) v,
      oneSup Γ focal v < twoUtility Γ focal v bStar ∧
      0 < twoUtility Γ focal v bStar ∧
      ∀ b ≥ 0, oneUtility Γ focal v b < twoUtility Γ focal v bStar := by
  let L := SourceRankRates.Lm i m
  let U := oneSup Γ focal v
  have hL : 0 < L := Bayes.binomBelow_pos (m-1) (capacity m)
    (PhysicalRates.capacity_positive (by omega)) _ (SourceRankRates.source_rank_parameter i)
  have hbase : v*L/2 ≤ U :=
    (source_half_bid_benchmark i Γ hpolicy hroutes hlower hg focal hv).trans
      (oneUtility_le_oneSup Γ focal hg hv.le (by positivity))
  have hU : 0 < U := (show 0 < v*L/2 by positivity).trans_le hbase
  have hchoose : ∃ b ≥ 0, (3/4)*U < oneUtility Γ focal v b := by
    by_contra hn
    have hbound : U ≤ (3/4)*U := by
      apply csSup_le (show ((oneUtility Γ focal v) '' Ici (0:ℝ)).Nonempty from
        ⟨oneUtility Γ focal v 0,0,(by simp : (0:ℝ) ∈ Ici 0),rfl⟩)
      rintro _ ⟨b,hb,rfl⟩
      exact le_of_not_gt (fun hb' => hn ⟨b,hb,hb'⟩)
    linarith
  obtain ⟨bStar,hb,hnear⟩ := hchoose
  have hpositive : 0 < oneUtility Γ focal v bStar :=
    (show 0 < (3/4)*U by positivity).trans hnear
  have hbv : bStar < v := by
    by_contra hn
    rw [oneUtility_eq Γ focal hg v hb] at hpositive
    have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hn))
      (meanAccept_nonnegative Γ focal bStar)
    linarith
  have hD := hdup bStar ⟨hb,hbv.le.trans hvlow⟩
  have hD0 : 0 ≤ duplicates Γ focal bStar := CountLaw.duplicates_nonneg _
  have hη : eta i ≤ 1 := by cases i <;> norm_num [eta,etaQ]
  have hcharge : ((v-bStar)+eta i*bStar)*duplicates Γ focal bStar ≤ v*L/10 := by
    have hcoeff : (v-bStar)+eta i*bStar ≤ v := by
      nlinarith [mul_le_mul_of_nonneg_right hη hb]
    have h1 := mul_le_mul_of_nonneg_right hcoeff hD0
    have h2 := mul_le_mul_of_nonneg_left hD hv.le
    nlinarith
  have hidentity := exact_two_minus_one Γ focal (eta_pos i).le hη hA hg v hb
  have hstrict : U < twoUtility Γ focal v bStar := by nlinarith
  exact ⟨bStar,⟨hb,hbv⟩,hstrict,hU.trans hstrict,
    fun b hb => (oneUtility_le_oneSup Γ focal hg hv.le hb).trans_lt hstrict⟩

end FCAppendix.Affine.Uniform06.NativeLowRoute
