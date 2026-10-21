import FCAppendix.Affine.Uniform06.EntryEarlyFamilyAdapter
import FCAppendix.Affine.Uniform06.NativeLowRoute

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryNativeSource

open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open scoped BigOperators
open FCAppendix.Affine.Uniform07
open LiteralExperiment NativeLowRoute EntryConstructedSource EntryConstructedSource.EarlyArray
open EntryFullRestoration EntryFullDominance EntryGoodOptimizer EntryEarlyFamilyAdapter
attribute [local instance] Classical.propDecidable

variable {Seed : Type*} [MeasurableSpace Seed] {m c : ℕ}

def fixedValueCountLaw (Γ : FiniteGame m 2 c Seed) (focal : Fin m)
    (_v : ℝ) (a : JointAction 2) : CountLaw 2 := (problem Γ focal).outcome a

theorem two_count_masses (P : CountLaw 2) :
    P.mass 0=1-P.success ∧ P.mass 1=P.success-P.duplicates ∧ P.mass 2=P.duplicates := by
  have hS : P.success=P.mass 1+P.mass 2 := by
    simp [CountLaw.success,FiniteLaw.expect,Fin.sum_univ_succ,successIndicator]
  have hL : P.load=P.mass 1+2*P.mass 2 := by
    simp [CountLaw.load,FiniteLaw.expect,Fin.sum_univ_succ]
    ring
  have hT : P.mass 0+P.mass 1+P.mass 2=1 := by
    simpa [Fin.sum_univ_succ,add_assoc] using P.total
  unfold CountLaw.duplicates
  constructor
  · linarith
  · constructor <;> linarith

structure CountTransport (i : Row) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (cm : (Fin (m-1) → Fin 4) → ℝ)
    (Γ : FiniteGame m 2 (capacity m) Seed) (focal : Fin m) : Prop where
  success : ∀ b : ℝ,b∈Icc (0:ℝ) (ReceiptGap.cap i) →
    ((problem Γ focal).outcome (twoAction b)).success=sourceSuccess i m G g cm b
  duplicate : ∀ b : ℝ,b∈Icc (0:ℝ) (ReceiptGap.cap i) →
    ((problem Γ focal).outcome (twoAction b)).duplicates=sourceDuplicate i m G g cm b

theorem every_fixed_value_count_law (i : Row) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (cm : (Fin (m-1) → Fin 4) → ℝ)
    (Γ : FiniteGame m 2 (capacity m) Seed) (focal : Fin m)
    (hT : CountTransport i G g cm Γ focal) :
    ∀ v b : ℝ,b∈Icc (0:ℝ) (ReceiptGap.cap i) →
      (fixedValueCountLaw Γ focal v (twoAction b)).mass 0=1-sourceSuccess i m G g cm b ∧
      (fixedValueCountLaw Γ focal v (twoAction b)).mass 1=
        sourceSuccess i m G g cm b-sourceDuplicate i m G g cm b ∧
      (fixedValueCountLaw Γ focal v (twoAction b)).mass 2=sourceDuplicate i m G g cm b := by
  intro v b hb
  have hh := two_count_masses ((problem Γ focal).outcome (twoAction b))
  simpa only [fixedValueCountLaw,hT.success b hb,hT.duplicate b hb] using hh

theorem mean_transport (i : Row) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (cm : (Fin (m-1) → Fin 4) → ℝ)
    (Γ : FiniteGame m 2 (capacity m) Seed) (focal : Fin m)
    (hT : CountTransport i G g cm Γ focal) {b : ℝ} (hb : b∈Icc (0:ℝ) (ReceiptGap.cap i)) :
    meanAcceptProb Γ focal b=(sourceSuccess i m G g cm b+sourceDuplicate i m G g cm b)/2 := by
  have hload : ((problem Γ focal).outcome (twoAction b)).load=2*meanAcceptProb Γ focal b := by
    simpa [twoAction,max_eq_left hb.1] using load_eq_mean Γ (by norm_num) focal (twoAction b)
  have hS := hT.success b hb
  have hD := hT.duplicate b hb
  unfold CountLaw.duplicates at hD
  linarith

theorem every_fixed_value_payoffs (i : Row) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (cm : (Fin (m-1) → Fin 4) → ℝ)
    (Γ : FiniteGame m 2 (capacity m) Seed) (focal : Fin m)
    (hT : CountTransport i G g cm Γ focal)
    (hA : Γ.A=Schedule.affine 2 (eta i) (eta_pos i).le
      (by cases i <;> norm_num [eta,etaQ])) (hg : Γ.g=0) :
    ∀ v b : ℝ,b∈Icc (0:ℝ) (ReceiptGap.cap i) →
      oneUtility Γ focal v b=(v-b)*(sourceSuccess i m G g cm b+sourceDuplicate i m G g cm b)/2 ∧
      twoUtility Γ focal v b=(v-b)*sourceSuccess i m G g cm b-eta i*b*sourceDuplicate i m G g cm b := by
  intro v b hb
  have hq := mean_transport i G g cm Γ focal hT hb
  have h1 := oneUtility_eq Γ focal hg v hb.1
  have h2 := exact_two_minus_one Γ focal (eta_pos i).le
    (by cases i <;> norm_num [eta,etaQ]) hA hg v hb.1
  have hD : duplicates Γ focal b=sourceDuplicate i m G g cm b := hT.duplicate b hb
  rw [hq] at h1
  constructor
  · nlinarith [h1]
  · rw [hD,h1] at h2
    nlinarith

theorem native_zero_route_payoff (Γ : FiniteGame m 2 c Seed) (focal : Fin m)
    (a : JointAction 2) (ha : a.routeCount=0) (v : ℝ) :
    (problem Γ focal).payoff v a=0 := by
  let P := (problem Γ focal).outcome a
  have hL : P.load≤0 := by
    have hh := load_le_routeCount_mul_success Γ focal a
    simpa only [ha,Nat.cast_zero,zero_mul] using hh
  have hS : P.success=0 := le_antisymm (P.success_le_load.trans hL) P.success_nonneg
  have hA : P.charge Γ.A=0 := le_antisymm ((P.charge_le_load Γ.A).trans hL) (P.charge_nonneg Γ.A)
  have hG : P.charge Γ.G=0 := le_antisymm ((P.charge_le_load Γ.G).trans hL) (P.charge_nonneg Γ.G)
  change P.utility v a.bid Γ.g Γ.A Γ.G=0
  rw [CountLaw.utility_eq,hS,hA,hG]
  ring

def recipientUtility (Γ : FiniteGame m 2 c Seed) (focal : Fin m)
    (recipient : Fin 2) (v b : ℝ) : ℝ :=
  (v-b)*acceptProb Γ focal b recipient

theorem recipientUtility_original_integral (Γ : FiniteGame m 2 c Seed) (focal : Fin m)
    (recipient : Fin 2) (v b : ℝ) :
    recipientUtility Γ focal recipient v b=
      ∫ ω : Background m 2 Seed,(v-b)*(if Accepts Γ focal b recipient ω then 1 else 0)
        ∂backgroundLaw Γ := by
  unfold recipientUtility acceptProb
  rw [← integral_indicator_one (measurableSet_accepts Γ focal b recipient),integral_const_mul]
  simp only [Set.indicator_apply,Set.mem_setOf_eq,Pi.one_apply]

section SourceSequence
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {i : Row} (s : EarlyArray μ i)

theorem original_native_entry_dominance
    (cm : (j : ℕ) → (Fin (s.population j-1) → Fin 4) → ℝ)
    (hc : ∀ j,CountContract i (s.guards j) (cm j))
    (v : ℕ → ℝ) (hv : Tendsto v atTop (𝓝 (entry i)))
    (hnull : ∀ j b,((s.jointLaw j).map Prod.snd) {b}=0)
    (Γ : ∀ j,FiniteGame (s.population j) 2 (capacity (s.population j)) Seed)
    (focal : ∀ j,Fin (s.population j))
    (hT : ∀ j,CountTransport i (s.jointLaw j) (s.guards j) (cm j) (Γ j) (focal j))
    (hA : ∀ j,(Γ j).A=Schedule.affine 2 (eta i) (eta_pos i).le
      (by cases i <;> norm_num [eta,etaQ])) (hg : ∀ j,(Γ j).g=0) :
    ∀ᶠ j in atTop,
      chosen s v j∈Icc (LowChernoff.physicalFloor i (v j)) (min (v j) (ReceiptGap.cap i)) ∧
      0<(problem (Γ j) (focal j)).payoff (v j) (twoAction (chosen s v j)) ∧
      ∀ a : JointAction 2,a.routeCount≤1 →
        (problem (Γ j) (focal j)).payoff (v j) a<
          (problem (Γ j) (focal j)).payoff (v j) (twoAction (chosen s v j)) := by
  filter_upwards [original_full_entry_dominance s cm hc v hv hnull,
    hv.eventually_lt_const (ReceiptGap.entry_below_cap i)] with j hj hvc
  have hb0 : 0≤ chosen s v j := by
    have hf : 0≤ LowChernoff.physicalFloor i (v j) := by unfold LowChernoff.physicalFloor; positivity
    exact hf.trans hj.1.1
  have hpay := every_fixed_value_payoffs i (s.jointLaw j) (s.guards j) (cm j)
    (Γ j) (focal j) (hT j) (hA j) (hg j)
  have hbcap : chosen s v j∈Icc (0:ℝ) (ReceiptGap.cap i) :=
    ⟨hb0,hj.1.2.trans (min_le_right _ _)⟩
  have htwo : twoUtility (Γ j) (focal j) (v j) (chosen s v j)=
      twoFull s cm v j (chosen s v j) := (hpay (v j) _ hbcap).2
  refine ⟨hj.1,?_,?_⟩
  · change 0< twoUtility (Γ j) (focal j) (v j) (chosen s v j)
    rw [htwo]
    exact hj.2.1
  intro a ha
  have htwo' : (problem (Γ j) (focal j)).payoff (v j) (twoAction (chosen s v j))=
      twoFull s cm v j (chosen s v j) := htwo
  rw [htwo']
  rcases Nat.eq_zero_or_pos a.routeCount with hz | hp
  · rw [native_zero_route_payoff (Γ j) (focal j) a hz]
    exact hj.2.1
  · have hs : a.routeCount=1 := by omega
    rw [singleton_payoff (Γ j) (by norm_num) (focal j) a hs (v j),hg j,sub_zero]
    by_cases hb : a.bid≤ v j
    · rw [mean_transport i (s.jointLaw j) (s.guards j) (cm j) (Γ j) (focal j)
        (hT j) ⟨a.bid_nonneg,hb.trans hvc.le⟩]
      have hh := hj.2.2 a.bid a.bid_nonneg
      simpa only [oneFull,mul_div_assoc] using hh
    · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith)
        (meanAccept_nonnegative (Γ j) (focal j) a.bid)).trans_lt hj.2.1

def RecipientTransport
    (cm : (j : ℕ) → (Fin (s.population j-1) → Fin 4) → ℝ)
    (Γ : ∀ j,FiniteGame (s.population j) 2 (capacity (s.population j)) Seed)
    (focal : ∀ j,Fin (s.population j)) : Prop :=
  ∀ j : ℕ,∀ b : ℝ,b∈Icc (0:ℝ) (ReceiptGap.cap i) → ∀ recipient : Fin 2,
    acceptProb (Γ j) (focal j) b recipient=
      (sourceSuccess i (s.population j) (s.jointLaw j) (s.guards j) (cm j) b+
        sourceDuplicate i (s.population j) (s.jointLaw j) (s.guards j) (cm j) b)/2

theorem original_deterministic_recipient_dominance
    (cm : (j : ℕ) → (Fin (s.population j-1) → Fin 4) → ℝ)
    (hc : ∀ j,CountContract i (s.guards j) (cm j))
    (v : ℕ → ℝ) (hv : Tendsto v atTop (𝓝 (entry i)))
    (hnull : ∀ j b,((s.jointLaw j).map Prod.snd) {b}=0)
    (Γ : ∀ j,FiniteGame (s.population j) 2 (capacity (s.population j)) Seed)
    (focal : ∀ j,Fin (s.population j))
    (hT : ∀ j,CountTransport i (s.jointLaw j) (s.guards j) (cm j) (Γ j) (focal j))
    (hrecipient : RecipientTransport s cm Γ focal)
    (hA : ∀ j,(Γ j).A=Schedule.affine 2 (eta i) (eta_pos i).le
      (by cases i <;> norm_num [eta,etaQ])) (hg : ∀ j,(Γ j).g=0) :
    ∀ᶠ j in atTop,
      chosen s v j∈Icc (LowChernoff.physicalFloor i (v j)) (min (v j) (ReceiptGap.cap i)) ∧
      0< twoUtility (Γ j) (focal j) (v j) (chosen s v j) ∧
      ∀ recipient : Fin 2,∀ b : ℝ,0≤ b →
        recipientUtility (Γ j) (focal j) recipient (v j) b<
          twoUtility (Γ j) (focal j) (v j) (chosen s v j) := by
  filter_upwards [original_full_entry_dominance s cm hc v hv hnull,
    hv.eventually_lt_const (ReceiptGap.entry_below_cap i)] with j hj hvc
  have hb0 : 0≤ chosen s v j := by
    have hf : 0≤ LowChernoff.physicalFloor i (v j) := by unfold LowChernoff.physicalFloor; positivity
    exact hf.trans hj.1.1
  have htwo := (every_fixed_value_payoffs i (s.jointLaw j) (s.guards j) (cm j)
    (Γ j) (focal j) (hT j) (hA j) (hg j) (v j) _
      ⟨hb0,hj.1.2.trans (min_le_right _ _)⟩).2
  change twoUtility (Γ j) (focal j) (v j) (chosen s v j)=
    twoFull s cm v j (chosen s v j) at htwo
  refine ⟨hj.1,by rw [htwo]; exact hj.2.1,?_⟩
  intro recipient b hb
  rw [htwo,recipientUtility]
  by_cases hbv : b≤ v j
  · rw [hrecipient j b ⟨hb,hbv.trans hvc.le⟩ recipient]
    simpa only [oneFull,mul_div_assoc] using hj.2.2 b hb
  · have hq : 0≤ acceptProb (Γ j) (focal j) b recipient := by unfold acceptProb; positivity
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) hq).trans_lt hj.2.1

end SourceSequence

section Family
variable {C : ℕ → Type*}
  (G : ∀ m,C m → ProbabilityMeasure (ℝ × ℝ))
  (g : ∀ m,C m → GuardData)
  (cm : ∀ m,C m → (Fin (m-1) → Fin 4) → ℝ)

theorem primitive_native_entry_dominance
    (i : Row) (h05 : SourceEarlyFamily.EarlyMenuFields G g cm i)
    (hr : RootFields G g i)
    (hc : ∀ m (E : C m),CountContract i (g m E) (cm m E))
    (hatom : ∀ m (E : C m) b,((G m E:Measure (ℝ × ℝ)).map Prod.snd) {b}=0)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (E : ∀ j,C (n j))
    (v : ℕ → ℝ) (hv : Tendsto v atTop (𝓝 (entry i)))
    (Γ : ∀ j,FiniteGame (n j) 2 (capacity (n j)) Seed)
    (focal : ∀ j,Fin (n j))
    (hT : ∀ j,CountTransport i (G (n j) (E j):Measure (ℝ × ℝ))
      (g (n j) (E j)) (cm (n j) (E j)) (Γ j) (focal j))
    (hA : ∀ j,(Γ j).A=Schedule.affine 2 (eta i) (eta_pos i).le
      (by cases i <;> norm_num [eta,etaQ])) (hg : ∀ j,(Γ j).g=0) :
    ∀ᶠ j in atTop,∃ a : JointAction 2,
      a.routeCount=2 ∧
      a.bid∈Icc (LowChernoff.physicalFloor i (v j)) (min (v j) (ReceiptGap.cap i)) ∧
      0<(problem (Γ j) (focal j)).payoff (v j) a ∧
      ∀ d : JointAction 2,d.routeCount≤1 →
        (problem (Γ j) (focal j)).payoff (v j) d<
          (problem (Γ j) (focal j)).payoff (v j) a := by
  let s := from_family G g cm i h05 hr n hn E
  have hs (j : ℕ) : s.jointLaw j=(G (n j) (E j):Measure (ℝ × ℝ)) :=
    from_family_jointLaw G g cm i h05 hr n hn E j
  have hc' : ∀ j,CountContract i (s.guards j) (cm (n j) (E j)) :=
    fun j => hc (n j) (E j)
  have hn' : ∀ j b,((s.jointLaw j).map Prod.snd) {b}=0 := by
    intro j b
    rw [hs j]
    exact hatom (n j) (E j) b
  have ht' : ∀ j,CountTransport i (s.jointLaw j) (s.guards j)
      (cm (n j) (E j)) (Γ j) (focal j) := by
    intro j
    rw [hs j]
    exact hT j
  filter_upwards [original_native_entry_dominance s (fun j => cm (n j) (E j))
    hc' v hv hn' Γ focal ht' hA hg] with j hj
  have hb0 : 0≤ chosen s v j := by
    have hf : 0≤ LowChernoff.physicalFloor i (v j) := by unfold LowChernoff.physicalFloor; positivity
    exact hf.trans hj.1.1
  refine ⟨twoAction (chosen s v j),rfl,?_,hj.2⟩
  simpa only [twoAction,max_eq_left hb0] using hj.1

end Family

end FCAppendix.Affine.Uniform06.EntryNativeSource
