import FCAppendix.Affine.Tail04.OrderedNativeSourceAllFeasible
import FCAppendix.Affine.Tail04.SourceRoleMasses
import FCAppendix.Affine.Tail04.MarketLimits

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedOriginalNativeUnderfill
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open OriginalValues OriginalPopulation Existence.Distributional NativeLocalPolicy
open Underfill

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem source_high_masses (P : ValueParameters) (E : Observable.Regions)
    (t : ℝ) (ht : P.M≤ t) (Γ : FiniteGame m 2 c Seed)
    (hF : Γ.F=valueLaw P)
    (hsource : ∀ᵐx ∂Γ.F⊗ₘΓ.σ,sourceBands P E t x) :
    (Γ.F⊗ₘΓ.σ).real (broadcastHigh E.R)=
      activeMass P.theta-activeMass P.theta*P.zeta*powerTail P.M 10 t ∧
    (Γ.F⊗ₘΓ.σ).real (privateHigh E.R)=
      partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t := by
  have hR1 : E.R<1 := E.R_le_Rp.trans_lt E.Rp_lt_one
  have hpa : 2+P.w< P.vA-P.w := P.partial_active_gap
  have hlt : P.d0< P.vA-P.w := by linarith [P.low_partial_gap,P.w_pos]
  have hpt : 2+P.w< t := by linarith [P.active_tail_gap,P.w_pos]
  have hb : ∀ᵐx ∂Γ.F⊗ₘΓ.σ,x∈broadcastHigh E.R↔x.1∈P.movingActiveValues t := by
    filter_upwards [hsource] with x hx
    rcases hx with hx|hx|hx|hx
    · have hnb : ¬E.R≤ x.2.bid := by linarith [hx.2.1,E.d_lt_R]
      have hnv : ¬x.1∈P.movingActiveValues t := by
        intro hv
        have hl:=hv.1
        linarith [hx.1.2]
      exact iff_of_false (fun h=> hnb h.1) hnv
    · have hnv : ¬x.1∈P.movingActiveValues t := by
        intro hv
        have hl:=hv.1
        linarith [hx.1.2]
      exact iff_of_false (fun h=> by have hr:=h.2;rw [hx.2.2] at hr;omega) hnv
    · exact iff_of_true ⟨hR1.le.trans hx.2.1.1,hx.2.2⟩ hx.1
    · exact iff_of_false (fun h=> by have hr:=h.2;rw [hx.2.2] at hr;omega)
        (fun hv=> not_le_of_gt hx.1 hv.2)
  have hp : ∀ᵐx ∂Γ.F⊗ₘΓ.σ,x∈privateHigh E.R↔x.1∈P.privateValues t := by
    filter_upwards [hsource] with x hx
    have hroles := (sourceBands_correspondence P E t ht x hx).2.1
    rw [←hroles]
    rcases hx with hx|hx|hx|hx
    · have hpriv : x.2.bid∉E.privateBids :=
        fun h=> not_lt_of_ge hx.2.1 (E.private_above_low h)
      exact iff_of_false (fun h=> by have hr:=h.2;rw [hx.2.2] at hr;omega) hpriv
    · exact iff_of_true ⟨hx.2.1.1,hx.2.2⟩ (Or.inl hx.2.1)
    · have hpriv : x.2.bid∉E.privateBids := by
        rintro (h|h)
        · linarith [h.2,hx.2.1.1,E.Rp_lt_one]
        · change E.H≤x.2.bid at h
          linarith [hx.2.1.2,E.U_lt_H]
      exact iff_of_false (fun h=> by have hr:=h.2;rw [hx.2.2] at hr;omega) hpriv
    · exact iff_of_true ⟨(E.R_le_Rp.trans E.Rp_lt_H.le).trans hx.2.1,hx.2.2⟩ (Or.inr hx.2.1)
  constructor
  · rw [joint_event_mass_from_value Γ.F Γ.σ (broadcastHigh E.R) (P.movingActiveValues t)
      measurableSet_Icc hb,hF,P.moving_active_mass t ht]
  · rw [joint_event_mass_from_value Γ.F Γ.σ (privateHigh E.R) (P.privateValues t)
      (measurableSet_Icc.union measurableSet_Ioi) hp,hF,P.private_mass t ht]

theorem normalized_unused_eq (Γ : FiniteGame m 2 c Seed) (j : Fin 2)
    (ω : Background m 2 Seed) :
    unusedCapacity (FeasibleListNormalization.game Γ) j ω=unusedCapacity Γ j ω := by
  unfold unusedCapacity
  rw [FeasibleListNormalization.allocation_eq]

section Source
variable (E : Observable.Regions) (P : ValueParameters) (hd : E.d=P.d0)
  (t : ℝ) (ht : P.M≤ t)
local instance : IsProbabilityMeasure (P.originalMovingActiveLaw t ht) :=
  P.originalMovingActiveLaw_probability t ht
variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (πP : Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
  (πA : Law (A:=Icc (1:ℝ) E.U) (P.originalMovingActiveLaw t ht))
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀v,t< v→ E.H≤ upperBid v)
  (m c : ℕ) (ξ width θ eA eR B0 : ℝ)
  (hξ : 0< ξ) (hξ1 : ξ<1) (hwidth : 0< width) (hθ0 : 0≤ θ) (hθ1 : θ≤1)
local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
variable (hrare : (1-ξ)*E.U+ξ*E.U*((m:ℝ)*
    ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
      (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ E.R)
  (hdup : (1-ξ)*E.U<1) (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
  (hcoef : (1-η)/2=ξ) (hlow : E.d<1-ξ)
local notation "Γ₀" => OrderedNativeSourcePosterior.game E P hd t ht πL πP πA upperBid hupperBid hfloor
  m c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1

include hrare hcoef hlow in
theorem source_unused (hc : (c:ℝ)≤(m:ℝ)/2) (hz : z≤1/10) (j : Fin 2) :
    (∫ω,unusedCapacity Γ₀ j ω ∂backgroundLaw Γ₀)≤(c:ℝ)*Real.exp (-(m:ℝ)/50) := by
  have hsource : ∀ᵐx ∂(Γ₀).F⊗ₘ(Γ₀).σ,sourceBands P E t x := by
    rw [OrderedNativeSourcePosterior.game_original_joint]
    exact originalJoint_sourceBands P E hd t ht πL πP πA upperBid hupperBid hfloor
  have hm := source_high_masses P E t ht Γ₀ rfl hsource
  have hmass : (3/5:ℝ)≤((Γ₀).F⊗ₘ(Γ₀).σ).real (broadcastHigh E.R)+
      ((Γ₀).F⊗ₘ(Γ₀).σ).real (privateHigh E.R)/2 := by
    rw [hm.1,hm.2]
    have hδ : delta P.theta≤8/125 := by
      dsimp [delta]
      nlinarith [P.theta_pos,P.theta_small]
    exact (both_source_arrival_margins (delta P.theta) z hδ hz).2
  let B:=OrderedNativeSourceAllFeasible.initialPosterior E P hd t ht πL πP πA upperBid hupperBid hfloor
    m c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1
  have hrat:=OrderedNativeSourcePosterior.game_rationalOnPath E P hd t ht πL πP πA
    upperBid hupperBid hfloor m c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1
    hrare hdup η hη0 hη1 B hcoef hlow j
  have hR : 0< E.R := E.d_nonneg.trans_lt E.d_lt_R
  apply native_unused_source_bound Γ₀ j hrat (1/2) (E.R/2) E.R
    (by norm_num) (by positivity) (by linarith) _ hc hmass
  intro r hr hr2
  change (1/2:ℝ)*(r:ℝ)≤(Schedule.affine 2 η hη0 hη1).charge r
  interval_cases r <;> norm_num [Schedule.affine,successIndicator]
  exact hη0

include hrare hcoef hlow in
theorem normalized_source_unused (hc : (c:ℝ)≤(m:ℝ)/2) (hz : z≤1/10) (j : Fin 2) :
    (∫ω,unusedCapacity (FeasibleListNormalization.game Γ₀) j ω
      ∂backgroundLaw (FeasibleListNormalization.game Γ₀))≤(c:ℝ)*Real.exp (-(m:ℝ)/50) := by
  simp only [normalized_unused_eq]
  exact source_unused E P hd t ht πL πP πA upperBid hupperBid hfloor m c
    ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 hrare hdup η hη0 hη1 hcoef hlow hc hz j

end Source
end FCAppendix.Affine.Tail04.OrderedOriginalNativeUnderfill
