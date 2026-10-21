import FCAppendix.Affine.Tail04.NativeLowInterim
import FCAppendix.Affine.Tail04.NativeSourceAllFeasible
import FCAppendix.Affine.Tail04.OriginalLowRow
import FCAppendix.Affine.Hybrid.NativeLowActualIncentives

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeLowSourceIC
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid LowBody NativeContinuation NativeMenuReports NativeLowCoordinates
open NativeLowIntegration NativeLowInterim OriginalValues OriginalPopulation
open Existence.Distributional NativeLocalPolicy
open scoped BigOperators

variable (P : ValueParameters) (t : ℝ) (ht : P.M≤ t)

def referenceLowLaw : Measure ℝ := realLowLaw P.originalLowLaw
instance referenceLowLaw_probability : IsProbabilityMeasure (referenceLowLaw P) := by
  unfold referenceLowLaw realLowLaw
  letI : IsProbabilityMeasure P.originalLowLaw := P.originalLowLaw_probability
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

def categories : FiniteLaw (Fin 4) :=
  categoryLaw (lowMass P.theta)
    (activeMass P.theta-activeMass P.theta*P.zeta*powerTail P.M 10 t)
    (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)
    P.low_mass_pos.le (P.movingActiveMass_positive t ht).le
    (add_nonneg (by norm_num [partialMass]) (P.tailMass_nonneg t ht))
    (by linarith [mass_sum P.theta]) (referenceLowLaw P)

variable (E : Observable.Regions) (hd : E.d=P.d0) (N c : ℕ)
  (ξ width θ eA eR B0 : ℝ) (hξ : 0< ξ) (hξ1 : ξ<1) (hwidth : 0< width)
  (hθ0 : 0≤ θ) (hθ1 : θ≤1)
  (L : ActualAtomlessLowLimit N P.d0 ξ c (categories P t ht) P.originalLowLaw)

local instance : IsProbabilityMeasure (P.originalMovingActiveLaw t ht) :=
  P.originalMovingActiveLaw_probability t ht

variable (πP : Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
  (πA : Law (A:=Icc (1:ℝ) E.U) (P.originalMovingActiveLaw t ht))
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀v,t< v→ E.H≤ upperBid v)

variable (hrare : (1-ξ)*E.U+ξ*E.U*((N+1:ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ E.R)
  (hdup : (1-ξ)*E.U<1)
  (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1) (hcoef : (1-η)/2=ξ)

include hrare

theorem original_profiles_on_menu :
    ∀ᵐp ∂userProfileLaw (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1),∀l,MenuAction E (p l).1.2 := by
  have hj := NativeSourcePosterior.game_original_user E P hd t ht L.joint πP πA
    upperBid hupperBid hfloor (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1
  have hu : ∀ᵐx ∂userLaw (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1),MenuAction E x.1.2 := by
    rw [hj]
    have hs : ∀ᵐx ∂((originalJoint P t ht E.R E.Rp E.U (E.d_nonneg.trans E.d_lt_R.le)   L.joint πP πA upperBid hupperBid) : Measure (ℝ×JointAction 2)),MenuAction E x.2 :=
      (originalJoint_sourceBands P E hd t ht L.joint πP πA
        upperBid hupperBid hfloor).mono (fun x hx=>source_menu E P t x hx)
    exact (measurePreserving_fst (μ:=((originalJoint P t ht E.R E.Rp E.U (E.d_nonneg.trans E.d_lt_R.le)   L.joint πP πA upperBid hupperBid) : Measure (ℝ×JointAction 2)))
      (ν:=permLaw 2)).quasiMeasurePreserving.ae hs
  exact ae_all_iff.mpr (fun l=>(measurePreserving_eval
    (fun _ : Fin (N+1)=>userLaw (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1)) l).quasiMeasurePreserving.ae hu)

theorem original_deleted_row (i : Fin (N+1)) :
    (userProfileLaw (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1)).map (rowProfile E i)=
      Measure.pi (fun _ : Fin N=> rivalLaw (lowMass P.theta) (activeMass P.theta-(activeMass P.theta*P.zeta*powerTail P.M 10 t)) (partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t)) (realLowLaw ((ProbabilityMeasure.map (L.joint).1 measurable_snd.aemeasurable : ProbabilityMeasure (LowValue P.d0)) : Measure (LowValue P.d0)))) := by
  rw [compact_bid_real_law P.originalLowLaw L.joint]
  exact deleted_rival_rows_law (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1) i (E.nativeRow (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1)) (E.measurable_nativeRow (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1)) _
    (native_original_exact_low_row E P hd t ht L.joint πP πA upperBid hupperBid hfloor (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1)
      (NativeSourcePosterior.game_original_joint E P hd t ht L.joint πP πA
        upperBid hupperBid hfloor (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1))

include hcoef in
theorem original_positive_payoff (i : Fin (N+1)) (v : ℝ) (act : JointAction 2)
    (hk : act.routeCount=2) (hb : 0< act.bid) (hbd : act.bid≤ P.d0) :
    (problem (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1) i).payoff v act=
      exactExpectedPayoff N P.d0 ξ c (categories P t ht) (ProbabilityMeasure.map (L.joint).1 measurable_snd.aemeasurable : ProbabilityMeasure (LowValue P.d0)) (v,act.bid) := by
  letI:=L.compact_atomless
  exact positive_payoff (NativeSourcePolicy.data E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup) (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1) rfl
    (original_profiles_on_menu P t ht E hd N c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1
      L πP πA upperBid hupperBid hfloor hrare hdup η hη0 hη1)
    rfl η hη0 hη1 hcoef rfl rfl rfl P.d0 hd (lowMass P.theta) (activeMass P.theta-(activeMass P.theta*P.zeta*powerTail P.M 10 t)) (partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))
    P.low_mass_pos.le (P.movingActiveMass_positive t ht).le
    (add_nonneg (by norm_num [partialMass]) (P.tailMass_nonneg t ht))
    (by linarith [mass_sum P.theta]) (referenceLowLaw P) (ProbabilityMeasure.map (L.joint).1 measurable_snd.aemeasurable : ProbabilityMeasure (LowValue P.d0)) i
    (original_deleted_row P t ht E hd N c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1
      L πP πA upperBid hupperBid hfloor hrare hdup η hη0 hη1 i) v act hk hb hbd

include hcoef in
theorem original_zero_envelope (i : Fin (N+1)) (v : ℝ) (hv : 0≤ v)
    (act : JointAction 2) (hk : act.routeCount=2) (hz : act.bid=0)
    (y : ℝ) (hy : 0< y) (hyd : y≤ P.d0) :
    (problem (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1) i).payoff v act≤
      (problem (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1) i).payoff v (NativeLowIncentives.broadcast y hy.le)+2*y :=
  zero_envelope (NativeSourcePolicy.data E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup) (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1) rfl rfl η hη0 hη1 hcoef rfl rfl rfl
    (original_profiles_on_menu P t ht E hd N c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1
      L πP πA upperBid hupperBid hfloor hrare hdup η hη0 hη1)
    i v hv act hk hz y hy (by change y≤E.d; rwa [hd])

theorem original_duplicates (i : Fin (N+1)) (act : JointAction 2)
    (hk : act.routeCount=2) (hbd : act.bid≤ P.d0) :
    ((problem (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1) i).outcome act).duplicates≤
      (CommonList.iid (categories P t ht) N).prob (BothUnderflow c) := by
  have hb:=duplicates_le_original_row (NativeSourcePolicy.data E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup) (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1) rfl
    (original_profiles_on_menu P t ht E hd N c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1
      L πP πA upperBid hupperBid hfloor hrare hdup η hη0 hη1) i _
    (original_deleted_row P t ht E hd N c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1
      L πP πA upperBid hupperBid hfloor hrare hdup η hη0 hη1 i) act hk (by change act.bid≤E.d; rwa [hd])
  rw [rowBothUnderflow_probability (lowMass P.theta) (activeMass P.theta-(activeMass P.theta*P.zeta*powerTail P.M 10 t)) (partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t)) P.low_mass_pos.le
    (P.movingActiveMass_positive t ht).le
    (add_nonneg (by norm_num [partialMass]) (P.tailMass_nonneg t ht))
    (by linarith [mass_sum P.theta]) (realLowLaw ((ProbabilityMeasure.map (L.joint).1 measurable_snd.aemeasurable : ProbabilityMeasure (LowValue P.d0)) : Measure (LowValue P.d0))) N c,
    categoryLaw_eq_low_law (lowMass P.theta) (activeMass P.theta-(activeMass P.theta*P.zeta*powerTail P.M 10 t)) (partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t)) P.low_mass_pos.le (P.movingActiveMass_positive t ht).le
      (add_nonneg (by norm_num [partialMass]) (P.tailMass_nonneg t ht))
      (by linarith [mass_sum P.theta]) (realLowLaw ((ProbabilityMeasure.map (L.joint).1 measurable_snd.aemeasurable : ProbabilityMeasure (LowValue P.d0)) : Measure (LowValue P.d0)))
      (referenceLowLaw P)] at hb
  exact hb

variable (hell : 0<(CommonList.iid (categories P t ht) N).prob (LocalUnderflow c 0))
  (hsmall : (CommonList.iid (categories P t ht) N).prob (BothUnderflow c)≤
    (CommonList.iid (categories P t ht) N).prob (LocalUnderflow c 0)/4)

include hcoef hell hsmall in
theorem original_low_joint_best_response (i : Fin (N+1)) :
    ∀ᵐx ∂(L.joint.1 : Measure (LowValue P.d0×LowValue P.d0)),
      (problem (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1) i).BestResponse x.1.1 (lowBroadcast x.2) := by
  have hξh : ξ≤1/2 := by linarith
  filter_upwards [L.all_bid_IC hξ hξh,L.value_positive,L.bid_positive] with x hIC hv hb
  apply NativeLowIncentives.best_response (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1) i hξ hξh hη0 hη1 rfl rfl
    (categories P t ht) (ProbabilityMeasure.map (L.joint).1 measurable_snd.aemeasurable : ProbabilityMeasure (LowValue P.d0)) x.1 x.2 hv hb hIC
  · intro act hk hpos hbd
    exact original_positive_payoff P t ht E hd N c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1
      L πP πA upperBid hupperBid hfloor hrare hdup η hη0 hη1 hcoef i x.1.1 act hk hpos hbd
  · intro act hk hz y hy hyd
    exact original_zero_envelope P t ht E hd N c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1
      L πP πA upperBid hupperBid hfloor hrare hdup η hη0 hη1 hcoef i x.1.1 x.1.2.1 act hk hz y hy hyd
  · exact hell
  · exact hsmall
  · intro act hk hbval
    exact original_duplicates P t ht E hd N c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1
      L πP πA upperBid hupperBid hfloor hrare hdup η hη0 hη1 i act hk (hbval.trans x.1.2.2)

include hcoef hell hsmall in
theorem original_low_all_labels :
    ∀ᵐx ∂(lowJoint P.originalLowLaw L.joint : Measure (ℝ×JointAction 2)),
      ∀i : Fin (N+1),(problem (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1) i).BestResponse x.1 x.2 := by
  apply (measurableEmbedding_lowJointPoint P.d0).ae_map_iff.mpr
  exact ae_all_iff.mpr (fun i=> original_low_joint_best_response P t ht E hd N c
    ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 L πP πA upperBid hupperBid hfloor
    hrare hdup η hη0 hη1 hcoef hell hsmall i)

include hcoef hell hsmall in
theorem normalized_low_all_labels :
    ∀ᵐx ∂(lowJoint P.originalLowLaw L.joint : Measure (ℝ×JointAction 2)),
      ∀i : Fin (N+1),(problem (FeasibleListNormalization.game (NativeSourcePosterior.game E P hd t ht L.joint πP πA upperBid hupperBid hfloor   (N+1) c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1 (by simpa only [Nat.cast_add,Nat.cast_one] using hrare) hdup η hη0 hη1)) i).BestResponse x.1 x.2 := by
  simpa only [FeasibleListNormalization.problem_eq] using
    original_low_all_labels P t ht E hd N c ξ width θ eA eR B0 hξ hξ1 hwidth hθ0 hθ1
      L πP πA upperBid hupperBid hfloor hrare hdup η hη0 hη1 hcoef hell hsmall

end FCAppendix.Affine.Tail04.NativeLowSourceIC
