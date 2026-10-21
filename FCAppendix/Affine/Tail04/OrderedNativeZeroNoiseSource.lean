import FCAppendix.Affine.Tail04.OrderedNativeNoisySource

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativeZeroNoiseSource
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint FiniteTailNoisyGame

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)

lemma base_partial_le_physical : D.Up≤ D.V := by
  have hu : 0≤ D.Up := D.hR.le.trans D.hRUp
  have h := mul_nonneg hu D.heps.le
  dsimp [Data.V]
  nlinarith

lemma base_active_le_physical : D.U≤ D.B := by
  have hu : 0≤ D.U := (by norm_num : (0:ℝ)≤1).trans D.hU
  have h := mul_nonneg hu D.heps.le
  dsimp [Data.B]
  nlinarith

lemma base_partial_lt_one : D.Up<1 :=
  (base_partial_le_physical D).trans_lt D.hRp

lemma base_receipt_gap : (1-D.ξ)*D.U< D.R := by
  have hh := mul_le_mul_of_nonneg_left (base_active_le_physical D)
    (sub_nonneg.mpr D.hξ1.le)
  exact hh.trans_lt D.hgap

lemma base_duplicate_gap : (1-D.ξ)*D.U<1 := by
  have h := mul_le_mul_of_nonneg_left (base_active_le_physical D)
    (sub_nonneg.mpr D.hξ1.le)
  exact (h.trans_lt D.hgap).trans
    (D.hRUp.trans_lt (base_partial_lt_one D))

variable (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)

def regions : Observable.Regions where
  d:=P.d0
  R:=D.R
  Rp:=D.Up
  U:=D.U
  H:=H
  d_nonneg:=P.d0_pos.le
  d_lt_R:=hdR
  R_le_Rp:=D.hRUp
  Rp_lt_one:=base_partial_lt_one D
  one_le_U:=D.hU
  U_lt_H:=hUH

local instance movingActive_probability (hle : P.M ≤ t) :
    IsProbabilityMeasure (P.originalMovingActiveLaw t hle) :=
  P.originalMovingActiveLaw_probability t hle

def active (π : JointProfile D P t ht) :
    Law (A:=Icc (1:ℝ) D.U) (P.originalMovingActiveLaw t ht.le) :=
  ActiveJointMerge.mergedActiveLaw P t ht D.u D.U D.huU (π 0) (π 1)

def partialLaw (π : JointProfile D P t ht) :
    Law (A:=Icc D.R D.Up) P.originalPartialLaw := π 2

variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (π : JointProfile D P t ht)
    (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
    (hfloor : ∀ v,t< v→ H≤ upperBid v) (m : ℕ)

variable (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((m:ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ D.R)

def joint : ProbabilityMeasure (ℝ×JointAction 2) :=
  originalJoint P t ht.le D.R D.Up D.U D.hR.le πL
    (partialLaw D P t ht π) (active D P t ht π) upperBid hupperBid

theorem joint_value :
    (joint D P t ht πL π upperBid hupperBid : Measure (ℝ×JointAction 2)).map Prod.fst=valueLaw P :=
  originalJoint_value P t ht.le D.R D.Up D.U D.hR.le πL
    (partialLaw D P t ht π) (active D P t ht π) upperBid hupperBid

def game : FiniteGame m 2 D.c NativeLocalPolicy.Seed :=
  OrderedNativeSourceAllFeasible.nativeGame (regions D P hdR H hUH) P rfl t ht.le πL
    (partialLaw D P t ht π) (active D P t ht π)
    upperBid hupperBid hfloor m D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 hrare
    (base_duplicate_gap D) D.eta D.heta0 D.heta1

theorem game_original_value : (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor m hrare).F=valueLaw P := rfl

theorem game_original_joint :
    (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor m hrare).F ⊗ₘ (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor m hrare).σ=(joint D P t ht πL π upperBid hupperBid : Measure (ℝ×JointAction 2)) :=
  OrderedNativeSourcePosterior.game_original_joint (regions D P hdR H hUH) P rfl t ht.le πL
    (partialLaw D P t ht π) (active D P t ht π)
    upperBid hupperBid hfloor m D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 hrare
    (base_duplicate_gap D) D.eta D.heta0 D.heta1

theorem game_original_user :
    userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor m hrare)=(joint D P t ht πL π upperBid hupperBid : Measure (ℝ×JointAction 2)).prod (permLaw 2) := by
  rw [userLaw,game_original_joint]

theorem game_original_iid :
    userProfileLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor m hrare)=Measure.pi (fun _ : Fin m =>
      (joint D P t ht πL π upperBid hupperBid : Measure (ℝ×JointAction 2)).prod (permLaw 2)) := by
  simp only [userProfileLaw,game_original_user]

theorem joint_active_components :
    ENNReal.ofReal (activeMass P.theta-(activeMass P.theta*P.zeta*powerTail P.M 10 t)) •
      (bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl (P.originalMovingActiveLaw t ht.le)
        (active D P t ht π) : Measure (ℝ×JointAction 2)) =
      ENNReal.ofReal P.bulkWeight •
        (bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl P.originalBulkLaw (π 0) : Measure (ℝ×JointAction 2))+
      ENNReal.ofReal (P.truncatedTailWeight t) •
        (bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl
          (P.originalTruncatedTailLaw t ht) (π 1) : Measure (ℝ×JointAction 2)) :=
  ActiveJointMerge.weighted_bandJoint_merged P t ht D.u D.U D.huU (π 0) (π 1)

include hfloor in
theorem source_bands :
    ∀ᵐ x ∂(joint D P t ht πL π upperBid hupperBid : Measure (ℝ×JointAction 2)),
      OriginalPopulation.sourceBands P (regions D P hdR H hUH) t x :=
  originalJoint_sourceBands P (regions D P hdR H hUH) rfl t ht.le πL (partialLaw D P t ht π)
    (active D P t ht π) upperBid hupperBid hfloor

variable (hcoef : (1-D.eta)/2=D.ξ)

def posterior : PosteriorSystem (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor m hrare) :=
  OrderedNativeSourceAllFeasible.nativeAllListPosterior (regions D P hdR H hUH) P rfl t ht.le πL
    (partialLaw D P t ht π) (active D P t ht π)
    upperBid hupperBid hfloor m D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 hrare
    (base_duplicate_gap D) D.eta D.heta0 D.heta1 hcoef

theorem proposer_optimal (hlow : P.d0<1-D.ξ) :
    PosteriorProposerOptimal (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor m hrare)
      (posterior D P t ht hdR H hUH πL π upperBid hupperBid hfloor m hrare hcoef) :=
  OrderedNativeSourceAllFeasible.native_all_list_optimal (regions D P hdR H hUH) P rfl t ht.le πL
    (partialLaw D P t ht π) (active D P t ht π)
    upperBid hupperBid hfloor m D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 hrare
    (base_duplicate_gap D) D.eta D.heta0 D.heta1 hcoef hlow

include ht in
theorem rare_guard_of_physical
    (hphys : (1-D.ξ)*D.B+D.ξ*D.B*((m:ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ D.R) :
    (1-D.ξ)*D.U+D.ξ*D.U*((m:ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ D.R := by
  have hz : 0≤ (activeMass P.theta*P.zeta*powerTail P.M 10 t) := P.tailMass_nonneg t ht.le
  have hp : 0≤(m:ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))) := mul_nonneg (Nat.cast_nonneg _)
    (div_nonneg hz (add_nonneg (by norm_num [partialMass]) hz))
  exact le_trans
    (add_le_add
      (mul_le_mul_of_nonneg_left (base_active_le_physical D) (sub_nonneg.mpr D.hξ1.le))
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (base_active_le_physical D) D.hξ.le) hp)) hphys

end FCAppendix.Affine.Tail04.OrderedNativeZeroNoiseSource
