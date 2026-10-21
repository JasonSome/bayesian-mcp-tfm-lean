import FCAppendix.Affine.Tail04.NativeNoisySource
import FCAppendix.Affine.Tail04.NativeNoisyBindings

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeZeroNoiseSource
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

local notation "E" => regions D P hdR H hUH

local instance movingActiveProbability (Q : ValueParameters) (s : ℝ) (hs : Q.M<s) :
    IsProbabilityMeasure (Q.originalMovingActiveLaw s hs.le) :=
  Q.originalMovingActiveLaw_probability s hs.le

def active (π : JointProfile D P t ht) :
    Law (A:=Icc (1:ℝ) D.U) (P.originalMovingActiveLaw t ht.le) :=
  ActiveJointMerge.mergedActiveLaw P t ht D.u D.U D.huU (π 0) (π 1)

def «partial» (π : JointProfile D P t ht) :
    Law (A:=Icc D.R D.Up) P.originalPartialLaw := π 2

variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (π : JointProfile D P t ht)
    (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
    (hfloor : ∀ v,t< v→ H≤ upperBid v) (m : ℕ)

local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
local notation "pH" => z/(partialMass+z)
variable (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((m:ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ D.R)

def joint : ProbabilityMeasure (ℝ×JointAction 2) :=
  originalJoint P t ht.le D.R D.Up D.U D.hR.le πL
    («partial» D P t ht π) (active D P t ht π) upperBid hupperBid

theorem joint_value :
    (ProbabilityMeasure.toMeasure (joint D P t ht πL π upperBid hupperBid)).map Prod.fst=valueLaw P :=
  originalJoint_value P t ht.le D.R D.Up D.U D.hR.le πL
    («partial» D P t ht π) (active D P t ht π) upperBid hupperBid

def game : FiniteGame m 2 D.c NativeLocalPolicy.Seed :=
  NativeSourceAllFeasible.nativeGame E P rfl t ht.le πL
    («partial» D P t ht π) (active D P t ht π)
    upperBid hupperBid hfloor m D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 hrare
    (base_duplicate_gap D) D.eta D.heta0 D.heta1

local notation "Γ" => game D P t ht hdR H hUH πL π upperBid hupperBid hfloor m hrare

theorem game_original_value : (Γ).F=valueLaw P := rfl

theorem game_original_joint :
    (Γ).F⊗ₘ(Γ).σ=(ProbabilityMeasure.toMeasure (joint D P t ht πL π upperBid hupperBid)) :=
  NativeSourcePosterior.game_original_joint E P rfl t ht.le πL
    («partial» D P t ht π) (active D P t ht π)
    upperBid hupperBid hfloor m D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 hrare
    (base_duplicate_gap D) D.eta D.heta0 D.heta1

theorem game_original_user :
    userLaw Γ=(ProbabilityMeasure.toMeasure (joint D P t ht πL π upperBid hupperBid)).prod (permLaw 2) := by
  rw [userLaw,game_original_joint]

theorem game_original_iid :
    userProfileLaw Γ=Measure.pi (fun _ : Fin m =>
      (ProbabilityMeasure.toMeasure (joint D P t ht πL π upperBid hupperBid)).prod (permLaw 2)) := by
  simp only [userProfileLaw,game_original_user]

theorem joint_active_components :
    ENNReal.ofReal (activeMass P.theta-z) •
      (ProbabilityMeasure.toMeasure (@bandJoint (P.vA-P.w) t 1 D.U (by norm_num : (0:ℝ)≤1) 2 le_rfl
        (P.originalMovingActiveLaw t ht.le) (P.originalMovingActiveLaw_probability t ht.le)
        (active D P t ht π))) =
      ENNReal.ofReal P.bulkWeight •
        (ProbabilityMeasure.toMeasure (bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl P.originalBulkLaw (π 0)))+
      ENNReal.ofReal (P.truncatedTailWeight t) •
        (ProbabilityMeasure.toMeasure (bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl
          (P.originalTruncatedTailLaw t ht) (π 1))) :=
  ActiveJointMerge.weighted_bandJoint_merged P t ht D.u D.U D.huU (π 0) (π 1)

include hfloor in
theorem source_bands :
    ∀ᵐ x ∂(ProbabilityMeasure.toMeasure (joint D P t ht πL π upperBid hupperBid)),
      OriginalPopulation.sourceBands P E t x :=
  originalJoint_sourceBands P E rfl t ht.le πL («partial» D P t ht π)
    (active D P t ht π) upperBid hupperBid hfloor

variable (hcoef : (1-D.eta)/2=D.ξ)

def posterior : PosteriorSystem Γ :=
  NativeSourceAllFeasible.nativeAllListPosterior E P rfl t ht.le πL
    («partial» D P t ht π) (active D P t ht π)
    upperBid hupperBid hfloor m D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 hrare
    (base_duplicate_gap D) D.eta D.heta0 D.heta1 hcoef

theorem proposer_optimal (hlow : P.d0<1-D.ξ) :
    PosteriorProposerOptimal Γ
      (posterior D P t ht hdR H hUH πL π upperBid hupperBid hfloor m hrare hcoef) :=
  NativeSourceAllFeasible.native_all_list_optimal E P rfl t ht.le πL
    («partial» D P t ht π) (active D P t ht π)
    upperBid hupperBid hfloor m D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 hrare
    (base_duplicate_gap D) D.eta D.heta0 D.heta1 hcoef hlow

include ht in
theorem rare_guard_of_physical
    (hphys : (1-D.ξ)*D.B+D.ξ*D.B*((m:ℝ)*pH)≤ D.R) :
    (1-D.ξ)*D.U+D.ξ*D.U*((m:ℝ)*pH)≤ D.R := by
  have hz : 0≤ z := P.tailMass_nonneg t ht.le
  have hp : 0≤(m:ℝ)*pH := mul_nonneg (Nat.cast_nonneg _)
    (div_nonneg hz (add_nonneg (by norm_num [partialMass]) hz))
  exact le_trans
    (add_le_add
      (mul_le_mul_of_nonneg_left (base_active_le_physical D) (sub_nonneg.mpr D.hξ1.le))
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (base_active_le_physical D) D.hξ.le) hp)) hphys

end FCAppendix.Affine.Tail04.NativeZeroNoiseSource
