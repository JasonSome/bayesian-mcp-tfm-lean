import FCAppendix.Affine.Tail04.SourceTailNoisyFixedPoint
import FCAppendix.Affine.Tail04.ActiveJointMerge
import FCAppendix.Affine.Tail04.NativeSourceAllFeasible
import FCAppendix.Affine.Tail04.NoisyPrivateLaws

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeNoisySource
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint FiniteTailNoisyGame

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)

def bulkBase (π : JointProfile D P t ht) :
    Law (A:=Icc (1:ℝ) (1+D.u)) P.originalBulkLaw := π 0

def tailBase (π : JointProfile D P t ht) :
    Law (A:=Icc (1:ℝ) D.U) (P.originalTruncatedTailLaw t ht) := π 1

def partialBase (π : JointProfile D P t ht) :
    Law (A:=Icc D.R D.Up) P.originalPartialLaw := π 2

def bulkPhysicalWidth (D : Data) : ℝ := (1+D.u)*(1+D.eps)-1

lemma one_add_bulkPhysicalWidth :
    1+bulkPhysicalWidth D=(1+D.u)*(1+D.eps) := by
  unfold bulkPhysicalWidth
  ring

lemma bulkPhysicalWidth_nonneg : 0≤ bulkPhysicalWidth D := by
  unfold bulkPhysicalWidth
  nlinarith [D.hu,D.heps,mul_nonneg D.hu D.heps.le]

include D in
lemma bulkPhysicalWidth_le : 1+bulkPhysicalWidth D≤ D.B := by
  rw [one_add_bulkPhysicalWidth]
  exact mul_le_mul_of_nonneg_right D.huU (by linarith [D.heps])

include D in
lemma physical_one_le : 1≤ D.B := by
  exact (show (1:ℝ)≤1+bulkPhysicalWidth D by
    linarith [bulkPhysicalWidth_nonneg D]).trans (bulkPhysicalWidth_le D)

def bulkPhysical (π : JointProfile D P t ht) :
    Law (A:=Icc (1:ℝ) (1+bulkPhysicalWidth D)) P.originalBulkLaw := by
  rw [one_add_bulkPhysicalWidth]
  exact Hybrid.activeNoisyLaw (by norm_num : (0:ℝ)<1) D.heps.le
    P.originalBulkLaw (bulkBase D P t ht π)

def tailPhysical (π : JointProfile D P t ht) :
    Law (A:=Icc (1:ℝ) D.B) (P.originalTruncatedTailLaw t ht) :=
  Hybrid.activeNoisyLaw (by norm_num : (0:ℝ)<1) D.heps.le
    (P.originalTruncatedTailLaw t ht) (tailBase D P t ht π)

def partialPhysical (π : JointProfile D P t ht) :
    Law (A:=Icc D.R D.V) P.originalPartialLaw :=
  Hybrid.activeNoisyLaw D.hR D.heps.le P.originalPartialLaw
    (partialBase D P t ht π)

local instance movingActive_probability (hle : P.M ≤ t) :
    IsProbabilityMeasure (P.originalMovingActiveLaw t hle) :=
  P.originalMovingActiveLaw_probability t hle

def activePhysical (π : JointProfile D P t ht) :
    Law (A:=Icc (1:ℝ) D.B) (P.originalMovingActiveLaw t ht.le) :=
  ActiveJointMerge.mergedActiveLaw P t ht (bulkPhysicalWidth D) D.B
    (bulkPhysicalWidth_le D) (bulkPhysical D P t ht π) (tailPhysical D P t ht π)

variable (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)

def regions : Observable.Regions where
  d:=P.d0
  R:=D.R
  Rp:=D.V
  U:=D.B
  H:=H
  d_nonneg:=P.d0_pos.le
  d_lt_R:=hdR
  R_le_Rp:=by
    have hU : 0≤ D.Up := D.hR.le.trans D.hRUp
    dsimp [Data.V]
    nlinarith [mul_nonneg hU D.heps.le,D.hRUp]
  Rp_lt_one:=D.hRp
  one_le_U:=physical_one_le D
  U_lt_H:=hBH

variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (π : JointProfile D P t ht)
    (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
    (hfloor : ∀ v,t< v → H≤ upperBid v)
    (m : ℕ)

variable (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((m:ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ D.R)

lemma duplicate_gap : (1-D.ξ)*D.B<1 := by
  have hUp : D.Up≤ D.Up*(1+D.eps) := by
    have hn : 0≤ D.Up := D.hR.le.trans D.hRUp
    nlinarith [mul_nonneg hn D.heps.le]
  exact D.hgap.trans (D.hRUp.trans hUp |>.trans_lt D.hRp)

def joint : ProbabilityMeasure (ℝ×JointAction 2) :=
  originalJoint P t ht.le D.R D.V D.B D.hR.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π) upperBid hupperBid

def game : FiniteGame m 2 D.c NativeLocalPolicy.Seed :=
  NativeSourceAllFeasible.nativeGame (regions D P hdR H hBH) P rfl t ht.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π)
    upperBid hupperBid hfloor m D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 hrare
    (duplicate_gap D) D.eta D.heta0 D.heta1

theorem game_original_value : (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor m hrare).F=valueLaw P := rfl

theorem game_original_joint :
    (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor m hrare).F ⊗ₘ (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor m hrare).σ=(joint D P t ht πL π upperBid hupperBid : Measure (ℝ×JointAction 2)) := by
  exact NativeSourcePosterior.game_original_joint (regions D P hdR H hBH) P rfl t ht.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π)
    upperBid hupperBid hfloor m D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 hrare
    (duplicate_gap D) D.eta D.heta0 D.heta1

theorem game_original_user :
    userLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor m hrare)=(joint D P t ht πL π upperBid hupperBid : Measure (ℝ×JointAction 2)).prod (permLaw 2) := by
  rw [userLaw,game_original_joint]

theorem game_original_iid :
    userProfileLaw (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor m hrare)=Measure.pi (fun _ : Fin m =>
      (joint D P t ht πL π upperBid hupperBid : Measure (ℝ×JointAction 2)).prod (permLaw 2)) := by
  simp only [userProfileLaw,game_original_user]

theorem joint_active_components :
    ENNReal.ofReal (activeMass P.theta-(activeMass P.theta*P.zeta*powerTail P.M 10 t)) •
      (bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl (P.originalMovingActiveLaw t ht.le)
        (activePhysical D P t ht π) : Measure (ℝ×JointAction 2)) =
      ENNReal.ofReal P.bulkWeight •
        (bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl P.originalBulkLaw
          (bulkPhysical D P t ht π) : Measure (ℝ×JointAction 2))+
      ENNReal.ofReal (P.truncatedTailWeight t) •
        (bandJoint (by norm_num : (0:ℝ)≤1) 2 le_rfl (P.originalTruncatedTailLaw t ht)
          (tailPhysical D P t ht π) : Measure (ℝ×JointAction 2)) :=
  ActiveJointMerge.weighted_bandJoint_merged P t ht (bulkPhysicalWidth D) D.B
    (bulkPhysicalWidth_le D) (bulkPhysical D P t ht π) (tailPhysical D P t ht π)

variable (hcoef : (1-D.eta)/2=D.ξ)

def posterior : PosteriorSystem (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor m hrare) :=
  NativeSourceAllFeasible.nativeAllListPosterior (regions D P hdR H hBH) P rfl t ht.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π)
    upperBid hupperBid hfloor m D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 hrare
    (duplicate_gap D) D.eta D.heta0 D.heta1 hcoef

theorem proposer_optimal (hlow : P.d0<1-D.ξ) :
    PosteriorProposerOptimal (game D P t ht hdR H hBH πL π upperBid hupperBid hfloor m hrare)
      (posterior D P t ht hdR H hBH πL π upperBid hupperBid hfloor m hrare hcoef) :=
  NativeSourceAllFeasible.native_all_list_optimal (regions D P hdR H hBH) P rfl t ht.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π)
    upperBid hupperBid hfloor m D.c D.ξ D.width D.regimeShare D.eA D.eR D.F
    D.hξ D.hξ1 D.hw D.regimeShare.2.1 D.regimeShare.2.2 hrare
    (duplicate_gap D) D.eta D.heta0 D.heta1 hcoef hlow

def provisionalUpper (D : Data) : ℝ → ℝ := fun _ => D.F+1

lemma provisionalUpper_measurable : Measurable (provisionalUpper D) := measurable_const

lemma provisionalUpper_gap : D.B< D.F+1 := lt_of_le_of_lt D.hUF (by linarith)

lemma provisionalUpper_floor (v : ℝ) : D.F+1≤ provisionalUpper D v := le_rfl

end FCAppendix.Affine.Tail04.NativeNoisySource
