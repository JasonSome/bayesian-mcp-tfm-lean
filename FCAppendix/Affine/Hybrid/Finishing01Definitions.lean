import FCAppendix.Affine.Hybrid.ActiveNoisyCompactLimit
import FCAppendix.Affine.Hybrid.ActiveNoisyClusterIC
import FCAppendix.Affine.Hybrid.ActivePureCrossing
import FCAppendix.Affine.Hybrid.FavoredFiniteCrossing
import FCAppendix.Affine.Hybrid.SourceUniformMenus
import FCAppendix.Affine.Hybrid.ActivePatternCountBounds
import FCAppendix.Affine.Hybrid.ActivePhysicalPattern
import FCAppendix.Affine.LowBody.ActualLowBidEquilibrium
import FCAppendix.Affine.LowBody.BoundedNullWeakIntegral
import FCAppendix.Affine.Hybrid.ActiveMenuEndpointSigns
noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional
open scoped BigOperators

structure Primitives where
  s : ℝ
  a : ℝ
  h : ℝ
  rho : ℝ
  d : ℝ
  vlo : ℝ
  vhi : ℝ
  L : ℝ
  U : ℝ
  xi : ℝ
  z : ℝ
  s_pos : 0< s
  a_pos : 0< a
  h_pos : 0< h
  mass : s+a+h=1
  xi_pos : 0< xi
  xi_half : xi<1/2
  z_nonneg : 0≤ z
  z_lt_one : z<1
  d_nonneg : 0≤ d
  L_pos : 0< L
  value_order : vlo≤ vhi
  rho_lower : h/2< rho
  rho_upper : rho< a+h/2
  qbar_pos : 0< sourceExposure a h rho z
  qbar_lt_one : sourceExposure a h rho z<1
  box_lower : (1-xi)*U<(1-xi*sourceExposure a h rho z)*L
  box_upper : (1-xi*sourceExposure a h rho z)*U< L
  low_receipt : d<(1-xi)*L
  value_surplus : U< vlo
  inward_lower : L< inwardScale xi z (sourceExposure a h rho z)*vlo
  inward_upper : inwardScale xi z (sourceExposure a h rho z)*vhi< U
  low_rate_gap : 2*Ample.binaryKL rho (1-h/2)< LowBody.jointRate s a h rho

namespace Primitives
variable (P : Primitives)
def eta : ℝ:=1-2*P.xi
def kappa : ℝ:=1-P.xi
def qbar : ℝ:=sourceExposure P.a P.h P.rho P.z
def h0 : ℝ:=1-P.xi*P.qbar
abbrev Value := ActiveValue P.vlo P.vhi
abbrev Bid := ActiveBaseBid P.L P.U
abbrev Low := LowBody.LowValue P.d
lemma eta_pos : 0< P.eta := by dsimp [eta];linarith [P.xi_half]

lemma xi_lt_one : P.xi < 1 := by linarith [P.xi_half]
lemma kappa_pos : 0 < P.kappa := by dsimp [kappa]; linarith [P.xi_half]
lemma qbar_mem : P.qbar ∈ Ioo (0 : ℝ) 1 := ⟨P.qbar_pos,P.qbar_lt_one⟩
lemma h0_pos : 0 < P.h0 := by
  dsimp [h0]
  nlinarith [P.xi_pos,P.xi_lt_one,P.qbar_mem.2]
lemma h0_le_one : P.h0 ≤ 1 := by
  dsimp [h0]
  nlinarith [P.xi_pos,P.qbar_mem.1]
lemma scale_pos : 0 < inwardScale P.xi P.z P.qbar :=
  inwardScale_pos P.xi_pos P.xi_lt_one P.z_nonneg P.z_lt_one P.qbar_mem
lemma L_lt_U : P.L < P.U := by
  have h := mul_le_mul_of_nonneg_left P.value_order P.scale_pos.le
  exact P.inward_lower.trans_le (h.trans P.inward_upper.le)
lemma U_pos : 0 < P.U := P.L_pos.trans P.L_lt_U
lemma vlo_pos : 0 < P.vlo := P.U_pos.trans P.value_surplus
lemma value_pos (v : P.Value) : 0 < (v : ℝ) := P.vlo_pos.trans_le v.property.1
lemma bid_pos (b : P.Bid) : 0 < (b : ℝ) := P.L_pos.trans_le b.property.1
lemma eta_nonneg : 0 ≤ P.eta := P.eta_pos.le
lemma eta_le_one : P.eta ≤ 1 := by dsimp [eta]; linarith [P.xi_pos]
lemma kappa_U_lt_L : P.kappa * P.U < P.L := by
  have h := mul_le_mul_of_nonneg_right P.h0_le_one P.L_pos.le
  simpa only [kappa,one_mul] using P.box_lower.trans_le h

instance value_nonempty : Nonempty P.Value := ⟨⟨P.vlo,le_rfl,P.value_order⟩⟩
instance bid_nonempty : Nonempty P.Bid := ⟨⟨P.L,le_rfl,P.L_lt_U.le⟩⟩
instance low_nonempty : Nonempty P.Low := ⟨⟨0,le_rfl,P.d_nonneg⟩⟩

def categories : FiniteLaw (Fin 4):=
  LowBody.categoryLaw P.s P.a P.h P.s_pos.le P.a_pos.le P.h_pos.le P.mass (Measure.dirac (0:ℝ))

def exactUtility (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    (t : P.Value×P.Bid) : ℝ :=
  ∑kind : Fin N→ Fin 4,(CommonList.iid P.categories N).mass kind*
    ∫rows : (Fin N→ P.Low)×(Fin N→ P.Bid),
      activePhysicalPatternPayoff P.xi P.z P.L P.U c kind
        (t.1,t.2,(fun j=>(rows.1 j:ℝ)),fun j=>(rows.2 j:ℝ))
      ∂(productLaw (rowLaw N low) (rowLaw N (pi.1.map measurable_snd.aemeasurable)) :
        Measure ((Fin N→ P.Low)×(Fin N→ P.Bid)))
def reference (v lam b : ℝ) : ℝ:=
  P.z*(v-b)+(1-P.z)*independentTwo P.eta v b (exposure P.xi lam b)
def price (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu) : ℝ:=
  P.h0/(∫t : P.Value×P.Bid,((t.2:ℝ)⁻¹) ∂(pi.1 : Measure (P.Value×P.Bid)))

structure LowSourceState (M c : ℕ) (muLow : Measure P.Low) [IsProbabilityMeasure muLow] where
  witness : LowBody.ActualAtomlessLowLimit (M-1) P.d P.xi c P.categories muLow

def LowSourceState.bidLaw {M c : ℕ} {muLow : Measure P.Low} [IsProbabilityMeasure muLow]
    (A : P.LowSourceState M c muLow) : ProbabilityMeasure P.Low:=
  A.witness.joint.1.map measurable_snd.aemeasurable

structure FiniteLawSolution (M c : ℕ) (low : ProbabilityMeasure P.Low)
    (mu : Measure P.Value) [IsProbabilityMeasure mu] where
  joint : Law (A:=P.Bid) mu
  atomless : NullSingletonClass (joint.1.map measurable_snd.aemeasurable : Measure P.Bid)
  interior : ∃tau>0,∀ᵐt ∂(joint.1 : Measure (P.Value×P.Bid)),
    (t.2:ℝ)∈ Icc (P.L+tau) (P.U-tau)
  all_bid_IC : ∀ᵐt ∂(joint.1 : Measure (P.Value×P.Bid)),∀ B' : P.Bid,
    P.exactUtility (M-1) c low mu joint (t.1,B')≤ P.exactUtility (M-1) c low mu joint t

structure NoisyWitness (M c : ℕ) (low : ProbabilityMeasure P.Low)
    (mu : Measure P.Value) [IsProbabilityMeasure mu] where
  eps : ℕ→ unitInterval
  noisy : ℕ→ Law (A:=P.Bid) mu
  joint : Law (A:=P.Bid) mu
  eps_pos : ∀ j,0<(eps j:ℝ)
  eps_zero : Tendsto eps atTop (𝓝 0)
  joint_tendsto : Tendsto noisy atTop (𝓝 joint)
  physical_tendsto : Tendsto (fun j=> activeUniversalNoisyLaw P.L_pos
    P.L_lt_U.le mu (eps j,noisy j)) atTop
      (𝓝 (activeUniversalNoisyLaw P.L_pos P.L_lt_U.le mu (0,joint)))
  noisy_IC : ∀ j,∃sigma : Kernel P.Value P.Bid,IsMarkovKernel sigma ∧
    mu⊗ₘsigma=((noisy j).1 : Measure (P.Value×P.Bid)) ∧
    (∀ᵐv ∂mu,∀ᵐB ∂sigma v,∀ B' : P.Bid,
      activeNoisyExpectedUtility (N:=M-1) P.L_pos (eps j).property.1 P.xi P.z c P.categories low mu
        (noisy j,(v,B'))≤ activeNoisyExpectedUtility (N:=M-1) P.L_pos (eps j).property.1 P.xi P.z c
          P.categories low mu (noisy j,(v,B)))

theorem exists_noisyWitness (M c : ℕ) (low : ProbabilityMeasure P.Low)
    (mu : Measure P.Value) [IsProbabilityMeasure mu] : Nonempty (P.NoisyWitness M c low mu) := by
  obtain ⟨eps,pi,pi0,hpos,hzero,hIC,hlim,hphys⟩:=exists_actual_noisy_active_limit
    (N:=M-1) P.L_pos P.L_lt_U.le P.xi_pos (by linarith [P.xi_half])
    P.z c P.categories low mu
  exact ⟨⟨eps,pi,pi0,hpos,hzero,hlim,hphys,hIC⟩⟩
end Primitives

end FCAppendix.Affine.Hybrid.Finish01
