import FCAppendix.Affine.Tail04.EqualPrivateActiveRelabel
import FCAppendix.Affine.Tail04.EqualNoisyUtilities

noncomputable section
namespace FCAppendix.Affine.Tail04.EqualPrivateFiniteLoss
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal EqualPrivateFrontier EqualPrivateContinuity
open EqualPrivateActiveRelabel EqualNoisyUtilities
open scoped BigOperators

local instance (N H : ℕ) : TopologicalSpace (Finset (Target N H)) := ⊥
local instance (N H : ℕ) : DiscreteTopology (Finset (Target N H)) := ⟨rfl⟩
local instance (N H : ℕ) : MeasurableSpace (Finset (Target N H)) := ⊤
local instance (N H : ℕ) : BorelSpace (Finset (Target N H)) := ⟨borel_eq_top_of_discrete.symm⟩

theorem policyMean_own_bid_lipschitz {N H c : ℕ} {R Rp ξ B : ℝ}
    (hξ : 0< ξ) (hξ1 : ξ≤1) (μ : WeakProbability.Law (Signal H R Rp))
    (b d : Fin N → Icc (1:ℝ) B) (i : Fin N) (hother : ∀ j,j≠i → d j=b j) :
    |policyMean N H c R Rp ξ 1 B (b,μ) i-policyMean N H c R Rp ξ 1 B (d,μ) i|≤
      |(b i:ℝ)-(d i:ℝ)|/ξ := by
  let x := activeIndicator N H c R Rp
  let r := privateReceipt N H c R Rp
  let π := chosenPlan x r ξ (EqualPrivateMeasurable.forget (b,μ))
  let τ := chosenPlan x r ξ (EqualPrivateMeasurable.forget (d,μ))
  have hp := integralOptimal_of_gap_eq_zero x r _ ξ (WeakProbability.toMeasure μ) π
    (chosenPlan_gap x r ξ (EqualPrivateMeasurable.forget (b,μ)))
  have ht := integralOptimal_of_gap_eq_zero x r _ ξ (WeakProbability.toMeasure μ) τ
    (chosenPlan_gap x r ξ (EqualPrivateMeasurable.forget (d,μ)))
  have h := own_bid_lipschitz (WeakProbability.toMeasure μ) x r
    (fun j => (b j:ℝ)) (fun j => (d j:ℝ)) ξ hξ hξ1 (fun j => (b j).2.1)
    activeIndicator_bounds i (fun j hj => congrArg Subtype.val (hother j hj)) π τ hp ht
  change |EqualPrivateMeasurable.q x r ξ 1 B (b,μ) i-
    EqualPrivateMeasurable.q x r ξ 1 B (d,μ) i|≤_
  rw [EqualPrivateMeasurable.q_eq_chosenMarginal x r ξ 1 B hξ (by norm_num),
    EqualPrivateMeasurable.q_eq_chosenMarginal x r ξ 1 B hξ (by norm_num)]
  exact h

def coinUtility (q v b eta : ℝ) : ℝ := (2*q-q^2)*v-(2*q+(eta-1)*q^2)*b

theorem countUtility_formula {N H c : ℕ} {R Rp ξ B eta : ℝ}
    (he0 : 0≤ eta) (he1 : eta≤1) (p : PolicyParameters N H R Rp 1 B)
    (i : Fin N) (v b : ℝ) :
    affineCountUtility (EqualPrivateCountPayoff.countLaw N H c R Rp ξ 1 B p i) v b eta he0 he1=
      coinUtility (policyMean N H c R Rp ξ 1 B p i) v b eta := by
  unfold EqualPrivateCountPayoff.countLaw affineCountUtility CountLaw.utility
  rw [twoCoinCountLaw_expect]
  simp only [userPayoff,Schedule.affine,Schedule.once,successIndicator]
  norm_num
  unfold coinUtility
  ring

lemma coinUtility_finite_loss {q q' eta v b y B : ℝ}
    (hq : q∈Icc (0:ℝ) 1) (hq' : q'∈Icc (0:ℝ) 1)
    (he0 : 0≤ eta) (he1 : eta≤1) (hv : 0≤ v) (hb : b∈Icc (0:ℝ) B) (hy : b≤ y) :
    coinUtility q v b eta-coinUtility q' v y eta≤
      (2*v+2*B)*|q-q'|+2*(y-b) := by
  let K := (2-q-q')*v-(2+(eta-1)*(q+q'))*b
  have hsum : 0≤ q+q' ∧ q+q'≤2 := by constructor <;> linarith [hq.1,hq.2,hq'.1,hq'.2]
  have hc0 : 0≤2+(eta-1)*(q+q') := by nlinarith [mul_nonneg he0 hsum.1]
  have hc1 : 2+(eta-1)*(q+q')≤2 := by nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : eta-1≤0) hsum.1]
  have hK : |K|≤2*v+2*B := by
    apply abs_le.mpr
    have h1 : 0≤(2-q-q')*v := mul_nonneg (by linarith) hv
    have h2 : (2-q-q')*v≤2*v := mul_le_mul_of_nonneg_right (by linarith : 2-q-q'≤2) hv
    have h3 : 0≤(2+(eta-1)*(q+q'))*b := mul_nonneg hc0 hb.1
    have h4 : (2+(eta-1)*(q+q'))*b≤2*B :=
      (mul_le_mul_of_nonneg_right hc1 hb.1).trans (mul_le_mul_of_nonneg_left hb.2 (by norm_num))
    constructor <;> dsimp [K] <;> linarith
  have hp : 2*q'+(eta-1)*q'^2≤2 := by
    have hh := mul_nonpos_of_nonpos_of_nonneg (by linarith : eta-1≤0) (sq_nonneg q')
    linarith [hq'.2]
  have hleft : (q-q')*K≤(2*v+2*B)*|q-q'| := by
    calc
      _ ≤ |(q-q')*K| := le_abs_self _
      _ = |q-q'| *|K| := abs_mul _ _
      _ ≤ |q-q'| *(2*v+2*B) := mul_le_mul_of_nonneg_left hK (abs_nonneg _)
      _ = _ := by ring
  have hright := mul_le_mul_of_nonneg_right hp (sub_nonneg.mpr hy)
  have he : coinUtility q v b eta-coinUtility q' v y eta=
      (q-q')*K+(2*q'+(eta-1)*q'^2)*(y-b) := by dsimp [coinUtility,K];ring
  rw [he]
  linarith

theorem countUtility_finite_loss {N H c : ℕ} {R Rp ξ B eta : ℝ}
    (hξ : 0< ξ) (hξ1 : ξ≤1) (he0 : 0≤ eta) (he1 : eta≤1)
    (μ : WeakProbability.Law (Signal H R Rp))
    (b d : Fin N → Icc (1:ℝ) B) (i : Fin N) (hother : ∀ j,j≠i → d j=b j)
    (v : ℝ) (hv : 0≤ v) (hy : (b i:ℝ)≤(d i:ℝ)) :
    affineCountUtility (EqualPrivateCountPayoff.countLaw N H c R Rp ξ 1 B (b,μ) i)
        v (b i) eta he0 he1-
      affineCountUtility (EqualPrivateCountPayoff.countLaw N H c R Rp ξ 1 B (d,μ) i)
        v (d i) eta he0 he1≤
      ((2*v+2*B)/ξ+2)*((d i:ℝ)-(b i:ℝ)) := by
  rw [countUtility_formula,countUtility_formula]
  have hb0 : 0≤(b i:ℝ) := (by norm_num : (0:ℝ)≤1).trans (b i).2.1
  have hB : 0≤ B := hb0.trans (b i).2.2
  have h := coinUtility_finite_loss
    (policyMean_bounds N H c R Rp ξ 1 B (b,μ) i)
    (policyMean_bounds N H c R Rp ξ 1 B (d,μ) i)
    he0 he1 hv ⟨hb0,(b i).2.2⟩ hy
  have hq := policyMean_own_bid_lipschitz (c:=c) hξ hξ1 μ b d i hother
  rw [abs_of_nonpos (sub_nonpos.mpr hy),neg_sub] at hq
  have hm := mul_le_mul_of_nonneg_left hq (by positivity : 0≤2*v+2*B)
  calc
    _ ≤ (2*v+2*B)*(((d i:ℝ)-(b i:ℝ))/ξ)+2*((d i:ℝ)-(b i:ℝ)) := by linarith
    _ = _ := by ring

theorem sorted_countUtility_finite_loss {N H c : ℕ} {R Rp ξ B eta : ℝ}
    (hξ : 0< ξ) (hξ1 : ξ≤1) (he0 : 0≤ eta) (he1 : eta≤1)
    (μ : WeakProbability.Law (Signal H R Rp))
    (b d : Fin N → Icc (1:ℝ) B) (i : Fin N) (hother : ∀ j,j≠i → d j=b j)
    (v : ℝ) (hv : 0≤ v) (hy : (b i:ℝ)≤(d i:ℝ)) :
    affineCountUtility (EqualPrivateCountPayoff.countLaw N H c R Rp ξ 1 B
        (SortedAllNoise.sortedBox b,μ) (SortedAllNoise.focalRank (fun j => (b j:ℝ)) i))
        v (b i) eta he0 he1-
      affineCountUtility (EqualPrivateCountPayoff.countLaw N H c R Rp ξ 1 B
        (SortedAllNoise.sortedBox d,μ) (SortedAllNoise.focalRank (fun j => (d j:ℝ)) i))
        v (d i) eta he0 he1≤
      ((2*v+2*B)/ξ+2)*((d i:ℝ)-(b i:ℝ)) := by
  rw [countLaw_sorted hξ,countLaw_sorted hξ]
  exact countUtility_finite_loss hξ hξ1 he0 he1 μ b d i hother v hv hy

theorem physical_countUtility_finite_loss {N H c : ℕ} {R Rp ξ U eps eta : ℝ}
    (heps : 0≤ eps) (hξ : 0< ξ) (hξ1 : ξ≤1) (he0 : 0≤ eta) (he1 : eta≤1)
    (μ : ProbabilityMeasure (Signal H R Rp))
    (b d : Fin N → Icc (1:ℝ) U) (i : Fin N) (hother : ∀ j,j≠i → d j=b j)
    (v : ℝ) (hv : 0≤ v) (hy : (b i:ℝ)≤(d i:ℝ)) (z : Fin N → unitInterval) :
    affineCountUtility (EqualNoisyUtilities.rawCount (c:=c) heps ξ (b,μ) z i)
        v (physicalReal heps b z i) eta he0 he1-
      affineCountUtility (EqualNoisyUtilities.rawCount (c:=c) heps ξ (d,μ) z i)
        v (physicalReal heps d z i) eta he0 he1≤
      ((2*v+2*(U*(1+eps)))/ξ+2)*(1+eps)*((d i:ℝ)-(b i:ℝ)) := by
  have hfac0 : 0≤1+eps*(z i:ℝ) := by nlinarith [mul_nonneg heps (z i).2.1]
  have hfac1 : 1+eps*(z i:ℝ)≤1+eps := by nlinarith [(z i).2.2]
  have hphys : (physicalReal heps d z i)-(physicalReal heps b z i)=
      (1+eps*(z i:ℝ))*((d i:ℝ)-(b i:ℝ)) := by
    dsimp [physicalReal,physical,CompactSourceBidLaws.noisyBid,Hybrid.activeNoisyRealBid]
    ring
  have hp : physicalReal heps b z i≤ physicalReal heps d z i := by
    have h := mul_nonneg hfac0 (sub_nonneg.mpr hy)
    rw [←hphys] at h
    exact sub_nonneg.mp h
  have hother' (j : Fin N) (hj : j≠i) : physical heps d z j=physical heps b z j := by
    simp only [physical,hother j hj]
  have h := sorted_countUtility_finite_loss (c:=c) hξ hξ1 he0 he1
    (WeakProbability.mk μ) (physical heps b z) (physical heps d z) i hother' v hv hp
  change _≤((2*v+2*(U*(1+eps)))/ξ+2)*(physicalReal heps d z i-physicalReal heps b z i) at h
  rw [hphys] at h
  have hU : 0≤ U := (by norm_num : (0:ℝ)≤1).trans ((b i).2.1.trans (b i).2.2)
  have hC : 0≤(2*v+2*(U*(1+eps)))/ξ+2 := by positivity
  have hs := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hfac1 (sub_nonneg.mpr hy)) hC
  exact h.trans (by simpa only [mul_assoc] using hs)

end FCAppendix.Affine.Tail04.EqualPrivateFiniteLoss
