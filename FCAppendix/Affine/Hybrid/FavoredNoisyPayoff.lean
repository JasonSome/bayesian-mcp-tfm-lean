import FCAppendix.Affine.Hybrid.FavoredValue
import FCAppendix.Affine.LowBody.NoisyPurePayoff
import Mathlib.MeasureTheory.Constructions.UnitInterval

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Topology
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def activeNoisyRealBid (eps : ℝ) (B : ℝ) (z : unitInterval) : ℝ := B*(1+eps*(z:ℝ))

lemma activeNoisyRealBid_mem {L U eps : ℝ} (hL : 0<L) (heps : 0≤eps)
    (B : Icc L U) (z : unitInterval) : activeNoisyRealBid eps B z∈Icc L (U*(1+eps)) := by
  have hB : 0≤(B:ℝ) := (hL.trans_le B.property.1).le
  have hz0 : 1≤1+eps*(z:ℝ) := by nlinarith [mul_nonneg heps z.property.1]
  have hz1 : 1+eps*(z:ℝ)≤1+eps := by nlinarith [z.property.2]
  constructor
  · exact B.property.1.trans (by simpa only [mul_one,activeNoisyRealBid] using mul_le_mul_of_nonneg_left hz0 hB)
  · exact (mul_le_mul_of_nonneg_left hz1 hB).trans
      (mul_le_mul_of_nonneg_right B.property.2 (by linarith))

lemma ae_activeNoisyRealBid_ne (eps B target : ℝ) (heps : eps≠0) (hB : B≠0) :
    ∀ᵐz : unitInterval ∂volume,activeNoisyRealBid eps B z≠target := by
  have hh:=LowBody.ae_affine_ne LowBody.uniformNoise (B*eps) B target (mul_ne_zero hB heps)
  have hcoe:=unitInterval.measurePreserving_coe.quasiMeasurePreserving.ae hh
  filter_upwards [hcoe] with z hz
  simpa only [activeNoisyRealBid,mul_add,mul_one,mul_assoc,add_comm] using hz

abbrev GuardedNoiseInput (ι : Type*) (vlo vhi L U eps : ℝ) :=
  (Icc vlo vhi × Icc L U) × (ι→Icc L (U*(1+eps)))

def guardedNoisyInput {vlo vhi L U : ℝ} (eps : ℝ) (i : ι)
    (t : GuardedNoiseInput ι vlo vhi L U eps) (z : unitInterval) : ℝ×(ι→ℝ) :=
  (t.1.1,Function.update (fun j=>(t.2 j:ℝ)) i (activeNoisyRealBid eps t.1.2 z))

omit [Fintype ι] in
lemma continuous_guardedNoisyInput {vlo vhi L U : ℝ} (eps : ℝ) (i : ι) (z : unitInterval) :
    Continuous (fun t : GuardedNoiseInput ι vlo vhi L U eps=>guardedNoisyInput eps i t z) := by
  have hv : Continuous (fun t : GuardedNoiseInput ι vlo vhi L U eps=>(t.1.1:ℝ)) := by fun_prop
  have hb : Continuous (fun t : GuardedNoiseInput ι vlo vhi L U eps=>fun j=>(t.2 j:ℝ)) :=
    continuous_boxBids.comp continuous_snd
  have hi : Continuous (fun t : GuardedNoiseInput ι vlo vhi L U eps=>
      activeNoisyRealBid eps t.1.2 z) := by unfold activeNoisyRealBid; fun_prop
  exact hv.prodMk (hb.update i hi)

omit [Fintype ι] in
lemma continuous_guardedNoisyInput_noise {vlo vhi L U : ℝ} (eps : ℝ) (i : ι)
    (t : GuardedNoiseInput ι vlo vhi L U eps) : Continuous (guardedNoisyInput eps i t) := by
  have hi : Continuous (fun z : unitInterval=>activeNoisyRealBid eps t.1.2 z) := by
    unfold activeNoisyRealBid
    fun_prop
  exact continuous_const.prodMk (continuous_const.update i hi)

omit [Fintype ι] in
lemma guardedNoisyInput_bid_mem {vlo vhi L U eps : ℝ} (hL : 0<L) (heps : 0≤eps)
    (i : ι) (t : GuardedNoiseInput ι vlo vhi L U eps) (z : unitInterval) (j : ι) :
    (guardedNoisyInput eps i t z).2 j∈Icc L (U*(1+eps)) := by
  by_cases hji : j=i
  · subst j
    simpa only [guardedNoisyInput,Function.update_self] using activeNoisyRealBid_mem hL heps t.1.2 z
  · simpa only [guardedNoisyInput,Function.update_of_ne hji] using (t.2 j).property

lemma ae_guardedNoisyInput_notie {vlo vhi L U eps : ℝ} (hL : 0<L) (heps : eps≠0)
    (i : ι) (t : GuardedNoiseInput ι vlo vhi L U eps) :
    ∀ᵐz : unitInterval ∂volume,∀j,j≠i→(guardedNoisyInput eps i t z).2 j≠
      (guardedNoisyInput eps i t z).2 i := by
  have hB : (t.1.2:ℝ)≠0 := (hL.trans_le t.1.2.property.1).ne'
  have hh (j : ι) : ∀ᵐz : unitInterval ∂volume,j≠i→
      (guardedNoisyInput eps i t z).2 j≠(guardedNoisyInput eps i t z).2 i := by
    filter_upwards [ae_activeNoisyRealBid_ne eps t.1.2 (t.2 j) heps hB] with z hz hji
    simpa only [guardedNoisyInput,Function.update_self,Function.update_of_ne hji] using hz.symm
  exact ae_all_iff.mpr hh

def guardedNoisyPayoff [Nonempty ι] {vlo vhi L U : ℝ} (xi eta eps : ℝ)
    (r K1 K2 : ℕ) (i : ι) (t : GuardedNoiseInput ι vlo vhi L U eps) (z : unitInterval) : ℝ :=
  sourceOwnerPayoff xi eta (guardedNoisyInput eps i t z).1
    (guardedNoisyInput eps i t z).2 r K1 K2 i

def guardedSmoothedPayoff [Nonempty ι] {vlo vhi L U : ℝ} (xi eta eps : ℝ)
    (r K1 K2 : ℕ) (i : ι) (t : GuardedNoiseInput ι vlo vhi L U eps) : ℝ :=
  ∫z : unitInterval,guardedNoisyPayoff xi eta eps r K1 K2 i t z

lemma measurable_guardedNoisyPayoff [Nonempty ι] {vlo vhi L U : ℝ} (xi eta eps : ℝ)
    (r K1 K2 : ℕ) (i : ι) (t : GuardedNoiseInput ι vlo vhi L U eps) :
    Measurable (guardedNoisyPayoff xi eta eps r K1 K2 i t) :=
  (measurable_joint_sourceOwnerPayoff xi eta r K1 K2 i).comp
    (continuous_guardedNoisyInput_noise eps i t).measurable

theorem continuous_guardedSmoothedPayoff [Nonempty ι] {vlo vhi L U eps : ℝ}
    (hL : 0<L) (heps : 0<eps) (xi eta : ℝ) (r K1 K2 : ℕ) (i : ι)
    (hN : 2≤Fintype.card ι) (hK0 : 0<K1+K2) (hKN : K1+K2<Fintype.card ι) :
    Continuous (guardedSmoothedPayoff (vlo:=vlo) (vhi:=vhi) (L:=L) (U:=U)
      xi eta eps r K1 K2 i) := by
  obtain ⟨C,hC⟩:=exists_joint_sourceOwnerPayoff_box_bound (U:=U*(1+eps))
    (vlo:=vlo) (vhi:=vhi) hL xi eta r K1 K2 i hN hK0 hKN
  rw [continuous_iff_continuousAt]
  intro t
  apply MeasureTheory.continuousAt_of_dominated
    (F:=guardedNoisyPayoff xi eta eps r K1 K2 i) (bound:=fun _=>C)
    (Eventually.of_forall (fun s=>(measurable_guardedNoisyPayoff xi eta eps r K1 K2 i s).aestronglyMeasurable))
    ?_ (integrable_const C) ?_
  · exact Eventually.of_forall (fun s=>Eventually.of_forall (fun z=>
      hC s.1.1 s.1.1.property _ (guardedNoisyInput_bid_mem hL heps.le i s z)))
  · filter_upwards [ae_guardedNoisyInput_notie hL heps.ne' i t] with z hz
    exact (continuousAt_joint_sourceOwnerPayoff xi eta r K1 K2 i hN hK0 hKN
      (guardedNoisyInput eps i t z)
      (fun j=>hL.trans_le (guardedNoisyInput_bid_mem hL heps.le i t z j).1) hz).comp
      (f:=fun s=>guardedNoisyInput eps i s z) (continuous_guardedNoisyInput eps i z).continuousAt

end FCAppendix.Affine.Hybrid
