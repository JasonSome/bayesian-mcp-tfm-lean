import FCAppendix.Affine.Uniform06.SourceCoarseIncrement
import FCAppendix.Affine.Uniform06.InactiveDeviation
import FCAppendix.Affine.Uniform06.LiteralPureComponents
import FCAppendix.Affine.Uniform06.LowInactiveIdentity

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralRemoteInactive
open MeasureTheory Set Filter Topology LowBody
open Uniform07 LiteralExperiment LiteralPrefixStieltjes LiteralRankIC
open LiteralPureComponents SourceRankRates PureRankCounts PureRankProbability
open SourceValueEnvelope EarlyCoarseUniform SourceCoarseIncrement

def gainConstant (i : Row) (τ Θ : ℝ) : ℝ :=
  Real.exp (-Θ)*τ*TiltedGood.stripMass i/(xi i*ReceiptGap.cap i)

theorem gainConstant_pos (i : Row) {τ Θ : ℝ} (hτ : 0 < τ) :
    0 < gainConstant i τ Θ := by
  unfold gainConstant
  exact div_pos (mul_pos (mul_pos (Real.exp_pos _) hτ) (TiltedGood.stripMass_pos i))
    (mul_pos (xi_pos i) (ReceiptGap.cap_bounds i).1)

attribute [local irreducible] sourceCanonicalMarginal sourceCanonicalDuplicate sourcePureSuccess sourcePureDuplicate

set_option maxHeartbeats 400000 in
theorem actual_positive_rent_contradiction (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hatom : ∀ b : ℝ,(G.map Prod.snd) {b}=0)
    (hactive : ∀ᵐ q ∂G,q.1 ∈ Ioc (EarlyRankCeiling.ceilingValue i) (cutoff i) →
      |q.2-ActiveGraphComponent.activeBid i q.1| ≤ cutoff i/10000)
    (g : GuardData) {K : ℝ} (hg : PrefixConditions (xi i) g K)
    (cm : (Fin (m-1) → Fin 4) → ℝ)
    (hcommon : ∀ᵐ q ∂G,q ∈ usedSet i m G g cm (ReceiptGap.cap i))
    {p : ℝ × ℝ} (hp : p ∈ usedSet i m G g cm (ReceiptGap.cap i))
    (hpK : p.1 < K) (hpEntry : p.1 < entry i) (hpLow : cutoff i/2 ≤ p.2)
    {ε A τ Θ : ℝ} (hε : 0 < ε) (hA : 0 < A) (hτ : 0 < τ)
    (hrent : ε ≤ p.1-p.2) (θ : ℝ → ℝ)
    (hcoarse : ∀ z ∈ Icc (p.2/cutoff i) ((p.2+ε/4)/cutoff i),
      θ z ∈ Icc τ Θ ∧
      SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i (z*cutoff i) G))
        Prod.fst (θ z)=(capacity m:ℝ)/((m-1:ℕ):ℝ) ∧
      1/A ≤ normalizedC i m G g cm z (θ z) ∧ normalizedC i m G g cm z (θ z) ≤ A ∧
      normalizedR i m G g cm z (θ z) ≤ A ∧ 0 ≤ normalizedR i m G g cm z (θ z))
    (hL : 0 < Lm i m)
    (hrare : LiteralLowDuplicate.pureRare m ≤ Real.exp (-(6/1000000:ℝ)*m)*Lm i m)
    (hpure : ∀ b > (0:ℝ), sourceRank (cutoff i) (G.map Prod.snd) b ≤ RankCutoff.Mstar i →
      Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)
        (sourceRank (cutoff i) (G.map Prod.snd) b)/2 ≤
          qPure (m-1) (capacity m) (kappa i) (cutoff i) (G.map Prod.snd) b)
    (hsmall : 40000/(m:ℝ)+cutoff i*Real.exp (-(6/1000000:ℝ)*m) ≤ ε/8)
    (hdup : cutoff i*A^2/((m-1:ℕ):ℝ) ≤ ε/2)
    (hgain : 4*cutoff i/ε < (1/A^2)*Real.exp (((m-1:ℕ):ℝ)*gainConstant i τ Θ*(ε/4))) :
    False := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let b := p.2
  let b' := b+ε/4
  let Q := Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) p.1
  let SP := sourcePureSuccess i m G
  let DP := sourcePureDuplicate i m G
  let C := sourceCanonicalMarginal i m G g cm
  let R := sourceCanonicalDuplicate i m G g cm
  let Z := fun a : ℝ => a/cutoff i
  have ht := cutoff_pos i
  have htne := ht.ne'
  have hz (a : ℝ) : Z a*cutoff i=a := div_mul_cancel₀ a htne
  have hb : 0 < b := hp.2.1
  have hbb : b < b' := by dsimp [b']; linarith
  have hbp : b' < p.1 := by dsimp [b',b]; linarith
  have hbpK : b' < K := hbp.trans hpK
  have hbentry : b' < entry i := hbp.trans hpEntry
  have hpbv : b ≤ p.1 := hp.2.2.1.2.trans (min_le_left _ _)
  have hcap : ∀ᵐ q ∂G,q.2 ≤ ReceiptGap.cap i :=
    hcommon.mono fun q hq => hq.2.2.1.2.trans (min_le_right _ _)
  have hfloor : ∀ᵐ q ∂G,LowChernoff.physicalFloor i q.1 ≤ q.2 :=
    hcommon.mono fun q hq => hq.2.2.1.1
  have hpM : p.1 ≤ RankCutoff.Mstar i := by
    have he : entry i < RankCutoff.Mstar i := by
      unfold entry RankCutoff.Mstar
      nlinarith
    exact hpEntry.le.trans he.le
  have hrank := source_rank_identity_on_usedSet i hm G hvalue hatom g hg cm
    (ReceiptGap.cap i) hcommon p hp hpK
  have hLQ : Lm i m ≤ Q := by
    have hh := unilateral_le_pureRank ht.le (cutoff_lt_one i) (G.map Prod.snd)
      b (m-1) (capacity m)
    rwa [hrank] at hh
  have hQ : 0 < Q := hL.trans_le hLQ
  have hZ : Z b < Z b' := div_lt_div_of_pos_right hbb ht
  have hco := hcoarse (Z b) ⟨le_rfl,hZ.le⟩
  have hco' := hcoarse (Z b') ⟨hZ.le,le_rfl⟩
  have hc := source_bounds i (by omega) G g cm hA hco.2.2.1 hco.2.2.2.1
    hco.2.2.2.2.1 hco.2.2.2.2.2
  have hc' := source_bounds i (by omega) G g cm hA hco'.2.2.1 hco'.2.2.2.1
    hco'.2.2.2.2.1 hco'.2.2.2.2.2
  simp only [hz] at hc hc'
  have hC : 0 < C b := hc.1
  have hC' : 0 < C b' := hc'.1
  have hR : 0 ≤ R b := hc.2.1
  have hR' : 0 ≤ R b' := hc'.2.1
  have hDP := source_pure_duplicate_nonnegative_le_rare i hm G hvalue hfloor hb (hpbv.trans hpM)
  have hDP' := source_pure_duplicate_nonnegative_le_rare i hm G hvalue hfloor
    (hb.trans hbb) (hbp.le.trans hpM)
  have hPQ : Q/2 ≤ SP b := by
    have hh := hpure b hb (by rw [hrank]; exact hpM)
    rw [hrank] at hh
    exact hh.trans (source_pure_success_ge_qPure i m G b)
  have hqnon : 0 ≤ qPure (m-1) (capacity m) (kappa i) (cutoff i) (G.map Prod.snd) b' :=
    measureReal_nonneg
  have hSP' : 0 ≤ SP b' := hqnon.trans (source_pure_success_ge_qPure i m G b')
  have hrareQ : LiteralLowDuplicate.pureRare m ≤ Real.exp (-(6/1000000:ℝ)*m)*Q :=
    hrare.trans (mul_le_mul_of_nonneg_left hLQ (Real.exp_pos _).le)
  have hRsmall : cutoff i*R b ≤ ε*C b := by
    have hh := (div_le_iff₀ hC).mp hc.2.2.2.2.2
    change R b ≤ A^2/((m-1:ℕ):ℝ)*C b at hh
    have hh' := mul_le_mul_of_nonneg_left hh ht.le
    have hh'' := mul_le_mul_of_nonneg_right hdup hC.le
    ring_nf at hh' hh''
    nlinarith only [hh',hh'',mul_nonneg hε.le hC.le]
  have hRsmall' : cutoff i*R b' ≤ ε*C b'/2 := by
    have hh := (div_le_iff₀ hC').mp hc'.2.2.2.2.2
    change R b' ≤ A^2/((m-1:ℕ):ℝ)*C b' at hh
    have hh' := mul_le_mul_of_nonneg_left hh ht.le
    have hh'' := mul_le_mul_of_nonneg_right hdup hC'.le
    ring_nf at hh' hh''
    nlinarith only [hh',hh'']
  have hsmallRare : cutoff i*Real.exp (-(6/1000000:ℝ)*m) ≤ ε/8 := by
    have hz : 0 ≤ (40000:ℝ)/(m:ℝ) := by positivity
    linarith only [hsmall,hz]
  have hDPsmall : cutoff i*DP b ≤ ε*(1/2)*Q/4 := by
    have hh := mul_le_mul_of_nonneg_left (hDP.2.trans hrareQ) ht.le
    change cutoff i*DP b ≤ cutoff i*(Real.exp (-(6/1000000:ℝ)*m)*Q) at hh
    have hh' := mul_le_mul_of_nonneg_right hsmallRare hQ.le
    nlinarith only [hh,hh']
  have hE := actual_envelope_on_usedSet i hm G hvalue hatom g
    (ReceiptGap.cap_bounds i).1.le hg cm hcommon p hp hpK hpEntry.le hpM
  have hdecomp (a : ℝ) (ha : a ∈ Icc (0:ℝ) K) :=
    source_both_decompositions i m G g hg cm ha
  have hid (a : ℝ) (ha : a ∈ Icc (0:ℝ) K) :
      Rank.payoff (eta i) p.1 a (sourceSuccess i m G g cm a) (sourceDuplicate i m G g cm a)=
        InactiveDeviation.utility (eta i) p.1 a (SP a) (DP a) (C a) (R a) := by
    rw [(hdecomp a ha).1,(hdecomp a ha).2]
    rfl
  rw [hid b ⟨hb.le,hpbv.trans hpK.le⟩] at hE
  have henvelope : InactiveDeviation.utility (eta i) p.1 b (SP b) (DP b) (C b) (R b) ≤
      ε*(1/2)*Q/4+2*cutoff i*C b := by
    have hrare' := mul_le_mul_of_nonneg_left hrareQ hp.1.1
    have hpt := mul_le_mul_of_nonneg_right hp.1.2 (Real.exp_pos (-(6/1000000:ℝ)*m)).le
    have hpt' := mul_le_mul_of_nonneg_right hpt hQ.le
    have hcpt := mul_le_mul_of_nonneg_right hp.1.2 hC.le
    have hcoef := mul_le_mul_of_nonneg_right hsmall hQ.le
    have hpr := mul_nonneg hp.1.1 hR
    change InactiveDeviation.utility (eta i) p.1 b (SP b) (DP b) (C b) (R b) ≤
      40000/(m:ℝ)*Q+p.1*LiteralLowDuplicate.pureRare m+p.1*(2*C b-R b) at hE
    nlinarith only [hE,hrare',hpt',hcpt,hcoef,hpr]
  have hη0 := (eta_pos i).le
  have hη1 : eta i ≤ 1 := by cases i <;> norm_num [eta,etaQ]
  have hforce := InactiveDeviation.positive_rent_forces_canonical hη0 hη1 hb.le hε
    hrent hp.1.2 hQ.le (by norm_num : (0:ℝ) ≤ 1/2) hDP.1 hC.le hR
    (by nlinarith only [hPQ]) hDPsmall hRsmall henvelope
  have hDP'loss : cutoff i*DP b' ≤ cutoff i*C b := by
    have hh := mul_le_mul_of_nonneg_left (hDP'.2.trans hrareQ) ht.le
    change cutoff i*DP b' ≤ cutoff i*(Real.exp (-(6/1000000:ℝ)*m)*Q) at hh
    have hh' := mul_le_mul_of_nonneg_right hsmallRare hQ.le
    nlinarith only [hh,hh',hforce.1]
  have hamp := actual_increment i (by omega) G hvalue hcap hactive g cm hA hτ
    (by dsimp [Z]; apply (le_div_iff₀ ht).mpr; nlinarith [hpLow]) hZ
    (by rw [hz]; exact hbentry.le.trans (by unfold EarlyRankCeiling.prefixEnd; linarith))
    hco'.1 hco.2.1 hco.2.2 hco'.2.2
  have hdiff : (Z b'-Z b)*cutoff i=ε/4 := by
    dsimp [Z,b']
    field_simp [htne]
    ring
  rw [hz,hz,hdiff] at hamp
  have hratio : 4*cutoff i/ε < C b'/C b := hgain.trans_le hamp
  have hgrowth : 4*cutoff i*C b < ε*C b' := by
    have hh := (lt_div_iff₀ hC).mp hratio
    have hh' := mul_lt_mul_of_pos_left hh hε
    field_simp [hε.ne'] at hh'
    nlinarith only [hh']
  have hraised := InactiveDeviation.raised_bid_gain hη1 hb.le hε hrent hp.1.2 hSP'
    hDP'.1 hR' hC'.le hDP'loss hRsmall' hgrowth hforce.2
  have hfloor0 : LowChernoff.physicalFloor i p.1=0 :=
    source_floor_zero (hpEntry.le.trans (by linarith))
  have hlegal : b' ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i)) := by
    rw [hfloor0]
    exact ⟨(hb.trans hbb).le,le_min hbp.le (hbentry.le.trans (ReceiptGap.entry_below_cap i).le)⟩
  have hic := hp.2.2.2 b' hlegal
  rw [hid b' ⟨(hb.trans hbb).le,hbpK.le⟩,hid b ⟨hb.le,hpbv.trans hpK.le⟩] at hic
  exact (not_lt_of_ge hic) hraised

end FCAppendix.Affine.Uniform06.LiteralRemoteInactive
