import FCAppendix.Affine.Uniform06.LiteralRankIC
import FCAppendix.Affine.Uniform06.ICSourceLocalAC

noncomputable section
namespace FCAppendix.Affine.Uniform06.LowRankMeasures

open MeasureTheory Set Filter Topology
open Rank LiteralExperiment LiteralPrefixStieltjes LiteralPrefixContinuity LiteralRankIC
open FCAppendix.Affine.Uniform07

def bidMeasure (i : Row) (G : Measure (ℝ × ℝ)) : Measure ℝ :=
  ENNReal.ofReal (cutoff i) • G.map Prod.snd

def lowBidMeasure (i : Row) (G : Measure (ℝ × ℝ)) (H : ℝ) : Measure ℝ :=
  (bidMeasure i G).restrict (Ioc (0:ℝ) H)

def lowJointMeasure (i : Row) (G : Measure (ℝ × ℝ)) (H : ℝ) : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (cutoff i) • G.restrict {p | p.2 ∈ Ioc (0:ℝ) H}

instance bidMeasure_finite (i : Row) (G : Measure (ℝ × ℝ)) [IsFiniteMeasure G] :
    IsFiniteMeasure (bidMeasure i G) := by
  unfold bidMeasure
  exact (G.map Prod.snd).smul_finite ENNReal.ofReal_ne_top

instance lowBidMeasure_finite (i : Row) (G : Measure (ℝ × ℝ)) [IsFiniteMeasure G] (H : ℝ) :
    IsFiniteMeasure (lowBidMeasure i G H) := by
  unfold lowBidMeasure
  infer_instance

instance lowJointMeasure_finite (i : Row) (G : Measure (ℝ × ℝ)) [IsFiniteMeasure G] (H : ℝ) :
    IsFiniteMeasure (lowJointMeasure i G H) := by
  unfold lowJointMeasure
  exact (G.restrict {p | p.2 ∈ Ioc (0:ℝ) H}).smul_finite ENNReal.ofReal_ne_top

theorem lowJoint_map_snd (i : Row) (G : Measure (ℝ × ℝ)) (H : ℝ) :
    (lowJointMeasure i G H).map Prod.snd=lowBidMeasure i G H := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_snd hA,lowJointMeasure,Measure.smul_apply,
    Measure.restrict_apply (measurable_snd hA),lowBidMeasure,
    Measure.restrict_apply hA,bidMeasure,Measure.smul_apply,
    Measure.map_apply measurable_snd (hA.inter measurableSet_Ioc)]
  congr 1

theorem lowJoint_ae (i : Row) (G : Measure (ℝ × ℝ)) (H : ℝ)
    {P : ℝ × ℝ → Prop} (hP : ∀ᵐ p ∂G, P p) :
    ∀ᵐ p ∂lowJointMeasure i G H, P p ∧ p.2 ∈ Ioc (0:ℝ) H := by
  unfold lowJointMeasure
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_of_ae hP,
    ae_restrict_mem (measurable_snd measurableSet_Ioc)] with p hp hband
  exact ⟨hp,hband⟩

theorem bidMeasure_real (i : Row) (G : Measure (ℝ × ℝ)) (A : Set ℝ) :
    (bidMeasure i G).real A=cutoff i*(G.map Prod.snd).real A := by
  simp only [bidMeasure,Measure.real,Measure.smul_apply,smul_eq_mul,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (cutoff_pos i).le]

theorem lowBidMeasure_real_Ioc (i : Row) (G : Measure (ℝ × ℝ)) {H a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ H) :
    (lowBidMeasure i G H).real (Ioc a b)=cutoff i*(G.map Prod.snd).real (Ioc a b) := by
  have hs : Ioc a b ⊆ Ioc (0:ℝ) H := fun x hx => ⟨ha.trans_lt hx.1,hx.2.trans hb⟩
  unfold lowBidMeasure
  rw [measureReal_restrict_apply measurableSet_Ioc,inter_eq_left.mpr hs]
  exact bidMeasure_real i G _

theorem lowBidMeasure_atomless (i : Row) (G : Measure (ℝ × ℝ))
    (hatom : ∀ b : ℝ, (G.map Prod.snd) {b}=0) (H b : ℝ) :
    lowBidMeasure i G H {b}=0 := by
  rw [lowBidMeasure,Measure.restrict_apply (measurableSet_singleton b)]
  apply measure_mono_null (show {b} ∩ Ioc (0:ℝ) H ⊆ {b} from inter_subset_left)
    (show bidMeasure i G {b}=0 by simp [bidMeasure,hatom b])

theorem PrefixConditions.mono {ξ K H : ℝ} {g : GuardData}
    (hg : PrefixConditions ξ g K) (hHK : H ≤ K) : PrefixConditions ξ g H :=
  ⟨hg.margin_pos,hg.population_pos,hg.radius_nonneg,hg.requiredDemand_pos,
    hg.rejectionScale_pos,hg.lower_pos,hg.seed_below_lower,
    hHK.trans hg.upper,hHK.trans hg.rejection,hg.radius_small⟩

def lowEnd (i : Row) : ℝ := cutoff i/2
def extensionEnd (i : Row) : ℝ := (501/1000:ℝ)*cutoff i

theorem lowEnd_bounds (i : Row) :
    0 < lowEnd i ∧ lowEnd i < extensionEnd i ∧
      extensionEnd i+cutoff i/10000 < entry i ∧ extensionEnd i < RankCutoff.Mstar i := by
  have h₁ : (501/1000:ℝ)+1/10000 < x i := by cases i <;> norm_num [x,xQ]
  have h₂ : (501/1000:ℝ) < x i+1/200 := by cases i <;> norm_num [x,xQ]
  have ht := cutoff_pos i
  unfold lowEnd extensionEnd entry RankCutoff.Mstar
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem lowEnd_below_cap (i : Row) : lowEnd i < ReceiptGap.cap i :=
  (lt_trans (lowEnd_bounds i).2.1 (by
    have ht := cutoff_pos i
    linarith [(lowEnd_bounds i).2.2.1])).trans (ReceiptGap.entry_below_cap i)

theorem source_bid_support (i : Row) (G : Measure (ℝ × ℝ))
    (hmenu : ∀ᵐ p ∂G, p.2 ∈ Icc (LowChernoff.physicalFloor i p.1)
      (min p.1 (ReceiptGap.cap i))) :
    ∀ᵐ b ∂G.map Prod.snd, b ∈ Icc (0:ℝ) (ReceiptGap.cap i) := by
  apply (ae_map_iff measurable_snd.aemeasurable measurableSet_Icc).mpr
  filter_upwards [hmenu] with p hp
  refine ⟨?_,hp.2.trans (min_le_right _ _)⟩
  have hz : 0 ≤ LowChernoff.physicalFloor i p.1 := by
    unfold LowChernoff.physicalFloor
    positivity
  exact hz.trans hp.1

end FCAppendix.Affine.Uniform06.LowRankMeasures
