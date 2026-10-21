import FCAppendix.Affine.Tail04.NativeLowSourceIC
import FCAppendix.Affine.Tail04.OriginalMovingLow
import FCAppendix.Affine.Tail04.SourceTailNoisyFixedPoint

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceLowConstructor
open MeasureTheory ProbabilityTheory Set Classical Filter Topology
open OriginalValues LowBody NativeLowSourceIC

variable (P : ValueParameters)

theorem categories_eq_C1 (t : ℝ) (ht : P.M< t) :
    NativeLowSourceIC.categories P t ht.le=SourceTailNoisyFixedPoint.originalCategories P t ht := by
  apply FiniteLaw.ext
  intro k
  rw [NativeLowSourceIC.categories,categoryLaw_mass]
  simp only [SourceTailNoisyFixedPoint.originalCategories,
    SourceTailNoisyFixedPoint.tailMass,P.component_weight_sum t]

theorem moving_categories_exact (m : ℕ) (hM : P.M< movingThreshold m)
    (hm : OriginalMovingLow.mass P m=movingPrivateMass (activeMass P.theta) P.zeta P.M m) :
    OriginalMovingLow.categoryLaw P (OriginalMovingLow.originalLowRealLaw P) m=
      NativeLowSourceIC.categories P (movingThreshold m) hM.le := by
  have hz : OriginalMovingLow.mass P m=
      activeMass P.theta*P.zeta*powerTail P.M 10 (movingThreshold m) := by
    rw [hm,powerTail_ten P.M _ P.M_pos (P.M_pos.trans hM)]
    rfl
  unfold OriginalMovingLow.categoryLaw MovingLow.categories NativeLowSourceIC.categories
  apply FiniteLaw.ext
  intro k
  simp only [categoryLaw_mass,hz]

structure AtMarket (ξ : ℝ) (c : ℕ→ℕ) (m : ℕ) where
  market_large : 2< m
  threshold_large : P.M< movingThreshold m
  low : ActualAtomlessLowLimit (m-1) P.d0 ξ (c m)
    (NativeLowSourceIC.categories P (movingThreshold m) threshold_large.le) P.originalLowLaw
  underflow_pos : 0<(CommonList.iid
    (NativeLowSourceIC.categories P (movingThreshold m) threshold_large.le) (m-1)).prob
      (LocalUnderflow (c m) 0)
  double_underflow : (CommonList.iid
    (NativeLowSourceIC.categories P (movingThreshold m) threshold_large.le) (m-1)).prob
      (BothUnderflow (c m))≤
    (CommonList.iid (NativeLowSourceIC.categories P (movingThreshold m) threshold_large.le)
      (m-1)).prob (LocalUnderflow (c m) 0)/4

theorem eventually_construct (ξ : ℝ) (hξ : 0< ξ) (hξh : ξ≤1/2)
    (c : ℕ→ℕ) (hc : Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) atTop (𝓝 (99/200:ℝ)))
    (hgap : 2*Ample.binaryKL (99/200) (1-partialMass/2)<
      jointRate (lowMass P.theta) (activeMass P.theta) partialMass (99/200)) :
    ∀ᶠm : ℕ in atTop,Nonempty (AtMarket P ξ c m) := by
  have hlow:=OriginalMovingLow.eventually_exists_original_low P ξ hξ hξh c hc hgap
  have hrank : (99/200:ℝ)< activeMass P.theta+partialMass/2 := by
    have hθ:=P.theta_pos
    have hθs:=P.theta_small
    dsimp [activeMass,partialMass,delta]
    nlinarith
  have hg:=MovingLow.eventually_primitive_guards
    (lowMass P.theta) (activeMass P.theta) partialMass P.low_mass_pos P.active_mass_pos.le
    (by norm_num [partialMass]) (OriginalMovingLow.source_mass_sum P)
    (OriginalMovingLow.mass P) (OriginalMovingLow.mass_nonneg P) (OriginalMovingLow.mass_le_active P)
    (OriginalMovingLow.mass_tendsto P) (OriginalMovingLow.originalLowRealLaw P)
    c (99/200) 1 (by norm_num) hrank (by norm_num) hc hgap
  filter_upwards [hlow,hg,OriginalMovingLow.eventually_mass_original P,
    movingThreshold_tendsto.eventually_gt_atTop P.M] with m hl hg hm hM
  have hcat:=moving_categories_exact P m hM hm.1
  change 2< m ∧ 0< c m ∧ 0<(CommonList.iid
    (OriginalMovingLow.categoryLaw P (OriginalMovingLow.originalLowRealLaw P) m) (m-1)).prob
      (LocalUnderflow (c m) 0) ∧ _ at hg
  obtain ⟨L⟩ := hl.2
  have hL : ActualAtomlessLowLimit (m-1) P.d0 ξ (c m)
      (NativeLowSourceIC.categories P (movingThreshold m) hM.le) P.originalLowLaw := by
    rw [←hcat]
    exact L
  refine ⟨⟨hg.1,hM,hL,?_,?_⟩⟩
  · rw [←hcat]
    exact hg.2.2.1
  · rw [←hcat]
    exact hg.2.2.2.2.1

end FCAppendix.Affine.Tail04.SourceLowConstructor
