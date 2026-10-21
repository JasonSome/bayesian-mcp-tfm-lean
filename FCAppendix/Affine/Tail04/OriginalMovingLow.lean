import FCAppendix.Affine.Tail04.MovingLowPrimitiveGuards
import FCAppendix.Affine.Tail04.OriginalValueSplits
import FCAppendix.Affine.Tail04.OriginalCompactLaws

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalMovingLow
open MeasureTheory ProbabilityTheory Set Filter Topology
open LowBody OriginalValues

variable (P : ValueParameters)

def mass (m : ℕ) : ℝ :=
  min (activeMass P.theta) (movingPrivateMass (activeMass P.theta) P.zeta P.M m)

theorem mass_nonneg (m : ℕ) : 0 ≤ mass P m :=
  le_min P.active_mass_pos.le
    (movingPrivateMass_nonneg _ _ _ _ P.active_mass_pos.le P.zeta_pos.le)

theorem mass_le_active (m : ℕ) : mass P m ≤ activeMass P.theta := min_le_left _ _

theorem raw_mass_tendsto :
    Tendsto (movingPrivateMass (activeMass P.theta) P.zeta P.M) atTop (𝓝 0) := by
  have hi := (tendsto_natCast_atTop_atTop :
    Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop).inv_tendsto_atTop
  have h := (hi.pow 2).const_mul (activeMass P.theta*P.zeta*P.M^10)
  convert! h using 1
  · funext m
    rw [movingPrivateMass_exact]
    simp only [div_eq_mul_inv,inv_pow,Pi.inv_apply]
  · norm_num

theorem mass_tendsto : Tendsto (mass P) atTop (𝓝 0) := by
  change Tendsto (fun m => min (activeMass P.theta) (movingPrivateMass (activeMass P.theta) P.zeta P.M m)) atTop (𝓝 0)
  simpa only [min_eq_right P.active_mass_pos.le] using
    ((tendsto_const_nhds (x := activeMass P.theta)).min (raw_mass_tendsto P))

theorem eventually_mass_original :
    ∀ᶠ m : ℕ in atTop,
      mass P m = movingPrivateMass (activeMass P.theta) P.zeta P.M m ∧
      mass P m = (P.movingUpperMeasure (movingThreshold m)).real univ := by
  have hsmall := (raw_mass_tendsto P).eventually_lt_const P.active_mass_pos
  have hM := movingThreshold_tendsto.eventually_ge_atTop P.M
  filter_upwards [hsmall,hM] with m hm hMm
  have he : mass P m = movingPrivateMass (activeMass P.theta) P.zeta P.M m :=
    min_eq_right hm.le
  exact ⟨he,he.trans (P.moving_mass_exact m hMm).symm⟩

theorem source_mass_sum :
    lowMass P.theta+activeMass P.theta+partialMass=1 := by
  linarith [mass_sum P.theta]

def categoryLaw (Gref : Measure ℝ) [IsProbabilityMeasure Gref] (m : ℕ) :
    FiniteLaw (Fin 4) :=
  MovingLow.categories (lowMass P.theta) (activeMass P.theta) partialMass
    P.low_mass_pos.le P.active_mass_pos.le (by norm_num [partialMass])
    (source_mass_sum P) (mass P) (mass_nonneg P) (mass_le_active P) Gref m

theorem eventually_source_masses :
    ∀ᶠ m : ℕ in atTop,
      (valueLaw P).real P.lowValues=lowMass P.theta ∧
      (valueLaw P).real (P.movingActiveValues (movingThreshold m))=
        activeMass P.theta-mass P m ∧
      (valueLaw P).real (P.privateValues (movingThreshold m))=
        partialMass+mass P m := by
  filter_upwards [eventually_mass_original P,
    movingThreshold_tendsto.eventually_ge_atTop P.M] with m hm hM
  refine ⟨P.low_mass,?_,?_⟩
  · rw [P.moving_active_mass _ hM,hm.1]
    rw [powerTail_ten P.M _ P.M_pos (P.M_pos.trans_le hM)]
    rfl
  · rw [P.private_mass _ hM,hm.1]
    rw [powerTail_ten P.M _ P.M_pos (P.M_pos.trans_le hM)]
    rfl

theorem eventually_exists_actual_low (xi : ℝ) (hxi : 0 < xi) (hxih : xi ≤ 1/2)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (c : ℕ → ℕ)
    (hc : Tendsto (fun m => (c m:ℝ)/(m:ℝ)) atTop (𝓝 (99/200:ℝ)))
    (hgap : 2*Ample.binaryKL (99/200) (1-partialMass/2) <
      jointRate (lowMass P.theta) (activeMass P.theta) partialMass (99/200))
    (mu : Measure (LowValue P.d0)) [IsProbabilityMeasure mu]
    (hmu : ∀ᵐ w ∂mu, 0 < w.1) :
    ∀ᶠ m : ℕ in atTop,
      mass P m=(P.movingUpperMeasure (movingThreshold m)).real univ ∧
      Nonempty (ActualAtomlessLowLimit (m-1) P.d0 xi (c m)
        (categoryLaw P Gref m) mu) := by
  have hrank : (99/200:ℝ) < activeMass P.theta+partialMass/2 := by
    have hp := P.theta_pos
    have hs := P.theta_small
    dsimp [activeMass,partialMass,delta]
    nlinarith
  have he := MovingLow.eventually_exists_actual_atomless_low_limit P.d0_pos.le
    hxi hxih (lowMass P.theta) (activeMass P.theta) partialMass P.low_mass_pos
    P.active_mass_pos.le (by norm_num [partialMass]) (source_mass_sum P)
    (mass P) (mass_nonneg P) (mass_le_active P) (mass_tendsto P) Gref c
    (99/200) (by norm_num) hrank hc hgap mu hmu
  filter_upwards [he,eventually_mass_original P] with m hm horiginal
  exact ⟨horiginal.2,hm⟩

def originalLowRealLaw : Measure ℝ := P.originalLowLaw.map Subtype.val

instance originalLowRealLaw_probability : IsProbabilityMeasure (originalLowRealLaw P) :=
  Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

theorem eventually_exists_original_low (xi : ℝ) (hxi : 0 < xi) (hxih : xi ≤ 1/2)
    (c : ℕ → ℕ)
    (hc : Tendsto (fun m => (c m:ℝ)/(m:ℝ)) atTop (𝓝 (99/200:ℝ)))
    (hgap : 2*Ample.binaryKL (99/200) (1-partialMass/2) <
      jointRate (lowMass P.theta) (activeMass P.theta) partialMass (99/200)) :
    ∀ᶠ m : ℕ in atTop,
      mass P m=(P.movingUpperMeasure (movingThreshold m)).real univ ∧
      Nonempty (ActualAtomlessLowLimit (m-1) P.d0 xi (c m)
        (categoryLaw P (originalLowRealLaw P) m) P.originalLowLaw) := by
  exact eventually_exists_actual_low P xi hxi hxih
    (originalLowRealLaw P) c hc hgap P.originalLowLaw P.originalLowLaw_positive

end FCAppendix.Affine.Tail04.OriginalMovingLow
