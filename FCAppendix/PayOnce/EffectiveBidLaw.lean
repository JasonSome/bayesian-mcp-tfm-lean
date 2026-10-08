import FCAppendix.PayOnce.EffectiveParticipation

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open PayOnce.CompactifiedBidLaws
variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_realEffectiveBidLaw_nonneg (Γ : FiniteGame m n c Seed) :
    ∀ᵐ b ∂(PayOnce.BidScaling.realBidLaw Γ : Measure ℝ), 0 ≤ b := by
  have hm : Measurable (fun d : UserDraw n => effectiveBid d.1.2) :=
    (measurable_effectiveBid n).comp (measurable_snd.comp measurable_fst)
  change ∀ᵐ b ∂(userLaw Γ).map (fun d => effectiveBid d.1.2), 0 ≤ b
  exact (ae_map_iff hm.aemeasurable (measurableSet_le measurable_const measurable_id)).mpr
    (Filter.Eventually.of_forall fun d => effectiveBid_nonneg d.1.2)

theorem realEffectiveBidLaw_positive_atomless (Γ : FiniteGame m (k+1) c Seed)
    (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hvalue : PositiveValueAtomless Γ)
    (hatom : PositiveVisibleAtomless Γ) {b : ℝ} (hb : 0 < b) :
    (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ) {b} = 0 := by
  have hm : Measurable (fun d : UserDraw (k+1) => effectiveBid d.1.2) :=
    (measurable_effectiveBid (k+1)).comp (measurable_snd.comp measurable_fst)
  change (Measure.map (fun d : UserDraw (k+1) => effectiveBid d.1.2) (userLaw Γ)) {b} = 0
  rw [Measure.map_apply hm (measurableSet_singleton b)]
  apply measure_eq_zero_iff_ae_notMem.mpr
  let j : Fin (k+1) := ⟨0,by omega⟩
  have he := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw (k+1))).quasiMeasurePreserving.ae
    (ae_effectiveBid_participation Γ hc hcm hA hG hu B hB hsym hvalue)
  have hz := measure_eq_zero_iff_ae_notMem.mp (hatom j b hb)
  filter_upwards [he,hz] with d hd hdz hdb
  have heb : effectiveBid d.1.2 = b := hdb
  have hpos : 0 < effectiveBid d.1.2 := heb ▸ hb
  have hr := hd.2.2 (hd.1.mp hpos)
  have hbraw : d.1.2.bid = b := by
    simpa only [effectiveBid,hr,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false] using heb
  apply hdz
  refine ⟨?_,hbraw⟩
  rw [hr,mem_firstK]
  exact Nat.succ_le_of_lt (d.2 j).isLt

theorem effectiveBid_profile_measurePreserving (Γ : FiniteGame m n c Seed) :
    MeasurePreserving (fun d : UserProfile m n => fun i => effectiveBid (d i).1.2)
      (userProfileLaw Γ) (Measure.pi (fun _ : Fin m => (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ))) := by
  have hm : Measurable (fun d : UserDraw n => effectiveBid d.1.2) :=
    (measurable_effectiveBid n).comp (measurable_snd.comp measurable_fst)
  exact measurePreserving_pi (fun _ : Fin m => userLaw Γ)
    (fun _ => (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ)) (fun _ => ⟨hm,rfl⟩)

theorem realEffectiveBidLaw_eq_action_map (Γ : FiniteGame m n c Seed) :
    (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ) = (Γ.F ⊗ₘ Γ.σ).map (fun x => effectiveBid x.2) := by
  have hp := measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw n)
  change (userLaw Γ).map (fun d => effectiveBid d.1.2) = _
  rw [← hp.map_eq,Measure.map_map
    (show Measurable (fun x : ℝ × JointAction n => effectiveBid x.2) from
      (measurable_effectiveBid n).comp measurable_snd) measurable_fst]
  rfl

theorem realEffectiveBidLaw_zero_mass (Γ : FiniteGame m (k+1) c Seed)
    (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hvalue : PositiveValueAtomless Γ) :
    (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ) {0} = Γ.F (Iic Γ.g) := by
  have hm : Measurable (fun d : UserDraw (k+1) => effectiveBid d.1.2) :=
    (measurable_effectiveBid (k+1)).comp (measurable_snd.comp measurable_fst)
  change (Measure.map (fun d : UserDraw (k+1) => effectiveBid d.1.2) (userLaw Γ)) {0} = _
  rw [Measure.map_apply hm (measurableSet_singleton 0)]
  have he := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw (k+1))).quasiMeasurePreserving.ae
    (ae_effectiveBid_participation Γ hc hcm hA hG hu B hB hsym hvalue)
  have heq : {d : UserDraw (k+1) | effectiveBid d.1.2 = 0} =ᵐ[userLaw Γ] {d | d.1.1 ≤ Γ.g} := by
    filter_upwards [he] with d hd
    apply propext
    constructor
    · intro hz
      apply le_of_not_gt
      intro hv
      have hp := hd.1.mpr hv
      rw [hz] at hp
      exact (lt_irrefl _ hp).elim
    · intro hv
      exact le_antisymm (le_of_not_gt fun hb => (not_lt_of_ge hv) (hd.1.mp hb)) (effectiveBid_nonneg d.1.2)
  change userLaw Γ {d | effectiveBid d.1.2 = 0} = Γ.F (Iic Γ.g)
  rw [measure_congr heq]
  rw [← userLaw_value_map Γ,Measure.map_apply
    (show Measurable (fun d : UserDraw (k+1) => d.1.1) from measurable_fst.comp measurable_fst) measurableSet_Iic]
  rfl

end FCAppendix.Bayes
