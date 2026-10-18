import FCAppendix.Exclusive.SourceStationaryGame
import FCAppendix.Exclusive.NonpositiveEntry
import FCAppendix.Exclusive.NarrowExistenceNativeUtility
import FCAppendix.Exclusive.NarrowExistenceNativeSampled

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter
open Exclusive.Narrow.Existence Exclusive.Narrow.Finite

def narrowPrimitive {eps : ℝ} (h : unitInterval) (H : ℝ)
    (nu : Measure (ValueBand eps)) : Measure ℝ :=
  twoBandLaw h (scaledHighLaw H nu) (Measure.dirac 0)

instance narrowPrimitive_probability {eps : ℝ} (h : unitInterval) (H : ℝ)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu] : IsProbabilityMeasure (narrowPrimitive h H nu) := by
  unfold narrowPrimitive
  infer_instance

theorem zero_not_bandHighSet {eps H : ℝ} (heps : eps < 1) (hH : 0 < H) :
    (0:ℝ) ∉ bandHighSet eps H := by
  have hp := mul_pos hH (sub_pos.mpr heps)
  intro hz
  exact (not_le_of_gt hp) hz.1

theorem narrowPrimitive_high_mass {eps H : ℝ} (h : unitInterval)
    (heps : eps < 1) (hH : 0 < H) (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu] :
    (narrowPrimitive h H nu).real (bandHighSet eps H) = (h:ℝ) := by
  apply twoBandLaw_high_mass h (scaledHighLaw H nu) (Measure.dirac 0) _ measurableSet_Icc
    (scaledHighLaw_supported hH nu)
  simpa only [bandHighSet, ae_dirac_eq, Filter.eventually_pure] using zero_not_bandHighSet heps hH

theorem narrowPrimitive_restrict_high {eps H : ℝ} (h : unitInterval)
    (heps : eps < 1) (hH : 0 < H) (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu] :
    (narrowPrimitive h H nu).restrict (bandHighSet eps H) =
      ENNReal.ofReal (h:ℝ) • scaledHighLaw H nu := by
  classical
  have hz : (Measure.dirac (0:ℝ)).restrict (bandHighSet eps H) = 0 := by
    rw [restrict_dirac, if_neg (zero_not_bandHighSet heps hH)]
  have hs : ∀ᵐ v ∂scaledHighLaw H nu, v ∈ bandHighSet eps H :=
    scaledHighLaw_supported hH nu
  rw [narrowPrimitive, twoBandLaw, Measure.restrict_add, Measure.restrict_smul,
    Measure.restrict_smul, Measure.restrict_eq_self_of_ae_mem hs, hz, smul_zero, add_zero]

theorem narrowPrimitive_restrict_high_atomless {eps H : ℝ} (h : unitInterval)
    (heps : eps < 1) (hH : 0 < H) (nu : Measure (ValueBand eps))
    [IsProbabilityMeasure nu] [NullSingletonClass nu] :
    NullSingletonClass ((narrowPrimitive h H nu).restrict (bandHighSet eps H)) := by
  rw [narrowPrimitive_restrict_high h heps hH nu]
  letI := scaledHighLaw_atomless hH nu
  constructor
  intro x
  simp only [Measure.smul_apply, smul_eq_mul, measure_singleton, mul_zero]

def narrowCanonicalGame (m d c : ℕ) (hd : 1 ≤ d) (hc : 0 < c)
    (h : unitInterval) {eps : ℝ} (heps : 0 ≤ eps) (H scale : ℝ)
    (beta : ValueBand eps → ℝ) (hbeta : Continuous beta)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu]
    (A G : Schedule (d+1)) (g : ℝ) (hg : 0 ≤ g) : FiniteGame m (d+1) c unitInterval :=
  canonicalGame m (d+1) c (by omega) hc (narrowPrimitive h H nu) (bandHighSet eps H) measurableSet_Icc
    (extendedSourceBid eps heps H scale beta)
    (continuous_extendedSourceBid eps heps H scale beta hbeta).measurable A G g hg

theorem narrowCanonicalGame_rival_action_law {m d c : ℕ}
    (hd : 1 ≤ d) (hc : 0 < c) (h : unitInterval) {eps : ℝ} (heps : 0 ≤ eps)
    (heps1 : eps < 1) {H : ℝ} (hH : 0 < H) (scale : ℝ)
    (beta : ValueBand eps → ℝ) (hbeta : Continuous beta)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu]
    (A G : Schedule (d+1)) (g : ℝ) (hg : 0 ≤ g) (i : Fin (m+1)) :
    (userProfileLaw (narrowCanonicalGame (m+1) d c hd hc h heps H scale beta hbeta nu A G g hg)).map
      (fun profile j => (profile (i.succAbove j)).1.2) =
      (iidRivalLaw m h nu).map (fun omega j => flagAction (d+1)
        (fun u => scale*Real.exp (beta u)) (omega j)) := by
  have hlow : ∀ᵐ v ∂(Measure.dirac (0:ℝ)), v ∉ bandHighSet eps H := by
    simpa only [ae_dirac_eq, Filter.eventually_pure] using zero_not_bandHighSet heps1 hH
  have he := game_rival_action_law_eq_flag_law i h H nu (Measure.dirac 0)
    (bandHighSet eps H) measurableSet_Icc (extendedSourceBid eps heps H scale beta)
    (continuous_extendedSourceBid eps heps H scale beta hbeta).measurable A G g hg
    (chosenCanonicalPolicy (m+1) (d+1) c (by omega) hc)
    (measurable_chosenCanonicalPolicy (m+1) (d+1) c (by omega) hc)
    (scaledHighLaw_supported hH nu) hlow
  simpa only [extendedSourceBid_high heps hH.ne' scale beta, narrowCanonicalGame,
    canonicalGame, narrowPrimitive] using he

theorem narrowCanonicalGame_highRivals_zero {m d c : ℕ}
    (hd : 1 ≤ d) (hc : 0 < c) (h : unitInterval) {eps : ℝ} (heps : 0 ≤ eps)
    (H scale : ℝ) (beta : ValueBand eps → ℝ) (hbeta : Continuous beta)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu]
    (A G : Schedule (d+1)) (g : ℝ) (hg : 0 ≤ g) (i : Fin m) :
    ∀ᵐ profile ∂userProfileLaw (narrowCanonicalGame m d c hd hc h heps H scale beta hbeta nu A G g hg),
      ExclusiveSource.HighRivals 0 i profile := by
  have hr := ae_profile_zero_or_full (F := narrowPrimitive h H nu) (E := bandHighSet eps H) measurableSet_Icc
    (continuous_extendedSourceBid eps heps H scale beta hbeta).measurable A G g hg
    (chosenCanonicalPolicy m (d+1) c (by omega) hc)
    (measurable_chosenCanonicalPolicy m (d+1) c (by omega) hc)
  filter_upwards [hr] with profile hprofile
  intro j _
  exact (hprofile j).imp_right (fun hj => ⟨hj,(profile j).1.2.bid_nonneg⟩)

theorem canonicalGame_corridorPlay {m d c : ℕ}
    (hd : 1 ≤ d) (hc : 0 < c) (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (A G : Schedule (d+1)) (g : ℝ) (hg : 0 ≤ g) (P : Corridor (d+1) m c)
    (hband : ∀ v ∈ E, b v ∈ Icc P.lower P.upper) :
    CorridorPlay (canonicalGame m (d+1) c (by omega) hc F E hE b hb A G g hg) P := by
  let Gamma := canonicalGame m (d+1) c (by omega) hc F E hE b hb A G g hg
  have hlaw : Gamma.F ⊗ₘ Gamma.σ = F.map (fun v => (v,pureAction (d+1) E b v)) :=
    value_action_law hE hb A G g hg (chosenCanonicalPolicy m (d+1) c (by omega) hc)
      (measurable_chosenCanonicalPolicy m (d+1) c (by omega) hc)
  unfold CorridorPlay
  change ∀ᵐ x ∂Gamma.F ⊗ₘ Gamma.σ, _
  rw [hlaw]
  have hset : MeasurableSet {x : ℝ×JointAction (d+1) | x.2.routeCount=0 ∨
      (x.2.routeCount=d+1 ∧ x.2.bid ∈ Icc P.lower P.upper)} := by
    have hk : Measurable (fun x : ℝ×JointAction (d+1) => x.2.routeCount) :=
      (measurable_routeCount (d+1)).comp measurable_snd
    have hbi : Measurable (fun x : ℝ×JointAction (d+1) => x.2.bid) :=
      (measurable_bid (d+1)).comp measurable_snd
    exact (measurableSet_eq_fun hk measurable_const).union
      ((measurableSet_eq_fun hk measurable_const).inter (hbi measurableSet_Icc))
  apply (ae_map_iff (measurable_id.prodMk (measurable_pureAction (d+1) hE hb)).aemeasurable hset).mpr
  apply Eventually.of_forall
  intro v
  by_cases hv : v ∈ E
  · have hpos : 0 < b v := P.lower_pos.trans_le (hband v hv).1
    have ha := pureAction_active (n := d+1) (E := E) (b := b) hv hpos
    exact Or.inr ⟨ha.2,by rw [ha.1]; exact hband v hv⟩
  · exact Or.inl (by simp [pureAction,hv,Interim.abstain])

theorem narrowCanonicalGame_users_optimal {m d c : ℕ}
    (hd : 1 ≤ d) (hc : 0 < c) (h : unitInterval) {eps : ℝ} (heps : 0 ≤ eps)
    (heps1 : eps < 1) {H : ℝ} (hH : 0 < H) (scale : ℝ)
    (beta : ValueBand eps → ℝ) (hbeta : Continuous beta)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu]
    (A G : Schedule (d+1)) (g : ℝ) (hg : 0 ≤ g) (a : UserTariff) (ha : a.Allowed)
    (hHigh : ∀ (i : Fin m) (u : ValueBand eps),
      ExclusiveTariffBestResponse (narrowCanonicalGame m d c hd hc h heps H scale beta hbeta nu A G g hg)
        a i (H*(u:ℝ)) (pureAction (d+1) (bandHighSet eps H)
          (extendedSourceBid eps heps H scale beta) (H*(u:ℝ)))) :
    ExclusiveTariffUsersOptimal (narrowCanonicalGame m d c hd hc h heps H scale beta hbeta nu A G g hg) a := by
  intro i
  have hs : ∀ᵐ v ∂narrowPrimitive h H nu, v ∈ bandHighSet eps H ∨ v=0 := by
    apply twoBandLaw_ae
    · exact (scaledHighLaw_supported hH nu).mono (fun _ hv => Or.inl hv)
    · simp
  filter_upwards [hs] with v hv
  change ∀ᵐ act ∂Kernel.deterministic (pureAction (d+1) (bandHighSet eps H)
      (extendedSourceBid eps heps H scale beta))
      (measurable_pureAction (d+1) measurableSet_Icc
        (continuous_extendedSourceBid eps heps H scale beta hbeta).measurable) v,
    ExclusiveTariffBestResponse _ a i v act
  simp only [Kernel.deterministic_apply, ae_dirac_eq, Filter.eventually_pure]
  rcases hv with hv | hv
  · have he := highValue_normalization heps hH hv
    simpa only [he] using hHigh i (normalizedType eps heps (v/H))
  · subst v
    rw [pureAction, if_neg (zero_not_bandHighSet heps1 hH)]
    exact nonpositive_exclusiveTariffBestResponse _ a ha i 0 hg

end FCAppendix.Bayes.ExclusiveConstruction
