import FCAppendix.Exclusive.SourceGame
import FCAppendix.Exclusive.SourceBidExtension
import FCAppendix.Exclusive.ActionLawTransport

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter
open Exclusive.Narrow.Existence

def bandHighSet (eps H : ℝ) : Set ℝ := Icc (H*(1-eps)) (H*(1+eps))

def bandPrimitive {eps : ℝ} (h : unitInterval) (H : ℝ)
    (nu : Measure (ValueBand eps)) (g L : ℝ) : Measure ℝ :=
  twoBandLaw h (scaledHighLaw H nu) (intervalLaw g L)

instance bandPrimitive_probability {eps : ℝ} (h : unitInterval) (H : ℝ)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu] (g L : ℝ) :
    IsProbabilityMeasure (bandPrimitive h H nu g L) := by unfold bandPrimitive; infer_instance

theorem bandPrimitive_atomless {eps H L : ℝ} (h : unitInterval)
    (nu : Measure (ValueBand eps)) [NullSingletonClass nu] (g : ℝ)
    (hH : 0 < H) (hL : 0 < L) : NullSingletonClass (bandPrimitive h H nu g L) := by
  letI := scaledHighLaw_atomless hH nu
  letI := intervalLaw_atomless g hL
  unfold bandPrimitive
  infer_instance

theorem bandPrimitive_properties {eps H L : ℝ} (h : unitInterval)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu] [NullSingletonClass nu]
    (g : ℝ) (hH : 0 < H) (hL : 0 < L) (hseparate : g+L < H*(1-eps)) :
    (bandPrimitive h H nu g L).real (bandHighSet eps H)=(h : ℝ) ∧
    (bandPrimitive h H nu g L).real (Ioi g)=1 ∧
    (∀ᵐ v ∂bandPrimitive h H nu g L, v ∈ bandHighSet eps H ∨ v ∈ Ioo g (g+L)) := by
  letI := scaledHighLaw_atomless hH nu
  have hp := scarce_primitive_law h (scaledHighLaw H nu) g hL hseparate
    (scaledHighLaw_supported hH nu)
  exact ⟨hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2⟩

def bandSourceGame (m n c : ℕ) (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (h : unitInterval) {eps : ℝ} (heps : 0 ≤ eps) (H scale : ℝ)
    (beta : ValueBand eps → ℝ) (hbeta : Continuous beta)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu]
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g) (L cutoff : ℝ) : FiniteGame m n c unitInterval :=
  sourceGame m n c hm hn hc (bandPrimitive h H nu g L) (bandHighSet eps H)
    measurableSet_Icc (extendedSourceBid eps heps H scale beta)
    (continuous_extendedSourceBid eps heps H scale beta hbeta).measurable A G g hg cutoff

variable {m n c : ℕ} (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (h : unitInterval) {eps : ℝ} (heps : 0 ≤ eps) (H scale : ℝ)
    (beta : ValueBand eps → ℝ) (hbeta : Continuous beta)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu]
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g) (L cutoff : ℝ)

local notation "Γ" => bandSourceGame m n c hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff

theorem bandSourceGame_high_action (hH : 0 < H) (u : ValueBand eps) :
    pureAction n (bandHighSet eps H) (extendedSourceBid eps heps H scale beta) (H*(u : ℝ)) =
      ExclusiveNarrow.broadcastBid n (scale*Real.exp (beta u)) := by
  have hu : H*(u : ℝ) ∈ bandHighSet eps H :=
    ⟨mul_le_mul_of_nonneg_left u.property.1 hH.le,
      mul_le_mul_of_nonneg_left u.property.2 hH.le⟩
  simp only [pureAction,if_pos hu,extendedSourceBid_high heps hH.ne' scale beta,
    ExclusiveNarrow.broadcastBid,max_comm]

theorem bandSourceGame_sigma_high (hH : 0 < H) (u : ValueBand eps) :
    (Γ).σ (H*(u : ℝ)) =
      Measure.dirac (ExclusiveNarrow.broadcastBid n (scale*Real.exp (beta u))) := by
  change Measure.dirac (pureAction n (bandHighSet eps H)
    (extendedSourceBid eps heps H scale beta) (H*(u : ℝ))) = _
  rw [bandSourceGame_high_action heps H scale beta hH u]

theorem bandSourceGame_broadcast (hscale : 0 < scale) : ExclusiveBroadcastOn Γ (bandHighSet eps H) :=
  sourceGame_broadcast hm hn hc _ _ measurableSet_Icc _ _ A G g hg cutoff
    (Eventually.of_forall fun v _ => extendedSourceBid_pos heps H hscale beta v)

theorem bandSourceGame_equivariant : PolicyLawEquivariant Γ :=
  sourceGame_equivariant hm hn hc _ _ measurableSet_Icc _ _ A G g hg cutoff

theorem bandSourceGame_symmetric : SymmetricProposersOnPath Γ :=
  sourceGame_symmetric hm hn hc _ _ measurableSet_Icc _ _ A G g hg cutoff

theorem bandSourceGame_floor {delta : ℝ} (hscale : 0 ≤ scale)
    (hband : ∀ u, beta u ∈ Icc (-delta) delta)
    (hcut : cutoff ≤ scale*Real.exp (-delta)) :
    ∀ᵐ v ∂(Γ).F, v ∈ bandHighSet eps H →
      cutoff ≤ extendedSourceBid eps heps H scale beta v :=
  Eventually.of_forall fun v _ => hcut.trans
    (extendedSourceBid_band heps H hscale beta hband v).1

theorem bandSourceGame_low_action {v : ℝ} (hseparate : g+L < H*(1-eps))
    (hv : v ∈ Ioo g (g+L)) :
    pureAction n (bandHighSet eps H) (extendedSourceBid eps heps H scale beta) v =
      Interim.abstain n := by
  have hnot : v ∉ bandHighSet eps H := by intro hh; dsimp [bandHighSet] at hh; linarith [hh.1,hv.2]
  simp only [pureAction,if_neg hnot]

end FCAppendix.Bayes.ExclusiveConstruction

namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter
open Exclusive.Narrow.Existence

theorem bandSourceGame_rival_action_law {m n c : ℕ}
    (hm : 0 < m+1) (hn : 2 ≤ n) (hc : 0 < c)
    (h : unitInterval) {eps : ℝ} (heps : 0 ≤ eps) {H : ℝ} (hH : 0 < H) (scale : ℝ)
    (beta : ValueBand eps → ℝ) (hbeta : Continuous beta)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu]
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g) {L : ℝ} (hL : 0 < L)
    (cutoff : ℝ) (hseparate : g+L < H*(1-eps)) (i : Fin (m+1)) :
    (userProfileLaw (bandSourceGame (m+1) n c hm hn hc h heps H scale beta hbeta nu
      A G g hg L cutoff)).map (fun x j => (x (i.succAbove j)).1.2) =
      (iidRivalLaw m h nu).map
        (fun omega j => flagAction n (fun u => scale*Real.exp (beta u)) (omega j)) := by
  have hhigh : ∀ᵐ v ∂scaledHighLaw H nu, v ∈ bandHighSet eps H := scaledHighLaw_supported hH nu
  have hlow : ∀ᵐ v ∂intervalLaw g L, v ∉ bandHighSet eps H := by
    filter_upwards [intervalLaw_supported g hL] with v hv hvin
    dsimp [bandHighSet] at hvin
    linarith [hv.2,hvin.1]
  have hx := game_rival_action_law_eq_flag_law i h H nu (intervalLaw g L)
    (bandHighSet eps H) measurableSet_Icc (extendedSourceBid eps heps H scale beta)
    (continuous_extendedSourceBid eps heps H scale beta hbeta).measurable A G g hg
    (chosenSourcePolicy hm hn hc cutoff) (measurable_chosenSourcePolicy hm hn hc cutoff) hhigh hlow
  simpa only [extendedSourceBid_high heps hH.ne' scale beta,bandSourceGame,sourceGame,bandPrimitive] using hx

theorem normalizedHighBid_atomless {eps scale : ℝ} (hscale : 0 < scale)
    (nu : Measure (ValueBand eps)) [NullSingletonClass nu]
    (beta : ValueBand eps → ℝ) (hbeta : Continuous beta) (hmono : StrictMono beta) :
    NullSingletonClass (nu.map (fun u => scale*Real.exp (beta u))) := by
  apply nullSingletonClass_map_of_injective nu
    (continuous_const.mul (Real.continuous_exp.comp hbeta)).measurable
  exact (fun u v huv => hmono.injective (Real.exp_injective
    (mul_left_cancel₀ hscale.ne' huv)))

theorem bandSourceGame_users_optimal {m n c : ℕ}
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (h : unitInterval) {eps : ℝ} (heps : 0 ≤ eps) {H : ℝ} (hH : 0 < H) (scale : ℝ)
    (beta : ValueBand eps → ℝ) (hbeta : Continuous beta)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu]
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g) {L : ℝ} (hL : 0 < L)
    (cutoff : ℝ) (hseparate : g+L < H*(1-eps)) (tariff : UserTariff)
    (hHigh : ∀ (i : Fin m) (u : ValueBand eps),
      let Γ := bandSourceGame m n c hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff
      ExclusiveTariffBestResponse Γ tariff i (H*(u : ℝ))
        (pureAction n (bandHighSet eps H) (extendedSourceBid eps heps H scale beta) (H*(u : ℝ))))
    (hLow : ∀ (i : Fin m) (v : ℝ), v ∈ Ioo g (g+L) →
      ExclusiveTariffBestResponse
        (bandSourceGame m n c hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff)
        tariff i v (Interim.abstain n)) :
    ExclusiveTariffUsersOptimal
      (bandSourceGame m n c hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff) tariff := by
  intro i
  have hs : ∀ᵐ v ∂bandPrimitive h H nu g L,
      v ∈ bandHighSet eps H ∨ v ∈ Ioo g (g+L) :=
    twoBandLaw_ae h (scaledHighLaw H nu) (intervalLaw g L) _
      ((scaledHighLaw_supported hH nu).mono fun _ hv => Or.inl hv)
      ((intervalLaw_strict_supported g hL).mono fun _ hv => Or.inr hv)
  filter_upwards [hs] with v hv
  change ∀ᵐ a ∂Kernel.deterministic (pureAction n (bandHighSet eps H)
    (extendedSourceBid eps heps H scale beta))
      (measurable_pureAction n measurableSet_Icc
        (continuous_extendedSourceBid eps heps H scale beta hbeta).measurable) v,
    ExclusiveTariffBestResponse _ tariff i v a
  simp only [Kernel.deterministic_apply,ae_dirac_eq,Filter.eventually_pure]
  rcases hv with hv | hv
  · have he := highValue_normalization heps hH hv
    simpa only [he] using hHigh i (normalizedType eps heps (v/H))
  · have hnot : v ∉ bandHighSet eps H := by
      intro hh
      dsimp [bandHighSet] at hh
      linarith [hh.1,hv.2]
    rw [pureAction,if_neg hnot]
    exact hLow i v hv

end FCAppendix.Bayes.ExclusiveConstruction
