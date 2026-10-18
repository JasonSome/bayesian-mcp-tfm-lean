import FCAppendix.Exclusive.SourceEquivariant

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter

def chosenSourcePolicy {m n c : ℕ} (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (cutoff : ℝ) : LocalPolicy m c unitInterval :=
  Marker.sourceContinuation hm hn hc cutoff (chosenCanonicalPolicy m n c hn hc)

theorem measurable_chosenSourcePolicy {m n c : ℕ} (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (cutoff : ℝ) : Measurable (fun x : LocalList m × unitInterval =>
      (chosenSourcePolicy hm hn hc cutoff x.1 x.2).val) :=
  Marker.measurable_sourceContinuation hm hn hc cutoff (chosenCanonicalPolicy m n c hn hc)
    (measurable_chosenCanonicalPolicy m n c hn hc)

def sourceGame (m n c : ℕ) (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g) (cutoff : ℝ) : FiniteGame m n c unitInterval :=
  game m n c F E hE b hb A G g hg (chosenSourcePolicy hm hn hc cutoff)
    (measurable_chosenSourcePolicy hm hn hc cutoff)

def sourceProfiles (m n : ℕ) (cutoff : ℝ) : Set (UserProfile m n) :=
  {d | ∀ i, (d i).1.2.routeCount=0 ∨
    ((d i).1.2.routeCount=n ∧ cutoff ≤ (d i).1.2.bid)}

theorem measurableSet_sourceProfiles (m n : ℕ) (cutoff : ℝ) :
    MeasurableSet (sourceProfiles m n cutoff) := by
  simp only [sourceProfiles,setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have ha : Measurable (fun d : UserProfile m n => (d i).1.2) :=
    measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i))
  have hk := (measurable_routeCount n).comp ha
  exact (measurableSet_eq_fun hk measurable_const).union
    ((measurableSet_eq_fun hk measurable_const).inter
      (measurableSet_le measurable_const ((measurable_bid n).comp ha)))

theorem sourceProfiles_broadcast {m n : ℕ} {cutoff : ℝ} (d : UserProfile m n)
    (hd : d ∈ sourceProfiles m n cutoff) : d ∈ broadcastProfiles m n := by
  intro i
  rcases hd i with hz | ⟨hr,_⟩
  · exact Or.inl hz
  · exact Or.inr hr

theorem sourceProfiles_high {m n : ℕ} {cutoff : ℝ} (d : UserProfile m n)
    (hd : d ∈ sourceProfiles m n cutoff) :
    ∀ i, (d i).1.2.routeCount=0 ∨ cutoff ≤ (d i).1.2.bid := by
  intro i
  rcases hd i with hz | ⟨_,hb⟩
  · exact Or.inl hz
  · exact Or.inr hb

variable {m n c : ℕ} (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g) (cutoff : ℝ)

local notation "Γ" => sourceGame m n c hm hn hc F E hE b hb A G g hg cutoff

theorem sourceGame_ae_profiles (hfloor : ∀ᵐ v ∂F, v ∈ E → cutoff ≤ b v) :
    ∀ᵐ d ∂userProfileLaw Γ, d ∈ sourceProfiles m n cutoff := by
  have hplay : ∀ᵐ x ∂(Γ).F ⊗ₘ (Γ).σ,
      x.2.routeCount=0 ∨ (x.2.routeCount=n ∧ cutoff ≤ x.2.bid) := by
    have hlaw : (Γ).F ⊗ₘ (Γ).σ = F.map (fun v => (v,pureAction n E b v)) :=
      value_action_law (F := F) hE hb A G g hg (chosenSourcePolicy hm hn hc cutoff)
        (measurable_chosenSourcePolicy hm hn hc cutoff)
    rw [hlaw]
    have hmeas : MeasurableSet {x : ℝ × JointAction n |
        x.2.routeCount=0 ∨ (x.2.routeCount=n ∧ cutoff ≤ x.2.bid)} := by
      have hk : Measurable (fun x : ℝ × JointAction n => x.2.routeCount) :=
        (measurable_routeCount n).comp measurable_snd
      exact (measurableSet_eq_fun hk measurable_const).union
        ((measurableSet_eq_fun hk measurable_const).inter
          (measurableSet_le measurable_const ((measurable_bid n).comp measurable_snd)))
    apply (ae_map_iff (measurable_id.prodMk (measurable_pureAction n hE hb)).aemeasurable hmeas).mpr
    filter_upwards [hfloor] with v hv
    by_cases hvE : v ∈ E
    · exact Or.inr ⟨by simp [pureAction,hvE],by
        simpa only [pureAction,if_pos hvE] using (hv hvE).trans (le_max_left (b v) 0)⟩
    · exact Or.inl (by simp [pureAction,hvE,Interim.abstain])
  have hu := (measurePreserving_fst (μ := (Γ).F ⊗ₘ (Γ).σ)
    (ν := permLaw n)).quasiMeasurePreserving.ae hplay
  exact ae_all_iff.mpr fun i =>
    (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae hu

def sourcePosterior (hroom : n-1 ≤ m-n*c)
    (hfloor : ∀ᵐ v ∂F, v ∈ E → cutoff ≤ b v) : PosteriorSystem Γ :=
  posteriorWithFallback Γ (measurableSet_sourceProfiles m n cutoff)
    (sourceGame_ae_profiles hm hn hc F E hE b hb A G g hg cutoff hfloor)
    (fun j => Marker.sourceFallbackKernel (c := c) hm j cutoff)
    (fun j L hL => Marker.sourceFallbackKernel_feasible hm j cutoff hroom L hL)

theorem sourceGame_equivariant : PolicyLawEquivariant Γ :=
  constructed_source_policy_equivariant Γ hm hn hc cutoff
    (chosenCanonicalPolicy m n c hn hc) (measurable_chosenCanonicalPolicy m n c hn hc)
    (chosenCanonicalPolicy_law m n c hn hc) (fun _ _ _ => rfl)

theorem sourceGame_symmetric : SymmetricProposersOnPath Γ :=
  symmetric_on_path hE hb A G g hg (chosenSourcePolicy hm hn hc cutoff)
    (measurable_chosenSourcePolicy hm hn hc cutoff)

theorem sourceGame_broadcast (hpos : ∀ᵐ v ∂F, v ∈ E → 0 < b v) : ExclusiveBroadcastOn Γ E :=
  broadcast_on hE hb A G g hg (chosenSourcePolicy hm hn hc cutoff)
    (measurable_chosenSourcePolicy hm hn hc cutoff) hpos

end FCAppendix.Bayes.ExclusiveConstruction

namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter

theorem sourceGame_proposer_optimal {m k c : ℕ}
    (hm : 0 < m) (hn : 2 ≤ k+1) (hc : 0 < c)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (A G : Schedule (k+1)) (g : ℝ) (hg : 0 ≤ g) (cutoff : ℝ)
    (hroom : (k+1)-1 ≤ m-(k+1)*c) (hfloor : ∀ᵐ v ∂F, v ∈ E → cutoff ≤ b v) :
    ExclusivePosteriorOptimalAE (sourceGame m (k+1) c hm hn hc F E hE b hb A G g hg cutoff)
      (sourcePosterior hm hn hc F E hE b hb A G g hg cutoff hroom hfloor) :=
  constructed_source_proposer_optimal _ hm hn hc cutoff
    (chosenCanonicalPolicy m (k+1) c hn hc) (measurable_chosenCanonicalPolicy m (k+1) c hn hc)
    (chosenCanonicalPolicy_law m (k+1) c hn hc) (fun _ _ _ => rfl) hroom
    (sourceProfiles m (k+1) cutoff) (measurableSet_sourceProfiles m (k+1) cutoff)
    (sourceGame_ae_profiles hm hn hc F E hE b hb A G g hg cutoff hfloor)
    sourceProfiles_broadcast sourceProfiles_high

theorem sourceGame_rawBandContinuation {m k c : ℕ}
    (hm : 0 < m) (hn : 2 ≤ k+1) (hc : 0 < c)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (A G : Schedule (k+1)) (g : ℝ) (hg : 0 ≤ g) (cutoff : ℝ)
    (hroom : (k+1)-1 ≤ m-(k+1)*c) (hfloor : ∀ᵐ v ∂F, v ∈ E → cutoff ≤ b v)
    (lo hi : ℝ) (hlo : cutoff ≤ lo) :
    Completion.Exclusive.RawBandContinuation
      (sourceGame m (k+1) c hm hn hc F E hE b hb A G g hg cutoff)
      (sourcePosterior hm hn hc F E hE b hb A G g hg cutoff hroom hfloor) lo hi where
  common := by
    intro j L hL hband
    have hzero : Marker.lows cutoff L=∅ := by
      classical
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hiLow
      have hp := Marker.lows_subset_positives cutoff L hiLow
      let v : VisibleUser L := ⟨i,Marker.positive_visible L hp⟩
      have hbid := (hband v).1
      have hsmall := (Finset.mem_filter.mp hiLow).2.2
      change lo ≤ (L i).getD 0 at hbid
      linarith
    have hnot : ¬ Marker.SourceEligible hm cutoff L (k+1) c := by
      intro he
      have hh := he.1.2.1
      rw [hzero,Finset.card_empty] at hh
      omega
    exact sourcePosterior_common_of_not_eligible _ hm cutoff hroom
      (sourceProfiles m (k+1) cutoff) (measurableSet_sourceProfiles m (k+1) cutoff)
      (sourceGame_ae_profiles hm hn hc F E hE b hb A G g hg cutoff hfloor)
      sourceProfiles_broadcast j L hL hnot
  symmetric := fun j L _ _ => symmetric_at_list hE hb A G g hg
    (chosenSourcePolicy hm hn hc cutoff) (measurable_chosenSourcePolicy hm hn hc cutoff) j L
  optimal := fun j L hL _ =>
    sourceGame_proposer_optimal hm hn hc F E hE b hb A G g hg cutoff hroom hfloor j L hL

end FCAppendix.Bayes.ExclusiveConstruction
