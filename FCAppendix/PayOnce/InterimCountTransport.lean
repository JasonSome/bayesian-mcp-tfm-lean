import FCAppendix.PayOnce.ProfileCountLaw
import FCAppendix.PayOnce.BinomialContinuity
import FCAppendix.PayOnce.AnalyticalReindex
import FCAppendix.Finite.ConditionalCountLaw

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open PayOnce
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem interim_expect_eq_profile_update (Γ : FiniteGame m n c Seed) (i : Fin m)
    (x : ℝ × JointAction n) (test : Fin (n+1) → ℝ) :
    ((problem Γ i).outcome x.2).expect test =
      ∫ r, ∫ d, (profileCountLaw Γ (Function.update d i (x,r)) i).expect test
        ∂userProfileLaw Γ ∂permLaw n := by
  let f := fun ω : Sample m n Seed => test (focalCount Γ i x.2 ω)
  have hi : Integrable f (sampleLaw Γ) :=
    CountLaw.integrable_comp _ _ (measurable_focalCount Γ i x.2) test
  rw [problem_outcome,CountLaw.expect_ofMeasure]
  change (∫ ω, f ω ∂(backgroundLaw Γ).prod (permLaw n)) = _
  rw [integral_prod_symm f hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  dsimp only
  have hir : Integrable (fun ω : Background m n Seed => f (ω,r)) (backgroundLaw Γ) := by
    apply CountLaw.integrable_comp _ _ _ test
    exact (measurable_focalCount Γ i x.2).comp (measurable_id.prodMk measurable_const)
  change Integrable (fun ω : Background m n Seed => f (ω,r))
    ((userProfileLaw Γ).prod (Measure.pi fun _ : Fin n => Γ.seedLaw)) at hir
  change (∫ ω : Background m n Seed, f (ω,r)
    ∂(userProfileLaw Γ).prod (Measure.pi fun _ : Fin n => Γ.seedLaw)) = _
  rw [integral_prod _ hir]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro d
  dsimp only
  unfold profileCountLaw
  rw [CountLaw.expect_ofMeasure]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  exact congrArg test (playedCount_insertDraw Γ i ((x,r),(d,s))).symm

theorem ae_interim_countMass_eq_analytical {k : ℕ} (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) (i : Fin m) (j : ℕ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), ((problem Γ i).outcome x.2).prob (fun r => r.val = j) =
      ∫ rivals, ManyProposers.binomialMass (k+1)
        (AnalyticalKernel.allocation (k+1) c (by omega)
          (by simpa only [card_rival_add_one] using hcm) rivals x.2.bid) j ∂analyticalRivalLaw Γ i := by
  classical
  have hp := (ae_profileCountLaw_eq_binomial Γ hk hcm hA B hB hsym hroute hbid).mono fun d hd =>
    congrArg (fun μ : CountLaw (k+1) => μ.prob (fun r => r.val = j)) (hd i)
  simp only [ManyProposers.binomial_prob_eq_binomialMass] at hp
  have hpres : MeasurePreserving (fun z : UserDraw (k+1) × UserProfile m (k+1) =>
      Function.update z.2 i z.1) ((userLaw Γ).prod (userProfileLaw Γ)) (userProfileLaw Γ) :=
    ⟨Resample.measurable_update_pair i,Resample.map_update_eq (userLaw Γ) i⟩
  have hup := Measure.ae_ae_of_ae_prod (hpres.quasiMeasurePreserving.ae hp)
  have hx := Measure.ae_ae_of_ae_prod hup
  filter_upwards [hx,hbid] with x hx hxb
  rw [FiniteLaw.prob_eq_expect,interim_expect_eq_profile_update Γ i x]
  have he : ∀ᵐ r ∂permLaw (k+1),
      (∫ d, (profileCountLaw Γ (Function.update d i (x,r)) i).expect
        (fun s => if s.val = j then (1:ℝ) else 0) ∂userProfileLaw Γ) =
      ∫ rivals, ManyProposers.binomialMass (k+1)
        (AnalyticalKernel.allocation (k+1) c (by omega)
          (by simpa only [card_rival_add_one] using hcm) rivals x.2.bid) j ∂analyticalRivalLaw Γ i := by
    filter_upwards [hx] with r hr
    unfold analyticalRivalLaw
    have hm : Measurable (fun rivals : Rival i → ℝ => ManyProposers.binomialMass (k+1)
        (AnalyticalKernel.allocation (k+1) c (by omega)
          (by simpa only [card_rival_add_one] using hcm) rivals x.2.bid) j) :=
      (ManyProposers.continuous_binomialMass (k+1) j).measurable.comp
        (AnalyticalKernel.measurable_allocation_rivals (by omega)
          (by simpa only [card_rival_add_one] using hcm) hxb)
    rw [integral_map (measurable_rivalBids i).aemeasurable hm.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hr] with d hd
    have hrv : rivalBids i (Function.update d i (x,r)) = rivalBids i d := by
      funext l
      simp only [rivalBids,Function.update_of_ne l.property]
    rw [← FiniteLaw.prob_eq_expect,hd]
    simp only [analyticalProfileMarginal,Function.update_self,hrv]
  rw [integral_congr_ae he]
  simp only [integral_const,probReal_univ,one_smul]

end FCAppendix.Bayes

namespace FCAppendix.PayOnce.AnalyticalKernel
open MeasureTheory Set
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem integral_allocation_test_equiv (e : κ ≃ ι) {n c : ℕ} (hn : 2 ≤ n)
    (hcι : c ≤ Fintype.card ι+1) (hcκ : c ≤ Fintype.card κ+1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (b : ℝ) (test : ℝ → ℝ) :
    (∫ rivals : κ → ℝ, test (allocation n c hn hcκ rivals b) ∂Measure.pi (fun _ : κ => G)) =
      ∫ rivals : ι → ℝ, test (allocation n c hn hcι rivals b) ∂Measure.pi (fun _ : ι => G) := by
  have hm := measurePreserving_piCongrLeft (fun _ : κ => G) e.symm
  have hh := hm.integral_comp' (fun rivals : κ → ℝ => test (allocation n c hn hcκ rivals b))
  rw [← hh]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun rivals => by
    apply congrArg test
    have heval : (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e.symm) rivals =
        fun j => rivals (e j) := by
      funext j
      simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
    rw [heval]
    exact allocation_comp_equiv e hn hcι hcκ rivals b

end FCAppendix.PayOnce.AnalyticalKernel

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open PayOnce PayOnce.AnalyticalKernel
open scoped ProbabilityTheory BigOperators
variable {N c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_pure_bid_pos (Γ : FiniteGame (N+1) (k+1) c Seed) (b : ℝ → ℝ)
    (heq : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.bid = b x.1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) : ∀ᵐ v ∂Γ.F, 0 < b v := by
  have hh : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < b x.1 := by
    filter_upwards [heq,hbid] with x hx hb
    rwa [← hx]
  have ha := Measure.ae_ae_of_ae_compProd hh
  exact ha.mono fun _ hv => hv.exists.choose_spec

theorem ae_typeOutcome_countMass_eq (Γ : FiniteGame (N+1) (k+1) c Seed)
    (hk : 1 ≤ k) (hcm : c ≤ N+1)
    (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid)
    (b : ℝ → ℝ) (heq : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.bid = b x.1) (j : ℕ) :
    ∀ᵐ v ∂Γ.F, ∀ i : Fin (N+1), (typeOutcome Γ i v).prob (fun r => r.val = j) =
      ∫ rivals : Fin N → ℝ, ManyProposers.binomialMass (k+1)
        (allocation (k+1) c (by omega) (by simpa using hcm) rivals (b v)) j
          ∂Measure.pi (fun _ : Fin N => realBidLaw Γ) := by
  classical
  have ha i : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v,
      ((problem Γ i).outcome a).prob (fun r => r.val = j) =
        ∫ rivals : Rival i → ℝ, ManyProposers.binomialMass (k+1)
          (allocation (k+1) c (by omega) (by simpa only [card_rival_add_one] using hcm) rivals (b v)) j
            ∂analyticalRivalLaw Γ i := by
    have hx : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
        ((problem Γ i).outcome x.2).prob (fun r => r.val = j) =
          ∫ rivals : Rival i → ℝ, ManyProposers.binomialMass (k+1)
            (allocation (k+1) c (by omega) (by simpa only [card_rival_add_one] using hcm) rivals (b x.1)) j
              ∂analyticalRivalLaw Γ i := by
      filter_upwards [ae_interim_countMass_eq_analytical Γ hk hcm hA B hB hsym hroute hbid i j,heq]
        with x hx hb
      simpa only [hb] using hx
    exact Measure.ae_ae_of_ae_compProd hx
  filter_upwards [ae_all_iff.mpr ha] with v hv
  intro i
  rw [FiniteLaw.prob_eq_expect,typeOutcome_expect]
  simp_rw [← FiniteLaw.prob_eq_expect]
  have hconst := integral_congr_ae (hv i)
  rw [integral_const,probReal_univ,one_smul] at hconst
  change (∫ a, ((problem Γ i).outcome a).prob (fun r => r.val = j) ∂Γ.σ v) = _
  rw [hconst,analyticalRivalLaw_eq_pi]
  have hcard : Fintype.card (Fin N) = Fintype.card (Rival i) := by
    have hh := card_rival_add_one i
    simp only [Fintype.card_fin]
    omega
  let e : Fin N ≃ Rival i := Fintype.equivOfCardEq hcard
  exact (integral_allocation_test_equiv e (by omega) _ _ (realBidLaw Γ) (b v)
    (fun p => ManyProposers.binomialMass (k+1) p j)).symm

end FCAppendix.Bayes
