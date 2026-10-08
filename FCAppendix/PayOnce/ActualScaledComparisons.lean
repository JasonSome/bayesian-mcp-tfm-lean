import FCAppendix.PayOnce.AnalyticalReindex
import FCAppendix.PayOnce.AnalyticalScaling

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce.AnalyticalKernel PayOnce.AnalyticalRareSuccess
variable {N c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem exists_ae_scaled_analytical_comparisons (Γ : FiniteGame (N+1) (k+1) c Seed)
    (hk : 1 ≤ k) (hcm : c ≤ N+1)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid)
    (i : Fin (N+1)) (a : ℝ) (ha : 0 < a) :
    let hn : 2 ≤ k+1 := by omega
    let hc : c ≤ Fintype.card (Fin N)+1 := by simpa using hcm
    let G : ProbabilityMeasure ℝ := ⟨realBidLaw Γ, inferInstance⟩
    ∃ S : Set ℝ, MeasurableSet S ∧ (∀ b ∈ S, 0 < b) ∧ (∀ᵐ b ∂realBidLaw Γ, b ∈ S) ∧
      ∀ᵐ z ∂(Γ.F ⊗ₘ Γ.σ), 0 < z.2.bid ∧
        z.2.bid / a ∈ regularSupportedSet (ι := Fin N) (k+1) c
          (rescaledRealLaw G a : Measure ℝ) ((fun b => b/a) '' S) ∧
        ∀ y ∈ S,
          (z.1 - Γ.g - y) * coverage (k+1) c hn hc
            (Measure.pi (fun _ : Fin N => realBidLaw Γ)) y ≤
          (z.1 - Γ.g - z.2.bid) * coverage (k+1) c hn hc
            (Measure.pi (fun _ : Fin N => realBidLaw Γ)) z.2.bid := by
  dsimp only
  let hn : 2 ≤ k+1 := by omega
  let hc : c ≤ Fintype.card (Fin N)+1 := by simpa using hcm
  let G : ProbabilityMeasure ℝ := ⟨realBidLaw Γ, inferInstance⟩
  letI := nullSingleton_realBidLaw_of_full_routes Γ (by omega) hatom hroute hbid
  letI : NullSingletonClass (G : Measure ℝ) :=
    inferInstanceAs (NullSingletonClass (realBidLaw Γ))
  letI := nullSingleton_rescaledRealLaw G ha
  obtain ⟨S, hSm, hS, hposS, hagree⟩ :=
    exists_common_analytical_agreement_set Γ hk hcm hA B hB hsym hroute hbid i
  have hdiv : MeasurableEmbedding (fun b : ℝ => b/a) := by
    simpa only [div_eq_mul_inv] using measurableEmbedding_mulRight₀ (inv_ne_zero ha.ne')
  have hSm' : MeasurableSet ((fun b : ℝ => b/a) '' S) := hdiv.measurableSet_image.mpr hSm
  have hS' : ∀ᵐ b ∂(rescaledRealLaw G a : Measure ℝ), b ∈ (fun b => b/a) '' S := by
    apply (ae_map_iff (measurable_id.div_const a).aemeasurable hSm').mpr
    exact hS.mono fun b hb => mem_image_of_mem _ hb
  have hgood := ae_mem_regularSupportedSet (ι := Fin N) (rescaledRealLaw G a : Measure ℝ)
    hn hc (ae_pos_rescaledRealLaw G ha (ae_realBidLaw_pos Γ hbid)) hS'
  have hbase : ∀ᵐ b ∂realBidLaw Γ, b/a ∈ regularSupportedSet (ι := Fin N) (k+1) c
      (rescaledRealLaw G a : Measure ℝ) ((fun b => b/a) '' S) :=
    ae_of_ae_map (measurable_id.div_const a).aemeasurable hgood
  rw [realBidLaw_eq_action_map] at hbase hS
  have hgoodz := ae_of_ae_map ((measurable_bid (k+1)).comp measurable_snd).aemeasurable hbase
  have hSz := ae_of_ae_map ((measurable_bid (k+1)).comp measurable_snd).aemeasurable hS
  have hcard : Fintype.card (Fin N) = Fintype.card (Rival i) := by
    have hh := card_rival_add_one i
    simp only [Fintype.card_fin]
    omega
  let e : Fin N ≃ Rival i := Fintype.equivOfCardEq hcard
  have hQ (b : ℝ) : coverage (k+1) c hn hc (Measure.pi (fun _ : Fin N => realBidLaw Γ)) b =
      coverage (k+1) c hn (by simpa only [card_rival_add_one] using hcm)
        (analyticalRivalLaw Γ i) b := by
    rw [analyticalRivalLaw_eq_pi]
    exact coverage_equiv e hn _ hc (realBidLaw Γ) b
  refine ⟨S, hSm, hposS, ?_, ?_⟩
  · rwa [realBidLaw_eq_action_map]
  · filter_upwards [hbid, hroute, hgoodz, hSz, ae_bestResponse_compProd Γ hu i]
      with z hb hr hgood hSz hbest
    refine ⟨hb, hgood, ?_⟩
    intro y hy
    let act := fullBid (k+1) y (hposS y hy).le
    have ha : act.bid = y := rfl
    have har : act.routeCount = k+1 := rfl
    have hyQ := hagree y hy act ha har
    have hzQ := hagree z.2.bid hSz z.2 rfl hr
    have hcmp := hbest act
    rw [payoff_once Γ hA hG, payoff_once Γ hA hG, hyQ, hzQ, ha, ← hQ, ← hQ] at hcmp
    convert hcmp using 1 <;> ring

end FCAppendix.Bayes
