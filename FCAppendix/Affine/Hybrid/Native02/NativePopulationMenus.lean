import FCAppendix.Affine.Hybrid.Native02.FullContextUniformMenus
import FCAppendix.Affine.Hybrid.Native02.NativeGame

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Game Bayes LowBody Set Filter Topology

def jointBidLaw (P : ProbabilityMeasure (ℝ × JointAction 2)) : ProbabilityMeasure ℝ :=
  P.map (((measurable_bid 2).comp measurable_snd).aemeasurable)

@[simp] lemma jointBidLaw_coe (P : ProbabilityMeasure (ℝ × JointAction 2)) :
    (jointBidLaw P : Measure ℝ) =
      (P : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid) := rfl

lemma jointBidLaw_ae {C : Set ℝ} (hC : MeasurableSet C)
    (P : ProbabilityMeasure (ℝ × JointAction 2))
    (hP : ∀ᵐ x ∂(P : Measure (ℝ × JointAction 2)), x.2.bid ∈ C) :
    ∀ᵐ b ∂(jointBidLaw P : Measure ℝ), b ∈ C :=
  (ae_map_iff ((measurable_bid 2).comp measurable_snd).aemeasurable hC).mpr hP

theorem native_population_context_facts {m c : ℕ} {d L U R : ℝ}
    (hdL : d < L) (hLU : L ≤ U) (hUR : U < R)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (PL PA PH : ProbabilityMeasure (ℝ × JointAction 2))
    (hlow : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ d ∧ x.2.routeCount=2)
    (hactive : ∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)),
      x.2.bid ∈ Icc L U ∧ x.2.routeCount=2)
    (hupper : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)),
      R ≤ x.2.bid ∧ x.2.routeCount=1)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta < 1) :
    let P := populationLaw s a h hs ha hh hsum PL PA PH
    let Γ := PopulationGame.game m c P eta heta0 heta1 U
    (∀ᵐ p ∂userProfileLaw Γ, p ∈ closedProfiles m R) ∧
    (∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid) ∧
    (userLaw Γ).map (physicalRow d U) =
      physicalRivalLaw s a h (jointBidLaw PL) (jointBidLaw PA) := by
  let P := populationLaw s a h hs ha hh hsum PL PA PH
  let Γ := PopulationGame.game m c P eta heta0 heta1 U
  have hdU : d ≤ U := hdL.le.trans hLU
  have hshape : ∀ᵐ x ∂(P : Measure (ℝ × JointAction 2)),
      (x.2.bid < R ∧ x.2.routeCount=2) ∨ (R ≤ x.2.bid ∧ x.2.routeCount=1) := by
    apply original_population_mixture_ae s a h PL PA PH
    · exact hlow.mono (fun x hx => Or.inl ⟨(hx.1.trans hdU).trans_lt hUR, hx.2⟩)
    · exact hactive.mono (fun x hx => Or.inl ⟨hx.1.2.trans_lt hUR, hx.2⟩)
    · exact hupper.mono (fun x hx => Or.inr hx)
  have hj : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ,
      (x.2.bid < R ∧ x.2.routeCount=2) ∨ (R ≤ x.2.bid ∧ x.2.routeCount=1) := by
    rw [PopulationGame.joint_law]
    exact hshape
  have hu := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ)
    (ν := permLaw 2)).quasiMeasurePreserving.ae hj
  refine ⟨ae_all_iff.mpr (fun i =>
    (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae hu), ?_, ?_⟩
  · rw [PopulationGame.joint_law]
    apply original_population_mixture_ae s a h PL PA PH
    · exact hlow.mono (fun x hx => Or.inl (hx.1.trans hdU))
    · exact hactive.mono (fun x hx => Or.inl hx.1.2)
    · exact hupper.mono (fun x hx => Or.inr hx.1)
  · exact native_population_physical_row hdU s a h hs ha hh hsum PL PA PH
      (hlow.mono (fun _ hx => hx.1))
      (hactive.mono (fun _ hx => ⟨hdL.trans_le hx.1.1, hx.1.2⟩))
      (hupper.mono (fun _ hx => hUR.trans_le hx.1)) eta heta0 heta1

theorem eventually_native_population_boxed_menus
    (s a h rho z xi eta d L U R W : ℝ) (hxiEq : xi=(1-eta)/2)
    (hs : 0 < s) (ha : 0 < a) (hh : 0 < h) (hsum : s+a+h=1)
    (hz0 : 0 ≤ z) (hz1 : z < 1) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hd : 0 ≤ d) (hL : 0 < L) (hLU : L ≤ U) (hUR : U < R) (hW : 0 ≤ W)
    (hgap : d < (1-xi)*L) (hlower : h/2 < rho) (hupper : rho < a+h/2)
    (hq0 : 0 < sourceExposure a h rho z) (hq1 : sourceExposure a h rho z < 1)
    (hboxlo : (1-xi)*U < (1-xi*sourceExposure a h rho z)*L)
    (hboxhi : (1-xi*sourceExposure a h rho z)*U < L)
    (capacityFamily : ℕ → ℕ)
    (hc : Tendsto (fun M => (capacityFamily M:ℝ)/(M:ℝ)) atTop (nhds rho))
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop,
      ∀ PL PA PH : ProbabilityMeasure (ℝ × JointAction 2),
      (∀ b, (jointBidLaw PL : Measure ℝ) {b}=0) →
      (∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ d ∧ x.2.routeCount=2) →
      (∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)), x.2.bid ∈ Icc L U ∧ x.2.routeCount=2) →
      (∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), R ≤ x.2.bid ∧ x.2.routeCount=1) →
      ∀ (i : Fin (N+1)) (act : JointAction 2), act.bid ∈ Icc L U →
      ∀ v : ℝ, |v| ≤ W →
      let P := populationLaw s a h hs.le ha.le hh.le hsum PL PA PH
      let G := nativeC5Game (N+1) (capacityFamily (N+1)) P eta heta0 heta1
        d L U R z (jointBidLaw PL)
      let q := exposure xi ((1-xi*sourceExposure a h rho z)/reciprocalMean (jointBidLaw PA)) act.bid
      (act.routeCount=2 → |(problem G i).payoff v act-
        (z*(v-act.bid)+(1-z)*independentTwo eta v act.bid q)| < eps) ∧
      (act.routeCount=1 → |(problem G i).payoff v act-
        ((z/2+(1-z)*q)*(v-act.bid))| < eps) := by
  subst xi
  have hxi : 0 < (1-eta)/2 := by linarith
  have hxi1 : (1-eta)/2 < 1 := by linarith
  have hsep : d < L := hgap.trans (by nlinarith [mul_pos hxi hL])
  have hm := FullContext.eventually_original_game_boxed_menus
    s a h rho z ((1-eta)/2) eta d L U R W hs ha hh hsum hz0 hz1 hxi hxi1
    heta0 heta1.le hd hL hLU hUR hW hgap hlower hupper hq0 hq1 hboxlo hboxhi
    capacityFamily hc eps heps
  filter_upwards [hm] with N hN
  intro PL PA PH hnull hlow hactive hhigh i act hb v hv
  have hμ : ∀ᵐ b ∂(jointBidLaw PL : Measure ℝ), b ∈ Icc 0 d :=
    jointBidLaw_ae measurableSet_Icc PL (hlow.mono (fun x hx => ⟨x.2.bid_nonneg, hx.1⟩))
  have hB : ∀ᵐ b ∂(jointBidLaw PA : Measure ℝ), b ∈ Icc L U :=
    jointBidLaw_ae measurableSet_Icc PA (hactive.mono (fun _ hx => hx.1))
  let P := populationLaw s a h hs.le ha.le hh.le hsum PL PA PH
  let Γ := PopulationGame.game (N+1) (capacityFamily (N+1)) P eta heta0 heta1 U
  obtain ⟨hfull, hpopgap, hrow⟩ := native_population_context_facts
    (m := N+1) (c := capacityFamily (N+1)) hsep hLU hUR s a h hs.le ha.le hh.le hsum
    PL PA PH hlow hactive hhigh eta heta0 heta1
  exact hN (jointBidLaw PL) (jointBidLaw PA) hnull hμ hB Γ rfl rfl rfl
    hfull hpopgap hrow i act hb v hv

theorem eventually_native_population_boxed_count_masses
    (s a h rho z xi eta d L U R : ℝ) (hxiEq : xi=(1-eta)/2)
    (hs : 0 < s) (ha : 0 < a) (hh : 0 < h) (hsum : s+a+h=1)
    (hz0 : 0 ≤ z) (hz1 : z < 1) (heta : 0 < eta) (heta1 : eta < 1)
    (hd : 0 ≤ d) (hL : 0 < L) (hLU : L ≤ U) (hUR : U < R)
    (hgap : d < (1-xi)*L) (hlower : h/2 < rho) (hupper : rho < a+h/2)
    (hq0 : 0 < sourceExposure a h rho z) (hq1 : sourceExposure a h rho z < 1)
    (hboxlo : (1-xi)*U < (1-xi*sourceExposure a h rho z)*L)
    (hboxhi : (1-xi*sourceExposure a h rho z)*U < L)
    (capacityFamily : ℕ → ℕ)
    (hc : Tendsto (fun M => (capacityFamily M:ℝ)/(M:ℝ)) atTop (nhds rho))
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop,
      ∀ PL PA PH : ProbabilityMeasure (ℝ × JointAction 2),
      (∀ b, (jointBidLaw PL : Measure ℝ) {b}=0) →
      (∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ d ∧ x.2.routeCount=2) →
      (∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)), x.2.bid ∈ Icc L U ∧ x.2.routeCount=2) →
      (∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), R ≤ x.2.bid ∧ x.2.routeCount=1) →
      ∀ (i : Fin (N+1)) (act : JointAction 2), act.bid ∈ Icc L U → act.routeCount=2 →
      let P := populationLaw s a h hs.le ha.le hh.le hsum PL PA PH
      let G := nativeC5Game (N+1) (capacityFamily (N+1)) P eta heta.le heta1
        d L U R z (jointBidLaw PL)
      let q := exposure xi ((1-xi*sourceExposure a h rho z)/reciprocalMean (jointBidLaw PA)) act.bid
      ∃ (hq0' : 0 ≤ q) (hq1' : q ≤ 1), ∀ r : Fin 3,
        |((problem G i).outcome act).mass r-
          (activeLimitLaw z q hz0 hz1.le hq0' hq1').mass r| < eps := by
  subst xi
  have hxi : 0 < (1-eta)/2 := by linarith
  have hxi1 : (1-eta)/2 < 1 := by linarith
  have hsep : d < L := hgap.trans (by nlinarith [mul_pos hxi hL])
  have hm := FullContext.eventually_original_game_boxed_count_masses
    s a h rho z ((1-eta)/2) eta d L U R hs ha hh hsum hz0 hz1 hxi hxi1
    heta heta1.le hd hL hLU hUR hgap hlower hupper hq0 hq1 hboxlo hboxhi
    capacityFamily hc eps heps
  filter_upwards [hm] with N hN
  intro PL PA PH hnull hlow hactive hhigh i act hb hk
  have hμ : ∀ᵐ b ∂(jointBidLaw PL : Measure ℝ), b ∈ Icc 0 d :=
    jointBidLaw_ae measurableSet_Icc PL (hlow.mono (fun x hx => ⟨x.2.bid_nonneg, hx.1⟩))
  have hB : ∀ᵐ b ∂(jointBidLaw PA : Measure ℝ), b ∈ Icc L U :=
    jointBidLaw_ae measurableSet_Icc PA (hactive.mono (fun _ hx => hx.1))
  let P := populationLaw s a h hs.le ha.le hh.le hsum PL PA PH
  let Γ := PopulationGame.game (N+1) (capacityFamily (N+1)) P eta heta.le heta1 U
  obtain ⟨hfull, hpopgap, hrow⟩ := native_population_context_facts
    (m := N+1) (c := capacityFamily (N+1)) hsep hLU hUR s a h hs.le ha.le hh.le hsum
    PL PA PH hlow hactive hhigh eta heta.le heta1
  exact hN (jointBidLaw PL) (jointBidLaw PA) hnull hμ hB Γ rfl rfl rfl
    hfull hpopgap hrow i act hb hk

end FCAppendix.Affine.Hybrid.Native02
