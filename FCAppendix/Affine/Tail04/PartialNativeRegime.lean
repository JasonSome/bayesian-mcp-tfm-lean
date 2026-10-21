import FCAppendix.Affine.Tail04.PartialNativeGuardIntegration

noncomputable section
namespace FCAppendix.Affine.Tail04.PartialNativeRegime
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open NativeLocalPolicy NativeMenuReports NativePartialReports NativeObservationPair JoinedHighPolicy
open PartialNativeCoordinates PartialNativeEvents PartialNativeCategoryBounds
open PartialNativeSeed PartialNativeGuardIntegration NativePartialDeviation
open scoped BigOperators ENNReal

def publicCoin (Q : PublicScenario.Data) (u : unitInterval) : Bool :=
  PublicScenario.regimeSample Q (PublicScenario.split (PublicScenario.split u).1).1

lemma measurable_publicCoin (Q : PublicScenario.Data) : Measurable (publicCoin Q) :=
  (PublicScenario.measurable_regimeSample Q).comp
    (PublicScenario.measurable_split.fst.comp PublicScenario.measurable_split.fst)

lemma publicCoin_law (Q : PublicScenario.Data) :
    (volume : Measure unitInterval).map (publicCoin Q)=
      FiniteLaw.probabilityMeasure (IndependentCounts.bernoulli Q.θ Q.θ_nonneg Q.θ_le_one) := by
  have hs : MeasurePreserving (fun u : unitInterval => (PublicScenario.split u).1)
      volume volume :=
    measurePreserving_fst.comp ⟨PublicScenario.measurable_split,PublicScenario.split_law⟩
  have hr : MeasurePreserving (PublicScenario.regimeSample Q) volume
      (FiniteLaw.probabilityMeasure (IndependentCounts.bernoulli Q.θ Q.θ_nonneg Q.θ_le_one)) :=
    ⟨PublicScenario.measurable_regimeSample Q,PublicScenario.regimeSample_law Q⟩
  exact (hr.comp (hs.comp hs)).map_eq

lemma publicCoin_true_probability (Q : PublicScenario.Data) :
    (volume : Measure unitInterval).real {u | publicCoin Q u=true}=Q.θ := by
  have h := congrArg (fun μ : Measure Bool => μ {true}) (publicCoin_law Q)
  rw [Measure.map_apply (measurable_publicCoin Q) (measurableSet_singleton true),
    FiniteLaw.probabilityMeasure_singleton] at h
  simpa only [measureReal_def,IndependentCounts.bernoulli,Bool.true_eq,if_true,
    ENNReal.toReal_ofReal Q.θ_nonneg,Set.preimage,Set.mem_singleton_iff] using congrArg ENNReal.toReal h

section Native
variable {N c : ℕ} (Γ : FiniteGame (N+1) 2 c NativeLocalPolicy.Seed)
  (D : Data (N+1) c) (Q : PublicScenario.Data)
  (hpublic : ∀ n z,D.publicChoice n z=
    PublicScenario.localChoice D.E Q (NativeFlag.nativeLowBidLaw Γ D.E) n z)
  (hcat : ∀ k : Fin 4,(userLaw Γ) (D.E.coarseTag ⁻¹' {k})≠0)
  (hlow : ∀ b,NativeFlag.nativeLowBidLaw Γ D.E {b}=0)
  (hmenu : ∀ᵐ x ∂Γ.F⊗ₘΓ.σ,MenuAction D.E x.2)

include hpublic in
lemma localRegime_of_seed (L : LocalList (N+1)) (u : unitInterval)
    (hu : seedOnList (NativeFlag.nativeLowBidLaw Γ D.E) (D.E.roleList 0 L)=some u) :
    localRegime D 0 L=if 0<(LocalCoordinates.ids D.E 1 L).card then publicCoin Q u else false := by
  simp only [localRegime,regimeAtKey,D.key_self,if_true,Data.parameter,hpublic,
    PublicScenario.localChoice,hu,JoinedHighPolicy.regime,
    PublicScenario.draw,PublicScenario.sample_regime,publicCoin]

include hpublic in
lemma localRegime_of_no_seed (L : LocalList (N+1))
    (hu : seedOnList (NativeFlag.nativeLowBidLaw Γ D.E) (D.E.roleList 0 L)=none) :
    localRegime D 0 L=false := by
  simp only [localRegime,regimeAtKey,D.key_self,if_true,Data.parameter,hpublic,
    PublicScenario.localChoice,hu,JoinedHighPolicy.regime,PublicScenario.fallback]

include hpublic hcat hlow hmenu in
theorem fiber_reject_probability (i : Fin (N+1)) (kind : Fin N→ Fin 4) :
    (fiber Γ D kind).real {z | backgroundRegime D i (restoreBackground i z)=true}≤ Q.θ := by
  letI := fiber_isProbabilityMeasure Γ D hcat kind
  let b : Icc D.E.R D.E.Rp := ⟨D.E.R,le_rfl,D.E.R_le_Rp⟩
  by_cases hn : ∀ r,kind r≠0
  · have he : {z | backgroundRegime D i (restoreBackground i z)=true}=ᵐ[fiber Γ D kind] (∅ : Set (DeletedBackground N Seed)) := by
      filter_upwards [fiber_shape Γ D kind,fiber_menu Γ D hmenu kind] with z hz hmz
      have hr : ∀ r,MenuAction D.E ((restoreBackground i z).1 (i.succAbove r)).1.2 := by
        intro r;simpa only [restoreBackground_rival] using hmz r
      have hnone : ∀ r,rivalKinds D.E i (restoreBackground i z) r≠0 := by
        intro r;simpa only [rivalKinds,restoreBackground_rival,hz r] using hn r
      have hs := no_low_seed D.E i (restoreBackground i z) hr b 0
        (NativeFlag.nativeLowBidLaw Γ D.E) hnone
      have hh := localRegime_of_no_seed Γ D Q hpublic _ hs
      apply propext
      change (_=true ↔ False)
      simp only [backgroundRegime,b,hh,Bool.false_eq_true]
    rw [measureReal_def,measure_congr he,measure_empty,ENNReal.toReal_zero]
    exact Q.θ_nonneg
  · obtain ⟨r,hr⟩ := not_forall.mp hn
    have hpos : 0< Fintype.card {r : Fin N // kind r=0} :=
      Fintype.card_pos_iff.mpr ⟨⟨r,not_not.mp hr⟩⟩
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    let e : Fin (n+1)≃{r : Fin N // kind r=0} := (Fintype.equivFinOfCardEq hn).symm
    have hsub : {z | backgroundRegime D i (restoreBackground i z)=true}≤ᵐ[fiber Γ D kind]
        {z | publicCoin Q (fiberMinimum Γ D kind n e z)=true} := by
      filter_upwards [fiber_seed_on_present Γ D hmenu i kind n e b 0] with z hz
      have hh := localRegime_of_seed Γ D Q hpublic _ _ hz
      intro htrue
      change localRegime D 0 (presentList (restoreBackground i z) i D.E.R 0)=true at htrue
      rw [hh] at htrue
      split_ifs at htrue
      exact htrue
    have hp : (fiber Γ D kind).real {z | publicCoin Q (fiberMinimum Γ D kind n e z)=true}=Q.θ := by
      change ((fiber Γ D kind) ((fiberMinimum Γ D kind n e) ⁻¹' {u | publicCoin Q u=true})).toReal=Q.θ
      rw [←Measure.map_apply (measurable_fiberMinimum Γ D kind n e)
        (measurableSet_eq_fun (measurable_publicCoin Q) measurable_const),
        fiberMinimum_law Γ D hcat hlow kind n e]
      exact publicCoin_true_probability Q
    exact (real_mono_ae (fiber Γ D kind) hsub).trans_eq hp

include hpublic hcat hlow hmenu in
theorem native_reject_probability (i : Fin (N+1)) :
    (backgroundLaw Γ).real {ω | backgroundRegime D i ω=true}≤ Q.θ := by
  let μ := deletedBackgroundLaw Γ
  let w : (Fin N→ Fin 4)→ℝ≥0∞ := fun kind => μ (deletedTag D ⁻¹' {kind})
  haveI (kind : Fin N→ Fin 4) : IsProbabilityMeasure (fiber Γ D kind) :=
    fiber_isProbabilityMeasure Γ D hcat kind
  have hw (kind : Fin N→ Fin 4) : w kind≠⊤ := measure_ne_top _ _
  have hμ : μ=∑ kind,w kind • fiber Γ D kind := deleted_fiber_sum Γ D
  have hsum : (∑ kind,(w kind).toReal)=1 := by
    have hh := real_finite_mixture μ w (fiber Γ D) hw hμ univ
    simpa only [measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using hh.symm
  have he := native_event_deleted Γ i {ω | backgroundRegime D i ω=true}
    (measurableSet_eq_fun (measurable_backgroundRegime D i) measurable_const)
    (fun ω => by simp only [mem_setOf_eq,backgroundRegime,present_restore_delete])
  rw [he,real_finite_mixture μ w (fiber Γ D) hw hμ]
  calc
    _≤∑ kind,(w kind).toReal*Q.θ := Finset.sum_le_sum fun kind _ =>
      mul_le_mul_of_nonneg_left
        (fiber_reject_probability Γ D Q hpublic hcat hlow hmenu i kind) ENNReal.toReal_nonneg
    _=Q.θ := by rw [←Finset.sum_mul,hsum,one_mul]

include hpublic hcat hlow hmenu in
theorem serviceProb_lower (i : Fin (N+1)) : 1-Q.θ≤ serviceProb D Γ i := by
  let ν := actualRegimeLaw D Γ i
  have htrue : ν.mass true≤ Q.θ := by
    change (actualRegimeLaw D Γ i).mass true≤Q.θ
    rw [actualRegimeLaw,FiniteLaw.ofMeasure_mass]
    exact native_reject_probability Γ D Q hpublic hcat hlow hmenu i
  have htotal : ν.mass false+ν.mass true=1 := by
    have hh := ν.total
    have hB : (Finset.univ : Finset Bool)={false,true} := by decide
    simpa only [hB,Finset.sum_insert (by decide : false∉({true}:Finset Bool)),
      Finset.sum_singleton] using hh
  change 1-Q.θ≤ ν.mass false
  linarith

end Native
end FCAppendix.Affine.Tail04.PartialNativeRegime
