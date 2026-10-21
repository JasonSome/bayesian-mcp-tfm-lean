import FCAppendix.Affine.Tail04.PartialNativeRegime

noncomputable section
namespace FCAppendix.Affine.Tail04.PartialRegimeLimit
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open NativeLocalPolicy NativePartialReports NativeObservationPair
open PartialNativeCoordinates PartialNativeEvents PartialNativeCategoryBounds
open PartialNativeSeed PartialNativeGuardIntegration PartialNativeRegime NativePartialDeviation
open scoped BigOperators

variable {N c : ℕ} (Γ : FiniteGame (N+1) 2 c NativeLocalPolicy.Seed)
  (D : Data (N+1) c) (Q : PublicScenario.Data)
  (hpublic : ∀n z,D.publicChoice n z=
    PublicScenario.localChoice D.E Q (NativeFlag.nativeLowBidLaw Γ D.E) n z)
  (hcat : ∀k : Fin 4,(userLaw Γ) (D.E.coarseTag ⁻¹' {k})≠0)
  (hlow : ∀b,NativeFlag.nativeLowBidLaw Γ D.E {b}=0)
  (hmenu : ∀ᵐ x ∂Γ.F⊗ₘΓ.σ,NativeMenuReports.MenuAction D.E x.2)

def missing (kind : Fin N→ Fin 4) : Prop := (∀r,kind r≠0) ∨ (∀r,kind r≠1)

include hpublic hcat hlow hmenu in
lemma fiber_reject_eq (i : Fin (N+1)) (kind : Fin N→ Fin 4)
    (hkind : ¬missing kind) :
    (fiber Γ D kind).real {z | backgroundRegime D i (restoreBackground i z)=true}=Q.θ := by
  haveI := fiber_isProbabilityMeasure Γ D hcat kind
  have hlow' : ∃r,kind r=0 := by
    by_contra hn
    exact hkind (Or.inl (by simpa only [not_exists] using hn))
  have hactive : ∃r,kind r=1 := by
    by_contra hn
    exact hkind (Or.inr (by simpa only [not_exists] using hn))
  have hpos : 0< Fintype.card {r : Fin N // kind r=0} :=
    Fintype.card_pos_iff.mpr ⟨⟨hlow'.choose,hlow'.choose_spec⟩⟩
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  let e : Fin (n+1)≃{r : Fin N // kind r=0} := (Fintype.equivFinOfCardEq hn).symm
  let b : Icc D.E.R D.E.Rp := ⟨D.E.R,le_rfl,D.E.R_le_Rp⟩
  have he : {z | backgroundRegime D i (restoreBackground i z)=true}=ᵐ[fiber Γ D kind]
      {z | publicCoin Q (fiberMinimum Γ D kind n e z)=true} := by
    filter_upwards [fiber_shape Γ D kind,fiber_menu Γ D hmenu kind,
      fiber_seed_on_present Γ D hmenu i kind n e b 0] with z hz hm hs
    have hr : ∀r,NativeMenuReports.MenuAction D.E ((restoreBackground i z).1 (i.succAbove r)).1.2 := by
      intro r;simpa only [restoreBackground_rival] using hm r
    have hk : rivalKinds D.E i (restoreBackground i z)=kind := by
      funext r;simpa only [rivalKinds,restoreBackground_rival] using hz r
    have hc : 0<(LocalCoordinates.ids D.E 1 (presentList (restoreBackground i z) i b 0)).card := by
      rw [(partial_ids D.E i (restoreBackground i z) hr b 0).2.1,hk]
      exact Finset.card_pos.mpr ⟨i.succAbove hactive.choose,
        (mem_rivalSet_succAbove i kind 1 hactive.choose).mpr hactive.choose_spec⟩
    have hh := localRegime_of_seed Γ D Q hpublic _ _ hs
    rw [if_pos hc] at hh
    apply propext
    change (_=true ↔ _=true)
    simp only [backgroundRegime,b,hh]
  rw [measureReal_def,measure_congr he]
  change ((fiber Γ D kind) ((fiberMinimum Γ D kind n e) ⁻¹' (publicCoin Q ⁻¹' {true}))).toReal=Q.θ
  rw [←Measure.map_apply (measurable_fiberMinimum Γ D kind n e)
    ((measurable_publicCoin Q) (measurableSet_singleton true)),fiberMinimum_law Γ D hcat hlow kind n e]
  exact publicCoin_true_probability Q

include hpublic hcat hlow hmenu in
lemma fiber_reject_error (i : Fin (N+1)) (kind : Fin N→ Fin 4) :
    0≤ Q.θ-(fiber Γ D kind).real {z | backgroundRegime D i (restoreBackground i z)=true} ∧
    Q.θ-(fiber Γ D kind).real {z | backgroundRegime D i (restoreBackground i z)=true}≤
      if missing kind then 1 else 0 := by
  have hle := fiber_reject_probability Γ D Q hpublic hcat hlow hmenu i kind
  constructor
  · linarith
  · by_cases h : missing kind
    · simp only [if_pos h]
      linarith [measureReal_nonneg (μ:=fiber Γ D kind)
        (s:={z | backgroundRegime D i (restoreBackground i z)=true}),Q.θ_le_one]
    · rw [if_neg h,fiber_reject_eq Γ D Q hpublic hcat hlow hmenu i kind h]
      norm_num

include hpublic hcat hlow hmenu in
theorem service_error_le_missing (i : Fin (N+1)) :
    |serviceProb D Γ i-(1-Q.θ)|≤
      (Measure.pi (fun _ : Fin N=> userLaw Γ)).real
        {row | missing (fun r=> D.E.coarseTag (row r))} := by
  let μ := deletedBackgroundLaw Γ
  let w : (Fin N→ Fin 4)→ ENNReal := fun kind=> μ (deletedTag D ⁻¹' {kind})
  haveI (kind : Fin N→ Fin 4) : IsProbabilityMeasure (fiber Γ D kind) :=
    fiber_isProbabilityMeasure Γ D hcat kind
  have hw (kind : Fin N→ Fin 4) : w kind≠⊤ := measure_ne_top _ _
  have hμ : μ=∑kind,w kind • fiber Γ D kind := deleted_fiber_sum Γ D
  have hsum : ∑kind,(w kind).toReal=1 := by
    have hh := real_finite_mixture μ w (fiber Γ D) hw hμ univ
    simpa only [measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using hh.symm
  have he := native_event_deleted Γ i {ω | backgroundRegime D i ω=true}
    (measurableSet_eq_fun (measurable_backgroundRegime D i) measurable_const)
    (fun ω=> by simp only [mem_setOf_eq,backgroundRegime,present_restore_delete])
  rw [real_finite_mixture μ w (fiber Γ D) hw hμ] at he
  have hprob (kind : Fin N→ Fin 4) :
      (fiber Γ D kind).real {z | missing (deletedTag D z)}=if missing kind then 1 else 0 := by
    have ht : {z | missing (deletedTag D z)}=ᵐ[fiber Γ D kind] {z | missing kind} := by
      filter_upwards [fiber_shape Γ D kind] with z hz
      have hh : deletedTag D z=kind := funext hz
      change missing (deletedTag D z)=missing kind
      rw [hh]
    rw [measureReal_def,measure_congr ht]
    split_ifs <;> simp_all
  have hmissing : μ.real {z | missing (deletedTag D z)}=
      ∑kind,(w kind).toReal*(if missing kind then 1 else 0) := by
    rw [real_finite_mixture μ w (fiber Γ D) hw hμ]
    simp_rw [hprob]
  have hstat : serviceProb D Γ i=1-(backgroundLaw Γ).real {ω | backgroundRegime D i ω=true} := by
    let ν := actualRegimeLaw D Γ i
    have ht : ν.mass false+ν.mass true=1 := by
      have hh:=ν.total
      have hB : (Finset.univ : Finset Bool)={false,true} := by decide
      simpa only [hB,Finset.sum_insert (by decide : false∉({true}:Finset Bool)),
        Finset.sum_singleton] using hh
    have heq : ν.mass true=(backgroundLaw Γ).real {ω | backgroundRegime D i ω=true} := by
      change (actualRegimeLaw D Γ i).mass true=_
      rw [actualRegimeLaw,FiniteLaw.ofMeasure_mass]
      rfl
    change ν.mass false=_
    rw [←heq]
    linarith
  have hnon : 0≤ serviceProb D Γ i-(1-Q.θ) :=
    sub_nonneg.mpr (serviceProb_lower Γ D Q hpublic hcat hlow hmenu i)
  rw [abs_of_nonneg hnon,hstat,he]
  have hs : Q.θ-(∑kind,(w kind).toReal*
      (fiber Γ D kind).real {z | backgroundRegime D i (restoreBackground i z)=true})=
      ∑kind,(w kind).toReal*(Q.θ-
        (fiber Γ D kind).real {z | backgroundRegime D i (restoreBackground i z)=true}) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,←Finset.sum_mul,hsum,one_mul]
  have hbound : Q.θ-(∑kind,(w kind).toReal*
      (fiber Γ D kind).real {z | backgroundRegime D i (restoreBackground i z)=true})≤
        μ.real {z | missing (deletedTag D z)} := by
    rw [hs,hmissing]
    exact Finset.sum_le_sum fun kind _=> mul_le_mul_of_nonneg_left
      (fiber_reject_error Γ D Q hpublic hcat hlow hmenu i kind).2 ENNReal.toReal_nonneg
  have hM : μ.real {z | missing (deletedTag D z)}=
      (Measure.pi (fun _ : Fin N=> userLaw Γ)).real {row | missing (fun r=> D.E.coarseTag (row r))} := by
    change (deletedBackgroundLaw Γ).real
      (Prod.fst ⁻¹' {row : Fin N→ UserDraw 2 | missing (fun r=> D.E.coarseTag (row r))})=_
    have hset : MeasurableSet {row : Fin N→ UserDraw 2 | missing (fun r=> D.E.coarseTag (row r))} :=
      ((Set.to_countable {kind : Fin N→ Fin 4 | missing kind}).measurableSet).preimage
        (measurable_pi_lambda _ fun r=> D.E.measurable_coarseTag.comp (measurable_pi_apply r))
    have hm := congrArg (fun η : Measure (Fin N→ UserDraw 2)=>
      η {row | missing (fun r=> D.E.coarseTag (row r))})
      (measurePreserving_fst (μ:=Measure.pi (fun _ : Fin N=> userLaw Γ))
        (ν:=Measure.pi (fun _ : Fin 2=> Γ.seedLaw))).map_eq
    rw [Measure.map_apply measurable_fst hset] at hm
    exact congrArg ENNReal.toReal hm
  rw [hM] at hbound
  have hb := hbound
  change Q.θ-(∑kind,(w kind).toReal*
    (fiber Γ D kind).real (restoreBackground i ⁻¹' {ω | backgroundRegime D i ω=true}))≤_ at hb
  linarith

include hpublic hcat hlow hmenu in
theorem service_error_le_exponentials (i : Fin (N+1)) (hN : 0< N)
    (s a : ℝ) (hs : 0< s) (ha : 0< a)
    (hm0 : s≤(userLaw Γ).real (D.E.coarseTag ⁻¹' {0}))
    (hm1 : a≤(userLaw Γ).real (D.E.coarseTag ⁻¹' {1})) :
    |serviceProb D Γ i-(1-Q.θ)|≤
      Real.exp (-(N:ℝ)*s^2/2)+Real.exp (-(N:ℝ)*a^2/2) := by
  let ν := Measure.pi (fun _ : Fin N=> userLaw Γ)
  have hempty (k : Fin 4) (p : ℝ) (hp : 0< p)
      (hm : p≤(userLaw Γ).real (D.E.coarseTag ⁻¹' {k})) :
      ν.real {row | ∀r,D.E.coarseTag (row r)≠k}≤ Real.exp (-(N:ℝ)*p^2/2) := by
    apply (measureReal_mono (μ:=ν) ?_).trans
      (NativeFlag.iid_bulk_count_lower_tail (userLaw Γ) (D.E.coarseTag ⁻¹' {k})
        (D.E.measurable_coarseTag (measurableSet_singleton k)) N hN hp hm)
    intro row hr
    have hc : Probability.sampleCount (D.E.coarseTag ⁻¹' {k}) row=0 := by
      unfold Probability.sampleCount
      have he : (Finset.univ.filter fun r=> row r∈D.E.coarseTag ⁻¹' {k})=∅ := by
        ext r;simp [hr r]
      rw [he,Finset.card_empty]
    change (Probability.sampleCount (D.E.coarseTag ⁻¹' {k}) row:ℝ)<p*(N:ℝ)/2
    rw [hc,Nat.cast_zero]
    positivity
  apply (service_error_le_missing Γ D Q hpublic hcat hlow hmenu i).trans
  calc
    _≤ ν.real {row | ∀r,D.E.coarseTag (row r)≠0}+
        ν.real {row | ∀r,D.E.coarseTag (row r)≠1} := by
      exact measureReal_union_le _ _
    _≤_ := add_le_add (hempty 0 s hs hm0) (hempty 1 a ha hm1)

end FCAppendix.Affine.Tail04.PartialRegimeLimit
