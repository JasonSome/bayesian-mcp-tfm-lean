import FCAppendix.Exclusive.LimitBounds
import FCAppendix.Finite.ScarcityBounds
import FCAppendix.Finite.FixedReceiptLimits

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter Topology

theorem exists_scarce_actual_limit
    {d : ℕ} (hd : 1 ≤ d) {M C : ℕ → ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (d+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, ExclusivePosteriorOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (E : Set ℝ) (hE : MeasurableSet E)
    (hclass : ∀ t, ExclusiveBroadcastOn (Γ t) E)
    {h rho target : ℝ} (hmass : ∀ t, (Γ t).F.real E = h)
    (hM : Tendsto M atTop atTop)
    (hrho : Tendsto (fun t => (C t : ℝ)/(M t : ℝ)) atTop (𝓝 rho))
    (hrho0 : 0 < rho) (hrhoh : rho < h)
    (htarget : target < ((d+1:ℕ):ℝ)*rho/(h*PayOnce.success (d+1) (rho/h))) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ Q mu : ℝ,
      0 < Q ∧ target < mu ∧ mu ≤ ((d+1:ℕ):ℝ) ∧
      Q ≤ h*PayOnce.success (d+1) (rho/h) ∧
      Tendsto (fun t => finiteCoverage (Γ (phi t))) atTop (𝓝 Q) ∧
      Tendsto (fun t => finiteLoad (Γ (phi t))) atTop (𝓝 (((d+1:ℕ):ℝ)*rho)) ∧
      Tendsto (fun t => finiteMultiplicity (Γ (phi t))) atTop (𝓝 mu) := by
  have hb : ∀ᶠ t in atTop, finiteCoverage (Γ t) ∈ Icc (0:ℝ) 1 := by
    filter_upwards [hM.eventually_gt_atTop 0] with t ht
    exact finiteCoverage_unit_bounds (Γ t) ht
  obtain ⟨Q,_hQunit,phi,hphi,hQ⟩ :=
    (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).tendsto_subseq' hb.frequently
  have hopt : ∀ t, ExclusiveOptimalOnPath (Γ t) (B t) :=
    fun t => exclusiveOptimalOnPath_of_feasible (Γ t) (B t) (hB t)
  obtain ⟨hQlo,hQhi,hmu,hmuLo,hmuHi⟩ := exclusive_scarce_limit_multiplicity
    (fun t => Γ (phi t)) hd (hM.comp hphi.tendsto_atTop)
    (fun t => B (phi t)) (fun t => hopt (phi t)) (fun t => hsym (phi t)) E hE
    (fun t => hclass (phi t)) (fun t => hmass (phi t))
    (hrho.comp hphi.tendsto_atTop) hrho0 hrhoh hQ
  have hload := exclusive_broadcast_load_limit Γ hd hM B hopt hsym E hE hclass
    hmass hrho hrhoh.le
  exact ⟨phi,hphi,Q,((d+1:ℕ):ℝ)*rho/Q,hrho0.trans_le hQlo,
    htarget.trans_le hmuLo,hmuHi,hQhi,hQ,hload.comp hphi.tendsto_atTop,hmu⟩

end FCAppendix.Bayes.ExclusiveConstruction
