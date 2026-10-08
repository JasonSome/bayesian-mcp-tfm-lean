import FCAppendix.Exclusive.CompletionNarrowFamily
import FCAppendix.Exclusive.ScarceAssembly
import FCAppendix.Exclusive.OnceAssembly
import FCAppendix.Exclusive.OnceLimits

noncomputable section
namespace FCAppendix.Completion.Exclusive
open MeasureTheory ProbabilityTheory Filter Topology Set
open FCAppendix Game Bayes Exclusive Exclusive.Narrow
open scoped BigOperators ProbabilityTheory

theorem scarce_mass_and_low_cutoff (n : ℕ) (hn : 2 ≤ n) {rho zeta L g : ℝ}
    (hrho : 0 < rho) (hbeta : (n:ℝ)*rho < 1) (hzeta : 0 < zeta) (hL : 0 < L) :
    ∃ h : ℝ, rho < h ∧ h < (n:ℝ)*rho ∧ h < 1 ∧
      (n:ℝ)-zeta < (n:ℝ)*rho/(h*PayOnce.success n (rho/h)) ∧
      g < g+L*(1-(n:ℝ)*rho)/(1-h) ∧
      g+L*(1-(n:ℝ)*rho)/(1-h) < g+L := by
  obtain ⟨h,hrh,hhb,hh1,hmul⟩ := exists_scarce_parameters n hn hrho hbeta hzeta
  refine ⟨h,hrh,hhb,hh1,hmul,?_,?_⟩
  · exact lt_add_of_pos_right _ (div_pos (mul_pos hL (sub_pos.mpr hbeta)) (sub_pos.mpr hh1))
  · have hr : (1-(n:ℝ)*rho)/(1-h) < 1 := by
      apply (div_lt_one (sub_pos.mpr hh1)).mpr
      linarith
    have h := mul_lt_mul_of_pos_left hr hL
    simpa [mul_div_assoc] using add_lt_add_left h g

theorem scarce_existing_final {d : ℕ} (hd : 1 ≤ d) {rho zeta : ℝ}
    (hrho : 0 < rho) (hbeta : ((d+1:ℕ):ℝ)*rho < 1) (hzeta : 0 < zeta) :
    ∃ h : ℝ, rho < h ∧ h < ((d+1:ℕ):ℝ)*rho ∧ h < 1 ∧
      ∀ {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
        (Γ : (t : ℕ) → FiniteGame (M t) (d+1) (C t) Seed)
        (B : (t : ℕ) → PosteriorSystem (Γ t)),
        (∀ t, ExclusiveOptimalOnPath (Γ t) (B t)) →
        (∀ t, SymmetricProposersOnPath (Γ t)) →
        ∀ E : Set ℝ, MeasurableSet E →
        (∀ t, ExclusiveBroadcastOn (Γ t) E) → (∀ t, (Γ t).F.real E = h) →
        Tendsto M atTop atTop → Tendsto (fun t => (C t:ℝ)/M t) atTop (𝓝 rho) →
        Tendsto (fun t => finiteLoad (Γ t)) atTop (𝓝 (((d+1:ℕ):ℝ)*rho)) ∧
        ∀ᶠ t in atTop, 0 < finiteCoverage (Γ t) ∧
          ((d+1:ℕ):ℝ)-zeta < finiteMultiplicity (Γ t) ∧ finiteMultiplicity (Γ t) ≤ d+1 := by
  obtain ⟨h,hrh,hhb,hh1,hmu⟩ := exists_scarce_parameters (d+1) (by omega) hrho hbeta hzeta
  refine ⟨h,hrh,hhb,hh1,?_⟩
  intro Seed _ M C Γ B hB hsym E hE hclass hmass hM hcap
  simpa only [Nat.cast_add, Nat.cast_one] using
    exclusive_scarce_eventual_multiplicity Γ hd hM B hB hsym E hE hclass hmass hcap hrho hrh hmu

theorem scarce_subsequence_final
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    (Γ : (t : ℕ) → FiniteGame (M t) (d+1) (C t) Seed)
    (hd : 1 ≤ d) (hM : Tendsto M atTop atTop)
    (B : (t : ℕ) → PosteriorSystem (Γ t))
    (hB : ∀ t, ExclusiveOptimalOnPath (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (E : Set ℝ) (hE : MeasurableSet E) (hclass : ∀ t, ExclusiveBroadcastOn (Γ t) E)
    {h rho Q : ℝ} (hmass : ∀ t, (Γ t).F.real E = h)
    (hcap : Tendsto (fun t => (C t:ℝ)/M t) atTop (𝓝 rho))
    (hrho : 0 < rho) (hrh : rho < h)
    (hQ : Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 Q)) :
    0 < Q ∧ Q ≤ h*PayOnce.success (d+1) (rho/h) ∧
      Tendsto (fun t => finiteMultiplicity (Γ t)) atTop (𝓝 (((d+1:ℕ):ℝ)*rho/Q)) ∧
      ((d+1:ℕ):ℝ)*rho/(h*PayOnce.success (d+1) (rho/h)) ≤ ((d+1:ℕ):ℝ)*rho/Q := by
  obtain ⟨hlo,hup,hlim,hmu,_⟩ := exclusive_scarce_limit_multiplicity
    Γ hd hM B hB hsym E hE hclass hmass hcap hrho hrh hQ
  exact ⟨hrho.trans_le hlo,hup,hlim,hmu⟩

theorem once_finite_outcome_chain
    {n m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (hc : 0 < c) (hcm : c < m) (H : ExclusiveOnceEquilibrium Γ B)
    (j : Fin n) (hh : 0 < exclusiveActiveMass Γ) :
    ExclusiveOnceContributionBounds Γ j :=
  exclusive_once_contribution_bounds Γ hc hcm B H j hh

theorem once_existing_final
    {n : ℕ} {M C : ℕ → ℕ} {Seeds : ℕ → Type*} [∀ t, MeasurableSpace (Seeds t)]
    (Γ : (t : ℕ) → FiniteGame (M t) n (C t) (Seeds t))
    (B : (t : ℕ) → PosteriorSystem (Γ t)) (hn : 2 ≤ n)
    (hvalid : ∀ᶠ t in atTop, 0 < C t ∧ C t < M t ∧ ExclusiveOnceEquilibrium (Γ t) (B t))
    (F : Measure ℝ) (g : ℝ) (hF : ∀ t, (Γ t).F = F) (hg : ∀ t, (Γ t).g = g)
    {rho Q Load : ℝ} (hrho : 0 < rho) (hrh : rho < F.real (Ioi g))
    (hcap : Tendsto (fun t => (C t:ℝ)/M t) atTop (𝓝 rho))
    (hQ : Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 Q))
    (hLoad : Tendsto (fun t => finiteLoad (Γ t)) atTop (𝓝 Load)) :
    Q ≤ F.real (Ioi g)*PayOnce.success n (rho/F.real (Ioi g)) ∧
      Q < min ((n:ℝ)*rho) (F.real (Ioi g)) ∧
      ((n:ℝ)-1)*Q^2/((n:ℝ)^2*F.real (Ioi g)) ≤ Load-Q ∧
      (0 < Q → 0 < Load-Q) := by
  obtain ⟨hQcap,hstrict,hdup,hpos⟩ := exclusive_once_existing_equilibrium_limit
    Γ B hn hvalid F g hF hg hrho hrh hcap hQ hLoad
  exact ⟨by simpa [PayOnce.success] using hQcap,hQcap.trans_lt hstrict,hdup,hpos⟩

theorem once_existing_sequence_final
    {n : ℕ} {M C : ℕ → ℕ} {Seeds : ℕ → Type*} [∀ t, MeasurableSpace (Seeds t)]
    (Γ : (t : ℕ) → FiniteGame (M t) n (C t) (Seeds t))
    (B : (t : ℕ) → PosteriorSystem (Γ t)) (hn : 2 ≤ n)
    (hM : Tendsto M atTop atTop)
    (heq : ∀ᶠ t in atTop, ExclusiveOnceEquilibrium (Γ t) (B t))
    (F : Measure ℝ) (g : ℝ) (hF : ∀ t, (Γ t).F = F) (hg : ∀ t, (Γ t).g = g)
    {rho Q Load : ℝ} (hrho : 0 < rho) (hrh : rho < F.real (Ioi g))
    (hcap : Tendsto (fun t => (C t:ℝ)/M t) atTop (𝓝 rho))
    (hQ : Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 Q))
    (hLoad : Tendsto (fun t => finiteLoad (Γ t)) atTop (𝓝 Load)) :
    Q ≤ F.real (Ioi g)*PayOnce.success n (rho/F.real (Ioi g)) ∧
      F.real (Ioi g)*PayOnce.success n (rho/F.real (Ioi g)) <
        min ((n:ℝ)*rho) (F.real (Ioi g)) ∧
      Q < min ((n:ℝ)*rho) (F.real (Ioi g)) ∧
      ((n:ℝ)-1)*Q^2/((n:ℝ)^2*F.real (Ioi g)) ≤ Load-Q ∧
      (0 < Q → 0 < Load-Q) := by
  obtain ⟨hQcap,hstrict,hdup,hpos⟩ := exclusive_once_existing_sequence
    Γ B hn hM heq F g hF hg hrho hrh hcap hQ hLoad
  refine ⟨?_,?_,hQcap.trans_lt hstrict,hdup,hpos⟩
  · simpa only [PayOnce.success] using hQcap
  · simpa only [PayOnce.success] using hstrict

theorem once_existing_subsequence_final
    {n : ℕ} {M C : ℕ → ℕ} {Seeds : ℕ → Type*} [∀ t, MeasurableSpace (Seeds t)]
    (Γ : (t : ℕ) → FiniteGame (M t) n (C t) (Seeds t))
    (B : (t : ℕ) → PosteriorSystem (Γ t)) (hn : 2 ≤ n)
    (hM : Tendsto M atTop atTop)
    (heq : ∀ᶠ t in atTop, ExclusiveOnceEquilibrium (Γ t) (B t))
    (F : Measure ℝ) (g : ℝ) (hF : ∀ t, (Γ t).F = F) (hg : ∀ t, (Γ t).g = g)
    {rho : ℝ} (hrho : 0 < rho) (hrh : rho < F.real (Ioi g))
    (hcap : Tendsto (fun t => (C t:ℝ)/M t) atTop (𝓝 rho))
    (phi : ℕ → ℕ) (hphi : StrictMono phi) {Q Load : ℝ}
    (hQ : Tendsto (fun t => finiteCoverage (Γ (phi t))) atTop (𝓝 Q))
    (hLoad : Tendsto (fun t => finiteLoad (Γ (phi t))) atTop (𝓝 Load)) :
    Q ≤ F.real (Ioi g)*PayOnce.success n (rho/F.real (Ioi g)) ∧
      F.real (Ioi g)*PayOnce.success n (rho/F.real (Ioi g)) <
        min ((n:ℝ)*rho) (F.real (Ioi g)) ∧
      Q < min ((n:ℝ)*rho) (F.real (Ioi g)) ∧
      ((n:ℝ)-1)*Q^2/((n:ℝ)^2*F.real (Ioi g)) ≤ Load-Q ∧
      (0 < Q → 0 < Load-Q) := by
  exact once_existing_sequence_final (fun t => Γ (phi t)) (fun t => B (phi t)) hn
    (hM.comp hphi.tendsto_atTop) (hphi.tendsto_atTop.eventually heq)
    F g (fun t => hF (phi t)) (fun t => hg (phi t)) hrho hrh
    (hcap.comp hphi.tendsto_atTop) hQ hLoad

theorem scarce_existing_subsequence_final
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    (Γ : (t : ℕ) → FiniteGame (M t) (d+1) (C t) Seed)
    (hd : 1 ≤ d) (hM : Tendsto M atTop atTop)
    (B : (t : ℕ) → PosteriorSystem (Γ t))
    (hB : ∀ t, ExclusiveOptimalOnPath (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (E : Set ℝ) (hE : MeasurableSet E) (hclass : ∀ t, ExclusiveBroadcastOn (Γ t) E)
    {h rho : ℝ} (hmass : ∀ t, (Γ t).F.real E = h)
    (hcap : Tendsto (fun t => (C t:ℝ)/M t) atTop (𝓝 rho))
    (hrho : 0 < rho) (hrh : rho < h)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) {Q : ℝ}
    (hQ : Tendsto (fun t => finiteCoverage (Γ (phi t))) atTop (𝓝 Q)) :
    0 < Q ∧ Q ≤ h*PayOnce.success (d+1) (rho/h) ∧
      Tendsto (fun t => finiteMultiplicity (Γ (phi t))) atTop
        (𝓝 (((d+1:ℕ):ℝ)*rho/Q)) ∧
      ((d+1:ℕ):ℝ)*rho/(h*PayOnce.success (d+1) (rho/h)) ≤ ((d+1:ℕ):ℝ)*rho/Q := by
  exact scarce_subsequence_final (fun t => Γ (phi t)) hd (hM.comp hphi.tendsto_atTop)
    (fun t => B (phi t)) (fun t => hB (phi t)) (fun t => hsym (phi t))
    E hE (fun t => hclass (phi t)) (fun t => hmass (phi t))
    (hcap.comp hphi.tendsto_atTop) hrho hrh hQ

theorem eventual_strict_coverage_comparison
    {M C n : ℕ → ℕ} {SeedsE SeedsD : ℕ → Type*}
    [∀ t, MeasurableSpace (SeedsE t)] [∀ t, MeasurableSpace (SeedsD t)]
    (efficient : (t : ℕ) → FiniteGame (M t) (n t) (C t) (SeedsE t))
    (duplicative : (t : ℕ) → FiniteGame (M t) (n t) (C t) (SeedsD t))
    {Qe Qd : ℝ}
    (hE : Tendsto (fun t => finiteCoverage (efficient t)) atTop (𝓝 Qe))
    (hD : Tendsto (fun t => finiteCoverage (duplicative t)) atTop (𝓝 Qd))
    (hgap : Qd < Qe) :
    ∀ᶠ t in atTop, finiteCoverage (duplicative t) < finiteCoverage (efficient t) := by
  have hg := (hE.sub hD).eventually (eventually_gt_nhds (sub_pos.mpr hgap))
  exact hg.mono fun t ht => sub_pos.mp ht

theorem once_positive_duplicate_gap {n : ℕ} (hn : 2 ≤ n) {h Q D : ℝ}
    (hh : 0 < h) (hQ : 0 < Q)
    (hbound : ((n:ℝ)-1)*Q^2/((n:ℝ)^2*h) ≤ D)
    (dup : ℕ → ℝ) (hdup : Tendsto dup atTop (𝓝 D)) :
    ∀ᶠ t in atTop, ((n:ℝ)-1)*Q^2/(2*((n:ℝ)^2*h)) < dup t := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnm : 0 < (n:ℝ)-1 := by linarith
  have hn0 : 0 < (n:ℝ) := by linarith
  have hpos : 0 < ((n:ℝ)-1)*Q^2/((n:ℝ)^2*h) :=
    div_pos (mul_pos hnm (sq_pos_of_pos hQ)) (mul_pos (sq_pos_of_pos hn0) hh)
  apply hdup.eventually
  apply eventually_gt_nhds
  have hhalf : ((n:ℝ)-1)*Q^2/(2*((n:ℝ)^2*h)) =
      (((n:ℝ)-1)*Q^2/((n:ℝ)^2*h))/2 := by ring
  rw [hhalf]
  linarith

end FCAppendix.Completion.Exclusive
