import FCAppendix.Ample.RankLimitProperties
import FCAppendix.Ample.SlackParticipation

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ENNReal BigOperators
open Ample Ample.RankMeasureTools

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem rankClassLaw_mass_eq_raw_of_ae {m c : ℕ}
    (Γ : FiniteGame m n c Seed)
    (hpositive : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.routeCount → 0 < x.2.bid)
    {j : ℕ} (hj : 1 ≤ j) :
    (rankClassLaw Γ j).real univ = actualRouteMass Γ j := by
  rw [rankClassLaw_real_apply Γ j univ MeasurableSet.univ]
  unfold actualRouteMass
  apply measureReal_congr
  filter_upwards [hpositive] with x hx
  apply propext
  change (0 < x.2.bid ∧ x.2.routeCount = j ∧ True) ↔ x.2.routeCount = j
  simp only [and_true]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨hx (by omega), h⟩

theorem exists_rank_limit_from_participation {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    {pi : ℕ → ℝ} (hp : RouteLimit Γ pi) {h : ℝ}
    (hpart : ∀ᶠ t in atTop, positiveRouteMass (Γ t) (fun _ => True) = h)
    (hpositive : ∀ᶠ t in atTop, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ),
      0 < x.2.routeCount → 0 < x.2.bid) :
    ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∃ nu : ℕ → Measure ℝ,
      RankLimit (fun t => Γ (psi t)) pi h nu := by
  classical
  let μ : ℕ → ℕ → FiniteMeasure ℝ :=
    fun t j => ⟨rankClassLaw (Γ t) j, inferInstance⟩
  have hm (t j : ℕ) : (μ t j).mass ≤ 1 := by
    have hR : ((μ t j).mass : ℝ) ≤ 1 := rankClassLaw_mass_le_one (Γ t) j
    exact_mod_cast hR
  obtain ⟨psi, hpsi, ν, hw, hνmass, hνsupp⟩ :=
    finite_marked_compactness
      (fun t (j : Fin (n+1)) => μ t j.val)
      (fun t j => hm t j.val)
      (fun t j => rankClassLaw_unit_support (Γ t) j.val)
  let νf : ℕ → FiniteMeasure ℝ := fun j =>
    if hj : j ≤ n then ν ⟨j, Nat.lt_succ_iff.mpr hj⟩ else 0
  let nu : ℕ → Measure ℝ := fun j => (νf j : Measure ℝ)
  have hfinite : ∀ j, IsFiniteMeasure (nu j) := fun j => (νf j).property
  letI : ∀ j, IsFiniteMeasure (nu j) := hfinite
  have hweak (j : ℕ) (hj : j ∈ Finset.Icc 1 n) :
      Tendsto (fun t => μ (psi t) j) atTop (𝓝 (νf j)) := by
    have hjn := (Finset.mem_Icc.mp hj).2
    simpa only [νf, dif_pos hjn] using hw ⟨j, Nat.lt_succ_iff.mpr hjn⟩
  have hmassν (j : ℕ) (hj : j ∈ Finset.Icc 1 n) : (νf j).mass ≤ 1 := by
    have hjn := (Finset.mem_Icc.mp hj).2
    simpa only [νf, dif_pos hjn] using hνmass ⟨j, Nat.lt_succ_iff.mpr hjn⟩
  have hsupportν (j : ℕ) (hj : j ∈ Finset.Icc 1 n) :
      ∀ᵐ u ∂nu j, u ∈ Icc (0 : ℝ) 1 := by
    have hjn := (Finset.mem_Icc.mp hj).2
    simpa only [nu, νf, dif_pos hjn] using hνsupp ⟨j, Nat.lt_succ_iff.mpr hjn⟩
  letI := volume_rank_interval_finite h
  let νtotal : FiniteMeasure ℝ := ⟨volume.restrict (Ioc 0 h), inferInstance⟩
  have hsumlim : Tendsto (fun t => ∑ j ∈ Finset.Icc 1 n, μ (psi t) j) atTop
      (𝓝 (∑ j ∈ Finset.Icc 1 n, νf j)) :=
    tendsto_finsetSum _ hweak
  have hsumconst : Tendsto (fun t => ∑ j ∈ Finset.Icc 1 n, μ (psi t) j) atTop
      (𝓝 νtotal) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hpsi.tendsto_atTop.eventually hpart] with t ht
    apply FiniteMeasure.toMeasure_injective
    dsimp only [νtotal]
    rw [FiniteMeasure.toMeasure_sum]
    change volume.restrict (Ioc 0 h) =
      ∑ j ∈ Finset.Icc 1 n, rankClassLaw (Γ (psi t)) j
    rw [sum_rankClassLaw, positiveRankLaw_eq_volume _ (hatom (psi t)), ht]
  have hsumf : (∑ j ∈ Finset.Icc 1 n, νf j) = νtotal :=
    tendsto_nhds_unique hsumlim hsumconst
  have hsum : (∑ j ∈ Finset.Icc 1 n, nu j) = volume.restrict (Ioc 0 h) := by
    have he := congrArg (fun m : FiniteMeasure ℝ => (m : Measure ℝ)) hsumf
    dsimp only [νtotal] at he
    simpa only [FiniteMeasure.toMeasure_sum, FiniteMeasure.toMeasure_mk, nu] using he
  have hdom (j : ℕ) (hj : j ∈ Finset.Icc 1 n) :
      nu j ≤ volume.restrict (Ioc 0 h) := by
    rw [← hsum]
    exact Finset.single_le_sum (fun _ _ => bot_le) hj
  have hatomν (j : ℕ) (hj : j ∈ Finset.Icc 1 n) (u : ℝ) : nu j {u} = 0 :=
    atomless_of_rank_domination (hdom j hj) u
  have htailEq (j : ℕ) (hj : j ∈ Finset.Icc 1 n) (u : ℝ) :
      (nu j).real (Ioi u) = rankTail nu h u j :=
    strict_tail_eq_bounded_tail
      ((support_of_rank_domination (hdom j hj)).mono fun _ hu => hu.2) u
  refine ⟨psi, hpsi, nu, hdom, hsum, ?_, ?_, ?_⟩
  · intro j hj
    have hc : Tendsto (fun t => (rankClassLaw (Γ (psi t)) j).real univ) atTop
        (𝓝 (pi j)) := by
      have hpj := (hp j (Finset.mem_Icc.mpr
        ⟨Nat.zero_le _, (Finset.mem_Icc.mp hj).2⟩)).comp hpsi.tendsto_atTop
      apply hpj.congr'
      filter_upwards [hpsi.tendsto_atTop.eventually hpositive] with t ht
      exact (rankClassLaw_mass_eq_raw_of_ae (Γ (psi t)) ht
        (Finset.mem_Icc.mp hj).1).symm
    have hwj : Tendsto (fun t => (rankClassLaw (Γ (psi t)) j).real univ) atTop
        (𝓝 ((nu j).real univ)) := by
      change Tendsto (fun t => ((μ (psi t) j).mass : ℝ)) atTop
        (𝓝 ((νf j).mass : ℝ))
      exact (NNReal.continuous_coe.tendsto _).comp (hweak j hj).mass
    exact tendsto_nhds_unique hwj hc
  · intro j hj f hf
    exact finite_tendsto_integral_of_unit_support
      (ν := fun t => μ (psi t) j) (μ := νf j)
      (fun t => rankClassLaw_unit_support (Γ (psi t)) j)
      (hsupportν j hj) (hweak j hj) hf
  · intro ε hε
    apply rank_eventually_finset (Finset.Icc 1 n)
    intro j hj
    have hdrow : ∀ᶠ t in atTop,
        rankClassLaw (Γ (psi t)) j ≤ volume.restrict (Ioc 0 h) := by
      filter_upwards [hpsi.tendsto_atTop.eventually hpart] with t ht
      simpa only [ht] using rankClassLaw_dominated (Γ (psi t)) (hatom (psi t))
        (Finset.mem_Icc.mp hj).1
    have hup := uniform_of_one_lipschitz
      (f := fun t u => (rankClassLaw (Γ (psi t)) j).real (Ioi u))
      (g := fun u => (nu j).real (Ioi u)) (h := h)
      (hdrow.mono fun t ht u _ v _ => strict_tail_one_lipschitz ht u v)
      (fun u _ v _ => strict_tail_one_lipschitz (hdom j hj) u v)
      (fun u hu => finite_tail_tendsto (fun t => hm (psi t) j)
        (hmassν j hj) (hweak j hj) hu.1 (hatomν j hj u)) ε hε
    simpa only [htailEq j hj] using hup

end FCAppendix.Bayes
