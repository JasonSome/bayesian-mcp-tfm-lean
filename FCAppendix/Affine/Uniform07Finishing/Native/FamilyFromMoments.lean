import FCAppendix.Affine.Uniform07Finishing.Native.FiniteNativeCompletion

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem actual_upper_conditional_mass_of_raw_outcome_equality
    (Γ Δ : FiniteGame m 2 c Seed) (hm : 0< m) (v q : ℝ)
    (a : JointAction 2) (ha : a.routeCount=1)
    (hσ : Γ.σ v=Measure.dirac a)
    (hout : ∀ u : Fin m, (problem Γ u).outcome a=(problem Δ u).outcome a)
    (hmean : ∀ u : Fin m, meanAcceptProb Δ u a.bid=q) (r : Fin 3) :
    (conditionalTypeCountLaw Γ hm v).mass r=upperSingletonMass q r := by
  apply actual_upper_conditional_mass Γ hm v q a ha hσ
  intro u
  have hg := load_eq_mean Γ (by norm_num : 0<2) u a
  have hd := load_eq_mean Δ (by norm_num : 0<2) u a
  rw [ha] at hg hd
  simp only [Nat.cast_one,one_mul] at hg hd
  rw [←hg,hout u,hd,hmean u]

theorem upper_mass_formula_tendsto
    (row : Uniform07.Row) (M C : ℕ→ℕ)
    (Γ : (k : ℕ)→ FiniteGame (M k) 2 (C k) Seed)
    (hM : ∀ k, 0< M k) (hMtop : Tendsto M atTop atTop)
    (v : ℝ) (hv : Uniform07.cutoff row≤ v)
    (hcount : ∀ k (r : Fin 3), (conditionalTypeCountLaw (Γ k) (hM k) v).mass r=
      upperSingletonMass (source_upper_rank row (M k) v) r) (r : Fin 3) :
    Tendsto (fun k=>(conditionalTypeCountLaw (Γ k) (hM k) v).mass r)
      atTop (𝓝 (sourceLimitMass row v r)) := by
  have hq := (source_upper_rank_tendsto_one_at row hv).comp hMtop
  have hcont : Continuous (fun q : ℝ=>upperSingletonMass q r) := by
    fin_cases r <;> norm_num [upperSingletonMass] <;> fun_prop
  have hlim := (hcont.tendsto 1).comp hq
  have hentryv := (source_entry_lt_cutoff row).le.trans hv
  have hm : upperSingletonMass 1 r=sourceLimitMass row v r := by
    fin_cases r <;> simp [upperSingletonMass,sourceLimitMass,not_lt.mpr hentryv,not_lt.mpr hv]
  rw [←hm]
  exact hlim.congr' (.of_forall fun k=>(hcount k r).symm)

def uniformNativePair_from_actual_moments
    (start : ℕ) (hstart : 2≤ start)
    (Γ : (row : Uniform07.Row)→(k : ℕ)→
      FiniteGame (start+k) 2 (Uniform07.capacity (start+k)) unitInterval)
    (hF : ∀ row k, (Γ row k).F=Uniform07.uniformLaw)
    (hA : ∀ row k, (Γ row k).A=Schedule.affine 2 (Uniform07.eta row)
      (Uniform07.eta_pos row).le (source_eta_le_one row))
    (hG : ∀ row k, (Γ row k).G=Schedule.once 2)
    (hg : ∀ row k, (Γ row k).g=0)
    (hseed : ∀ row k, (Γ row k).seedLaw=volume)
    (hEQ : ∀ row k, IsBayesianEquilibrium (Γ row k))
    (hVis : ∀ row k, VisibleAtomless (Γ row k))
    (hIC : ∀ row k v, 0< v → v≤ 1 → ∀ᵐ a ∂(Γ row k).σ v,
      ∀ u : Fin (start+k), ∀ d : JointAction 2,
        (problem (Γ row k) u).payoff v d≤(problem (Γ row k) u).payoff v a)
    (hshape : ∀ row k v, 0< v → v< Uniform07.cutoff row →
      ∀ᵐ a ∂(Γ row k).σ v, a.bid≤ Early.bidCap row ∧ a.routeCount=2)
    (hroute : ∀ row k v, 0< v → v≤ 1 → v≠Uniform07.cutoff row →
      ∀ᵐ a ∂(Γ row k).σ v,
        a.routeCount=if v< Uniform07.cutoff row then 2 else 1)
    (ε : Uniform07.Row→ℕ→ℝ) (hεpos : ∀ row k, 0≤ε row k)
    (hε0 : ∀ row, Tendsto (ε row) atTop (𝓝 0))
    (hmom : ∀ row, ∀ᶠ k in atTop, ∀ u : Fin (start+k),
      ∀ b : Icc (0:ℝ) (Early.bidCap row),
      |((problem (Γ row k) u).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).load-
        2*sourceProductProbability row b|≤ε row k ∧
      |((problem (Γ row k) u).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-
        (sourceProductProbability row b)^2|≤ε row k)
    (hupper : ∀ row k v, Uniform07.cutoff row≤ v → ∀ r : Fin 3,
      (conditionalTypeCountLaw (Γ row k) (by omega) v).mass r=
        upperSingletonMass (source_upper_rank row (start+k) v) r) :
    UniformNativePair where
  start:=start
  start_ge_two:=hstart
  game:=Γ
  value_law:=hF
  bid_schedule:=hA
  base_schedule:=hG
  base_fee:=hg
  seed_law:=hseed
  equilibrium:=hEQ
  visible_atomless:=hVis
  fixed_value_best_response:=hIC
  fixed_value_routing:=hroute
  conditional_law:=by
    intro row v hv hv1 _ _ r
    by_cases hvt:v< Uniform07.cutoff row
    · have hversion : ∀ w : ℝ, 0< w → w< Uniform07.cutoff row → ∀ k,
          ∀ᵐ a ∂(Γ row k).σ w, a.bid≤ Early.bidCap row ∧ a.routeCount=2 ∧
            ∀ u : Fin (start+k), ∀ d : JointAction 2,
              (problem (Γ row k) u).payoff w d≤(problem (Γ row k) u).payoff w a := by
        intro w hw hwt k
        filter_upwards [hshape row k w hw hwt,
          hIC row k w hw (hwt.le.trans (Uniform07.cutoff_lt_one row).le)] with a ha hi
        exact ⟨ha.1,ha.2,hi⟩
      exact actual_lower_conditional_count_limit row (fun k=>start+k)
        (fun k=>Uniform07.capacity (start+k)) (Γ row) (fun k=>by omega)
        (hA row) (hg row) (ε row) (hεpos row) (hε0 row) (hmom row) hversion v hv hvt r
    · apply upper_mass_formula_tendsto row (fun k=>start+k)
        (fun k=>Uniform07.capacity (start+k)) (Γ row) (fun k=>by omega)
        (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat start) v (le_of_not_gt hvt)
      exact fun k r=>hupper row k v (le_of_not_gt hvt) r

theorem all_positive_conditional_counts_from_actual_moments
    (row : Uniform07.Row) (M C : ℕ→ℕ)
    (Γ : (k : ℕ)→ FiniteGame (M k) 2 (C k) Seed)
    (hM : ∀ k, 0< M k) (hMtop : Tendsto M atTop atTop)
    (hA : ∀ k, (Γ k).A=Schedule.affine 2 (Uniform07.eta row)
      (Uniform07.eta_pos row).le (sourceProduct_eta_le_one row))
    (hg : ∀ k, (Γ k).g=0)
    (ε : ℕ→ℝ) (hεpos : ∀ k, 0≤ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    (hmom : ∀ᶠ k in atTop, ∀ u : Fin (M k),
      ∀ b : Icc (0:ℝ) (Early.bidCap row),
      |((problem (Γ k) u).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).load-
        2*sourceProductProbability row b|≤ε k ∧
      |((problem (Γ k) u).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-
        (sourceProductProbability row b)^2|≤ε k)
    (hversion : ∀ v : ℝ, 0< v → v< Uniform07.cutoff row → ∀ k,
      ∀ᵐ a ∂(Γ k).σ v, a.bid≤ Early.bidCap row ∧ a.routeCount=2 ∧
        ∀ u : Fin (M k), ∀ a' : JointAction 2,
          (problem (Γ k) u).payoff v a'≤(problem (Γ k) u).payoff v a)
    (hupper : ∀ k v, Uniform07.cutoff row≤ v → ∀ r : Fin 3,
      (conditionalTypeCountLaw (Γ k) (hM k) v).mass r=
        upperSingletonMass (source_upper_rank row (M k) v) r) :
    ∀ v : ℝ, 0< v → ∀ r : Fin 3,
      Tendsto (fun k=>(conditionalTypeCountLaw (Γ k) (hM k) v).mass r)
        atTop (𝓝 (sourceLimitMass row v r)) := by
  intro v hv r
  by_cases hvt:v< Uniform07.cutoff row
  · exact actual_lower_conditional_count_limit row M C Γ hM hA hg ε hεpos hε0
      hmom hversion v hv hvt r
  · exact upper_mass_formula_tendsto row M C Γ hM hMtop v (le_of_not_gt hvt)
      (fun k r=>hupper k v (le_of_not_gt hvt) r) r

end FCAppendix.Affine.Uniform07Finishing
