import FCAppendix.Finite.PPISubcutoffPairGame
import FCAppendix.Finite.PPIRankTypes

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators

variable {m N n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_ppi_accepts_implies_rank_nonneg
    (Γ : FiniteGame m n c Seed) (hA : Γ.A = Schedule.ppi n)
    (j : Fin n) (hj : ProposerRationalAtFeasibleLists Γ j)
    (i : Fin m) (b : ℝ) (hb : 0 ≤ b) :
    ∀ᵐ ω ∂backgroundLaw Γ,
      Accepts Γ i b j ω → rivals i (aboveAt j b) ω < c := by
  have hrank := measurableSet_rivals_lt (Seed := Seed) i (aboveAt j b)
    (measurableSet_aboveAt j b) c
  have hacc := measurableSet_accepts Γ i b j
  have hp : MeasurableSet {ω : Background m n Seed |
      Accepts Γ i b j ω → rivals i (aboveAt j b) ω < c} := by
    simpa only [imp_iff_not_or, Set.compl_setOf, Set.setOf_or] using
      hacc.compl.union hrank
  have hcharge (r : ℕ) (_hr : 0 < r) (_hrn : r ≤ n) :
      1 * (r : ℝ) ≤ Γ.A.charge r := by
    simp [hA, Schedule.ppi]
  apply (Measure.ae_prod_iff_ae_ae hp).mpr
  obtain ⟨belief, hopt⟩ := hj
  apply Filter.Eventually.of_forall
  intro d
  let ℓ := presentDrawList d i b j
  have hs := hopt ℓ (presentDrawList_feasible d i b hb j)
  have hseeds :=
    (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae hs
  filter_upwards [hseeds] with s hS
  simpa only [div_one] using
    (few_rivals_of_accepts_local_nonneg Γ j i 1 (by norm_num)
      hcharge b hb (d, s) (belief ℓ) hS)

theorem ppi_pair_le_rank_pair_nonneg
    (Γ : FiniteGame (N+1) n c Seed) (hA : Γ.A = Schedule.ppi n)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N+1)) (j l : Fin n) (b : ℝ) (hb : 0 ≤ b) :
    ppiPairProb Γ i b j l ≤
      (Measure.pi fun _ : Fin (N+1) => userLaw Γ).real {draws |
        PiBinomial.count (aboveAt j b) (Finset.univ.erase i) draws < c ∧
        PiBinomial.count (aboveAt l b) (Finset.univ.erase i) draws < c} := by
  have hbound : ppiPairProb Γ i b j l ≤
      (backgroundLaw Γ).real {ω | rivals i (aboveAt j b) ω < c ∧
        rivals i (aboveAt l b) ω < c} := by
    unfold ppiPairProb
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [ae_ppi_accepts_implies_rank_nonneg Γ hA j (hj j) i b hb,
      ae_ppi_accepts_implies_rank_nonneg Γ hA l (hj l) i b hb] with ω hjω hlω hω
    exact ⟨hjω hω.1, hlω hω.2⟩
  have hset : {ω : Background (N+1) n Seed |
      rivals i (aboveAt j b) ω < c ∧ rivals i (aboveAt l b) ω < c} =
      {draws : UserProfile (N+1) n |
        PiBinomial.count (aboveAt j b) (Finset.univ.erase i) draws < c ∧
        PiBinomial.count (aboveAt l b) (Finset.univ.erase i) draws < c} ×ˢ Set.univ := by
    ext ω
    simp [rivals]
  rw [hset, backgroundLaw, measureReal_prod_prod, probReal_univ, mul_one] at hbound
  exact hbound

theorem ppi_zero_pair_le_rank_pair
    (Γ : FiniteGame (N+1) n c Seed) (hA : Γ.A = Schedule.ppi n)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N+1)) (j l : Fin n) :
    ppiPairProb Γ i 0 j l ≤
      (Measure.pi fun _ : Fin (N+1) => userLaw Γ).real {draws |
        PiBinomial.count (aboveAt j 0) (Finset.univ.erase i) draws < c ∧
        PiBinomial.count (aboveAt l 0) (Finset.univ.erase i) draws < c} := by
  exact ppi_pair_le_rank_pair_nonneg Γ hA hj i j l 0 le_rfl

theorem ppi_rank_pair_le_exp_of_mass_and_rank
    (Γ : FiniteGame (N+1) n c Seed) (hc : 0 < c) (hcN : c ≤ N+1)
    (ρ a η t γ : ℝ) (hρ1 : ρ < 1) (ha1 : a < 1)
    (hη : η < ρ) (ht : 0 ≤ t)
    (hcap : (c : ℝ) = ρ*((N : ℝ)+1))
    (hγ : γ = ((1-ρ)*(ρ-η)/(1-a))*(1-Real.exp (-t))-ρ*t)
    (i : Fin (N+1)) (j l : Fin n) (b : ℝ)
    (hrank : a ≤ alphaGt Γ j b) (hslack : alphaGt Γ j b < 1)
    (hmass : ρ-η ≤ (userLaw Γ).real (aboveAt l b \ aboveAt j b)) :
    (Measure.pi fun _ : Fin (N+1) => userLaw Γ).real {draws |
      PiBinomial.count (aboveAt j b) (Finset.univ.erase i) draws < c ∧
      PiBinomial.count (aboveAt l b) (Finset.univ.erase i) draws < c} ≤
        Real.exp (-γ*((N : ℝ)+1))*binomBelow N (alphaGt Γ j b) c := by
  classical
  have htail := PiBinomial.pi_joint_lower_tail_le_exp_from_disjoint (userLaw Γ)
    (aboveAt j b) (aboveAt l b) (measurableSet_aboveAt j b)
    (measurableSet_aboveAt l b) t ht (Finset.univ.erase i) c hslack
  have hcard : (Finset.univ.erase i : Finset (Fin (N+1))).card = N := by simp
  rw [hcard] at htail
  change _ ≤ Real.exp (t*(c-1 : ℕ)-(N-(c-1) : ℕ)*
    ((userLaw Γ).real (aboveAt l b \ aboveAt j b)/(1-alphaGt Γ j b))*
      (1-Real.exp (-t)))*binomBelow N (alphaGt Γ j b) c at htail
  have hc1 : 1 ≤ c := hc
  have hdN : c-1 ≤ N := by omega
  have hd : ((c-1 : ℕ) : ℝ) = ρ*((N : ℝ)+1)-1 := by
    rw [Nat.cast_sub hc1, Nat.cast_one, hcap]
  have hnd : ((N-(c-1) : ℕ) : ℝ) = (1-ρ)*((N : ℝ)+1) := by
    rw [Nat.cast_sub hdN, hd]
    ring
  have hpden : 0 < 1-alphaGt Γ j b := sub_pos.mpr hslack
  have haden : 0 < 1-a := sub_pos.mpr ha1
  have hfrac : (ρ-η)/(1-a) ≤
      (userLaw Γ).real (aboveAt l b \ aboveAt j b)/(1-alphaGt Γ j b) := by
    apply (div_le_div_iff₀ haden hpden).mpr
    calc
      (ρ-η)*(1-alphaGt Γ j b) ≤ (ρ-η)*(1-a) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left hrank 1) (sub_nonneg.mpr hη.le)
      _ ≤ (userLaw Γ).real (aboveAt l b \ aboveAt j b)*(1-a) :=
        mul_le_mul_of_nonneg_right hmass haden.le
  have hdnonneg : 0 ≤ (1-ρ)*((N : ℝ)+1) :=
    mul_nonneg (sub_nonneg.mpr hρ1.le) (by positivity)
  have hepos : 0 ≤ 1-Real.exp (-t) := by
    have hh := Real.exp_le_one_iff.mpr (show -t ≤ 0 by linarith)
    linarith
  have hmult := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hfrac hdnonneg) hepos
  have hexponent : t*(c-1 : ℕ)-(N-(c-1) : ℕ)*
      ((userLaw Γ).real (aboveAt l b \ aboveAt j b)/(1-alphaGt Γ j b))*
      (1-Real.exp (-t)) ≤ -γ*((N : ℝ)+1) := by
    rw [hd, hnd, hγ]
    have he : (1-ρ)*((N : ℝ)+1)*((ρ-η)/(1-a)) =
        ((1-ρ)*(ρ-η)/(1-a))*((N : ℝ)+1) := by ring
    rw [he] at hmult
    nlinarith
  have hQ0 : 0 ≤ binomBelow N (alphaGt Γ j b) c :=
    (binomBelow_pos_of_lt_one N c hc _ measureReal_nonneg hslack).le
  exact htail.trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexponent) hQ0)

end FCAppendix.Bayes
