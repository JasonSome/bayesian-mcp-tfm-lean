import FCAppendix.Finite.PPISubcutoffPairTail
import FCAppendix.Finite.PPISubcutoffUpperMass

noncomputable section
namespace FCAppendix.PiBinomial
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

theorem pi_joint_lower_tail_le_exp_from_disjoint
    {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (E F : Set α) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (t : ℝ) (ht : 0 ≤ t) (s : Finset ι) (c : ℕ) (hα : μ.real E < 1) :
    (Measure.pi fun _ : ι => μ).real {ω | count E s ω < c ∧ count F s ω < c} ≤
      Real.exp (t*(c-1:ℕ) - (s.card-(c-1):ℕ)*
        (μ.real (F \ E)/(1-μ.real E))*(1-Real.exp (-t))) *
        ∑ r ∈ Finset.range c, pmf s.card (μ.real E) r := by
  classical
  have hcount (ω : ι → α) : count (F \ E) s ω ≤ count F s ω := by
    unfold count
    apply Finset.card_le_card
    intro l hl
    simp only [Finset.mem_filter,Set.mem_sdiff] at hl ⊢
    exact ⟨hl.1,hl.2.1⟩
  have hsub : {ω : ι → α | count E s ω < c ∧ count F s ω < c} ⊆
      {ω | count E s ω < c ∧ count (F \ E) s ω < c} := by
    intro ω hω
    exact ⟨hω.1,lt_of_le_of_lt (hcount ω) hω.2⟩
  exact (measureReal_mono hsub).trans
    (pi_pair_lower_tail_le_exp μ E (F \ E) hE (hF.diff hE)
      (Set.disjoint_left.mpr (fun _ h1 h2 => h2.2 h1)) t ht s c hα)
end FCAppendix.PiBinomial

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators
variable {N n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def ppiPairProb (Γ : FiniteGame (N+1) n c Seed) (i : Fin (N+1))
    (b : ℝ) (j l : Fin n) : ℝ :=
  (backgroundLaw Γ).real {ω | Accepts Γ i b j ω ∧ Accepts Γ i b l ω}

theorem exists_ppi_subcutoff_pair_decay (ρ a : ℝ)
    (hρ : 0 < ρ) (hra : ρ < a) (ha : a < 1) :
    ∃ η t γ : ℝ, 0 < η ∧ η < ρ/2 ∧ 0 < t ∧ 0 < γ ∧
      γ = ((1-ρ)*(ρ-η)/(1-a))*(1-Real.exp (-t))-ρ*t := by
  have hρ1 : ρ < 1 := hra.trans ha
  let η := min (ρ/4) (ρ*(a-ρ)/(4*(1-ρ)))
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηhalf : η < ρ/2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hηbound : (1-ρ)*η ≤ ρ*(a-ρ)/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*(1-ρ))).mp (min_le_right (ρ/4) (ρ*(a-ρ)/(4*(1-ρ))))
    change η*(4*(1-ρ)) ≤ ρ*(a-ρ) at hh
    nlinarith
  let rate := (1-ρ)*(ρ-η)/(1-a)
  have hrate : ρ < rate := by
    dsimp only [rate]
    apply (lt_div_iff₀ (sub_pos.mpr ha)).mpr
    nlinarith [mul_pos hρ (sub_pos.mpr hra)]
  let t := (rate-ρ)/(2*ρ)
  have ht : 0 < t := by dsimp only [t]; positivity
  have htid : 2*ρ*t = rate-ρ := by
    dsimp only [t]
    field_simp [hρ.ne']
  have htid_mul := congrArg (fun x : ℝ => t*x) htid
  let γ := rate*(1-Real.exp (-t))-ρ*t
  have hex : (1+t)*Real.exp (-t) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) (Real.exp_pos (-t)).le
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hh
    nlinarith
  have hγ : 0 < γ := by
    have hrate0 := hρ.trans hrate
    have hmult := mul_le_mul_of_nonneg_left hex hrate0.le
    have hpos : 0 < t*(rate-ρ)/2 := by positivity
    have hlower : 0 < (1+t)*γ := by
      dsimp only [γ]
      nlinarith [htid_mul]
    have hh : 0 < γ*(1+t) := by nlinarith [hlower]
    exact pos_of_mul_pos_left hh (by linarith : 0 ≤ 1+t)
  exact ⟨η,t,γ,hη,hηhalf,ht,hγ,rfl⟩

theorem ppi_pair_acceptance_le_exp_of_mass_and_rank
    (Γ : FiniteGame (N+1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hc : 0 < c) (hcN : c ≤ N+1)
    (ρ a η t γ : ℝ) (_hρ : 0 < ρ) (hρ1 : ρ < 1)
    (ha1 : a < 1) (hη : η < ρ) (ht : 0 ≤ t)
    (hcap : (c:ℝ) = ρ*((N:ℝ)+1))
    (hγ : γ = ((1-ρ)*(ρ-η)/(1-a))*(1-Real.exp (-t))-ρ*t)
    (i : Fin (N+1)) (j l : Fin n) (b : ℝ) (hb : 0 < b)
    (hrank : a ≤ alphaGt Γ j b) (hslack : alphaGt Γ j b < 1)
    (hmass : ρ-η ≤ (userLaw Γ).real (aboveAt l b \ aboveAt j b)) :
    ppiPairProb Γ i b j l ≤
      Real.exp (-γ*((N:ℝ)+1))*meanAcceptProb Γ i b := by
  classical
  let js : Fin 2 → Fin n := ![j,l]
  have heq := ppi_pair_acceptance_eq_rank Γ hA hatom js (fun k => hj (js k)) i b hb
  have htail := PiBinomial.pi_joint_lower_tail_le_exp_from_disjoint (userLaw Γ)
    (aboveAt j b) (aboveAt l b) (measurableSet_aboveAt j b)
    (measurableSet_aboveAt l b) t ht (Finset.univ.erase i) c hslack
  have hcard : (Finset.univ.erase i : Finset (Fin (N+1))).card = N := by simp
  rw [hcard] at htail
  change _ ≤ Real.exp (t*(c-1:ℕ)-(N-(c-1):ℕ)*
    ((userLaw Γ).real (aboveAt l b \ aboveAt j b)/(1-alphaGt Γ j b))*
      (1-Real.exp (-t)))*binomBelow N (alphaGt Γ j b) c at htail
  have hc1 : 1 ≤ c := hc
  have hdN : c-1 ≤ N := by omega
  have hd : ((c-1:ℕ):ℝ) = ρ*((N:ℝ)+1)-1 := by
    rw [Nat.cast_sub hc1,Nat.cast_one,hcap]
  have hnd : ((N-(c-1):ℕ):ℝ) = (1-ρ)*((N:ℝ)+1) := by
    rw [Nat.cast_sub hdN,hd]
    ring
  have hpden : 0 < 1-alphaGt Γ j b := sub_pos.mpr hslack
  have haden : 0 < 1-a := sub_pos.mpr ha1
  have hfrac : (ρ-η)/(1-a) ≤
      (userLaw Γ).real (aboveAt l b \ aboveAt j b)/(1-alphaGt Γ j b) := by
    calc
      (ρ-η)/(1-a) ≤ (ρ-η)/(1-alphaGt Γ j b) := by
        apply div_le_div_of_nonneg_left (sub_nonneg.mpr hη.le) hpden
        linarith
      _ ≤ (userLaw Γ).real (aboveAt l b \ aboveAt j b)/(1-alphaGt Γ j b) :=
        div_le_div_of_nonneg_right hmass hpden.le
  have hdnonneg : 0 ≤ (1-ρ)*((N:ℝ)+1) := by positivity
  have hepos : 0 ≤ 1-Real.exp (-t) := by
    have hh := Real.exp_le_one_iff.mpr (show -t ≤ 0 by linarith)
    linarith
  have hmult := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hfrac hdnonneg) hepos
  have hexponent : t*(c-1:ℕ)-(N-(c-1):ℕ)*
      ((userLaw Γ).real (aboveAt l b \ aboveAt j b)/(1-alphaGt Γ j b))*
      (1-Real.exp (-t)) ≤ -γ*((N:ℝ)+1) := by
    rw [hd,hnd,hγ]
    have he : (1-ρ)*((N:ℝ)+1)*((ρ-η)/(1-a)) =
        ((1-ρ)*(ρ-η)/(1-a))*((N:ℝ)+1) := by ring
    rw [he] at hmult
    nlinarith
  have hQ0 : 0 ≤ binomBelow N (alphaGt Γ j b) c :=
    (binomBelow_pos_of_lt_one N c hc _ measureReal_nonneg hslack).le
  have hbound := htail.trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexponent) hQ0)
  have heq' : ppiPairProb Γ i b j l =
      (Measure.pi fun _ : Fin (N+1) => userLaw Γ).real {d |
        PiBinomial.count (aboveAt j b) (Finset.univ.erase i) d < c ∧
        PiBinomial.count (aboveAt l b) (Finset.univ.erase i) d < c} := by
    simpa only [ppiPairProb,js,Matrix.cons_val_zero,Matrix.cons_val_one] using heq
  rw [heq',ppi_meanAcceptProb_eq_rank Γ hA hatom hj i j b hb]
  exact hbound

end FCAppendix.Bayes
