import FCAppendix.Affine.Uniform06.CrossoverStieltjesIC

noncomputable section
namespace FCAppendix.Affine.Uniform06.SourcePrefixConstructor

open MeasureTheory Set Filter Topology
open Rank LiteralExperiment LiteralPrefixStieltjes LiteralRankIC LowRankMeasures
open PrefixRoot CrossoverStieltjesIC CrossoverRankDensity
open FCAppendix.Affine.Uniform07

def radius (i : Row) : ℝ := cutoff i/10000
def sortEnd (i : Row) : ℝ := entry i+cutoff i/20000
def extensionEnd (i : Row) : ℝ := entry i+cutoff i/80000
def crossoverEnd (i : Row) : ℝ := entry i+cutoff i/160000
def activeError (i : Row) : ℝ := cutoff i/1000000

def sourceGuard (i : Row) (L z ε M : ℝ) : GuardData where
  multiplier := L
  radius := radius i
  rejectionRoot := z
  rejectionScale := cutoff i/1000
  requiredDemand := requiredDemand i
  margin := ε
  population := M
  seedCutoff := cutoff i/2
  countMargin := 0

structure LiteralFields (i : Row) (g : GuardData) : Prop where
  radius_eq : g.radius=radius i
  demand_eq : g.requiredDemand=requiredDemand i
  scale_eq : g.rejectionScale=cutoff i/1000
  seed_eq : g.seedCutoff=cutoff i/2
  margin_pos : 0 < g.margin
  population_pos : 0 < g.population

theorem sourceGuard_fields (i : Row) (L z ε M : ℝ) (hε : 0 < ε) (hM : 0 < M) :
    LiteralFields i (sourceGuard i L z ε M) :=
  ⟨rfl,rfl,rfl,rfl,hε,hM⟩

theorem requiredDemand_lower (i : Row) : (1/60:ℝ) ≤ requiredDemand i := by
  have ht := cutoff_pos i
  have hb := (LowChernoff.sourceTBox_ok i).1
  unfold requiredDemand
  apply (le_div_iff₀ (show 0 < 2*cutoff i by positivity)).mpr
  cases i <;> norm_num [LowChernoff.sourceTBox,delta] at hb ⊢ <;> linarith

theorem band_geometry (i : Row) :
    0 < crossoverEnd i ∧ entry i < crossoverEnd i ∧
    crossoverEnd i < extensionEnd i ∧ extensionEnd i ≤ sortEnd i ∧
    extensionEnd i < ReceiptGap.cap i ∧ entry i < sortEnd i ∧
    sortEnd i ≤ entry i+cutoff i/400 ∧
    extensionEnd i+activeError i < ActiveGraphComponent.activeBid i (sortEnd i) ∧
    LowRankMeasures.extensionEnd i < sortEnd i ∧
    sortEnd i < (tailStartQ i:ℝ)*cutoff i := by
  have ht := cutoff_pos i
  have he : 0 < entry i := mul_pos (by cases i <;> norm_num [x,xQ]) ht
  have hU : x i+1/80000 < ReceiptGap.capFactor i := by
    cases i <;> norm_num [ReceiptGap.capFactor,x,xQ,kappa,kappaQ,xi,xiQ,etaQ]
  have hUK := mul_lt_mul_of_pos_right hU ht
  rw [ReceiptGap.cap_scaled]
  have hKrep : sortEnd i=cutoff i*(x i+1/20000) := by unfold sortEnd entry; ring
  have hactive := ActiveGraphComponent.activeBid_scaled i
    (show 0 < x i+1/20000 by cases i <;> norm_num [x,xQ])
  have hgapQ : x i+1/80000+1/1000000 <
      x i*(x i+1/20000)/(kappa i*(x i+1/20000)+xi i*x i) := by
    cases i <;> norm_num [x,xQ,kappa,kappaQ,xi,xiQ,etaQ]
  have hgap := mul_lt_mul_of_pos_left hgapQ ht
  have htailQ : x i+1/20000 < (tailStartQ i:ℝ) := by
    cases i <;> norm_num [x,xQ,tailStartQ]
  have htail := mul_lt_mul_of_pos_right htailQ ht
  have hlowQ : (501/1000:ℝ) < x i+1/20000 := by cases i <;> norm_num [x,xQ]
  have hlow := mul_lt_mul_of_pos_right hlowQ ht
  rw [hKrep,hactive]
  unfold crossoverEnd extensionEnd sortEnd activeError entry LowRankMeasures.extensionEnd at *
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> nlinarith

theorem prefix_of_scalar_roots (i : Row) (g : GuardData) (hf : LiteralFields i g)
    (hL : |g.multiplier-entry i| < cutoff i/40000)
    (hz : entry i+cutoff i/100 < g.rejectionRoot) :
    PrefixConditions (xi i) g (sortEnd i) ∧
      LowRankMeasures.extensionEnd i ≤ g.multiplier-g.radius := by
  have ht := cutoff_pos i
  have hroot := abs_lt.mp hL
  have hx : (7/10:ℝ) ≤ x i := by cases i <;> norm_num [x,xQ]
  have hξ : (2/5:ℝ) ≤ xi i := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hΛ : (2/3:ℝ)*cutoff i ≤ g.multiplier := by
    have hh := mul_le_mul_of_nonneg_right hx ht.le
    unfold entry at hroot
    linarith
  have hr : (1/60:ℝ) ≤ g.requiredDemand := by rw [hf.demand_eq]; exact requiredDemand_lower i
  have hr0 : 0 < g.requiredDemand := lt_of_lt_of_le (by norm_num) hr
  have hΛ0 : 0 < g.multiplier := (mul_pos (by norm_num) ht).trans_le hΛ
  have hprod : cutoff i/225 ≤ xi i*g.requiredDemand*g.multiplier := by
    calc
      cutoff i/225 = (2/5:ℝ)*(1/60)*((2/3)*cutoff i) := by ring
      _ ≤ xi i*g.requiredDemand*g.multiplier :=
        mul_le_mul (mul_le_mul hξ hr (by norm_num) (xi_pos i).le) hΛ
          (by positivity) (mul_nonneg (xi_pos i).le hr0.le)
  have ha : 0 ≤ g.radius := by rw [hf.radius_eq]; unfold radius; positivity
  have hlo : 0 < g.multiplier-g.radius := by
    rw [hf.radius_eq]
    unfold radius
    linarith
  have hseed : g.seedCutoff < g.multiplier-g.radius := by
    rw [hf.seed_eq,hf.radius_eq]
    unfold radius
    linarith
  have hsmall : g.radius ≤ xi i*g.requiredDemand*g.multiplier/4 := by
    rw [hf.radius_eq]
    unfold radius
    linarith
  have hupper : sortEnd i ≤ g.multiplier+g.radius := by
    rw [hf.radius_eq]
    unfold sortEnd radius
    linarith
  have hrejection : sortEnd i ≤ g.rejectionRoot := by unfold sortEnd; linarith
  refine ⟨⟨hf.margin_pos,hf.population_pos,ha,hr0,?_,hlo,hseed,hupper,hrejection,hsmall⟩,?_⟩
  · rw [hf.scale_eq]
    positivity
  · rw [hf.radius_eq]
    unfold LowRankMeasures.extensionEnd radius
    linarith

theorem active_tail_lower_of_dimensional_error (i : Row)
    (G : Measure (ℝ × ℝ))
    (hactive : ∀ᵐ p ∂G, p.1 ∈ Icc (sortEnd i) (cutoff i) →
      |p.2-ActiveGraphComponent.activeBid i p.1| ≤ activeError i) :
    ∀ᵐ p ∂G, p.1 ∈ Icc ((tailStartQ i:ℝ)*cutoff i) (cutoff i) →
      (lowerActiveQ i:ℝ)*cutoff i ≤ p.2 := by
  have htail := (band_geometry i).2.2.2.2.2.2.2.2.2
  have ht := cutoff_pos i
  have ha : 0 < (tailStartQ i:ℝ) := by exact_mod_cast (tail_numeric_guard i).1
  have hbid : ActiveGraphComponent.activeBid i ((tailStartQ i:ℝ)*cutoff i)=
      (activeAtTailQ i:ℝ)*cutoff i := by
    rw [mul_comm (tailStartQ i:ℝ) (cutoff i),ActiveGraphComponent.activeBid_scaled i ha]
    have hn := normalizedActiveBid_tail i
    unfold normalizedActiveBid at hn
    rw [hn,mul_comm]
  filter_upwards [hactive] with p hp hv
  have hpK : p.1 ∈ Icc (sortEnd i) (cutoff i) := ⟨htail.le.trans hv.1,hv.2⟩
  have hm := EarlyRankCeiling.activeBid_monotone_positive i (mul_pos ha ht)
    ((mul_pos ha ht).trans_le hv.1) hv.1
  rw [hbid] at hm
  have he := (abs_le.mp (hp hpK)).1
  unfold lowerActiveQ
  push_cast
  unfold activeError at he
  linarith

theorem original_prefix_constructor (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (g : GuardData) (hf : LiteralFields i g)
    (hL : |g.multiplier-entry i| < cutoff i/40000)
    (hroot : (∫ p, sourcePsi i g.rejectionRoot p.2 ∂G)=3*requiredDemand i)
    (hactive : ∀ᵐ p ∂G, p.1 ∈ Icc (sortEnd i) (cutoff i) →
      |p.2-ActiveGraphComponent.activeBid i p.1| ≤ activeError i) :
    PrefixConditions (xi i) g (sortEnd i) ∧
      LowRankMeasures.extensionEnd i ≤ g.multiplier-g.radius := by
  have hz := source_root_above_prefix i G hvalue
    (active_tail_lower_of_dimensional_error i G hactive) hroot
  exact prefix_of_scalar_roots i g hf hL hz

section Family
variable (C : ℕ → Type*) (G : (m : ℕ) → C m → ProbabilityMeasure (ℝ × ℝ))
variable (g : (m : ℕ) → C m → GuardData)
variable (cm : (m : ℕ) → C m → (Fin (m-1) → Fin 4) → ℝ)

theorem eventually_family_crossover_stieltjes_IC (i : Row)
    (hvalue : ∀ m (E : C m), (G m E:Measure (ℝ × ℝ)).map Prod.fst=
      LowChernoff.conditionalValueLaw i)
    (hmenu : ∀ m (E : C m), ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
      p.2 ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i)))
    (hatom : ∀ m (E : C m) b, ((G m E:Measure (ℝ × ℝ)).map Prod.snd) {b}=0)
    (hfields : ∀ m (E : C m), LiteralFields i (g m E))
    (hpsi : ∀ m (E : C m),
      (∫ p, sourcePsi i (g m E).rejectionRoot p.2 ∂(G m E:Measure (ℝ × ℝ)))=3*requiredDemand i)
    (hroot : ∀ ε > (0:ℝ), ∀ᶠ m in atTop, ∀ E : C m,
      |(g m E).multiplier-entry i| < ε)
    (hactive : ∀ a > (0:ℝ), ∀ ε > (0:ℝ), ∀ᶠ m in atTop, ∀ E : C m,
      ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)), p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ ε)
    (hIC : ∀ m (E : C m), ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
      ∀ a ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i)),
      payoff (eta i) p.1 a (sourceSuccess i m (G m E) (g m E) (cm m E) a)
        (sourceDuplicate i m (G m E) (g m E) (cm m E) a) ≤
      payoff (eta i) p.1 p.2 (sourceSuccess i m (G m E) (g m E) (cm m E) p.2)
        (sourceDuplicate i m (G m E) (g m E) (cm m E) p.2)) :
    ∀ᶠ m in atTop, ∀ E : C m, ∀ lo : ℝ, 0 < lo → lo ≤ crossoverEnd i →
      ∃ (F D : StieltjesFunction ℝ),
        Continuous F ∧ Continuous D ∧ IsFiniteMeasure F.measure ∧ IsFiniteMeasure D.measure ∧
        (∀ b ∈ Icc (lo/2) (crossoverEnd i),
          F b=sourceSuccess i m (G m E) (g m E) (cm m E) b ∧
          D b=sourceDuplicate i m (G m E) (g m E) (cm m E) b) ∧
        (let U := (lowBidMeasure i (G m E) (crossoverEnd i)).support ∩ Icc lo (crossoverEnd i)
         F.measure.restrict U ≪ volume ∧ D.measure.restrict U ≪ volume ∧
           (F.measure.restrict U).withDensityᵥ
             (fun b => PureRankCounts.sourceRank (cutoff i) ((G m E:Measure (ℝ × ℝ)).map Prod.snd) b-b)=
             (volume.restrict U).withDensityᵥ (fun b =>
               sourceSuccess i m (G m E) (g m E) (cm m E) b+
                 eta i*sourceDuplicate i m (G m E) (g m E) (cm m E) b)+
             (D.measure.restrict U).withDensityᵥ (fun b => eta i*b)) := by
  have ht := cutoff_pos i
  have ha : 0 < cutoff i/40000 := by positivity
  have he : 0 < activeError i := by unfold activeError; positivity
  filter_upwards [eventually_source_crossover_stieltjes_IC i,
    hroot (cutoff i/40000) ha,hactive (cutoff i/40000) ha (activeError i) he]
      with m hst hr hac
  intro E lo hlo hloH
  have hA : ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)), p.1 ∈ Icc (sortEnd i) (cutoff i) →
      |p.2-ActiveGraphComponent.activeBid i p.1| ≤ activeError i := by
    filter_upwards [hac E] with p hp hv
    apply hp ⟨?_,hv.2⟩
    unfold sortEnd at hv
    linarith [hv.1]
  have hp := original_prefix_constructor i (G m E) (hvalue m E) (g m E) (hfields m E)
    (hr E) (hpsi m E) hA
  obtain ⟨hH,_,hHZ,hZK,hZcap,hK,hKfloor,hgap,_,_⟩ := band_geometry i
  exact hst (G m E) inferInstance (hvalue m E) (hmenu m E) (hatom m E)
    (g m E) (crossoverEnd i) (extensionEnd i) (sortEnd i) (activeError i) (cm m E)
    hH hHZ hZK hZcap hK hKfloor hp.1 hp.2 hgap hA (hIC m E) lo hlo hloH

end Family
end FCAppendix.Affine.Uniform06.SourcePrefixConstructor
