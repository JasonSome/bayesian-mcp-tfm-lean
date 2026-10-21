import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06Positive
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06Guard

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology
open FCAppendix.Affine Uniform06 Uniform06.LiteralExperiment Physical

section Family
variable {C : ℕ→ Type*}
    (G : ∀ m,C m→ ProbabilityMeasure (ℝ×ℝ))
    (g : ∀ m,C m→ GuardData)
    (cm : ∀ m,C m→(Fin (m-1)→ Fin 4)→ℝ)
variable {population : ℕ→ℕ}
    (Γ : ∀ k,FiniteGame (population k) 2 (Uniform07.capacity (population k)) unitInterval)

theorem entry_full_menu (row : Uniform07.Row)
    (h05 : SourceEarlyFamily.EarlyMenuFields G g cm row)
    (hr : EntryEarlyFamilyAdapter.RootFields G g row)
    (hatom : ∀ m (e : C m) b,((G m e:Measure (ℝ×ℝ)).map Prod.snd) {b}=0)
    (hc : ∀ m (e : C m),EntryFullRestoration.CountContract row (g m e) (cm m e))
    (e : ∀ k,C (population k)) (hpopulation : Tendsto population atTop atTop)
    (hT : ∀ k (i : Fin (population k)),PositiveCountTransport row (G (population k) (e k))
      (g (population k) (e k)) (cm (population k) (e k)) (Γ k) i)
    (L : LowFamily06 Γ row)
    (hA : ∀ k,(Γ k).A=Schedule.affine 2 (Uniform07.eta row)
      (source_eta_mem row).1 (source_eta_mem row).2)
    (hg : ∀ k,(Γ k).g=0) : EntryFullMenu06 Γ row where
  compare := by
    intro w hw
    let n : ℕ→ℕ:=fun j=>population (w.market j)
    have hn : Tendsto n atTop atTop:=hpopulation.comp w.marketTendsto
    let ee : ∀ j,C (n j):=fun j=>e (w.market j)
    let s:=EntryEarlyFamilyAdapter.from_family G g cm row h05 hr n hn ee
    let cc : (j : ℕ)→(Fin (s.population j-1)→ Fin 4)→ℝ:=fun j=>cm (n j) (ee j)
    have hcount : ∀ j,EntryFullRestoration.CountContract row (s.guards j) (cc j):=
      fun j=>hc (n j) (ee j)
    have hpopulation (j : ℕ) : s.population j=n j := rfl
    have hguards (j : ℕ) : s.guards j=g (n j) (ee j) := rfl
    have hjo (j : ℕ) : s.jointLaw j=(G (n j) (ee j):Measure (ℝ×ℝ)):=
      EntryEarlyFamilyAdapter.from_family_jointLaw G g cm row h05 hr n hn ee j
    have hnull : ∀ j b,((s.jointLaw j).map Prod.snd) {b}=0:=by
      intro j b
      rw [hjo]
      exact hatom _ _ b
    have hfull:=EntryFullDominance.original_full_entry_dominance s cc hcount w.value hw hnull
    have hopt:=EntryGoodOptimizer.eventually_optimizer s w.value hw
    filter_upwards [hfull,hopt,w.marketTendsto.eventually L.small_duplicate,
      w.marketTendsto.eventually L.halfValue,
      hw.eventually (Iio_mem_nhds (ReceiptGap.entry_below_cap row))]
      with j hj hoptj hlow hhalf hvc
    by_cases hz : (w.action j).bid=0
    · have hh:=every_low_singleton_action_loses (Γ (w.market j)) (w.identity j)
        (source_eta_mem row) (hA _) (hg _) (w.valueMem j).1 hlow.1
        (source_half_value_cap row (w.valueMem j).2).1
        (source_half_value_cap row (w.valueMem j).2).2
        (hhalf (w.identity j) _ (w.valueMem j))
        (hlow.2 (w.identity j)) (w.action j) (w.route j)
        ((w.bidMem j).2.trans (min_le_right _ _))
        (by rw [hz]; exact (source_low_positive row).le)
      obtain ⟨b,hb,hgain⟩:=hh
      exact ⟨b,⟨hb.1,hb.2.trans (min_le_right _ _)⟩,hgain⟩
    · have ha0 : 0<(w.action j).bid:=lt_of_le_of_ne (w.action j).bid_nonneg (Ne.symm hz)
      let b:=EntryGoodOptimizer.chosen s w.value j
      have hlo : 0< EntryFiniteConstructor.lowerPrice row := by
        have ht:=Uniform07.cutoff_pos row
        have hx : (7/10:ℝ)≤ Uniform07.x row := by
          cases row <;> norm_num [Uniform07.x,Uniform07.xQ]
        unfold EntryFiniteConstructor.lowerPrice Uniform07.entry
        nlinarith
      have hb0 : 0< b:=hlo.trans hoptj.2.1
      have hbU : b≤ ReceiptGap.cap row:=hj.1.2.trans (min_le_right _ _)
      have hcap : ReceiptGap.cap row=Early.bidCap row := by
        rw [Early.cap_literal_product_formula]
        rfl
      refine ⟨b,⟨hb0.le,by rwa [←hcap]⟩,?_⟩
      have hsingle:=(hT _ (w.identity j)).one_payoff (hg _) (w.value j) (w.action j)
        (w.route j) ⟨ha0,((w.bidMem j).2.trans (min_le_left _ _)).trans hvc.le⟩
      have htwo:=(hT _ (w.identity j)).two_payoff (hA _) (hg _) (w.value j) ⟨hb0,hbU⟩
      rw [hsingle,htwo]
      have hh:=hj.2.2 (w.action j).bid (w.action j).bid_nonneg
      simpa only [EntryFullDominance.oneFull,EntryFullDominance.twoFull,hjo,
        hpopulation,hguards,cc,n,ee,b,div_eq_mul_inv,mul_assoc] using! hh

end Family
end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
