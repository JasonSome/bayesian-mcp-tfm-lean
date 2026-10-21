import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalOptimizerCover
import FCAppendix.Affine.Uniform06.EntryNativeSource

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology
open FCAppendix.Affine Uniform06 Uniform06.LiteralExperiment Physical

variable {m : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure PositiveCountTransport (row : Uniform07.Row)
    (G : Measure (ℝ×ℝ)) (g : GuardData)
    (cm : (Fin (m-1)→ Fin 4)→ℝ)
    (Γ : FiniteGame m 2 (Uniform07.capacity m) Seed) (i : Fin m) : Prop where
  success : ∀ b∈Ioc (0:ℝ) (ReceiptGap.cap row),
    Physical.success Γ i b=sourceSuccess row m G g cm b
  duplicate : ∀ b∈Ioc (0:ℝ) (ReceiptGap.cap row),
    Physical.duplicate Γ i b=sourceDuplicate row m G g cm b

theorem PositiveCountTransport.mean
    {row : Uniform07.Row} {G : Measure (ℝ×ℝ)} {g : GuardData}
    {cm : (Fin (m-1)→ Fin 4)→ℝ}
    {Γ : FiniteGame m 2 (Uniform07.capacity m) Seed} {i : Fin m}
    (T : PositiveCountTransport row G g cm Γ i)
    {b : ℝ} (hb : b∈Ioc (0:ℝ) (ReceiptGap.cap row)) :
    q Γ i b=(sourceSuccess row m G g cm b+sourceDuplicate row m G g cm b)/2 := by
  have h:=success_eq_two_q_sub_duplicate Γ i hb.1.le
  rw [T.success b hb,T.duplicate b hb] at h
  linarith

theorem PositiveCountTransport.one_payoff
    {row : Uniform07.Row} {G : Measure (ℝ×ℝ)} {g : GuardData}
    {cm : (Fin (m-1)→ Fin 4)→ℝ}
    {Γ : FiniteGame m 2 (Uniform07.capacity m) Seed} {i : Fin m}
    (T : PositiveCountTransport row G g cm Γ i) (hg : Γ.g=0)
    (v : ℝ) (a : JointAction 2) (ha : a.routeCount=1)
    (hb : a.bid∈Ioc (0:ℝ) (ReceiptGap.cap row)) :
    (problem Γ i).payoff v a=(v-a.bid)*
      (sourceSuccess row m G g cm a.bid+sourceDuplicate row m G g cm a.bid)/2 := by
  rw [singleton_payoff Γ (by norm_num : 0<2) i a ha,hg,sub_zero]
  change (v-a.bid)*q Γ i a.bid=_
  rw [T.mean hb]
  ring

theorem PositiveCountTransport.two_payoff
    {row : Uniform07.Row} {G : Measure (ℝ×ℝ)} {g : GuardData}
    {cm : (Fin (m-1)→ Fin 4)→ℝ}
    {Γ : FiniteGame m 2 (Uniform07.capacity m) Seed} {i : Fin m}
    (T : PositiveCountTransport row G g cm Γ i)
    (hA : Γ.A=Schedule.affine 2 (Uniform07.eta row)
      (source_eta_mem row).1 (source_eta_mem row).2) (hg : Γ.g=0)
    (v : ℝ) {b : ℝ} (hb : b∈Ioc (0:ℝ) (ReceiptGap.cap row)) :
    (problem Γ i).payoff v (two b)=
      (v-b)*sourceSuccess row m G g cm b-
        Uniform07.eta row*b*sourceDuplicate row m G g cm b := by
  rw [LowBody.native_affine_zero_fee_payoff Γ
    (source_eta_mem row).1 (source_eta_mem row).2 hA hg]
  simp only [two_bid hb.1.le]
  change (v-b)*Physical.success Γ i b-Uniform07.eta row*b*Physical.duplicate Γ i b=_
  rw [T.success b hb,T.duplicate b hb]

theorem PositiveCountTransport.every_fixed_value_counts
    {row : Uniform07.Row} {G : Measure (ℝ×ℝ)} {g : GuardData}
    {cm : (Fin (m-1)→ Fin 4)→ℝ}
    {Γ : FiniteGame m 2 (Uniform07.capacity m) Seed} {i : Fin m}
    (T : PositiveCountTransport row G g cm Γ i) :
    ∀ v b : ℝ,b∈Ioc (0:ℝ) (ReceiptGap.cap row) →
      (EntryNativeSource.fixedValueCountLaw Γ i v (two b)).mass 0=
        1-sourceSuccess row m G g cm b ∧
      (EntryNativeSource.fixedValueCountLaw Γ i v (two b)).mass 1=
        sourceSuccess row m G g cm b-sourceDuplicate row m G g cm b ∧
      (EntryNativeSource.fixedValueCountLaw Γ i v (two b)).mass 2=
        sourceDuplicate row m G g cm b := by
  intro v b hb
  have h:=EntryNativeSource.two_count_masses ((problem Γ i).outcome (two b))
  change ((problem Γ i).outcome (two b)).mass 0=1-Physical.success Γ i b ∧
    ((problem Γ i).outcome (two b)).mass 1=Physical.success Γ i b-Physical.duplicate Γ i b ∧
    ((problem Γ i).outcome (two b)).mass 2=Physical.duplicate Γ i b at h
  simpa only [EntryNativeSource.fixedValueCountLaw,T.success b hb,T.duplicate b hb] using h

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
