import FCAppendix.Affine.UniformFinite.SourceGuards
import FCAppendix.Affine.Uniform06.PreciseFamilyFields
import FCAppendix.Affine.Uniform06.EntryFullRestoration

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine
open Uniform06 Uniform06.LiteralExperiment
open scoped BigOperators

theorem demand_eq (i : Uniform07.Row) :
    Uniform05.requiredDemand i=PrefixRoot.requiredDemand i := by
  simp only [Uniform05.requiredDemand,PrefixRoot.requiredDemand,
    Uniform05.t_eq_canonical,Uniform05.delta_eq_canonical]

theorem cap_eq (i : Uniform07.Row) : Uniform05.cap i=ReceiptGap.cap i := by
  simp only [Uniform05.cap,Uniform05.activeBid,ReceiptGap.cap,
    ActiveGraphComponent.activeBid,Uniform05.lambda_eq_canonical,
    Uniform05.t_eq_canonical,Uniform05.xi_eq_canonical,
    Uniform05.kappa_eq_canonical]

theorem radius_eq (i : Uniform07.Row) :
    Uniform05.guardRadius i=SourcePrefixConstructor.radius i := by
  simp only [Uniform05.guardRadius,SourcePrefixConstructor.radius,
    Uniform05.t_eq_canonical]

theorem demand_margin_eq (i : Uniform07.Row) :
    UniformFinite.Source.demandMargin i=EntryFiniteConstructor.gamma i := by
  simp only [UniformFinite.Source.demandMargin,Uniform05.lawDemandSlack,
    EntryFiniteConstructor.gamma,EntryPopulationMargins.demandSlack,
    Uniform05.t_eq_canonical,Uniform05.xi_eq_canonical,demand_eq,radius_eq,cap_eq]

theorem weight_margin_eq (i : Uniform07.Row) :
    UniformFinite.Source.weightMargin i=EntryPopulationMargins.stripMass i := by
  simp only [UniformFinite.Source.weightMargin,EntryPopulationMargins.stripMass,
    Uniform05.t_eq_canonical,demand_eq]

theorem mean_residual_eq (i : Uniform07.Row) :
    UniformFinite.Source.meanResidual i=EntryFiniteConstructor.residualMass i := by
  rw [UniformFinite.Source.meanResidual,Uniform05.t_eq_canonical,demand_eq]
  exact EntryPopulationMargins.residual_density i

theorem common_margin_eq_entry_epsilon (i : Uniform07.Row) :
    UniformFinite.Source.commonGuardMargin i=EntryFiniteConstructor.epsilon i := by
  let A:=min (EntryFiniteConstructor.gamma i)
    (min (EntryPopulationMargins.stripMass i) (EntryFiniteConstructor.residualMass i))
  have hAr : A≤ EntryFiniteConstructor.residualMass i :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hr : EntryFiniteConstructor.residualMass i< Uniform07.cutoff i/2 := by
    rw [←mean_residual_eq]
    simp only [UniformFinite.Source.meanResidual,Uniform05.t_eq_canonical]
    have hh:=Uniform05.requiredDemand_range i
    have ht:=Uniform05.t_pos i
    have hp:=mul_lt_mul_of_pos_left hh.2 ht
    rw [Uniform05.t_eq_canonical] at hp
    nlinarith
  have ht : Uniform07.cutoff i<1 := Uniform07.cutoff_lt_one i
  have hroom : A≤ EntryFiniteConstructor.roomMass i := by
    unfold EntryFiniteConstructor.roomMass
    linarith
  have hA1 : A≤ 1 := by linarith
  have hAt : A≤ Uniform07.cutoff i/2 := hAr.trans hr.le
  have hB : EntryFiniteConstructor.budget i=A := by
    apply le_antisymm
    · have hg : EntryFiniteConstructor.budget i≤ EntryFiniteConstructor.gamma i :=
        (min_le_right _ _).trans (min_le_left _ _)
      have hs : EntryFiniteConstructor.budget i≤ EntryPopulationMargins.stripMass i :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
      have hres : EntryFiniteConstructor.budget i≤ EntryFiniteConstructor.residualMass i :=
        (min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _)))
      exact le_min hg (le_min hs hres)
    · unfold EntryFiniteConstructor.budget
      exact le_min hA1 (le_min (min_le_left _ _)
        (le_min ((min_le_right _ _).trans (min_le_left _ _))
          (le_min hAr (le_min hroom hAt))))
  simp only [UniformFinite.Source.commonGuardMargin,EntryFiniteConstructor.epsilon,
    demand_margin_eq,weight_margin_eq,mean_residual_eq,hB,A]

def received06GuardData (i : Uniform07.Row) (m : ℕ) (L z : ℝ) : GuardData :=
  SourcePrefixConstructor.sourceGuard i L z
    (UniformFinite.Source.commonGuardMargin i) (m:ℝ)

theorem received06GuardData_fields (i : Uniform07.Row) {m : ℕ} (hm : 0< m)
    (L z : ℝ) : SourcePrefixConstructor.LiteralFields i (received06GuardData i m L z) :=
  SourcePrefixConstructor.sourceGuard_fields i L z _ _
    (UniformFinite.Source.common_guard_margin i) (Nat.cast_pos.mpr hm)

theorem received06GuardData_margin (i : Uniform07.Row) (m : ℕ) (L z : ℝ) :
    (received06GuardData i m L z).margin=EntryFiniteConstructor.epsilon i :=
  common_margin_eq_entry_epsilon i

section Encoding

def countRamp (ε a p : ℝ) : ℝ :=
  FiniteGuards.ramp (2*ε) ε (10*ε-|a-p|)

def countProduct (ε : ℝ) (a p : Fin 3→ℝ) : ℝ :=
  ∏ j : Fin 3,countRamp ε (a j) (p j)

def encodedCount (ε M : ℝ) (a p : Fin 3→ℝ) : ℝ :=
  ε*M*(1+countProduct ε a p)

theorem countProduct_bounds (ε : ℝ) (a p : Fin 3→ℝ) :
    countProduct ε a p∈Icc (0:ℝ) 1 := by
  exact ⟨Finset.prod_nonneg (fun _ _ => (FiniteGuards.ramp_bounds _ _ _).1),
    Finset.prod_le_one (fun _ _ => (FiniteGuards.ramp_bounds _ _ _).1)
      (fun _ _ => (FiniteGuards.ramp_bounds _ _ _).2)⟩

theorem ramp_normalize {ε M s : ℝ} (hε : ε≠0) (hM : M≠0) :
    FiniteGuards.ramp (2*ε*M) (ε*M) s=
      FiniteGuards.ramp (2*ε) ε (s/M) := by
  unfold FiniteGuards.ramp
  congr 1
  rw [show 2*ε*M-ε*M=ε*M by ring,show 2*ε-ε=ε by ring]
  field_simp [hε,hM]

theorem encodedCount_ramp {ε M : ℝ} (hε : 0<ε) (hM : 0< M)
    (a p : Fin 3→ℝ) :
    FiniteGuards.ramp (2*ε*M) (ε*M) (encodedCount ε M a p)=
      countProduct ε a p := by
  unfold FiniteGuards.ramp encodedCount
  have he : (ε*M*(1+countProduct ε a p)-ε*M)/(2*ε*M-ε*M)=
      countProduct ε a p := by
    rw [show 2*ε*M-ε*M=ε*M by ring]
    field_simp [hε.ne',hM.ne']
    ring
  rw [he]
  exact FiniteGuards.clip01_self (countProduct_bounds ε a p)

theorem seven_factors_eq_five {ε M : ℝ} (hε : 0<ε) (hM : 0< M)
    (physical : Fin 4→ℝ) (a p : Fin 3→ℝ) :
    (∏ j : Fin 5,FiniteGuards.ramp (2*ε*M) (ε*M)
      (![physical 0,physical 1,physical 2,physical 3,encodedCount ε M a p] j))=
    UniformFinite.Literal.guardWeight ε (2*ε)
      ![physical 0/M,physical 1/M,physical 2/M,physical 3/M,
        10*ε-|a 0-p 0|,10*ε-|a 1-p 1|,10*ε-|a 2-p 2|] := by
  change _ = ∏ j : Fin 7,FiniteGuards.ramp (2*ε) ε
    (![physical 0/M,physical 1/M,physical 2/M,physical 3/M,
      10*ε-|a 0-p 0|,10*ε-|a 1-p 1|,10*ε-|a 2-p 2|] j)
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  rw [encodedCount_ramp hε hM]
  simp only [ramp_normalize hε.ne' hM.ne']
  unfold countProduct countRamp
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
  ring_nf
  rfl

theorem countRamp_distance {ε : ℝ} (hε : 0<ε) (a b p : ℝ) :
    |countRamp ε a p-countRamp ε b p|≤|a-b|/ε := by
  have hh:=FiniteGuards.ramp_lipschitz (show ε<2*ε by linarith)
    (10*ε-|a-p|) (10*ε-|b-p|)
  have hab : |(10*ε-|a-p|)-(10*ε-|b-p|)|≤|a-b| := by
    have h:=abs_abs_sub_abs_le_abs_sub (a-p) (b-p)
    have he : (10*ε-|a-p|)-(10*ε-|b-p|)=-(|a-p|-|b-p|) := by ring
    rw [he,abs_neg]
    convert h using 1; congr 1; ring
  exact hh.trans (by
    have hden : 2*ε-ε=ε := by ring
    rw [hden]
    exact div_le_div_of_nonneg_right hab hε.le)

theorem encodedCount_normalized_distance {ε M : ℝ}
    (hε : 0<ε) (hM : M≠0) (a b p : Fin 3→ℝ) :
    |encodedCount ε M a p/M-encodedCount ε M b p/M|≤
      ∑ j : Fin 3,|a j-b j| := by
  have he : encodedCount ε M a p/M-encodedCount ε M b p/M=
      ε*(countProduct ε a p-countProduct ε b p) := by
    unfold encodedCount
    field_simp [hM]
    ring
  rw [he,abs_mul,abs_of_pos hε]
  have hp:=FiniteGuards.abs_product_sub_product_le Finset.univ
    (fun j : Fin 3=>countRamp ε (a j) (p j))
    (fun j : Fin 3=>countRamp ε (b j) (p j))
    (fun _ _=>FiniteGuards.ramp_bounds _ _ _)
    (fun _ _=>FiniteGuards.ramp_bounds _ _ _)
  have hsum : (∑ j : Fin 3,|countRamp ε (a j) (p j)-countRamp ε (b j) (p j)|)≤
      (∑ j : Fin 3,|a j-b j|)/ε := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum (fun j _=>countRamp_distance hε _ _ _)
  have hh:=mul_le_mul_of_nonneg_left (hp.trans hsum) hε.le
  have hcancel : ε*((∑ j : Fin 3,|a j-b j|)/ε)=∑ j : Fin 3,|a j-b j| := by
    field_simp [hε.ne']
  rw [hcancel] at hh
  exact hh

end Encoding

def categoryMean (i : Uniform07.Row) : Fin 3→ℝ :=
  ![Uniform07.cutoff i,(1-Uniform07.cutoff i)/2,(1-Uniform07.cutoff i)/2]

def countCoordinate {N : ℕ} (m : ℕ) (r : Fin N→ Fin 4) : Fin 3→ℝ :=
  ![((EntryFullRestoration.count 0 r:ℝ)+1)/(m:ℝ),
    (EntryFullRestoration.count 2 r:ℝ)/(m:ℝ),
    (EntryFullRestoration.count 3 r:ℝ)/(m:ℝ)]

def received06CountMargin (i : Uniform07.Row) (m : ℕ)
    (r : Fin (m-1)→ Fin 4) : ℝ :=
  encodedCount (UniformFinite.Source.commonGuardMargin i) (m:ℝ)
    (countCoordinate m r) (categoryMean i)

def centeredCountCoordinate (μ : Measure LowBody.RowRival) (i : Uniform07.Row)
    (m : ℕ) (L z : ℝ) : Fin 3→ℝ :=
  let g:=received06GuardData i m L z
  ![LiteralGuardRare.currentMeans μ (m-1) (Uniform07.xi i) g 0+(m:ℝ)⁻¹,
    LiteralGuardRare.currentMeans μ (m-1) (Uniform07.xi i) g 2,
    LiteralGuardRare.currentMeans μ (m-1) (Uniform07.xi i) g 3]

def received06CountCenter (μ : Measure LowBody.RowRival) (i : Uniform07.Row)
    (m : ℕ) (L z : ℝ) : ℝ :=
  encodedCount (UniformFinite.Source.commonGuardMargin i) (m:ℝ)
    (centeredCountCoordinate μ i m L z) (categoryMean i)/(m:ℝ)

theorem countCoordinate_eq_sums (i : Uniform07.Row) {m : ℕ} (_hm : 0< m)
    (L z : ℝ) (ω : Fin (m-1)→ LowBody.RowRival) :
    countCoordinate m (fun j=>(ω j).1)=
      ![LiteralGuardEmpirical.sums (Uniform07.xi i) (received06GuardData i m L z) ω 0+
          (m:ℝ)⁻¹,
        LiteralGuardEmpirical.sums (Uniform07.xi i) (received06GuardData i m L z) ω 2,
        LiteralGuardEmpirical.sums (Uniform07.xi i) (received06GuardData i m L z) ω 3] := by
  funext j
  fin_cases j
  · change ((EntryFullRestoration.count 0 (fun j => (ω j).1):ℝ)+1)/(m:ℝ)=
      (∑ j,RivalGood.tag 0 (ω j))/(m:ℝ)+(m:ℝ)⁻¹
    rw [RawGoodGeometry.sum_tag_eq_count,←EntryFullRestoration.count_eq_classCount]
    ring
  · change (EntryFullRestoration.count 2 (fun j => (ω j).1):ℝ)/(m:ℝ)=
      (∑ j,RivalGood.tag 2 (ω j))/(m:ℝ)
    rw [RawGoodGeometry.sum_tag_eq_count,←EntryFullRestoration.count_eq_classCount]
  · change (EntryFullRestoration.count 3 (fun j => (ω j).1):ℝ)/(m:ℝ)=
      (∑ j,RivalGood.tag 3 (ω j))/(m:ℝ)
    rw [RawGoodGeometry.sum_tag_eq_count,←EntryFullRestoration.count_eq_classCount]

theorem received06_count_receipt (i : Uniform07.Row) {m : ℕ} (hm : 2≤ m)
    (μ : Measure LowBody.RowRival) (L z : ℝ) (ω : Fin (m-1)→ LowBody.RowRival) :
    |received06CountMargin i m (fun j=>(ω j).1)/(m:ℝ)-
      received06CountCenter μ i m L z|≤
      LiteralGuardRare.deviationSum μ (Uniform07.xi i) (received06GuardData i m L z) ω+
        (m:ℝ)⁻¹ := by
  let g:=received06GuardData i m L z
  have hN : 0< m-1 := by omega
  have hM : 0<(m:ℝ) := Nat.cast_pos.mpr (by omega)
  have hNM : ((m-1:ℕ):ℝ)/(m:ℝ)≤ 1 :=
    (div_le_one hM).mpr (by exact_mod_cast Nat.sub_le m 1)
  have hratio : 0≤((m-1:ℕ):ℝ)/(m:ℝ) := by positivity
  have hd (j : Fin 8) :
      |LiteralGuardEmpirical.sums (Uniform07.xi i) g ω j-
        LiteralGuardRare.currentMeans μ (m-1) (Uniform07.xi i) g j|≤
      |RareEmpiricalReplacement.empirical (LiteralGuardEmpirical.statistic (Uniform07.xi i) g j)
        (m-1) ω-∫ r,LiteralGuardEmpirical.statistic (Uniform07.xi i) g j r ∂μ| := by
    rw [LiteralGuardRare.sums_current_difference μ (Uniform07.xi i) g hN ω j,abs_mul]
    change |((m-1:ℕ):ℝ)/(m:ℝ)| * _ ≤ _
    rw [abs_of_nonneg hratio]
    exact mul_le_of_le_one_left (abs_nonneg _) hNM
  have hsum : (∑ j : Fin 3,|countCoordinate m (fun j=>(ω j).1) j-
      centeredCountCoordinate μ i m L z j|)≤
      LiteralGuardRare.deviationSum μ (Uniform07.xi i) g ω := by
    rw [countCoordinate_eq_sums i (by omega) L z ω]
    simp only [centeredCountCoordinate,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
      Matrix.cons_val_zero,Matrix.cons_val_succ,add_sub_add_right_eq_sub]
    have h0:=hd 0
    have h2:=hd 2
    have h3:=hd 3
    change |LiteralGuardEmpirical.sums (Uniform07.xi i) g ω 0-
      LiteralGuardRare.currentMeans μ (m-1) (Uniform07.xi i) g 0|+
      (|LiteralGuardEmpirical.sums (Uniform07.xi i) g ω 2-
      LiteralGuardRare.currentMeans μ (m-1) (Uniform07.xi i) g 2|+
      |LiteralGuardEmpirical.sums (Uniform07.xi i) g ω 3-
      LiteralGuardRare.currentMeans μ (m-1) (Uniform07.xi i) g 3|) ≤ _
    let f : Fin 8 → ℝ := fun j => |RareEmpiricalReplacement.empirical
      (LiteralGuardEmpirical.statistic (Uniform07.xi i) g j) (m-1) ω-
        ∫ r,LiteralGuardEmpirical.statistic (Uniform07.xi i) g j r ∂μ|
    apply (add_le_add h0 (add_le_add h2 h3)).trans
    change f 0+(f 2+f 3) ≤ ∑ j,f j
    calc
      _ = ∑ j ∈ ({0,2,3} : Finset (Fin 8)),f j := by simp
      _ ≤ ∑ j,f j := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => abs_nonneg _)
  have he:=encodedCount_normalized_distance (UniformFinite.Source.common_guard_margin i)
    hM.ne' (countCoordinate m (fun j=>(ω j).1))
    (centeredCountCoordinate μ i m L z) (categoryMean i)
  exact (he.trans hsum).trans (le_add_of_nonneg_right (inv_nonneg.mpr hM.le))

def received06KernelFields {E : ℕ→ Type*}
    (G : ∀ m,E m→ ProbabilityMeasure (ℝ×ℝ))
    (L z : ∀ m,E m→ℝ) (hm : ∀ m (_ : E m),2≤ m) (i : Uniform07.Row) :
    SourcePreciseFamily.KernelFields G
      (fun m e=>received06GuardData i m (L m e) (z m e))
      (fun m _=>received06CountMargin i m) i where
  population_eq:=fun _ _=>rfl
  ε:=UniformFinite.Source.commonGuardMargin i
  margin_pos:=UniformFinite.Source.common_guard_margin i
  margin_lower:=fun _ _=>le_rfl
  Kcount:=1
  count_constant_nonneg:=by norm_num
  cmbar:=fun m e b θ=>received06CountCenter
    (RawTiltedSource.tiltedSource i (G m e:Measure (ℝ×ℝ)) b θ) i m (L m e) (z m e)
  count_receipt:=by
    intro m e b θ hb hbL
    exact ae_of_all _ fun ω=>by
      simpa only [one_mul,received06GuardData,SourcePrefixConstructor.sourceGuard] using received06_count_receipt i (hm m e)
        (RawTiltedSource.tiltedSource i (G m e:Measure (ℝ×ℝ)) b θ)
        (L m e) (z m e) ω

section EntryCount

theorem normalized_count_error {N m : ℕ} (hsize : N+1=m)
    (hm : 0< m) {ε c q d : ℝ} (hε : 0≤ε)
    (hq : q∈Icc (0:ℝ) 1) (hd : d∈Icc (0:ℝ) 1)
    (hc : |c-(N:ℝ)*q|<ε*(N:ℝ)) :
    |(c+d)/(m:ℝ)-q|<ε+(m:ℝ)⁻¹ := by
  have hM : 0<(m:ℝ) := Nat.cast_pos.mpr hm
  have hsizeR : (N:ℝ)+1=m := by exact_mod_cast hsize
  have hshift : |d-q|≤ 1 := abs_le.mpr ⟨by linarith [hd.1,hq.2],by linarith [hd.2,hq.1]⟩
  have he : (c+d)/(m:ℝ)-q=((c-(N:ℝ)*q)+(d-q))/(m:ℝ) := by
    field_simp [hM.ne']
    have hprod := congrArg (fun x : ℝ => x*q) hsizeR
    nlinarith only [hprod]
  rw [he,abs_div,abs_of_pos hM]
  apply (div_lt_iff₀ hM).mpr
  have ht:=abs_add_le (c-(N:ℝ)*q) (d-q)
  have hright : (ε+(m:ℝ)⁻¹)*(m:ℝ)=ε*(m:ℝ)+1 := by
    field_simp [hM.ne']
  rw [hright]
  have hNle : (N:ℝ)≤ m := by linarith
  have hεN:=mul_le_mul_of_nonneg_left hNle hε
  linarith

theorem categoryMean_mem (i : Uniform07.Row) (j : Fin 3) :
    categoryMean i j∈Icc (0:ℝ) 1 := by
  have ht:=Uniform07.cutoff_pos i
  have ht1:=Uniform07.cutoff_lt_one i
  fin_cases j <;> dsimp [categoryMean]
  <;> constructor <;> linarith

theorem countProduct_eq_one {ε : ℝ} (hε : 0<ε) (a p : Fin 3→ℝ)
    (hclose : ∀ j,|a j-p j|≤ 8*ε) : countProduct ε a p=1 := by
  apply Finset.prod_eq_one
  intro j _
  unfold countRamp FiniteGuards.ramp
  apply FiniteGuards.clip01_one
  apply (le_div_iff₀ (by linarith : 0<2*ε-ε)).mpr
  linarith [hclose j]

theorem received06_count_contract (i : Uniform07.Row) {m : ℕ} (hm : 2≤ m)
    (hlarge : (m:ℝ)⁻¹≤ 7*UniformFinite.Source.commonGuardMargin i) (L z : ℝ) :
    EntryFullRestoration.CountContract i (received06GuardData i m L z)
      (received06CountMargin i m) := by
  let ε:=UniformFinite.Source.commonGuardMargin i
  have hε : 0<ε := UniformFinite.Source.common_guard_margin i
  have hsize : m-1+1=m := Nat.sub_add_cancel (by omega)
  have heq : EntryFiniteConstructor.epsilon i=ε :=
    (common_margin_eq_entry_epsilon i).symm
  intro r hno h0 h2 h3
  rw [heq] at h0 h2 h3
  have hc : ∀ j : Fin 3,|countCoordinate m r j-categoryMean i j|≤ 8*ε := by
    intro j
    fin_cases j
    · have hh:=normalized_count_error hsize (by omega) hε.le
        (categoryMean_mem i 0) (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num) h0
      change |((EntryFullRestoration.count 0 r:ℝ)+1)/(m:ℝ)-Uniform07.cutoff i|≤ 8*ε
      change |((EntryFullRestoration.count 0 r:ℝ)+1)/(m:ℝ)-Uniform07.cutoff i|<
        ε+(m:ℝ)⁻¹ at hh
      linarith
    · have hh:=normalized_count_error hsize (by omega) hε.le
        (categoryMean_mem i 1) (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) h2
      change |(EntryFullRestoration.count 2 r:ℝ)/(m:ℝ)-(1-Uniform07.cutoff i)/2|≤8*ε
      change |((EntryFullRestoration.count 2 r:ℝ)+0)/(m:ℝ)-(1-Uniform07.cutoff i)/2|<
        ε+(m:ℝ)⁻¹ at hh
      apply le_trans (b := ε+(m:ℝ)⁻¹) ?_ (by linarith)
      simpa only [add_zero] using hh.le
    · have hh:=normalized_count_error hsize (by omega) hε.le
        (categoryMean_mem i 2) (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) h3
      change |(EntryFullRestoration.count 3 r:ℝ)/(m:ℝ)-(1-Uniform07.cutoff i)/2|≤8*ε
      change |((EntryFullRestoration.count 3 r:ℝ)+0)/(m:ℝ)-(1-Uniform07.cutoff i)/2|<
        ε+(m:ℝ)⁻¹ at hh
      apply le_trans (b := ε+(m:ℝ)⁻¹) ?_ (by linarith)
      simpa only [add_zero] using hh.le
  have hp:=countProduct_eq_one hε (countCoordinate m r) (categoryMean i) hc
  change 2*ε*(m:ℝ)≤ encodedCount ε (m:ℝ) (countCoordinate m r) (categoryMean i)
  rw [encodedCount,hp]
  ring_nf
  rfl

theorem eventually_received06_count_contract (i : Uniform07.Row) :
    ∀ᶠ m : ℕ in atTop,∀ L z : ℝ,
      EntryFullRestoration.CountContract i (received06GuardData i m L z)
        (received06CountMargin i m) := by
  have hε : 0<7*UniformFinite.Source.commonGuardMargin i :=
    mul_pos (by norm_num) (UniformFinite.Source.common_guard_margin i)
  have hlim : Tendsto (fun m : ℕ=>(m:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2:ℕ),hlim.eventually (Iio_mem_nhds hε)]
    with m hm hsmall
  exact fun L z=>received06_count_contract i hm hsmall.le L z

end EntryCount

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
