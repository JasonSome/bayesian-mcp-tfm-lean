import FCAppendix.Affine.Tail04.ActivePhysicalPayoff
import FCAppendix.Affine.Tail04.OrderedAtomActiveCompression
import FCAppendix.Affine.Tail04.IntegratedActiveFiniteGain
import FCAppendix.Affine.Tail04.SourceOrderedNoisyFixedPoint

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomFiniteGain
open MeasureTheory ProbabilityTheory Set Classical
open FiniteTailNoisyGame SourceTailNoisyFixedPoint
open ActivePhysicalPayoff AllCountActiveFiniteGain ActiveGainUniformModulus
open ActualActiveFiniteGain ActualFallbackPromotion EqualPrivateSignal
open OrderedAtomActiveCompression OriginalActiveCrossingCarrier
open scoped BigOperators

theorem finite_common_radius {ι : Type*} [Fintype ι]
    (r : ι→ℝ) (hr : ∀ i,0<r i) : ∃ δ : ℝ,0<δ ∧ ∀ i,δ≤r i := by
  let S := ∑ i,1/r i
  have hS : 0≤S := Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hr i)).le)
  refine ⟨1/(1+S),by positivity,?_⟩
  intro i
  have hi : 1/r i≤S := Finset.single_le_sum
    (fun j _ => (one_div_pos.mpr (hr j)).le) (Finset.mem_univ i)
  have hh := one_div_le_one_div_of_le (one_div_pos.mpr (hr i))
    (show 1/r i≤1+S by linarith)
  simpa only [one_div_one_div] using hh

lemma ordered_counts_equal_iff (H0 H1 : ℕ) :
    min H0 H1=max H0 H1 ↔ H0=H1 := by omega

section Compression
variable (D : Data) {X : Type*} {N : ℕ}
    (tag : X→ Fin 4) (decode : X→ Icc (1:ℝ) D.B)

theorem crossing_compression (x : X) (row : Fin N→ X) (y : ℝ) :
    AtypicalFittingFiniteLoss.crossingCount
      (fun j => (focalRow D (tags tag row) decode (decode x) row j:ℝ)) 0 y=
      ∑ i : Fin N,if crossing {z | tag z=1} (fun z => (decode z:ℝ)) (fun _ => y) x (row i)
        then 1 else 0 := by
  let k := tags tag row
  let e := enumeration D k 1
  have hs := Equiv.sum_comp e (fun i : {i : Fin N // k i=1} =>
    if (decode (row i.val):ℝ)∈Icc (decode x:ℝ) y then (1:ℝ) else 0)
  have hp := Fintype.sum_subtype_add_sum_subtype (p:=fun i : Fin N => k i=1)
    (fun i => if k i=1 then (if (decode (row i):ℝ)∈Icc (decode x:ℝ) y then (1:ℝ) else 0) else 0)
  have hz : (∑ i : {i : Fin N // ¬k i=1},
      if k i.val=1 then (if (decode (row i.val):ℝ)∈Icc (decode x:ℝ) y then (1:ℝ) else 0) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact if_neg i.property
  rw [hz,add_zero] at hp
  unfold AtypicalFittingFiniteLoss.crossingCount
  rw [Fin.sum_univ_succ]
  simp only [focalRow,Fin.cons_zero,ne_eq,not_true_eq_false,false_and,if_false,zero_add,
    Fin.cons_succ,Fin.succ_ne_zero,not_false_eq_true,true_and]
  change (∑ j : Fin (D.count k 1),if (decode (row (e j).val):ℝ)∈Icc (decode x:ℝ) y
    then (1:ℝ) else 0)=_
  rw [hs]
  have hsub (i : {i : Fin N // k i=1}) : k i.val=1 := i.property
  have he := (show (∑ i : {i : Fin N // k i=1},
      if (decode (row i.val):ℝ)∈Icc (decode x:ℝ) y then (1:ℝ) else 0)=
        ∑ i : Fin N,if k i=1 then
          (if (decode (row i):ℝ)∈Icc (decode x:ℝ) y then (1:ℝ) else 0) else 0 by
    simpa only [hsub,if_true] using hp)
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : tag (row i)=1 <;>
    simp only [k,tags,Function.comp_apply,crossing,mem_setOf_eq,hi,if_true,if_false,
      true_and,false_and,mem_Icc]

end Compression

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M<t)
local notation "Ds" => installOriginal D P t ht

def minFlag : ℝ := min D.eA D.eR

lemma minFlag_nonneg : 0 ≤ minFlag D := le_min D.heA0 D.heR0
lemma minFlag_le (reg : Bool) : minFlag D≤D.e0 reg := by
  cases reg
  · exact min_le_left _ _
  · exact min_le_right _ _

lemma count_le {N : ℕ} (kind : Fin N→Fin 4) (k : Fin 4) :
    D.count kind k≤N := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

def firstCount {N : ℕ} (kind : Fin N→Fin 4) : ℕ :=
  min ((Ds).count kind 2) ((Ds).count kind 3)

def secondCount {N : ℕ} (kind : Fin N→Fin 4) : ℕ :=
  max ((Ds).count kind 2) ((Ds).count kind 3)

def beta (N : ℕ) (kind : Fin N→Fin 4) (reg : Bool)
    (b : Fin ((Ds).count kind 1+1)→Icc (1:ℝ) D.B) (y : Icc (1:ℝ) D.B) : ℝ :=
  let old := fun j => (b j:ℝ)
  let cut := effectivePhi (decide (0<(Ds).count kind 0))
    (TypicalGuardStatistics.phi ((Ds).count kind 1+1)
      (firstCount D P t ht kind) (secondCount D P t ht kind)
      D.c D.ξ D.B D.R D.V D.width reg ((Ds).marksLaw _) ((Ds).marksLaw _))
  badWeightProbability cut (D.e0 reg) D.F (freezeFocal old 0 y)+
    badWeightProbability cut (D.e0 reg) D.F (Function.update old 0 (y:ℝ))

def meanBeta (N : ℕ) (kind : Fin N→Fin 4)
    (b : Fin ((Ds).count kind 1+1)→Icc (1:ℝ) D.B) (y : Icc (1:ℝ) D.B) : ℝ :=
  (1-(D.regimeShare:ℝ))*beta D P t ht N kind false b y+
    (D.regimeShare:ℝ)*beta D P t ht N kind true b y

lemma beta_bounds (N : ℕ) (kind : Fin N→Fin 4) (reg : Bool)
    (b : Fin ((Ds).count kind 1+1)→Icc (1:ℝ) D.B) (y : Icc (1:ℝ) D.B) :
    beta D P t ht N kind reg b y∈Icc (0:ℝ) 2 := by
  dsimp only [beta]
  constructor
  · exact add_nonneg (FiniteLaw.prob_nonneg _ _) (FiniteLaw.prob_nonneg _ _)
  · calc
      _ ≤ (1:ℝ)+1 := add_le_add (FiniteLaw.prob_le_one _ _) (FiniteLaw.prob_le_one _ _)
      _ = 2 := by norm_num

lemma meanBeta_bounds (N : ℕ) (kind : Fin N→Fin 4)
    (b : Fin ((Ds).count kind 1+1)→Icc (1:ℝ) D.B) (y : Icc (1:ℝ) D.B) :
    meanBeta D P t ht N kind b y∈Icc (0:ℝ) 2 := by
  have h0 := beta_bounds D P t ht N kind false b y
  have h1 := beta_bounds D P t ht N kind true b y
  have hs0 := D.regimeShare.2.1
  have hs1 := D.regimeShare.2.2
  dsimp only [meanBeta]
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs1) h0.1) (mul_nonneg hs0 h1.1)
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr h0.2),
      mul_nonneg hs0 (sub_nonneg.mpr h1.2)]

def orderedValue {N : ℕ} (kind : Fin N→Fin 4)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (v : ℝ)
    (b : Fin ((Ds).count kind 1+1)→Icc (1:ℝ) D.B) : ℝ :=
  ActivePhysicalPayoff.regimeValue Ds ((Ds).count kind 1)
    (firstCount D P t ht kind) (secondCount D P t ht kind) μP v
    (decide (0<(Ds).count kind 0)) b

theorem ordered_fiber_integral {N : ℕ} (kind : Fin N→Fin 4)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (v : ℝ) (b : Icc (1:ℝ) D.U)
    (row : Fin ((Ds).count kind 1)→Icc (1:ℝ) D.U) :
    OrderedFiniteTailNoisyGame.activeRegimeFiber Ds ((Ds).count kind 1)
      ((Ds).count kind 2) ((Ds).count kind 3) (decide (0<(Ds).count kind 0)) ((v,b,μP),row)=
      ∫ u : Fin ((Ds).count kind 1+1)→unitInterval,
        orderedValue D P t ht kind μP v
          (OriginalNoiseProduct.physicalRow (by norm_num : (0:ℝ)<1) D.heps.le
            ((Ds).count kind 1+1) (Fin.cons b row,u))
        ∂Measure.pi (fun _ : Fin ((Ds).count kind 1+1) => (volume : Measure unitInterval)) := by
  exact ActivePhysicalPayoff.activeRegimeFiber_integral Ds ((Ds).count kind 1)
    (firstCount D P t ht kind) (secondCount D P t ht kind) μP v
    (decide (0<(Ds).count kind 0)) b row

theorem exists_ordered_physical_gain_radius (N : ℕ) {C vhi e : ℝ}
    (hξh : D.ξ≤1/2) (hη : D.eta=1-2*D.ξ)
    (hC : 1≤C) (hBC : D.B≤C) (hCF : C≤D.F) (hvhi : 0≤vhi) (he : 0<e) :
    ∃ δ : ℝ,0<δ ∧ ∀ kind : Fin N→Fin 4,∀ μP : ProbabilityMeasure (Icc D.R D.Up),
      ∀ v∈Icc (0:ℝ) vhi,∀ b : Fin ((Ds).count kind 1+1)→Icc (1:ℝ) D.B,
      (∀ i j,i≠j→(b i:ℝ)≠(b j:ℝ)) → (b 0:ℝ)≤v →
      ∀ y : Icc (1:ℝ) D.B,(b 0:ℝ)<y → (y:ℝ)-(b 0:ℝ)<δ →
        populationCoefficient (N+1) D.ξ D.width (minFlag D) D.F C*
          (if (Ds).count kind 2=(Ds).count kind 3 then 0 else
            AtypicalFittingFiniteLoss.crossingCount (fun j => (b j:ℝ)) 0 y)-
          (vhi+2*C+1)*meanBeta D P t ht N kind b y*
            AtypicalFittingFiniteLoss.crossingCount (fun j => (b j:ℝ)) 0 y-
          2*e-smoothCoefficient D.ξ C vhi*((y:ℝ)-(b 0:ℝ))≤
        orderedValue D P t ht kind μP v (Function.update b 0 y)-
          orderedValue D P t ht kind μP v b := by
  have hex (q : (Fin N→Fin 4)×Bool) :=
    AllCountActiveFiniteGain.exists_finite_gain_radius
      (R:=D.R) (vlo:=0)
      (firstCount D P t ht q.1) (secondCount D P t ht q.1) D.c (N+1)
      (Nat.add_le_add_right (count_le Ds q.1 1) 1) D.hξ hξh D.hw
      (show 0≤D.e0 q.2 by
        cases q.2
        · exact D.heA0
        · exact D.heR0)
      (show D.e0 q.2≤1 by
        cases q.2
        · exact D.heA1
        · exact D.heR1) D.hF hCF hC hvhi
      q.2 (decide (0<(Ds).count q.1 0)) ((Ds).marksLaw _) ((Ds).marksLaw _)
      (0 : Fin ((Ds).count q.1 1+1)) he
  choose r hr hp using hex
  obtain ⟨δ,hδ,hδr⟩ := finite_common_radius r hr
  refine ⟨δ,hδ,?_⟩
  intro kind μP v hv b hno hval y hy hsmall
  have hB0 : 1≤D.B := by
    unfold Data.B
    nlinarith [D.hU,mul_nonneg (show 0≤D.U by linarith [D.hU]) D.heps.le]
  have hV0 : 0≤D.V := by
    unfold Data.V
    exact mul_nonneg (D.hR.le.trans D.hRUp) (by linarith [D.heps])
  have hRV : D.Up≤D.V := by
    dsimp [Data.V]
    nlinarith [mul_nonneg (D.hR.le.trans D.hRUp) D.heps.le]
  have hsep : (1-D.ξ)*D.B<1 := D.hgap.trans ((D.hRUp.trans hRV).trans_lt D.hRp)
  have hh (reg : Bool) := hp (kind,reg) D.B ⟨hB0,hBC⟩ D.V ⟨hV0,D.hRp.le⟩
    v hv hsep ((Ds).privateBayes (firstCount D P t ht kind) μP) b hno hval y hy
      (hsmall.trans_le (hδr (kind,reg)))
  have hm (reg : Bool) := populationCoefficient_mono_flag
    (m:=N+1) (width:=D.width) (F:=D.F) (C:=C) hξh (minFlag_nonneg D) (minFlag_le D reg)
  have hc : 0≤(if firstCount D P t ht kind=secondCount D P t ht kind then 0 else
      AtypicalFittingFiniteLoss.crossingCount (fun j => (b j:ℝ)) 0 y) := by
    split_ifs
    · exact le_rfl
    · exact AtypicalFittingFiniteLoss.crossingCount_nonneg _ _ _
  have hg (reg : Bool) := mul_le_mul_of_nonneg_right (hm reg) hc
  have h0 := mul_le_mul_of_nonneg_left (hh false) (sub_nonneg.mpr D.regimeShare.2.2)
  have h1 := mul_le_mul_of_nonneg_left (hh true) D.regimeShare.2.1
  have h0' := mul_le_mul_of_nonneg_left (hg false) (sub_nonneg.mpr D.regimeShare.2.2)
  have h1' := mul_le_mul_of_nonneg_left (hg true) D.regimeShare.2.1
  dsimp only at h0 h1
  unfold orderedValue ActivePhysicalPayoff.regimeValue ActivePhysicalPayoff.value meanBeta beta
  simp only [physicalUtility,Function.update_self] at h0 h1
  simp [firstCount,secondCount,Data.count,
    SourceTailNoisyFixedPoint.installOriginal,Data.B,Data.V,Data.e0,hη] at h0 h1 h0' h1' ⊢
  split_ifs at h0 h1 h0' h1' ⊢ <;> nlinarith only [h0,h1,h0',h1']

end FCAppendix.Affine.Tail04.OrderedAtomFiniteGain
