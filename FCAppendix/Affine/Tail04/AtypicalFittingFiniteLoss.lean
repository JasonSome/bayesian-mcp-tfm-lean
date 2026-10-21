import FCAppendix.Affine.Tail04.AtypicalActiveNoisy
import FCAppendix.Affine.Tail04.SortedAllNoise
import FCAppendix.Affine.Hybrid.PureRelabel
import FCAppendix.Affine.LowBody.PureFiniteCrossing
import FCAppendix.Affine.LowBody.PureFiniteEnvelope

noncomputable section
namespace FCAppendix.Affine.Tail04.AtypicalFittingFiniteLoss
open MeasureTheory Set Classical
open LowBody LowBody.CompleteInformation AllCountAtypical SortedAllNoise
open scoped BigOperators

variable {N : ℕ}

lemma maximizing_pair_copy_mono {κ : ℝ} (hκ : 0< κ) (b : Fin N → ℝ)
    (i : Fin N) (y : ℝ) (hy : b i< y)
    (P Q : Finset (Fin N)×Finset (Fin N))
    (hP : potential κ b Q.1 Q.2≤ potential κ b P.1 P.2)
    (hQ : potential κ (Function.update b i y) P.1 P.2≤
      potential κ (Function.update b i y) Q.1 Q.2) :
    focalCopy P i≤ focalCopy Q i := by
  rw [potential_update_focal,potential_update_focal] at hQ
  apply focalCopy_mono_of_coefficient hκ P Q i
  nlinarith

theorem duplicate_acquisition_active_interval {r0 r1 : ℕ} (hr0 : r0≤ N) (hr1 : r1≤ N)
    {κ B : ℝ} (hκ : 0< κ) (hsep : κ*B<1)
    (b : Fin N → ℝ) (hb : ∀ j,b j∈Icc (1:ℝ) B)
    (i : Fin N) (y : ℝ) (hy : b i< y) (hyB : y≤ B)
    (P0 P1 : Finset (Fin N)×Finset (Fin N))
    (hP00 : P0.1.card=r0) (hP01 : P0.2.card=r1)
    (hP10 : P1.1.card=r0) (hP11 : P1.2.card=r1)
    (hm0 : ∀ S T,S.card=r0 → T.card=r1 → potential κ b S T≤ potential κ b P0.1 P0.2)
    (hm1 : ∀ S T,S.card=r0 → T.card=r1 →
      potential κ (Function.update b i y) S T≤ potential κ (Function.update b i y) P1.1 P1.2)
    (hn : focalCopy P0 i≠2) (hd : focalCopy P1 i=2) :
    ∃ j,j≠i ∧ b j∈Icc (b i) y := by
  let A := Choice (ι:=Fin N) r0×Choice (ι:=Fin N) r1
  let f : ℝ → A → ℝ := fun t P => potential κ (Function.update b i t) P.1.1 P.2.1
  have hf (P : A) : Continuous (fun t => f t P) :=
    (continuous_potential κ (P.1.1,P.2.1)).comp (continuous_const.update i continuous_id)
  let a0 : A := (⟨P0.1,hP00⟩,⟨P0.2,hP01⟩)
  let a1 : A := (⟨P1.1,hP10⟩,⟨P1.2,hP11⟩)
  have htag0 : ¬i∈a0.1.1∩a0.2.1 := fun h => hn ((focalCopy_eq_two_iff P0 i).mpr h)
  have htag1 : i∈a1.1.1∩a1.2.1 := (focalCopy_eq_two_iff P1 i).mp hd
  have hx (a : A) : f (b i) a≤ f (b i) a0 := by
    simpa only [f,Function.update_eq_self,a0] using hm0 a.1.1 a.2.1 a.1.2 a.2.2
  have hz (a : A) : f y a≤ f y a1 := hm1 a.1.1 a.2.1 a.1.2 a.2.2
  obtain ⟨t,ht,P,Q,hP,hQ,hmP,hmQ⟩ := finite_mixed_maxima f hf
    (fun a => i∈a.1.1∩a.2.1) (b i) y hy.le a0 a1 htag0 htag1 hx hz
  by_contra hnone
  push Not at hnone
  have huni (j : Fin N) (hji : j≠i) :
      Function.update b i t j≠Function.update b i t i := by
    rw [Function.update_self,Function.update_of_ne hji]
    intro h
    exact hnone j hji (h.symm ▸ ht)
  have hbt (j : Fin N) : 0≤ Function.update b i t j := by
    by_cases hj : j=i
    · subst j
      simpa only [Function.update_self] using (show 0≤ t by linarith [(hb i).1,ht.1])
    · rw [Function.update_of_ne hj]
      exact (by norm_num : (0:ℝ)≤1).trans (hb j).1
  obtain ⟨j,hji,hj⟩ := SortedPotential.duplicate_change_scaled_tie_unsorted hr0 hr1
    κ hκ (Function.update b i t) hbt i huni P.1.1 P.2.1 Q.1.1 Q.2.1
    P.1.2 P.2.2 Q.1.2 Q.2.2
    (fun S T hS hT => hmP (⟨S,hS⟩,⟨T,hT⟩))
    (fun S T hS hT => hmQ (⟨S,hS⟩,⟨T,hT⟩)) hP hQ
  rw [Function.update_of_ne hji,Function.update_self] at hj
  have hsmall : κ*t<1 := (mul_le_mul_of_nonneg_left (ht.2.trans hyB) hκ.le).trans_lt hsep
  linarith [(hb j).1]

def crossingCount (b : Fin N → ℝ) (i : Fin N) (y : ℝ) : ℝ :=
  ∑ j : Fin N,if j≠i ∧ b j∈Icc (b i) y then 1 else 0

lemma crossingCount_nonneg (b : Fin N → ℝ) (i : Fin N) (y : ℝ) :
    0≤ crossingCount b i y := Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

lemma one_le_crossingCount (b : Fin N → ℝ) (i : Fin N) (y : ℝ)
    (h : ∃ j,j≠i ∧ b j∈Icc (b i) y) : 1≤ crossingCount b i y := by
  obtain ⟨j,hj⟩ := h
  have hh := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun k : Fin N => if k≠i ∧ b k∈Icc (b i) y then (1:ℝ) else 0)
    (fun k _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
  simpa only [if_pos hj,crossingCount] using hh

theorem maximizing_pairs_finite_loss {r0 r1 : ℕ} (hr0 : r0≤ N) (hr1 : r1≤ N)
    {κ B v : ℝ} (hκ : 1/2≤ κ) (hsep : κ*B<1)
    (b : Fin N → ℝ) (hb : ∀ j,b j∈Icc (1:ℝ) B)
    (i : Fin N) (hiv : b i≤ v) (y : ℝ) (hy : b i< y) (hyB : y≤ B)
    (P0 P1 : Finset (Fin N)×Finset (Fin N))
    (hP00 : P0.1.card=r0) (hP01 : P0.2.card=r1)
    (hP10 : P1.1.card=r0) (hP11 : P1.2.card=r1)
    (hm0 : ∀ S T,S.card=r0 → T.card=r1 → potential κ b S T≤ potential κ b P0.1 P0.2)
    (hm1 : ∀ S T,S.card=r0 → T.card=r1 →
      potential κ (Function.update b i y) S T≤ potential κ (Function.update b i y) P1.1 P1.2) :
    purePayoff κ v b P0 i-purePayoff κ v (Function.update b i y) P1 i≤
      (2*κ-1)*B*crossingCount b i y+2*κ*(y-b i) := by
  have hκp : 0< κ := by linarith
  have hB : 0≤ B := (by norm_num : (0:ℝ)≤1).trans ((hb i).1.trans (hb i).2)
  have hcoef : 0≤2*κ-1 := by linarith
  have hmono := maximizing_pair_copy_mono hκp b i y hy P0 P1
    (hm0 _ _ hP10 hP11) (hm1 _ _ hP00 hP01)
  have hjump := purePayoff_loss_le_duplicate (κ:=κ) b i hiv P0 P1 hmono
  have hprice := purePayoff_price_loss hκ b i y hy.le P1 (w:=v)
  have he : (if focalCopy P0 i≠2 ∧ focalCopy P1 i=2 then (2*κ-1)*b i else 0)≤
      (2*κ-1)*B*crossingCount b i y := by
    split_ifs with hd
    · have hc := one_le_crossingCount b i y
        (duplicate_acquisition_active_interval hr0 hr1 hκp hsep b hb i y hy hyB
          P0 P1 hP00 hP01 hP10 hP11 hm0 hm1 hd.1 hd.2)
      exact (mul_le_mul_of_nonneg_left (hb i).2 hcoef).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (mul_nonneg hcoef hB))
    · exact mul_nonneg (mul_nonneg hcoef hB) (crossingCount_nonneg b i y)
  linarith

lemma fittingPair_max (N H0 H1 c : ℕ) (ξ : ℝ) (b : Fin N → ℝ)
    (h0 : c-H0≤ N) (h1 : c-H1≤ N)
    (S T : Finset (Fin N)) (hS : S.card=c-H0) (hT : T.card=c-H1) :
    potential (1-ξ) b S T≤ potential (1-ξ) b
      (fittingPair N H0 H1 c ξ b).1 (fittingPair N H0 H1 c ξ b).2 := by
  letI : Nonempty (Choice (ι:=Fin N) (c-H0)) := choice_nonempty (c-H0) (by simpa using h0)
  letI : Nonempty (Choice (ι:=Fin N) (c-H1)) := choice_nonempty (c-H1) (by simpa using h1)
  change potential (1-ξ) b S T≤_
  rw [fittingPair,dif_pos ⟨h0,h1⟩]
  exact FiniteSelector.select_max
    (fun p : Choice (ι:=Fin N) (c-H0)×Choice (ι:=Fin N) (c-H1) =>
      potential (1-ξ) b p.1.1 p.2.1) (⟨S,hS⟩,⟨T,hT⟩)

def decodedFitting (N H0 H1 c : ℕ) (ξ : ℝ) (b : Fin N → ℝ) :
    Finset (Fin N)×Finset (Fin N) :=
  relabelPair (PrivateRowSorting.permutation b) (fittingPair N H0 H1 c ξ (sorted b))

lemma decodedFitting_cards (N H0 H1 c : ℕ) (ξ : ℝ) (b : Fin N → ℝ)
    (h0 : c-H0≤ N) (h1 : c-H1≤ N) :
    (decodedFitting N H0 H1 c ξ b).1.card=c-H0 ∧
      (decodedFitting N H0 H1 c ξ b).2.card=c-H1 := by
  simpa only [decodedFitting,relabelPair,Finset.card_map] using
    fittingPair_cards N H0 H1 c ξ (sorted b) h0 h1

lemma decodedFitting_max (N H0 H1 c : ℕ) (ξ : ℝ) (b : Fin N → ℝ)
    (h0 : c-H0≤ N) (h1 : c-H1≤ N)
    (S T : Finset (Fin N)) (hS : S.card=c-H0) (hT : T.card=c-H1) :
    potential (1-ξ) b S T≤ potential (1-ξ) b
      (decodedFitting N H0 H1 c ξ b).1 (decodedFitting N H0 H1 c ξ b).2 := by
  let σ := PrivateRowSorting.permutation b
  have h := fittingPair_max N H0 H1 c ξ (sorted b) h0 h1
    (S.map σ.symm.toEmbedding) (T.map σ.symm.toEmbedding)
    (by simpa only [Finset.card_map] using hS) (by simpa only [Finset.card_map] using hT)
  rw [SortedPotential.potential_map] at h
  have he : (fun j => sorted b (σ.symm j))=b := by
    funext j
    simp only [sorted,Function.comp_apply,σ,Equiv.apply_symm_apply]
  rw [he] at h
  simp only [decodedFitting,relabelPair,SortedPotential.potential_map,sorted] at h ⊢
  convert! h using 1

theorem sorted_fitting_finite_loss (N H0 H1 c : ℕ) {ξ B v : ℝ}
    (hξ : ξ≤1/2) (hsep : (1-ξ)*B<1)
    (h0 : c-H0≤ N) (h1 : c-H1≤ N)
    (b : Fin N → ℝ) (hb : ∀ j,b j∈Icc (1:ℝ) B)
    (i : Fin N) (hiv : b i≤ v) (y : ℝ) (hy : b i< y) (hyB : y≤ B) :
    purePayoff (1-ξ) v b (decodedFitting N H0 H1 c ξ b) i-
      purePayoff (1-ξ) v (Function.update b i y)
        (decodedFitting N H0 H1 c ξ (Function.update b i y)) i≤
      (1-2*ξ)*B*crossingCount b i y+2*(1-ξ)*(y-b i) := by
  have hP := decodedFitting_cards N H0 H1 c ξ b h0 h1
  have hQ := decodedFitting_cards N H0 H1 c ξ (Function.update b i y) h0 h1
  have h := maximizing_pairs_finite_loss h0 h1 (by linarith : (1:ℝ)/2≤1-ξ)
    hsep b hb i hiv y hy hyB
    (decodedFitting N H0 H1 c ξ b) (decodedFitting N H0 H1 c ξ (Function.update b i y))
    hP.1 hP.2 hQ.1 hQ.2
    (decodedFitting_max N H0 H1 c ξ b h0 h1)
    (decodedFitting_max N H0 H1 c ξ (Function.update b i y) h0 h1)
  convert! h using 1; ring

end FCAppendix.Affine.Tail04.AtypicalFittingFiniteLoss
