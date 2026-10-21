import FCAppendix.Affine.Tail04.PrivateUpdate
import FCAppendix.Affine.Tail04.PartialAtomCarrier

noncomputable section
namespace FCAppendix.Affine.Tail04.NativePartialInclusion
open MeasureTheory Set Classical Game Bayes
open LocalCoordinates PartialAtomCarrier NativeLocalPolicy.Data PrivateUpdate

variable {m c : ℕ} (D : NativeLocalPolicy.Data m c) (hlow : D.E.d<1-D.ξ)

lemma nonnegative_update (L : LocalList m) (hL : NonnegativeList L)
    (i : Fin m) {b : ℝ} (hb : 0≤ b) : NonnegativeList (Function.update L i (some b)) := by
  intro k
  by_cases hk : k=i
  · subst k;simpa [entryBid] using hb
  · simpa [Function.update_of_ne hk] using hL k

lemma partial_receipt (j : Fin 2) (L : LocalList m) (i : Fin m) {b : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) : D.numericalReceipt j L i=b := by
  have ht : i∈ids D.E 2 L := by simp [ids,hi,PrivateUpdate.tag_partial D hb]
  rw [D.numericalReceipt_private j L i ht,hi]
  rfl

include hlow in
theorem policy_inclusion_mono (j : Fin 2) (L : LocalList m)
    (hL : NonnegativeList L) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp)
    (hlt : b< b') (u u' : NativeLocalPolicy.Seed)
    (haccept : i∈(D.policy j L u).val) :
    i∈(D.policy j (Function.update L i (some b')) u').val := by
  have hnew : NonnegativeList (Function.update L i (some b')) :=
    nonnegative_update L hL i ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans hb'.1)
  apply optimal_inclusion_mono c (D.numericalReceipt j L)
    (D.policy j L u).val (D.policy j (Function.update L i (some b')) u').val i b'
  · rw [partial_receipt D j L i hi hb];exact hlt
  · exact D.numerical_optimal hlow j L hL u
  · rw [← PrivateUpdate.numericalReceipt_update D j L i hi hb hb']
    exact D.numerical_optimal hlow j _ hnew u'
  · exact haccept

include hlow in
lemma policy_indicator_mono (j : Fin 2) (L : LocalList m)
    (hL : NonnegativeList L) (i : Fin m) {b b' : ℝ}
    (hi : L i=some b) (hb : b∈Icc D.E.R D.E.Rp) (hb' : b'∈Icc D.E.R D.E.Rp)
    (hlt : b< b') (u u' : NativeLocalPolicy.Seed) :
    (if i∈(D.policy j L u).val then (1:ℝ) else 0) ≤
      if i∈(D.policy j (Function.update L i (some b')) u').val then 1 else 0 := by
  by_cases h : i∈(D.policy j L u).val
  · simp [h,policy_inclusion_mono D hlow j L hL i hi hb hb' hlt u u' h]
  · simp only [if_neg h]
    split_ifs <;> norm_num

include hlow in
theorem policy_above_partial_cluster (hc : 0< c) (j : Fin 2) (L : LocalList m)
    (b : Fin m → ℝ) (hL : ∀ k,L k=some (b k))
    (hb : ∀ k,b k∈Icc D.E.R D.E.Rp) (i : Fin m) {b' : ℝ}
    (hb' : b'∈Icc D.E.R D.E.Rp) (hbetter : ∀ k,b k< b') (u : NativeLocalPolicy.Seed) :
    i∈(D.policy j (Function.update L i (some b')) u).val := by
  have hnonneg : NonnegativeList L := by
    intro k
    rw [hL k]
    exact (D.E.d_nonneg.trans D.E.d_lt_R.le).trans (hb k).1
  have hnew := nonnegative_update L hnonneg i
    ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans hb'.1)
  have hreceipt : D.numericalReceipt j L=b := funext (fun k => partial_receipt D j L k (hL k) (hb k))
  have hh := D.numerical_optimal hlow j (Function.update L i (some b')) hnew u
  rw [PrivateUpdate.numericalReceipt_update D j L i (hL i) (hb i) hb',hreceipt] at hh
  exact included_above_every_receipt c hc b _ i b'
    ((D.E.d_nonneg.trans_lt D.E.d_lt_R).trans_le hb'.1) (fun k _ => hbetter k) hh

theorem old_rejections_at_least (j : Fin 2) (L : LocalList m) (u : NativeLocalPolicy.Seed) :
    ((m:ℝ)-c) ≤ ∑ i : Fin m,if i∈(D.policy j L u).val then (0:ℝ) else 1 := by
  have he : (∑ i : Fin m,if i∈(D.policy j L u).val then (0:ℝ) else 1)=
      (m:ℝ)-((D.policy j L u).val.card:ℝ) := by
    have hh (i : Fin m) : (if i∈(D.policy j L u).val then (0:ℝ) else 1)=
        1-(if i∈(D.policy j L u).val then (1:ℝ) else 0) := by split_ifs <;> norm_num
    simp_rw [hh]
    rw [Finset.sum_sub_distrib]
    simp
  rw [he]
  have hc' : (((D.policy j L u).val.card:ℕ):ℝ)≤ c := by
    exact_mod_cast (D.policy j L u).property.1
  linarith

include hlow in
theorem noisy_partial_comparison (j : Fin 2) (L : LocalList m)
    (hL : NonnegativeList L) (i : Fin m) (x y ε z : ℝ)
    (hε : 0≤ ε) (hz : 0≤ z) (hxy : x< y)
    (hi : L i=some (x*(1+ε*z)))
    (hx : x*(1+ε*z)∈Icc D.E.R D.E.Rp)
    (hy : y*(1+ε*z)∈Icc D.E.R D.E.Rp) (u u' : NativeLocalPolicy.Seed) :
    (if i∈(D.policy j L u).val then (1:ℝ) else 0) ≤
      if i∈(D.policy j (Function.update L i (some (y*(1+ε*z)))) u').val then 1 else 0 := by
  exact policy_indicator_mono D hlow j L hL i hi hx hy
    (mul_lt_mul_of_pos_right hxy (by nlinarith [mul_nonneg hε hz])) u u'

end FCAppendix.Affine.Tail04.NativePartialInclusion
