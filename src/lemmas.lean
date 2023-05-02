import data.fintype.basic
import data.finset.sum
import data.set.pairwise
import algebra.big_operators.basic
import algebra.big_operators.order
import algebra.order.monoid
import tactic

variables {α : Type*} [decidable_eq α] [fintype α]

open_locale big_operators

lemma sdiff_empty_of_subset_of_inter_card_eq {s t u : finset α} 
  (h₁ : s ⊆ t) (h₂ : (s ∩ u).card = (t ∩ u).card) 
  : (t ∩ u) \ (s ∩ u) = ∅ :=
begin
  rw finset.sdiff_eq_empty_iff_subset,
  rw finset.eq_of_subset_of_card_le (finset.inter_subset_inter_right h₁) (h₂.ge),
  refl,
end

lemma sdiff_subset_compl_of_card_eq {s t u : finset α} 
  (h₁ : s ⊆ t) (h₂ : (s ∩ u).card = (t ∩ u).card) 
  : ∀ x ∈ (t \ s), x ∉ u := 
begin
  have tmp := (finset.eq_of_subset_of_card_le (finset.inter_subset_inter_right h₁) h₂.ge),
  intro x,
  simp,
  rintro ht hs hu,
  have : x ∈ t ∩ u := finset.mem_inter.2 ⟨ht, hu⟩,
  rw [←tmp, finset.mem_inter] at this,
  exact hs this.1,
end

lemma sdiff_subset_compl {k} {s t : finset α} {u : finset α} (h₁ : s ⊆ t) (h₂ : (s ∩ u).card = k) (h₃ : (t ∩ u).card = k) 
  : ∀ x ∈ (t \ s), x ∉ u := sdiff_subset_compl_of_card_eq h₁ (h₂.trans h₃.symm)

lemma cards_eq_of_cards_le_sum_eq {β} [decidable_eq β] (s : finset β) {f : β → finset α} {g : β → ℕ}
  (h1 : ∀ i ∈ s, (f i).card ≤ g i)
  (h2 : (s.bUnion f).card ≥ ∑ i in s, g i) :
  ∀ i ∈ s, (f i).card = g i :=
begin
  have h3 := @finset.card_bUnion_le _ _ _ s f,
  replace h3 := h3.trans (finset.sum_le_sum h1),
  replace h3 := h3.antisymm h2,
  rintro i is,
  apply (h1 i is).antisymm,
  have h4 := finset.not_mem_erase i s,
  rw [←finset.insert_erase is] at h1 h3,
  rw [finset.sum_insert h4, finset.bUnion_insert] at h3,
  rw [finset.forall_mem_insert] at h1,
  have h5 := @finset.card_bUnion_le _ _ _ (s.erase i) f,
  replace h5 := h5.trans (finset.sum_le_sum h1.2),
  linarith [finset.card_union_le (f i) ((s.erase i).bUnion f)],
end

lemma card_union_eq_of_cards_le_sum_eq {s t : finset α} {S T : ℕ}
  (hs : s.card ≤ S) (ht : t.card ≤ T) (hsum : (s ∪ t).card = S + T) :
  s.card = S ∧ t.card = T :=
begin
  have h_union : (s ∪ t).card ≤ s.card + t.card := finset.card_union_le _ _,
  split;
  linarith,
end

lemma eq_pointwise_of_le_pointwise_of_sum_eq 
  {α} {s : finset α} {f g : α → ℕ}
  (h1 : ∀ i ∈ s, f i ≤ g i) (h2 : (∑ i in s, f i) ≥ (∑ i in s, g i)) :
  ∀ i ∈ s, f i = g i :=
begin
  induction s using finset.cons_induction_on with a s has ih, {
    simp,
  }, {
    simp only [finset.mem_cons, forall_eq_or_imp, finset.sum_cons] at *,
    refine ⟨by linarith [finset.sum_le_sum h1.2], ih h1.2 (by linarith)⟩,
  }
end

lemma cards_eq_of_cards_le_sum_ge {β} [decidable_eq β] (s : finset β) {f : β → finset α} {g : β → ℕ}
  (h1 : ∀ i ∈ s, (f i).card ≤ g i)
  (h2 : (s.bUnion f).card ≥ ∑ i in s, g i) :
  ∀ i ∈ s, (f i).card = g i :=
begin
  apply eq_pointwise_of_le_pointwise_of_sum_eq h1,
  refine h2.le.trans (finset.card_bUnion_le),
end

lemma left_ge_of_right_le_sum_ge (a b c d : ℕ) 
  (h1 : b ≤ d) (h2 : a + b ≥ c + d) : a ≥ c := by linarith

lemma card_left_ge_of_card_right_le_card_union_ge {a b : finset α} {c d : ℕ}
  (h1 : b.card ≤ d) (h2 : (a ∪ b).card ≥ c + d) : a.card ≥ c :=
begin
  linarith [left_ge_of_right_le_sum_ge, finset.card_union_le a b],
end

lemma card_right_ge_of_card_left_le_card_union_ge {a b : finset α} {c d : ℕ}
  (h1 : a.card ≤ c) (h2 : (a ∪ b).card ≥ c + d) : b.card ≥ d :=
begin
  rw [finset.union_comm, add_comm] at h2,
  exact card_left_ge_of_card_right_le_card_union_ge h1 h2,
end

lemma cards_le_bUnion_card_ge {β} [decidable_eq β] (s : finset β) {f : β → finset α} {g : β → ℕ}
  (h1 : ∀ i ∈ s, (f i).card ≤ g i)
  (h2 : (s.bUnion f).card ≥ ∑ i in s, g i) :
  (∀ i ∈ s, (f i).card = g i) ∧ (s : set β).pairwise_disjoint f :=
begin
  induction s using finset.cons_induction_on with a s has ih, {
    simp,
  }, {
    -- rw ←finset.sup_indep_iff_pairwise_disjoint,
    -- rw finset.sup_indep_iff_disjoint_erase,
    simp [has] at *,
    specialize ih h1.2 (card_right_ge_of_card_left_le_card_union_ge h1.1 h2),
    -- refine ⟨⟨_, ih.1⟩, ih.2, _⟩,
    sorry,
  } 
end

namespace adjacent 

variables {n : ℕ} [has_zero (fin n)] [has_one (fin n)]

def neighbors1d (z : fin n.succ) : finset (fin n.succ) := 
  if (z = 0) then {z, z + 1} else
  if (z = n) then {z - 1, z} else
  {z - 1, z, z + 1}

def neighbors (z : fin n.succ × fin n.succ) :=
  finset.product (neighbors1d z.1) (neighbors1d z.2)

@[derive decidable_rel]
def adj (i j : fin n.succ) : Prop :=
  if i = 0 then j = i ∨ j = i + 1 else
  if i = n then j = i - 1 ∨ j = i else
  j = i - 1 ∨ j = i ∨ j = i + 1


@[derive decidable_rel]
def adj2 (a b : fin n.succ × fin n.succ) := adj a.1 b.1 ∧ adj a.2 b.2

lemma neighbors_eq_filter_adj (z : fin n.succ × fin n.succ) : 
  neighbors z = finset.univ.filter (adj2 z) :=
begin
  ext,
  simp [neighbors, neighbors1d, adj2, adj],
  split_ifs,
  all_goals { simp only [finset.mem_insert, finset.mem_singleton] },
end

lemma mem_neighbors1d_self (z : fin n.succ) :
  z ∈ neighbors1d z :=
begin
  simp [neighbors1d, adj],
  split_ifs; simp,
end

lemma mem_neighbors_self (z : fin n.succ × fin n.succ) 
  : z ∈ neighbors z := 
  by simp [neighbors, mem_neighbors1d_self]

end adjacent