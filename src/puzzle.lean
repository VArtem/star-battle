import star_battle

def region : fin 5 → finset (fin 5 × fin 5)
| ⟨0, _⟩ := {(0, 0), (0, 1), (1, 0), (2, 0), (3, 0), (4, 0)}
| ⟨1, _⟩ := {(1, 1), (2, 1), (3, 1), (4, 1)}
| ⟨2, _⟩ := {(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4)}
| ⟨3, _⟩ := {(2, 2), (3, 2), (3, 3), (3, 4)}
| ⟨4, _⟩ := {(4, 2), (4, 3), (4, 4)}
| ⟨x+5, h⟩ := (nat.not_lt_zero x ((add_lt_iff_neg_right 5).mp h)).elim

example (p : star_battle 5 1) 
  (h_reg0 : p.region 0 = {(0, 0), (0, 1), (1, 0), (2, 0), (3, 0), (4, 0)})
  (h_reg1 : p.region 1 = {(1, 1), (2, 1), (3, 1), (4, 1)})
  (h_reg2 : p.region 2 = {(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4)})
  (h_reg3 : p.region 3 = {(2, 2), (3, 2), (3, 3), (3, 4)})
  (h_reg4 : p.region 4 = {(4, 2), (4, 3), (4, 4)})
  : ((0 : fin 5), (0 : fin 5)) ∈ p.star :=
begin
  have reg4_subset_row4 : p.region 4 ⊆ row 4, by simp [h_reg4, row, finset.insert_subset],
  have t1 := sdiff_subset_compl reg4_subset_row4 (p.star_region _) (p.star_row _),
  simp [row, h_reg4] at t1,
  have no_star_4_0 : ((4 : fin 5), (0 : fin 5)) ∉ p.star := by {
    apply t1,
    all_goals {dec_trivial},
  },
  have no_star_4_1 := t1 4 1 rfl (by dec_trivial),
  sorry
end