import data.set.function
import data.fin.basic
import data.set.finite
import tactic
import data.fin.basic
import lemmas

section defs

variables {n : ℕ} [has_one (fin n)]

def row (i : fin n) : finset (fin n × fin n) := finset.filter (λ p, p.1 = i) finset.univ

def col (i : fin n) : finset (fin n × fin n) := finset.filter (λ p, p.2 = i) finset.univ

def adj (i j : fin n) := i + 1 = j ∨ i = j ∨ i = j + 1

def adj2 (a b : fin n × fin n) := adj a.1 b.1 ∧ adj a.2 b.2

end defs

variables (n k : ℕ) [has_one (fin n)]

structure star_battle :=
  (region : fin n → finset (fin n × fin n))
  (star : finset (fin n × fin n))
  (star_adj : ∀ {a b}, a ∈ star → b ∈ star → adj2 a b → a = b)
  (star_row : ∀ i, (row i ∩ star).card = k)
  (star_col : ∀ i, (col i ∩ star).card = k)
  (star_region : ∀ i, (region i ∩ star).card = k)
