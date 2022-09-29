import combinatorics.simple_graph.strongly_regular

variables {α : Type*} {k : ℕ}
open finset

/-!
In this file, we're going to show that the Petersen graph is strongly regular. Now, in Lean it
is unfortunately a bit tricky to talk about individual graphs, so we define the Petersen graph
as the Kneser graph K(5, 2).

The Kneser graph K(n, k) is the graph whose vertices correspond to k-element subsets of a set of
n elements. For any two k-element subsets, their vertices in the graph are adjacent iff their
intersection is empty, i.e. they don't share any elements.
-/
def kneser (α : Type*) (k : ℕ) : simple_graph {X : finset α // X.card = k} :=
{ adj := λ X Y, k ≠ 0 ∧ ∀ x ∈ (X : finset α), x ∉ (Y : finset α),
    -- a strange definition so that i don't need to assume α is decidable
  loopless :=
  begin
    sorry,
  end,
  symm :=
  begin
    sorry,
  end }

variables [decidable_eq α] {X Y : {X : finset α // X.card = k}}

instance decidable_kneser_adj : decidable ((kneser α k).adj X Y) := and.decidable

/-!
Here we have translated our weird definition to one that'll give us the finset lemmas that make
our life easier by showing that they're equivalent.
-/
lemma kneser_adj :
  (kneser α k).adj X Y ↔ k ≠ 0 ∧ disjoint (X : finset α) Y :=
begin
  sorry,
end

/-!
The same thing as before, just with k ≠ 0 in our hypotheses (sometimes this makes things easier)
-/
lemma kneser_adj' (hk : k ≠ 0) :
  (kneser α k).adj X Y ↔ disjoint (X : finset α) Y :=
begin
    sorry,
end

open fintype
variables [fintype α] (hk : k ≠ 0)

include hk

lemma kneser_neighbours :
  (kneser α k).neighbor_finset X = finset.univ.filter (λ Y, disjoint (X : finset α) Y) :=
begin
  sorry,
end

-- hint: filters
lemma kneser_degree :
  (kneser α k).degree X = ((card α - k).choose k) :=
begin
  sorry,
end

lemma kneser_regular [fintype α] :
  (kneser α k).is_regular_of_degree ((card α - k).choose k) :=
begin
  sorry,
end

lemma kneser_card_common_neighbors  :
  card ((kneser α k).common_neighbors X Y) = (card α - ((X : finset α) ∪ Y).card).choose k :=
begin
  sorry,
end

lemma kneser_adjacent_neighbors (h : (kneser α k).adj X Y) :
  card ((kneser α k).common_neighbors X Y) = (card α - 2 * k).choose k :=
begin
  sorry,
end

omit hk

lemma kneser_two_non_adjacent_neighbors {X Y : finset α} (hX : X.card = 2) (hY : Y.card = 2)
  (h' : X ≠ Y) (h : ¬ (kneser α 2).adj ⟨X, hX⟩ ⟨Y, hY⟩) :
  card ((kneser α 2).common_neighbors ⟨X, hX⟩ ⟨Y, hY⟩) = (card α - 3).choose 2 :=
begin
  sorry,
end

lemma kneser_srg :
  (kneser α 2).is_SRG_with
    ((card α).choose 2) ((card α - 2).choose 2) ((card α - 4).choose 2) ((card α - 3).choose 2) :=
begin
-- so one thing that's cool about structures is that, another way you can show something satisfies a
-- structure's properties is the "constructor" tactic. if you want to give it a try it'll separate
-- what you have to prove into goals. if you're more comfortable using the usual { field := proof, etc }
-- format, you can replace the begin/end block with an underscore, hover over it, and select
-- "generate skeleton for the structure under construction" to get the usual setup
  constructor,
  sorry,
  sorry,
  sorry,
  sorry,
end

def petersen : simple_graph _ := kneser (fin 5) 2
instance : decidable_rel petersen.adj := λ _ _, decidable_kneser_adj

lemma petersen_srg : petersen.is_SRG_with 10 3 0 1 :=
begin
-- hint: convert tactic is useful here
  sorry,
end
